/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 nov. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "CompilerOfTransition.h"

#include <builder/analysis/CommunicationDependency.h>
#include <builder/primitive/AvmcodeCompiler.h>
#include <builder/primitive/CompilationEnvironment.h>
#include <builder/compiler/Compiler.h>
#include <builder/compiler/CompilerOfVariable.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableLib.h>

#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementFactory.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Transition.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
CompilerOfTransition::CompilerOfTransition(Compiler & aCompiler)
: BaseCompiler(aCompiler),
mCompiler( aCompiler ),
mVariableCompiler( aCompiler.getVariableCompiler() ),
mMocStack( ),
mCurrentMoc( nullptr ),
mDefaultMoc( TransitionMoc::MOE_RDE_RUN )
{
	setDefaultMoc();
}



void CompilerOfTransition::setDefaultMoc()
{
	mCurrentMoc = & mDefaultMoc;
}


void CompilerOfTransition::pushMoc(const WObject * mocTransition)
{
	mCurrentMoc = new TransitionMoc( mocTransition );

	mMocStack.push_back( mCurrentMoc );
}

void CompilerOfTransition::popMoc()
{
	if( mMocStack.nonempty() )
	{
		delete( mMocStack.pop_last() );
	}

	if( mMocStack.nonempty() )
	{
		mCurrentMoc = mMocStack.last();
	}
	else
	{
		mCurrentMoc = & mDefaultMoc;
	}
}


/**
 *******************************************************************************
 * PRECOMPILATION
 *******************************************************************************
 */
void CompilerOfTransition::precompileTransition(
		ExecutableForm & aContainer, Transition & aTransition)
{
//	AVM_OS_TRACE << TAB << "<$$$$$ precompiling transition < "
//			<< aTransition.getFullyQualifiedNameID() << " >" << std::endl;

	AvmTransition * anAvmTransition =
			new AvmTransition((& aContainer), aTransition, 0);

	getSymbolTable().addTransition(
			aContainer.saveTransition( anAvmTransition ) );

	Machine * target = nullptr;
	if( aTransition.hasTarget() )
	{
		target = getTransitionTarget(aTransition, aTransition.getTarget());
		if( target != nullptr )
		{
			aTransition.getTarget().acquirePointer( target );

			target->getUniqBehaviorPart()->
					appendIncomingTransition( INCR_BF(& aTransition) );
		}
	}

	/*
	 * Allocation of declaration contents :>
	 * constant, variable, typedef, buffer, port
	 */
	if( aTransition.hasPropertyPart() )
	{
		TableOfInstanceOfData tableOfVariable;

		mCompiler.precompileDataType( (* anAvmTransition),
				aTransition.getPropertyPart(), tableOfVariable );

		/*
		 * Update data table
		 */
		anAvmTransition->setVariables(tableOfVariable);
	}



//	AVM_OS_TRACE << TAB << ">$$$$$ end precompiling transition < "
//			<< aTransition.getFullyQualifiedNameID() << " >" << std::endl;
}




/**
 *******************************************************************************
 * COMPILATION
 *******************************************************************************
 */

/**
 * compile
 * transition
 */
void CompilerOfTransition::compileTransition(AvmTransition & anAvmTransition)
{
	const Transition & aTransition = anAvmTransition.getAstTransition();

//	AVM_OS_TRACE << TAB << "<| compiling<transiton>: "
//			<< TRIM(aTransition.toString(AVM_OS_TRACE.INDENT))
//			<< std::endl;

	const Machine & source = aTransition.getSource();

	const Machine * target = nullptr;


	BF sourceMachine = getSymbolTable().searchInstanceStatic(source);
	BF targetVariable;
	BF targetMachine;

	if( aTransition.hasTarget() )
	{
		BF tgt = compileTransitionTarget(anAvmTransition, aTransition.getTarget());

		if( tgt.valid() )
		{
			anAvmTransition.setTarget( tgt );

			if( tgt.is< InstanceOfMachine >() )
			{
				target = &( tgt.to< InstanceOfMachine >().getAstMachine() );

				targetMachine = tgt;

				if( target->getSpecifier().isPseudostateInitial() )
				{
					incrWarningCount();
					aTransition.warningLocation(AVM_OS_WARN)
							<< "Unexpected the pseudo-state< initial > '"
							<< target->getFullyQualifiedNameID()
							<< "' as target of the transition : "
							<< str_header( aTransition ) << std::endl;
				}
			}
			else if( tgt.is< InstanceOfData >() )
			{
				targetVariable = tgt;
			}
		}
	}

	// By default : the last active state
	// Only for Trace usage
	else if( not source.getSpecifier().isPseudostate() )
	{
		anAvmTransition.setTarget( sourceMachine );

		//???
//		aTransition.setTarget( anAvmTransition.getTarget() );
//		aTransition.setTarget( INCR_BF(source) );
	}
	else
	{
		// TODO found last stable state !!!
	}


	// COMPILATION OF DATA
	mVariableCompiler.compileVariable(anAvmTransition);

	/*
	 * EVAL transition
	 */
	BFCode OnRun(OperatorManager::OPERATOR_SEQUENCE);

	// DISABLE source / ENABLE target
	BFCode disableSource;
	BFCode enableTarget;
	BFCodeList ienableSequence;

	// DISABLE source
	disableSource = StatementConstructor::newCode(
			aTransition.hasMocAbort() ?
					OperatorManager::OPERATOR_ABORT_INVOKE :
					OperatorManager::OPERATOR_DISABLE_INVOKE,
			sourceMachine);

	if( targetMachine.valid() )
	{
		enableTarget = BFCode( OperatorManager::OPERATOR_ENABLE_INVOKE,
				targetMachine);

		if( target->getSpecifier().hasPseudostateHistory() )
		{
			//!! moe< statemachine > :> don't invoke ENABLE_SET
		}
		else if( target->getSpecifier().hasFamilyPseudostateEnding() )
		{
			enableTarget = StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					StatementConstructor::newCode(
						OperatorManager::OPERATOR_ENABLE_SET, targetMachine),
					enableTarget);
		}
		else if( target->getSpecifier().isPseudostate() )
		{
			//!! moe< statemachine > :> no need to invoke ENABLE_SET
		}
		// TRANSITION INSTABLE
		else if( aTransition.getModifier().hasFeatureTransient() )
		{
			enableTarget = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_IENABLE_INVOKE,
							targetMachine),
					StatementConstructor::newCode(
						OperatorManager::OPERATOR_RUN, targetMachine) );
		}
		else if( COMPILE_CONTEXT::INLINE_ENABLE_MASK )
		{
			enableTarget = StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					StatementConstructor::newCode(
						OperatorManager::OPERATOR_ENABLE_SET, targetMachine),
					enableTarget);
		}
		else
		{
			enableTarget = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					StatementConstructor::newCode(
						OperatorManager::OPERATOR_ENABLE_SET, targetMachine),
					enableTarget);
		}

		if( (& source) == target )
		{
			if( source.getSpecifier().isPseudostateInitial() )
			{
				incrErrorCount();
				AVM_OS_WARN << source.errorLocation(aTransition)
						<< "Unexpected transition loop in initial state << "
						<< str_header( source ) << " >> !!!" << std::endl;
			}
			else if( source.getSpecifier().isPseudostate() )
			{
				incrWarningCount();
				OS_VERBOSITY_MINIMUM_OR_DEBUG( AVM_OS_WARN )
						<< source.warningLocation(aTransition)
						<< "Transition loop in (unstable) pseudo state << "
						<< str_header( source ) << " >> !!!" << std::endl;
			}

			//!! NOTHING
			// BETWEEN  DISABLE/ABORT SOURCE
			// ==>  ENABLE TARGET
		}

		else if( source.getContainerMachine() == target->getContainerMachine() )
		{
			//!! NOTHING
			// BETWEEN  DISABLE/ABORT SOURCE
			// ==>  ENABLE TARGET
		}

		else if( (& source) == target->getContainerMachine() )
		{
			// IDISABLE/IABORT SOURCE
			// ==>  IENABLE & ENABLE TARGET
			disableSource = StatementConstructor::newCode(
					aTransition.hasMocAbort() ?
							OperatorManager::OPERATOR_IABORT_INVOKE :
							OperatorManager::OPERATOR_IDISABLE_INVOKE,
					sourceMachine);

			disableSource = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					StatementConstructor::newCode(
							aTransition.hasMocAbort() ?
									OperatorManager::OPERATOR_ABORT_CHILD :
									OperatorManager::OPERATOR_DISABLE_CHILD),
					disableSource);

			ienableSequence.push_front(
					BFCode(OperatorManager::OPERATOR_IENABLE_INVOKE) );
//							ExecutableLib::MACHINE_SELF) );
		}

		else if( source.getContainerMachine() == target )
		{
			// DISABLE/ABORT SOURCE & IDISABLE/IABORT CONTAINER
			// ==>  IENABLE & ENABLE TARGET
			disableSource = StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					disableSource,
					StatementConstructor::newCode(
							aTransition.hasMocAbort() ?
									OperatorManager::OPERATOR_IABORT_INVOKE :
									OperatorManager::OPERATOR_IDISABLE_INVOKE) );

			enableTarget = BFCode(
					aTransition.getModifier().hasFeatureTransient()
						? OperatorManager::OPERATOR_RETURN
						: OperatorManager::OPERATOR_ENABLE_INVOKE );
		}

		else
		{
			const Machine * lcaMachine = source.LCA(
				( target->getSpecifier().hasPseudostateHistory()
				|| target->getSpecifier().isPseudostateInitial() ) ?
						target->getContainerMachine() : target );

			AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( lcaMachine ) "LCA( "
					<< source.getFullyQualifiedNameID() << " , "
					<< target->getFullyQualifiedNameID() << " ) !!!"
					<< SEND_EXIT;

			if( (& source) != lcaMachine )
			{
				const Machine * containerOfSource = source.getContainerMachine();
				if( containerOfSource != lcaMachine )
				{
					avm_uinteger_t disableLevel = 1;

					for( ; containerOfSource != lcaMachine ; ++disableLevel )
					{
						containerOfSource =
								containerOfSource->getContainerMachine();
					}

					disableSource = StatementConstructor::newCode(
							aTransition.hasMocAbort()
								? OperatorManager::OPERATOR_ABORT_SELVES
								: OperatorManager::OPERATOR_DISABLE_SELVES,
							ExpressionConstructor::newUInteger(disableLevel) );

					if( source.hasMachine() )
					{
						disableSource = StatementConstructor::newCode(
							OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
							StatementConstructor::newCode(
								aTransition.hasMocAbort() ?
									OperatorManager::OPERATOR_ABORT_CHILD :
									OperatorManager::OPERATOR_DISABLE_CHILD),
							disableSource);
					}
				}
			}

			if( target->getContainerMachine() != lcaMachine )
			{
				const Machine * containerOfTarget = target->getContainerMachine();
				for( ; containerOfTarget != lcaMachine ;
					containerOfTarget = containerOfTarget->getContainerMachine() )
				{
					targetMachine = getSymbolTable().
							searchInstanceStatic(* containerOfTarget);
					if( targetMachine.valid() )
					{
						ienableSequence.push_front(
								BFCode(OperatorManager::OPERATOR_IENABLE_INVOKE,
										targetMachine) );
//										ExecutableLib::MACHINE_SELF) );

						ienableSequence.push_front(
								BFCode(OperatorManager::OPERATOR_ENABLE_SET,
										targetMachine) );
					}
					else
					{
						incrErrorCount();
						aTransition.errorLocation(AVM_OS_WARN)
								<< "Unfound transition target container"
									" state instance < "
								<< str_header( containerOfTarget )
								<< " > where LCA is < "
								<< str_header( lcaMachine )<< " >"
								<< std::endl
								<< aTransition.toString(AVM_TAB1_INDENT)
								<< std::endl;
					}
				}
			}
		}
	}
	else if( targetVariable.valid() )
	{
		enableTarget = BFCode( OperatorManager::OPERATOR_ENABLE_INVOKE,
				targetVariable);

		enableTarget = StatementConstructor::newCode(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
				StatementConstructor::newCode(
					OperatorManager::OPERATOR_ENABLE_SET, targetVariable),
				enableTarget);
	}


	if( aTransition.hasStatement() )
	{
		// Attention: création possible de variable local dans le conteneur,
		// i.e. l'état source de la transition
		OnRun->appendFlat( aTransition.getStatement() );
	}

	/*
	 * DISABLE source / ENABLE target
	 */
	if( disableSource.valid() && enableTarget.valid() &&
			(! aTransition.isMocInternal()) )
	{
		switch( mCurrentMoc->getMoeRun() )
		{
			case TransitionMoc::MOE_RDE_RUN:
			{
//				OnRun->getOperands().push_back( disableSource );
//				OnRun->getOperands().push_back( ienableSequence );
//				OnRun->getOperands().push_back( enableTarget );

				if( ienableSequence.nonempty() )
				{
					BFCode disableEnableAtomicSequence(
							StatementConstructor::newCodeFlat(
									OperatorManager::OPERATOR_SEQUENCE,
									disableSource) );
					disableEnableAtomicSequence->getOperands().push_back(
							ienableSequence);
					disableEnableAtomicSequence->getOperands().push_back(
							enableTarget);

					OnRun->getOperands().push_back( disableEnableAtomicSequence );
				}
				else
				{
					OnRun->getOperands().push_back( StatementConstructor::newCodeFlat(
							OperatorManager::OPERATOR_SEQUENCE,
							disableSource, enableTarget ) );
				}
				break;
			}

			case TransitionMoc::MOE_DRE_RUN:
			{
				OnRun->getOperands().push_front( disableSource );

				if( ienableSequence.nonempty() )
				{
					BFCode ienableEnableAtomicSequence(
							StatementConstructor::newCode(
									OperatorManager::OPERATOR_SEQUENCE,
									ienableSequence) );
					ienableEnableAtomicSequence->getOperands().push_back(
							enableTarget );

					OnRun->getOperands().push_back( ienableEnableAtomicSequence );
				}
				else
				{
					OnRun->getOperands().push_back( enableTarget );
				}
				break;
			}

			case TransitionMoc::MOE_DER_RUN:
			{
//				OnRun->getOperands().push_front( enableTarget );
//				OnRun->getOperands().push_front( ienableSequence );
//				OnRun->getOperands().push_front( disableSource );

				if( ienableSequence.nonempty() )
				{
					BFCode disableEnableAtomicSequence(
							StatementConstructor::newCodeFlat(
									OperatorManager::OPERATOR_SEQUENCE,
									disableSource) );
					disableEnableAtomicSequence->getOperands().push_back(
							ienableSequence );
					disableEnableAtomicSequence->getOperands().push_back(
							enableTarget );

					OnRun->getOperands().push_front(
							disableEnableAtomicSequence );
				}
				else
				{
					OnRun->getOperands().push_front(
							StatementConstructor::newCodeFlat(
									OperatorManager::OPERATOR_SEQUENCE,
									disableSource, enableTarget ) );
				}
				break;
			}

			case TransitionMoc::MOE_UNDEFINED_RUN:
			default:
			{
				//!!! NOTHING
				break;
			}
		}
	}

	if( OnRun->hasOperand() )
	{
		anAvmTransition.setCode( mAvmcodeCompiler.
				compileStatement(anAvmTransition, OnRun) );

		if( aTransition.hasStatement() )
		{
			// Attention: création possible de variable local dans le conteneur,
			// i.e. l'état source de la transition
			const BFCode & aCompiledCode = anAvmTransition.getCode();


			// the communication information
			bool hasMutableSchedule = false;

			anAvmTransition.setCommunicationCode(
					CommunicationDependency::getCommunicationCode(
							anAvmTransition, aCompiledCode, hasMutableSchedule) );

			anAvmTransition.setMutableCommunication( hasMutableSchedule );


			anAvmTransition.setInternalCommunicationCode(
					CommunicationDependency::getInternalCommunicationCode(
							anAvmTransition, aCompiledCode, hasMutableSchedule) );

//??!!??
//			if( anAvmTransition.getExecutableContainer()->
//					getSpecifier().hasFeatureInputEnabled() )
			{
				const AvmCode & aCode = (* aCompiledCode);

				CommunicationDependency::computeInputEnabledCom(
						anAvmTransition, aCode);

				CommunicationDependency::computeInputEnabledSave(
						anAvmTransition, aCode);


				CommunicationDependency::computeInputCom(
						anAvmTransition, aCode);

				CommunicationDependency::computeOutputCom(
						anAvmTransition, aCode);


				anAvmTransition.setEnvironmentCom(
						CommunicationDependency::getEnvironmentCom(
							anAvmTransition, aCompiledCode, hasMutableSchedule) );

				anAvmTransition.setEnvironmentInputCom(
						CommunicationDependency::getEnvironmentInputCom(
							anAvmTransition, aCompiledCode, hasMutableSchedule) );

				anAvmTransition.setEnvironmentOutputCom(
						CommunicationDependency::getEnvironmentOutputCom(
							anAvmTransition, aCompiledCode, hasMutableSchedule) );

//				AVM_OS_COUT << "compileTransition:> "
//						<< str_header( anAvmTransition ) << std::endl;
//				anAvmTransition.toStreamStaticCom(AVM_OS_COUT);
			}
		}
	}
	else
	{
		if( OperatorManager::isSchedule(OnRun->getOperator()) )
		{
			OnRun = StatementConstructor::nopCode();
		}
		anAvmTransition.setCode( OnRun );
	}

//	AVM_OS_TRACE << TAB << ">| compiling<transiton>: "
//			<< aTransition.getFullyQualifiedNameID() << std::endl;
}



/*
 * GETTER
 * for transition
 */
Machine * CompilerOfTransition::getTransitionTarget(
		const Transition & aTransition, const BF & smTarget)
{
	if( smTarget.is< Machine >() )
	{
		return( smTarget.to_ptr< Machine >() );
	}
	else if( smTarget.is< Variable >() )
	{
		return( nullptr );
	}
	else
	{
		Machine * tgtMachine = nullptr;

		Machine * srcMachine = aTransition.getContainer()->as_ptr< Machine >();
		if( srcMachine->getNameID() == smTarget.str() )
		{
			return( srcMachine );
		}

		Machine * containerMachine = srcMachine;
		while( containerMachine->isContainerMachine() )
		{
			tgtMachine = containerMachine;
			containerMachine = containerMachine->getContainer()->as_ptr< Machine >();

			tgtMachine = containerMachine->getrecMachine(smTarget.str(), tgtMachine);
			if( tgtMachine != nullptr )
			{
				if( tgtMachine->isContainerMachine()
					&& tgtMachine->getContainer()->to_ptr< Machine >()->
							getSpecifier().isMocStateTransitionStructure() )
				{
					return( tgtMachine );
				}
				else
				{
					incrErrorCount();
					aTransition.errorLocation(AVM_OS_WARN)
							<< "Unexpected transition target without "
							"a STATEMACHINE< or > container :> "
							<< std::endl
							<< TAB << "target state:> " << str_header( tgtMachine )
							<< std::endl
							<< TAB << "target super:> " << str_header(
								tgtMachine->getContainer()->to_ptr< Machine >() )
							<< std::endl
							<< aTransition.toString(AVM_TAB1_INDENT)
							<< std::endl;

					return( tgtMachine );
				}
			}
		}

		if( srcMachine->hasMachine() )
		{
			Machine * tgtMachine =
					srcMachine->getrecMachine(smTarget.str(), nullptr);
			if( tgtMachine != nullptr )
			{
				if( tgtMachine->isContainerMachine()
					&& tgtMachine->getContainer()->to_ptr< Machine >()->
							getSpecifier().isMocStateTransitionStructure() )
				{
					incrWarningCount();
					aTransition.warningLocation(AVM_OS_WARN)
							<< "The transition target is a sub-state"
							" of the transition source "
							<< std::endl
							<< TAB << str_header(
								tgtMachine->getContainer()->to_ptr< Machine >() )
							<< " --> " << str_header( tgtMachine )
							<< std::endl
							<< aTransition.toString(AVM_TAB1_INDENT)
							<< std::endl;
				}
				else
				{
					incrErrorCount();
					aTransition.errorLocation(AVM_OS_WARN)
							<< "Unexpected transition target without "
							"a STATEMACHINE< or > container :> "
							<< std::endl
							<< TAB << "target state:> "
							<< str_header( tgtMachine )
							<< std::endl
							<< TAB << "target super:> " << str_header(
								tgtMachine->getContainer()->to_ptr< Machine >() )
							<< std::endl
							<< aTransition.toString(AVM_TAB1_INDENT)
							<< std::endl;
				}

				return( tgtMachine );
			}
		}

		incrErrorCount();
		aTransition.errorLocation(AVM_OS_WARN)
				<< "Unfound the transition target :> " << smTarget.str()
				<< std::endl
				<< aTransition.toString(AVM_TAB1_INDENT)
				<< std::endl;

		return( nullptr );
	}
}


BF CompilerOfTransition::compileTransitionTarget(
		AvmTransition & anAvmTransition, const BF & smTarget)
{
	if( smTarget.is< Variable >() )
	{
		CompilationEnvironment compilENV(anAvmTransition);

		return( getSymbolTable().searchDataInstance(
				compilENV.mCTX, smTarget.to< Variable >()) );

//		if( not ExpressionTypeChecker::isTyped(TypeManager::MACHINE, smTarget) )
//		{
//			incrErrorCount();
//			anAvmTransition.safeAstElement().errorLocation(AVM_OS_WARN)
//					<< "Unexpected the transition variable target type :> "
//					<< str_header( smTarget.to_ptr< Variable >() ) << std::endl;
//		}
	}

	if( smTarget.is< Machine >() )
	{
		return( getSymbolTable().
				searchInstanceStatic(smTarget.to< Machine >()) );
	}
	else
	{
		BFList foundTarget;
		getSymbolTable().searchMachineInstanceByQualifiedNameID(
				smTarget.str(), foundTarget);
		if( foundTarget.singleton() )
		{
			return( foundTarget.pop_first() );
		}
		else if( foundTarget.populated() )
		{
			incrErrorCount();
			AVM_OS_WARN << "Indeterminism:> found many target state < "
					<< smTarget.str() << " > from program < "
					<< str_header( anAvmTransition ) << " > !!!";
			while( foundTarget.nonempty() )
			{
				AVM_OS_WARN << "\n\tFound :> " << str_header(
					foundTarget.pop_first().to_ptr< InstanceOfMachine >() );
			}

			return( foundTarget.pop_first() );
		}
		else
		{
			incrErrorCount();
			AVM_OS_WARN << "Unfound target state < "
					<< smTarget.str() << " > from program < "
					<< str_header( anAvmTransition ) << " > !!!";
			while( foundTarget.nonempty() )
			{
				AVM_OS_WARN << "\n\tFound :> " << str_header(
						foundTarget.pop_first().to_ptr< InstanceOfMachine >() );
			}

			return( BF::REF_NULL );
		}
	}
}



/**
 * compile
 * list of transition
 */
BFCode CompilerOfTransition::scheduleListOfTransition(
		ExecutableForm & anExecutableForm, const BFList & listOfTransition)
{
	if( listOfTransition.populated() )
	{
		ListOfBFList schedList;
		ListOfInt priorList;
		int priority = 0;

		BFList * tmpList = new BFList();
		schedList.append( tmpList );
		priorList.append( priority );

		ListOfBFList::iterator itSched;
		ListOfBFList::iterator endSched;
		ListOfInt::iterator itPrior;

		// TRI
		for( const auto & itTransition : listOfTransition )
		{
			priority = itTransition.to< AvmTransition >().
					getAstTransition().getPriority();

			itSched = schedList.begin();
			endSched = schedList.end();
			itPrior = priorList.begin();
			for( ; itSched != endSched ; ++itSched , ++itPrior )
			{
				if( (*itPrior) == priority )
				{
					(*itSched)->append( itTransition );

					break;
				}

				else if( (mCurrentMoc->isUserPriorityMinFirst() &&
						((*itPrior) > priority)) ||
						((! mCurrentMoc->isUserPriorityMinFirst()) &&
								((*itPrior) < priority)) )
				{
					tmpList = new BFList();
					tmpList->append( itTransition );

					schedList.insert( itSched , tmpList );
					priorList.insert( itPrior , priority );

					break;
				}
			}

			if( itSched == endSched )
			{
				tmpList = new BFList();
				tmpList->append( itTransition );

				schedList.append( tmpList );
				priorList.append( priority );
			}
		}


		// SCHEDULE
		if( schedList.populated() )
		{
			BFCode aCode(OperatorManager::OPERATOR_PRIOR_GT);

			endSched = schedList.end();
			for( itSched = schedList.begin() ; itSched != endSched ; ++itSched )
			{
				if( (*itSched)->populated() )
				{
					BFCode tmpCode( OperatorManager::OPERATOR_NONDETERMINISM );

					BFList::iterator it = (*itSched)->begin();
					for( ; it != (*itSched)->end() ; ++it )
					{
						tmpCode->append( StatementConstructor::newCode(
								OperatorManager::OPERATOR_INVOKE_TRANSITION,
								(*it)) );
					}

					aCode->append( tmpCode );
				}
				else if( (*itSched)->nonempty() )
				{
					aCode->append( StatementConstructor::newCode(
							OperatorManager::OPERATOR_INVOKE_TRANSITION,
							(*itSched)->last()) );
				}

				delete( (*itSched) );
			}

			return( aCode );
		}

		else
		{
			BFCode aTrans;

			if( schedList.last()->populated() )
			{
				BFCode tmpCode( OperatorManager::OPERATOR_NONDETERMINISM );

				BFList::iterator it = schedList.last()->begin();
				for( ; it != schedList.last()->end() ; ++it )
				{
					tmpCode->append( StatementConstructor::newCode(
							OperatorManager::OPERATOR_INVOKE_TRANSITION, (*it)) );
				}

				aTrans = tmpCode;
			}
			else if( schedList.last()->nonempty() )
			{
				aTrans = StatementConstructor::newCode(
						OperatorManager::OPERATOR_INVOKE_TRANSITION,
						schedList.last()->last());
			}

			delete( schedList.last() );

			return( aTrans );
		}
	}

	else if( listOfTransition.nonempty() )
	{
		return( StatementConstructor::newCode(
				OperatorManager::OPERATOR_INVOKE_TRANSITION,
				listOfTransition.first()) );
	}

	return( BFCode::REF_NULL );
}


BFCode CompilerOfTransition::scheduleListOfTransition(
		ExecutableForm & anExecutableForm,
		const BFList & listOfTransition, const BFList & listOfElseTransition)
{
	if( listOfElseTransition.empty() )
	{
		return scheduleListOfTransition(anExecutableForm, listOfTransition);
	}
	else if( listOfTransition.empty() )
	{
		return scheduleListOfTransition(anExecutableForm, listOfElseTransition);
	}
	else
	{
		return StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_PRIOR_GT,
				scheduleListOfTransition(anExecutableForm, listOfTransition),
				scheduleListOfTransition(anExecutableForm, listOfElseTransition));
	}
}



void CompilerOfTransition::compileStatemachineTransition(
		ExecutableForm & anExecutableForm, const BFCode & runRoutine)
{
	const Machine & aStatemachine = anExecutableForm.getAstMachine();

//	AVM_OS_TRACE << TAB << "<| compiling<transition> of "
//			<< str_header( aStatemachine ) << std::endl;

	bool hasTransition = aStatemachine.hasOutgoingTransition();

	/*
	 * Compiling transition
	 */
	BFList listOfSimpleTransition;
	BFList listOfSimpleElseTransition;

	BFList listOfAbortTransition;
	BFList listOfAbortElseTransition;


	BFList listOfFinalTransition;
	BFList listOfFinalElseTransition;

	BFList listOfInternalTransition;
	BFList listOfInternalElseTransition;

	BFList listOfAutoTransition;
	BFList listOfAutoElseTransition;

	if( hasTransition )
	{
		ListOfAvmTransition usedTransition;

		if( runRoutine.valid() )
		{
			StatementFactory::collectInvokeTransition(
					anExecutableForm, runRoutine, usedTransition);
		}

		BehavioralPart::transition_iterator itTransition =
				aStatemachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endIt =
				aStatemachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endIt ; ++itTransition )
		{
			const BF & compiledTransition =
					anExecutableForm.getTransitionByAstElement(itTransition);

			if( usedTransition.nonempty() && usedTransition.contains(
					compiledTransition.to_ptr< AvmTransition >()) )
			{
				continue;
			}

			switch( (itTransition)->getMocKind() )
			{
				case Transition::MOC_SIMPLE_KIND:
				{
					listOfSimpleTransition.append(compiledTransition);
					break;
				}
				case Transition::MOC_ELSE_KIND:
				case Transition::MOC_SIMPLE_ELSE_KIND:
				{
					listOfSimpleElseTransition.append(compiledTransition);
					break;
				}

				case Transition::MOC_ABORT_KIND:
				{
					listOfAbortTransition.append(compiledTransition);
					break;
				}
				case Transition::MOC_ABORT_ELSE_KIND:
				{
					listOfAbortElseTransition.append(compiledTransition);
					break;
				}

				case Transition::MOC_FINAL_KIND:
				{
					listOfFinalTransition.append(compiledTransition);
					break;
				}
				case Transition::MOC_FINAL_ELSE_KIND:
				{
					listOfFinalElseTransition.append(compiledTransition);
					break;
				}

				case Transition::MOC_INTERNAL_KIND:
				{
					listOfInternalTransition.append(compiledTransition);
					break;
				}
				case Transition::MOC_INTERNAL_ELSE_KIND:
				{
					listOfInternalElseTransition.append(compiledTransition);
					break;
				}

				case Transition::MOC_AUTO_KIND:
				{
					listOfAutoTransition.append(compiledTransition);
					break;
				}
				case Transition::MOC_AUTO_ELSE_KIND:
				{
					listOfAutoElseTransition.append(compiledTransition);
					break;
				}

				case Transition::MOC_UNDEFINED_KIND:
				default:
				{
					incrErrorCount();
					(itTransition)->errorLocation(AVM_OS_WARN)
							<< "Unexpected transition kind:> "
							<< std::endl << (*itTransition) << std::flush;

					break;
				}
			}
		}
	}


	/*
	 * OnRun
	 * whith high priority order
	 *
	 * StrongAbort Transition
	 * ActivityDo
	 * ( Simple Transition or submachine ) depend on MOC
	 * WeakAbort Transition
	 * NormalTerminaison Transition
	 */

	AvmCode::OperandCollectionT listOfOrderArg;

	if( hasTransition && runRoutine.valid() )
	{
		if( aStatemachine.hasModelOfComputation() )
		{

		}

		// Abort Transition
		if( listOfAbortTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(
					anExecutableForm, listOfAbortTransition) );
		}
		// Else Transition< abort >
		if( listOfAbortElseTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(
					anExecutableForm, listOfAbortElseTransition) );
		}

		/*
		 * EVAL
		 * ( Simple Transition or submachine ) depend on MOC
		 */
		if( listOfSimpleTransition.nonempty() && runRoutine.valid() )
		{
			const Operator * op = OperatorManager::OPERATOR_PRIOR_GT;
			if( (mCurrentMoc->isLcaEnabled() &&
					mCurrentMoc->isLcaMinFirst()) ||
					(mCurrentMoc->isSourceEnabled() &&
							mCurrentMoc->isSourceMinFirst()) )
			{
				listOfOrderArg.append( StatementConstructor::xnewCodeFlat(op,
						runRoutine,
						scheduleListOfTransition(
								anExecutableForm, listOfSimpleTransition)) );
			}
			else if( (mCurrentMoc->isLcaEnabled() &&
					(! mCurrentMoc->isLcaMinFirst())) ||
					(mCurrentMoc->isSourceEnabled() &&
							(! mCurrentMoc->isSourceMinFirst())) )
			{
				listOfOrderArg.append( StatementConstructor::xnewCodeFlat(op,
						scheduleListOfTransition(
								anExecutableForm, listOfSimpleTransition),
						runRoutine) );
			}
			else
			{
				op = OperatorManager::OPERATOR_NONDETERMINISM;
				listOfOrderArg.append( StatementConstructor::xnewCodeFlat(op,
						runRoutine,
						scheduleListOfTransition(
								anExecutableForm, listOfSimpleTransition)) );
			}
		}
		else if( listOfSimpleTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(
					anExecutableForm, listOfSimpleTransition) );
		}
		else if( runRoutine.valid() )
		{
			listOfOrderArg.append( runRoutine );
		}

		// Else Transition< simple >
		if( listOfSimpleElseTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(
					anExecutableForm, listOfSimpleElseTransition) );
		}

		// Final Transition

		// Auto Transition
		if( listOfAutoTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(
					anExecutableForm, listOfAutoTransition) );
		}
		// Else Transition< auto >
		if( listOfAutoElseTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(
					anExecutableForm, listOfAutoElseTransition) );
		}

		// Internal Transition
		if( listOfInternalTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(
					anExecutableForm, listOfInternalTransition) );
		}
		// Else Transition< simple >
		if( listOfInternalElseTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(
					anExecutableForm, listOfInternalElseTransition) );
		}
	}
	else if( hasTransition )
	{
		/*
		 * OnRun
		 * StrongAbort Transition >
		 * ActivityDo >
		 * Simple Transition >
		 * WeakAbort Transition >
		 * NormalTerminaison Transition
		 */

		// Abort Transition
		if( listOfAbortTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(anExecutableForm,
					listOfAbortTransition) );
		}
		// Else Transition< abort >
		if( listOfAbortElseTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(
					anExecutableForm, listOfAbortElseTransition) );
		}


		// Simple Transition
		if( listOfSimpleTransition.nonempty()  )
		{
			listOfOrderArg.append( scheduleListOfTransition(anExecutableForm,
					listOfSimpleTransition) );
		}

		// Else Transition< simple >
		if( listOfSimpleElseTransition.nonempty() )
		{
			listOfOrderArg.append( scheduleListOfTransition(anExecutableForm,
					listOfSimpleElseTransition) );
		}

		// Final Transition
	}
	else if( runRoutine.valid() )
	{
		listOfOrderArg.append( runRoutine );
	}


	/*
	 * Assemble OnRun code
	 */
	if( listOfOrderArg.populated() )
	{
		BFCode aCode = StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_PRIOR_GT, listOfOrderArg);

		anExecutableForm.setOnRun( aCode );
	}
	else if( listOfOrderArg.nonempty() )
	{
		if( listOfOrderArg.first().is< AvmCode >() )
		{
			anExecutableForm.setOnRun( listOfOrderArg.first().bfCode() );
		}
		else
		{
			anExecutableForm.setOnRun( StatementConstructor::newCode(
					OperatorManager::OPERATOR_INVOKE_TRANSITION,
					listOfOrderArg.first()) );
		}
	}


	// Transition< final > and Transition< final & else >
	if( listOfFinalTransition.nonempty()
		|| listOfFinalElseTransition.nonempty() )
	{
		anExecutableForm.setOnFinal( StatementConstructor::xnewCodeFlat(
				OperatorManager::OPERATOR_SEQUENCE,
				anExecutableForm.getOnFinal(),
				anExecutableForm.getOnDisable(),
				scheduleListOfTransition(anExecutableForm,
						listOfFinalTransition, listOfFinalElseTransition) ) );
	}

//	AVM_OS_TRACE << TAB << ">| compiling<transition> of "
//			<< str_header( aStatemachine ) << std::endl;
}



void CompilerOfTransition::compileStateForkOutputTransition(
		ExecutableForm & anExecutableForm, const BFCode & runRoutine)
{
	const Machine & aStatemachine = anExecutableForm.getAstMachine();

//	AVM_OS_TRACE << TAB << "<| compiling<transition> of "
//			<< str_header( aStatemachine ) << std::endl;

	/*
	 * Schedule transition
	 */
	BFCode forkCode(OperatorManager::OPERATOR_FORK);

	BehavioralPart::transition_iterator it =
			aStatemachine.getBehavior()->outgoing_transition_begin();
	BehavioralPart::transition_iterator endIt =
			aStatemachine.getBehavior()->outgoing_transition_end();
	for( ; it != endIt ; ++it )
	{
		switch( (it)->getMocKind() )
		{
			case Transition::MOC_SIMPLE_KIND:
			{
				forkCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_INVOKE_TRANSITION,
						anExecutableForm.getTransitionByAstElement(it)) );
				break;
			}

			case Transition::MOC_ABORT_KIND:
			case Transition::MOC_ELSE_KIND:
			case Transition::MOC_FINAL_KIND:
			case Transition::MOC_INTERNAL_KIND:
			case Transition::MOC_AUTO_KIND:
			case Transition::MOC_UNDEFINED_KIND:
			default:
			{
				incrErrorCount();
				(it)->errorLocation(AVM_OS_WARN)
						<< "Unexpected outgoing transition kind:> "
						<< (*it) << "for the pseudostate< fork > << "
						<< str_header( aStatemachine ) << std::endl;
				break;
			}
		}
	}

	anExecutableForm.setOnRun( StatementConstructor::xnewCodeFlat(
			OperatorManager::OPERATOR_SEQUENCE, runRoutine, forkCode) );

//	AVM_OS_TRACE << TAB << ">| compiling<transition> of "
//			<< str_header( aStatemachine ) << std::endl;
}



void CompilerOfTransition::compileStateJoinInputTransition(
		ExecutableForm & anExecutableForm)
{
	const Machine & aStatemachine = anExecutableForm.getAstMachine();

//	AVM_OS_TRACE << TAB << "<| compiling<transition> of "
//			<< str_header( aStatemachine ) << std::endl;

	/*
	 * Schedule transition
	 */
	BFCode syncCode(OperatorManager::OPERATOR_STRONG_SYNCHRONOUS);

	CompilationEnvironment compilENV(anExecutableForm);

	for( const auto & itTransition :
			aStatemachine.getBehavior()->getIncomingTransitions() )
	{
		const Transition & aTransition = itTransition.to< Transition >();

		switch( aTransition.getMocKind() )
		{
			case Transition::MOC_SIMPLE_KIND:
			{
				const BF & bfTransition = getSymbolTable().
						searchTransition(compilENV.mCTX, aTransition);
				if( bfTransition.valid() )
				{
					syncCode->append( StatementConstructor::newCode(
							OperatorManager::OPERATOR_INVOKE_TRANSITION,
							bfTransition) );
				}
				else
				{
					incrErrorCount();
					aTransition.errorLocation(AVM_OS_WARN)
							<< "compileStateJoinInputTransition:> "
							"Unfound incoming transition :"
							<< std::endl << to_stream(aTransition) << std::flush;
				}

				break;
			}

			case Transition::MOC_ABORT_KIND:
			case Transition::MOC_ELSE_KIND:
			case Transition::MOC_FINAL_KIND:
			case Transition::MOC_INTERNAL_KIND:
			case Transition::MOC_AUTO_KIND:
			case Transition::MOC_UNDEFINED_KIND:
			default:
			{
				incrErrorCount();
				aTransition.errorLocation(AVM_OS_WARN)
						<< "Unexpected outgoing transition kind:> "
						<< std::endl << to_stream( aTransition ) << std::flush
						<< "for the pseudostate< fork > << "
						<< str_header( aStatemachine ) << std::endl;
				break;
			}
		}
	}

	anExecutableForm.setOnEnable( StatementConstructor::xnewCodeFlat(
			OperatorManager::OPERATOR_SEQUENCE,
			StatementConstructor::newCode(
					OperatorManager::OPERATOR_JOIN, syncCode),
			anExecutableForm.getOnEnable()) );

//	AVM_OS_TRACE << TAB << ">| compiling<transition> of "
//			<< str_header( aStatemachine ) << std::endl;
}



}

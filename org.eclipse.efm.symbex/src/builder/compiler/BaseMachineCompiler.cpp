/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 nov. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BaseMachineCompiler.h"

#include <builder/primitive/AvmcodeCompiler.h>

#include <fml/expression/AvmCode.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableSystem.h>

#include <sew/Configuration.h>


namespace sep
{


/**
 *******************************************************************************
 * POST-COMPILATION OF EXECUTABLE
 *******************************************************************************
 */

void BaseMachineCompiler::postcompileExecutableSystem()
{
	for( auto & itExec : getConfiguration().getExecutableSystem().getExecutables() )
	{
		optimizeExecutable( const_cast< ExecutableForm & >(
				itExec.to< ExecutableForm >() ));
	}

	// Optimize the system Instance
	InstanceOfMachine * theSystemInstance = getConfiguration().
			getExecutableSystem().getSystemInstance().rawMachine();
	optimizeInstance( theSystemInstance->refExecutable(), theSystemInstance );
}


void BaseMachineCompiler::optimizeExecutable(ExecutableForm & anExecutableForm)
{
	if( anExecutableForm.getLifecycle().isOptimized() ||
		anExecutableForm.getLifecycle().isOptimizing() )
	{
		return;
	}
	else
	{
		anExecutableForm.getwLifecycle().setOptimizing();
	}

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "< begin postcompiling executable routine:> "
			<< anExecutableForm.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	// Optimize all routines which defined the executable's behavior
	optimizeAllBehavioralRoutines( anExecutableForm );

	// Optimize all instance of machine parameters
	optimizeInstance( anExecutableForm );

	anExecutableForm.updateOpcodeFamily();

	anExecutableForm.getwLifecycle().setOptimized();

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT
	<< "> end postcompiling executable routine:> "
			<< anExecutableForm.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
}



void BaseMachineCompiler::optimizeAllBehavioralRoutines(
		ExecutableForm & anExecutableForm)
{
//	AVM_OS_TRACE << TAB << "<| optimizing<machine>: "
//			<< anExecutableForm.getFullyQualifiedNameID() << std::endl;


	/*
	 * onRead / onWrite routines of data
	 */
	mAvmcodeCompiler.optimizeDataRoutine( anExecutableForm );


	/*
	 * onCreate
	 */
	if( anExecutableForm.hasOnCreate() )
	{
		anExecutableForm.setOnCreate(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnCreate()) );
	}

	/*
	 * onInit
	 */
	if( anExecutableForm.hasOnInit() )
	{
		anExecutableForm.setOnInit(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnInit()) );
	}

	/*
	 * onExit
	 */
	if( anExecutableForm.hasOnFinal() )
	{
		anExecutableForm.setOnFinal(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnFinal()) );
	}


	/*
	 * onStart
	 */
	if( anExecutableForm.hasOnStart() )
	{
		anExecutableForm.setOnStart(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnStart()) );
	}

	/*
	 * onStop
	 */
	if( anExecutableForm.hasOnStop() )
	{
		anExecutableForm.setOnStop(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnStop()) );
	}


	/*
	 * onIEnable
	 */
	if( anExecutableForm.hasOnIEnable() )
	{
		anExecutableForm.setOnIEnable(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnIEnable()) );
	}

	/*
	 * onEnable
	 */
	if( anExecutableForm.hasOnEnable() )
	{
		anExecutableForm.setOnEnable(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnEnable()) );
	}


	/*
	 * onIDisable
	 */
	if( anExecutableForm.hasOnIDisable() )
	{
		anExecutableForm.setOnIDisable(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnIDisable()) );
	}

	/*
	 * onDisable
	 */
	if( anExecutableForm.hasOnDisable() )
	{
		anExecutableForm.setOnDisable(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnDisable()) );
	}


	/*
	 * onIAbort
	 */
	if( anExecutableForm.hasOnIAbort() )
	{
		anExecutableForm.setOnIAbort(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnIAbort()) );
	}

	/*
	 * onAbort
	 */
	if( anExecutableForm.hasOnAbort() )
	{
		anExecutableForm.setOnAbort(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnAbort()) );
	}


	/*
	 * onIRun
	 */
	if( anExecutableForm.hasOnIRun() )
	{
		anExecutableForm.setOnIRun(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnIRun()) );
	}

	/*
	 * onRun
	 */
	if( anExecutableForm.hasOnRun() )
	{
		anExecutableForm.setOnRun(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnRun()) );
	}
	else if( anExecutableForm.hasOnIRun() )
	{
		anExecutableForm.setOnRun( anExecutableForm.getOnIRun() );
	}


	/*
	 * onRtc
	 */
	if( anExecutableForm.hasOnRtc() )
	{
		anExecutableForm.setOnRtc(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnRtc()) );
	}


	/*
	 * onConcurrency
	 */
	if( anExecutableForm.hasOnConcurrency() )
	{
		if( not StatementTypeChecker::isEmptySchedule(
				* anExecutableForm.getOnConcurrency()) )
		{
			anExecutableForm.setOnConcurrency(
				mAvmcodeCompiler.optimizeStatement(
					anExecutableForm,
					anExecutableForm.getOnConcurrency()) );
		}
	}

	/*
	 * onSchedule
	 */
	if( anExecutableForm.hasOnSchedule() )
	{
		anExecutableForm.setOnSchedule(
				optimizeSchedulingRoutine(
						anExecutableForm,
						anExecutableForm.getOnSchedule() ) );
	}

	/*
	 * onSynchronize
	 */
	if( anExecutableForm.hasOnSynchronize() )
	{
		anExecutableForm.setOnSynchronize(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm.getOnSynchronize()) );
	}


	/*
	 * all Transition
	 */
	AvmTransition * itTransition;
	std::size_t endOffset = anExecutableForm.getTransition().size();
	for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
	{
		itTransition = anExecutableForm.getTransition().rawAt(offset);

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "< begin postcompiling transition:> "
			<< itTransition->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

		// Optimize all program routine
		mAvmcodeCompiler.optimizeProgramRoutine( *itTransition );

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "> end postcompiling transition:> "
			<< itTransition->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
	}


	/*
	 * all Program
	 */
	AvmProgram * itProg;
	endOffset = anExecutableForm.getProgram().size();
	for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
	{
		itProg = anExecutableForm.getProgram().rawAt(offset);

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "< begin postcompiling avm_program:> "
			<< itProg->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

		// Optimize all program routine
		mAvmcodeCompiler.optimizeProgramRoutine( *itProg );

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "> end postcompiling avm_program:> "
			<< itProg->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
	}

//	AVM_OS_TRACE << TAB << ">| optimizing<machine>: "
//			<< anExecutableForm.getFullyQualifiedNameID() << std::endl << std::endl;
}



void BaseMachineCompiler::optimizeInstance(ExecutableForm & anExecutableForm)
{
//AVM_OS_TRACE << TAB << "<| optimizing<machine>: "
//		<< anExecutableForm.getFullyQualifiedNameID() << std::endl;

	/*
	 * all Program
	 */
	if( anExecutableForm.hasInstanceStatic() )
	{
		TableOfSymbol::const_iterator itMachine =
				anExecutableForm.instance_static_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm.instance_static_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			optimizeInstance(anExecutableForm, (*itMachine).rawMachine());
		}
	}

	if( anExecutableForm.hasInstanceDynamic() )
	{
		TableOfSymbol::const_iterator itMachine =
				anExecutableForm.instance_dynamic_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm.instance_dynamic_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			optimizeInstance(anExecutableForm, (*itMachine).rawMachine());
		}
	}

//AVM_OS_TRACE << TAB << ">| optimizing<machine>: "
//		<< anExecutableForm.getFullyQualifiedNameID() << std::endl << std::endl;
}



void BaseMachineCompiler::optimizeInstance(
		ExecutableForm & theExecutableContainer, InstanceOfMachine * anInstance)
{
	AVM_IF_DEBUG_FLAG( COMPILING )
		AVM_OS_TRACE << INCR_INDENT_TAB
				<< "< begin postcompiling instance of machine parameter :> "
				<< str_header( anInstance ) << std::endl;
	AVM_ENDIF_DEBUG_FLAG( COMPILING )

	// Optimize Executable model if it's not yet
	optimizeExecutable( anInstance->refExecutable() );

	// Optimize all instance routine
	mAvmcodeCompiler.optimizeInstance( theExecutableContainer, anInstance );

	AVM_IF_DEBUG_FLAG( COMPILING )
		AVM_OS_TRACE << TAB_DECR_INDENT
				<< "> end postcompiling instance of machine parameter :> "
				<< str_header( anInstance ) << std::endl;
	AVM_ENDIF_DEBUG_FLAG( COMPILING )
}


/**
 * COMPILING EXECUTABLE SCHEDULER
 * Specific because of dynamic instantiation
 */
BFCode BaseMachineCompiler::compileSchedulerRoutine(
		ExecutableForm & anExecutableForm,
		ListOfInstanceOfMachine & usedInstance, BFCode & aSchedulerCode)
{
	if( aSchedulerCode.invalid() )
	{
		AVM_OS_EXIT( FAILED )
				<< "completeSchedulerRoutine:> Unexpected a << $null<code> >> !!!"
				<< SEND_EXIT;

		return( aSchedulerCode );
	}
	else if( aSchedulerCode->noOperand() )
	{
		return( aSchedulerCode );
	}

	if( aSchedulerCode->hasOneOperand()
		&& aSchedulerCode->first().is< InstanceOfMachine >()
		&& OperatorManager::isActivity( aSchedulerCode->getOperator() ) )
	{
		InstanceOfMachine * anInstance =
				aSchedulerCode->first().to_ptr< InstanceOfMachine >();

		if( anInstance->getSpecifier().isDesignInstanceStatic() )
		{
			return( aSchedulerCode );
		}

		else if( anExecutableForm.hasOnConcurrency() )
		{
			BFCode compilCode( anExecutableForm.getOnConcurrencyOperator() );

			compileSchedulerRoutine(anExecutableForm,
					usedInstance, aSchedulerCode, compilCode);

			return( compilCode );
		}
		else if( anInstance->getSpecifier().isDesignPrototypeStatic()
				&& anInstance->isAutoStart() )
		{
			return( aSchedulerCode );
		}
		else
		{
			TableOfSymbol::const_iterator itMachine =
					anExecutableForm.instance_static_begin();
			TableOfSymbol::const_iterator endMachine =
					anExecutableForm.instance_static_end();
			for( ; itMachine != endMachine ; ++itMachine )
			{
				if( anInstance->getSpecifier().hasDesignModel()
					&& (anInstance != (*itMachine).rawMachine())
					&& (*itMachine).isInstanceModel( anInstance )
					&& (not usedInstance.contains((*itMachine).rawMachine())) )
				{
					usedInstance.append( (*itMachine).rawMachine() );

					return( StatementConstructor::newCode(
							aSchedulerCode->getOperator(), (*itMachine)) );
				}
			}

			AVM_OS_FATAL_ERROR_EXIT
					<< "completeSchedulerRoutine:> Failed !!!\n"
					<< aSchedulerCode
					<< SEND_EXIT;

			return( aSchedulerCode );
		}
	}

	else if( aSchedulerCode->isOpCode(AVM_OPCODE_IF) )
	{
		BFCode compilCode( aSchedulerCode->getOperator() );

		compilCode->append(
				mAvmcodeCompiler.decode_compileExpression(
						anExecutableForm, aSchedulerCode->first()) );

		compileSchedulerRoutine(anExecutableForm, usedInstance,
				aSchedulerCode->second().bfCode(), compilCode);

		return( compilCode );
	}
	else if( aSchedulerCode->isOpCode(AVM_OPCODE_IFE) )
	{
		BFCode compilCode( aSchedulerCode->getOperator() );

		compilCode->append(
				mAvmcodeCompiler.decode_compileExpression(
						anExecutableForm, aSchedulerCode->first()) );

		compileSchedulerRoutine(anExecutableForm, usedInstance,
				aSchedulerCode->second().bfCode(), compilCode);

		compileSchedulerRoutine(anExecutableForm, usedInstance,
				aSchedulerCode->third().bfCode(), compilCode);

		return( compilCode );
	}

	else
	{
		BFCode compilCode( aSchedulerCode->getOperator() );

		for( auto & itOperand : aSchedulerCode.getOperands() )
		{
			if( itOperand.is< AvmCode >() )
			{
				compileSchedulerRoutine(anExecutableForm,
						usedInstance, itOperand.bfCode(), compilCode);
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "completeSchedulerRoutine:> Unexpected arg :>\n"
						<< itOperand
						<< SEND_EXIT;

				compilCode->append( itOperand );
			}
		}

		return( compilCode );
	}
}


void BaseMachineCompiler::compileSchedulerRoutine(
		ExecutableForm & anExecutableForm,
		ListOfInstanceOfMachine & usedInstance,
		BFCode & aSchedulerCode, BFCode & compilCode)
{
	if( aSchedulerCode->hasOneOperand()
		&& aSchedulerCode->first().is< InstanceOfMachine >()
		&& OperatorManager::isActivity( aSchedulerCode->getOperator() ) )
	{
		InstanceOfMachine * anInstance =
				aSchedulerCode->first().to_ptr< InstanceOfMachine >();

		if( anInstance->getSpecifier().isDesignInstanceStatic() )
		{
			compilCode.append( aSchedulerCode );
		}
		else
		{
			BFCode modelScheduler;

			if( anInstance->getSpecifier().isDesignPrototypeStatic() )
			{
				if( anInstance->isAutoStart() )
				{
					AVM_OS_ASSERT_FATAL_ERROR_EXIT( compilCode->hasOperand()
						|| (anInstance->getExecutable() != (& anExecutableForm)) )
							<< "Infinite recursive loop detection with "
								"instance << " << str_header( anInstance )
							<< " >> in the schedule code of the executable << "
							<< str_header( anExecutableForm ) << " >> !!!"
							<< SEND_EXIT;

					compilCode.append( aSchedulerCode );
				}

				if( anInstance->hasInstanceModel() )
				{
					anInstance = anInstance->getInstanceModel();

					modelScheduler = StatementConstructor::newCode(
						aSchedulerCode->getOperator(), INCR_BF(anInstance) );
				}
				else
				{
					AVM_OS_ASSERT_WARNING_ALERT(
							not anInstance->getSpecifier().isComponentSystem() )
							<< "Unexpected the system instance << "
							<< str_header( anInstance )
							<< " >> in the schedule code of the executable << "
							<< str_header( anExecutableForm ) << " >> !!!"
							<< SEND_EXIT;
				}
			}
			else
			{
				modelScheduler = aSchedulerCode;
			}

			TableOfSymbol::const_iterator itMachine =
					anExecutableForm.instance_static_begin();
			TableOfSymbol::const_iterator endMachine =
					anExecutableForm.instance_static_end();
			for( ; itMachine != endMachine ; ++itMachine )
			{
				if( anInstance == (*itMachine).getInstanceModel() &&
					(not usedInstance.contains((*itMachine).rawMachine())) )
				{
					compilCode->append( StatementConstructor::newCode(
							aSchedulerCode->getOperator(), (*itMachine)) );

					usedInstance.append( (*itMachine).rawMachine() );
				}
			}

			if( modelScheduler.valid() )
			{
				compilCode.append( modelScheduler );
			}
		}
	}
	else
	{
		compilCode->append( compileSchedulerRoutine(
				anExecutableForm, usedInstance, aSchedulerCode) );
	}
}


BFCode BaseMachineCompiler::compileSchedulerRoutine(
		ExecutableForm & anExecutableForm, BFCode & aCode)
{
	if( OperatorManager::isSchedule( aCode->getOperator() )
		|| aCode->hasOpCode(AVM_OPCODE_AND_THEN, AVM_OPCODE_OR_ELSE) )
	{
		BFCode schedCode( aCode->getOperator() );

		for( auto & itOperand : aCode.getOperands() )
		{
			if( itOperand.is< AvmCode >() )
			{
				schedCode->append( compileSchedulerRoutine(
						anExecutableForm, itOperand.bfCode() ) );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "compileSchedulerRoutine:> Unexpected arg :>\n"
						<< itOperand
						<< SEND_EXIT;

				schedCode->append( itOperand );
			}
		}

		return( schedCode );
	}
	else if( OperatorManager::isActivity( aCode->getOperator() ) )
	{
		return( mAvmcodeCompiler.compileStatement(anExecutableForm, aCode) );
	}
	else if( aCode->isOpCode(AVM_OPCODE_IF) )
	{
		BFCode schedCode( aCode->getOperator() );
		schedCode->append(
				mAvmcodeCompiler.decode_compileExpression(
						anExecutableForm, aCode->first()) );
		schedCode->append(
				compileSchedulerRoutine(
						anExecutableForm, aCode->second().bfCode()) );

		return( schedCode );
	}
	else if( aCode->isOpCode(AVM_OPCODE_IFE) )
	{
		BFCode schedCode( aCode->getOperator() );
		schedCode->append(
				mAvmcodeCompiler.decode_compileExpression(
						anExecutableForm, aCode->first()) );
		schedCode->append(
				compileSchedulerRoutine(
						anExecutableForm, aCode->second().bfCode()) );
		schedCode->append(
				compileSchedulerRoutine(
						anExecutableForm, aCode->third().bfCode()) );

		return( schedCode );
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "compileSchedulerRoutine:> Unexpected code :>\n" << aCode
				<< SEND_EXIT;
		return( aCode );
	}
}


BFCode BaseMachineCompiler::optimizeSchedulingRoutine(
		ExecutableForm & anExecutableForm, BFCode & aSchedulerCode)
{
	if( aSchedulerCode.invalid() )
	{
		AVM_OS_EXIT( FAILED )
				<< "completeSchedulerRoutine:> Unexpected a << null<code> >> !!!"
				<< SEND_EXIT;

		return( aSchedulerCode );
	}
	else if( aSchedulerCode->noOperand() )
	{
		return( aSchedulerCode );
	}

	if( aSchedulerCode->hasOneOperand()
		&& aSchedulerCode->first().is< InstanceOfMachine >()
		&& OperatorManager::isActivity( aSchedulerCode->getOperator() ) )
	{
		InstanceOfMachine * anInstance =
				aSchedulerCode->first().to_ptr< InstanceOfMachine >();

		if( anInstance->getSpecifier().isDesignInstanceStatic() )
		{
			return( aSchedulerCode );
		}

		else if( anInstance->getSpecifier().isDesignPrototypeStatic() )
		{
			if( anInstance->isAutoStart() )
			{
				return( aSchedulerCode );
			}
			else if( anInstance->hasPossibleDynamicInstanciation() )
			{
				return( StatementConstructor::newCode(
						aSchedulerCode->getOperator(),
						INCR_BF(anInstance->getInstanceModel()) ) );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "optimizeSchedulingRoutine:> "
							"Unexpected non auto-start prototype machine :>\n"
						<< to_stream( anInstance )
						<< SEND_EXIT;

				return( aSchedulerCode );
			}
		}

		else if( anInstance->getSpecifier().isDesignModel() )
		{
			if( anInstance->hasPossibleDynamicInstanciation() )
			{
				return( aSchedulerCode );
			}
			else
			{
				return( BFCode::REF_NULL );
			}
		}
	}

	else
	{
		BFCode optiCode( aSchedulerCode->getOperator() );
		BFCode argCode;

		for( auto & itOperand : aSchedulerCode.getOperands() )
		{
			if( itOperand.is< AvmCode >() )
			{
				argCode = optimizeSchedulingRoutine(
						anExecutableForm, itOperand.bfCode() );

				if( argCode.valid() )
				{
					optiCode->append( argCode );
				}
			}
			else
			{
				optiCode->append( itOperand );
			}
		}

		if( optiCode->noOperand() )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "optimizeSchedulingRoutine:> "
						"Unexpected scheduler code :>\n"
					<< aSchedulerCode
					<< SEND_EXIT;
		}

		return( optiCode );
	}

	return( aSchedulerCode );
//	return( mAvmcodeCompiler.optimizeStatement(anExecutableForm, aCode) );
}


} /* namespace sep */

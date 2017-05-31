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
	TableOfExecutableForm::const_raw_iterator itExec =
			getConfiguration().getExecutableSystem().getExecutables().begin();
	TableOfExecutableForm::const_raw_iterator endExec =
			getConfiguration().getExecutableSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		optimizeExecutable( itExec );
	}

	// Optimize the system Instance
	InstanceOfMachine * theSystemInstance = getConfiguration().
			getExecutableSystem().getSystemInstance().rawMachine();
	optimizeInstance( theSystemInstance->getExecutable(), theSystemInstance );
}


void BaseMachineCompiler::optimizeExecutable(ExecutableForm * anExecutableForm)
{
	if( anExecutableForm->isOptimizedFlag() )
	{
		return;
	}

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "< begin postcompiling executable routine:> "
			<< anExecutableForm->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	// Optimize all routines which defined the executable's behavior
	optimizeAllBehavioralRoutines( anExecutableForm );

	// Optimize all instance of machine parameters
	optimizeInstance( anExecutableForm );

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT
	<< "> end postcompiling executable routine:> "
			<< anExecutableForm->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	anExecutableForm->setOptimizedFlag();
}



void BaseMachineCompiler::optimizeAllBehavioralRoutines(
		ExecutableForm * anExecutableForm)
{
//	AVM_OS_TRACE << TAB << "<| optimizing<machine>: "
//			<< anExecutableForm->getFullyQualifiedNameID() << std::endl;


	/*
	 * onRead / onWrite routines of data
	 */
	mAvmcodeCompiler.optimizeDataRoutine( anExecutableForm );


	/*
	 * onCreate
	 */
	if( anExecutableForm->hasOnCreate() )
	{
		anExecutableForm->setOnCreate(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnCreate()) );
	}

	/*
	 * onInit
	 */
	if( anExecutableForm->hasOnInit() )
	{
		anExecutableForm->setOnInit(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnInit()) );
	}

	/*
	 * onExit
	 */
	if( anExecutableForm->hasOnFinal() )
	{
		anExecutableForm->setOnFinal(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnFinal()) );
	}


	/*
	 * onStart
	 */
	if( anExecutableForm->hasOnStart() )
	{
		anExecutableForm->setOnStart(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnStart()) );
	}

	/*
	 * onStop
	 */
	if( anExecutableForm->hasOnStop() )
	{
		anExecutableForm->setOnStop(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnStop()) );
	}


	/*
	 * onIEnable
	 */
	if( anExecutableForm->hasOnIEnable() )
	{
		anExecutableForm->setOnIEnable(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnIEnable()) );
	}

	/*
	 * onEnable
	 */
	if( anExecutableForm->hasOnEnable() )
	{
		anExecutableForm->setOnEnable(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnEnable()) );
	}


	/*
	 * onIDisable
	 */
	if( anExecutableForm->hasOnIDisable() )
	{
		anExecutableForm->setOnIDisable(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnIDisable()) );
	}

	/*
	 * onDisable
	 */
	if( anExecutableForm->hasOnDisable() )
	{
		anExecutableForm->setOnDisable(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnDisable()) );
	}


	/*
	 * onIAbort
	 */
	if( anExecutableForm->hasOnIAbort() )
	{
		anExecutableForm->setOnIAbort(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnIAbort()) );
	}

	/*
	 * onAbort
	 */
	if( anExecutableForm->hasOnAbort() )
	{
		anExecutableForm->setOnAbort(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnAbort()) );
	}


	/*
	 * onIRun
	 */
	if( anExecutableForm->hasOnIRun() )
	{
		anExecutableForm->setOnIRun(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnIRun()) );
	}

	/*
	 * onRun
	 */
	if( anExecutableForm->hasOnRun() )
	{
		anExecutableForm->setOnRun(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnRun()) );
	}
	else if( anExecutableForm->hasOnIRun() )
	{
		anExecutableForm->setOnRun( anExecutableForm->getOnIRun() );
	}


	/*
	 * onRtc
	 */
	if( anExecutableForm->hasOnRtc() )
	{
		anExecutableForm->setOnRtc(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnRtc()) );
	}


	/*
	 * onConcurrency
	 */
	if( anExecutableForm->hasOnConcurrency() )
	{
		if( not StatementTypeChecker::isEmptySchedule(
				anExecutableForm->getOnConcurrency()) )
		{
			anExecutableForm->setOnConcurrency(
				mAvmcodeCompiler.optimizeStatement(
					anExecutableForm,
					anExecutableForm->getOnConcurrency()) );
		}
	}

	/*
	 * onSchedule
	 */
	if( anExecutableForm->hasOnSchedule() )
	{
		anExecutableForm->setOnSchedule(
				optimizeSchedulingRoutine(
						anExecutableForm,
						anExecutableForm->getOnSchedule() ) );
	}

	/*
	 * onSynchronize
	 */
	if( anExecutableForm->hasOnSynchronize() )
	{
		anExecutableForm->setOnSynchronize(
				mAvmcodeCompiler.optimizeStatement(
						anExecutableForm,
						anExecutableForm->getOnSynchronize()) );
	}


	/*
	 * all Transition
	 */
	AvmTransition * itTransition;
	avm_size_t endOffset = anExecutableForm->getTransition().size();
	for( avm_size_t offset = 0 ; offset < endOffset ; ++offset )
	{
		itTransition = anExecutableForm->getTransition().rawAt(offset);

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "< begin postcompiling transition:> "
			<< itTransition->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

		// Optimize all program routine
		mAvmcodeCompiler.optimizeProgramRoutine( itTransition );

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
	endOffset = anExecutableForm->getProgram().size();
	for( avm_size_t offset = 0 ; offset < endOffset ; ++offset )
	{
		itProg = anExecutableForm->getProgram().rawAt(offset);

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "< begin postcompiling avm_program:> "
			<< itProg->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

		// Optimize all program routine
		mAvmcodeCompiler.optimizeProgramRoutine( itProg );

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "> end postcompiling avm_program:> "
			<< itProg->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
	}

//	AVM_OS_TRACE << TAB << ">| optimizing<machine>: "
//			<< anExecutableForm->getFullyQualifiedNameID() << std::endl << std::endl;
}



void BaseMachineCompiler::optimizeInstance(ExecutableForm * anExecutableForm)
{
//AVM_OS_TRACE << TAB << "<| optimizing<machine>: "
//		<< anExecutableForm->getFullyQualifiedNameID() << std::endl;

	/*
	 * all Program
	 */
	if( anExecutableForm->hasInstanceStatic() )
	{
		TableOfSymbol::const_iterator itMachine =
				anExecutableForm->instance_static_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm->instance_static_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			optimizeInstance(anExecutableForm, (*itMachine).rawMachine());
		}
	}

	if( anExecutableForm->hasInstanceDynamic() )
	{
		TableOfSymbol::const_iterator itMachine =
				anExecutableForm->instance_dynamic_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm->instance_dynamic_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			optimizeInstance(anExecutableForm, (*itMachine).rawMachine());
		}
	}

//AVM_OS_TRACE << TAB << ">| optimizing<machine>: "
//		<< anExecutableForm->getFullyQualifiedNameID() << std::endl << std::endl;
}



void BaseMachineCompiler::optimizeInstance(
		ExecutableForm * theExecutableContainer, InstanceOfMachine * anInstance)
{
	AVM_IF_DEBUG_FLAG( COMPILING )
		AVM_OS_TRACE << INCR_INDENT_TAB
				<< "< begin postcompiling instance of machine parameter :> "
				<< str_header( anInstance ) << std::endl;
	AVM_ENDIF_DEBUG_FLAG( COMPILING )

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
		ExecutableForm * anExecutableForm,
		ListOfInstanceOfMachine & usedInstance,
		const BFCode & aSchedulerCode)
{
	if( aSchedulerCode.invalid() )
	{
		AVM_OS_EXIT( FAILED )
				<< "completeSchedulerRoutine:> Unexpected a << null<code> >> !!!"
				<< SEND_EXIT;

		return( aSchedulerCode );
	}
	else if( aSchedulerCode->empty() )
	{
		return( aSchedulerCode );
	}

	if( aSchedulerCode->singleton()
		&& aSchedulerCode->first().is< InstanceOfMachine >()
		&& OperatorManager::isActivity( aSchedulerCode->getOperator() ) )
	{
		InstanceOfMachine * anInstance =
				aSchedulerCode->first().to_ptr< InstanceOfMachine >();

		if( anInstance->getSpecifier().isDesignInstanceStatic() )
		{
			return( aSchedulerCode );
		}

		else if( anExecutableForm->hasOnConcurrency() )
		{
			BFCode compilCode( anExecutableForm->getOnConcurrencyOperator() );

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
					anExecutableForm->instance_static_begin();
			TableOfSymbol::const_iterator endMachine =
					anExecutableForm->instance_static_end();
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

	else
	{
		BFCode compilCode( aSchedulerCode->getOperator() );

		AvmCode::iterator itArg = aSchedulerCode->begin();
		AvmCode::iterator endArg = aSchedulerCode->end();
		for( ; itArg != endArg ; ++itArg )
		{
			if( (*itArg).is< AvmCode >() )
			{
				compileSchedulerRoutine(anExecutableForm,
						usedInstance, (*itArg).bfCode(), compilCode);
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "completeSchedulerRoutine:> Unexpected arg :>\n"
						<< (*itArg)
						<< SEND_EXIT;

				compilCode->append( *itArg );
			}
		}

		return( compilCode );
	}
}


void BaseMachineCompiler::compileSchedulerRoutine(
		ExecutableForm * anExecutableForm,
		ListOfInstanceOfMachine & usedInstance,
		const BFCode & aSchedulerCode, BFCode & compilCode)
{
	if( aSchedulerCode->singleton() &&
		aSchedulerCode->first().is< InstanceOfMachine >() &&
		OperatorManager::isActivity( aSchedulerCode->getOperator() ) )
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
					AVM_OS_ASSERT_FATAL_ERROR_EXIT( compilCode->nonempty()
						|| (anInstance->getExecutable() != anExecutableForm) )
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
					anExecutableForm->instance_static_begin();
			TableOfSymbol::const_iterator endMachine =
					anExecutableForm->instance_static_end();
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
		ExecutableForm * anExecutableForm, const BFCode & aCode)
{
	if( OperatorManager::isSchedule( aCode->getOperator() ) )
	{
		BFCode schedCode( aCode->getOperator() );

		AvmCode::iterator itArg = aCode->begin();
		AvmCode::iterator endArg = aCode->end();
		for( ; itArg != endArg ; ++itArg )
		{
			if( (*itArg).is< AvmCode >() )
			{
				schedCode->append( compileSchedulerRoutine(
						anExecutableForm, (*itArg).bfCode() ) );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "compileSchedulerRoutine:> Unexpected arg :>\n"
						<< (*itArg)
						<< SEND_EXIT;

				schedCode->append( *itArg );
			}
		}

		return( schedCode );
	}
	else if( OperatorManager::isActivity( aCode->getOperator() ) )
	{
		return( mAvmcodeCompiler.compileStatement(anExecutableForm, aCode) );
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
		ExecutableForm * anExecutableForm, const BFCode & aSchedulerCode)
{
	if( aSchedulerCode.invalid() )
	{
		AVM_OS_EXIT( FAILED )
				<< "completeSchedulerRoutine:> Unexpected a << null<code> >> !!!"
				<< SEND_EXIT;

		return( aSchedulerCode );
	}
	else if( aSchedulerCode->empty() )
	{
		return( aSchedulerCode );
	}

	if( aSchedulerCode->singleton() &&
		aSchedulerCode->first().is< InstanceOfMachine >() &&
		OperatorManager::isActivity( aSchedulerCode->getOperator() ) )
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

		AvmCode::iterator itArg = aSchedulerCode->begin();
		AvmCode::iterator endArg = aSchedulerCode->end();
		for( ; itArg != endArg ; ++itArg )
		{
			if( (*itArg).is< AvmCode >() )
			{
				argCode = optimizeSchedulingRoutine(
						anExecutableForm, (*itArg).bfCode() );

				if( argCode.valid() )
				{
					optiCode->append( argCode );
				}
			}
			else
			{
				optiCode->append( *itArg );
			}
		}

		if( optiCode->empty() )
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

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Loader.h"

#include <builder/primitive/AvmcodeCompiler.h>

#include <builder/Builder.h>
#include <computer/ExecutionEnvironment.h>

#include <fml/buffer/BaseBufferForm.h>
#include <fml/buffer/BroadcastBuffer.h>
#include <fml/buffer/FifoBuffer.h>
#include <fml/buffer/LifoBuffer.h>
#include <fml/buffer/MultiFifoBuffer.h>
#include <fml/buffer/MultiLifoBuffer.h>
#include <fml/buffer/RamBuffer.h>
#include <fml/buffer/SetBuffer.h>

#include <fml/common/ModifierElement.h>

#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/Router.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinQueue.h>
#include <fml/expression/BuiltinContainer.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/infrastructure/Buffer.h>

#include <fml/operator/OperatorManager.h>

#include <fml/symbol/Symbol.h>
#include <fml/symbol/TableOfSymbol.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/Message.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>
#include <fml/runtime/RuntimeLib.h>
#include <fml/runtime/TableOfData.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/ClassTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/TypeManager.h>

#include <sew/Configuration.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
Loader::Loader(Configuration & aConfiguration, Builder & aBuilder,
		AvmPrimitiveProcessor & aPrimitiveProcessor)
: mConfiguration( aConfiguration ),
mBuilder( aBuilder ),
ENV( aPrimitiveProcessor ),
mOnCreateRoutime( )
{
	//!! NOTHING
}

/**
 * CONFIGURE
 */
bool Loader::configure()
{
	//!! NOTHING

	return( true );
}


/**
 * RUNNING onCREATE
 * mOnCreateRoutime
 */
bool Loader::finalizeRunningOnCreate(
		const BaseEnvironment & ENV, ExecutionData & anED)
{
	if( hasOnCreateRoutime() )
	{
		// Save current active RID
		RuntimeID saveRID = anED.getRID();

		for( const auto & itRID : getOnCreateRoutime() )
		{
			ExecutionEnvironment tmpENV(ENV, anED, itRID, itRID.getOnCreate() );

			if( tmpENV.run(PROCESS_CREATING_STATE) )
			{
				tmpENV.outEDS.pop_last_to( anED );

				if( tmpENV.outEDS.nonempty() )
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unsupported << onCreate Primitive >> "
									"which execution create more than one "
									"Execution Context :>\n"
							<< itRID.getOnCreate()->toString( AVM_TAB1_INDENT )
							<< SEND_ALERT;

					return( false );
				}

				anED.mwsetRuntimeFormState(itRID,
						PROCESS_CREATING_STATE, PROCESS_DISABLED_STATE);
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Failed to eval << onCreate Routine >> "
								"on initial Execution Context :>\n"
						<< tmpENV.inCODE->toString( AVM_TAB1_INDENT )
						<< SEND_ALERT;

				return( false );
			}
		}

		resetOnCreateRoutime();

		// Restore current active RID
		anED.setRID( saveRID );
	}

	return( true );
}



/**
 * loadSchedulerCode
 * for onSchedule Routine
 */
BFCode Loader::loadSchedulerCode(
		ExecutionData & anED, const RuntimeForm & aRF,
		const BFCode & aSchedulerCode, bool isStaticLoading)
{
	if( aSchedulerCode.invalid() )
	{
		AVM_OS_EXIT( FAILED )
				<< "loadSchedulerCode:> Unexpected a << $null<code> >> !!!"
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

		if( isStaticLoading
			&& anInstance->hasRuntimeRID()
			&& anED.isAlive( anInstance->getRuntimeRID() ) )
		{
			return( StatementConstructor::newOptiNopCode(
					aSchedulerCode->getOperator(),
					anInstance->getRuntimeRID(), AVM_ARG_MACHINE_RID) );
		}
		else
		{
			if( aRF.refExecutable().hasOnConcurrency() )
			{
				BFCode loadCode( aRF.refExecutable().getOnConcurrencyOperator() );

				loadSchedulerCode(anED, aRF, aSchedulerCode,
						loadCode, isStaticLoading);

				return( mBuilder.getAvmcodeCompiler().optimizeStatement(
						aRF.refExecutable(), loadCode) );
			}
			else
			{
				TableOfRuntimeID::iterator itChild = aRF.getChildTable()->begin();
				TableOfRuntimeID::iterator endChild = aRF.getChildTable()->end();
				for( ; itChild != endChild ; ++itChild )
				{
					if( anInstance->getSpecifier().hasDesignInstanceStatic()
						&& (anInstance == (*itChild).getInstance())
						&& anED.isAlive( *itChild ) )
					{
						return( StatementConstructor::newOptiNopCode(
								aSchedulerCode->getOperator(),
								(*itChild), AVM_ARG_MACHINE_RID) );
					}
					else if( anInstance->getSpecifier().hasDesignModel()
							&& (*itChild).isDynamicLoaded()
							&& (anInstance == (*itChild).
									getInstance()->getInstanceModel())
							&& anED.isAlive( *itChild ) )
					{
						return( StatementConstructor::newOptiNopCode(
								aSchedulerCode->getOperator(),
								(*itChild), AVM_ARG_MACHINE_RID) );
					}
				}

				AVM_OS_FATAL_ERROR_EXIT
						<< "loadSchedulerCode:> Failed !!!" << aSchedulerCode
						<< SEND_EXIT;

				return( aSchedulerCode );
			}
		}
	}

	else if( aSchedulerCode->isOpCode(AVM_OPCODE_IF) )
	{
		BFCode loadCode( aSchedulerCode->getOperator() );

		loadCode->append( aSchedulerCode->first() );

		loadSchedulerCode(anED, aRF,
				aSchedulerCode->second().bfCode(), loadCode, isStaticLoading);

		return( mBuilder.getAvmcodeCompiler().optimizeStatement(
				aRF.refExecutable(), loadCode) );
	}
	else if( aSchedulerCode->isOpCode(AVM_OPCODE_IFE) )
	{
		BFCode loadCode( aSchedulerCode->getOperator() );

		loadCode->append( aSchedulerCode->first() );

		loadSchedulerCode(anED, aRF,
				aSchedulerCode->second().bfCode(), loadCode, isStaticLoading);

		loadSchedulerCode(anED, aRF,
				aSchedulerCode->third().bfCode(), loadCode, isStaticLoading);

		return( mBuilder.getAvmcodeCompiler().optimizeStatement(
				aRF.refExecutable(), loadCode) );
	}

	else
	{
		BFCode loadCode( aSchedulerCode->getOperator() );

		for( const auto & itArg : aSchedulerCode->getOperands() )
		{
			if( itArg.is< AvmCode >() )
			{
				loadSchedulerCode(anED, aRF,
						itArg.bfCode(), loadCode, isStaticLoading);
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "loadSchedulerCode:> Unexpected arg :>"
						<< itArg
						<< SEND_EXIT;

				loadCode->append( itArg );
			}
		}

		return( mBuilder.getAvmcodeCompiler().optimizeStatement(
				aRF.refExecutable(), loadCode) );
	}
}


void Loader::loadSchedulerCode(ExecutionData & anED,
		const RuntimeForm & aRF, const BFCode & aSchedulerCode,
		BFCode & loadCode, bool isStaticLoading)
{
	if( aSchedulerCode->hasOneOperand()
		&& aSchedulerCode->first().is< InstanceOfMachine >()
		&& OperatorManager::isActivity( aSchedulerCode->getOperator() ) )
	{
		InstanceOfMachine * anInstance =
				aSchedulerCode->first().to_ptr< InstanceOfMachine >();

		if( isStaticLoading
			&& anInstance->hasRuntimeRID()
			&& anED.isAlive( anInstance->getRuntimeRID() ) )
		{
			loadCode->append( StatementConstructor::newOptiNopCode(
					aSchedulerCode->getOperator(),
					anInstance->getRuntimeRID(), AVM_ARG_MACHINE_RID) );
		}
		else
		{
			TableOfRuntimeID::iterator itChild = aRF.getChildTable()->begin();
			TableOfRuntimeID::iterator endChild = aRF.getChildTable()->end();
			for( ; itChild != endChild ; ++itChild )
			{
				if( anInstance->getSpecifier().hasDesignInstanceStatic()
					&& (anInstance == (*itChild).getInstance())
					&& anED.isAlive( *itChild ) )
				{
					loadCode->append( StatementConstructor::newOptiNopCode(
							aSchedulerCode->getOperator(),
							(*itChild), AVM_ARG_MACHINE_RID) );
				}
				else if( anInstance->getSpecifier().hasDesignModel()
						&& (*itChild).isDynamicLoaded()
						&& (anInstance == (*itChild).
								getInstance()->getInstanceModel())
						&& anED.isAlive( *itChild ) )
				{
					loadCode->append( StatementConstructor::newOptiNopCode(
							aSchedulerCode->getOperator(),
							(*itChild), AVM_ARG_MACHINE_RID) );
				}
			}
		}
	}
	else
	{
		loadCode->append(
				loadSchedulerCode(anED, aRF,
						aSchedulerCode, isStaticLoading) );
	}
}


void Loader::setRuntimeSchedulerCode(ExecutionData & anED, RuntimeForm & aRF,
		const ExecutableForm & anExecutable, bool isStaticLoading)
{
	BFCode scheduleCode = loadSchedulerCode(anED, aRF,
			anExecutable.getOnSchedule(), isStaticLoading);

	if( (not aRF.hasOnDefer())
		&& scheduleCode->isOpCode(AVM_OPCODE_PARTIAL_ORDER) )
	{
		aRF.setOnSchedule( scheduleCode );

		if( scheduleCode->first().is< AvmCode >() )
		{
			aRF.setOnDefer( scheduleCode->first().bfCode() );
		}
	}
	else
	{
		aRF.setOnSchedule( scheduleCode );
	}
}


/**
 * loadSystemInstance
 */
RuntimeForm * Loader::loadSystemInstance(ExecutionData & anED,
		const RuntimeID & aParentRID, InstanceOfMachine * aMachine,
		int & thePid, avm_offset_t & theOffset)
{
AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "< begin loading system instance < "
			<< aMachine->getFullyQualifiedNameID() << " >"
			<< std::endl
			<< TAB << "\t>>>> parent is: "
			<< std::endl;

	aParentRID.toStream(AVM_OS_TRACE << INCR2_INDENT);

	AVM_OS_TRACE << EOL_DECR2_INDENT;
AVM_ENDIF_DEBUG_FLAG( LOADING )


	// PID & OFFSET for the runtime machine
	int pid = thePid++;
	avm_offset_t offset = theOffset++;

	RuntimeID loadMachineRID(aParentRID, pid, offset, aMachine);

	mConfiguration.appendRID( loadMachineRID );

	if( aMachine->refExecutable().hasSingleRuntimeInstance() )
	{
		aMachine->setRuntimeRID(loadMachineRID);
	}

	RuntimeForm * aRF = new RuntimeForm( loadMachineRID );

	anED.saveRuntimeForm(offset, aRF);

	if( aMachine->hasOnCreate() )
	{
		mOnCreateRoutime.append( loadMachineRID );

		anED.setRuntimeFormState(offset, PROCESS_CREATING_STATE);
	}
	else
	{
		anED.setRuntimeFormState(offset, PROCESS_DISABLED_STATE);
	}

//!?! Code pour évolution future
//	aRF->setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
//	aRF->setNodeTimedCondition( ExpressionConstant::BOOLEAN_TRUE );


	if( aParentRID.valid() )
	{
		anED.getRuntime(aParentRID).appendChild( loadMachineRID );
	}

	ExecutableForm & anExecutable = aMachine->refExecutable();

	// Load DATA
	if( loadData(anED, loadMachineRID, loadMachineRID) )
	{
		// Optimization for runtime resource access
		TableOfInstanceOfData::raw_iterator itVar =
				anExecutable.getVariables().begin();
		TableOfInstanceOfData::raw_iterator endVar =
				anExecutable.getVariables().end();
		for( ; itVar != endVar ; ++itVar )
		{
			(itVar)->setRuntimeContainerRID( loadMachineRID );
		}
	}

	// Load BUFFER
	if( loadBuffer(anED, loadMachineRID, loadMachineRID) )
	{
		// Optimization for runtime resource access
		for( auto & itBuffer : anExecutable.getBuffer() )
		{
			itBuffer.setRuntimeContainerRID( loadMachineRID );
		}
	}

	// Load ROUTER
	if( loadRouter(anED, loadMachineRID, loadMachineRID) )
	{
		// Optimization for runtime resource access
		for( auto & itPort : anExecutable.getPort() )
		{
			itPort.setRuntimeContainerRID( loadMachineRID );

			if( itPort.asPort().isPort() )
			{
				if( itPort.getModifier().hasDirectionInput() )
				{
					itPort.setInputRoutingData( aRF->getRouter().
							getInputRouting(itPort.getRouteOffset()) );
				}
				if( itPort.getModifier().hasDirectionOutput() )
				{
					itPort.setOutputRoutingData( aRF->getRouter().
							getOutputRouting(itPort.getRouteOffset()) );
				}
			}
		}
	}


	// Load MACHINE
	loadMachine(anED, loadMachineRID, loadMachineRID, thePid, theOffset);

	// set SCHEDULE
	if( anExecutable.hasSingleRuntimeInstance()
		&& aMachine->refExecutable().hasOnSchedule() )
	{
		setRuntimeSchedulerCode(anED, (*aRF), aMachine->refExecutable(), true);
	}

	// Optimization for runtime resource access
	TableOfInstanceOfData::const_raw_iterator itVar =
			anExecutable.getVariableAlias().begin();
	TableOfInstanceOfData::const_raw_iterator endVar =
			anExecutable.getVariableAlias().end();
	for( ; itVar != endVar ; ++itVar )
	{
		if( (itVar)->isAlias() )
		{
			if( (itVar)->hasAliasTarget() &&
				(itVar)->getAliasTarget()->hasRuntimeContainerRID() )
			{
				(itVar)->setRuntimeContainerRID(
						(itVar)->getAliasTarget()->getRuntimeContainerRID() );
			}
			else if( (itVar)->hasMachinePath() )
			{
				(itVar)->setRuntimeContainerRID( (itVar)->getMachinePath()->
					last()->refExecutable().getVariables().
					rawAt((itVar)->getOffset())->getRuntimeContainerRID() );
			}
		}
	}

	// Optimization for runtime resource access
	for( auto & itAlias : anExecutable.getAlias() )
	{
		if( itAlias.isAlias() )
		{
			if( itAlias.hasAliasTarget()
				&& itAlias.getAliasTarget()->hasRuntimeContainerRID() )
			{
				itAlias.setRuntimeContainerRID(
						itAlias.getAliasTarget()->getRuntimeContainerRID() );
			}
			else if( itAlias.hasMachinePath() )
			{
				itAlias.setRuntimeContainerRID(
						itAlias.getMachinePath()->last()->refExecutable()
						.getVariables().rawAt(itAlias.getOffset())
						->getRuntimeContainerRID() );
			}
		}
	}

AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "> end loading system instance < "
			<< aMachine->getFullyQualifiedNameID() << " >" << std::endl;
AVM_ENDIF_DEBUG_FLAG( LOADING )

	return( aRF );
}


/**
 * loadMachineInstance
 */
RuntimeForm * Loader::loadMachineInstance(ExecutionData & anED,
		const RuntimeID & aParentRID, InstanceOfMachine * anInstance,
		int & thePid, avm_offset_t & theOffset)
{
AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "< begin loading machine instance < "
			<< anInstance->getFullyQualifiedNameID() << " >"
			<< std::endl
			<< TAB << "\t>>>> parent is: "
			<< std::endl;

	aParentRID.toStream(AVM_OS_TRACE << INCR2_INDENT);

	AVM_OS_TRACE << EOL_DECR2_INDENT;
AVM_ENDIF_DEBUG_FLAG( LOADING )

	// PID & OFFSET for the runtime machine
	int pid = thePid++;
	avm_offset_t offset = theOffset++;

	RuntimeID loadMachineRID(aParentRID, pid, offset, anInstance);
	if( anInstance->refExecutable().hasSingleRuntimeInstance() )
	{
		anInstance->setRuntimeRID(loadMachineRID);
	}

	mConfiguration.appendRID( loadMachineRID );

	RuntimeForm * aRF = new RuntimeForm( loadMachineRID );

	anED.saveRuntimeForm(offset, aRF);

//!?! Code pour évolution future
//	aRF->setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
//	aRF->setNodeTimedCondition( ExpressionConstant::BOOLEAN_TRUE );


	if( anInstance->isAutoStart() )
	{
//		anED.setRuntimeFormState(offset, anED.getRuntimeFormState(aParentRF));

		if( anInstance->hasOnCreate() )
		{
			mOnCreateRoutime.append( loadMachineRID );

			anED.setRuntimeFormState(offset, PROCESS_CREATING_STATE);
		}
		else
		{
			anED.setRuntimeFormState(offset, PROCESS_DISABLED_STATE);
		}
	}
	else
	{
		anED.setRuntimeFormState(offset, PROCESS_CREATED_STATE);

		loadMachineRID.setDynamicLoaded( true );
	}

	if( aParentRID.valid() )
	{
		anED.getRuntime(aParentRID).appendChild( loadMachineRID );
	}


	ExecutableForm & anExecutable = anInstance->refExecutable();

	// Load DATA
	if( loadData(anED, loadMachineRID, loadMachineRID) )
	{
		// Optimization for runtime resource access
		if( anExecutable.hasSingleRuntimeInstance() &&
				anExecutable.getVariables().nonempty() )
		{
			TableOfInstanceOfData::raw_iterator itVar =
					anExecutable.getVariables().begin();
			TableOfInstanceOfData::raw_iterator endVar =
					anExecutable.getVariables().end();
			for( ; itVar != endVar ; ++itVar )
			{
				(itVar)->setRuntimeContainerRID( loadMachineRID );
			}
		}
	}

	// Load BUFFER
	if( loadBuffer(anED, loadMachineRID, loadMachineRID) )
	{
		// Optimization for runtime resource access
		if( anExecutable.hasSingleRuntimeInstance()
			&& anExecutable.getBuffer().nonempty())
		{
			for( auto & itBuffer : anExecutable.getBuffer() )
			{
				itBuffer.setRuntimeContainerRID( loadMachineRID );
			}
		}
	}

	// Load ROUTER
	if( loadRouter(anED, loadMachineRID, loadMachineRID) )
	{
		if( anExecutable.hasSingleRuntimeInstance()
			&& anExecutable.getPort().nonempty() )
		{
			// Optimization for runtime resource access
			for( auto & itPort : anExecutable.getPort() )
			{
				itPort.setRuntimeContainerRID( loadMachineRID );

				if( itPort.asPort().isPort() )
				{
					if( itPort.getModifier().hasDirectionInput() )
					{
						itPort.setInputRoutingData( aRF->getRouter().
								getInputRouting(itPort.getRouteOffset()) );
					}
					if( itPort.getModifier().hasDirectionOutput() )
					{
						itPort.setOutputRoutingData(aRF->getRouter().
								getOutputRouting(itPort.getRouteOffset()) );
					}
				}
			}
		}
	}


	// Load MACHINE
	loadMachine(anED, loadMachineRID, loadMachineRID, thePid, theOffset);

	// set SCHEDULE
	if( //anExecutable.hasSingleRuntimeInstance() &&
			anExecutable.hasOnSchedule() )
	{
		setRuntimeSchedulerCode(anED, (*aRF), anExecutable, true);
	}


	// Optimization for runtime resource access
	TableOfInstanceOfData::const_raw_iterator itVar =
			anExecutable.getVariableAlias().begin();
	TableOfInstanceOfData::const_raw_iterator endVar =
			anExecutable.getVariableAlias().end();
	for( ; itVar != endVar ; ++itVar )
	{
		if( (itVar)->isAlias() )
		{
			if( (itVar)->hasAliasTarget() &&
				(itVar)->getAliasTarget()->hasRuntimeContainerRID() )
			{
				(itVar)->setRuntimeContainerRID(
						(itVar)->getAliasTarget()->getRuntimeContainerRID() );
			}
			else if( (itVar)->hasMachinePath() )
			{
				(itVar)->setRuntimeContainerRID((itVar)->getMachinePath()->
					last()->refExecutable().getVariables().
					rawAt((itVar)->getOffset())->getRuntimeContainerRID() );
			}
		}
	}

	// Optimization for runtime resource access
	for( auto & itAlias : anExecutable.getAlias() )
	{
		if( itAlias.isAlias() )
		{
			if( itAlias.hasAliasTarget()
				&& itAlias.getAliasTarget()->hasRuntimeContainerRID() )
			{
				itAlias.setRuntimeContainerRID(
						itAlias.getAliasTarget()->getRuntimeContainerRID() );
			}
			else if( itAlias.hasMachinePath() )
			{
				itAlias.setRuntimeContainerRID(
						itAlias.getMachinePath()->last()->refExecutable()
						.getVariables().rawAt(itAlias.getOffset())
						->getRuntimeContainerRID() );
			}
		}
	}

AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "> end loading machine instance < "
			<< anInstance->getFullyQualifiedNameID() << " >" << std::endl;
AVM_ENDIF_DEBUG_FLAG( LOADING )

	return( aRF );
}


/**
 * loadData
 */
bool Loader::loadData(ExecutionData & anED,
		const RuntimeID & aRID, const RuntimeID & aDataRID)
{
	ExecutableForm & theExecutable = aDataRID.refExecutable();

	anED.appendConstParameters( theExecutable.getConstVariable() );

	if( theExecutable.hasVariable() )
	{
		std::size_t errorCount = 0;

		TableOfData * aDataTable =
				new TableOfData( theExecutable.getVariablesSize() );
		anED.getRuntime(aDataRID).setDataTable(aDataTable);

		InstanceOfMachine * aMachine = aDataRID.getInstance();

		TableOfInstanceOfData::ref_iterator itVar =
				theExecutable.getVariables().begin();
		TableOfInstanceOfData::ref_iterator endVar =
				theExecutable.getVariables().end();
		avm_offset_t offset = 0;

		// LOAD PARAMETER & RETURN
		if( theExecutable.hasParamReturn()
			&& aMachine->hasParamReturnTable() )
		{
			BF paramReturnArgument;

			anED.makeWritableRuntimeFormStateTable();

			std::size_t paramReturnCount = theExecutable.getParamReturnCount();
			for( ; offset < paramReturnCount ; ++itVar , ++offset )
			{
				anED.setAssigned(aDataRID, offset);

AVM_OS_ASSERT_FATAL_ERROR_EXIT( offset == (itVar)->getOffset() )
		<< "Invalid variable offset in data table !\n\t"
		<< str_header( *itVar )
		<< SEND_EXIT;

				paramReturnArgument = aMachine->getParamReturn(offset);
				if( paramReturnArgument.invalid() && (itVar)->hasValue() )
				{
					paramReturnArgument = (itVar)->getValue();
				}

				if( paramReturnArgument.valid() )
				{
					if( (itVar)->getModifier().hasNatureReference() )
					{
						if( paramReturnArgument.isnot< InstanceOfData >() )
						{
							AVM_OS_EXIT( FAILED )
									<< "loading:> Unexpected a non "
										"lvalue for reference param << "
									<< paramReturnArgument.str() << " >> !!!"
									<< SEND_EXIT;
						}
					}
					else if( (itVar)->getModifier().hasNatureMacro() )
					{
						//!! NOTHING
					}
					else if( aDataRID.getInstance()->isAutoStart() )
					//(not theExecutable.getSpecifier().isComponentProcedure()))
					{
						if( ENV.eval(anED, aDataRID, paramReturnArgument) )
						{
							paramReturnArgument = ENV.outVAL;
						}
						// ASSERT paramForm is an LVALUE
						else //if( not (itVar)->getModifier().hasNatureReference() )
						{
							AVM_OS_EXIT( FAILED )
									<< "loading:> Failed to eval initial "
										"value for param << "
									<< paramReturnArgument.str() << " >> !!!"
									<< SEND_EXIT;
						}
					}
					else
					{
						paramReturnArgument = ENV.createInitial(
								anED, aDataRID, (itVar) );
					}

					if( not ExpressionTypeChecker::isTyped(
							(itVar)->getTypeSpecifier(), paramReturnArgument) )
					{
						++errorCount;

//						getCompilerTable().incrErrorCount();
						AVM_OS_WARN
								<< aMachine->safeAstElement().errorLocation()
								<< "loadData :> Unexpected << ";

AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_WARN << std::endl << paramReturnArgument
			<< " >> as << " << (itVar)->getTypeSpecifier().strT();

	aMachine->safeAstElement().errorLocation(AVM_OS_TRACE)
			<< "loadData :> Unexpected << "
			<< str_header( paramReturnArgument ) << " >> as << "
			<< (itVar)->getTypeSpecifier().strT()
			<< " >> parameter for\n\t<< " << str_header( *itVar ) << " >> !!!"
			<< std::endl;

AVM_ELSE

	AVM_OS_WARN << str_header( paramReturnArgument ) << " >> as << "
			<< (itVar)->getTypeSpecifier().strT();
AVM_ENDIF_DEBUG_FLAG( LOADING )

						AVM_OS_WARN << " >> parameter for\n\t<< "
								<< str_header( *itVar ) << " >>!!!"
								<< std::endl;
					}
				}
				else
				{
					paramReturnArgument =
							ENV.createInitial(anED, aDataRID, (itVar));
				}

				aDataTable->assign(offset, paramReturnArgument);
			}
		}


		for( ; itVar != endVar ; ++itVar , ++offset )
		{
			anED.setAssigned(aDataRID, offset);

			aDataTable->assign(offset,
					ENV.createInitial(anED, aDataRID, (itVar)));
		}

		return( errorCount == 0 );
	}

	return( true );
}

/**
 * loadInitialMonitorData
 */
//!![MIGRATION]:MONITOR --> onCreate Routine
//void Loader::loadInitialMonitorData(
//		ExecutionData & anED, const RuntimeID & aRID,
//		InstanceOfMachine * anInstanceMachine, bool isRecursive)
//{
//	const RuntimeID & aDataRID = anED.getRuntimeID(anInstanceMachine);
//	ExecutableForm & theExecutable = aDataRID.refExecutable();
//
//	// Load DATA
//	if( theExecutable.getVariables().nonempty() )
//	{
//		TableOfInstanceOfData::const_raw_iterator itVar =
//				theExecutable.getVariables().begin();
//		TableOfInstanceOfData::const_raw_iterator endVar =
//				theExecutable.getVariables().end();
//
//		// LOAD PARAMETER
//		if( theExecutable.hasParam() && anInstanceMachine->hasParamReturnTable() )
//		{
//			std::size_t paramCount = theExecutable.getParamCount();
//			for( avm_offset_t offset = 0 ; offset < paramCount ; ++itVar , ++offset )
//			{
//				if( (itVar)->hasOnWriteRoutine() )
//				{
//					BF paramForm = anInstanceMachine->getParam(offset);
//
//					if( paramForm.valid() )
//					{
//						ENV.eval(anED, aRID, paramForm);
//						paramForm = ENV.outVAL;
//					}
//					else if( ENV.getRvalue(anED, aDataRID, (itVar)).invalid() )
//					{
//						paramForm = ENV.createInitial(anED, aDataRID, (itVar));
//					}
//
//					if( not ExpressionFactory::containsVariable(
//							(itVar)->getOnWriteCode(), (itVar)) )
//					{
//						if( not ENV.writeData(anED, aDataRID, (itVar), paramForm) )
//						{
//							AVM_OS_EXIT( FAILED )
//									<< "loadInitialMonitorData:> Unvalid "
//										"Initial Value << " << paramForm.str()
//									<< " >> for onInit monitor !\n"
//									<< (itVar)->toString()
//									<< SEND_EXIT;
//						}
//					}
//				}
//			}
//		}
//
//		for( ; itVar != endVar ; ++itVar )
//		{
//			if( (itVar)->hasOnWriteRoutine() )
//			{
//				BF paramForm = ENV.getRvalue(anED, aDataRID, (itVar));
//				if( paramForm.invalid() )
//				{
//					paramForm = ENV.createInitial(anED, aDataRID, (itVar));
//				}
//
//				if( not ExpressionFactory::containsVariable(
//						(itVar)->getOnWriteCode(), (itVar)) )
//				{
//					if( not ENV.writeData(anED, aDataRID, (itVar), paramForm) )
//					{
//						AVM_OS_EXIT( FAILED )
//								<< "loadInitialMonitorData:> Unvalid "
//									"Initial Value << " << paramForm.str()
//								<< " >> for onInit monitor !\n"
//								<< (itVar)->toString()
//								<< SEND_EXIT;
//					}
//				}
//			}
//		}
//	}
//
//	// Load MACHINE
//	if( isRecursive && theExecutable.getMachineInstance().nonempty() )
//	{
//		TableOfSymbol::const_iterator itMachine =
//				theExecutable.instance_static_begin();
//		TableOfSymbol::const_iterator endMachine =
//				theExecutable.instance_static_end();
//		for(  ; itMachine != endMachine ; ++itMachine )
//		{
//			loadInitialMonitorData(anED, aRID,
//					(*itMachine).rawMachine(), isRecursive);
//		}
//	}
//}


/**
 * loadBuffer
 */
bool Loader::loadBuffer(ExecutionData & anED,
		const RuntimeID & aRID, const RuntimeID & loadMachineRID)
{
	ExecutableForm & loadExecutable = loadMachineRID.refExecutable();

	if( loadExecutable.getBuffer().nonempty() )
	{
		TableOfBufferT aBufferTable( loadExecutable.getBuffer().size() );
		anED.getRuntime( loadMachineRID ).setBufferTable(aBufferTable);

		TableOfSymbol::const_iterator itBuffer = loadExecutable.getBuffer().begin();
		TableOfSymbol::const_iterator endBuffer = loadExecutable.getBuffer().end();
		for( std::size_t offset = 0 ; itBuffer < endBuffer ; ++itBuffer , ++offset )
		{
			switch( (*itBuffer).getPolicySpecifierKind() )
			{
				case TYPE_FIFO_SPECIFIER:
				{
					aBufferTable.set(offset,
							new FifoBuffer(((*itBuffer).asBuffer())));
					break;
				}
				case TYPE_LIFO_SPECIFIER:
				{
					aBufferTable.set(offset,
							new LifoBuffer(((*itBuffer).asBuffer())));
					break;
				}


				case TYPE_MULTI_FIFO_SPECIFIER:
				{
					aBufferTable.set(offset,
							new MultiFifoBuffer(((*itBuffer).asBuffer())));
					break;
				}
				case TYPE_MULTI_LIFO_SPECIFIER:
				{
					aBufferTable.set(offset,
							new MultiLifoBuffer(((*itBuffer).asBuffer())));
					break;
				}


				case TYPE_RAM_SPECIFIER:
				{
					aBufferTable.set(offset,
							new RamBuffer(((*itBuffer).asBuffer())));
					break;
				}

				case TYPE_MULTISET_SPECIFIER:
				{
					aBufferTable.set(offset,
							new MultisetBuffer(((*itBuffer).asBuffer())));
					break;
				}
				case TYPE_SET_SPECIFIER:
				{
					aBufferTable.set(offset,
							new SetBuffer(((*itBuffer).asBuffer())));
					break;
				}

				default:
				{
					AVM_OS_EXIT( FAILED )
							<< "theBuffer Nature is unexpected"
							<< SEND_EXIT;

					aBufferTable.set(offset,
							new FifoBuffer(((*itBuffer).asBuffer())));
					break;
				}
			}
		}
	}

	return( true );
}


/**
 * loadMachine
 */
void Loader::loadMachine(ExecutionData & anED,
		const RuntimeID & aRID, const RuntimeID & loadMachineRID,
		int & thePid, avm_offset_t & theOffset)
{
	ExecutableForm & loadExecutable = loadMachineRID.refExecutable();

	if( loadExecutable.getInstanceStatic().nonempty() )
	{
		if( loadExecutable.hasInstanceStaticThis() )
		{
			anED.getRuntime( loadMachineRID ).appendChild( loadMachineRID );
		}

		TableOfSymbol::const_iterator itInstance =
				loadExecutable.instance_static_begin();
		TableOfSymbol::const_iterator endInstance =
				loadExecutable.instance_static_end();
		for(  ; itInstance != endInstance ; ++itInstance )
		{
			loadMachineInstance( anED , loadMachineRID,
					(*itInstance).rawMachine(), thePid, theOffset);
		}
	}
}


/**
 * dynamicLoadMachine
 */
RuntimeForm * Loader::dynamicLoadMachine(ExecutionData & anED,
		const RuntimeID & aRID, RuntimeForm * aModelRF,
		const RuntimeID & aParentRID, const Operator * aScheduleOp)
{
	InstanceOfMachine * aMachine = aModelRF->getInstance()->clone();
//	BF bfMachine( aMachine );

	aMachine->setInstanciationCount( aModelRF->getInstanciationCount() );

	ExecutableForm & theExecutable = aMachine->refExecutable();

	aMachine->updateUfid( aModelRF->getInstanciationCount() );

	aMachine->setOffset( anED.getRuntime(aParentRID).getChildTable()->size() );


AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "< begin loading machine instance < "
			<< aMachine->getFullyQualifiedNameID() << " >" << std::endl;

	AVM_OS_TRACE << incr_stream( aMachine ) << TAB << "\t>>>> parent is: "
			<< std::endl;

	aParentRID.toStream(AVM_OS_TRACE << INCR2_INDENT);

	AVM_OS_TRACE << EOL_DECR2_INDENT;
AVM_ENDIF_DEBUG_FLAG( LOADING )


	// PID & OFFSET for the runtime machine
	avm_offset_t theOffset = anED.getTableOfRuntime().size();
	int thePid = anED.getRuntimeID(theOffset - 1).getRid() + 1;

	std::size_t newMachineCount =
			1 + theExecutable.getrecMachineCount() + theOffset;

	int pid = thePid++;
	avm_offset_t offset = theOffset++;


	//!! TODO RESIZE & MEMORY
	anED.resize( newMachineCount );


	RuntimeID loadMachineRID(
			aModelRF->getRID(), aParentRID, pid, offset, aMachine);

	loadMachineRID.setDynamicLoaded( true );

	mConfiguration.appendRID( loadMachineRID );

	RuntimeForm * aRF = new RuntimeForm( loadMachineRID );
	anED.saveRuntimeForm(offset, aRF);

//!?! Code pour évolution future
//	aRF->setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
//	aRF->setNodeTimedCondition( ExpressionConstant::BOOLEAN_TRUE );

	if( aMachine->hasOnCreate() )
	{
		mOnCreateRoutime.append( loadMachineRID );

		anED.setRuntimeFormState(offset, PROCESS_CREATING_STATE);
	}
	else
	{
		anED.setRuntimeFormState(offset, PROCESS_DISABLED_STATE);
	}

	RuntimeForm & aParentRF = anED.getWritableRuntime( aParentRID );

	aParentRF.makeWritableChildTable();
	aParentRF.appendChild( loadMachineRID );

	setRuntimeSchedulerCode(anED, aParentRF, aParentRF.refExecutable(), true);

	// Load DATA
	if( loadData(anED, aRID, loadMachineRID) )
	{
		if( loadMachineRID.hasVariable() )
		{
//!![MIGRATION]:MONITOR --> onCreate Routine
//			loadInitialMonitorData(anED, aRID,
//					loadMachineRID.getInstance(), false);
		}
	}
	else
	{
		AVM_OS_EXIT( FAILED )
				<< "dynamicLoadMachine:> loadData failed"
				<< SEND_EXIT;
	}

	// Load BUFFER
	if( not loadBuffer(anED, aRID, loadMachineRID) )
	{
		AVM_OS_EXIT( FAILED )
				<< "dynamicLoadMachine:> loadBuffer failed"
				<< SEND_EXIT;
	}

	// Load ROUTER
	if( not dynamicLoadRouter(anED, loadMachineRID) )
	{
		AVM_OS_EXIT( FAILED )
				<< "dynamicLoadMachine:> dynamicLoadRouter failed"
				<< SEND_EXIT;
	}


	// Load MACHINE
	loadMachine(anED, loadMachineRID, loadMachineRID, thePid, theOffset);

	// set SCHEDULE
	if( theExecutable.hasOnSchedule() )
	{
		setRuntimeSchedulerCode(anED, (*aRF), theExecutable, true);
	}


AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "> end loading machine instance < "
			<< aMachine->getFullyQualifiedNameID() << " >" << std::endl;
AVM_ENDIF_DEBUG_FLAG( LOADING )


	return( aRF );
}



RuntimeForm * Loader::dynamicLoadMachine(ExecutionData & anED,
		const RuntimeID & aRID, InstanceOfMachine * anInstanceDynamic,
		const RuntimeID & aParentRID, const Operator * aScheduleOp)
{
	InstanceOfMachine * aMachine = anInstanceDynamic->clone();
//	BF bfMachine( aMachine );

	aMachine->setInstanciationCount(
			anInstanceDynamic->getInstanciationCount() );

	ExecutableForm & theExecutable = aMachine->refExecutable();

//	aMachine->updateUfid( anInstanceDynamic->getInstanciationCount() );

	aMachine->setOffset(
			anED.getRuntime(aParentRID).getChildTable()->size() );


AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "< begin loading machine instance < "
			<< aMachine->getFullyQualifiedNameID() << " >" << std::endl;

	AVM_OS_TRACE << to_stream( aMachine ) << TAB << "\t>>>> parent is: "
			<< std::endl;

	aParentRID.toStream(AVM_OS_TRACE << INCR2_INDENT);

	AVM_OS_TRACE << EOL_DECR2_INDENT;
AVM_ENDIF_DEBUG_FLAG( LOADING )


	// PID & OFFSET for the runtime machine
	avm_offset_t theOffset = anED.getTableOfRuntime().size();
	int thePid = anED.getRuntimeID(theOffset - 1).getRid() + 1;

	std::size_t newMachineCount =
			1 + theExecutable.getrecMachineCount() + theOffset;

	int pid = thePid++;
	avm_offset_t offset = theOffset++;


	//!! TODO RESIZE & MEMORY
	anED.resize( newMachineCount );


	RuntimeID loadMachineRID(aParentRID, pid, offset, aMachine);

	loadMachineRID.setDynamicLoaded( true );

	mConfiguration.appendRID( loadMachineRID );

	RuntimeForm * aRF = new RuntimeForm( loadMachineRID );
	anED.saveRuntimeForm(offset, aRF);

//!?! Code pour évolution future
//	aRF->setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
//	aRF->setNodeTimedCondition( ExpressionConstant::BOOLEAN_TRUE );

	if( aMachine->hasOnCreate() )
	{
		mOnCreateRoutime.append( loadMachineRID );

		anED.setRuntimeFormState(offset, PROCESS_CREATING_STATE);
	}
	else
	{
		anED.setRuntimeFormState(offset, PROCESS_DISABLED_STATE);
	}

	RuntimeForm & aParentRF = anED.getWritableRuntime( aParentRID );

	aParentRF.makeWritableChildTable();
	aParentRF.appendChild( loadMachineRID );

	setRuntimeSchedulerCode(anED, aParentRF, aParentRF.refExecutable(), false);

	// Load DATA
	if( loadData(anED, aRID, loadMachineRID) )
	{
		if( loadMachineRID.hasVariable() )
		{
//			loadInitialMonitorData(anED, aRID,
//					loadMachineRID.getInstance(), false);
		}
	}
	else
	{
		AVM_OS_EXIT( FAILED )
				<< "dynamicLoadMachine:> loadData failed"
				<< SEND_EXIT;
	}

	// Load BUFFER
	if( not loadBuffer(anED, aRID, loadMachineRID) )
	{
		AVM_OS_EXIT( FAILED )
				<< "dynamicLoadMachine:> loadBuffer failed"
				<< SEND_EXIT;
	}

	// Load ROUTER
	if( not dynamicLoadRouter(anED, loadMachineRID) )
	{
		AVM_OS_EXIT( FAILED )
				<< "dynamicLoadMachine:> dynamicLoadRouter failed"
				<< SEND_EXIT;
	}


	// Load MACHINE
	loadMachine(anED, loadMachineRID, loadMachineRID, thePid, theOffset);

	// set SCHEDULE
	if( theExecutable.hasOnSchedule() )
	{
		setRuntimeSchedulerCode(anED, (*aRF), theExecutable, true);
	}


AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "> end loading machine instance < "
			<< aMachine->getFullyQualifiedNameID() << " >" << std::endl;
AVM_ENDIF_DEBUG_FLAG( LOADING )


	return( aRF );
}


/**
 * getRouter4Model
 */
const Router & Loader::getRouter4Model(
		ExecutionData & anED, RuntimeID & aRoutingRID)
{
	while( aRoutingRID.valid() )
	{
		if( aRoutingRID.refExecutable().hasRouter4Model() )
		{
			const Router & aRouter = aRoutingRID.refExecutable()
					.getRouter4Model( aRoutingRID.getExecutable() );

			if( aRouter.valid() )
			{
				return( aRouter );
			}
		}

		aRoutingRID = aRoutingRID.getPRID();
	}

	return( Router::nullref() );
}

/**
 * cloneUpdateRouter
 */
static Router cloneUpdateRouter(const Router & loadRouter,
		const RuntimeID & aRoutingRID, const RuntimeID & loadMachineRID)
{
	std::size_t routeCount = loadRouter.getRouteID();

	Router newRouter(*( loadMachineRID.getInstance() ), routeCount, routeCount);

	RoutingData aRoutingData;

	// GLOBAL INPUT or OUTPUT ROUTE
	std::size_t offset = 0;
	for( ; offset < routeCount ; ++offset )
	{
		aRoutingData = loadRouter.getInputRouting(offset);
		if( aRoutingData.valid() )
		{
			aRoutingData.makeWritable();
			aRoutingData.setRuntimeRID(aRoutingRID);

			newRouter.setInputRouting(offset, aRoutingData);
		}

		// NO ELSE because of INOUT PORT
		aRoutingData = loadRouter.getOutputRouting(offset);
		if( aRoutingData.valid() )
		{
			aRoutingData.makeWritable();
			aRoutingData.setRuntimeRID(aRoutingRID);

			newRouter.setOutputRouting(offset, aRoutingData);
		}
	}


	// LOCAL INPUT ROUTE
	offset = loadRouter.getRouteID();
	routeCount = loadRouter.getInputRoutingTable().size();
	for( ; offset < routeCount ; ++offset )
	{
		aRoutingData = loadRouter.getInputRouting(offset);
		if( aRoutingData.valid() )
		{
			aRoutingData.makeWritable();
			aRoutingData.setRuntimeRID(aRoutingRID);

			newRouter.appendInputRouting( aRoutingData );
		}
	}

	// LOCAL OUPUT ROUTE
	offset = loadRouter.getRouteID();
	routeCount = loadRouter.getOutputRoutingTable().size();
	for( ; offset < routeCount ; ++offset )
	{
		aRoutingData = loadRouter.getOutputRouting(offset);
		if( aRoutingData.valid() )
		{
			aRoutingData.makeWritable();
			aRoutingData.setRuntimeRID(aRoutingRID);

			newRouter.appendOutputRouting( aRoutingData );
		}
	}

	return( newRouter );
}


/**
 * loadRouter
 */
bool Loader::loadRouter(ExecutionData & anED,
		const RuntimeID & aRID, const RuntimeID & loadMachineRID)
{
	ExecutableForm & loadExecutable = loadMachineRID.refExecutable();

	// Load ROUTER
	if( loadExecutable.hasPort() || loadExecutable.hasRouter4This() )
	{
		RuntimeForm & loadRF = anED.getRuntime( loadMachineRID );

		Router parentLoadRouter;
		RuntimeID aRoutingRID;
		TableOfRouter * containerRouterTable = nullptr;

		if( loadMachineRID.hasPRID() )
		{
			containerRouterTable = &( loadMachineRID.getPRID().
					refExecutable().getRouters4Instance() );

			parentLoadRouter = anED.getRuntime(
					loadMachineRID.getPRID() ).getRouter();
		}

		if( loadExecutable.hasRouter4Instance() )
		{
			const Router & theRouter4This = loadExecutable.getRouter4This();

			if( (containerRouterTable != nullptr)
				&& containerRouterTable->populated() )
			{
				const Router & theRouter4Parent = containerRouterTable->get(
						loadMachineRID.getInstance()->getOffset());

				std::size_t routeCount = theRouter4This.getRouteID();

				Router newRouter(
					*( loadMachineRID.getInstance() ), routeCount, routeCount);
				loadRF.setRouter( newRouter );

				RoutingData aRoutingData;

				// GLOBAL INPUT or OUTPUT ROUTE
				for( std::size_t offset = 0 ; offset < routeCount ; ++offset )
				{
					aRoutingData = theRouter4This.getInputRouting(offset);
					if( aRoutingData.invalid() )
					{
						aRoutingData = theRouter4Parent.getInputRouting(offset);
					}
					if( aRoutingData.invalid() )
					{
						aRoutingData = parentLoadRouter.getInputRouting(offset);
					}
					if( aRoutingData.valid() )
					{
						aRoutingData.makeWritable();
						aRoutingData.setRuntimeRID(loadMachineRID);

						newRouter.setInputRouting(offset, aRoutingData);
					}

					// NO ELSE because of INOUT PORT
					aRoutingData = theRouter4This.getOutputRouting(offset);
					if( aRoutingData.invalid() )
					{
						aRoutingData = theRouter4Parent.getOutputRouting(offset);
					}
					if( aRoutingData.invalid() )
					{
						aRoutingData = parentLoadRouter.getOutputRouting(offset);
					}
					if( aRoutingData.valid() )
					{
						aRoutingData.makeWritable();
						aRoutingData.setRuntimeRID(loadMachineRID);

						newRouter.setOutputRouting(offset, aRoutingData);
					}
				}

				// LOCAL INPUT or OUTPUT ROUTE
				for( const auto & itPort : loadExecutable.getPort() )
				{
					if( itPort.asPort().isPort() )
					{
						if( itPort.getModifier().hasDirectionInput() )
						{
							if( itPort.getModifier().isVisibilityPublic() )
							{
								aRoutingData = theRouter4Parent.getInputRouting(
										itPort.getRouteOffset());

								aRoutingRID = loadMachineRID.getPRID();
							}
							else
							{
								aRoutingData = theRouter4This.getInputRouting(
										itPort.getRouteOffset());

								aRoutingRID = loadMachineRID;
							}

							aRoutingData.makeWritable();
							aRoutingData.setRuntimeRID(aRoutingRID);

							newRouter.appendInputRouting( aRoutingData );
						}
						// NO ELSE because of INOUT PORT
						if( itPort.getModifier().hasDirectionOutput() )
						{
							if( itPort.getModifier().isVisibilityPublic() )
							{
								aRoutingData = theRouter4Parent.getOutputRouting(
										itPort.getRouteOffset());
								aRoutingRID = loadMachineRID.getPRID();
							}
							else
							{
								aRoutingData = theRouter4This.getOutputRouting(
										itPort.getRouteOffset());
								aRoutingRID =loadMachineRID;
							}

							aRoutingData.makeWritable();
							aRoutingData.setRuntimeRID(aRoutingRID);

							newRouter.appendOutputRouting( aRoutingData );
						}
					}
				}
			}
			else
			{
//				loadRF.setRouter( theRouter4This );

				loadRF.setRouter( cloneUpdateRouter(
						theRouter4This, loadMachineRID, loadMachineRID) );
			}
		}
		else if( (containerRouterTable != nullptr)
				&& containerRouterTable->nonempty() )
		{
//			loadRF.setRouter( containerRouterTable->getRouter(machineOffset) );

			loadRF.setRouter( cloneUpdateRouter(
					containerRouterTable->get(
							loadMachineRID.getInstance()->getOffset()),
					loadMachineRID.getPRID(), loadMachineRID) );
		}

		else
		{
			aRoutingRID = loadMachineRID;
			const Router & aRouter = getRouter4Model(anED, aRoutingRID);
			if( aRouter.valid() )
			{
//				loadRF.setRouter( aRouter );

				loadRF.setRouter( cloneUpdateRouter(
						aRouter, aRoutingRID, loadMachineRID) );
			}
			else
			{
				AVM_OS_EXIT( FAILED )
						<< "No Router Table found !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
//!@?DEBUG:
//		AVM_OS_TRACE << "loadRouter: " << loadRF.getFullyQualifiedNameID() << std::endl;
//		loadRF.getRouter().toStream(AVM_OS_TRACE);
	}

	return( true );
}


/**
 * dynamicLoadRouter
 */
bool Loader::dynamicLoadRouter(ExecutionData & anED,
		const RuntimeID & loadMachineRID)
{
	ExecutableForm & loadExecutable = loadMachineRID.refExecutable();

	// Load ROUTER
	if( loadExecutable.hasPort() || loadExecutable.hasRouter4This() )
	{
		RuntimeForm & loadRF = anED.getRuntime( loadMachineRID );

		const TableOfRouter & containerRouterTable =
				loadMachineRID.getPRID().refExecutable().getRouters4Model();

		Router parentLoadRouter = anED.getRuntime(
				loadMachineRID.getPRID() ).getRouter();

		if( loadExecutable.hasRouter4Instance() )
		{
			const Router & theRouter4This = loadExecutable.getRouter4This();

			if( containerRouterTable.nonempty() )
			{
				const Router & theRouter4Parent = containerRouterTable.get(
					loadMachineRID.getInstance()->getInstanceModel()->getOffset());

				std::size_t aRouteID = theRouter4This.getRouteID();

				Router newRouter(
						*( loadMachineRID.getInstance() ), aRouteID, aRouteID);
				loadRF.setRouter( newRouter );

				RoutingData aRoutingData;

				// GLOBAL INPUT or OUTPUT ROUTE
				for( std::size_t offset = 0 ; offset < aRouteID ; ++offset )
				{
					aRoutingData = theRouter4This.getInputRouting(offset);
					if( aRoutingData.invalid() )
					{
						aRoutingData = theRouter4Parent.getInputRouting(offset);
					}
					if( aRoutingData.invalid() )
					{
						aRoutingData = parentLoadRouter.getInputRouting(offset);
					}
					if( aRoutingData.valid() )
					{
						aRoutingData.makeWritable();
						aRoutingData.setRuntimeRID(loadMachineRID);

						newRouter.setInputRouting(offset, aRoutingData);
					}

					// NO ELSE because of INOUT PORT
					aRoutingData = theRouter4This.getOutputRouting(offset);
					if( aRoutingData.invalid() )
					{
						aRoutingData = theRouter4Parent.getOutputRouting(offset);
					}
					if( aRoutingData.invalid() )
					{
						aRoutingData = parentLoadRouter.getOutputRouting(offset);
					}
					if( aRoutingData.valid() )
					{
						aRoutingData.makeWritable();
						aRoutingData.setRuntimeRID(loadMachineRID);

						newRouter.setOutputRouting(offset, aRoutingData);
					}
				}

				// LOCAL INPUT or OUTPUT ROUTE
				for( const auto & itPort : loadExecutable.getPort() )
				{
					if( itPort.getModifier().hasDirectionInput() )
					{
						if( itPort.getModifier().isVisibilityPublic() )
						{
							newRouter.appendInputRouting( theRouter4Parent
									.getInputRouting(itPort.getRouteOffset()) );
						}
						else
						{
							newRouter.appendInputRouting( theRouter4This
									.getInputRouting(itPort.getRouteOffset()) );
						}
					}
					// NO ELSE because of INOUT PORT
					if( itPort.getModifier().hasDirectionOutput() )
					{
						if( itPort.getModifier().isVisibilityPublic() )
						{
							newRouter.appendOutputRouting( theRouter4Parent
								.getOutputRouting(itPort.getRouteOffset()) );
						}
						else
						{
							newRouter.appendOutputRouting( theRouter4This
								.getOutputRouting(itPort.getRouteOffset()) );
						}
					}
				}
			}
			else
			{
				loadRF.setRouter( theRouter4This );
			}
		}
		else if( containerRouterTable.nonempty() )
		{
			loadRF.setRouter( containerRouterTable.get(
				loadMachineRID.getInstance()->getInstanceModel()->getOffset()) );
		}

		else
		{
			RuntimeID aRoutingRID = loadMachineRID;
			const Router & aRouter = getRouter4Model(anED, aRoutingRID);
			if( aRouter.valid() )
			{
				loadRF.setRouter( aRouter );
			}
			else
			{
				AVM_OS_EXIT( FAILED )
						<< "No Router Table found !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
	}

	return( true );
}


}

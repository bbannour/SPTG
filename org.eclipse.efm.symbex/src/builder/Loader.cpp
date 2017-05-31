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
#include <fml/buffer/MultisetBuffer.h>
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
		const BaseEnvironment & ENV, APExecutionData & anED)
{
	if( hasOnCreateRoutime() )
	{
		// Save current active RID
		RuntimeID saveRID = anED->mRID;

		const_rid_iterator itRID = on_create_begin();
		const_rid_iterator endRID = on_create_end();
		for( ; itRID != endRID ; ++itRID )
		{
//!![TRACE]: to delete
//AVM_OS_DEBUG << "onCreate: " << str_header( *itRID ) << std::endl
//		<< to_stream( (*itRID).getOnCreate() ) << std::flush;

			ExecutionEnvironment tmpENV(ENV, anED,
					(*itRID), (*itRID).getOnCreate() );

			if( tmpENV.run(PROCESS_CREATING_STATE) )
			{
				tmpENV.outEDS.pop_last_to( anED );

				if( tmpENV.outEDS.nonempty() )
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unsupported << onCreate Primitive >> "
									"which execution create more than one "
									"Execution Context :>\n"
							<< (*itRID).getOnCreate()->toString( AVM_TAB1_INDENT )
							<< SEND_ALERT;

					return( false );
				}

				anED.mwsetRuntimeFormState((*itRID),
						PROCESS_CREATING_STATE, PROCESS_DISABLED_STATE);
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Failed to eval << onCreate Routine >> "
								"on initial Execution Context :>\n"
						<< ENV.inCODE->toString( AVM_TAB1_INDENT )
						<< SEND_ALERT;

				return( false );
			}
		}

		resetOnCreateRoutime();

		// Restore current active RID
		anED->mRID = saveRID;
	}

	return( true );
}



/**
 * loadSchedulerCode
 * for onSchedule Routine
 */
BFCode Loader::loadSchedulerCode(
		APExecutionData & anED, const RuntimeForm & aRF,
		const BFCode & aSchedulerCode, bool isStaticLoading)
{
	if( aSchedulerCode.invalid() )
	{
		AVM_OS_EXIT( FAILED )
				<< "loadSchedulerCode:> Unexpected a << null<code> >> !!!"
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

		if( isStaticLoading
			&& anInstance->hasRuntimeRID()
			&& anED->isAlive( anInstance->getRuntimeRID() ) )
		{
			return( StatementConstructor::newOptiNopCode(
					aSchedulerCode->getOperator(),
					anInstance->getRuntimeRID(), AVM_ARG_MACHINE_RID) );
		}
		else
		{
			if( aRF.getExecutable()->hasOnConcurrency() )
			{
				BFCode loadCode( aRF.getExecutable()->getOnConcurrencyOperator() );

				loadSchedulerCode(anED, aRF, aSchedulerCode,
						loadCode, isStaticLoading);

				loadCode = mBuilder.getAvmcodeCompiler().optimizeStatement(
						aRF.getExecutable(), loadCode);

				return( loadCode );
			}
			else
			{
				TableOfRuntimeID::iterator itChild = aRF.getChildTable()->begin();
				TableOfRuntimeID::iterator endChild = aRF.getChildTable()->end();
				for( ; itChild != endChild ; ++itChild )
				{
					if( anInstance->getSpecifier().hasDesignInstanceStatic()
						&& (anInstance == (*itChild).getInstance())
						&& anED->isAlive( *itChild ) )
					{
						return( StatementConstructor::newOptiNopCode(
								aSchedulerCode->getOperator(),
								(*itChild), AVM_ARG_MACHINE_RID) );
					}
					else if( anInstance->getSpecifier().hasDesignModel()
							&& (*itChild).isDynamicLoaded()
							&& (anInstance == (*itChild).
									getInstance()->getInstanceModel())
							&& anED->isAlive( *itChild ) )
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

	else
	{
		BFCode loadCode( aSchedulerCode->getOperator() );

		AvmCode::iterator itArg = aSchedulerCode->begin();
		AvmCode::iterator endArg = aSchedulerCode->end();
		for( ; itArg != endArg ; ++itArg )
		{
			if( (*itArg).is< AvmCode >() )
			{
				loadSchedulerCode(anED, aRF,
						(*itArg).bfCode(), loadCode, isStaticLoading);
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "loadSchedulerCode:> Unexpected arg :>"
						<< (*itArg)
						<< SEND_EXIT;

				loadCode->append( *itArg );
			}
		}

		return( mBuilder.getAvmcodeCompiler().optimizeStatement(
				aRF.getExecutable(), loadCode) );
	}
}


void Loader::loadSchedulerCode(APExecutionData & anED,
		const RuntimeForm & aRF, const BFCode & aSchedulerCode,
		BFCode & loadCode, bool isStaticLoading)
{
	if( aSchedulerCode->singleton() &&
		aSchedulerCode->first().is< InstanceOfMachine >() &&
		OperatorManager::isActivity( aSchedulerCode->getOperator() ) )
	{
		InstanceOfMachine * anInstance =
				aSchedulerCode->first().to_ptr< InstanceOfMachine >();

		if( isStaticLoading
			&& anInstance->hasRuntimeRID()
			&& anED->isAlive( anInstance->getRuntimeRID() ) )
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
					&& anED->isAlive( *itChild ) )
				{
					loadCode->append( StatementConstructor::newOptiNopCode(
							aSchedulerCode->getOperator(),
							(*itChild), AVM_ARG_MACHINE_RID) );
				}
				else if( anInstance->getSpecifier().hasDesignModel()
						&& (*itChild).isDynamicLoaded()
						&& (anInstance == (*itChild).
								getInstance()->getInstanceModel())
						&& anED->isAlive( *itChild ) )
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


/**
 * loadSystemInstance
 */
RuntimeForm * Loader::loadSystemInstance(APExecutionData & anED,
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

	if( aMachine->getExecutable()->hasSingleRuntimeInstance() )
	{
		aMachine->setRuntimeRID(loadMachineRID);
	}

	RuntimeForm * aRF = new RuntimeForm( loadMachineRID );

	anED->saveRuntimeForm(offset, aRF);

	if( aMachine->hasOnCreate() )
	{
		mOnCreateRoutime.append( loadMachineRID );

		anED->setRuntimeFormState(offset, PROCESS_CREATING_STATE);
	}
	else
	{
		anED->setRuntimeFormState(offset, PROCESS_DISABLED_STATE);
	}

//!?! Code pour évolution future
//	aRF->setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
//	aRF->setNodeTimedCondition( ExpressionConstant::BOOLEAN_TRUE );


	if( aParentRID.valid() )
	{
		anED->getRuntime(aParentRID).appendChild( loadMachineRID );
	}

	ExecutableForm * anExecutable = aMachine->getExecutable();

	// Load DATA
	if( loadData(anED, loadMachineRID, loadMachineRID) )
	{
		// Optimization for runtime resource access
		TableOfInstanceOfData::const_raw_iterator itData =
				anExecutable->getData().begin();
		TableOfInstanceOfData::const_raw_iterator endData =
				anExecutable->getData().end();
		for( ; itData != endData ; ++itData )
		{
			(itData)->setRuntimeContainerRID( loadMachineRID );
		}
	}

	// Load BUFFER
	if( loadBuffer(anED, loadMachineRID, loadMachineRID) )
	{
		// Optimization for runtime resource access
		TableOfSymbol::iterator itBuffer = anExecutable->getBuffer().begin();
		TableOfSymbol::iterator endBuffer = anExecutable->getBuffer().end();
		for( ; itBuffer < endBuffer ; ++itBuffer )
		{
			(*itBuffer).setRuntimeContainerRID( loadMachineRID );
		}
	}

	// Load ROUTER
	if( loadRouter(anED, loadMachineRID, loadMachineRID) )
	{
		// Optimization for runtime resource access
		TableOfSymbol::iterator itPort = anExecutable->getPort().begin();
		TableOfSymbol::iterator endPort = anExecutable->getPort().end();
		for( ; itPort != endPort ; ++itPort )
		{
			(*itPort).setRuntimeContainerRID( loadMachineRID );

			if( (*itPort).port().isPort() )
			{
				if( (*itPort).getModifier().hasDirectionInput() )
				{
					(*itPort).setInputRoutingData( aRF->getRouter().
							getInputRouting((*itPort).getRouteOffset()) );
				}
				if( (*itPort).getModifier().hasDirectionOutput() )
				{
					(*itPort).setOutputRoutingData( aRF->getRouter().
							getOutputRouting((*itPort).getRouteOffset()) );
				}
			}
		}
	}


	// Load MACHINE
	loadMachine(anED, loadMachineRID, loadMachineRID, thePid, theOffset);

	// set SCHEDULE
	if( anExecutable->hasSingleRuntimeInstance() &&
			aMachine->getExecutable()->hasOnSchedule() )
	{
		aRF->setOnSchedule(
				loadSchedulerCode(anED, (*aRF),
						aMachine->getExecutable()->getOnSchedule(), true) );
	}

	// Optimization for runtime resource access
	TableOfInstanceOfData::const_raw_iterator itData =
			anExecutable->getDataAlias().begin();
	TableOfInstanceOfData::const_raw_iterator endData =
			anExecutable->getDataAlias().end();
	for( ; itData != endData ; ++itData )
	{
		if( (itData)->isAlias() )
		{
			if( (itData)->hasAliasTarget() &&
				(itData)->getAliasTarget()->hasRuntimeContainerRID() )
			{
				(itData)->setRuntimeContainerRID(
						(itData)->getAliasTarget()->getRuntimeContainerRID() );
			}
			else if( (itData)->hasMachinePath() )
			{
				(itData)->setRuntimeContainerRID( (itData)->getMachinePath()->
					last()->getExecutable()->getData().
					rawAt((itData)->getOffset())->getRuntimeContainerRID() );
			}
		}
	}

	// Optimization for runtime resource access
	TableOfSymbol::iterator itAlias = anExecutable->getAlias().begin();
	TableOfSymbol::iterator endAlias = anExecutable->getAlias().end();
	for( ; itAlias < endAlias ; ++itAlias )
	{
		if( (*itAlias).isAlias() )
		{
			if( (*itAlias).hasAliasTarget() &&
					(*itAlias).getAliasTarget()->hasRuntimeContainerRID() )
			{
				(*itAlias).setRuntimeContainerRID(
					(*itAlias).getAliasTarget()->getRuntimeContainerRID() );
			}
			else if( (*itAlias).hasMachinePath() )
			{
				(*itAlias).setRuntimeContainerRID((*itAlias).
					getMachinePath()->last()->getExecutable()->getData().
					rawAt((*itAlias).getOffset())->getRuntimeContainerRID() );
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
RuntimeForm * Loader::loadMachineInstance(APExecutionData & anED,
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
	if( anInstance->getExecutable()->hasSingleRuntimeInstance() )
	{
		anInstance->setRuntimeRID(loadMachineRID);
	}

	mConfiguration.appendRID( loadMachineRID );

	RuntimeForm * aRF = new RuntimeForm( loadMachineRID );

	anED->saveRuntimeForm(offset, aRF);

//!?! Code pour évolution future
//	aRF->setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
//	aRF->setNodeTimedCondition( ExpressionConstant::BOOLEAN_TRUE );


	if( anInstance->isAutoStart() )
	{
//		anED->setRuntimeFormState(offset, anED->getRuntimeFormState(aParentRF));

		if( anInstance->hasOnCreate() )
		{
			mOnCreateRoutime.append( loadMachineRID );

			anED->setRuntimeFormState(offset, PROCESS_CREATING_STATE);
		}
		else
		{
			anED->setRuntimeFormState(offset, PROCESS_DISABLED_STATE);
		}
	}
	else
	{
		anED->setRuntimeFormState(offset, PROCESS_CREATED_STATE);

		loadMachineRID.setDynamicLoaded( true );
	}

	if( aParentRID.valid() )
	{
		anED->getRuntime(aParentRID).appendChild( loadMachineRID );
	}


	ExecutableForm * anExecutable = anInstance->getExecutable();

	// Load DATA
	if( loadData(anED, loadMachineRID, loadMachineRID) )
	{
		// Optimization for runtime resource access
		if( anExecutable->hasSingleRuntimeInstance() &&
				anExecutable->getData().nonempty() )
		{
			TableOfInstanceOfData::const_raw_iterator itData =
					anExecutable->getData().begin();
			TableOfInstanceOfData::const_raw_iterator endData =
					anExecutable->getData().end();
			for( ; itData != endData ; ++itData )
			{
				(itData)->setRuntimeContainerRID( loadMachineRID );
			}
		}
	}

	// Load BUFFER
	if( loadBuffer(anED, loadMachineRID, loadMachineRID) )
	{
		// Optimization for runtime resource access
		if( anExecutable->hasSingleRuntimeInstance() &&
				anExecutable->getBuffer().nonempty())
		{
			TableOfSymbol::iterator itBuffer = anExecutable->getBuffer().begin();
			TableOfSymbol::iterator endBuffer = anExecutable->getBuffer().end();
			for( ; itBuffer < endBuffer ; ++itBuffer )
			{
				(*itBuffer).setRuntimeContainerRID( loadMachineRID );
			}
		}
	}

	// Load ROUTER
	if( loadRouter(anED, loadMachineRID, loadMachineRID) )
	{
		if( anExecutable->hasSingleRuntimeInstance() &&
				anExecutable->getPort().nonempty() )
		{
			// Optimization for runtime resource access
			TableOfSymbol::iterator itPort = anExecutable->getPort().begin();
			TableOfSymbol::iterator endPort = anExecutable->getPort().end();
			for( ; itPort != endPort ; ++itPort )
			{
				(*itPort).setRuntimeContainerRID( loadMachineRID );

				if( (*itPort).port().isPort() )
				{
					if( (*itPort).getModifier().hasDirectionInput() )
					{
						(*itPort).setInputRoutingData( aRF->getRouter().
								getInputRouting((*itPort).getRouteOffset()) );
					}
					if( (*itPort).getModifier().hasDirectionOutput() )
					{
						(*itPort).setOutputRoutingData(aRF->getRouter().
								getOutputRouting((*itPort).getRouteOffset()) );
					}
				}
			}
		}
	}


	// Load MACHINE
	loadMachine(anED, loadMachineRID, loadMachineRID, thePid, theOffset);

	// set SCHEDULE
	if( //anExecutable->hasSingleRuntimeInstance() &&
			anExecutable->hasOnSchedule() )
	{
		aRF->setOnSchedule(
				loadSchedulerCode(anED, (*aRF),
						anExecutable->getOnSchedule(), true) );
	}


	// Optimization for runtime resource access
	TableOfInstanceOfData::const_raw_iterator itData =
			anExecutable->getDataAlias().begin();
	TableOfInstanceOfData::const_raw_iterator endData =
			anExecutable->getDataAlias().end();
	for( ; itData != endData ; ++itData )
	{
		if( (itData)->isAlias() )
		{
			if( (itData)->hasAliasTarget() &&
				(itData)->getAliasTarget()->hasRuntimeContainerRID() )
			{
				(itData)->setRuntimeContainerRID(
						(itData)->getAliasTarget()->getRuntimeContainerRID() );
			}
			else if( (itData)->hasMachinePath() )
			{
				(itData)->setRuntimeContainerRID((itData)->getMachinePath()->
					last()->getExecutable()->getData().
					rawAt((itData)->getOffset())->getRuntimeContainerRID() );
			}
		}
	}

	// Optimization for runtime resource access
	TableOfSymbol::iterator itAlias = anExecutable->getAlias().begin();
	TableOfSymbol::iterator endAlias = anExecutable->getAlias().end();
	for( ; itAlias < endAlias ; ++itAlias )
	{
		if( (*itAlias).isAlias() )
		{
			if( (*itAlias).hasAliasTarget() &&
					(*itAlias).getAliasTarget()->hasRuntimeContainerRID() )
			{
				(*itAlias).setRuntimeContainerRID(
					(*itAlias).getAliasTarget()->getRuntimeContainerRID() );
			}
			else if( (*itAlias).hasMachinePath() )
			{
				(*itAlias).setRuntimeContainerRID( (*itAlias).
					getMachinePath()->last()->getExecutable()->getData().
					rawAt((*itAlias).getOffset())->getRuntimeContainerRID() );
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
bool Loader::loadData(APExecutionData & anED,
		const RuntimeID & aRID, const RuntimeID & aDataRID)
{
	if( aDataRID.hasVariable() )
	{
		avm_size_t errorCount = 0;

		ExecutableForm * theExecutable = aDataRID.getExecutable();

		TableOfData * aDataTable = new TableOfData( theExecutable->getDataSize() );
		anED->getRuntime(aDataRID).setDataTable(aDataTable);

		InstanceOfMachine * aMachine = aDataRID.getInstance();

		TableOfInstanceOfData::const_raw_iterator itData =
				theExecutable->getData().begin();
		TableOfInstanceOfData::const_raw_iterator endData =
				theExecutable->getData().end();
		avm_offset_t offset = 0;

		// LOAD PARAMETER & RETURN
		if( theExecutable->hasParamReturn()
			&& aMachine->hasParamReturnTable() )
		{
			BF paramReturnArgument;

			anED->makeWritableRuntimeFormStateTable();

			avm_size_t paramReturnCount = theExecutable->getParamReturnCount();
			for( ; offset < paramReturnCount ; ++itData , ++offset )
			{
				anED->setAssigned(aDataRID, offset, true);

AVM_OS_ASSERT_FATAL_ERROR_EXIT( offset == (itData)->getOffset() )
		<< "Invalid variable offset in data table !\n\t"
		<< str_header( *itData )
		<< SEND_EXIT;

				paramReturnArgument = aMachine->getParamReturn(offset);
				if( paramReturnArgument.invalid() && (itData)->hasValue() )
				{
					paramReturnArgument = (itData)->getValue();
				}

				if( paramReturnArgument.valid() )
				{
					if( (itData)->getModifier().hasNatureReference() )
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
					else if( (itData)->getModifier().hasNatureMacro() )
					{
						//!! NOTHING
					}
					else if( aDataRID.getInstance()->isAutoStart() )
							//(not theExecutable->getSpecifier().isComponentProcedure()))
					{
						if( ENV.eval(anED, aDataRID, paramReturnArgument) )
						{
							paramReturnArgument = ENV.outVAL;
						}
						// ASSERT paramForm is an LVALUE
						else //if( not (itData)->getModifier().hasNatureReference() )
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
								anED, aDataRID, (itData) );
					}

					if( not ExpressionTypeChecker::isTyped(
							(itData)->getTypeSpecifier(), paramReturnArgument) )
					{
						++errorCount;

//						getCompilerTable().incrErrorCount();
						AVM_OS_WARN
								<< aMachine->getAstElement()->errorLocation()
								<< "loadData :> Unexpected << ";

AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_WARN << std::endl << paramReturnArgument
			<< " >> as << " << (itData)->getTypeSpecifier()->strT();

	aMachine->getAstElement()->errorLocation(AVM_OS_TRACE)
			<< "loadData :> Unexpected << "
			<< str_header( paramReturnArgument ) << " >> as << "
			<< (itData)->getTypeSpecifier()->strT()
			<< " >> parameter for\n\t<< " << str_header( *itData ) << " >> !!!"
			<< std::endl;

AVM_ELSE

	AVM_OS_WARN << str_header( paramReturnArgument ) << " >> as << "
			<< (itData)->getTypeSpecifier()->strT();
AVM_ENDIF_DEBUG_FLAG( LOADING )

						AVM_OS_WARN << " >> parameter for\n\t<< "
								<< str_header( *itData ) << " >>!!!"
								<< std::endl;
					}
				}
				else
				{
					paramReturnArgument =
							ENV.createInitial(anED, aDataRID, (itData));
				}

				aDataTable->set(offset, paramReturnArgument);
			}
		}


		for( ; itData != endData ; ++itData , ++offset )
		{
			anED->setAssigned(aDataRID, offset, true);

			aDataTable->set(offset,
					ENV.createInitial(anED, aDataRID, (itData)));
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
//		APExecutionData & anED, const RuntimeID & aRID,
//		InstanceOfMachine * anInstanceMachine, bool isRecursive)
//{
//	const RuntimeID & aDataRID = anED->getRuntimeID(anInstanceMachine);
//	ExecutableForm * theExecutable = aDataRID.getExecutable();
//
//	// Load DATA
//	if( theExecutable->getData().nonempty() )
//	{
//		TableOfInstanceOfData::const_raw_iterator itData =
//				theExecutable->getData().begin();
//		TableOfInstanceOfData::const_raw_iterator endData =
//				theExecutable->getData().end();
//
//		// LOAD PARAMETER
//		if( theExecutable->hasParam() && anInstanceMachine->hasParamReturnTable() )
//		{
//			avm_size_t paramCount = theExecutable->getParamCount();
//			for( avm_offset_t offset = 0 ; offset < paramCount ; ++itData , ++offset )
//			{
//				if( (itData)->hasOnWriteRoutine() )
//				{
//					BF paramForm = anInstanceMachine->getParam(offset);
//
//					if( paramForm.valid() )
//					{
//						ENV.eval(anED, aRID, paramForm);
//						paramForm = ENV.outVAL;
//					}
//					else if( ENV.getRvalue(anED, aDataRID, (itData)).invalid() )
//					{
//						paramForm = ENV.createInitial(anED, aDataRID, (itData));
//					}
//
//					if( not ExpressionFactory::containsVariable(
//							(itData)->getOnWriteCode(), (itData)) )
//					{
//						if( not ENV.writeData(anED, aDataRID, (itData), paramForm) )
//						{
//							AVM_OS_EXIT( FAILED )
//									<< "loadInitialMonitorData:> Unvalid "
//										"Initial Value << " << paramForm.str()
//									<< " >> for onInit monitor !\n"
//									<< (itData)->toString()
//									<< SEND_EXIT;
//						}
//					}
//				}
//			}
//		}
//
//		for( ; itData != endData ; ++itData )
//		{
//			if( (itData)->hasOnWriteRoutine() )
//			{
//				BF paramForm = ENV.getRvalue(anED, aDataRID, (itData));
//				if( paramForm.invalid() )
//				{
//					paramForm = ENV.createInitial(anED, aDataRID, (itData));
//				}
//
//				if( not ExpressionFactory::containsVariable(
//						(itData)->getOnWriteCode(), (itData)) )
//				{
//					if( not ENV.writeData(anED, aDataRID, (itData), paramForm) )
//					{
//						AVM_OS_EXIT( FAILED )
//								<< "loadInitialMonitorData:> Unvalid "
//									"Initial Value << " << paramForm.str()
//								<< " >> for onInit monitor !\n"
//								<< (itData)->toString()
//								<< SEND_EXIT;
//					}
//				}
//			}
//		}
//	}
//
//	// Load MACHINE
//	if( isRecursive && theExecutable->getMachineInstance().nonempty() )
//	{
//		TableOfSymbol::const_iterator itMachine =
//				theExecutable->instance_static_begin();
//		TableOfSymbol::const_iterator endMachine =
//				theExecutable->instance_static_end();
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
bool Loader::loadBuffer(APExecutionData & anED,
		const RuntimeID & aRID, const RuntimeID & loadMachineRID)
{
	ExecutableForm * loadExecutable = loadMachineRID.getExecutable();

	if( loadExecutable->getBuffer().nonempty() )
	{
		TableOfBufferT aBufferTable( loadExecutable->getBuffer().size() );
		anED->getRuntime( loadMachineRID ).setBufferTable(aBufferTable);

		TableOfSymbol::const_iterator itBuffer = loadExecutable->getBuffer().begin();
		TableOfSymbol::const_iterator endBuffer = loadExecutable->getBuffer().end();
		for( avm_size_t offset = 0 ; itBuffer < endBuffer ; ++itBuffer , ++offset )
		{
			switch( (*itBuffer).getPolicySpecifierKind() )
			{
				case TYPE_FIFO_SPECIFIER:
				{
					aBufferTable.set(offset,
							new FifoBuffer(((*itBuffer).rawBuffer())));
					break;
				}
				case TYPE_LIFO_SPECIFIER:
				{
					aBufferTable.set(offset,
							new LifoBuffer(((*itBuffer).rawBuffer())));
					break;
				}


				case TYPE_MULTI_FIFO_SPECIFIER:
				{
					aBufferTable.set(offset,
							new MultiFifoBuffer(((*itBuffer).rawBuffer())));
					break;
				}
				case TYPE_MULTI_LIFO_SPECIFIER:
				{
					aBufferTable.set(offset,
							new MultiLifoBuffer(((*itBuffer).rawBuffer())));
					break;
				}


				case TYPE_RAM_SPECIFIER:
				{
					aBufferTable.set(offset,
							new RamBuffer(((*itBuffer).rawBuffer())));
					break;
				}

				case TYPE_MULTISET_SPECIFIER:
				{
					aBufferTable.set(offset,
							new MultisetBuffer(((*itBuffer).rawBuffer())));
					break;
				}
				case TYPE_SET_SPECIFIER:
				{
					aBufferTable.set(offset,
							new SetBuffer(((*itBuffer).rawBuffer())));
					break;
				}

				default:
				{
					AVM_OS_EXIT( FAILED )
							<< "theBuffer Nature is unexpected"
							<< SEND_EXIT;

					aBufferTable.set(offset,
							new FifoBuffer(((*itBuffer).rawBuffer())));
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
void Loader::loadMachine(APExecutionData & anED,
		const RuntimeID & aRID, const RuntimeID & loadMachineRID,
		int & thePid, avm_offset_t & theOffset)
{
	ExecutableForm * loadExecutable = loadMachineRID.getExecutable();

	if( loadExecutable->getInstanceStatic().nonempty() )
	{
		if( loadExecutable->hasInstanceStaticThis() )
		{
			anED->getRuntime( loadMachineRID ).appendChild( loadMachineRID );
		}

		TableOfSymbol::const_iterator itInstance =
				loadExecutable->instance_static_begin();
		TableOfSymbol::const_iterator endInstance =
				loadExecutable->instance_static_end();
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
RuntimeForm * Loader::dynamicLoadMachine(APExecutionData & anED,
		const RuntimeID & aRID, RuntimeForm * aModelRF,
		const RuntimeID & aParentRID, Operator * aScheduleOp)
{
	InstanceOfMachine * aMachine = aModelRF->getInstance()->clone();
//	BF bfMachine( aMachine );

	aMachine->setInstanciationCount( aModelRF->getInstanciationCount() );

	ExecutableForm * theExecutable = aMachine->getExecutable();

	aMachine->updateUfid( aModelRF->getInstanciationCount() );

	aMachine->setOffset( anED->getRuntime(aParentRID).getChildTable()->size() );


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
	avm_offset_t theOffset = anED->getTableOfRuntime().size();
	int thePid = anED->getRuntimeID(theOffset - 1).getRid() + 1;

	avm_size_t newMachineCount =
			1 + theExecutable->getrecMachineCount() + theOffset;

	int pid = thePid++;
	avm_offset_t offset = theOffset++;


	//!! TODO RESIZE & MEMORY
	anED->resize( newMachineCount );


	RuntimeID loadMachineRID(
			aModelRF->getRID(), aParentRID, pid, offset, aMachine);

	loadMachineRID.setDynamicLoaded( true );

	mConfiguration.appendRID( loadMachineRID );

	RuntimeForm * aRF = new RuntimeForm( loadMachineRID );
	anED->saveRuntimeForm(offset, aRF);

//!?! Code pour évolution future
//	aRF->setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
//	aRF->setNodeTimedCondition( ExpressionConstant::BOOLEAN_TRUE );

	if( aMachine->hasOnCreate() )
	{
		mOnCreateRoutime.append( loadMachineRID );

		anED->setRuntimeFormState(offset, PROCESS_CREATING_STATE);
	}
	else
	{
		anED->setRuntimeFormState(offset, PROCESS_DISABLED_STATE);
	}

	RuntimeForm & aParentRF = anED.getWritableRuntime( aParentRID );

	aParentRF.makeWritableChildTable();
	aParentRF.appendChild( loadMachineRID );

	aParentRF.setOnSchedule(
			loadSchedulerCode(anED, aParentRF,
					aParentRF.getExecutable()->getOnSchedule(), true) );

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
	if( theExecutable->hasOnSchedule() )
	{
		aRF->setOnSchedule(
				loadSchedulerCode(anED, (*aRF),
						theExecutable->getOnSchedule(), true) );
	}


AVM_IF_DEBUG_FLAG( LOADING )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "> end loading machine instance < "
			<< aMachine->getFullyQualifiedNameID() << " >" << std::endl;
AVM_ENDIF_DEBUG_FLAG( LOADING )


	return( aRF );
}



RuntimeForm * Loader::dynamicLoadMachine(APExecutionData & anED,
		const RuntimeID & aRID, InstanceOfMachine * anInstanceDynamic,
		const RuntimeID & aParentRID, Operator * aScheduleOp)
{
	InstanceOfMachine * aMachine = anInstanceDynamic->clone();
//	BF bfMachine( aMachine );

	aMachine->setInstanciationCount(
			anInstanceDynamic->getInstanciationCount() );

	ExecutableForm * theExecutable = aMachine->getExecutable();

//	aMachine->updateUfid( anInstanceDynamic->getInstanciationCount() );

	aMachine->setOffset(
			anED->getRuntime(aParentRID).getChildTable()->size() );


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
	avm_offset_t theOffset = anED->getTableOfRuntime().size();
	int thePid = anED->getRuntimeID(theOffset - 1).getRid() + 1;

	avm_size_t newMachineCount =
			1 + theExecutable->getrecMachineCount() + theOffset;

	int pid = thePid++;
	avm_offset_t offset = theOffset++;


	//!! TODO RESIZE & MEMORY
	anED->resize( newMachineCount );


	RuntimeID loadMachineRID(aParentRID, pid, offset, aMachine);

	loadMachineRID.setDynamicLoaded( true );

	mConfiguration.appendRID( loadMachineRID );

	RuntimeForm * aRF = new RuntimeForm( loadMachineRID );
	anED->saveRuntimeForm(offset, aRF);

//!?! Code pour évolution future
//	aRF->setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
//	aRF->setNodeTimedCondition( ExpressionConstant::BOOLEAN_TRUE );

	if( aMachine->hasOnCreate() )
	{
		mOnCreateRoutime.append( loadMachineRID );

		anED->setRuntimeFormState(offset, PROCESS_CREATING_STATE);
	}
	else
	{
		anED->setRuntimeFormState(offset, PROCESS_DISABLED_STATE);
	}

	RuntimeForm & aParentRF = anED.getWritableRuntime( aParentRID );

	aParentRF.makeWritableChildTable();
	aParentRF.appendChild( loadMachineRID );

	aParentRF.setOnSchedule( loadSchedulerCode(anED, aParentRF,
			aParentRF.getExecutable()->getOnSchedule(), false) );

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
	if( theExecutable->hasOnSchedule() )
	{
		aRF->setOnSchedule(
				loadSchedulerCode(anED, (*aRF),
						theExecutable->getOnSchedule(), true) );
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
		APExecutionData & anED, RuntimeID & aRoutingRID)
{
	while( aRoutingRID.valid() )
	{
		if( aRoutingRID.getExecutable()->hasRouter4Model() )
		{
			const Router & aRouter = aRoutingRID.getExecutable()
					->getRouter4Model( aRoutingRID.getExecutable() );

			if( aRouter.valid() )
			{
				return( aRouter );
			}
		}

		aRoutingRID = aRoutingRID.getPRID();
	}

	return( Router::_NULL_ );
}

/**
 * cloneUpdateRouter
 */
static Router cloneUpdateRouter(const Router & loadRouter,
		const RuntimeID & aRoutingRID,
		const RuntimeID & loadMachineRID)
{
	avm_size_t routeCount = loadRouter.getRouteID();

	Router newRouter(loadMachineRID.getInstance(), routeCount, routeCount);

	RoutingData aRoutingData;

	// GLOBAL INPUT or OUTPUT ROUTE
	avm_size_t offset = 0;
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
bool Loader::loadRouter(APExecutionData & anED,
		const RuntimeID & aRID, const RuntimeID & loadMachineRID)
{
	ExecutableForm * loadExecutable = loadMachineRID.getExecutable();

	// Load ROUTER
	if( loadExecutable->hasPort() || loadExecutable->hasRouter4This() )
	{
		RuntimeForm & loadRF = anED->getRuntime( loadMachineRID );

		Router parentLoadRouter;
		RuntimeID aRoutingRID;
		TableOfRouter * containerRouterTable = NULL;

		if( loadMachineRID.hasPRID() )
		{
			containerRouterTable = &( loadMachineRID.getPRID().
					getExecutable()->getRouters4Instance() );

			parentLoadRouter = anED->getRuntime(
					loadMachineRID.getPRID() ).getRouter();
		}

		if( loadExecutable->hasRouter4Instance() )
		{
			const Router & theRouter4This = loadExecutable->getRouter4This();

			if( (containerRouterTable != NULL)
				&& containerRouterTable->populated() )
			{
				const Router & theRouter4Parent = containerRouterTable->get(
						loadMachineRID.getInstance()->getOffset());

				avm_size_t routeCount = theRouter4This.getRouteID();

				Router newRouter(
						loadMachineRID.getInstance(), routeCount, routeCount);
				loadRF.setRouter( newRouter );

				RoutingData aRoutingData;

				// GLOBAL INPUT or OUTPUT ROUTE
				for( avm_size_t offset = 0 ; offset < routeCount ; ++offset )
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
				TableOfSymbol::const_iterator itPort =
						loadExecutable->getPort().begin();
				TableOfSymbol::const_iterator endPort =
						loadExecutable->getPort().end();
				for( ; itPort != endPort ; ++itPort )
				{
					if( (*itPort).port().isPort() )
					{
						if( (*itPort).getModifier().hasDirectionInput() )
						{
							if( (*itPort).getModifier().isVisibilityPublic() )
							{
								aRoutingData = theRouter4Parent.getInputRouting(
										(*itPort).getRouteOffset());

								aRoutingRID = loadMachineRID.getPRID();
							}
							else
							{
								aRoutingData = theRouter4This.getInputRouting(
										(*itPort).getRouteOffset());

								aRoutingRID = loadMachineRID;
							}

							aRoutingData.makeWritable();
							aRoutingData.setRuntimeRID(aRoutingRID);

							newRouter.appendInputRouting( aRoutingData );
						}
						// NO ELSE because of INOUT PORT
						if( (*itPort).getModifier().hasDirectionOutput() )
						{
							if( (*itPort).getModifier().isVisibilityPublic() )
							{
								aRoutingData = theRouter4Parent.getOutputRouting(
										(*itPort).getRouteOffset());
								aRoutingRID = loadMachineRID.getPRID();
							}
							else
							{
								aRoutingData = theRouter4This.getOutputRouting(
										(*itPort).getRouteOffset());
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
		else if( (containerRouterTable != NULL)
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
//@debug:
//		AVM_OS_TRACE << "loadRouter: " << loadRF.getFullyQualifiedNameID() << std::endl;
//		loadRF.getRouter().toStream(AVM_OS_TRACE);
	}

	return( true );
}


/**
 * dynamicLoadRouter
 */
bool Loader::dynamicLoadRouter(APExecutionData & anED,
		const RuntimeID & loadMachineRID)
{
	ExecutableForm * loadExecutable = loadMachineRID.getExecutable();

	// Load ROUTER
	if( loadExecutable->hasPort() || loadExecutable->hasRouter4This() )
	{
		RuntimeForm & loadRF = anED->getRuntime( loadMachineRID );

		const TableOfRouter & containerRouterTable = loadMachineRID.
				getPRID().getExecutable()->getRouters4Model();

		Router parentLoadRouter = anED->getRuntime(
				loadMachineRID.getPRID() ).getRouter();

		if( loadExecutable->hasRouter4Instance() )
		{
			const Router & theRouter4This = loadExecutable->getRouter4This();

			if( containerRouterTable.nonempty() )
			{
				const Router & theRouter4Parent = containerRouterTable.get(
					loadMachineRID.getInstance()->getInstanceModel()->getOffset());

				avm_size_t aRouteID = theRouter4This.getRouteID();

				Router newRouter(
						loadMachineRID.getInstance(), aRouteID, aRouteID);
				loadRF.setRouter( newRouter );

				RoutingData aRoutingData;

				// GLOBAL INPUT or OUTPUT ROUTE
				for( avm_size_t offset = 0 ; offset < aRouteID ; ++offset )
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
				TableOfSymbol::const_iterator itPort =
						loadExecutable->getPort().begin();
				TableOfSymbol::const_iterator endPort =
						loadExecutable->getPort().end();
				for( ; itPort != endPort ; ++itPort )
				{
					if( (*itPort).getModifier().hasDirectionInput() )
					{
						if( (*itPort).getModifier().isVisibilityPublic() )
						{
							newRouter.appendInputRouting( theRouter4Parent
									.getInputRouting((*itPort).getRouteOffset()) );
						}
						else
						{
							newRouter.appendInputRouting( theRouter4This
									.getInputRouting((*itPort).getRouteOffset()) );
						}
					}
					// NO ELSE because of INOUT PORT
					if( (*itPort).getModifier().hasDirectionOutput() )
					{
						if( (*itPort).getModifier().isVisibilityPublic() )
						{
							newRouter.appendOutputRouting( theRouter4Parent
								.getOutputRouting((*itPort).getRouteOffset()) );
						}
						else
						{
							newRouter.appendOutputRouting( theRouter4This
								.getOutputRouting((*itPort).getRouteOffset()) );
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

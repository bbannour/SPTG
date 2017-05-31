/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 nov. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmInvokePrimitive.h"


#include <builder/Loader.h>

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionDataFactory.h>
#include <computer/ExecutionEnvironment.h>

#include <fml/executable/AvmLambda.h>
#include <fml/executable/AvmProgram.h>
#include <fml/executable/AvmTransition.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/LocalRuntime.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeLib.h>

#include <fml/type/TypeManager.h>

#include <sew/SymbexEngine.h>

#include <util/ExecutionTime.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// execution of a INVOKE NEW meta program
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_InvokeNew::seval(EvaluationEnvironment & ENV)
{
	InstanceOfMachine * anInstanceDynamic =
			ENV.mARG->at(0).to_ptr< InstanceOfMachine >();

	ENV.outED = ENV.mARG->outED;

	RuntimeID invokerRID = ENV.outED->mRID;

	if( ENV.outED->couldBeInstanciated( anInstanceDynamic ) )
	{
		const RuntimeID & aCompositeRID =
				ENV.outED->mRID.getCompositeComponentParent();

		Operator * aScheduleOp = aCompositeRID.
				getExecutable()->getOnConcurrencyOperator();

		RuntimeForm * newRF =
				ENV.PRIMITIVE_PROCESSOR.getLoader().dynamicLoadMachine(
						ENV.outED, ENV.outED->mRID, anInstanceDynamic,
						aCompositeRID, aScheduleOp );

		// RUNNING onCREATE
		if( not ENV.PRIMITIVE_PROCESSOR.getLoader().
				finalizeRunningOnCreate(ENV, ENV.outED) )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "InvokeNew: Failed to finalize loading by "
							"running << onCreate Primitive >> !!!"
					<< SEND_EXIT;
		}

		const RuntimeID & newRID = newRF->getRID();
		ENV.outVAL = newRID;

//[REGRESSION]!TODO
		ExecutableForm * modelExecutable = newRID.getExecutable();
		InstanceOfData * aVar = NULL;
		avm_size_t offset = 0;
		ENV.mARG->begin(1);
		for( ; ENV.mARG->hasNext() ; ENV.mARG->next() , ++offset )
		{
			aVar = modelExecutable->rawParamData(offset);

//AVM_OS_COUT << std::endl << invokerRID.strUniqId()
//		<< " , " << newRID.getFullyQualifiedNameID()
//		<< " |= " << aVar->getFullyQualifiedNameID()
//		<< " " << ENV.mARG->current().str() << std::endl;

			if( not ENV.setRvalue(ENV.outED, newRID, aVar, ENV.mARG->current()) )
			{
				return( false );
			}
		}


		BFCode onStartProgram = anInstanceDynamic->getOnStart();
		if( onStartProgram.valid() )
		{
			ExecutionEnvironment tmpENV(ENV, ENV.outED, newRID, onStartProgram);

			if( tmpENV.run(PROCESS_STARTING_STATE) )
			{
				tmpENV.outEDS.pop_last_to( ENV.outED );

				if( tmpENV.outEDS.nonempty() )
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unsupported << new >> Primitive which execution "
								"create more than one Execution Context :>\n"
							<< ENV.inCODE->toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;
				}

				ENV.outED.mwsetRuntimeFormState(newRID,
						PROCESS_STARTING_STATE,  PROCESS_IDLE_STATE);
			}
			else
			{
				return( false );
			}
		}
		else
		{
			ENV.outED.mwsetRuntimeFormState(newRID, PROCESS_IDLE_STATE);
		}

		ENV.outED->mRID = invokerRID;

		return( true );
	}
	else
	{
		ENV.outVAL = RuntimeLib::RID_NIL;

		return( true );
	}
}


bool AvmPrimitive_InvokeNew::run(ExecutionEnvironment & ENV)
{
	InstanceOfMachine * anInstanceDynamic =
			ENV.mARG->at(0).to_ptr< InstanceOfMachine >();

	APExecutionData outED = ENV.mARG->outED;

	RuntimeID invokerRID = outED->mRID;

	if( outED->couldBeInstanciated( anInstanceDynamic ) )
	{
		const RuntimeID & aCompositeRID =
				outED->mRID.getCompositeComponentParent();

		Operator * aScheduleOp = aCompositeRID.
				getExecutable()->getOnConcurrencyOperator();

		RuntimeForm * newRF = ENV.getLoader().dynamicLoadMachine(outED,
				outED->mRID, anInstanceDynamic, aCompositeRID, aScheduleOp );

		// RUNNING onCREATE
		if( not ENV.PRIMITIVE_PROCESSOR.getLoader().
				finalizeRunningOnCreate(ENV, outED) )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "InvokeNew: Failed to finalize loading by "
							"running << onCreate Primitive >> !!!"
					<< SEND_EXIT;
		}

		const RuntimeID & newRID = newRF->getRID();


		BFCode onStartProgram = anInstanceDynamic->getOnStart();
		if( onStartProgram.valid() )
		{
			ExecutionEnvironment tmpENV(ENV, outED, newRID, onStartProgram);

			if( tmpENV.run(PROCESS_STARTING_STATE) )
			{
				ENV.spliceNotOutput( tmpENV );

				ListOfAPExecutionData::iterator itED = tmpENV.outEDS.begin();
				ListOfAPExecutionData::iterator endED = tmpENV.outEDS.end();
				for( ; itED != endED ; ++itED )
				{
					(*itED).mwsetRuntimeFormState(newRID,
							PROCESS_STARTING_STATE,  PROCESS_IDLE_STATE);

					(*itED)->mRID = invokerRID;

					ENV.appendOutput( *itED );
				}
			}
			else
			{
				return( false );
			}
		}
		else if( not ENV.appendOutput_mwsetPES(
					outED, newRID, PROCESS_IDLE_STATE) )
		{
			outED->mRID = invokerRID;

			if( not ENV.appendOutput_mwsetPES(
					outED, newRID, PROCESS_IDLE_STATE) )
			{
				return( false );
			}
		}

		return( true );
	}
	else
	{
		return( true );
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// execution of a INVOKE ROUTINE program
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmBaseInvokePrimitive::pushLocalVars(
		ExecutionEnvironment & ENV, const BaseAvmProgram & aProgram)
{
	ENV.inED.makeWritable();
	ENV.inED->makeWritableLocalRuntimeStack();

	LocalRuntime aLocalRuntime( aProgram );
	ENV.inED->getLocalRuntimes()->push( aLocalRuntime );

	EvaluationEnvironment eENV( ENV );

	TableOfInstanceOfData::const_raw_iterator itData = aProgram.getData().begin();
	TableOfInstanceOfData::const_raw_iterator endData = aProgram.getData().end();
	for( avm_size_t i = 0 ; itData != endData ; ++itData , ++i )
	{
		if( (itData)->hasValue() )
		{
			eENV.seval( (itData)->getValue() );
			aLocalRuntime.setData(i, eENV.outVAL);
		}
		else
		{
			BFList paramList;

			aLocalRuntime.setData(i, ENV.createNewFreshParam(
					ENV.inED->mRID, (itData), paramList) );

			ENV.inED.appendParameters( paramList );
		}
	}

	return( true );
}


bool AvmBaseInvokePrimitive::pushLocalVar1(ExecutionEnvironment & ENV,
		const BaseAvmProgram & aProgram, const BF & aParam)
{
	ENV.inED.makeWritable();
	ENV.inED->makeWritableLocalRuntimeStack();

	LocalRuntime aLocalRuntime( aProgram );
	ENV.inED->getLocalRuntimes()->push( aLocalRuntime );

	aLocalRuntime.setData(static_cast< avm_size_t >(0), aParam);

	return( true );
}


bool AvmBaseInvokePrimitive::pushLocalVars(ExecutionEnvironment & ENV,
		const BaseAvmProgram & aProgram, ArrayBF * params)
{
	ENV.inED.makeWritable();
	ENV.inED->makeWritableLocalRuntimeStack();

	LocalRuntime aLocalRuntime( aProgram );
	ENV.inED->getLocalRuntimes()->push( aLocalRuntime );

	EvaluationEnvironment eENV( ENV );

	TableOfInstanceOfData::const_raw_iterator itData = aProgram.getData().begin();
	TableOfInstanceOfData::const_raw_iterator endData = aProgram.getData().end();
	for( avm_size_t i = 0 ; itData != endData ; ++itData , ++i )
	{
		if( params->at(i).valid() )
		{
//			eENV.seval( params->get(i) );
//			aLocalRuntime.setData(i, eENV.outVAL);
			aLocalRuntime.setData(i, params->at(i));
		}
		else if( (itData)->hasValue() )
		{
			eENV.seval( (itData)->getValue() );
			aLocalRuntime.setData(i, eENV.outVAL);
		}
		else
		{
			BFList paramList;

			aLocalRuntime.setData(i, ENV.createNewFreshParam(
					ENV.inED->mRID, (itData), paramList) );

			ENV.inED.appendParameters( paramList );
		}
	}

	return( true );
}



bool AvmBaseInvokePrimitive::popLocalVars(APExecutionData & anED)
{
	anED.makeWritable();
	anED->makeWritableLocalRuntimeStack();

	anED->getLocalRuntimes()->pop();

	if( not anED->hasLocalRuntime() )
	{
		anED->destroyLocalRuntimeStack();
	}

	return( true );
}




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// execution of a INVOKE EXECUTABLE routine
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


bool AvmPrimitive_InvokeRoutine::run(
		ExecutionEnvironment & ENV, const AvmProgram & anAvmProgram)
{
	ExecutionTime theExecutionTimeManager(false);
AVM_IF_DEBUG_FLAG( TIME )
	theExecutionTimeManager.start_time();
AVM_ENDIF_DEBUG_FLAG( TIME )


	ExecutionEnvironment tmpENV(ENV, anAvmProgram.getCode());

	tmpENV.inED.makeWritable();

//	ExecutionDataFactory::appendRunnableElementTrace(tmpENV.inED,
//			BF(new ExecutionConfiguration(tmpENV.inED->mRID, anAvmProgram)));

	if( not tmpENV.run() )
	{
		return( false );
	}

	APExecutionData tmpED;

	// OUTPUT EDS traitement
	while( tmpENV.outEDS.nonempty() )
	{
		tmpENV.outEDS.pop_first_to( tmpED );

		// Verification of EXECUTION ENDING STATUS
		switch( tmpED->getAEES() )
		{
			case AEES_STMNT_NOTHING:
			case AEES_STMNT_FINAL:
			case AEES_STMNT_DESTROY:
			{
				tmpED.mwsetAEES( AEES_OK );

				ENV.outEDS.append( tmpED );

				break;
			}
			case AEES_OK:
			{
				ENV.outEDS.append( tmpED );

				break;
			}

			case AEES_STMNT_EXIT:
			case AEES_STMNT_EXIT_ALL:
			case AEES_STMNT_FATAL_ERROR:
			case AEES_SYMBOLIC_EXECUTION_LIMITATION:
			{
				ENV.exitEDS.append( tmpED );

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

	// IRQ EDS traitement
	while( tmpENV.irqEDS.nonempty() )
	{
		tmpENV.irqEDS.pop_last_to( tmpED );

		// Verification of EXECUTION ENDING STATUS
		switch( tmpED->getAEES() )
		{
			case AEES_STMNT_BREAK:
			case AEES_STMNT_CONTINUE:
			case AEES_STMNT_RETURN:
			{
				tmpED.mwsetAEES( AEES_OK );

				ENV.outEDS.append( tmpED );

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as irqEDS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

	// EXIT EDS traitement
	ENV.spliceExit(tmpENV);

	// Sync EDS traitement
	ENV.spliceSync_mwStorePos(tmpENV);

AVM_IF_DEBUG_FLAG( TIME )
	theExecutionTimeManager.finish_time();
	AVM_OS_TRACE << theExecutionTimeManager.time_stat();// << std::endl;
AVM_ENDIF_DEBUG_FLAG( TIME )

	return( true );
}


bool AvmPrimitive_InvokeRoutine::run(ExecutionEnvironment & ENV,
		const AvmProgram & anAvmProgram, const BF & aParam)
{
	ExecutionTime theExecutionTimeManager(false);
AVM_IF_DEBUG_FLAG( TIME )
	theExecutionTimeManager.start_time();
AVM_ENDIF_DEBUG_FLAG( TIME )


	ExecutionEnvironment tmpENV(ENV, anAvmProgram.getCode());

	tmpENV.inED.makeWritable();

//	ExecutionDataFactory::appendRunnableElementTrace(tmpENV.inED,
//			BF(new ExecutionConfiguration(tmpENV.inED->mRID, anAvmProgram)));

	// Allocated local data table
	pushLocalVar1(tmpENV, anAvmProgram, aParam);

	if( not tmpENV.run() )
	{
		return( false );
	}

	APExecutionData tmpED;

	// OUTPUT EDS traitement
	while( tmpENV.outEDS.nonempty() )
	{
		tmpENV.outEDS.pop_first_to( tmpED );

		// Verification of EXECUTION ENDING STATUS
		switch( tmpED->getAEES() )
		{
			case AEES_STMNT_NOTHING:
			case AEES_STMNT_FINAL:
			case AEES_STMNT_DESTROY:
			{
				tmpED.mwsetAEES( AEES_OK );

				// Free local data table
				popLocalVars(tmpED);

				ENV.outEDS.append( tmpED );

				break;
			}
			case AEES_OK:
			{
				// Free local data table
				popLocalVars(tmpED);

				ENV.outEDS.append( tmpED );

				break;
			}

			case AEES_STMNT_EXIT:
			case AEES_STMNT_EXIT_ALL:
			case AEES_STMNT_FATAL_ERROR:
			case AEES_SYMBOLIC_EXECUTION_LIMITATION:
			{
				ENV.exitEDS.append( tmpED );

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

	// IRQ EDS traitement
	while( tmpENV.irqEDS.nonempty() )
	{
		tmpENV.irqEDS.pop_last_to( tmpED );

		// Verification of EXECUTION ENDING STATUS
		switch( tmpED->getAEES() )
		{
			case AEES_STMNT_BREAK:
			case AEES_STMNT_CONTINUE:
			case AEES_STMNT_RETURN:
			{
				tmpED.mwsetAEES( AEES_OK );

				// Free local data table
				popLocalVars(tmpED);

				ENV.outEDS.append( tmpED );

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as irqEDS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

	// EXIT EDS traitement
	while( tmpENV.exitEDS.nonempty() )
	{
		tmpENV.exitEDS.pop_last_to( tmpED );

		// Free local data table
		popLocalVars(tmpED);

		ENV.exitEDS.append( tmpED );
	}


	// Sync EDS traitement
	ENV.spliceSync_mwStorePos(tmpENV);

AVM_IF_DEBUG_FLAG( TIME )
	theExecutionTimeManager.finish_time();
	AVM_OS_TRACE << theExecutionTimeManager.time_stat();// << std::endl;
AVM_ENDIF_DEBUG_FLAG( TIME )

	return( true );
}


bool AvmPrimitive_InvokeRoutine::run(ExecutionEnvironment & ENV)
{
	const BF & aCode = ENV.inCODE->first();
	const AvmProgram & anAvmProgram = aCode.to_ref< AvmProgram >();

	ExecutionTime theExecutionTimeManager(false);
AVM_IF_DEBUG_FLAG( TIME )
	theExecutionTimeManager.start_time();
AVM_ENDIF_DEBUG_FLAG( TIME )


	ExecutionEnvironment tmpENV(ENV, anAvmProgram.getCode());

	tmpENV.inED.makeWritable();

	ExecutionDataFactory::appendRunnableElementTrace(tmpENV.inED,
			BF(new ExecutionConfiguration(tmpENV.inED->mRID, aCode)));

	if( anAvmProgram.hasData() )
	{
		if( ENV.inCODE->populated() )
		{
			pushLocalVars(tmpENV, anAvmProgram,
					ENV.inCODE->second().to_ptr< ArrayBF >());
		}
		else
		{
			pushLocalVars(tmpENV, anAvmProgram);
		}
	}

	if( not tmpENV.run() )
	{
		return( false );
	}

	APExecutionData tmpED;

	// OUTPUT EDS traitement
	while( tmpENV.outEDS.nonempty() )
	{
		tmpENV.outEDS.pop_first_to( tmpED );

		// Verification of EXECUTION ENDING STATUS
		switch( tmpED->getAEES() )
		{
			case AEES_STMNT_NOTHING:
			case AEES_STMNT_FINAL:
			case AEES_STMNT_DESTROY:
			{
				tmpED.mwsetAEES( AEES_OK );

				// Free local data table
				if( anAvmProgram.hasData() )
				{
					popLocalVars(tmpED);
				}

				ENV.outEDS.append( tmpED );

				break;
			}
			case AEES_OK:
			{
				// Free local data table
				if( anAvmProgram.hasData() )
				{
					popLocalVars(tmpED);
				}

				ENV.outEDS.append( tmpED );

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

	// IRQ EDS traitement
	while( tmpENV.irqEDS.nonempty() )
	{
		tmpENV.irqEDS.pop_last_to( tmpED );

		// Verification of EXECUTION ENDING STATUS
		switch( tmpED->getAEES() )
		{
			case AEES_STMNT_BREAK:
			case AEES_STMNT_CONTINUE:
			case AEES_STMNT_RETURN:
			{
				tmpED.mwsetAEES( AEES_OK );

				if( anAvmProgram.hasData() )
				{
					popLocalVars(tmpED);
				}

				ENV.outEDS.append( tmpED );

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as irqEDS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

	// EXIT EDS traitement
	while( tmpENV.exitEDS.nonempty() )
	{
		tmpENV.exitEDS.pop_last_to( tmpED );

		if( anAvmProgram.hasData() )
		{
			popLocalVars(tmpED);
		}

		ENV.exitEDS.append( tmpED );
	}


	// Sync EDS traitement
	ENV.spliceSync_mwStorePos(tmpENV);

AVM_IF_DEBUG_FLAG( TIME )
	theExecutionTimeManager.finish_time();
	AVM_OS_TRACE << theExecutionTimeManager.time_stat();// << std::endl;
AVM_ENDIF_DEBUG_FLAG( TIME )

	return( true );
}


bool AvmPrimitive_InvokeRoutine::resume(ExecutionEnvironment & ENV)
{
	const AvmProgram & anAvmProgram = ENV.inCODE->first().to_ref< AvmProgram >();

	APExecutionData outED = ENV.inED;

	// Verification of EXECUTION ENDING STATUS
	switch( outED->getAEES() )
	{
		case AEES_STMNT_BREAK:
		case AEES_STMNT_CONTINUE:
		case AEES_STMNT_RETURN:

		case AEES_STMNT_NOTHING:
		case AEES_STMNT_FINAL:
		case AEES_STMNT_DESTROY:
		{
			outED.mwsetAEES( AEES_OK );

			// Free local data table
			if( anAvmProgram.hasData() )
			{
				popLocalVars(outED);
			}

			ENV.outEDS.append( outED );

			break;
		}
		case AEES_OK:
		case AEES_STEP_RESUME:
		{
			if( anAvmProgram.hasData() )
			{
				popLocalVars(outED);
			}

			ENV.outEDS.append( outED );

			break;
		}

		// Sync EDS traitement
		case AEES_STEP_MARK:
		case AEES_WAITING_INCOM_RDV:
		case AEES_WAITING_OUTCOM_RDV:
		case AEES_WAITING_JOIN_FORK:
		{
			ENV.appendSync_mwStorePos(outED);

			break;
		}

		case AEES_STMNT_EXIT:
		case AEES_STMNT_EXIT_ALL:
		case AEES_STMNT_FATAL_ERROR:
		case AEES_SYMBOLIC_EXECUTION_LIMITATION:
		{
			if( anAvmProgram.hasData() )
			{
				popLocalVars(outED);
			}

			ENV.exitEDS.append( outED );

			break;
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected ENDIND EXECUTION STATUS :> "
					<< RuntimeDef::strAEES( outED->mAEES ) << " !!!"
					<< SEND_EXIT;

			break;
		}
	}

	return( true );
}





////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// execution of a INVOKE TRANSITION transition
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_InvokeTransition::run(ExecutionEnvironment & ENV)
{
	const BF & aCode = ENV.inCODE->first();
	const AvmProgram & anAvmProgram = aCode.to_ref< AvmTransition >();

	ExecutionTime theExecutionTimeManager(false);
AVM_IF_DEBUG_FLAG( TIME )
	theExecutionTimeManager.start_time();
AVM_ENDIF_DEBUG_FLAG( TIME )


	ExecutionEnvironment tmpENV(ENV, anAvmProgram.getCode());

	tmpENV.inED.makeWritable();

	ExecutionDataFactory::appendRunnableElementTrace(tmpENV.inED,
			BF(new ExecutionConfiguration(tmpENV.inED->mRID, aCode)));

	if( not tmpENV.run() )
	{
		return( false );
	}

	APExecutionData tmpED;

	// OUTPUT EDS traitement
	while( tmpENV.outEDS.nonempty() )
	{
		tmpENV.outEDS.pop_first_to( tmpED );

		// Verification of EXECUTION ENDING STATUS
		switch( tmpED->getAEES() )
		{
			case AEES_STMNT_NOTHING:
			case AEES_STMNT_FINAL:
			case AEES_STMNT_DESTROY:
			{
				tmpED.mwsetAEES( AEES_OK );

				ENV.outEDS.append( tmpED );

				break;
			}
			case AEES_OK:
			case AEES_STEP_RESUME:
			{
				ENV.outEDS.append( tmpED );

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

	// IRQ EDS traitement
	while( tmpENV.irqEDS.nonempty() )
	{
		tmpENV.irqEDS.pop_last_to( tmpED );

		// Verification of EXECUTION ENDING STATUS
		switch( tmpED->getAEES() )
		{
			case AEES_STMNT_BREAK:
			case AEES_STMNT_CONTINUE:
			case AEES_STMNT_RETURN:
			{
				tmpED.mwsetAEES( AEES_OK );

				ENV.outEDS.append( tmpED );

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as irqEDS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

	// EXIT EDS traitement
	ENV.spliceExit(tmpENV);

	// Sync EDS traitement
	ENV.spliceSync_mwStorePos(tmpENV);

AVM_IF_DEBUG_FLAG( TIME )
	theExecutionTimeManager.finish_time();
	AVM_OS_TRACE << theExecutionTimeManager.time_stat();// << std::endl;
AVM_ENDIF_DEBUG_FLAG( TIME )

	return( true );
}


bool AvmPrimitive_InvokeTransition::resume(ExecutionEnvironment & ENV)
{
	APExecutionData outED = ENV.inED;

	// Verification of EXECUTION ENDING STATUS
	switch( outED->getAEES() )
	{
		case AEES_STMNT_BREAK:
		case AEES_STMNT_CONTINUE:
		case AEES_STMNT_RETURN:

		case AEES_STMNT_NOTHING:
		case AEES_STMNT_FINAL:
		case AEES_STMNT_DESTROY:
		{
			outED.mwsetAEES( AEES_OK );

			ENV.outEDS.append( outED );

			break;
		}
		case AEES_OK:
		case AEES_STEP_RESUME:
		{
			ENV.outEDS.append( outED );

			break;
		}

		// Sync EDS traitement
		case AEES_STEP_MARK:
		case AEES_WAITING_INCOM_RDV:
		case AEES_WAITING_OUTCOM_RDV:
		case AEES_WAITING_JOIN_FORK:
		{
			ENV.appendSync_mwStorePos(outED);

			break;
		}

		case AEES_STMNT_EXIT:
		case AEES_STMNT_EXIT_ALL:
		case AEES_STMNT_FATAL_ERROR:
		case AEES_SYMBOLIC_EXECUTION_LIMITATION:
		{
			ENV.exitEDS.append( outED );

			break;
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected ENDIND EXECUTION STATUS :> "
					<< RuntimeDef::strAEES( outED->mAEES ) << " !!!"
					<< SEND_EXIT;

			break;
		}
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// execution of a INVOKE EXECUTABLE program
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_InvokeMethod::run(ExecutionEnvironment & ENV)
{
	return( false );
}

bool AvmPrimitive_InvokeMethod::seval(EvaluationEnvironment & ENV)
{
	return( false );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// execution of a INVOKE FUNCTION program
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_InvokeFunction::seval(EvaluationEnvironment & ENV)
{
	return( false );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// execution of a INVOKE PROGRAM program
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_InvokeProgram::run(ExecutionEnvironment & ENV)
{
	const BF & aCode = ENV.inCODE->first();
	const AvmProgram & anAvmProgram = aCode.to_ref< AvmProgram >();

	ExecutionTime theExecutionTimeManager(false);
AVM_IF_DEBUG_FLAG( TIME )
		theExecutionTimeManager.start_time();
AVM_ENDIF_DEBUG_FLAG( TIME )


	ExecutionEnvironment tmpENV(ENV, anAvmProgram.getCode());

	tmpENV.inED.makeWritable();

	ExecutionDataFactory::appendRunnableElementTrace(tmpENV.inED,
			BF(new ExecutionConfiguration(tmpENV.inED->mRID, aCode)));

	if( anAvmProgram.hasData() )
	{
		if( ENV.inCODE->populated() )
		{
			pushLocalVars(tmpENV, anAvmProgram,
					ENV.inCODE->second().to_ptr< ArrayBF >());
		}
		else
		{
			pushLocalVars(tmpENV, anAvmProgram);
		}
	}

	if( not tmpENV.run() )
	{
		return( false );
	}

	APExecutionData tmpED;

	// OUTPUT EDS traitement
	while( tmpENV.outEDS.nonempty() )
	{
		tmpENV.outEDS.pop_first_to( tmpED );

		// Verification of EXECUTION ENDING STATUS
		switch( tmpED->getAEES() )
		{
			case AEES_STMNT_NOTHING:
			case AEES_STMNT_FINAL:
			case AEES_STMNT_DESTROY:
			{
				tmpED.mwsetAEES( AEES_OK );

				// Free local data table
				if( anAvmProgram.hasData() )
				{
					popLocalVars(tmpED);
				}

				ENV.outEDS.append( tmpED );

				break;
			}
			case AEES_OK:
			{
				if( anAvmProgram.hasData() )
				{
					popLocalVars(tmpED);
				}

				ENV.outEDS.append( tmpED );

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

	// IRQ EDS traitement
	while( tmpENV.irqEDS.nonempty() )
	{
		tmpENV.irqEDS.pop_last_to( tmpED );

		// Verification of EXECUTION ENDING STATUS
		switch( tmpED->getAEES() )
		{
			case AEES_STMNT_BREAK:
			case AEES_STMNT_CONTINUE:
			case AEES_STMNT_RETURN:
			{
				tmpED.mwsetAEES( AEES_OK );

				if( anAvmProgram.hasData() )
				{
					popLocalVars(tmpED);
				}

				ENV.outEDS.append( tmpED );

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as irqEDS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;

				break;
			}
		}
	}

	// EXIT EDS traitement
	while( tmpENV.exitEDS.nonempty() )
	{
		tmpENV.exitEDS.pop_last_to( tmpED );

		if( anAvmProgram.hasData() )
		{
			popLocalVars(tmpED);
		}

		ENV.exitEDS.append( tmpED );
	}


	// Sync EDS traitement
	ENV.spliceSync_mwStorePos(tmpENV);

AVM_IF_DEBUG_FLAG( TIME )
	theExecutionTimeManager.finish_time();
	AVM_OS_TRACE << theExecutionTimeManager.time_stat();// << std::endl;
AVM_ENDIF_DEBUG_FLAG( TIME )

	return( true );
}


bool AvmPrimitive_InvokeProgram::resume(ExecutionEnvironment & ENV)
{
	const AvmProgram & anAvmProgram = ENV.inCODE->first().to_ref< AvmProgram >();

	APExecutionData outED = ENV.inED;

	// Verification of EXECUTION ENDING STATUS
	switch( outED->getAEES() )
	{
		case AEES_STMNT_BREAK:
		case AEES_STMNT_CONTINUE:
		case AEES_STMNT_RETURN:

		case AEES_STMNT_NOTHING:
		case AEES_STMNT_FINAL:
		case AEES_STMNT_DESTROY:
		{
			outED.mwsetAEES( AEES_OK );

			// Free local data table
			if( anAvmProgram.hasData() )
			{
				popLocalVars(outED);
			}

			ENV.outEDS.append( outED );

			break;
		}
		case AEES_OK:
		case AEES_STEP_RESUME:
		{
			if( anAvmProgram.hasData() )
			{
				popLocalVars(outED);
			}

			ENV.outEDS.append( outED );

			break;
		}

		// Sync EDS traitement
		case AEES_STEP_MARK:
		case AEES_WAITING_INCOM_RDV:
		case AEES_WAITING_OUTCOM_RDV:
		case AEES_WAITING_JOIN_FORK:
		{
			ENV.appendSync_mwStorePos(outED);

			break;
		}

		case AEES_STMNT_EXIT:
		case AEES_STMNT_EXIT_ALL:
		case AEES_STMNT_FATAL_ERROR:
		case AEES_SYMBOLIC_EXECUTION_LIMITATION:
		{
			if( anAvmProgram.hasData() )
			{
				popLocalVars(outED);
			}

			ENV.exitEDS.append( outED );

			break;
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected ENDIND EXECUTION STATUS :> "
					<< RuntimeDef::strAEES( outED->mAEES ) << " !!!"
					<< SEND_EXIT;

			break;
		}
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// execution of a INVOKE LAMBDA APPLY program
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_InvokeLambdaApply::seval(EvaluationEnvironment & ENV)
{
	bool rtCode = true;

	const AvmCode * applyCode = ENV.inCODE;

	AvmCode::const_iterator itArg = applyCode->begin();
	AvmCode::const_iterator endArg = applyCode->end();

	// First arg is the lambda function
	BF theFunction = (*itArg);
	if( theFunction.isnot< AvmLambda >() )
	{
		if( not ENV.seval(theFunction) )
		{
			return( false );
		}
		theFunction = ENV.outVAL;
	}

	if( theFunction.is< AvmLambda >() )
	{
		// First paramater is in second position,
		++itArg;

		const AvmLambda & aLambdaFun = theFunction.to_ref< AvmLambda >();

		// CREATE LOCAL VARIABLE TABLE
		if( not ENV.inED->hasLocalRuntimeStack())
		{
			ENV.inED->createLocalRuntimeStack();
		}
		LocalRuntime aLocalRuntime( aLambdaFun );


		// COMPLETE REDUCTION :> the result is a TERM
		if( aLambdaFun.boundVarCount() < applyCode->size() )
		{
			// INITIALIZE LOCAL VARIABLE TABLE
			avm_size_t offset = 0;
			avm_size_t endOffset = aLambdaFun.getData().size();
			for( ; offset < endOffset ; ++itArg , ++offset )
			{
				if( not ENV.seval(*itArg ) )
				{
					return( false );
				}
				aLocalRuntime.setData(offset, ENV.outVAL);
			}

			// LOAD LOCAL VARIABLE TABLE
			ENV.inED->getLocalRuntimes()->push( aLocalRuntime );

			// REDUCTION
			rtCode = ENV.seval(aLambdaFun.getExpression());
		}

		// PARTIAL REDUCTION :> the result is a Lambda Function
		else
		{
			// NEW LAMBA EXPRESSION
			avm_size_t newBoundVariableCount =
					aLambdaFun.getData().size() - applyCode->size() + 1;

			AvmLambda * substLambda = new AvmLambda(aLambdaFun.getContainer(),
					newBoundVariableCount, aLambdaFun.getNature());

			ENV.outVAL.renew( substLambda );

			// INITIALIZE LOCAL VARIABLE TABLE
			avm_size_t offset = 0;
			for( ; itArg != endArg ; ++itArg , ++offset )
			{
				if( not ENV.seval(*itArg ) )
				{
					return( false );
				}
				aLocalRuntime.setData(offset, ENV.outVAL);
			}

			// SET NEW BOUND VARIABLE
			TableOfInstanceOfData::const_raw_iterator itData =
					aLambdaFun.getData().begin();
			TableOfInstanceOfData::const_raw_iterator endData =
					aLambdaFun.getData().end();
			avm_offset_t newOffset = 0;
			for( ; itData != endData ; ++itData , ++offset , ++newOffset )
			{
				Symbol lambdaVar( new InstanceOfData(
						IPointerDataNature::POINTER_STANDARD_NATURE,
						substLambda, (itData)->getAstElement(),
						TypeManager::UNIVERSAL, newOffset) );

				substLambda->setData(newOffset, lambdaVar);

				aLocalRuntime.setData(offset, lambdaVar);
			}

			// LOAD LOCAL VARIABLE TABLE
			ENV.inED->getLocalRuntimes()->push( aLocalRuntime );

			// REDUCTION
			if( (rtCode = ENV.seval(aLambdaFun.getExpression())) )
			{
				substLambda->setExpression( ENV.outVAL );
			}
		}

		// UNLOAD & DESTROY LOCAL VARIABLE TABLE
		if( ENV.inED->hasLocalRuntime() )
		{
			ENV.inED->getLocalRuntimes()->pop();

			if( not ENV.inED->hasLocalRuntime() )
			{
				ENV.inED->destroyLocalRuntimeStack();
			}
		}
	}

	else
	{
		BFCode theSubstCode( applyCode->getOperator() , theFunction );

		for ( ++itArg ; itArg != endArg ; ++itArg )
		{
			if( not ENV.seval(*itArg ) )
			{
				return( false );
			}
			theSubstCode->append( ENV.outVAL );
		}

		ENV.outVAL = theSubstCode;
	}

	return( rtCode );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// execution of a INVOKE LAMBDA LET program
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_InvokeLambdaLet::seval(EvaluationEnvironment & ENV)
{
	return( false );
}



}

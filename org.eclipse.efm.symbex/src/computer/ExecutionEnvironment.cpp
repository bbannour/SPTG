/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 févr. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExecutionEnvironment.h"

#include <computer/EvaluationEnvironment.h>

#include <computer/instruction/InstructionEnvironment.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>


#define EXEC_ENV_INITIAL_COUNT     16

#define EXEC_ENV_DEFAULT_CAPACITY  16

#define EXEC_ENV_INCR_CAPACITY      8



namespace sep
{


///////////////////////////////////////////////////////////////////////////
// CACHE MANAGER
///////////////////////////////////////////////////////////////////////////

List< ExecutionEnvironment::_EXEC_ENV_ * >
ExecutionEnvironment::EXEC_ENV_CACHE;


void ExecutionEnvironment::initENVS()
{
	for( avm_size_t i = 0 ; i < EXEC_ENV_INITIAL_COUNT ; ++i )
	{
		EXEC_ENV_CACHE.append( new _EXEC_ENV_() );
	}
}

void ExecutionEnvironment::finalizeENVS()
{
	while( EXEC_ENV_CACHE.nonempty() )
	{
		delete( EXEC_ENV_CACHE.pop_last() );
	}
}



ExecutionEnvironment::_EXEC_ENV_ * ExecutionEnvironment::newENV()
{
	ExecutionEnvironment::_EXEC_ENV_ * exec_env = NULL;

	if( EXEC_ENV_CACHE.nonempty() )
	{
		EXEC_ENV_CACHE.pop_last_to( exec_env );
	}
	else
	{
		exec_env = new _EXEC_ENV_();

		AVM_OS_ASSERT_OUT_OF_MEMORY_EXIT( exec_env )
				<< "BaseEnvironment::newENV !!!"
				<< SEND_EXIT;
	}

	return( exec_env );
}


void ExecutionEnvironment::freeENV(_EXEC_ENV_ * & exec_env)
{
	exec_env->PRIMITIVE_PROCESSOR = NULL;

	exec_env->inEC = NULL;
	exec_env->inFORM.destroy();
	exec_env->inCODE.destroy();
	exec_env->inED.destroy();

	InstructionEnvironment::freeARGS( exec_env->arg );

	exec_env->outEDS.clear();

	exec_env->syncEDS.clear();
	exec_env->irqEDS.clear();
	exec_env->exitEDS.clear();
	exec_env->failureEDS.clear();

	EXEC_ENV_CACHE.append( exec_env );
}


////////////////////////////////////////////////////////////////////////////////
///// the RUN statement
////////////////////////////////////////////////////////////////////////////////


bool ExecutionEnvironment::run(
		ListOfAPExecutionData & inEDS, const BFCode & aCode)
{
	ListOfAPExecutionData::iterator itED = inEDS.begin();
	ListOfAPExecutionData::iterator endED = inEDS.end();
	for( ; itED != endED ; ++itED )
	{
		inED = (*itED);
		inFORM = inCODE = aCode;
		if( not PRIMITIVE_PROCESSOR.run(inCODE->getOpOffset(), *this) )
		{
			return( false );
		}
	}
	return( true );
}


bool ExecutionEnvironment::runFromOutputs(const BFCode & aCode)
{
	inFORM = inCODE = aCode;

	if( outEDS.singleton() )
	{
		outEDS.pop_first_to( inED );

		return( PRIMITIVE_PROCESSOR.run(inCODE->getOpOffset(), *this) );
	}
	else
	{
		ListOfAPExecutionData inEDS;
		inEDS.splice( outEDS );

		ListOfAPExecutionData::iterator itED = inEDS.begin();
		ListOfAPExecutionData::iterator endED = inEDS.end();
		for( ; itED != endED ; ++itED )
		{
			inED = (*itED);
			inFORM = inCODE = aCode;
			if( not PRIMITIVE_PROCESSOR.run(inCODE->getOpOffset(), *this) )
			{
				return( false );
			}
		}
		return( true );
	}
}


bool ExecutionEnvironment::runFromOutputs(Operator * op, const BFCode & aCode)
{
	inFORM = inCODE = aCode;

	if( outEDS.singleton() )
	{
		outEDS.pop_first_to( inED );

		return( PRIMITIVE_PROCESSOR.run(op->getOffset(), *this) );
	}
	else
	{
		ListOfAPExecutionData inEDS;
		inEDS.splice( outEDS );

		ListOfAPExecutionData::iterator itED = inEDS.begin();
		ListOfAPExecutionData::iterator endED = inEDS.end();
		for( ; itED != endED ; ++itED )
		{
			inED = (*itED);
			inFORM = inCODE = aCode;
			if( not PRIMITIVE_PROCESSOR.run(inCODE->getOpOffset(), *this) )
			{
				return( false );
			}
		}
		return( true );
	}
}


////////////////////////////////////////////////////////////////////////////////
///// the RESUME statement
////////////////////////////////////////////////////////////////////////////////

bool ExecutionEnvironment::resume(
		ExecutionEnvironment & ENV, APExecutionData & anED)
{
	inEC = ENV.inEC;

	inED = anED;

	inED.makeWritable();

	inED->mSTATEMENT_QUEUE.popTo( saveEXEC_LOCATION );
	inEXEC_LOCATION = saveEXEC_LOCATION.to_ptr< ExecutionLocation >();

	inED->mRID = inEXEC_LOCATION->mRID;

	inFORM = inCODE = inEXEC_LOCATION->mCODE;

	return PRIMITIVE_PROCESSOR.resume(*this);
}


////////////////////////////////////////////////////////////////////////////////
///// the OUTPUT management
////////////////////////////////////////////////////////////////////////////////

void ExecutionEnvironment::appendOutput(EvaluationEnvironment & ENV)
{
	outEDS.append( ENV.outED );

	spliceFailure( ENV );
}

bool ExecutionEnvironment::extractOtherOutputED(
		const APExecutionData & anED, ListOfAPExecutionData & listEDS)
{
	avm_uint8_t flags = 0;

	while( outEDS.nonempty() )
	{
		if( outEDS.first()->isTNEQ( anED ) )
		{
			flags = flags | 0x01;
			listEDS.append( outEDS.pop_first() );
		}
		else
		{
			flags = flags | 0x02;
			outEDS.pop_first();
		}
	}

	return( flags == 0x02 );
}

/**
 * appendOutput
 * w.r.t. AVM_EXEC_ENDING_STATUS
 */
void ExecutionEnvironment::appendOutput_wrtAEES(APExecutionData & anED)
{
	// Verification of EXECUTION ENDING STATUS
	switch( anED->getAEES() )
	{
		case AEES_STMNT_NOTHING:
		case AEES_STMNT_BREAK:
		case AEES_STMNT_CONTINUE:
		case AEES_STMNT_RETURN:
		{
			anED.mwsetAEES(AEES_OK);

			outEDS.append( anED );

			break;
		}

		case AEES_OK:
		case AEES_STEP_RESUME:
		case AEES_STEP_MARK:
		{
			outEDS.append( anED );

			break;
		}

		case AEES_STMNT_EXIT:
		case AEES_STMNT_EXIT_ALL:
		case AEES_STMNT_FATAL_ERROR:
		case AEES_SYMBOLIC_EXECUTION_LIMITATION:
		{
			exitEDS.append( anED );

			break;
		}

		case AEES_FAILED:
		{
			failureEDS.append( anED );

			AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected ENDIND EXECUTION STATUS :> "
				<< RuntimeDef::strAEES( anED->mAEES ) << " !!!"
				<< SEND_EXIT;

			break;
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected ENDIND EXECUTION STATUS :> "
				<< RuntimeDef::strAEES( anED->mAEES ) << " !!!"
				<< SEND_EXIT;

			break;
		}
	}
}


/**
 * appendOutput
 * mwset PROCESS_EVAL_STATE
 * mwset AVM_EXEC_ENDING_STATUS
 */

bool ExecutionEnvironment::mwsetPES_mwsetAEES(
		APExecutionData & anED, const RuntimeID & aRID,
		PROCESS_EVAL_STATE aPES)
{
	anED.mwsetRuntimeFormState(aRID, aPES);

	anED->setAEES( RuntimeDef::PES_to_AEES(aPES, anED->getAEES()) );

	return( true );
}

bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES(
		APExecutionData & anED, const RuntimeID & aRID,
		PROCESS_EVAL_STATE aPES)
{
	if( mwsetPES_mwsetAEES(anED, aRID, aPES) )
	{
		outEDS.append( anED );

		return( true );
	}

	return( false );
}

bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES(
		ExecutionEnvironment & ENV, const RuntimeID & aRID,
		PROCESS_EVAL_STATE aPES)
{
	ListOfAPExecutionData::iterator itED = ENV.outEDS.begin();
	ListOfAPExecutionData::iterator endED = ENV.outEDS.end();
	for( ; itED != endED ; ++itED )
	{
		appendOutput_mwsetPES_mwsetAEES((*itED), aRID, aPES);
	}

	return( true );
}



bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES(
		APExecutionData & anED, const RuntimeID & aRID,
		PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES)
{
	if( anED->getRuntimeFormState(aRID) == oldPES )
	{
		anED.mwsetRuntimeFormState(aRID, aPES);

		anED->setAEES( RuntimeDef::PES_to_AEES(aPES, anED->getAEES()) );
	}

	outEDS.append( anED );

	return( true );
}

bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES(
		ExecutionEnvironment & ENV, const RuntimeID & aRID,
		PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES)
{
	ListOfAPExecutionData::iterator itED = ENV.outEDS.begin();
	ListOfAPExecutionData::iterator endED = ENV.outEDS.end();
	for( ; itED != endED ; ++itED )
	{
		appendOutput_mwsetPES_mwsetAEES( (*itED), aRID, oldPES, aPES );
	}

	return( true );
}



bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES_mwsetRID(
		APExecutionData & anED,
		const RuntimeID & currentRID, const RuntimeID & nextRID,
		PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES)
{
	if( anED->getRuntimeFormState(currentRID) == oldPES )
	{
		anED.mwsetRuntimeFormState(currentRID, aPES);

		anED->setAEES( RuntimeDef::PES_to_AEES(aPES, anED->getAEES()) );
	}

	anED->mRID = nextRID;

	outEDS.append( anED );

	return( true );
}

bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES_mwsetRID(
		ExecutionEnvironment & ENV,
		const RuntimeID & currentRID, const RuntimeID & nextRID,
		PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES)
{
	ListOfAPExecutionData::iterator itED = ENV.outEDS.begin();
	ListOfAPExecutionData::iterator endED = ENV.outEDS.end();
	for( ; itED != endED ; ++itED )
	{
		appendOutput_mwsetPES_mwsetAEES_mwsetRID(
				(*itED), currentRID, nextRID, oldPES, aPES );
	}

	return( true );
}




/**
 * Serialization
 */
void ExecutionEnvironment::toStream(OutStream & os) const
{
	os << TAB << "environment {" << EOL;

	inEC->traceDefault(os);

	//inEC->writeTraceAfterExec(os, TAB2, CHAR, EOL);

	os << TAB << "outEDS:>  count : " << outEDS.size() << std::endl;
	ListOfAPExecutionData::const_iterator itED = outEDS.begin();
	ListOfAPExecutionData::const_iterator endED = outEDS.end();
	for( ; itED != endED ; ++itED )
	{
		os << TAB2 << "==>E[?] " << (*itED)->strStateConf()
				<< " " << (*itED)->getRunnableElementTrace().str() << EOL;
	}
	os << std::flush;

	os << TAB << "syncEDS:> count : " << syncEDS.size() << std::endl;
	itED = syncEDS.begin();
	endED = syncEDS.end();
	for( ; itED != endED ; ++itED )
	{
		os << TAB2 << "==>E[?] " << (*itED)->strStateConf()
				<< " " << (*itED)->getRunnableElementTrace().str() << EOL;
	}
	os << std::flush;

	os << TAB << "irqEDS:>  count : " << irqEDS.size() << std::endl;
	itED = irqEDS.begin();
	endED = irqEDS.end();
	for( ; itED != endED ; ++itED )
	{
		os << TAB2 << "==>E[?] " << (*itED)->strStateConf()
				<< " " << (*itED)->getRunnableElementTrace().str() << EOL;
	}
	os << std::flush;

	os << TAB << "failEDS:> count : " << failureEDS.size() << std::endl;
	itED = failureEDS.begin();
	endED = failureEDS.end();
	for( ; itED != endED ; ++itED )
	{
		os << TAB2 << "==>E[?] " << (*itED)->strStateConf()
				<< " " << (*itED)->getRunnableElementTrace().str() << EOL;
	}

	os << TAB << "}" << EOL_FLUSH;

}



}

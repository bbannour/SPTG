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
	for( std::size_t i = 0 ; i < EXEC_ENV_INITIAL_COUNT ; ++i )
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
	ExecutionEnvironment::_EXEC_ENV_ * exec_env = nullptr;

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
	exec_env->PRIMITIVE_PROCESSOR = nullptr;

	exec_env->inEC = nullptr;
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
		ListOfExecutionData & inEDS, const BFCode & aCode)
{
	for( const auto & itED : inEDS )
	{
		inED = itED;
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
		ListOfExecutionData inEDS;
		inEDS.splice( outEDS );

		for( const auto & itED : inEDS )
		{
			inED = itED;
			inFORM = inCODE = aCode;
			if( not PRIMITIVE_PROCESSOR.run(inCODE->getOpOffset(), *this) )
			{
				return( false );
			}
		}
		return( true );
	}
}


bool ExecutionEnvironment::runFromOutputs(const Operator * op, const BFCode & aCode)
{
	inFORM = inCODE = aCode;

	if( outEDS.singleton() )
	{
		outEDS.pop_first_to( inED );

		return( PRIMITIVE_PROCESSOR.run(op->getOffset(), *this) );
	}
	else
	{
		ListOfExecutionData inEDS;
		inEDS.splice( outEDS );

		for( const auto & itED : inEDS )
		{
			inED = itED;
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
		ExecutionEnvironment & ENV, ExecutionData & anED)
{
	inEC = ENV.inEC;

	inED = anED;

	inED.makeWritable();

	inED.popExecutionLocationTo( saveEXEC_LOCATION );
	inEXEC_LOCATION = saveEXEC_LOCATION.to_ptr< ExecutionLocation >();

	inED.setRID( inEXEC_LOCATION->mRID );

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
		const ExecutionData & anED, ListOfExecutionData & listEDS)
{
	std::uint8_t flags = 0;

	while( outEDS.nonempty() )
	{
		if( outEDS.first().isTNEQ( anED ) )
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
 * w.r.t. AVM_EXECUTION_ENDING_STATUS
 */
void ExecutionEnvironment::appendOutput_wrtAEES(ExecutionData & anED)
{
	// Verification of EXECUTION ENDING STATUS
	switch( anED.getAEES() )
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
				<< RuntimeDef::strAEES( anED.getAEES() ) << " !!!"
				<< SEND_EXIT;

			break;
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected ENDIND EXECUTION STATUS :> "
				<< RuntimeDef::strAEES( anED.getAEES() ) << " !!!"
				<< SEND_EXIT;

			break;
		}
	}
}


/**
 * appendOutput
 * mwset PROCESS_EVAL_STATE
 * mwset AVM_EXECUTION_ENDING_STATUS
 */
bool ExecutionEnvironment::mwsetPES(
		const RuntimeID & aRID, PROCESS_EVAL_STATE aPES)
{
	for( auto & itED : outEDS )
	{
		itED.mwsetRuntimeFormState(aRID, aPES);
	}

	for( auto & itED : exitEDS )
	{
		itED.mwsetRuntimeFormState(aRID, aPES);
	}

	return( true );
}


bool ExecutionEnvironment::mwsetPES_mwsetAEES(
		ExecutionData & anED, const RuntimeID & aRID,
		PROCESS_EVAL_STATE aPES)
{
	anED.mwsetRuntimeFormState(aRID, aPES);

	anED.setAEES( RuntimeDef::PES_to_AEES(aPES, anED.getAEES()) );

	return( true );
}

bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES(
		ExecutionData & anED, const RuntimeID & aRID,
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
	for( auto & itED : ENV.outEDS )
	{
		appendOutput_mwsetPES_mwsetAEES(itED, aRID, aPES);
	}

	for( auto & itED : ENV.exitEDS )
	{
		itED.mwsetRuntimeFormState(aRID, aPES);

//		exitEDS.append( itED );
	}

	return( true );
}



bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES(
		ExecutionData & anED, const RuntimeID & aRID,
		PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES)
{
	if( anED.getRuntimeFormState(aRID) == oldPES )
	{
		anED.mwsetRuntimeFormState(aRID, aPES);

		anED.setAEES( RuntimeDef::PES_to_AEES(aPES, anED.getAEES()) );
	}

	outEDS.append( anED );

	return( true );
}

bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES(
		ExecutionEnvironment & ENV, const RuntimeID & aRID,
		PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES)
{
	for( auto & itED : ENV.outEDS )
	{
		appendOutput_mwsetPES_mwsetAEES( itED, aRID, oldPES, aPES );
	}

	for( auto & itED : ENV.exitEDS )
	{
		if( itED.getRuntimeFormState(aRID) == oldPES )
		{
			itED.mwsetRuntimeFormState(aRID, aPES);
		}

//		exitEDS.append( itED );
	}

	return( true );
}



bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES_mwsetRID(
		ExecutionData & anED,
		const RuntimeID & currentRID, const RuntimeID & nextRID,
		PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES)
{
	if( anED.getRuntimeFormState(currentRID) == oldPES )
	{
		anED.mwsetRuntimeFormState(currentRID, aPES);

		anED.setAEES( RuntimeDef::PES_to_AEES(aPES, anED.getAEES()) );
	}

	anED.setRID( nextRID );

	outEDS.append( anED );

	return( true );
}

bool ExecutionEnvironment::appendOutput_mwsetPES_mwsetAEES_mwsetRID(
		ExecutionEnvironment & ENV,
		const RuntimeID & currentRID, const RuntimeID & nextRID,
		PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES)
{
	for( auto & itED : ENV.outEDS )
	{
		appendOutput_mwsetPES_mwsetAEES_mwsetRID(
				itED, currentRID, nextRID, oldPES, aPES );
	}

	for( auto & itED : ENV.exitEDS )
	{
		if( itED.getRuntimeFormState(currentRID) == oldPES )
		{
			itED.mwsetRuntimeFormState(currentRID, aPES);
		}

		itED.setRID( nextRID );

//		exitEDS.append( itED );
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
	for( const auto & itED : outEDS )
	{
		os << TAB2 << "==>E[?] " << itED.strStateConf()
				<< " " << itED.getRunnableElementTrace().str() << EOL;
	}
	os << std::flush;

	os << TAB << "syncEDS:> count : " << syncEDS.size() << std::endl;
	for( const auto & itED : syncEDS )
	{
		os << TAB2 << "==>E[?] " << itED.strStateConf()
				<< " " << itED.getRunnableElementTrace().str() << EOL;
	}
	os << std::flush;

	os << TAB << "irqEDS:>  count : " << irqEDS.size() << std::endl;
	for( const auto & itED : irqEDS )
	{
		os << TAB2 << "==>E[?] " << itED.strStateConf()
				<< " " << itED.getRunnableElementTrace().str() << EOL;
	}
	os << std::flush;

	os << TAB << "failEDS:> count : " << failureEDS.size() << std::endl;
	for( const auto & itED : failureEDS )
	{
		os << TAB2 << "==>E[?] " << itED.strStateConf()
				<< " " << itED.getRunnableElementTrace().str() << EOL;
	}

	os << TAB << "}" << EOL_FLUSH;

}



}

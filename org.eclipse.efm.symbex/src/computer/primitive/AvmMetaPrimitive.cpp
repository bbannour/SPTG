/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 14 mars 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmMetaPrimitive.h"

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionDataFactory.h>
#include <computer/ExecutionEnvironment.h>

#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionConfiguration.h>


namespace sep
{


/**
 ***************************************************************************
 * execution of an INFORMAL program
 ***************************************************************************
 */
bool AvmPrimitive_Informal::seval(EvaluationEnvironment & ENV)
{
	ExecutionDataFactory::appendIOElementTrace(ENV.outED,
			BF(new ExecutionConfiguration(ENV.outED.getRID(), ENV.inCODE)) );

	return( true );
}


bool AvmPrimitive_Informal::run(ExecutionEnvironment & ENV)
{
	ExecutionData outED = ENV.inED;

	ExecutionDataFactory::appendIOElementTrace(outED,
			BF(new ExecutionConfiguration(outED.getRID(), ENV.inCODE)) );

	ENV.outEDS.append(outED);

	return( true );
}


/**
 ***************************************************************************
 * execution of an TRACE program
 ***************************************************************************
 */
bool AvmPrimitive_Trace::seval(EvaluationEnvironment & ENV)
{
	BFCode aTrace(OperatorManager::OPERATOR_TRACE);

	for( ENV.mARG->begin() ; ENV.mARG->hasNext() ; ENV.mARG->next() )
	{
		aTrace->append( ENV.mARG->current() );
	}

	ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
			BF(new ExecutionConfiguration(ENV.mARG->outED.getRID(), aTrace)) );

	return( true );
}


bool AvmPrimitive_Trace::run(ExecutionEnvironment & ENV)
{
	BFCode aTrace(OperatorManager::OPERATOR_TRACE);

	for( ENV.mARG->begin() ; ENV.mARG->hasNext() ; ENV.mARG->next() )
	{
		aTrace->append( ENV.mARG->current() );
	}

	ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
			BF(new ExecutionConfiguration(ENV.mARG->outED.getRID(), aTrace)) );

	ENV.outEDS.append(ENV.mARG->outED);

	return( true );
}


/**
 ***************************************************************************
 * execution of an DEBUG program
 ***************************************************************************
 */
bool AvmPrimitive_Debug::seval(EvaluationEnvironment & ENV)
{
	BFCode aDebug(OperatorManager::OPERATOR_DEBUG);

	AVM_OS_INFO << std::endl << "@debug{" << std::endl;

	for( ENV.mARG->begin() ; ENV.mARG->hasNext() ; ENV.mARG->next() )
	{
		AVM_OS_INFO << TAB << ENV.mARG->current();

		aDebug->append( ENV.mARG->current() );
	}

	AVM_OS_INFO << "}" << std::endl;

	ENV.outVAL = aDebug;

	return( true );
}


bool AvmPrimitive_Debug::run(ExecutionEnvironment & ENV)
{
	AVM_OS_INFO << std::endl << "@debug{" << std::endl;

	for( ENV.mARG->begin() ; ENV.mARG->hasNext() ; ENV.mARG->next() )
	{
		AVM_OS_INFO << TAB << ENV.mARG->current();
	}

	AVM_OS_INFO << "}" << std::endl;

	ENV.outEDS.append(ENV.mARG->outED);

	return( true );
}


/**
 ***************************************************************************
 * execution of an COMMENT program
 ***************************************************************************
 */
bool AvmPrimitive_Comment::seval(EvaluationEnvironment & ENV)
{
	ENV.outVAL = ENV.inCODE;

	return( true );
}


bool AvmPrimitive_Comment::run(ExecutionEnvironment & ENV)
{
	ENV.outEDS.append( ENV.inED );

	return( true );
}



/**
 ***************************************************************************
 * execution of an QUOTE program
 ***************************************************************************
 */
bool AvmPrimitive_Quote::run(ExecutionEnvironment & ENV)
{
	ENV.outEDS.append( ENV.inED );

	return( true );
}


bool AvmPrimitive_Quote::seval(EvaluationEnvironment & ENV)
{
	ENV.outVAL = ENV.inCODE->first();

	return( true );
}


/**
 ***************************************************************************
 * execution of an META_EVAL program
 ***************************************************************************
 */
bool AvmPrimitive_MetaEval::run(ExecutionEnvironment & ENV)
{
	BF codeToEval = ENV.inCODE->first();

	switch( codeToEval.classKind() )
	{
		case FORM_INSTANCE_DATA_KIND:
		{
			codeToEval = ENV.getRvalue( codeToEval.to< InstanceOfData >() );

			break;
		}

		case FORM_AVMCODE_KIND:
		{
			break;
		}

		default:
		{
			AVM_OS_EXIT( FAILED )
					<< "AvmPrimitive_MetaEval::run:> Unexpected a form KIND< "
					<< codeToEval.classKindName() << " >\n" << codeToEval.toString()
					<< SEND_EXIT;

			return( false );
		}
	}


	EvaluationEnvironment eENV(ENV, codeToEval);
	if( eENV.decode_seval() )
	{
		ENV.outEDS.append(eENV.outED);

		return( true );
	}

	return( false );
}


bool AvmPrimitive_MetaEval::seval(EvaluationEnvironment & ENV)
{
	BF codeToEval = ENV.inCODE->first();

	switch( codeToEval.classKind() )
	{
		case FORM_INSTANCE_DATA_KIND:
		{
			codeToEval = ENV.getRvalue( codeToEval.to< InstanceOfData >() );

			return( ENV.seval(codeToEval) );
		}

		case FORM_AVMCODE_KIND:
		{
			ENV.setCode( codeToEval.bfCode() );

			return( sevalx2(ENV) );
		}

		default:
		{
			AVM_OS_EXIT( FAILED )
					<< "AvmPrimitive_MetaEval::run:> Unexpected a form KIND< "
					<< codeToEval.classKindName() << " >\n" << codeToEval.toString()
					<< SEND_EXIT;

			return( false );
		}
	}
}



/**
 ***************************************************************************
 * execution of an META_RUN program
 ***************************************************************************
 */
bool AvmPrimitive_MetaRun::run(ExecutionEnvironment & ENV)
{
	BF codeToRun = ENV.inCODE->first();

	switch( codeToRun.classKind() )
	{
		case FORM_INSTANCE_DATA_KIND:
		{
			codeToRun = ENV.getRvalue( codeToRun.to< InstanceOfData >() );

			break;
		}

		case FORM_AVMCODE_KIND:
		{
			break;
		}

		default:
		{
			AVM_OS_EXIT( FAILED )
					<< "AvmPrimitive_MetaEval::run:> Unexpected a form KIND< "
					<< codeToRun.classKindName() << " >\n" << codeToRun.toString()
					<< SEND_EXIT;

			return( false );
		}
	}

	if( codeToRun.is< AvmCode >() )
	{
		return( ENV.run(codeToRun) );
	}

	return( false );
}






} /* namespace sep */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmJumpPrimitive.h"

#include <computer/ExecutionDataFactory.h>

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionEnvironment.h>

#include <fml/expression/AvmCode.h>
#include <fml/builtin/String.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>


namespace sep
{


/**
 ***************************************************************************
 * execution of a BREAK program
 ***************************************************************************
 */
bool AvmPrimitive_Break::run(ExecutionEnvironment & ENV)
{
	ExecutionData outED = ENV.inED;

	ENV.appendIrq_mwsetAEES(outED, AEES_STMNT_BREAK);

	return( true );
}


/**
 ***************************************************************************
 * execution of a CONTINUE program
 ***************************************************************************
 */
bool AvmPrimitive_Continue::run(ExecutionEnvironment & ENV)
{
	ExecutionData outED = ENV.inED;

	ENV.appendIrq_mwsetAEES(outED, AEES_STMNT_CONTINUE);

	return( true );
}


/**
 ***************************************************************************
 * execution of a RETURN program
 ***************************************************************************
 */
bool AvmPrimitive_Return::run(ExecutionEnvironment & ENV)
{
	if( ENV.inCODE->hasOperand() )
	{
		ENV.mARG->outED.setValue( ENV.mARG->at(0) );

		ENV.appendIrq_mwsetAEES(ENV.mARG->outED, AEES_STMNT_RETURN);
	}
	else
	{
		ExecutionData outED = ENV.inED;

		ENV.appendIrq_mwsetAEES(outED, AEES_STMNT_RETURN);
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a EXIT program
 ***************************************************************************
 */
bool AvmPrimitive_Exit::run(ExecutionEnvironment & ENV)
{
	ExecutionData outED = ENV.inED;

	if( ENV.inCODE->noOperand() )
	{
		ENV.appendExit_mwsetAEES(outED, AEES_STMNT_EXIT_ALL);

		ExecutionDataFactory::appendIOElementTrace(outED,
				BF( new String( "@exit_all" )) );
	}
	else
	{
		if( ! outED.hasValue() )
		{
			outED.setValue( ENV.mARG->at(0) );
		}

		ExecutionDataFactory::appendIOElementTrace(outED,
				BF( new String( "@exit{ " + ENV.mARG->at(0).str() + " }" )) );

		ENV.appendExit_mwsetAEES(outED, AEES_STMNT_EXIT);
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a TRACE STEP program
 ***************************************************************************
 */
bool AvmPrimitive_StepMark::run(ExecutionEnvironment & ENV)
{
	ExecutionData outED = ENV.inED;

	if( ENV.inCODE->hasOperand() )
	{
		if( ENV.inCODE->first().isBuiltinString() )
		{
			ExecutionDataFactory::appendIOElementTrace(outED, ENV.inCODE->first());
		}
		else
		{
			ExecutionDataFactory::appendIOElementTrace(outED,
					BF( new String( ENV.inCODE->first().str() )) );
		}
	}

	ENV.appendSync_mwsetAEES(outED, AEES_STEP_MARK);

	return( true );
}



}

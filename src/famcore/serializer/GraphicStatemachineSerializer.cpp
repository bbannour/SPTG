/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include  <famcore/serializer/GraphicStatemachineSerializer.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/PropertyPart.h>
#include <fml/infrastructure/System.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/PropertyPart.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>
#include <sew/SymbexControllerUnitManager.h>


namespace sep
{


/*******************************************************************************
serializer += GraphicStatemachineSerializer <name-id> "<description>" {
	// ...

@property:

@trace:

@format:

@vfs:
	file = "<save-file-path>"
}
*******************************************************************************/

/*
prototype processor::StatemachineSerializer as GraphicStatemachineSerializer is
section PROPERTY
	@info#selection = 'ALL';    // ALL | MODIFIED
	@data#selection = 'ALL';	// ALL | MODIFIED
endsection PROPERTY

section FORMAT
	@line#wrap#width = 42;
	@line#wrap#separator = "\\l";
endsection FORMAT

section REPORT
	@uri = "stream:std:cout";
	@uri = "stream:std:cerr";

	@uri = "stream:avm:log";
	@uri = "stream:avm:trace";

	@uri = "folder:report";
	@uri = "file:report/brusselator.report";
	@uri = "filename:brusselator";

	@uri = "socket:is006163.intra.cea.fr:123456";

	@when = "init:after?10#step:otf:every?5#us:before?100#macro_step:exit";

	@protocol = 'STATIC';   	// STATIC | DYNAMIC | STREAM
endsection REPORT


section MACHINE
	@machine = true;
	@machine#instance = true;
	@machine#model = true;
	@machine#prototype = true;

	@procedure = true;
	@program = true;
	@routine = true;

	@statemachine = true;
endsection MACHINE

section STATEMACHINE
	@transition = true;

	@enable = true;
	@disable = true;
	@routine = true;
  endsection STATEMACHINE

section TRANSITION
	@priority = true;
endsection TRANSITION

section STATEMENT
	@assign = true;

	@com = true;

	@com#env = true;

	@input = true;
	@input#env = true;

	@output = true;
	@output#env = true;
endsection STATEMENT
endprototype
*/

////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool GraphicStatemachineSerializer::configureImpl()
{
	mConfigFlag = Serializer::configureImpl();

	const WObject * theSECTION = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));
	if( theSECTION != WObject::_NULL_ )
	{
		//!! NOTHING
	}

	theSECTION = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("machine", "MACHINE"));
	if( theSECTION != WObject::_NULL_ )
	{
		mMachineFlag = Query::getWPropertyBoolean(
				theSECTION, "machine", true);

		mMachineInstanceFlag = Query::getRegexWPropertyBoolean(
				theSECTION, CONS_WID2("machine", "instance"), true);
		mMachineModelFlag = Query::getRegexWPropertyBoolean(
				theSECTION, CONS_WID2("machine", "model"), true);
		mMachinePrototypeFlag = Query::getRegexWPropertyBoolean(
				theSECTION, CONS_WID2("machine", "prototype"), true);


		mProcedureFlag = Query::getWPropertyBoolean(
				theSECTION, "procedure", mProcedureFlag);

		mProgramFlag = Query::getWPropertyBoolean(
				theSECTION, "program", mProgramFlag);

		mRoutineFlag = Query::getWPropertyBoolean(
				theSECTION, "routine", mRoutineFlag);

		mStatemachineFlag = Query::getWPropertyBoolean(
				theSECTION, "statemachine", mStatemachineFlag);

		mTransitionFlag = Query::getWPropertyBoolean(
				theSECTION, "transition", mTransitionFlag);

		mStatementFlag = Query::getWPropertyBoolean(
				theSECTION, "statement", mStatementFlag);
	}

	theSECTION = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("statemachine", "STATEMACHINE"));
	if( theSECTION != WObject::_NULL_ )
	{
		mProcedureFlag = Query::getWPropertyBoolean(
				theSECTION, "procedure", mProcedureFlag);

		mProgramFlag = Query::getWPropertyBoolean(
				theSECTION, "program", mProgramFlag);

		mRoutineFlag = Query::getWPropertyBoolean(
				theSECTION, "routine", mRoutineFlag);

		mStatemachineFlag = Query::getWPropertyBoolean(
				theSECTION, "statemachine", mStatemachineFlag);

		mTransitionFlag = Query::getWPropertyBoolean(
				theSECTION, "transition", mTransitionFlag);

		mStatemachineDisableFlag = Query::getWPropertyBoolean(
				theSECTION, "disable", true);

		mStatemachineEnableFlag = Query::getWPropertyBoolean(
				theSECTION, "enable", true);

		mStatementFlag = Query::getWPropertyBoolean(
				theSECTION, "statement", mStatementFlag);
	}

	theSECTION = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("transition", "TRANSITION"));
	if( theSECTION != WObject::_NULL_ )
	{
		mTransitionFlag = Query::getWPropertyBoolean(
				theSECTION, "transition", mTransitionFlag);

		mTransitionPriorityFlag = Query::getWPropertyBoolean(
				theSECTION, "priority", true);

		mStatementFlag = Query::getWPropertyBoolean(
				theSECTION, "statement", mStatementFlag);
	}

	theSECTION = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("statement", "STATEMENT"));
	if( theSECTION != WObject::_NULL_ )
	{
		mStatementFlag = Query::getWPropertyBoolean(
				theSECTION, "statement", mStatementFlag);

		mStatementAssignFlag = Query::getWPropertyBoolean(
				theSECTION, "assign", mStatementFlag);

		mStatementComFlag = Query::getWPropertyBoolean(
				theSECTION, "com", mStatementFlag);
		mStatementComEnvFlag = Query::getRegexWPropertyBoolean(
				theSECTION, CONS_WID2("com", "env"), mStatementFlag);

		mStatementInputFlag = Query::getWPropertyBoolean(
				theSECTION, "input", mStatementFlag && mStatementComFlag);
		mStatementInputEnvFlag = Query::getRegexWPropertyBoolean(
				theSECTION, CONS_WID2("input", "env"),
				mStatementFlag && mStatementComEnvFlag);

		mStatementOuputFlag = Query::getWPropertyBoolean(
				theSECTION, "output", mStatementFlag && mStatementComFlag);
		mStatementOuputEnvFlag = Query::getRegexWPropertyBoolean(
				theSECTION, CONS_WID2("output", "env"),
				mStatementFlag && mStatementComEnvFlag);

		mStatementGuardFlag = Query::getWPropertyBoolean(
				theSECTION, "guard", mStatementFlag);
		mStatementTestFlag = Query::getWPropertyBoolean(
				theSECTION, "test", mStatementFlag);
	}

	return( mConfigFlag );
}


/**
 * REPORT TRACE
 */
void GraphicStatemachineSerializer::reportDefault(OutStream & out) const
{
	AVM_OS_VERBOSITY_MEDIUM( out )
			<< TAB << "GRAPHIC STATEMACHINE SERIALIZER< "
			<< getParameterWObject()->getFullyQualifiedNameID()
			<< " > DONE !!!"  << EOL_FLUSH;
}


/**
 * PRE-PROCESSING API
 */
bool GraphicStatemachineSerializer::preprocess()
{
	bool saveFlag = String::USE_BACKSLASH_QUOTE;
	String::USE_BACKSLASH_QUOTE = true;

	beginStream();
	while( hasStream() )
	{
		CommonGraphicStatemachineSerializer::format(
				currentStream(), getConfiguration().getSpecification());
	}

	String::USE_BACKSLASH_QUOTE = saveFlag;

	closeStream();

	return( true );
}


////////////////////////////////////////////////////////////////////////////
// DEFAULT FORMAT API
////////////////////////////////////////////////////////////////////////////

void GraphicStatemachineSerializer::sformat(
		SymbexControllerUnitManager & aManager,
		OutStream & out, const System & aSystem)
{
	AbstractProcessorUnit * existingSerializer =
			aManager.getControllerUnit(
					GraphicStatemachineSerializer::AUTO_REGISTER_TOOL);

	if( existingSerializer != nullptr )
	{
		GraphicStatemachineSerializer gvSerializer(
				aManager, existingSerializer->getParameterWObject());

		if( gvSerializer.configureImpl() )
		{
			gvSerializer.format(out, aSystem);

			return;
		}
	}
	else
	{
		GraphicStatemachineSerializer gvSerializer(aManager, WObject::_NULL_);

		if( gvSerializer.configureImpl() )
		{
			gvSerializer.format(out, aSystem);

			return;
		}
	}

	out << ERROR_MESSAGE << std::endl;
}



} /* namespace sep */

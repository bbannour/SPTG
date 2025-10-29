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

#include "GraphVizStatemachineSerializer.h"

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

std::string GraphVizStatemachineSerializer::ERROR_MESSAGE = R""""(
digraph fscn {

ERROR [
	label=" Unfound, in the current SymbexControllerUnitManager,
an existing GraphVizStatemachineSerializer
which configuration could be used
to configure the default GraphViz's serializer !
"
	shape=tripleoctagon
	color=red
	style=filled
]

}
)"""";

/*******************************************************************************
serializer += GraphVizStatemachineSerializer <name-id> "<description>" {
	// ...

@property:

@trace:

@format:

@vfs:
	file = "<save-file-path>"
}
*******************************************************************************/

/*
prototype processor::StatemachineSerializer as GraphVizStatemachineSerializer is
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

bool GraphVizStatemachineSerializer::configureImpl()
{
	mConfigFlag = Serializer::configureImpl();

	const WObject * theSECTION = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));
	if( theSECTION != WObject::_NULL_ )
	{

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
				theSECTION, "procedure", true);

		mProgramFlag = Query::getWPropertyBoolean(
				theSECTION, "program", true);

		mRoutineFlag = Query::getWPropertyBoolean(
				theSECTION, "routine", true);

		mStatemachineFlag = Query::getWPropertyBoolean(
				theSECTION, "statemachine", true);
	}

	theSECTION = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("statemachine", "STATEMACHINE"));
	if( theSECTION != WObject::_NULL_ )
	{
		mTransitionFlag = Query::getWPropertyBoolean(
				theSECTION, "transition", true);

		mStatemachineDisableFlag = Query::getWPropertyBoolean(
				theSECTION, "disable", true);
		mStatemachineEnableFlag = Query::getWPropertyBoolean(
				theSECTION, "enable", true);
	}

	theSECTION = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("transition", "TRANSITION"));
	if( theSECTION != WObject::_NULL_ )
	{
		mTransitionPriorityFlag = Query::getWPropertyBoolean(
				theSECTION, "priority", true);
	}

	theSECTION = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("statement", "STATEMENT"));
	if( theSECTION != WObject::_NULL_ )
	{
		mStatementAssignFlag = Query::getWPropertyBoolean(
				theSECTION, "assign", false);

		mStatementComFlag = Query::getWPropertyBoolean(
				theSECTION, "com", false);
		mStatementComEnvFlag = Query::getRegexWPropertyBoolean(
				theSECTION, CONS_WID2("com", "env"), false);

		mStatementInputFlag = Query::getWPropertyBoolean(
				theSECTION, "input", false);
		mStatementInputEnvFlag = Query::getRegexWPropertyBoolean(
				theSECTION, CONS_WID2("input", "env"), false);

		mStatementOuputFlag = Query::getWPropertyBoolean(
				theSECTION, "output", false);
		mStatementOuputEnvFlag = Query::getRegexWPropertyBoolean(
				theSECTION, CONS_WID2("output", "env"), false);

		mStatementGuardFlag = Query::getWPropertyBoolean(
				theSECTION, "guard", false);
		mStatementTestFlag = Query::getWPropertyBoolean(
				theSECTION, "test", false);
	}

	return( mConfigFlag );
}


/**
 * REPORT TRACE
 */
void GraphVizStatemachineSerializer::reportDefault(OutStream & out) const
{
	AVM_OS_VERBOSITY_MEDIUM( out )
			<< TAB << "GRAPHVIZ STATEMACHINE SERIALIZER< "
			<< getParameterWObject()->getFullyQualifiedNameID()
			<< " > DONE !!!"  << EOL_FLUSH;
}


/**
 * PRE-PROCESSING API
 */
bool GraphVizStatemachineSerializer::preprocess()
{
	bool saveFlag = String::USE_BACKSLASH_QUOTE;
	String::USE_BACKSLASH_QUOTE = true;

	beginStream();
	while( hasStream() )
	{
		dotFormat(currentStream(), getConfiguration().getSpecification());
	}

	String::USE_BACKSLASH_QUOTE = saveFlag;

	closeStream();

	return( true );
}


////////////////////////////////////////////////////////////////////////////
// DEFAULT FORMAT API
////////////////////////////////////////////////////////////////////////////

void GraphVizStatemachineSerializer::format(
		SymbexControllerUnitManager & aManager,
		OutStream & out, const System & aSystem)
{
	AbstractProcessorUnit * existingSerializer =
			aManager.getControllerUnit(
					GraphVizStatemachineSerializer::AUTO_REGISTER_TOOL);

	if( existingSerializer != nullptr )
	{
		GraphVizStatemachineSerializer gvSerializer(
				aManager, existingSerializer->getParameterWObject());

		if( gvSerializer.configureImpl() )
		{
			gvSerializer.dotFormat(out, aSystem);

			return;
		}
	}
	else
	{
		GraphVizStatemachineSerializer gvSerializer(aManager, WObject::_NULL_);

		if( gvSerializer.configureImpl() )
		{
			gvSerializer.dotFormat(out, aSystem);

			return;
		}
	}

	out << ERROR_MESSAGE << std::endl;
}


////////////////////////////////////////////////////////////////////////////////
// FORMAT API
////////////////////////////////////////////////////////////////////////////////

void GraphVizStatemachineSerializer::dotFormat(
		OutStream & out, const System & aSystem)
{
	out.setSymbexValueCSS(mMultiValueArrayCSS,
			mMultiValueParamsCSS, mMultiValueStructCSS);

	out << "digraph " << aSystem.getPortableNameID() << " {" << EOL

		<< TAB << "compound = true;" << EOL

		<< TAB << "fontsize = 12" << EOL_INCR_INDENT;

	dotFormatSystem(out, aSystem);

	out << DECR_INDENT_TAB << "}" << EOL2_FLUSH;

	out.restoreSymbexValueCSS();
}


void GraphVizStatemachineSerializer::dotFormatSystem(
		OutStream & out, const System & aSystem)
{
	out << TAB << "subgraph \"cluster_" << aSystem.getFullyQualifiedNameID()
		<< "\" {" << EOL

		<< TAB2 << "label = \"SYSTEM " << aSystem.getFullyQualifiedNameID()
		<< "\"" << EOL2

		<< INCR_INDENT;

	if( aSystem.hasProcedure() && mProcedureFlag )
	{
		CompositePart::const_procedure_iterator itMachine =
				aSystem.getCompositePart()->procedure_begin();
		CompositePart::const_procedure_iterator endMachine =
				aSystem.getCompositePart()->procedure_end();
		dotFormatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			out << EOL;
			dotFormatMachine(out, itMachine);
		}
	}
	if( aSystem.hasMachine() )
	{
		CompositePart::const_machine_iterator itMachine =
				aSystem.getCompositePart()->machine_begin();
		CompositePart::const_machine_iterator endMachine =
				aSystem.getCompositePart()->machine_end();
		dotFormatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			out << EOL;
			dotFormatMachine(out, itMachine);
		}
	}

	out << DECR_INDENT

		<< TAB << "}" << EOL_FLUSH;
}


void GraphVizStatemachineSerializer::dotFormatMachine(
		OutStream & out, const Machine & aMachine)
{
	if( aMachine.getSpecifier().isMocCompositeStructure() )
	{
		if( aMachine.getSpecifier().isComponentProcedure()
			&& aMachine.getCompositePart()->getMachines().singleton()
			&& aMachine.getCompositePart()->getMachines().first().
				to< Machine >().getSpecifier().isDesignInstanceStatic()
			&& aMachine.getCompositePart()->getProcedures().empty() )
		{
			dotFormatStatemachineCall(out, aMachine);
		}
		else
		{
			dotFormatCompositeStructure(out, aMachine);
		}
	}

	else if( aMachine.getSpecifier().isMocStateTransitionStructure() )
	{
		dotFormatStateTransitionStructure(out, aMachine);
	}

	else if( aMachine.getSpecifier().isState() )
	{
		dotFormatMachineSimpleState(out, aMachine);
	}
	else if( aMachine.getSpecifier().isPseudostate() )
	{
		dotFormatMachinePseudoState(out, aMachine);
	}

	else if( aMachine.getSpecifier().isDesignInstanceStatic() )
	{
		if( mMachineInstanceFlag
			&& ( mProcedureFlag
				|| (not aMachine.getSpecifier().isComponentProcedure()) ) )
		{
			dotFormatMachineCall(out, aMachine);
		}
	}

	else //if( (not aMachine.getSpecifier().isComponentProcedure())
//			|| mProcedureFlag )
	{
		dotFormatMachineDefault(out, aMachine);
	}
}


void GraphVizStatemachineSerializer::dotFormatMachineModelInterface(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "\"" << aMachine.getFullyQualifiedNameID()
		<< "#parameters\"" << EOL

		<< TAB << "[" << EOL
		<< TAB2 << "label = \"|{Parameters: ";

	if( aMachine.hasVariableParameter() )
	{
		out << "Input";
		if( aMachine.hasVariableReturn() )
		{
			out << " / Output";
		}
	}
	else  if( aMachine.hasVariableReturn() )
	{
		out << "Output";
	}


	if( aMachine.hasParamReturn() )
	{
		std::string strValue;

		if( aMachine.hasVariableParameter() )
		{
			out << "|";

			TableOfVariable::const_raw_iterator itParam =
					aMachine.getVariableParameters().begin();
			TableOfVariable::const_raw_iterator endIt =
					aMachine.getVariableParameters().end();
			for( ; itParam != endIt ; ++itParam )
			{
				out << (itParam)->strT() << " " << (itParam)->getNameID();
				if( (itParam)->hasValue() )
				{
					strValue = (itParam)->prettyPrintableValue();

					StringTools::replaceAll(strValue, "\"", "\\\"");

					out << " := " << strValue;
				}
				out << "\\l\n";
			}

		}

		if( aMachine.hasVariableReturn() )
		{
			out << "|";

			TableOfVariable::const_raw_iterator itParam =
					aMachine.getVariableReturns().begin();
			TableOfVariable::const_raw_iterator endIt =
					aMachine.getVariableReturns().end();
			for( ; itParam != endIt ; ++itParam )
			{
				out << (itParam)->strT() << " " << (itParam)->getNameID();
				if( (itParam)->hasValue() )
				{
					strValue = (itParam)->prettyPrintableValue();

					StringTools::replaceAll(strValue, "\"", "\\\"");

					out << " =: " << strValue;
				}
				out << "\\l\n";
			}

		}
	}
	out << "}|\"" << EOL

		<< TAB2 << "shape=Mrecord, style=bold, color=blue" << EOL

		<< TAB << "];" << EOL2;

	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			out << EOL;
			dotFormatTransition( out, itTransition);
		}
	}
}


void GraphVizStatemachineSerializer::dotFormatMachineCall(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "\"" << aMachine.getFullyQualifiedNameID() << "\"" << EOL

		<< TAB << "[" << EOL
		<< TAB2 << "label = \"|{";

	if( aMachine.getSpecifier().isComponentProcedure() )
	{
		out << "caller: " << aMachine.getContainerMachine()->getNameID();
	}
	else
	{
		out << "model: " << aMachine.getModelMachine()->getNameID();
	}
	out << "|" << aMachine.getNameID();

	if( aMachine.hasParamReturn() )
	{
		std::string strValue;

		if( aMachine.hasVariableParameter() )
		{
			out << "|";

			TableOfVariable::const_raw_iterator itParam =
					aMachine.getVariableParameters().begin();
			TableOfVariable::const_raw_iterator endIt =
					aMachine.getVariableParameters().end();
			for( ; itParam != endIt ; ++itParam )
			{
				out << (itParam)->getNameID();
				if( (itParam)->hasValue() )
				{
					strValue = (itParam)->prettyPrintableValue();

					StringTools::replaceAll(strValue, "\"", "\\\"");

					out << " := " << strValue;
				}
				out << "\\l\n";
			}

		}

		if( aMachine.hasVariableReturn() )
		{
			out << "|";

			TableOfVariable::const_raw_iterator itParam =
					aMachine.getVariableReturns().begin();
			TableOfVariable::const_raw_iterator endIt =
					aMachine.getVariableReturns().end();
			for( ; itParam != endIt ; ++itParam )
			{
				out << (itParam)->getNameID();
				if( (itParam)->hasValue() )
				{
					strValue = (itParam)->prettyPrintableValue();

					StringTools::replaceAll(strValue, "\"", "\\\"");

					out << "=:" << strValue;
				}
				out << "\\l\n";
			}

		}
	}
	out << "}|\"" << EOL

		<< TAB2 << "shape=Mrecord, style=bold, color=orange" << EOL

		<< TAB << "];" << EOL;


	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			out << EOL;
			dotFormatTransition( out, itTransition);
		}
	}
}


void GraphVizStatemachineSerializer::dotFormatStatemachineCall(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "\"" << aMachine.getFullyQualifiedNameID() << "\"" << EOL

		<< TAB << "[" << EOL
		<< TAB2 << "label = \"|\n" //<< aMachine.getNameID() << "\n\n|\n"
			<< aMachine.getCompositePart()->
				getMachines().first().to< Machine >().getNameID()
			<< "\n\n|\"" << EOL

		<< TAB2 << "shape=Mrecord, style=bold, color=orange" << EOL

		<< TAB << "];" << EOL;


	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			out << EOL;
			dotFormatTransition( out, itTransition);
		}
	}
}


void GraphVizStatemachineSerializer::dotFormatCompositeStructure(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "subgraph \"cluster_" << aMachine.getFullyQualifiedNameID()
		<< "\" {" << EOL

		<< TAB2 << "label = \"" << aMachine.getNameID() << "\"" << EOL
		<< TAB2 << "style=bold" << ";" << EOL2

	// invisible target state
		<< TAB2 << "\"" << aMachine.getFullyQualifiedNameID() << "\"" << EOL
		<< TAB2 << "[" << EOL
		<< TAB3 << "label = \"" << aMachine.getNameID() << "\"" << EOL
		<< TAB3 << "shape=point, style=invis, color=white" << EOL
		<< TAB2 << "];" << EOL2

		<< INCR_INDENT;

	if( aMachine.hasParamReturn() )
	{
		dotFormatMachineModelInterface(out, aMachine);
	}

	if( aMachine.hasProcedure() && mProcedureFlag )
	{
		CompositePart::const_procedure_iterator itMachine =
				aMachine.getCompositePart()->procedure_begin();
		CompositePart::const_procedure_iterator endMachine =
				aMachine.getCompositePart()->procedure_end();
		dotFormatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			out << EOL;
			dotFormatMachine(out, itMachine);
		}
	}
	if( aMachine.hasMachine() )
	{
		CompositePart::const_machine_iterator itMachine =
				aMachine.getCompositePart()->machine_begin();
		CompositePart::const_machine_iterator endMachine =
				aMachine.getCompositePart()->machine_end();
		dotFormatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			out << EOL;
			dotFormatMachine(out, itMachine);
		}
	}

	out << DECR_INDENT

		<< TAB << "}" << EOL;

	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			out << EOL;
			dotFormatTransition( out, itTransition);
		}
	}
}


void GraphVizStatemachineSerializer::dotFormatStateTransitionStructure(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "subgraph \"cluster_"
			<< aMachine.getFullyQualifiedNameID() << "\" {" << EOL

		<< TAB2 << "label = \"" << aMachine.getNameID()

		<< "\"" << EOL_TAB2 << "style=dashed;" << EOL2

	// invisible target state for transitions
		<< TAB2 << "\"" << aMachine.getFullyQualifiedNameID() << "\"" << EOL
		<< TAB2 << "[" << EOL
		<< TAB3 << "label = \"" << aMachine.getNameID()

		<< "\"" << EOL
		<< TAB3 << "shape=point, style=invis, color=white" << EOL
		<< TAB2 << "];" << EOL2

		<< INCR_INDENT;

	if( aMachine.hasParamReturn() )
	{
		dotFormatMachineModelInterface(out, aMachine);
	}

	if( aMachine.hasProcedure() && mProcedureFlag )
	{
		CompositePart::const_procedure_iterator itMachine =
				aMachine.getCompositePart()->procedure_begin();
		CompositePart::const_procedure_iterator endMachine =
				aMachine.getCompositePart()->procedure_end();
		dotFormatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			out << EOL;
			dotFormatMachine(out, itMachine);
		}
	}
	if( aMachine.hasMachine() )
	{
		CompositePart::const_machine_iterator itMachine =
				aMachine.getCompositePart()->machine_begin();
		CompositePart::const_machine_iterator endMachine =
				aMachine.getCompositePart()->machine_end();
		dotFormatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			out << EOL;
			dotFormatMachine(out, itMachine);
		}
	}

	out << DECR_INDENT

		<< TAB << "}" << EOL;

	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			out << EOL;
			dotFormatTransition( out, itTransition);
		}
	}
}


void GraphVizStatemachineSerializer::dotFormatMachineDefault(
		OutStream & out, const Machine & aMachine)
{
	if( aMachine.hasMachine() || aMachine.hasParamReturn() )
	{
		dotFormatCompositeStructure(out, aMachine);
	}
	else
	{
		out << TAB << "\"" << aMachine.getFullyQualifiedNameID() << "\"" << EOL

			<< TAB << "[" << EOL
			<< TAB2 << "label = \"" << aMachine.getNameID() << "\"" << EOL

			<< TAB2 << "shape=box, style=bold, color=blue" << EOL

			<< TAB << "];" << EOL;

		if( aMachine.hasOutgoingTransition() )
		{
			BehavioralPart::transition_iterator itTransition =
					aMachine.getBehavior()->outgoing_transition_begin();
			BehavioralPart::transition_iterator endTransition =
					aMachine.getBehavior()->outgoing_transition_end();
			for( ; itTransition != endTransition ; ++itTransition )
			{
				out << EOL;
				dotFormatTransition( out, itTransition);
			}
		}
	}
}


void GraphVizStatemachineSerializer::dotFormatMachineSimpleState(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "\"" << aMachine.getFullyQualifiedNameID() << "\"" << EOL

		<< TAB << "[" << EOL
		<< TAB2 << "label = \"" << aMachine.getNameID() << "\"" << EOL

		<< TAB2;
	if( aMachine.getSpecifier().isStateStart() )
	{
		out << "shape=ellipse, style=\"bold,filled\", fillcolor=green";
	}
	else if( aMachine.getSpecifier().isStateFinal() )
	{
		out << "shape=octagon, style=\"bold,filled\", fillcolor=red";
	}
	else if( aMachine.getSpecifier().isStateSync() )
	{
		out << "shape=hexagon, style=\"bold,filled\", color=orange";
	}
	else
	{
		out << "shape=ellipse, style=\"bold,filled\", color=skyblue";
	}
	out << EOL

		<< TAB << "];" << EOL;


	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			out << EOL;
			dotFormatTransition( out, itTransition);
		}
	}
}


void GraphVizStatemachineSerializer::dotFormatMachinePseudoState(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "\"" << aMachine.getFullyQualifiedNameID() << "\"" << EOL

		<< TAB << "[" << EOL
		<< TAB2 << "label = \"" << aMachine.getNameID() << "\"" << EOL

		<< TAB2;
	if( aMachine.getSpecifier().isPseudostateInitial() )
	{
		out << "shape=oval, style=\"filled\", fillcolor=green";
	}
	else if( aMachine.getSpecifier().isPseudostateJunction() )
	{
		out << "shape=octagon, style=\"filled\", fillcolor=green";
	}
	else if( aMachine.getSpecifier().isPseudostateChoice() )
	{
		out << "shape=octagon, style=\"filled\", fillcolor=orange";
	}
	else if( aMachine.getSpecifier().isPseudostateTerminal() )
	{
		out << "shape=Msquare, style=\"filled\", fillcolor=red";
	}
	else if( aMachine.getSpecifier().isPseudostateReturn() )
	{
		out << "shape=invhouse, style=\"filled\", fillcolor=greenyellow";
	}
	else
	{
		out << "shape=ellipse, style=\"filled\", color=cyan";
	}
	out << EOL

		<< TAB << "];" << EOL;


	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			out << EOL;
			dotFormatTransition( out, itTransition);
		}
	}
}


void GraphVizStatemachineSerializer::dotFormatTransition(
		OutStream & out, const Transition & aTransition)
{
	// SOURCE -> TARGET
	std::string targetUfi = (aTransition.hasTarget() ?
			aTransition.getTarget().str() : "#Last#Active#State" );

	out << TAB << "\"" << aTransition.getSource().getFullyQualifiedNameID()
			<< "\" -> " << "\"" << targetUfi << "\" "
			<< "[ label = \"" << aTransition.getNameID() << "\"";

	if( aTransition.hasMocElse() )
	{
		out << ", color=orange";
	}

	out << " ];" << EOL_FLUSH;
}


} /* namespace sep */

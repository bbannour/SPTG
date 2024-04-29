/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 October 2018
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "CommonGraphicStatemachineSerializer.h"

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


std::string CommonGraphicStatemachineSerializer::FILE_HEADER =
	"@startuml\n"
	"\n"
//	"scale 600 width\n"

	"hide empty description\n\n"

	"skinparam backgroundColor White\n"
	"skinparam backgroundColor White\n"
	"skinparam noteBorderColor White\n"
	"skinparam shadowing false\n"
	"skinparam notefontsize 16\n"
	"skinparam notefontname Verdana\n"
	"'skinparam notefontname Consolas\n"
	"'skinparam noteShadowing false\n"
	"\n"
	"skinparam state {\n"
		"\tStartColor Green\n"
		"\tEndColor Red\n"
		"\n"
		"\t'Attribut pour les transitions\n"
		"\tArrowColor Black\n"
		"\tArrowColor<< Else >> Orange\n"
		"\n"
		"\t'Attribut par défaut pour les états\n"
		"\tBorderColor Gray\n"
		"\tBackgroundColor Wheat\n"
		"\n"
		"\t'Attribut pour les états composites\n"
		"\tBackgroundColor<< System       >> Turquoise\n"
		"\tBackgroundColor<< Statemachine >> DodgerBlue\n"
		"\tBackgroundColor<< Machine      >> SpringGreen\n"
		"\tBackgroundColor<< Instance     >> Orchid\n"
		"\tBackgroundColor<< Composite    >> SpringGreen\n"
		"\n"
		"\t'Attribut pour les états simples\n"
		"\tBackgroundColor<< Simple >> PaleTurquoise\n"
		"\tBackgroundColor<< Start  >> Green\n"
		"\tBackgroundColor<< Final  >> Red\n"
		"\tBackgroundColor<< Sync   >> Aqua\n"
		"\n"
		"\t'Attribut pour les pseudo-états\n"
		"\tBackgroundColor<< Pseudo   >> Lavender\n"

		"\tBackgroundColor<< Initial  >> GreenYellow\n"

		"\tBackgroundColor<< Junction >> GreenYellow\n"
		"\tBackgroundColor<< Choice   >> Orange\n"

		"\tBackgroundColor<< Fork     >> SpringGreen\n"
		"\tBackgroundColor<< Junction >> SpringGreen\n"

		"\tBackgroundColor<< DeepHistory    >> SpringGreen\n"
		"\tBackgroundColor<< ShallowHistory >> SpringGreen\n"

		"\tBackgroundColor<< Return   >>  OrangeRed\n"
		"\tBackgroundColor<< Terminal >> Red\n"
		"\n"
		"\tFontColor Black\n"
		"\tFontName Times\n"
		"\tFontSize 14\n"
	"}\n"



//	"'Déclaration de la liste des états\n"
//	"state \"Monitor\" as monitor <<Selector>>\n"
//	"state \"Sensor 1\" as sensor_1\n"
//	"state \"Sensor 2\" as sensor_2\n"
//	"state \"Sensor 3\" as sensor_3\n"
//	"state \"Fusion\" as fusion\n"
//	"state \"Display\" as display\n"
//
//	"'Définition de chacun des états\n"
//	"monitor: frequency : 3 Hz\n"
//	"monitor: selection set\n"
//	"monitor: \\tALL_SENSORS\n"
//	"monitor: \\tSENSOR_1_2\n"
//	"monitor: \\tSENSOR_3\n"
//	"monitor: \\tNO_SENSOR\n"
//
//	"sensor_1: frequency : 6 Hz\n"
//	"sensor_1: processing set\n"
//	"sensor_1: \\tALL_SENSORS\n"
//	"sensor_1: \\tSENSOR_1_2\n"
//
//	"sensor_2: frequency : 3 Hz\n"
//	"sensor_2: processing set\n"
//	"sensor_2: \\tALL_SENSORS\n"
//	"sensor_2: \\tSENSOR_1_2\n"
//
//	"sensor_3: frequency : 1 Hz\n"
//	"sensor_3: processing set\n"
//	"sensor_3: \\tALL_SENSORS\n"
//	"sensor_3: \\tSENSOR_3\n"
//	"sensor_3: phase : 4\n"
//
//	"state \"channel\" as chan_sensor3_fusion\n"
//
//	"fusion: frequency : 3 Hz\n"
//	"fusion: processing set\n"
//	"fusion: \\tALL_SENSORS\n"
//	"fusion: \\tSENSOR_1_2\n"
//	"fusion: \\tSENSOR_3\n"
//	"fusion: phase : 1\n"
//
//	"display: frequency : 3 Hz\n"
//	"display: phase : 1\n"
//
//
//	"'Définition du graphe d'états\n"
//
//	"[*] -down-> monitor\n"
//
//	"state \"channel\" as chan_monitor_sensor1 <<Channel>>\n"
//	"monitor --> chan_monitor_sensor1 : 1\n"
//	"chan_monitor_sensor1 --> sensor_1 : 1/2\n"
//
//	"state \"channel\" as chan_monitor_sensor2 <<Channel>>\n"
//	"monitor --> chan_monitor_sensor2 : 1\n"
//	"chan_monitor_sensor2 --> sensor_2 : 1\n"
//
//	"state \"channel\" as chan_monitor_sensor3 <<Channel>>\n"
//	"monitor --> chan_monitor_sensor3 : 1/3\n"
//	"chan_monitor_sensor3 --> sensor_3 : 1\n"
//
//	"state \"channel\" as chan_sensor1_fusion <<Channel>>\n"
//	"sensor_1 --> chan_sensor1_fusion : 1/2\n"
//	"chan_sensor1_fusion --> fusion : 1\n"
//
//	"state \"channel\" as chan_sensor2_fusion <<Channel>>\n"
//	"sensor_2 --> chan_sensor2_fusion : 1\n"
//	"chan_sensor2_fusion --> fusion : 1\n"
//
//	"state \"channel\" as chan_sensor3_fusion << Channel >>\n"
//	"chan_sensor3_fusion: init : 2/3  \n"
//	"chan_sensor3_fusion: mode : NORMAL  \n"
//	"sensor_3 --> chan_sensor3_fusion : 1\n"
//	"chan_sensor3_fusion --> fusion : 1/3\n"
//
//	"state \"channel\" as chan_fusion_display <<Channel>>\n"
//	"fusion --> chan_fusion_display : 1\n"
//	"chan_fusion_display --> display : 1\n"

	;


std::string CommonGraphicStatemachineSerializer::FILE_FOOTER =
	"@enduml"
	;

std::string CommonGraphicStatemachineSerializer::ERROR_MESSAGE =
	"digraph fscn {"
	"\n"
	"ERROR ["
	"\n"
		"\tlabel=\""
		"Unfound,\n"
			"in the current SymbexControllerUnitManager,\\n"
			"an existing GraphVizStatemachineSerializer\\n"
			"which configuration could be used\n"
			"to configure the default GraphViz's serializer!\""
	"\n"
		"\tshape=tripleoctagon\n"
		"\tcolor=red\n"
		"\tstyle=filled\n"
	"]\n"
	"}\n"
	;


////////////////////////////////////////////////////////////////////////////////
// FORMAT API
////////////////////////////////////////////////////////////////////////////////

void CommonGraphicStatemachineSerializer::format(
		OutStream & out, const System & aSystem)
{
	if( (pMultiValueArrayCSS != nullptr)
		|| (pMultiValueParamsCSS != nullptr)
		|| (pMultiValueStructCSS != nullptr) )
	{
		out.setSymbexValueCSS( *pMultiValueArrayCSS,
				*pMultiValueParamsCSS, *pMultiValueStructCSS);
	}

	out << FILE_HEADER << EOL;

	formatSystem(out, aSystem);

	out << DECR_INDENT_TAB << FILE_FOOTER << EOL2_FLUSH;

	out.restoreSymbexValueCSS();
}


void CommonGraphicStatemachineSerializer::formatSystem(
		OutStream & out, const System & aSystem)
{
	out << TAB << "state \"System " << aSystem.getUnrestrictedName()
		<< "\" as " << aSystem.getUniqNameID() << " << System >> {" << EOL
		<< INCR_INDENT;


	if( aSystem.hasProcedure() && mProcedureFlag )
	{
		CompositePart::const_procedure_iterator itMachine =
				aSystem.getCompositePart()->procedure_begin();
		CompositePart::const_procedure_iterator endMachine =
				aSystem.getCompositePart()->procedure_end();
		formatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			formatMachine(out << EOL, itMachine);
		}
	}

	if( aSystem.hasMachine() )
	{
		CompositePart::const_machine_iterator itMachine =
				aSystem.getCompositePart()->machine_begin();
		CompositePart::const_machine_iterator endMachine =
				aSystem.getCompositePart()->machine_end();
		formatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			out << TAB << "--" << EOL;
			formatMachine(out, itMachine);
		}
	}

	out << DECR_INDENT
		<< EOL_TAB << "}" << EOL;
}


void CommonGraphicStatemachineSerializer::formatMachine(
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
			formatStatemachineCall(out, aMachine);
		}
		else
		{
			formatCompositeStructure(out, aMachine);
		}
	}

	else if( aMachine.getSpecifier().isMocStateTransitionStructure() )
	{
		formatStateTransitionStructure(out, aMachine);
	}

	else if( aMachine.getSpecifier().isState() )
	{
		formatMachineSimpleState(out, aMachine);
	}
	else if( aMachine.getSpecifier().isPseudostate() )
	{
		formatMachinePseudoState(out, aMachine);
	}

	else if( aMachine.getSpecifier().isDesignInstanceStatic() )
	{
		if( mMachineInstanceFlag
			&& ( mProcedureFlag
				|| (not aMachine.getSpecifier().isComponentProcedure()) ) )
		{
			formatMachineCall(out, aMachine);
		}
	}

	else //if( (not aMachine.getSpecifier().isComponentProcedure())
//			|| mProcedureFlag )
	{
		formatMachineDefault(out, aMachine);
	}
}


void CommonGraphicStatemachineSerializer::formatMachineModelInterface(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << aMachine.getUniqNameID()
		<< " : Parameters ";

//	if( aMachine.hasVariableParameter() )
//	{
//		out << "Input";
//		if( aMachine.hasVariableReturn() )
//		{
//			out << " / Output";
//		}
//	}
//	else  if( aMachine.hasVariableReturn() )
//	{
//		out << "Output";
//	}


	if( aMachine.hasParamReturn() )
	{
		std::string strValue;

		if( aMachine.hasVariableParameter() )
		{
			TableOfVariable::const_raw_iterator itParam =
					aMachine.getVariableParameters().begin();
			TableOfVariable::const_raw_iterator endIt =
					aMachine.getVariableParameters().end();
			for( ; itParam != endIt ; ++itParam )
			{
				out << TAB << aMachine.getUniqNameID()
					<< " : \\t" << (itParam)->getModifier().strDirection()
					<< (itParam)->strT() << " " << (itParam)->getUnrestrictedName();
				if( (itParam)->hasValue() )
				{
					strValue = (itParam)->prettyPrintableValue();

					out << " := " << strValue;
				}
				out << EOL;
			}

		}

		if( aMachine.hasVariableReturn() )
		{
			TableOfVariable::const_raw_iterator itParam =
					aMachine.getVariableReturns().begin();
			TableOfVariable::const_raw_iterator endIt =
					aMachine.getVariableReturns().end();
			for( ; itParam != endIt ; ++itParam )
			{
				out << TAB << aMachine.getUniqNameID()
					<< " : \\t" << (itParam)->getModifier().strDirection()
					<< (itParam)->strT() << " " << (itParam)->getUnrestrictedName();
				if( (itParam)->hasValue() )
				{
					strValue = (itParam)->prettyPrintableValue();

					StringTools::replaceAll(strValue, "\"", "\\\"");

					out << " =: " << strValue;
				}
				out << EOL;
			}

		}
	}

	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			formatTransition(out << EOL, itTransition);
		}
	}
}


void CommonGraphicStatemachineSerializer::formatMachineCall(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "state \"" << aMachine.getUnrestrictedName()
		<< "\" as " << aMachine.getUniqNameID() << EOL;

	if( aMachine.getSpecifier().isComponentProcedure() )
	{
		out << TAB << aMachine.getUniqNameID()
			<< " : caller " << aMachine.getContainerMachine()->getUnrestrictedName();
	}
	else
	{
		out << TAB << aMachine.getUniqNameID()
			<< " : model " << aMachine.getModelMachine()->getUnrestrictedName();
	}

	if( aMachine.hasParamReturn() )
	{
		std::string strValue;

		out << TAB << aMachine.getUniqNameID()
			<< " : Parameters ";

		if( aMachine.hasVariableParameter() )
		{
			TableOfVariable::const_raw_iterator itParam =
					aMachine.getVariableParameters().begin();
			TableOfVariable::const_raw_iterator endIt =
					aMachine.getVariableParameters().end();
			for( ; itParam != endIt ; ++itParam )
			{
				out << TAB << aMachine.getUniqNameID()
					<< " : \\t" << (itParam)->getModifier().strDirection()
					<< (itParam)->strT() << " " << (itParam)->getUnrestrictedName();
				if( (itParam)->hasValue() )
				{
					strValue = (itParam)->prettyPrintableValue();

					out << " := " << strValue;
				}
				out << EOL;
			}

		}

		if( aMachine.hasVariableReturn() )
		{
			TableOfVariable::const_raw_iterator itParam =
					aMachine.getVariableReturns().begin();
			TableOfVariable::const_raw_iterator endIt =
					aMachine.getVariableReturns().end();
			for( ; itParam != endIt ; ++itParam )
			{
				out << TAB << aMachine.getUniqNameID()
					<< " : \\t" << (itParam)->getModifier().strDirection()
					<< (itParam)->strT() << " " << (itParam)->getUnrestrictedName();
				if( (itParam)->hasValue() )
				{
					strValue = (itParam)->prettyPrintableValue();

					out << "=:" << strValue;
				}
				out << EOL;
			}

		}
	}

	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			formatTransition(out << EOL, itTransition);
		}
	}
}


void CommonGraphicStatemachineSerializer::formatStatemachineCall(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "state \"" << aMachine.getCompositePart()->
			getMachines().first().to< Machine >().getUnrestrictedName()
		<< "\" as " << aMachine.getUniqNameID() << EOL;

	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			formatTransition(out << EOL, itTransition);
		}
	}
}


void CommonGraphicStatemachineSerializer::formatCompositeStructure(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "state \"" << aMachine.getUnrestrictedName()
		<< "\" as " << aMachine.getUniqNameID() << " << Composite >> {" << EOL
		<< INCR_INDENT;

	if( aMachine.hasParamReturn() )
	{
		formatMachineModelInterface(out, aMachine);
	}

	if( aMachine.hasProcedure() && mProcedureFlag )
	{
		CompositePart::const_procedure_iterator itMachine =
				aMachine.getCompositePart()->procedure_begin();
		CompositePart::const_procedure_iterator endMachine =
				aMachine.getCompositePart()->procedure_end();
		formatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			formatMachine(out << EOL, itMachine);
		}
	}
	if( aMachine.hasMachine() )
	{
		CompositePart::const_machine_iterator itMachine =
				aMachine.getCompositePart()->machine_begin();
		CompositePart::const_machine_iterator endMachine =
				aMachine.getCompositePart()->machine_end();
		formatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			formatMachine(out << EOL, itMachine);
		}
	}

	out << DECR_INDENT
		<< EOL_TAB << "}" << EOL;

	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			formatTransition( out << EOL, itTransition);
		}
	}
}


void CommonGraphicStatemachineSerializer::formatStateTransitionStructure(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "state \"" << aMachine.getUnrestrictedName()
		<< "\" as " << aMachine.getUniqNameID() << " << Statemachine >> {" << EOL
		<< INCR_INDENT;

	if( aMachine.hasParamReturn() )
	{
		formatMachineModelInterface(out, aMachine);
	}

	if( aMachine.hasProcedure() && mProcedureFlag )
	{
		CompositePart::const_procedure_iterator itMachine =
				aMachine.getCompositePart()->procedure_begin();
		CompositePart::const_procedure_iterator endMachine =
				aMachine.getCompositePart()->procedure_end();
		formatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			formatMachine(out << EOL, itMachine);
		}
	}
	if( aMachine.hasMachine() )
	{
		CompositePart::const_machine_iterator itMachine =
				aMachine.getCompositePart()->machine_begin();
		CompositePart::const_machine_iterator endMachine =
				aMachine.getCompositePart()->machine_end();
		formatMachine(out, itMachine);
		for( ++itMachine; itMachine != endMachine ; ++itMachine )
		{
			formatMachine(out << EOL, itMachine);
		}
	}

	out << DECR_INDENT
		<< EOL_TAB << "}" << EOL;

	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			formatTransition( out << EOL, itTransition);
		}
	}
}


void CommonGraphicStatemachineSerializer::formatMachineDefault(
		OutStream & out, const Machine & aMachine)
{
	if( aMachine.hasMachine() || aMachine.hasParamReturn() )
	{
		formatCompositeStructure(out, aMachine);
	}
	else
	{
		out << TAB << "state \"" << aMachine.getFullyQualifiedNameID()
			<< "\" as " << aMachine.getUniqNameID() << " << Machine >>  {" << EOL;

		if( aMachine.hasOutgoingTransition() )
		{
			BehavioralPart::transition_iterator itTransition =
					aMachine.getBehavior()->outgoing_transition_begin();
			BehavioralPart::transition_iterator endTransition =
					aMachine.getBehavior()->outgoing_transition_end();
			for( ; itTransition != endTransition ; ++itTransition )
			{
				formatTransition(out << EOL, itTransition);
			}
		}
	}
}


void CommonGraphicStatemachineSerializer::formatMachineSimpleState(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "state \"" << aMachine.getUnrestrictedName()
		<< "\" as " << aMachine.getUniqNameID() << " ";

	if( aMachine.getSpecifier().isStateStart() )
	{
		out << "<< Start >>";
	}
	else if( aMachine.getSpecifier().isStateFinal() )
	{
		out << "<< Final >>";
	}
	else if( aMachine.getSpecifier().isStateSync() )
	{
		out << "<< Sync >>";
	}
	else
	{
		out << "<< Simple >>";
	}
	out << EOL;

	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			formatTransition(out << EOL, itTransition);
		}
	}
}


void CommonGraphicStatemachineSerializer::formatMachinePseudoState(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "state \"" << aMachine.getUnrestrictedName()
		<< "\" as " << aMachine.getUniqNameID() << " ";

	if( aMachine.getSpecifier().isPseudostateInitial() )
	{
		out << "<< Initial >>";
	}
	else if( aMachine.getSpecifier().isPseudostateJunction() )
	{
		out << "<< Junction >>";
	}
	else if( aMachine.getSpecifier().isPseudostateChoice() )
	{
		out << "<< Choice >>";
	}
	else if( aMachine.getSpecifier().isPseudostateTerminal() )
	{
		out << "<< Terminal >>";
	}
	else if( aMachine.getSpecifier().isPseudostateReturn() )
	{
		out << "<< Return >>";
	}
	else
	{
		out << "<< Pseudo >>";
	}
	out << EOL;

	if( aMachine.hasOutgoingTransition() )
	{
		BehavioralPart::transition_iterator itTransition =
				aMachine.getBehavior()->outgoing_transition_begin();
		BehavioralPart::transition_iterator endTransition =
				aMachine.getBehavior()->outgoing_transition_end();
		for( ; itTransition != endTransition ; ++itTransition )
		{
			formatTransition(out << EOL, itTransition);
		}
	}
}


void CommonGraphicStatemachineSerializer::formatTransition(
		OutStream & out, const Transition & aTransition)
{
	// SOURCE -> TARGET
	std::string targetUfi = (aTransition.hasTarget() ?
			aTransition.getTarget().is< Machine >() ?
					aTransition.getTarget().to< Machine >().getUniqNameID()
					: aTransition.getTarget().str()
			: "_Last_Active_State" );

	out << TAB << aTransition.getSource().getUniqNameID()
		<< "--> " << targetUfi;
	if( mStatementFlag && aTransition.hasStatement() )
	{
		out << EOL_TAB << "note on link "
			<< (aTransition.isMocFinal() ? "#red" :
					(aTransition.isMocElse() ? "#orange" : "#white"))
			<< EOL_INCR_INDENT
			<< TAB << "**" << aTransition.getUnrestrictedName();
		if( aTransition.getStatement()->hasOperand() )
		{
			out << ":**";
			aTransition.getStatement()->toStreamRoutine( out );
		}
		else
		{
			out << "**" << EOL;
		}
		out << DECR_INDENT
			<< TAB << "end note";
	}
	else
	{
		out << " : " << aTransition.getUnrestrictedName() << EOL;
	}


	if( aTransition.hasMocElse() )
	{
//		out << ", color=orange";
	}

	out << EOL_FLUSH;
}

} /* namespace sep */



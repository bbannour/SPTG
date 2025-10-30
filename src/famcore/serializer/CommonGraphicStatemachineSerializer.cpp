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
#include "AvmCode2Puml.h"

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/PropertyPart.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/System.h>
#include <fml/infrastructure/Transition.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/PropertyPart.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>
#include <sew/SymbexControllerUnitManager.h>


namespace sep
{


std::string CommonGraphicStatemachineSerializer::FILE_HEADER = R""""(
@startuml

	' // scale 600 width
	
	' allow_mixing
	' !pragma teoz true
	
	skinparam componentstyle uml2
	
	hide empty description
	
	skinparam linetype polyline
	' skinparam linetype ortho
	' left to right direction
	
	!function $kw($key_word)
	' // !return "**<color blue>" + $key_word + "</color>**"
	!return "**" + $key_word + "**"
	!endfunction
	
	!function $kop($key_operator)
	' // !return "**<color blue>" + $key_operator + "</color>**"
	!return "**" + $key_operator + "**"
	!endfunction
	
	!function $ks($key_symbol)
	' // !return "**<color blue>" + $key_symbol + "</color>**"
	!return "**" + $key_symbol + "**"
	!endfunction
	
	!function $param($p)
	' // !return "**<color darkred>" + $p + "</color>**"
	!return "**" + $p + "**"
	!endfunction
	
	!$natural = "**<color darkred>&#9838;</color>**"
	
	!$tp_path = "#Green,thickness=2"
	
	<style>
		note {
			backgroundcolor white
			shadowing 0
			linecolor transparent
			FontSize 35
		}
	</style>
	
	skinparam backgroundColor White
	
	skinparam arrow {
		Thickness 3
	}
	
	skinparam RoundCorner 0
	
	skinparam state {
		StartColor Green
		EndColor Red
		'Attribut pour les transitions
		ArrowColor Black
		ArrowColor<< Else >> Orange
		'Attribut par défaut pour les états
		BorderColor Black
		BorderThickness 3
		BackgroundColor Wheat
		'Attribut pour les états composites
		BackgroundColor<< System            >> LightGrey
		BackgroundColor<< Statemachine      >> GenericDisplay
		BackgroundColor<< Machine           >> GenericDisplay
		BackgroundColor<< Instance          >> GenericDisplay
		BackgroundColor<< Composite         >> GenericDisplay
		'Attribut pour les états simples
		BackgroundColor<< simple_hierarchic >> PaleTurquoise
		BackgroundColor<< simple            >> #E6E6E6
		BackgroundColor<< start             >> #E6E6E6
		BackgroundColor<< final             >> #E6E6E6 //#E6F4EA
		BackgroundColor<< pass              >> GreenYellow
		BackgroundColor<< sync              >> Aqua
		'Attribut pour les pseudo-états
		BackgroundColor<< pseudostate       >> Lavender
		BackgroundColor<< initial           >> GreenYellow
		BackgroundColor<< junction          >> #FFF7CC
		BackgroundColor<< choice            >> Orange
		BackgroundColor<< fork              >> #FFF7CC
		BackgroundColor<< join              >> SpringGreen
		BackgroundColor<< dhistory          >> SpringGreen
		BackgroundColor<< shistory          >> SpringGreen
		BackgroundColor<< return            >> OrangeRed
		BackgroundColor<< terminal          >> #E6E6E6 // #F8E1E1
		FontColor Black
		FontName Times
		FontSize 35
	}
)"""";

/*
R""""(
@startuml

	' // scale 600 width

	hide empty description

	skinparam linetype polyline
	' skinparam linetype ortho
	' left to right direction

	skinparam backgroundColor White
	skinparam backgroundColor White
	skinparam noteBorderColor White
	skinparam shadowing false
	skinparam notefontsize 16
	skinparam notefontname Verdana
	'skinparam notefontname Consolas
	'skinparam noteShadowing false

	skinparam state {
		StartColor Green
		EndColor Red

		'Attribut pour les transitions
		ArrowColor Black
		ArrowColor<< Else >> Orange

		'Attribut par défaut pour les états
		BorderColor Gray
		BackgroundColor Wheat

		'Attribut pour les états composites
		BackgroundColor<< System       >> Turquoise
		BackgroundColor<< Statemachine >> DodgerBlue
		BackgroundColor<< Machine      >> SpringGreen
		BackgroundColor<< Instance     >> Orchid
		BackgroundColor<< Composite    >> SpringGreen

		'Attribut pour les états simples
		BackgroundColor<< Simple >> PaleTurquoise
		BackgroundColor<< Start  >> Green
		BackgroundColor<< Final  >> Red
		BackgroundColor<< Sync   >> Aqua

		'Attribut pour les pseudo-états
		BackgroundColor<< Pseudo   >> Lavender

		BackgroundColor<< Initial  >> GreenYellow

		BackgroundColor<< Junction >> GreenYellow
		BackgroundColor<< Choice   >> Orange

		BackgroundColor<< Fork     >> SpringGreen
		BackgroundColor<< Junction >> SpringGreen

		BackgroundColor<< DeepHistory    >> SpringGreen
		BackgroundColor<< ShallowHistory >> SpringGreen

		BackgroundColor<< Return   >>  OrangeRed
		BackgroundColor<< Terminal >> Red

		FontColor Black
		FontName Times
		FontSize 14
	}

)"""";*/

/*
R""""(
	'Déclaration de la liste des états
	state "Monitor" as monitor <<Selector>>
	state "Sensor 1" as sensor_1
	state "Sensor 2" as sensor_2
	state "Sensor 3" as sensor_3
	state "Fusion" as fusion
	state "Display" as display

	'Définition de chacun des états
	monitor: frequency : 3 Hz
	monitor: selection set
	monitor: \tALL_SENSORS
	monitor: \tSENSOR_1_2
	monitor: \tSENSOR_3
	monitor: \tNO_SENSOR

	sensor_1: frequency : 6 Hz
	sensor_1: processing set
	sensor_1: \tALL_SENSORS
	sensor_1: \tSENSOR_1_2

	sensor_2: frequency : 3 Hz
	sensor_2: processing set
	sensor_2: \tALL_SENSORS
	sensor_2: \tSENSOR_1_2

	sensor_3: frequency : 1 Hz
	sensor_3: processing set
	sensor_3: \tALL_SENSORS
	sensor_3: \tSENSOR_3
	sensor_3: phase : 4

	state "channel" as chan_sensor3_fusion

	fusion: frequency : 3 Hz
	fusion: processing set
	fusion: \tALL_SENSORS
	fusion: \tSENSOR_1_2
	fusion: \tSENSOR_3
	fusion: phase : 1

	display: frequency : 3 Hz
	display: phase : 1


	'Définition du graphe d'états

	[*] -down-> monitor

	state "channel" as chan_monitor_sensor1 <<Channel>>
	monitor --> chan_monitor_sensor1 : 1
	chan_monitor_sensor1 --> sensor_1 : 1/2

	state "channel" as chan_monitor_sensor2 <<Channel>>
	monitor --> chan_monitor_sensor2 : 1
	chan_monitor_sensor2 --> sensor_2 : 1

	state "channel" as chan_monitor_sensor3 <<Channel>>
	monitor --> chan_monitor_sensor3 : 1/3
	chan_monitor_sensor3 --> sensor_3 : 1

	state "channel" as chan_sensor1_fusion <<Channel>>
	sensor_1 --> chan_sensor1_fusion : 1/2
	chan_sensor1_fusion --> fusion : 1

	state "channel" as chan_sensor2_fusion <<Channel>>
	sensor_2 --> chan_sensor2_fusion : 1
	chan_sensor2_fusion --> fusion : 1

	state "channel" as chan_sensor3_fusion << Channel >>
	chan_sensor3_fusion: init : 2/3
	chan_sensor3_fusion: mode : NORMAL
	sensor_3 --> chan_sensor3_fusion : 1
	chan_sensor3_fusion --> fusion : 1/3

	state "channel" as chan_fusion_display <<Channel>>
	fusion --> chan_fusion_display : 1
	chan_fusion_display --> display : 1
)"""";
*/


std::string CommonGraphicStatemachineSerializer::FILE_FOOTER = R""""(
@enduml
)"""";

std::string CommonGraphicStatemachineSerializer::ERROR_MESSAGE = R""""(
@startuml

    ' state "ERROR" as ERROR #red

	' ERROR: **Unfound, in the current SymbexControllerUnitManager,**
    ' ERROR: **an existing GraphVizStatemachineSerializer which**
    ' ERROR: **configuration could be used to configure the  default GraphViz's serializer !**

    process ERROR #OrangeRed  [
        **ERROR !**

        **Unfound, in the current SymbexControllerUnitManager,**
        **an existing GraphVizStatemachineSerializer which**
        **configuration could be used to configure the  default GraphViz's serializer !**
    ]

@enduml
)"""";


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

	formatStateBehavior(out, aMachine);
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

	formatStateBehavior(out, aMachine);
}


void CommonGraphicStatemachineSerializer::formatStatemachineCall(
		OutStream & out, const Machine & aMachine)
{
	out << TAB << "state \"" << aMachine.getCompositePart()->
			getMachines().first().to< Machine >().getUnrestrictedName()
		<< "\" as " << aMachine.getUniqNameID() << EOL;

	formatStateBehavior(out, aMachine);
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

	formatStateBehavior(out, aMachine);
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

	formatStateBehavior(out, aMachine);
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

		formatStateBehavior(out, aMachine);
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

	formatStateBehavior(out, aMachine);
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
	else if( aMachine.getSpecifier().isPseudostateFork() )
	{
		out << "<< Fork >>";
	}
	else
	{
		out << "<< Pseudo >>";
	}
	out << EOL;

	formatStateBehavior(out, aMachine);
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
//			<< INCR_INDENT;
			<< EOL_INCR_INDENT
			<< TAB << "**" << aTransition.getUnrestrictedName();
		if( aTransition.getStatement()->hasOperand() )
		{
			out << "**";
			AvmCode2Puml::toStream(out, *(aTransition.getStatement()));
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

void CommonGraphicStatemachineSerializer::formatRoutine(
		OutStream & out, const Routine & aRoutine, const std::string & position)
{
	if( mStatementFlag && aRoutine.hasCode() )
	{
		const std::string & stateID = aRoutine.getContainerMachine()->getUniqNameID();
		out << EOL_TAB << "note " << position << " of " << stateID << " #white"
			<< EOL_INCR_INDENT
			<< TAB << "**" << aRoutine.getUnrestrictedName();
		if( aRoutine.getCode()->hasOperand() )
		{
			out << "**";
			AvmCode2Puml::toStream(out, *(aRoutine.getCode()));
		}
		else
		{
			out << "**" << EOL;
		}
		out << DECR_INDENT
			<< TAB << "end note";
	}


	out << EOL_FLUSH;
}


void CommonGraphicStatemachineSerializer::formatStateBehavior(
		OutStream & out, const Machine & aMachine)
{
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

	if( aMachine.hasBehavior() )
	{
		const auto behavior = aMachine.getBehavior();
		if( behavior->hasOnInit() )
		{
			formatRoutine(out << EOL, behavior->getOnInitRoutine(), "bottom");
		}
		if( behavior->hasOnEnable() )
		{
			formatRoutine(out << EOL, behavior->getOnEnableRoutine(), "left");
		}
		if( behavior->hasOnDisable() )
		{
			formatRoutine(out << EOL, behavior->getOnDisableRoutine(), "right");
		}
	}
}


} /* namespace sep */



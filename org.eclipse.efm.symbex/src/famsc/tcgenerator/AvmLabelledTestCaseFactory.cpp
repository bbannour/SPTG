/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmLabelledTestCaseFactory.h"
#include "AvmTestCaseUtils.h"

#include <collection/BFContainer.h>

#include <famcore/api/AbstractProcessorUnit.h>
#include <famsc/tcgenerator/AvmPathGuidedTestcaseGenerator.h>

#include <fml/builtin/Identifier.h>

#include <fml/common/ModifierElement.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/PropertyPart.h>
#include <fml/infrastructure/Transition.h>
#include <fml/infrastructure/System.h>

#include <fml/runtime/ExecutionContext.h>

#include <sew/Configuration.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
AvmLabelledTestCaseFactory::AvmLabelledTestCaseFactory(
		AvmPathGuidedTestcaseGenerator & aProcessor, const Symbol & aQuiescencePortTP)
: mProcessor(aProcessor),
mQuiescencePortTP( aQuiescencePortTP ),
testPurposeTrace( ),
sutSystem( mProcessor.getConfiguration().getSpecification() ),
tcSystem( "tcSystem", sutSystem.getSpecifier() ),
tcMachine( nullptr ),
tcQuiescencePort( )
//tcStateFAIL( nullptr ),
//tcStateINC( nullptr )
{
	//!! NOTHING
}


////////////////////////////////////////////////////////////////////////////////
// QUIESCENCE
////////////////////////////////////////////////////////////////////////////////

void AvmLabelledTestCaseFactory::buildTestCase()
{
	buildStructure(sutSystem, tcSystem);

	OutStream & out2File = mProcessor.getStream( "file#ltc" );
	tcSystem.toStream(out2File);
}

void AvmLabelledTestCaseFactory::buildStructure(const System & sutSystem, System & tcSystem)
{
	// Main test case machine
	tcMachine = Machine::newStatemachine(& tcSystem, "tcMachine",
			Specifier::DESIGN_PROTOTYPE_STATIC_SPECIFIER);
	tcSystem.saveOwnedElement(tcMachine);


//	tcStateFAIL = Machine::newState(tcMachine, "FAIL", Specifier::STATE_FINAL_MOC);
//	tcMachine->saveOwnedElement(tcStateFAIL);
//
//	tcStateINC = Machine::newState(tcMachine, "INC", Specifier::STATE_FINAL_MOC);
//	tcMachine->saveOwnedElement(tcStateINC);


	PropertyPart & tcPropertyDecl = tcMachine->getPropertyPart();

	// Quiescence port
	Modifier outputModifier;
	outputModifier.setVisibilityPublic().setDirectionOutput();

	tcQuiescencePort = tcPropertyDecl.saveOwnedElement(
			new Port(tcPropertyDecl, "Quiescence",
					IComPoint::IO_PORT_NATURE, outputModifier) );

	const PropertyPart & sutPropertyDecl = sutSystem.getPropertyPart();

	addPorts(tcPropertyDecl, sutPropertyDecl);

	if( sutSystem.hasMachine() )
	{
		const CompositePart * sutCompositePart = sutSystem.getCompositePart();
		TableOfMachine::const_ref_iterator itm = sutCompositePart->getMachines().begin();
		TableOfMachine::const_ref_iterator endItm = sutCompositePart->getMachines().end();
		for( ; itm != endItm ; ++itm )
		{
			if( itm->hasPortSignal() )
			{
				addPorts(tcPropertyDecl, itm->getPropertyPart());
			}
		}
	}

	ExecutionContext & rootEC =
			mProcessor.getConfiguration().getFirstExecutionTrace();

	AvmTestCaseUtils::getTestPurposeTrace(rootEC, testPurposeTrace);

	buildStatemachine();
}

void AvmLabelledTestCaseFactory::addPorts(PropertyPart & tcPropertyPart,
		const PropertyPart & sutPropertyPart)
{
	Modifier inputModifier;
	inputModifier.setVisibilityPublic().setDirectionInput();

	Modifier outputModifier;
	outputModifier.setVisibilityPublic().setDirectionOutput();

	PropertyPart::TableOfPort::const_ref_iterator itp =
			sutPropertyPart.getPorts().begin();
	PropertyPart::TableOfPort::const_ref_iterator endItp =
			sutPropertyPart.getPorts().end();
	for( ; itp != endItp ; ++itp )
	{
		if( itp->getModifier().isDirectionInput() )
		{
			Port * tcOutputPort = new Port(tcPropertyPart,
					itp->getNameID(), IComPoint::IO_PORT_NATURE, outputModifier);
			tcPropertyPart.saveOwnedElement(tcOutputPort);
		}
		else if( itp->getModifier().isDirectionOutput() )
		{
			Port * tcInputPort = new Port(tcPropertyPart,
					itp->getNameID(), IComPoint::IO_PORT_NATURE, inputModifier);
			tcPropertyPart.saveOwnedElement(tcInputPort);
		}
	}
}


bool AvmLabelledTestCaseFactory::buildStatemachine()
{
	ExecutionContext::ListOfConstPtr traceECs(testPurposeTrace);
	const ExecutionContext * tcSourceEC = traceECs.pop_first();

	std::string stateID = (OSS() << "ec_" << tcSourceEC->getIdNumber()
			<< "_" << tcSourceEC->getExecutionData().strStateConf("%4%"));

	Machine * tcSourceState = Machine::newState(tcMachine,
			stateID, Specifier::STATE_START_MOC);
	tcMachine->saveOwnedElement(tcSourceState);

	for( const auto tcTargetEC : traceECs )
	{
//		AVM_OS_DEBUG << "Build state-transition for : " << tcSourceEC->str() << std::endl;

		Specifier stateSpec = Specifier::STATE_SIMPLE_MOC;

		tcSourceState = buildState(*tcSourceState, *tcSourceEC, *tcTargetEC);

		tcSourceEC = tcTargetEC;
	}
	tcSourceState->setNames( tcSourceState->getNameID() + "_PASS" );
	tcSourceState->updateFullyQualifiedNameID();
	tcSourceState->getwSpecifier().setStateMocFINAL();


	return true;
}


Machine * AvmLabelledTestCaseFactory::buildState(Machine & tcSourceState,
		const ExecutionContext & tcSourceEC, const ExecutionContext & tcTargetEC)
{
	std::string stateID = (OSS() << "ec_" << tcTargetEC.getIdNumber()
			<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));
	Machine * tcTargetState = Machine::newState(tcMachine,
			stateID, Specifier::STATE_SIMPLE_MOC);
	tcMachine->saveOwnedElement(tcTargetState);

	Transition * tpTransition = new Transition(tcSourceState,
			"t_" + stateID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	const BF & ioTrace = tcTargetEC.getIOElementTrace();
	const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
	const BF comPort = comTrace->first();
	const std::string & portID = comPort.to< InstanceOfPort >().getNameID();

	BF tcPort = tcMachine->getPort(portID);
//	BF tcPort = ExpressionConstructor::newIdentifier(portID);

	if( StatementTypeChecker::isOutput(comTrace) )
	{
		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_INPUT, tcPort));

		addFailQuiescenceTransition(tcSourceEC, tcSourceState);

		BFList specSutOutputPort; // Only local soec output not in TP
		sutUnexpectedOutput(tcSourceEC, comPort, specSutOutputPort);

		addIncInputTransition(tcSourceEC,
				tcSourceState, specSutOutputPort, true);

		specSutOutputPort.append(comPort); // All local spec output
		addFailInputTransition(tcSourceEC,
				tcSourceState, specSutOutputPort, true);
//		addIncInputTransition(tcSourceState, tcPort->to< Port >());
	}
	else
	{
		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_OUTPUT, tcPort));

		addFailInputTransition(tcSourceEC, tcSourceState, true);
	}

	return tcTargetState;
}


void AvmLabelledTestCaseFactory::sutUnexpectedOutput(const ExecutionContext & anEC,
		const BF tpOutputPort, BFList & specSutOutputPort)
{
	for( const auto & aChildEC : anEC.getChildContexts()  )
	{
		const BF & ioTrace = aChildEC->getIOElementTrace();
		const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
		const BF comPort = comTrace->first();
		if( StatementTypeChecker::isOutput(comTrace) && (tpOutputPort != comPort) )
		{
			specSutOutputPort.append(comPort);
		}
	}
}


void AvmLabelledTestCaseFactory::addIncInputTransition(const ExecutionContext & anEC,
		Machine & tcSourceState, const BFList & specSutOutputPort, bool groupIncInput)
{
	BFCodeList allIncInputStatement;

//	Machine * treeStateINC = nullptr;

	for( const auto & sutPort : specSutOutputPort )
	{
		const std::string & portID = sutPort.to< InstanceOfPort >().getNameID();
		BF tcPort = tcMachine->getPort(portID);

		if( not sutPort.isTEQ(mQuiescencePortTP.rawPort()) )
		{
			allIncInputStatement.append( StatementConstructor::newCode(
					OperatorManager::OPERATOR_INPUT, tcPort) );
		}
	}

	createIncInputTransition(anEC, tcSourceState, allIncInputStatement, groupIncInput);
}

void AvmLabelledTestCaseFactory::createIncInputTransition(
		const ExecutionContext & anEC, Machine & tcSourceState,
		const BFCodeList & allIncInputStatement, bool groupFailedInput)
{
	if( allIncInputStatement.nonempty() )
	{
		std::string stateID = (OSS() << "ec_" << anEC.getIdNumber() << "_INC");
		Machine * treeStateFAIL = Machine::newState(tcMachine,
				stateID, Specifier::PSEUDOSTATE_TERMINAL_MOC);
		tcMachine->saveOwnedElement(treeStateFAIL);

		if( groupFailedInput )
		{
			Transition * incTransition = new Transition(tcSourceState,
					"t_inc", Transition::MOC_SIMPLE_KIND);
			incTransition->setTarget( *treeStateFAIL );
			tcSourceState.saveOwnedElement( incTransition );

			incTransition->setStatement( allIncInputStatement.singleton() ?
					allIncInputStatement.first() :
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_SCHEDULE_OR_ELSE, allIncInputStatement) );
		}
		else
		{
			for( const auto & failedInputStatement : allIncInputStatement )
			{
				const std::string & trNameID =
						failedInputStatement->first().to< Port >().getNameID();
				Transition * incTransition = new Transition(tcSourceState,
						"t_inc_" + trNameID, Transition::MOC_SIMPLE_KIND);
				incTransition->setTarget( *treeStateFAIL );
				tcSourceState.saveOwnedElement( incTransition );

				incTransition->setStatement(failedInputStatement);
			}
		}
	}
}

void AvmLabelledTestCaseFactory::addFailQuiescenceTransition(
		const ExecutionContext & anEC, Machine & tcSourceState)
{
	std::string stateID = (OSS() << "ec_" << anEC.getIdNumber() << "_FAIL_dur");
	Machine * treeStateFAIL = Machine::newState(tcMachine,
			stateID, Specifier::STATE_FINAL_MOC);
	tcMachine->saveOwnedElement(treeStateFAIL);

	Transition * quiescTransition = new Transition(tcSourceState,
			"t_quiescence", Transition::MOC_SIMPLE_KIND);
	quiescTransition->setTarget( *treeStateFAIL );
	tcSourceState.saveOwnedElement( quiescTransition );

	quiescTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_OUTPUT, tcQuiescencePort));
}

void AvmLabelledTestCaseFactory::addFailInputTransition(
		const ExecutionContext & anEC, Machine & tcSourceState, bool groupFailedInput)
{
	BFCodeList allFailedInputStatement;

//	Machine * treeStateFAIL = nullptr;

	const PropertyPart & tcPropertyPart = tcMachine->getPropertyPart();
	PropertyPart::TableOfPort::const_ref_iterator itp = tcPropertyPart.getPorts().begin();
	PropertyPart::TableOfPort::const_ref_iterator endItp = tcPropertyPart.getPorts().end();
	for( ; itp != endItp ; ++itp )
	{
		if( itp->getModifier().isDirectionInput() )
		{
			allFailedInputStatement.append(
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_INPUT, *itp) );
		}
	}

	createFailInputTransition(anEC, tcSourceState,
			allFailedInputStatement, groupFailedInput);
}

void AvmLabelledTestCaseFactory::addFailInputTransition(const ExecutionContext & anEC,
		Machine & tcSourceState, const BFList & specSutOutputPort, bool groupFailedInput)
{
	BFCodeList allFailedInputStatement;

//	Machine * treeStateFAIL = nullptr;

	const PropertyPart & tcPropertyPart = tcMachine->getPropertyPart();
	PropertyPart::TableOfPort::const_ref_iterator itp = tcPropertyPart.getPorts().begin();
	PropertyPart::TableOfPort::const_ref_iterator endItp = tcPropertyPart.getPorts().end();
	for( ; itp != endItp ; ++itp )
	{
		if( itp->getModifier().isDirectionInput() )
		{
			bool isUnexpectedOutput = true;
			for( const auto & sutPort : specSutOutputPort )
			{
				const std::string & portID = sutPort.to< InstanceOfPort >().getNameID();
				if( portID == itp->getNameID() )
				{
					isUnexpectedOutput = false;
					break;
				}
			}

			if( isUnexpectedOutput )
			{
				allFailedInputStatement.append(
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_INPUT, *itp) );
			}
		}
	}

	createFailInputTransition(anEC, tcSourceState,
			allFailedInputStatement, groupFailedInput);
}

void AvmLabelledTestCaseFactory::createFailInputTransition(const ExecutionContext & anEC, Machine & tcSourceState,
		const BFCodeList & allFailedInputStatement, bool groupFailedInput)
{
	if( allFailedInputStatement.nonempty() )
	{
		std::string stateID = (OSS() << "ec_" << anEC.getIdNumber() << "_FAIL_out");
		Machine * treeStateFAIL = Machine::newState(tcMachine,
				stateID, Specifier::STATE_FINAL_MOC);
		tcMachine->saveOwnedElement(treeStateFAIL);

		if( groupFailedInput )
		{
			Transition * failTransition = new Transition(tcSourceState,
					"t_fail_out", Transition::MOC_SIMPLE_KIND);
			failTransition->setTarget( *treeStateFAIL );
			tcSourceState.saveOwnedElement( failTransition );

			failTransition->setStatement( allFailedInputStatement.singleton() ?
					allFailedInputStatement.first() :
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_SCHEDULE_OR_ELSE, allFailedInputStatement) );
		}
		else
		{
			for( const auto & failedInputStatement : allFailedInputStatement )
			{
				const std::string & trNameID =
						failedInputStatement->first().to< Port >().getNameID();
				Transition * failTransition = new Transition(tcSourceState,
						"t_fail_" + trNameID, Transition::MOC_SIMPLE_KIND);
				failTransition->setTarget( *treeStateFAIL );
				tcSourceState.saveOwnedElement( failTransition );

				failTransition->setStatement(failedInputStatement);
			}
		}
	}
}




} /* namespace sep */

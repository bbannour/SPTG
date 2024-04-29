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

#include "AvmTestCaseFactory.h"
#include "AvmTestCaseStatistics.h"
#include "AvmTestCaseUtils.h"

#include <collection/BFContainer.h>

#include <computer/BaseEnvironment.h>
#include <computer/EvaluationEnvironment.h>

#include <famcore/api/AbstractProcessorUnit.h>
#include <famsc/tcgenerator/AvmPathGuidedTestcaseGenerator.h>

#include <fml/builtin/Identifier.h>

#include <fml/common/ModifierElement.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/ComProtocol.h>
#include <fml/infrastructure/ComRoute.h>
#include <fml/infrastructure/Connector.h>
#include <fml/infrastructure/InteractionPart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/PropertyPart.h>
#include <fml/infrastructure/Transition.h>
#include <fml/infrastructure/System.h>
#include <fml/infrastructure/Variable.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>

#include <fml/template/TimedMachine.h>

#include <fml/type/TypeManager.h>

#include <sew/Configuration.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
AvmTestCaseFactory::AvmTestCaseFactory(
		AvmPathGuidedTestcaseGenerator & aProcessor,
		AvmTestCaseStatistics & aTestCaseStatistics,
		const Symbol & aQuiescencePortTP)
: mProcessor(aProcessor),
ENV( aProcessor.getENV() ),
mQuiescencePortTP( aQuiescencePortTP ),
mUncontrollableTraceFilter( mProcessor.getUncontrollableTraceFilter() ),
mTestCaseStatistics( aTestCaseStatistics ),
mTestPurposeTrace( ),
mTestPurposeInoutParams( ),
mTestPurposeClockParams( ),
mVarTC_subst_mParamTP_ED( ),
mTestPurposePathCondition( ),
mSystemSUT( mProcessor.getConfiguration().getSpecification() ),
mSystemTC( "tcSystem", mSystemSUT.getSpecifier() ),
mMachineTC( nullptr ),
mOutputPortSUT_toInputTC( ),
mUncontrollableSUT_toInputTC( ),
mQuiescencePortTC( ),
mVariable_TC_TM( ),
mVariable_TC_Clock( ),
mNewfreshInitialVars( ),
mNewfreshTraceVarsTP( ),
mNewfreshInitialTraceVarsTP( )
//mStateTC_FAIL( nullptr ),
//mStateTC_INC( nullptr )
{
	//!! NOTHING
}


////////////////////////////////////////////////////////////////////////////////
// QUIESCENCE
////////////////////////////////////////////////////////////////////////////////

void AvmTestCaseFactory::buildTestCase()
{
AVM_IF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "BUILD TEST CASE STRUCTURE " ) << std::flush;
	AVM_OS_DEBUG << INCR_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )

	buildStructure(mSystemSUT, mSystemTC);

	OutStream & out2File = mProcessor.getStream( "file#tc" );
	mSystemTC.toStream(out2File);

AVM_IF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )
	AVM_OS_DEBUG << DECR_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )
}

void AvmTestCaseFactory::buildStructure(const System & sutSystem, System & tcSystem)
{
	// Main test case machine
	mMachineTC = Machine::newStatemachine(& tcSystem, "tcMachine",
			Specifier::DESIGN_PROTOTYPE_STATIC_SPECIFIER);
	tcSystem.saveOwnedElement(mMachineTC);


//	mStateTC_FAIL = Machine::newState(tcMachine, "FAIL", Specifier::STATE_FINAL_MOC);
//	tcMachine->saveOwnedElement(mStateTC_FAIL);
//
//	mStateTC_INC = Machine::newState(tcMachine, "INC", Specifier::STATE_FINAL_MOC);
//	tcMachine->saveOwnedElement(mStateTC_INC);


	PropertyPart & tcPropertyDecl = mMachineTC->getPropertyPart();
	InteractionPart * tcInteractionPart = mMachineTC->getUniqInteraction();

	// Quiescence port
	Modifier outputModifier;
	outputModifier.setVisibilityPublic().setDirectionOutput();

	Port * quiescencePort = new Port(tcPropertyDecl, "Quiescence",
					IComPoint::IO_PORT_NATURE, outputModifier);
	mQuiescencePortTC = tcPropertyDecl.saveOwnedElement(quiescencePort);

	Connector & aConnector = tcInteractionPart->appendConnector(
			ComProtocol::PROTOCOL_ENVIRONMENT_KIND);
	aConnector.appendComRoute(quiescencePort, Modifier::PROPERTY_OUTPUT_DIRECTION );

	const PropertyPart & sutPropertyDecl = sutSystem.getPropertyPart();

	addPorts(tcPropertyDecl, tcInteractionPart, sutPropertyDecl);

	if( sutSystem.hasMachine() )
	{
		const CompositePart * sutCompositePart = sutSystem.getCompositePart();
		CompositePart::TableOfMachine::const_ref_iterator itm =
				sutCompositePart->getMachines().begin();
		CompositePart::TableOfMachine::const_ref_iterator endItm =
				sutCompositePart->getMachines().end();
		for( ; itm != endItm ; ++itm )
		{
			if( itm->hasPortSignal() )
			{
				addPorts(tcPropertyDecl, tcInteractionPart, itm->getPropertyPart());
			}
		}
	}

	ExecutionContext & rootEC =
			mProcessor.getConfiguration().getFirstExecutionTrace();

	AvmTestCaseUtils::getTestPurposeTrace(rootEC, mTestPurposeTrace);

	const ExecutionContext * tpTargetEC = mTestPurposeTrace.last();

	mVarTC_subst_mParamTP_ED = tpTargetEC->getExecutionData();

	mTestPurposePathCondition = tpTargetEC->getPathCondition();

//	AvmTestCaseUtils::getParameters(*tpTargetEC, mTestPurposeParams);
	AvmTestCaseUtils::newfreshTraceParamsFromEC(
			*tpTargetEC, mTestPurposeInoutParams, mTestPurposeClockParams);
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	mTestPurposeInoutParams.strFQN( AVM_OS_DEBUG << "mTestPurposeInoutParams :" << std::endl );
	mTestPurposeClockParams.strFQN( AVM_OS_DEBUG << "mTestPurposeClockParams :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	addVariables(tcPropertyDecl, mTestPurposeInoutParams, mTestPurposeClockParams);

	AvmTestCaseUtils::getInitialVariablesOfParameters(
			rootEC, *mMachineTC, mNewfreshInitialVars);
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	mNewfreshInitialVars.strFQN( AVM_OS_DEBUG << "mNewfreshInitialVars :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	AvmTestCaseUtils::newfreshTraceVarsFromEC(
			*tpTargetEC, *mMachineTC, mNewfreshTraceVarsTP);
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	mNewfreshTraceVarsTP.strFQN( AVM_OS_DEBUG << "mNewfreshTraceVarsTP :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	mNewfreshInitialTraceVarsTP.append(mNewfreshInitialVars);
	mNewfreshInitialTraceVarsTP.add_unique(mNewfreshTraceVarsTP);
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	mNewfreshInitialTraceVarsTP.strFQN( AVM_OS_DEBUG << "mNewfreshInitialTraceVarsTP :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

//	buildStatemachine();

	buildStatemachineTC();
}

void AvmTestCaseFactory::addPorts(PropertyPart & tcPropertyPart,
		InteractionPart * tcInteractionPart, const PropertyPart & sutPropertyPart)
{
	Modifier inputModifier;
	inputModifier.setVisibilityPublic().setDirectionInput();

	Modifier outputModifier;
	outputModifier.setVisibilityPublic().setDirectionOutput();

	PropertyPart::TableOfPort::const_ref_iterator sutItp =
			sutPropertyPart.getPorts().begin();
	PropertyPart::TableOfPort::const_ref_iterator sutEndItp =
			sutPropertyPart.getPorts().end();
	for( ; sutItp != sutEndItp ; ++sutItp )
	{
		Connector & aConnector = tcInteractionPart->appendConnector(
				ComProtocol::PROTOCOL_ENVIRONMENT_KIND);

		if( sutItp->getModifier().isDirectionInput() )
		{
			if( mUncontrollableTraceFilter.pass(sutItp->to< Port >()) )
			{
				Port * tcInputPort = new Port(tcPropertyPart,
						sutItp->getNameID(), IComPoint::IO_PORT_NATURE, inputModifier);
				tcInputPort->setParameters( sutItp->getParameters() );
				addType( sutItp->getParameters() );

				const BF & inPort = tcPropertyPart.saveOwnedElement(tcInputPort);

				mUncontrollableSUT_toInputTC.append(inPort);

				aConnector.appendComRoute(
						tcInputPort, Modifier::PROPERTY_INPUT_DIRECTION );
			}
			else
			{
				Port * tcOutputPort = new Port(tcPropertyPart,
						sutItp->getNameID(), IComPoint::IO_PORT_NATURE, outputModifier);
				tcOutputPort->setParameters( sutItp->getParameters() );
				addType( sutItp->getParameters() );
				tcPropertyPart.saveOwnedElement(tcOutputPort);

				aConnector.appendComRoute(
						tcOutputPort, Modifier::PROPERTY_OUTPUT_DIRECTION);
			}
		}
		else if( sutItp->getModifier().isDirectionOutput() )
		{
			Port * tcInputPort = new Port(tcPropertyPart,
					sutItp->getNameID(), IComPoint::IO_PORT_NATURE, inputModifier);
			tcInputPort->setParameters( sutItp->getParameters() );
			addType( sutItp->getParameters() );
			const BF & inPort = tcPropertyPart.saveOwnedElement(tcInputPort);

			mOutputPortSUT_toInputTC.append(inPort);

			aConnector.appendComRoute(
					tcInputPort, Modifier::PROPERTY_INPUT_DIRECTION);
		}
	}
}


void AvmTestCaseFactory::addType(const Variable::Table & portParameters)
{
	for( const auto & param : portParameters )
	{
		const Variable & paramVar = param.to< Variable >();
		if( paramVar.hasTypeSpecifier() )
		{
			addType(paramVar.getTypeSpecifier());
		}
		else if( paramVar.hasDataType() )
		{
			addType(paramVar.getDataType());
		}
	}
}

void AvmTestCaseFactory::addType(const BaseTypeSpecifier & paramType)
{
	if( paramType.hasAstElement() )
	{
		const DataType & dataType = paramType.getAstDataType();
		if( not dataType.hasTypeBasic() )
		{
			addType(dataType);
		}
	}
}

void AvmTestCaseFactory::addType(const DataType & dataType)
{
	if( not dataType.hasTypeBasic() )
	{
		if( mSystemTC.getDataType(dataType.getNameID()).invalid() )
		{
			mSystemTC.getPropertyPart().appendDataType(
					INCR_BF( const_cast< DataType * >(& dataType) ) );
		}
	}
}


void AvmTestCaseFactory::addVariables(PropertyPart & tcPropertyDecl,
		InstanceOfData::Table & tpInoutParameters,
		InstanceOfData::Table & tpClockParameters)
{
	ParametersRuntimeForm & paramsRF =
			mVarTC_subst_mParamTP_ED.getWritableParametersRuntimeForm();
	paramsRF.makeWritableDataTable();

	paramsRF.update(tpClockParameters);
	paramsRF.update(tpInoutParameters);


	// Variable Timeout declaration
	mVariable_TC_TM = tcPropertyDecl.saveOwnedElement(
			new Variable(mMachineTC,
					Modifier::PROPERTY_PRIVATE_MODIFIER,
					TypeManager::POS_RATIONAL, "TM") );

	avm_type_specifier_kind_t time_type_specifier =
			TimedMachine::timeTypeSpecifierKind(mSystemSUT.getSpecifier());
	const TypeSpecifier & aTimeDomain =
			TimedMachine::timeTypeSpecifier(mSystemSUT.getSpecifier());

	TypeSpecifier clockType(
			TypeManager::newClockTime(TYPE_CLOCK_SPECIFIER, aTimeDomain) );

	mVariable_TC_Clock = tcPropertyDecl.saveOwnedElement(
			new Variable(mMachineTC,
					Modifier::PROPERTY_PRIVATE_MODIFIER, clockType, "tc_clock") );


	InstanceOfData::Table::const_raw_iterator itParam = tpInoutParameters.begin();
	InstanceOfData::Table::const_raw_iterator endParam = tpInoutParameters.end();
	for( ; itParam != endParam ; ++itParam )
	{
		const BaseTypeSpecifier & paramType = (itParam)->getTypeSpecifier();

		addType(paramType);

		BF typeVar = INCR_BF( const_cast< BaseTypeSpecifier * >(& paramType) );

		const BF tcVar = tcPropertyDecl.saveOwnedElement(
				new Variable(mMachineTC,
						Modifier::PROPERTY_PRIVATE_MODIFIER,
						typeVar, (itParam)->getNameID()) );

		// For substitution of symbex parameters by testcase variables
		(itParam)->getwModifier().setFeatureFinal( false );
		paramsRF.setData( (itParam)->getOffset(), tcVar );
	}

//	BF & timeElapsedType = mSystemSUT.getPropertyPart().getDeltaTimeType();
	TypeSpecifier timeElapsedType(
			TypeManager::newClockTime(time_type_specifier, aTimeDomain) );

	endParam = tpClockParameters.end();
	for( itParam = tpClockParameters.begin() ; itParam != endParam ; ++itParam )
	{
		const BaseTypeSpecifier & paramType = (itParam)->getTypeSpecifier();
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( paramType.is< ContainerTypeSpecifier >() )
				<< "Unexpected a parameter variable < " << (itParam)->strHeaderId()
				<< " > without an time type as ContainerTypeSpecifier !" << std::endl
				<< SEND_EXIT;

//		TypeSpecifier timeElapsedType(
//				TypeManager::newClockTime(time_type_specifier,
//						paramType.to< ContainerTypeSpecifier
//							>().getContentsTypeSpecifier()) );
		const BF tcVar = tcPropertyDecl.saveOwnedElement(
				new Variable(mMachineTC,
						Modifier::PROPERTY_PRIVATE_MODIFIER,
						timeElapsedType, (itParam)->getNameID()) );

		// For substitution of symbex parameters by testcase variables
		(itParam)->getwModifier().setFeatureFinal( false );
		paramsRF.setData( (itParam)->getOffset(), tcVar );
	}
}


bool AvmTestCaseFactory::buildStatemachineTC()
{
	ExecutionContext::ListOfConstPtr traceECs(mTestPurposeTrace);
	const ExecutionContext * tcSourceEC = traceECs.pop_first();

	std::string stateID = (OSS() << "ec_" << tcSourceEC->getIdNumber()
			<< "_" << tcSourceEC->getExecutionData().strStateConf("%4%"));

	Machine * tcSourceState = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_START_MOC);
	mMachineTC->saveOwnedElement(tcSourceState);

	for( const auto tcTargetEC : traceECs )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Build state-transition for : " << tcSourceEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		Specifier stateSpec = Specifier::STATE_SIMPLE_MOC;

		tcSourceState = buildStep(*tcSourceState, *tcSourceEC, *tcTargetEC);

		tcSourceEC = tcTargetEC;
	}

	return true;
}

Machine * AvmTestCaseFactory::buildStep(Machine & tcSourceState,
		const ExecutionContext & tcSourceEC, const ExecutionContext & tcTargetEC)
{
	Machine * tcTargetState = nullptr;

	Port::Table unexpectedOutputSUT( mOutputPortSUT_toInputTC );
	Port::Table uncontrollableSUT( mUncontrollableSUT_toInputTC );

	// Test purpose EC
	const BF & ioTrace = tcTargetEC.getIOElementTrace();
	const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
	const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();

	if( StatementTypeChecker::isOutput(comTrace) )
	{
		if( tcTargetEC.hasChildContext() )
		{
			tcTargetState = applyRule_R02_Progress_SpecifiedOutput(
					tcSourceState, tcSourceEC, comTrace, tcTargetEC);
		}
		else
		{
			tcTargetState = applyRule_R04_Pass_SpecifiedOutput(
					tcSourceState, tcSourceEC, comTrace, tcTargetEC);
		}

		if( unexpectedOutputSUT.getByNameID(comPort.getNameID()).valid() )
		{
			applyRule_R10a_Fail_UnspecifiedOutput(
					tcSourceState, tcSourceEC, comTrace, tcTargetEC);

			unexpectedOutputSUT.removeByNameID(comPort.getNameID());
		}
	}
	// if( StatementTypeChecker::isInput(comTrace) )
	else if( mUncontrollableTraceFilter.pass(comPort) )
	{
		if( uncontrollableSUT.getByNameID(comPort.getNameID()).valid() )
		{
			tcTargetState = applyRule_R03_Progress_UncontrollableInput_Specified(
					tcSourceState, tcSourceEC, comTrace, tcTargetEC);

//			uncontrollableSUT.removeByNameID(comPort.getNameID());
		}
	}
	else
	{
		tcTargetState = applyRule_R01_Progress_Stimulation(
				tcSourceState, tcSourceEC, comTrace, tcTargetEC);
	}

	// Quiescence : Admissible
	applyRule_R09_Inconclusive_SpecifiedQuiescence_Admissible(
			tcSourceState, tcSourceEC, tcTargetEC);

	// Quiescence : Unspecified
	applyRule_R11_Fail_UnspecifiedQuiescence(
			tcSourceState, tcSourceEC, tcTargetEC);

	// Sibling test purpose EC
	for( const auto & aChildEC : tcSourceEC.getChildContexts()  )
	{
		if( aChildEC == (& tcTargetEC) )
		{
			continue;
		}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Build sibling-transition for child EC : " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		if( (not aChildEC->hasIOElementTrace())
			|| (not aChildEC->hasRunnableElementTrace() ) )
		{
			continue;
		}
		const BF & ioTrace = aChildEC->getIOElementTrace();
		const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
		const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();

		if( StatementTypeChecker::isOutput(comTrace) )
		{
			applyRule_R06_Inconclusive_SpecifiedOutput(
					tcSourceState, tcSourceEC, comTrace, *aChildEC);

			if( unexpectedOutputSUT.getByNameID(comPort.getNameID()).valid() )
			{
				applyRule_R10a_Fail_UnspecifiedOutput(
						tcSourceState, tcSourceEC, comTrace, *aChildEC);

				unexpectedOutputSUT.removeByNameID(comPort.getNameID());
			}
		}
		// if( StatementTypeChecker::isInput(comTrace) )
		else if( mUncontrollableTraceFilter.pass(comPort) )
		{
			applyRule_R07_Inconclusive_UncontrollableInput_Specified(
					tcSourceState, tcSourceEC, comTrace, *aChildEC);
		}
//		else
//		{
//			if( aChildEC->getFlags().hasCoverageElement() )
//			{
//				applyRule_R06_Inconclusive_UncontrollableInput_Specified(
//						tcSourceState, tcSourceEC, comTrace, *aChildEC);
//			}
//			else
//			{
//				applyRule_R07_Inconclusive_UncontrollableInput_unspecified(
//						tcSourceState, tcSourceEC, comTrace, *aChildEC);
//			}
//		}
	}

	for( const auto & ucInPort : uncontrollableSUT )
	{
		applyRule_R08_Inconclusive_UncontrollableInput_unspecified(
				tcSourceState, tcSourceEC, ucInPort, tcTargetEC);
	}

	for( const auto & obsPort : unexpectedOutputSUT )
	{
		applyRule_R10b_Fail_UnspecifiedOutput(
				tcSourceState, tcSourceEC, obsPort, tcTargetEC);
	}

	return tcTargetState;
}


////////////////////////////////////////////////////////////////////////////////
// RULES FOR TESCASE GENERATION
////////////////////////////////////////////////////////////////////////////////

BF AvmTestCaseFactory::boundTimeOutCondition(const ExecutionContext & tcSourceEC)
{
	// The time elapsed value : z_i
	const BF & varElapsedTime =
			AvmTestCaseUtils::newfreshDurationVarFromEC(tcSourceEC, *mMachineTC);

	// Time elapsed constraint
	return ExpressionConstructor::andExpr(
			ExpressionConstructor::ltExpr(mVariable_TC_Clock, mVariable_TC_TM),
			ExpressionConstructor::eqExpr(varElapsedTime, mVariable_TC_Clock) );
}

BFCode AvmTestCaseFactory::boundTimeOutPathConditionGuard(
		const ExecutionContext & tcSourceEC, const ExecutionContext & tcTargetEC)
{
	BF guardCondition = boundTimeOutCondition(*(tcTargetEC.getContainer()));

	if( not tcTargetEC.getPathCondition().isEqualTrue() )
	{
		if( mNewfreshInitialVars.empty() )
		{
			guardCondition = ExpressionConstructor::andExpr(
					guardCondition, tcTargetEC.getPathCondition());
		}
		else
		{
			guardCondition = ExpressionConstructor::andExpr(guardCondition,
					ExpressionConstructor::existsExpr(mNewfreshInitialVars,
							tcTargetEC.getPathCondition()));
		}
	}

	return StatementConstructor::newCode(
			OperatorManager::OPERATOR_GUARD, guardCondition);
}

BF AvmTestCaseFactory::unboundTimeOutCondition(const ExecutionContext & tcSourceEC)
{
	// The time elapsed value : z_i
	const BF & varElapsedTime =
			AvmTestCaseUtils::newfreshDurationVarFromEC(tcSourceEC, *mMachineTC);

	// Time elapsed constraint
	return ExpressionConstructor::andExpr(
			ExpressionConstructor::gteExpr(mVariable_TC_Clock, mVariable_TC_TM),
			ExpressionConstructor::eqExpr(varElapsedTime, mVariable_TC_Clock) );
}


// PROGRESS
Machine * AvmTestCaseFactory::applyRule_R01_Progress_Stimulation(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R01_Progress_Stimulation for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\ttp_PC : " << mTestPurposePathCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The target state on the test purpose path
	std::string stateID = (OSS() << "ec_" << tcTargetEC.getIdNumber()
			<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));
	Machine * tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_SIMPLE_MOC);
	mMachineTC->saveOwnedElement(tcTargetState);

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R1_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	BF guardCondition = boundTimeOutCondition(tcSourceEC);
	if( not mTestPurposePathCondition.isEqualTrue() )
	{
		Variable::Table boundVars( mNewfreshInitialTraceVarsTP );

		Variable::Table newfreshTraceVarsTargetEC;
		AvmTestCaseUtils::newfreshTraceVarsFromEC(
				tcSourceEC, *mMachineTC, newfreshTraceVarsTargetEC);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
		newfreshTraceVarsTargetEC.strFQN( AVM_OS_DEBUG << "newfreshVarsTargetEC :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

//		existsBoundVars.remove(F_vars(TargetEC));
		for( const auto & freshVarTargetEC : newfreshTraceVarsTargetEC )
		{
			boundVars.remove(freshVarTargetEC);
		}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	boundVars.strFQN( AVM_OS_DEBUG << "existsBoundVars :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		guardCondition = ExpressionConstructor::andExpr(
				guardCondition,
				boundVars.empty() ?
						mTestPurposePathCondition :
						ExpressionConstructor::existsExpr(
								boundVars,
								mTestPurposePathCondition
						)
		);
	}
	BFCode guard = StatementConstructor::newCode(
			OperatorManager::OPERATOR_GUARD, guardCondition);

	// Statistic collector
	mTestCaseStatistics.takeAccount(guardCondition, tpTransition);

	// The com statement
	BFCode tcComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	// The reset of the testcase clock
	BFCode tcClockReset = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, mVariable_TC_Clock,
			ExpressionConstant::INTEGER_ZERO);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE,
			guard, tcComStatement, tcClockReset));

	return tcTargetState;
}

// PROGRESS
Machine * AvmTestCaseFactory::applyRule_R02_Progress_SpecifiedOutput(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R02_Progress_SpecifiedOutput for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC    : " << tcTargetEC.getPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The target state on the test purpose path
	std::string stateID = (OSS() << "ec_" << tcTargetEC.getIdNumber()
			<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));
	Machine * tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_SIMPLE_MOC);
	mMachineTC->saveOwnedElement(tcTargetState);

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R2_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	BFCode guard = boundTimeOutPathConditionGuard(tcSourceEC, tcTargetEC);

	// Statistic collector
	mTestCaseStatistics.takeAccount(guard->first(), tpTransition);

	// The com statement
	BFCode tcComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	// The reset of the testcase clock
	BFCode tcClockReset = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, mVariable_TC_Clock,
			ExpressionConstant::INTEGER_ZERO);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE,
			guard, tcComStatement, tcClockReset));

	return tcTargetState;
}

// PROGRESS
Machine * AvmTestCaseFactory::applyRule_R03_Progress_UncontrollableInput_Specified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R03_Progress_UncontrollableInput_Specified for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The target state on the test purpose path
	std::string stateID = (OSS() << "ec_" << tcTargetEC.getIdNumber()
			<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));
	Machine * tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_SIMPLE_MOC);
	mMachineTC->saveOwnedElement(tcTargetState);

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R3_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	BFCode guard = boundTimeOutPathConditionGuard(tcSourceEC, tcTargetEC);

	// Statistic collector
	mTestCaseStatistics.takeAccount(guard->first(), tpTransition);

	// The com statement
	BFCode tcComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	// The reset of the testcase clock
	BFCode tcClockReset = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, mVariable_TC_Clock,
			ExpressionConstant::INTEGER_ZERO);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE,
			guard, tcComStatement, tcClockReset));

	return tcTargetState;
}

// PROGRESS --> PASS
Machine * AvmTestCaseFactory::applyRule_R04_Pass_SpecifiedOutput(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R04_Pass_SpecifiedOutput for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The target state PASS of the test purpose
	std::string stateID = (OSS() << "PASS_ec_" << tcTargetEC.getIdNumber()
			<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));
	Machine * tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_FINAL_MOC);
	mMachineTC->saveOwnedElement(tcTargetState);

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The transition PASS of the test purpose
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R4_PASS_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	BFCode guard = boundTimeOutPathConditionGuard(tcSourceEC, tcTargetEC);

	// Statistic collector
	mTestCaseStatistics.takeAccount(guard->first(), tpTransition);

	BFCode tcComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE, guard, tcComStatement));

	return tcTargetState;
}

Machine * AvmTestCaseFactory::applyRule_R05_Pass_SpecifiedQuiescence(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R05_Pass_SpecifiedQuiescence for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The target state PASS of the test purpose
	std::string stateID = (OSS() << "PASS_ec_" << tcTargetEC.getIdNumber()
			<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));
	Machine * tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_SIMPLE_MOC);
	mMachineTC->saveOwnedElement(tcTargetState);

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The transition PASS of the test purpose
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R5_PASS_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	BF unboundTM = unboundTimeOutCondition(tcSourceEC);
	BFCode guard = StatementConstructor::newCode(
			OperatorManager::OPERATOR_GUARD,
			ExpressionConstructor::andExpr(unboundTM,
					mNewfreshInitialVars.empty() ?
							tcTargetEC.getPathCondition() :
							ExpressionConstructor::existsExpr(
									mNewfreshInitialVars,
									tcTargetEC.getPathCondition()
							)
			)
	);

	// Statistic collector
	mTestCaseStatistics.takeAccount(guard->first(), tpTransition);

	BFCode tcComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE, guard, tcComStatement));

	return tcTargetState;
}


// INCONCLUSIVE OUTPUT
void AvmTestCaseFactory::applyRule_R06_Inconclusive_SpecifiedOutput(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R06_Inconclusive_SpecifiedOutput for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The target state on the test purpose path
	std::string stateID = (OSS() << "INC_out_ec_" << tcSourceEC.getIdNumber()
			<< "_" << tcTargetEC.getIdNumber() << "_" << portID);
	Machine * tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::PSEUDOSTATE_TERMINAL_MOC);
	mMachineTC->saveOwnedElement(tcTargetState);

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R6_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	BFCode guard = boundTimeOutPathConditionGuard(tcSourceEC, tcTargetEC);

	// Statistic collector
	mTestCaseStatistics.takeAccount(guard->first(), tpTransition);

	// The com statement
	BFCode tcComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE, guard, tcComStatement));
}

// INCONCLUSIVE UNCONTROLLABLE INPUT SPECIFIED
void AvmTestCaseFactory::applyRule_R07_Inconclusive_UncontrollableInput_Specified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R07_Inconclusive_UncontrollableInput_Specified for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The target state on the test purpose path
	std::string stateID = (OSS() << "INC_ucInSpec_ec_" << tcSourceEC.getIdNumber()
			<< "_" << tcTargetEC.getIdNumber() << "_" << portID);
	Machine * tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::PSEUDOSTATE_TERMINAL_MOC);
	mMachineTC->saveOwnedElement(tcTargetState);

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R7_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	BFCode guard = boundTimeOutPathConditionGuard(tcSourceEC, tcTargetEC);

	// Statistic collector
	mTestCaseStatistics.takeAccount(guard->first(), tpTransition);

	// The com statement
	BFCode tcComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE, guard, tcComStatement));
}

// INCONCLUSIVE UNCONTROLLABLE INPUT UNSPECIFIED
void AvmTestCaseFactory::applyRule_R08_Inconclusive_UncontrollableInput_unspecified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BF & ucInPort, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R08_Inconclusive_UncontrollableInput_unspecified for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tucInPort : " << ucInPort.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	const Port & ucInPortTC = ucInPort.to< Port >();

	// The guard
	BFCode ucontrollableInputGuards = ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_AND );
	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
		if( aChildEC->hasIOElementTrace() && aChildEC->hasRunnableElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & specComTrace = BaseEnvironment::searchTraceIO(ioTrace);

			if( StatementTypeChecker::isInput(specComTrace) )
			{
				const InstanceOfPort & ucinSpecPort =
						specComTrace->first().to< InstanceOfPort >();
				if( ucInPortTC.getNameID() == ucinSpecPort.getNameID() )
				{
					if( aChildEC->getPathCondition().isEqualTrue() )
					{
						ucontrollableInputGuards.append(
								ExpressionConstant::BOOLEAN_FALSE);
//						return;
					}
					else if( mNewfreshInitialVars.empty() )
					{
						ucontrollableInputGuards.append(
								ExpressionConstructor::notExpr(
										aChildEC->getPathCondition()) );
					}
					else
					{
						ucontrollableInputGuards.append(
								ExpressionConstructor::notExpr(
										ExpressionConstructor::existsExpr(mNewfreshInitialVars,
												aChildEC->getPathCondition()) ));
					}
				}
			}
		}
	}

	const std::string & portID = ucInPortTC.getNameID();

	// The target state on the test purpose path
	std::string stateID = (OSS() << "INC_ucInUspec_ec_"
			<< tcSourceEC.getIdNumber() << "_" << portID);
	Machine * tcTargetState = mMachineTC->getMachineByNameID(stateID);
	if( tcTargetState == nullptr )
	{
		tcTargetState = Machine::newState(mMachineTC,
				stateID, Specifier::PSEUDOSTATE_TERMINAL_MOC);
		mMachineTC->saveOwnedElement(tcTargetState);
	}

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R8_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	if( ucontrollableInputGuards.size() > 0 )
	{
		ucontrollableInputGuards.getOperands().push_front(
				boundTimeOutCondition(tcSourceEC));
	}
	else
	{
		ucontrollableInputGuards = boundTimeOutCondition(tcSourceEC);
	}
	BFCode guard = StatementConstructor::newCode(
			OperatorManager::OPERATOR_GUARD, ucontrollableInputGuards);

	// Statistic collector
	mTestCaseStatistics.takeAccount(ucontrollableInputGuards, tpTransition);

	// The com statement
	BFCode tcComStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_INPUT, ucInPort);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE, guard, tcComStatement));
}


// INCONCLUSIVE SPECIFIED QUIESCENCE ADMISSIBLE
void AvmTestCaseFactory::applyRule_R09_Inconclusive_SpecifiedQuiescence_Admissible(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R09_Inconclusive_SpecifiedQuiescence_Admissible for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	BF quiescenceCondition = compute_R09_QuiescenceCondition(tcSourceEC);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Quiescence condition " << quiescenceCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	if( quiescenceCondition.isEqualFalse() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Quiescence condition is FALSE ! " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
//		return;
	}

	// The target state on the test purpose path
	std::string stateID = (OSS() << "INC_dur_ec_" << tcSourceEC.getIdNumber() );
	Machine * tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::PSEUDOSTATE_TERMINAL_MOC);
	mMachineTC->saveOwnedElement(tcTargetState);

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R9_quiescenceAdmissible", Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	if( quiescenceCondition.isEqualTrue() )
	{
		quiescenceCondition = unboundTimeOutCondition(tcSourceEC);
	}
	else
	{
		quiescenceCondition = ExpressionConstructor::andExpr(
				unboundTimeOutCondition(tcSourceEC), quiescenceCondition);
	}
	BFCode guard = StatementConstructor::newCode(
			OperatorManager::OPERATOR_GUARD, quiescenceCondition);

	// Statistic collector
	mTestCaseStatistics.takeAccount(quiescenceCondition, tpTransition);

	// The com statement
	BFCode failQuiescenceStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_OUTPUT, mQuiescencePortTC);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE, guard, failQuiescenceStatement));
}

BF AvmTestCaseFactory::compute_R09_QuiescenceCondition(
		const ExecutionContext & tcSourceEC)
{
	AvmCode::OperandCollectionT phiOutput_UcInput;
	bool hasOutput_UcInput = false;

	const BF & varElapsedTime =
			AvmTestCaseUtils::newfreshDurationVarFromEC(tcSourceEC, *mMachineTC);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
AVM_OS_DEBUG << "R9_Quiescence condition varElapsedTime : " << varElapsedTime.strHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R9_Quiescence condition for " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

		if( aChildEC->hasIOElementTrace() )
		{
			Variable::Table boundVars( mNewfreshInitialVars );
			hasOutput_UcInput = false;

			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			const InstanceOfPort & comPort =
					comTrace->first().to< InstanceOfPort >();
			if( StatementTypeChecker::isOutput(comTrace) )
			{
				if( comPort.isTEQ(mQuiescencePortTP.rawPort()) )
				{
					if( not aChildEC->getPathCondition().isEqualTrue() )
					{
						phiOutput_UcInput.append(
								ExpressionConstructor::existsExpr(
										mNewfreshInitialVars,
										aChildEC->getPathCondition()
								)
						);
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R9_Quiescence condition for output< " << comPort.getNameID()
		<< " > of " << aChildEC->str() << " : ";
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
					}
				}
				else
				{
					hasOutput_UcInput = true;

					AvmTestCaseUtils::newfreshOutputVarsFromEC(
							tcSourceEC, *mMachineTC, boundVars);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R9_Quiescence condition for output< " << comPort.getNameID() << " > : ";
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
				}
			}
			else if( mUncontrollableTraceFilter.pass(comPort) )
			{
				hasOutput_UcInput = true;

				AvmTestCaseUtils::newfreshInputVarsFromEC(
						tcSourceEC, *mMachineTC, boundVars);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R9_Quiescence condition for ucInput< " << comPort.getNameID() << " > : ";
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
			}

			if( hasOutput_UcInput )
			{
				AvmCode::OperandCollectionT conditions;
				for( const auto & boundVar : boundVars)
				{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R9_Quiescence condition boundVar : " << boundVar.strHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

					const BF & type = boundVar.to< Variable >().getType();
					if( type.is< BaseTypeSpecifier >() &&
						type.to< BaseTypeSpecifier >().isTypedPositiveNumber() )
					{
						conditions.append(
								ExpressionConstructor::gteExpr(boundVar,
										ExpressionConstant::INTEGER_ZERO) );
					}
				}

				BF boundVarZ( new Variable(mMachineTC,
						Modifier::PROPERTY_PRIVATE_MODIFIER,
						varElapsedTime.to< Variable >().getType(), "z") );
				boundVars.append(boundVarZ);

				conditions.append(
						ExpressionConstructor::gteExpr(boundVarZ,
								ExpressionConstant::INTEGER_ZERO) );

				conditions.append(
						ExpressionConstructor::ltExpr(varElapsedTime, boundVarZ));

				BF substPC = AvmTestCaseUtils::substitution(
						mVarTC_subst_mParamTP_ED,
						aChildEC->getPathCondition(),
						varElapsedTime, boundVarZ);

				conditions.append(substPC);

				phiOutput_UcInput.append(
						ExpressionConstructor::existsExpr(boundVars,
								ExpressionConstructor::andExpr(conditions) ));

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << phiOutput_UcInput.last().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
			}
		}
	}

	if( phiOutput_UcInput.nonempty() )
	{
		return ExpressionConstructor::orExpr(phiOutput_UcInput);
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
}


// FAIL UNSPECIFIED OUTPUT
void AvmTestCaseFactory::applyRule_R10a_Fail_UnspecifiedOutput(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R10a_Fail_UnspecifiedOutput for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	const InstanceOfPort & failOutPort = comTrace->first().to< InstanceOfPort >();
	// The guard
	BFCode outputGuards = StatementConstructor::newCode(
			OperatorManager::OPERATOR_AND );
	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
		if( aChildEC->hasIOElementTrace() && aChildEC->hasRunnableElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & specComTrace = BaseEnvironment::searchTraceIO(ioTrace);

			if( StatementTypeChecker::isOutput(specComTrace) )
			{
				const InstanceOfPort & specOutPort =
						specComTrace->first().to< InstanceOfPort >();
				if( (& failOutPort) == (& specOutPort) )
				{
					if( aChildEC->getPathCondition().isEqualTrue() )
					{
						outputGuards.append(
								ExpressionConstant::BOOLEAN_FALSE);
//						return;
					}
					else if( mNewfreshInitialVars.empty() )
					{
						outputGuards.append( ExpressionConstructor::notExpr(
								aChildEC->getPathCondition()) );
					}
					else
					{
						outputGuards.append( ExpressionConstructor::notExpr(
								ExpressionConstructor::existsExpr(mNewfreshInitialVars,
										aChildEC->getPathCondition()) ));
					}
				}
			}
		}
	}

	const std::string & portID = failOutPort.getNameID();

	// The target state on the test purpose path
	std::string stateID = (OSS()<< "FAIL_out_ec_" << tcSourceEC.getIdNumber()
			<< "_" << tcTargetEC.getIdNumber() << "_" << portID);
	Machine * tcTargetState = mMachineTC->getMachineByNameID(stateID);
	if( tcTargetState == nullptr )
	{
		tcTargetState = Machine::newState(mMachineTC,
				stateID, Specifier::PSEUDOSTATE_TERMINAL_MOC);
		mMachineTC->saveOwnedElement(tcTargetState);
	}

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R10a_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	outputGuards.getOperands().push_front(boundTimeOutCondition(tcSourceEC));
	BFCode guard = StatementConstructor::newCode(
			OperatorManager::OPERATOR_GUARD, outputGuards);

	// Statistic collector
	mTestCaseStatistics.takeAccount(outputGuards, tpTransition);

	// The com statement
	BFCode tcComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE, guard, tcComStatement));
}


// FAIL UNSPECIFIED OUTPUT
void AvmTestCaseFactory::applyRule_R10b_Fail_UnspecifiedOutput(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BF & obsPort, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R10b_Fail_UnspecifiedOutput for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tobsPort : " << obsPort.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	const Port & inputPortTC = obsPort.to< Port >();

	// The guard
	BFCode unspecifiedOutputGuards = StatementConstructor::newCode(
			OperatorManager::OPERATOR_AND );
	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
		if( aChildEC->hasIOElementTrace() && aChildEC->hasRunnableElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & specComTrace = BaseEnvironment::searchTraceIO(ioTrace);

			if( StatementTypeChecker::isInput(specComTrace) )
			{
				const InstanceOfPort & ucinSpecPort =
						specComTrace->first().to< InstanceOfPort >();
				if( inputPortTC.getNameID() == ucinSpecPort.getNameID() )
				{
					if( aChildEC->getPathCondition().isEqualTrue() )
					{
						unspecifiedOutputGuards.append(
								ExpressionConstant::BOOLEAN_FALSE);
//						return;
					}
					else if( mNewfreshInitialVars.empty() )
					{
						unspecifiedOutputGuards.append(
								ExpressionConstructor::notExpr(
										aChildEC->getPathCondition()) );
					}
					else
					{
						unspecifiedOutputGuards.append(
								ExpressionConstructor::notExpr(
										ExpressionConstructor::existsExpr(mNewfreshInitialVars,
												aChildEC->getPathCondition()) ));
					}
				}
			}
		}
	}

	const std::string & portID = obsPort.to< Port >().getNameID();

	// The target state on the test purpose path
	std::string stateID = (OSS()<< "FAIL_out_ec_" << tcSourceEC.getIdNumber()
			<< "_" << portID);
	Machine * tcTargetState = mMachineTC->getMachineByNameID(stateID);
	if( tcTargetState == nullptr )
	{
		tcTargetState = Machine::newState(mMachineTC,
				stateID, Specifier::PSEUDOSTATE_TERMINAL_MOC);
		mMachineTC->saveOwnedElement(tcTargetState);
	}

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R10b_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	if( unspecifiedOutputGuards.size() > 0 )
	{
		unspecifiedOutputGuards.getOperands().push_front(
				boundTimeOutCondition(tcSourceEC));
	}
	else
	{
		unspecifiedOutputGuards = boundTimeOutCondition(tcSourceEC);
	}
	BFCode guard = StatementConstructor::newCode(
			OperatorManager::OPERATOR_GUARD, unspecifiedOutputGuards);

	// Statistic collector
	mTestCaseStatistics.takeAccount(unspecifiedOutputGuards, tpTransition);

	// The com statement
	BFCode tcComStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_INPUT, obsPort);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE, guard, tcComStatement));
}

// FAIL DURATION : UNSPECIFIED QUIESCENCE
void AvmTestCaseFactory::applyRule_R11_Fail_UnspecifiedQuiescence(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R11_Fail_UnspecifiedQuiescence for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	BF quiescenceCondition = compute_R11_QuiescenceCondition(tcSourceEC);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Quiescence condition " << quiescenceCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	if( quiescenceCondition.isEqualFalse() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Quiescence condition is FALSE ! " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
//		return;
		quiescenceCondition = ExpressionConstant::BOOLEAN_FALSE;
	}

	// The target state on the test purpose path
	std::string stateID = (OSS() << "FAIL_dur_ec_" << tcSourceEC.getIdNumber() );
	Machine * tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::PSEUDOSTATE_TERMINAL_MOC);
	mMachineTC->saveOwnedElement(tcTargetState);

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_R11_unspecifiedQuiescence", Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	// The guard
	if( quiescenceCondition.isEqualTrue() )
	{
		quiescenceCondition = unboundTimeOutCondition(tcSourceEC);
	}
	else
	{
		quiescenceCondition = ExpressionConstructor::andExpr(
				unboundTimeOutCondition(tcSourceEC), quiescenceCondition);
	}
	BFCode guard = StatementConstructor::newCode(
			OperatorManager::OPERATOR_GUARD, quiescenceCondition);

	// Statistic collector
	mTestCaseStatistics.takeAccount(quiescenceCondition, tpTransition);

	// The com statement
	BFCode failQuiescenceStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_OUTPUT, mQuiescencePortTC);

	tpTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE, guard, failQuiescenceStatement));
}


BF AvmTestCaseFactory::compute_R11_QuiescenceCondition(
		const ExecutionContext & tcSourceEC)
{
	AvmCode::OperandCollectionT phiOutput_UcInput;
	bool hasOutput_UcInput = false;

	const BF & varElapsedTime =
			AvmTestCaseUtils::newfreshDurationVarFromEC(tcSourceEC, *mMachineTC);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
AVM_OS_DEBUG << "R9_Quiescence condition varElapsedTime : " << varElapsedTime.strHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R11_Quiescence condition for " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

		if( aChildEC->hasIOElementTrace() )
		{
			Variable::Table boundVars( mNewfreshInitialVars );
			hasOutput_UcInput = false;

			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			const InstanceOfPort & comPort =
					comTrace->first().to< InstanceOfPort >();

			if( StatementTypeChecker::isOutput(comTrace) )
			{
				if( comPort.isTEQ(mQuiescencePortTP.rawPort()) )
				{
					phiOutput_UcInput.append(
							ExpressionConstructor::forallExpr(
									mNewfreshInitialVars,
									ExpressionConstructor::notExpr(
											aChildEC->getPathCondition()
									)
							)
					);
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R11_Quiescence condition for < " << comPort.getNameID() << " > of "
		<< aChildEC->str() << " : " << phiOutput_UcInput.last().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
				}
				else
				{
					hasOutput_UcInput = true;

					AvmTestCaseUtils::newfreshOutputVarsFromEC(
							tcSourceEC, *mMachineTC, boundVars);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R11_Quiescence condition for output< " << comPort.getNameID() << " > : ";
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
				}
			}
			else if( mUncontrollableTraceFilter.pass(comPort) )
			{
				hasOutput_UcInput = true;

				AvmTestCaseUtils::newfreshInputVarsFromEC(
						tcSourceEC, *mMachineTC, boundVars);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R11_Quiescence condition for ucInput< " << comPort.getNameID() << " > : ";
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
			}

			if( hasOutput_UcInput )
			{
				AvmCode::OperandCollectionT preConditions;
				for( const auto & boundVar : boundVars)
				{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R11_Quiescence condition boundVar : " << boundVar.strHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

					const BF & type = boundVar.to< Variable >().getType();
					if( type.is< BaseTypeSpecifier >() &&
						type.to< BaseTypeSpecifier >().isTypedPositiveNumber() )
					{
						preConditions.append(
								ExpressionConstructor::gteExpr(boundVar,
										ExpressionConstant::INTEGER_ZERO) );
					}
				}

				BF boundVarZ( new Variable(mMachineTC,
						Modifier::PROPERTY_PRIVATE_MODIFIER,
						varElapsedTime.to< Variable >().getType(), "z") );
				boundVars.append(boundVarZ);

				preConditions.append(
						ExpressionConstructor::gteExpr(boundVarZ,
								ExpressionConstant::INTEGER_ZERO) );

				BF substPC = AvmTestCaseUtils::substitution(
						mVarTC_subst_mParamTP_ED,
						aChildEC->getPathCondition(),
						varElapsedTime, boundVarZ);

				BF zCond = ExpressionConstructor::ltExpr(varElapsedTime, boundVarZ);

				if( preConditions.nonempty() )
				{
					phiOutput_UcInput.append(
							ExpressionConstructor::forallExpr(
									boundVars,
									ExpressionConstructor::impliesExpr(
											ExpressionConstructor::andExpr(
													preConditions
											),
											ExpressionConstructor::notExpr(
													ExpressionConstructor::andExpr(
															zCond, substPC
													)
											)
									)
							)
					);
				}
				else
				{
					phiOutput_UcInput.append(
							ExpressionConstructor::forallExpr(
									boundVars,
									ExpressionConstructor::notExpr(
											ExpressionConstructor::andExpr(
													zCond, substPC
											)
									)
							)
					);
				}
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << phiOutput_UcInput.last().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
			}
		}
	}
	if( phiOutput_UcInput.nonempty() )
	{
		return ExpressionConstructor::andExpr(phiOutput_UcInput);
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmTestCaseFactory::buildStatemachine()
{
	ExecutionContext::ListOfConstPtr traceECs(mTestPurposeTrace);
	const ExecutionContext * tcSourceEC = traceECs.pop_first();

	std::string stateID = (OSS() << "ec_" << tcSourceEC->getIdNumber()
			<< "_" << tcSourceEC->getExecutionData().strStateConf("%4%"));

	Machine * tcSourceState = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_START_MOC);
	mMachineTC->saveOwnedElement(tcSourceState);

	for( const auto tcTargetEC : traceECs )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Build state-transition for : " << tcSourceEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		Specifier stateSpec = Specifier::STATE_SIMPLE_MOC;

		tcSourceState = buildState(*tcSourceState, *tcSourceEC, *tcTargetEC);

		tcSourceEC = tcTargetEC;
	}
	tcSourceState->setNames( tcSourceState->getNameID() + "_PASS" );
	tcSourceState->updateFullyQualifiedNameID();


	return true;
}

Machine * AvmTestCaseFactory::buildState(Machine & tcSourceState,
		const ExecutionContext & tcSourceEC, const ExecutionContext & tcTargetEC)
{
	std::string stateID = (OSS() << "ec_" << tcTargetEC.getIdNumber()
			<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));
	Machine * tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_SIMPLE_MOC);
	mMachineTC->saveOwnedElement(tcTargetState);

	Transition * tpTransition = new Transition(tcSourceState,
			"t_" + stateID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	tcSourceState.saveOwnedElement( tpTransition );

	const BF & ioTrace = tcTargetEC.getIOElementTrace();
	const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
	const BF & comPort = comTrace->first();
	const std::string & portID = comPort.to< InstanceOfPort >().getNameID();

	BF tcPort = mMachineTC->getPort(portID);
//	BF tcPort = ExpressionConstructor::newIdentifier(portID);

	const BF & varElapsedTime =
			AvmTestCaseUtils::newfreshDurationVarFromEC(tcSourceEC, *mMachineTC);

	BF tmConstraint = ExpressionConstructor::ltExpr(varElapsedTime, mVariable_TC_TM);

	if( StatementTypeChecker::isOutput(comTrace) )
	{
		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD,
				ExpressionConstructor::andExpr(
						tmConstraint, tcTargetEC.getPathCondition()));

		BFCode observ = StatementConstructor::newCode(
				OperatorManager::OPERATOR_INPUT, tcPort);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE, guard, observ));

		addFailQuiescenceTransition(tcSourceEC, tcSourceState);

		BFList specSutOutputPort; // Only local soec output not in TP
		sutUnexpectedOutput(tcSourceEC, comPort, specSutOutputPort);

		addIncInputTransition(tcSourceEC,
				tcSourceState, specSutOutputPort, false);

		specSutOutputPort.append(comPort); // All local spec output
		addFailInputTransition(tcSourceEC,
				tcSourceState, specSutOutputPort, false);
//		addIncInputTransition(tcSourceState, tcPort->to< Port >());
	}
	else
	{
		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD,
				ExpressionConstructor::andExpr(
						tmConstraint, mTestPurposePathCondition));

		BFCode stimuli = StatementConstructor::newCode(
				OperatorManager::OPERATOR_OUTPUT, tcPort);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE, guard, stimuli));

		addFailInputTransition(tcSourceEC, tcSourceState, false);
	}

	return tcTargetState;
}

void AvmTestCaseFactory::sutUnexpectedOutput(
		const ExecutionContext & tcSourceEC,
		const BF tpOutputPort, BFList & specSutOutputPort)
{
	for( const auto & aChildEC : tcSourceEC.getChildContexts()  )
	{
		const BF & ioTrace = aChildEC->getIOElementTrace();
		const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
		const BF & comPort = comTrace->first();
		if( StatementTypeChecker::isOutput(comTrace) && (tpOutputPort != comPort) )
		{
			specSutOutputPort.append(comPort);
		}
	}
}


void AvmTestCaseFactory::addIncInputTransition(
		const ExecutionContext & tcSourceEC, Machine & tcSourceState,
		const BFList & specSutOutputPort, bool groupIncInput)
{
	BFCodeList allIncInputStatement;

//	Machine * treeStateINC = nullptr;

	for( const auto & sutPort : specSutOutputPort )
	{
		const std::string & portID = sutPort.to< InstanceOfPort >().getNameID();
		BF tcPort = mMachineTC->getPort(portID);

		allIncInputStatement.append( StatementConstructor::newCode(
				OperatorManager::OPERATOR_INPUT, tcPort) );
	}

	createIncInputTransition(tcSourceEC, tcSourceState,
			allIncInputStatement, groupIncInput);
}

void AvmTestCaseFactory::createIncInputTransition(
		const ExecutionContext & tcSourceEC, Machine & tcSourceState,
		const BFCodeList & allIncInputStatement, bool groupFailedInput)
{
	if( allIncInputStatement.nonempty() )
	{
		std::string stateID = (OSS() << "INC_ec_" << tcSourceEC.getIdNumber());
		Machine * treeStateINC = Machine::newState(mMachineTC,
				stateID, Specifier::STATE_FINAL_MOC);
		mMachineTC->saveOwnedElement(treeStateINC);

		if( groupFailedInput )
		{
			Transition * failTransition = new Transition(tcSourceState,
					"t_inc", Transition::MOC_SIMPLE_KIND);
			failTransition->setTarget( *treeStateINC );
			tcSourceState.saveOwnedElement( failTransition );

			failTransition->setStatement( allIncInputStatement.singleton() ?
					allIncInputStatement.first() :
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_SCHEDULE_OR_ELSE,
							allIncInputStatement) );
		}
		else
		{
			for( const auto & failedInputStatement : allIncInputStatement )
			{
				const std::string & trNameID =
						failedInputStatement->first().to< Port >().getNameID();
				Transition * failTransition = new Transition(tcSourceState,
						"t_inc_" + trNameID, Transition::MOC_SIMPLE_KIND);
				failTransition->setTarget( *treeStateINC );
				tcSourceState.saveOwnedElement( failTransition );

				failTransition->setStatement(failedInputStatement);
			}
		}
	}
}

void AvmTestCaseFactory::addFailQuiescenceTransition(
		const ExecutionContext & tcSourceEC, Machine & tcSourceState)
{
	std::string stateID =
			(OSS() << "FAIL_dur_ec_" << tcSourceEC.getIdNumber());
	Machine * treeStateFAIL = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_FINAL_MOC);
	mMachineTC->saveOwnedElement(treeStateFAIL);

	Transition * quiescTransition = new Transition(tcSourceState,
			"t_quiescence", Transition::MOC_SIMPLE_KIND);
	quiescTransition->setTarget( *treeStateFAIL );
	tcSourceState.saveOwnedElement( quiescTransition );

	const BF & varElapsedTime =
			AvmTestCaseUtils::newfreshDurationVarFromEC(tcSourceEC, *mMachineTC);

	BFCode guard = StatementConstructor::newCode(
			OperatorManager::OPERATOR_GUARD,
			ExpressionConstructor::gteExpr(varElapsedTime, mVariable_TC_TM) );

	BFCode failQuiescenceStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_OUTPUT, mQuiescencePortTC);

	quiescTransition->setStatement( StatementConstructor::newCode(
			OperatorManager::OPERATOR_SEQUENCE, guard, failQuiescenceStatement));
}

void AvmTestCaseFactory::addFailInputTransition(
		const ExecutionContext & tcSourceEC,
		Machine & tcSourceState, bool groupFailedInput)
{
	BFCodeList allFailedInputStatement;

//	Machine * treeStateFAIL = nullptr;

	const PropertyPart & tcPropertyPart = mMachineTC->getPropertyPart();
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

	createFailInputTransition(tcSourceEC, tcSourceState,
			allFailedInputStatement, groupFailedInput);
}

void AvmTestCaseFactory::addFailInputTransition(
		const ExecutionContext & tcSourceEC, Machine & tcSourceState,
		const BFList & specSutOutputPort, bool groupFailedInput)
{
	BFCodeList allFailedInputStatement;

//	Machine * treeStateFAIL = nullptr;

	const PropertyPart & tcPropertyPart = mMachineTC->getPropertyPart();
	PropertyPart::TableOfPort::const_ref_iterator itp = tcPropertyPart.getPorts().begin();
	PropertyPart::TableOfPort::const_ref_iterator endItp = tcPropertyPart.getPorts().end();
	for( ; itp != endItp ; ++itp )
	{
		if( itp->getModifier().isDirectionInput() )
		{
			bool isUnexpectedOutput = true;
			for( const auto & sutPort : specSutOutputPort )
			{
				const std::string & portID =
						sutPort.to< InstanceOfPort >().getNameID();
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

	createFailInputTransition(tcSourceEC, tcSourceState,
			allFailedInputStatement, groupFailedInput);
}

void AvmTestCaseFactory::createFailInputTransition(
		const ExecutionContext & tcSourceEC, Machine & tcSourceState,
		const BFCodeList & allFailedInputStatement, bool groupFailedInput)
{
	if( allFailedInputStatement.nonempty() )
	{
		std::string stateID =
				(OSS() << "FAIL_out_ec_" << tcSourceEC.getIdNumber());
		Machine * treeStateFAIL = Machine::newState(mMachineTC,
				stateID, Specifier::STATE_FINAL_MOC);
		mMachineTC->saveOwnedElement(treeStateFAIL);

		const BF & varElapsedTime =
				AvmTestCaseUtils::newfreshDurationVarFromEC(
						tcSourceEC, *mMachineTC);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD,
				ExpressionConstructor::ltExpr(varElapsedTime, mVariable_TC_TM) );

		if( groupFailedInput )
		{
			Transition * failTransition = new Transition(tcSourceState,
					"t_fail_out", Transition::MOC_SIMPLE_KIND);
			failTransition->setTarget( *treeStateFAIL );
			tcSourceState.saveOwnedElement( failTransition );

			BF failedTransStatement = allFailedInputStatement.singleton() ?
					allFailedInputStatement.first() :
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_SCHEDULE_OR_ELSE,
							allFailedInputStatement);

			failTransition->setStatement(StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					guard, failedTransStatement) );
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

				failTransition->setStatement(StatementConstructor::newCode(
						OperatorManager::OPERATOR_SEQUENCE,
						guard, failedInputStatement) );
			}
		}
	}
}


} /* namespace sep */

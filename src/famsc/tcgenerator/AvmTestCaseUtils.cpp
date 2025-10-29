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

#include "AvmTestCaseUtils.h"

#include <computer/BaseEnvironment.h>

#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/StatementFactory.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/PropertyPart.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionContext.h>


namespace sep
{


void AvmTestCaseUtils::getTestPurposeTrace(const ExecutionContext & anEC,
		ExecutionContext::VectorOfConstPtr & testPurposeTrace)
{
	if( anEC.getFlags().hasObjectiveAchievedTrace() )
	{
		testPurposeTrace.append(& anEC);

		if( not anEC.hasChildContext() )
		{
			return;
		}
	}
	for( const auto & aChildEC : anEC.getChildContexts() )
	{
		if( aChildEC->getFlags().hasObjectiveAchievedTrace() )
		{
			getTestPurposeTrace(*aChildEC, testPurposeTrace);
			return;
		}
		else if( testPurposeTrace.empty() )
		{
			getTestPurposeTrace(*aChildEC, testPurposeTrace);
		}
	}
}



void AvmTestCaseUtils::getParameters(const ExecutionContext & tpEC,
		InstanceOfData::Table & listOfParameters)
{
//	BF tpPC = tpTargetEC.getPathCondition();

//	ExpressionFactory::collectVariable(tpPC, testPurposeParameters);

	const ParametersRuntimeForm & paramRF =
			tpEC.getExecutionData().getParametersRuntimeForm();

	TableOfInstanceOfData::const_raw_iterator itParam = paramRF.getParameters().begin();
	TableOfInstanceOfData::const_raw_iterator endParam = paramRF.getParameters().end();
	for( ; itParam != endParam ; ++itParam )
	{
//AVM_OS_DEBUG << "Param : " << itParam->getFullyQualifiedNameID() << std::endl;

		if( (itParam->getNameID() != PropertyPart::VAR_ID_TIME_INITIAL)
			&& (itParam->getNameID() != PropertyPart::VAR_ID_DELTA_TIME_INITIAL)
			&& itParam->getModifier().hasNatureParameter() )
		{
			listOfParameters.append(*itParam);
		}
	}
}

void AvmTestCaseUtils::getInitialVariablesOfParameters(const ExecutionContext & tpEC,
		Machine & tcMachine, Variable::Table & initParamVariables)
{
	const ParametersRuntimeForm & paramRF =
			tpEC.getExecutionData().getParametersRuntimeForm();

	TableOfInstanceOfData::const_raw_iterator itParam = paramRF.getParameters().begin();
	TableOfInstanceOfData::const_raw_iterator endParam = paramRF.getParameters().end();
	for( avm_offset_t offset = 0 ; itParam != endParam ; ++itParam , ++offset)
	{
		if( (itParam->getNameID() != PropertyPart::VAR_ID_TIME_INITIAL)
			&& (itParam->getNameID() != PropertyPart::VAR_ID_DELTA_TIME_INITIAL)
			&& itParam->getModifier().hasNatureParameter() )
		{
//AVM_OS_DEBUG << "ParamVariable : " << itParam->getFullyQualifiedNameID() << std::endl;

			initParamVariables.append( BF( new Variable(& tcMachine,
					sep::Modifier::PROPERTY_PRIVATE_MODIFIER,
					itParam->getAstElement().to< Variable >().getType(),
					itParam->getNameID()) ));
		}
	}
}

void AvmTestCaseUtils::getComPortVariableArguments(
		const Machine & tcMachine, const BFCode & comTrace,
		BF & tcPort, Variable::Table & varArgs, bool addUnique)
{
	const BF comPort = comTrace->first();
	const std::string & portID = comPort.to< InstanceOfPort >().getNameID();
	tcPort = tcMachine.getPort(portID);

	auto itArg = comTrace.getOperands().begin();
	const auto & endArg = comTrace.getOperands().end();
	for( ++itArg ; itArg != endArg ; ++itArg)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( (*itArg).is< InstanceOfData >() )
				<< "Unfexpected a comTrace< " << comTrace.str()
				<< " > without a variable argument< " << (*itArg).str()
				<< " > !" << std::endl
				<< SEND_EXIT;

		const std::string & varArgID = (*itArg).to< InstanceOfData >().getNameID();
		const BF & varArg = tcMachine.getVariable(varArgID);
		if( varArg.valid() )
		{
			if( addUnique )
			{
				varArgs.add_unique(varArg);
			}
			else
			{
				varArgs.append(varArg);
			}
		}
		else
		{
			AVM_OS_CERR << "Unfound in the comTrace< " << comTrace.str()
						<< " > the variable argument< " << varArgID
						<< " > in the testcase variables declaration !" << std::endl;
		}
	}
}

void AvmTestCaseUtils::comParametersFromEC(
		const ExecutionContext & tpEC, InstanceOfData::Table & comParams)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		if( aChildEC->hasIOElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			if( ! comTrace.valid() )
			{
				continue;
			}

			auto itArg = comTrace.getOperands().begin();
			const auto & endArg = comTrace.getOperands().end();
			for( ++itArg ; itArg != endArg ; ++itArg)
			{
				AVM_OS_ASSERT_FATAL_ERROR_EXIT( (*itArg).is< InstanceOfData >() )
						<< "Unfexpected a comTrace< " << comTrace.str()
						<< " > without a variable argument< " << (*itArg).str()
						<< " > !" << std::endl
						<< SEND_EXIT;

				comParams.add_unique( *itArg );
			}
		}
	}
}


BFCode AvmTestCaseUtils::tpTrace_to_tcStatement(
		const Machine & tcMachine, const BFCode & comTrace)
{
	BF tcPort;
	Variable::Table varArgs;
	getComPortVariableArguments(tcMachine, comTrace, tcPort, varArgs, false);

//	return StatementConstructor::newCode(comTrace.getOperator(), tcPort, varArgs);
	// Because the comTrace.getOperator() may be the OPERATOR_INPUT_ENV
	if( tcPort.to< Port >().getModifier().isDirectionInput() )
	{
		return StatementConstructor::newCode(
				OperatorManager::OPERATOR_INPUT, tcPort, varArgs);
	}
	// Because the comTrace.getOperator() may be the OPERATOR_OUTPUT_ENV
	else //if( tcPort.to< Port >().getModifier().isDirectionOutput() )
	{
		return StatementConstructor::newCode(
				OperatorManager::OPERATOR_OUTPUT, tcPort, varArgs);
	}
}


//void AvmTestCaseUtils::getComPortParametertsArguments(
//		const Machine & tcMachine, const BFCode & comTrace,
//		BF & tcPort, AvmCode::OperandCollectionT & paramArgs)
//{
//	const BF comPort = comTrace->first();
//	const std::string & portID = comPort.to< InstanceOfPort >().getNameID();
//	tcPort = tcMachine.getPort(portID);
//
//	auto itArg = comTrace.getOperands().begin();
//	const auto & endArg = comTrace.getOperands().end();
//	for( ++itArg ; itArg != endArg ; ++itArg)
//	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( (*itArg).is< InstanceOfData >() )
//				<< "Unfexpected a comTrace< " << comTrace.str()
//				<< " > without a variable argument< " << (*itArg).str()
//				<< " > !" << std::endl
//				<< SEND_EXIT;
//
//		paramArgs.append(*itArg);
//	}
//}
//
//
//BFCode AvmTestCaseUtils::tpTrace_to_tcIncFailStatement(
//		const Machine & tcMachine, const BFCode & comTrace)
//{
//	BF tcPort;
//	AvmCode::OperandCollectionT paramArgs;
//	getComPortParametertsArguments(tcMachine, comTrace, tcPort, paramArgs);
//
////	return StatementConstructor::newCode(comTrace.getOperator(), tcPort, varArgs);
//	// Because the comTrace.getOperator() may be the OPERATOR_INPUT_ENV
//	if( tcPort.to< Port >().getModifier().isDirectionInput() )
//	{
//		return StatementConstructor::newCode(
//				OperatorManager::OPERATOR_INPUT, tcPort, paramArgs);
//	}
//	// Because the comTrace.getOperator() may be the OPERATOR_OUTPUT_ENV
//	else //if( tcPort.to< Port >().getModifier().isDirectionOutput() )
//	{
//		return StatementConstructor::newCode(
//				OperatorManager::OPERATOR_OUTPUT, tcPort, paramArgs);
//	}
//}


/////////////////////////////////////////
// Substitution
/////////////////////////////////////////

BF AvmTestCaseUtils::substitution(const BF & anExpression,
		const BF & oldTerm, const BF & newTerm)
{
	if( anExpression.is< AvmCode >() )
	{
		BFCode substExpression( anExpression.to< AvmCode >().getOperator() );
		for( const auto & itOperand : anExpression.to< AvmCode >().getOperands() )
		{
			substExpression.append( substitution(itOperand, oldTerm, newTerm) );
		}
		return substExpression;
	}
	else if( oldTerm.isTEQ(anExpression) )
	{
		return BF(newTerm);
	}
	else if( anExpression.is< InstanceOfData >() && oldTerm.is< Variable >()
			&& anExpression.to< InstanceOfData >().getNameID() ==
					oldTerm.to< Variable >().getNameID() )
	{
		return BF(newTerm);
	}

	return BF(anExpression);
}

//BF AvmTestCaseUtils::substitution(const ExecutionData & varTC_subst_mParamTP_ED,
//		const BF & anExpression, const BF & oldTerm, const BF & newTerm)
//{
//	ExecutionData substED = varTC_subst_mParamTP_ED;
//	ParametersRuntimeForm & paramsRF = substED.getWritableParametersRuntimeForm();
//	if( oldTerm.is< InstanceOfData >() )
//	{
//		paramsRF.setData( oldTerm.is< InstanceOfData >().getOffset(), newTerm );
//	}
//
//	if( ENV.eval(substED, substED.getSystemRID(), anExpression) )
//	{
//		return ENV.outVAL;
//	}
//
//	return anExpression;
//}


/////////////////////////////////////////
// Fresh variables of EC
/////////////////////////////////////////

const BF & AvmTestCaseUtils::newfreshDurationVarOfEC(
		const ExecutionContext & anEC, const Machine & tcMachine)
{
	const BF & deltaTimeValue = anEC.getExecutionData().getDeltaTimeValue();
	if( deltaTimeValue.is< InstanceOfData >() )
	{
		const BF & varElapsedTime = tcMachine.getVariable(
				deltaTimeValue.to< InstanceOfData >().getNameID() );
		if( varElapsedTime.valid() )
		{
			return varElapsedTime;
		}
		else
		{
			AVM_OS_CERR << "Unfound for " << anEC.str()
					<< " the declaration of the elapsed time parameter< "
					<< deltaTimeValue.to< InstanceOfData >().getFullyQualifiedNameID()
					<< " > !" << std::endl;
		}
	}
	else if( anEC.hasIOElementTrace() )
	{
		AVM_OS_CERR << "Unexpected " << anEC.str()
				<< " without elapsed time< " << deltaTimeValue.str()
				<< " > as testcase parameter !" << std::endl;
	}

	return BF::REF_NULL;
}


const BF & AvmTestCaseUtils::newfreshDurationVarFromEC(
		const ExecutionContext & tpEC, const Machine & tcMachine)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		const BF & deltaTimeValue = aChildEC->getExecutionData().getDeltaTimeValue();
		if( deltaTimeValue.is< InstanceOfData >() )
		{
			const BF & varElapsedTime = tcMachine.getVariable(
					deltaTimeValue.to< InstanceOfData >().getNameID() );
			if( varElapsedTime.valid() )
			{
				return varElapsedTime;
			}
			else
			{
				AVM_OS_CERR << "Unfound for " << aChildEC->str()
						<< " the declaration of the elapsed time parameter< "
						<< deltaTimeValue.to< InstanceOfData >().getFullyQualifiedNameID()
						<< " > !" << std::endl;
			}
		}
		else if( aChildEC->hasIOElementTrace() )
		{
			AVM_OS_CERR << "Unexpected " << aChildEC->str()
					<< " without elapsed time< " << deltaTimeValue.str()
					<< " > as testcase parameter !" << std::endl;
		}
	}

	return BF::REF_NULL;
}

void AvmTestCaseUtils::newfreshDurationVarsOfEC(const ExecutionContext & anEC,
		const Machine & tcMachine, Variable::Table & tcVars)
{
	const BF & deltaTimeValue = anEC.getExecutionData().getDeltaTimeValue();
	if( deltaTimeValue.is< InstanceOfData >() )
	{
		const BF & varElapsedTime = tcMachine.getVariable(
				deltaTimeValue.to< InstanceOfData >().getNameID() );
		if( varElapsedTime.valid() )
		{
			tcVars.add_unique(varElapsedTime);
		}
		else
		{
			AVM_OS_CERR << "Unfound for " << anEC.str()
					<< " the declaration of the elapsed time parameter< "
					<< deltaTimeValue.to< InstanceOfData >().getFullyQualifiedNameID()
					<< " > !" << std::endl;
		}
	}
	else if( anEC.hasIOElementTrace() )
	{
		AVM_OS_CERR << "Unexpected " << anEC.str()
				<< " without elapsed time< " << deltaTimeValue.str()
				<< " > as testcase parameter !" << std::endl;
	}
}

void AvmTestCaseUtils::newfreshDurationVarsFromEC(const ExecutionContext & tpEC,
		const Machine & tcMachine, Variable::Table & tcVars)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		newfreshDurationVarsOfEC(*aChildEC, tcMachine, tcVars);
	}
}


void AvmTestCaseUtils::newfreshInputVarsOfEC(const ExecutionContext & anEC,
		const Machine & tcMachine, Variable::Table & tcVars)
{
	if( anEC.hasIOElementTrace() )
	{
		const BF & ioTrace = anEC.getIOElementTrace();
		const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
		if( comTrace.valid() && StatementTypeChecker::isInput(comTrace) )
		{
			BF tcPort;
			getComPortVariableArguments(tcMachine, comTrace, tcPort, tcVars);
		}
	}
}

void AvmTestCaseUtils::newfreshInputVarsFromEC(const ExecutionContext & tpEC,
		const Machine & tcMachine, Variable::Table & tcVars)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		newfreshInputVarsOfEC(*aChildEC, tcMachine, tcVars);
	}
}


void AvmTestCaseUtils::newfreshOutputVarsOfEC(const ExecutionContext & anEC,
		const Machine & tcMachine, Variable::Table & tcVars)
{
	if( anEC.hasIOElementTrace() )
	{
		const BF & ioTrace = anEC.getIOElementTrace();
		const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
		if( comTrace.valid() && StatementTypeChecker::isOutput(comTrace) )
		{
			BF tcPort;
			getComPortVariableArguments(tcMachine, comTrace, tcPort, tcVars);
		}
	}
}

void AvmTestCaseUtils::newfreshOutputVarsFromEC(const ExecutionContext & tpEC,
		const Machine & tcMachine, Variable::Table & tcVars)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		newfreshOutputVarsOfEC(*aChildEC, tcMachine, tcVars);
	}
}


void AvmTestCaseUtils::newfreshInoutVarsOfEC(const ExecutionContext & anEC,
		const Machine & tcMachine, Variable::Table & tcVars)
{
	if( anEC.hasIOElementTrace() )
	{
		const BF & ioTrace = anEC.getIOElementTrace();
		const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
		if( comTrace.valid() )
		{
			BF tcPort;
			getComPortVariableArguments(tcMachine, comTrace, tcPort, tcVars);
		}
	}
}

void AvmTestCaseUtils::newfreshInoutVarsFromEC(const ExecutionContext & tpEC,
		const Machine & tcMachine, Variable::Table & tcVars)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		newfreshInoutVarsOfEC(*aChildEC, tcMachine, tcVars);
	}
}


/////////////////////////////////////////
// Newfresh parameters of EC
/////////////////////////////////////////

void AvmTestCaseUtils::getInitialParameters(
		const ExecutionContext & tpEC, InstanceOfData::Table & initParamVariables)
{
	const ParametersRuntimeForm & paramRF =
			tpEC.getExecutionData().getParametersRuntimeForm();

	TableOfInstanceOfData::const_raw_iterator itParam = paramRF.getParameters().begin();
	TableOfInstanceOfData::const_raw_iterator endParam = paramRF.getParameters().end();
	for( avm_offset_t offset = 0 ; itParam != endParam ; ++itParam , ++offset)
	{
		if( (itParam->getNameID() != PropertyPart::VAR_ID_TIME_INITIAL)
			&& (itParam->getNameID() != PropertyPart::VAR_ID_DELTA_TIME_INITIAL)
			&& itParam->getModifier().hasNatureParameter() )
		{
//AVM_OS_DEBUG << "ParamVariable : " << itParam->getFullyQualifiedNameID() << std::endl;

			initParamVariables.append( *itParam );
		}
	}
}


const BF & AvmTestCaseUtils::newfreshDurationParamOfEC(
		const ExecutionContext & anEC)
{
	const BF & deltaTimeValue = anEC.getExecutionData().getDeltaTimeValue();
	if( deltaTimeValue.is< InstanceOfData >() )
	{
		return( deltaTimeValue );
	}
	else if( anEC.hasIOElementTrace() )
	{
		AVM_OS_CERR << "Unexpected " << anEC.str()
				<< " without elapsed time< " << deltaTimeValue.str()
				<< " > as newfresh parameter !" << std::endl;
	}

	return BF::REF_NULL;
}

const BF & AvmTestCaseUtils::newfreshDurationParamFromEC(
		const ExecutionContext & tpEC)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		const BF & deltaTimeValue = newfreshDurationParamOfEC(*aChildEC);
		if( deltaTimeValue.valid() )
		{
			return( deltaTimeValue );
		}
	}

	return BF::REF_NULL;
}


void AvmTestCaseUtils::newfreshDurationParamsOfEC(
		const ExecutionContext & anEC, InstanceOfData::Table & freshParameters)
{
	const BF & deltaTimeValue = newfreshDurationParamOfEC(anEC);
	if( deltaTimeValue.valid() )
	{
		freshParameters.add_unique( deltaTimeValue );
	}
}

void AvmTestCaseUtils::newfreshDurationParamsFromEC(
		const ExecutionContext & tpEC, InstanceOfData::Table & freshParameters)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		newfreshDurationParamsOfEC(*aChildEC, freshParameters);
	}
}


void AvmTestCaseUtils::newfreshOutputParamsOfEC(
		const ExecutionContext & anEC, InstanceOfData::Table & freshParameters)
{
	if( anEC.hasIOElementTrace() )
	{
		const BF & ioTrace = anEC.getIOElementTrace();
		const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
		if( comTrace.valid() && StatementTypeChecker::isOutput(comTrace) )
		{
			auto itArg = comTrace.getOperands().begin();
			const auto & endArg = comTrace.getOperands().end();
			for( ++itArg ; itArg != endArg ; ++itArg)
			{
				AVM_OS_ASSERT_FATAL_ERROR_EXIT(
						(*itArg).is< InstanceOfData >() )
						<< "Unexpected " << anEC.str()
						<< " with an output with arg< "
						<< (*itArg).str()
						<< " > as newfresh parameter !" << std::endl
						<< SEND_EXIT;

				freshParameters.add_unique( *itArg );
			}
		}
	}
}

void AvmTestCaseUtils::newfreshOutputParamsFromEC(
		const ExecutionContext & tpEC, InstanceOfData::Table & freshParameters)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		newfreshOutputParamsOfEC(*aChildEC, freshParameters);
	}
}


void AvmTestCaseUtils::newfreshInoutParamsOfEC(
		const ExecutionContext & anEC, InstanceOfData::Table & freshParameters)
{
	if( anEC.hasIOElementTrace() )
	{
		const BF & ioTrace = anEC.getIOElementTrace();
		const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
		if( comTrace.valid() && StatementTypeChecker::isCommunication(comTrace) )
		{
			auto itArg = comTrace.getOperands().begin();
			const auto & endArg = comTrace.getOperands().end();
			for( ++itArg ; itArg != endArg ; ++itArg)
			{
				AVM_OS_ASSERT_FATAL_ERROR_EXIT(
						(*itArg).is< InstanceOfData >() )
						<< "Unexpected " << anEC.str()
						<< " with an output with arg< "
						<< (*itArg).str()
						<< " > as newfresh parameter !" << std::endl
						<< SEND_EXIT;

				freshParameters.add_unique( *itArg );
			}
		}
	}
}

void AvmTestCaseUtils::newfreshInoutParamsFromEC(
		const ExecutionContext & tpEC, InstanceOfData::Table & freshParameters)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		newfreshInoutParamsOfEC(*aChildEC, freshParameters);
	}
}


void AvmTestCaseUtils::newfreshTraceParamsFromEC(const ExecutionContext & tpEC,
		InstanceOfData::Table & tcInoutParams, InstanceOfData::Table & tcClockParams)
{
	const ExecutionContext * pEC = & tpEC;
	while( pEC != nullptr )
	{
		const BF & deltaTimeValue = pEC->getExecutionData().getDeltaTimeValue();
		if( deltaTimeValue.is< InstanceOfData >() )
		{
			tcClockParams.add_unique( deltaTimeValue );
		}
		else if( pEC->hasIOElementTrace() )
		{
			AVM_OS_CERR << "Unexpected " << pEC->str()
					<< " without elapsed time< " << deltaTimeValue.str()
					<< " > as testcase parameter !" << std::endl;
		}

		comParametersFromEC( *pEC, tcInoutParams);

		pEC = pEC->getContainer();
	}
}

////////////////////////////////////////////////////////////////////////////
// CONDITION / GUARD SIMPLIFICATION
////////////////////////////////////////////////////////////////////////////

static bool extractUnquantifiedConditions(const AvmCode & aCode,
		const AvmCode::OperandCollectionT & boundVars,
		AvmCode::OperandCollectionT & quantifiedOperands,
		AvmCode::OperandCollectionT & unquantifiedOperands)
{
	BFList listOfVar;
	for( const auto & itOperand : aCode.getOperands() )
	{
		listOfVar.clear();
		ExpressionFactory::collectAnyVariable(itOperand, listOfVar);
		bool isQuantified = false;

		for( const auto & boundVar : boundVars )
		{
			for( const auto & itVar : listOfVar )
			{
				if( NamedElement::extractNameID(boundVar.str()) ==
						NamedElement::extractNameID(itVar.str()) )
				{
//AVM_OS_DEBUG << "found bound var " << itVar.str() << " in operand :> " << itOperand.str() << std::endl;
					isQuantified = true;
					break;
				}
			}
			if( isQuantified ) break;
		}
		if( isQuantified )
		{
			quantifiedOperands.append(itOperand);
		}
		else
		{
//AVM_OS_DEBUG << "Unquantified :> " << itOperand.str() << std::endl;
			unquantifiedOperands.append(itOperand);
		}
	}
	return unquantifiedOperands.nonempty();
}

BF AvmTestCaseUtils::existsExpr(const AvmCode::OperandCollectionT & boundVars,
		const BF & formula, bool enableSimplification)
{
	if( enableSimplification )
	{
		if( formula.is< AvmCode >() )
		{
			const AvmCode & aCode = formula.to< AvmCode >();
			if( aCode.isOpCode(AVM_OPCODE_AND) || aCode.isOpCode(AVM_OPCODE_OR) )
			{
				AvmCode::OperandCollectionT quantifiedOperands;
				AvmCode::OperandCollectionT unquantifiedOperands;
//AVM_OS_DEBUG << "Try to simplify " << ExpressionConstructor::existsExpr(boundVars, formula).str() << std::endl;
				if( extractUnquantifiedConditions(aCode, boundVars,
						quantifiedOperands, unquantifiedOperands) )
				{
					if( quantifiedOperands.empty() )
					{
						return formula;
					}
					else if( aCode.isOpCode(AVM_OPCODE_AND) )
					{
						unquantifiedOperands.append(
								ExpressionConstructor::existsExpr(boundVars,
										ExpressionConstructor::andExpr(
												quantifiedOperands
										)
								)
						);
//AVM_OS_DEBUG << "Result " << ExpressionConstructor::andExpr(unquantifiedOperands).str() << std::endl;
						return ExpressionConstructor::andExpr(unquantifiedOperands);
					}
					else // if( aCode.isOpCode(AVM_OPCODE_OR) )
					{
						unquantifiedOperands.append(
								ExpressionConstructor::existsExpr(boundVars,
										ExpressionConstructor::orExpr(
												quantifiedOperands
										)
								)
						);
//AVM_OS_DEBUG << "Result " << ExpressionConstructor::orExpr(unquantifiedOperands).str() << std::endl;
						return ExpressionConstructor::orExpr(unquantifiedOperands);
					}
				}
			}
		}
	}

	return ExpressionConstructor::existsExpr(boundVars, formula);
}


BF AvmTestCaseUtils::forallExpr(const AvmCode::OperandCollectionT & boundVars,
		const BF & formula, bool enableSimplification)
{
	if( enableSimplification )
	{
		if( formula.is< AvmCode >() )
		{
			const AvmCode & aCode = formula.to< AvmCode >();
			if( aCode.isOpCode(AVM_OPCODE_AND) || aCode.isOpCode(AVM_OPCODE_OR) )
			{
				AvmCode::OperandCollectionT quantifiedOperands;
				AvmCode::OperandCollectionT unquantifiedOperands;

//AVM_OS_DEBUG << "Try to simplify " << ExpressionConstructor::forallExpr(boundVars, formula).str() << std::endl;
				if( extractUnquantifiedConditions(aCode, boundVars,
						quantifiedOperands, unquantifiedOperands) )
				{
					if( quantifiedOperands.empty() )
					{
						return formula;
					}
					else if( aCode.isOpCode(AVM_OPCODE_AND) )
					{
						unquantifiedOperands.append(
								ExpressionConstructor::forallExpr(boundVars,
										ExpressionConstructor::andExpr(
												quantifiedOperands
										)
								)
						);
						return ExpressionConstructor::andExpr(unquantifiedOperands);
					}
					else // if( aCode.isOpCode(AVM_OPCODE_OR) )
					{
						unquantifiedOperands.append(
								ExpressionConstructor::forallExpr(boundVars,
										ExpressionConstructor::orExpr(
												quantifiedOperands
										)
								)
						);
						return ExpressionConstructor::orExpr(unquantifiedOperands);
					}
				}
			}
		}
	}

	return ExpressionConstructor::forallExpr(boundVars, formula);
}


bool AvmTestCaseUtils::containseParameter(const BF & condition, const BF & aParameter)
{
	BFList listOfVar;
	BFList listOfBoundVar;
	ExpressionFactory::collectsAnyFreeVariable(condition, listOfBoundVar, listOfVar);
	for( const auto & itVar : listOfVar )
	{
		if( NamedElement::extractNameID(aParameter.str()) ==
				NamedElement::extractNameID(itVar.str()) )
		{
			return true;
		}
	}

	return false;
}

bool AvmTestCaseUtils::containsSomeParameter(const BF & condition,
		const std::vector<BF> & newfreshParamsAtHeight) {
	BFList listOfVar;
	BFList listOfBoundVar;
	ExpressionFactory::collectsAnyFreeVariable(condition, listOfBoundVar, listOfVar);

	for( const auto & itVar : listOfVar )
	{
		for( const auto & paramAtHeight : newfreshParamsAtHeight )
		{
			if( NamedElement::extractNameID(paramAtHeight.str()) ==
					NamedElement::extractNameID(itVar.str()) )
			{
				return true;
			}
		}
	}

	return false;
}

bool AvmTestCaseUtils::containsSomeParameter(
		AvmCode::OperandCollectionT & guardClauses,
		const std::vector<BF> & newfreshParamsAtHeight) {
	BFList listOfVar;
	BFList listOfBoundVar;
	for( const auto & itClause : guardClauses )
	{
		listOfVar.clear();
		listOfBoundVar.clear();
		ExpressionFactory::collectsAnyFreeVariable(itClause, listOfBoundVar, listOfVar);

		for( const auto & itVar : listOfVar )
		{
			for( const auto & paramAtHeight : newfreshParamsAtHeight )
			{
				if( NamedElement::extractNameID(paramAtHeight.str()) ==
						NamedElement::extractNameID(itVar.str()) )
				{
					return true;
				}
			}
		}
	}

	return false;
}



} /* namespace sep */

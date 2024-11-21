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

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/PropertyPart.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionContext.h>


namespace sep
{


void AvmTestCaseUtils::getTestPurposeTrace(const ExecutionContext & anEC,
		ExecutionContext::ListOfConstPtr & testPurposeTrace)
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

void AvmTestCaseUtils::newfreshDurationVarsFromEC(const ExecutionContext & tpEC,
		const Machine & tcMachine, Variable::Table & tcVars)
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
				tcVars.add_unique(varElapsedTime);
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
}


void AvmTestCaseUtils::newfreshInputVarsFromEC(const ExecutionContext & tpEC,
		const Machine & tcMachine, Variable::Table & tcVars)
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

			if( StatementTypeChecker::isInput(comTrace) )
			{
				BF tcPort;
				getComPortVariableArguments(tcMachine, comTrace, tcPort, tcVars);
			}
		}
	}
}

void AvmTestCaseUtils::newfreshOutputVarsFromEC(const ExecutionContext & tpEC,
		const Machine & tcMachine, Variable::Table & tcVars)
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

			if( StatementTypeChecker::isOutput(comTrace) )
			{
				BF tcPort;
				getComPortVariableArguments(tcMachine, comTrace, tcPort, tcVars);
			}
		}
	}
}

void AvmTestCaseUtils::newfreshInoutVarsFromEC(const ExecutionContext & tpEC,
		const Machine & tcMachine, Variable::Table & tcVars)
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

			BF tcPort;
			getComPortVariableArguments(tcMachine, comTrace, tcPort, tcVars);
		}
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


const BF & AvmTestCaseUtils::newfreshDurationParamFromEC(
		const ExecutionContext & tpEC)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		const BF & deltaTimeValue = aChildEC->getExecutionData().getDeltaTimeValue();
		if( deltaTimeValue.is< InstanceOfData >() )
		{
			return( deltaTimeValue );
		}
		else if( aChildEC->hasIOElementTrace() )
		{
			AVM_OS_CERR << "Unexpected " << aChildEC->str()
					<< " without elapsed time< " << deltaTimeValue.str()
					<< " > as newfresh parameter !" << std::endl;
		}
	}

	return BF::REF_NULL;
}


void AvmTestCaseUtils::newfreshDurationParamsFromEC(
		const ExecutionContext & tpEC, InstanceOfData::Table & freshParameters)
{
	for( const auto & aChildEC : tpEC.getChildContexts() )
	{
		const BF & deltaTimeValue = aChildEC->getExecutionData().getDeltaTimeValue();
		if( deltaTimeValue.is< InstanceOfData >() )
		{
			freshParameters.add_unique( deltaTimeValue );
		}
		else if( aChildEC->hasIOElementTrace() )
		{
			AVM_OS_CERR << "Unexpected " << aChildEC->str()
					<< " without elapsed time< " << deltaTimeValue.str()
					<< " > as newfresh parameter !" << std::endl;
		}
	}
}

void AvmTestCaseUtils::newfreshInoutParamsFromEC(
		const ExecutionContext & tpEC, InstanceOfData::Table & freshParameters)
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

			if( StatementTypeChecker::isCommunication(comTrace) )
			{
				auto itArg = comTrace.getOperands().begin();
				const auto & endArg = comTrace.getOperands().end();
				for( ++itArg ; itArg != endArg ; ++itArg)
				{
					AVM_OS_ASSERT_FATAL_ERROR_EXIT(
							(*itArg).is< InstanceOfData >() )
							<< "Unexpected " << tpEC.str()
							<< " with an output with arg< "
							<< (*itArg).str()
							<< " > as newfresh parameter !" << std::endl
							<< SEND_EXIT;

					freshParameters.add_unique( *itArg );
				}
			}
		}
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



} /* namespace sep */

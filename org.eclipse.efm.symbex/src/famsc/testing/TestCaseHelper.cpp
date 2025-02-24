/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 Sep. 2017
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include <computer/ExecutionDataFactory.h>
#include <computer/primitive/AvmCommunicationFactory.h>
#include <famcore/queue/ExecutionQueue.h>
#include <famsc/testing/TestCaseHelper.h>
#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/symbol/Symbol.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/infrastructure/System.h>
#include <fml/infrastructure/Variable.h>
#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/InteractionPart.h>
#include <fml/infrastructure/ComPoint.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionContextFlags.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeQuery.h>
#include <fml/type/TypeManager.h>
#include <fml/trace/TraceFactory.h>
#include <sew/Configuration.h>
#include <sew/SymbexControllerRequestManager.h>
#include <sew/Workflow.h>
#include <time.h>

#include <solver/api/SolverFactory.h>
using namespace std;

namespace sep
{

////////////////////////////////////////////////////////////////////////////
// FILTERING API
////////////////////////////////////////////////////////////////////////////

InstanceOfPort * TestCaseHelper::getIOPort(const BF & ioTrace)
{
	if( ioTrace.invalid() )
	{
		return( nullptr );
	}
	else if( ioTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf = ioTrace.to< ExecutionConfiguration >();

		if( aConf.getCode().is< AvmCode >() )
		{
			const AvmCode & ioCode = aConf.getCode().to< AvmCode >();

			if( ioCode.first().is< InstanceOfPort >() ) // Verify whether the first element of ioCode is a port
			{
				return( ioCode.first().to_ptr< InstanceOfPort >() );
			}

			return( nullptr );
		}
		else if( aConf.getCode().is< InstanceOfPort >() )
		{
			return( aConf.getCode().to_ptr< InstanceOfPort >() );
		}
	}
	else if( ioTrace.is< AvmCode >() )
	{
		InstanceOfPort * aPort;
		// this loop will continue until it finds a port, if it is the case, it returns the port
		for( const auto & itOperand : ioTrace.to< AvmCode >().getOperands() )
		{
			aPort = getIOPort( itOperand );
			if( aPort != nullptr )
			{
				return( aPort );
			}
		}
	}

	return( nullptr );

}
// This function checks the deterministic in symbolic execution of TIOSTS
bool TestCaseHelper::checkDeterministic()
{
	bool deterministic = true;

	for ( auto & anEC : mListOfECWithOutputPort )
	{
		for ( auto & anOtherEC : mListOfECWithOutputPort )
		{
			BF conjunctionOfConditions = anEC->getNodeCondition();

			if ( anEC != anOtherEC )
			{
				if ( getIOPort(anEC->getIOElementTrace())->getNameID() ==
					 getIOPort(anOtherEC->getIOElementTrace())->getNameID() )
				{

					AvmCode::OperandCollectionT termsOfPortEC =
							getTermListOfPort( anEC->getIOElementTrace() );

					AvmCode::OperandCollectionT termsOfPortOtherEC =
							getTermListOfPort( anOtherEC->getIOElementTrace() );

					BF equalityOnFreshVars = ExpressionConstant::BOOLEAN_TRUE;

					BF singleEQualityOnFreshVar;

					if ( termsOfPortEC.nonempty() )
					{
						if ( termsOfPortOtherEC.nonempty() )
						{
							auto itNewFresh = termsOfPortEC.begin();

							for ( const auto & itParam : termsOfPortOtherEC )
							{
								singleEQualityOnFreshVar = ExpressionConstructor::newExpr(
										OperatorManager::OPERATOR_EQ, (*itNewFresh), itParam);

								equalityOnFreshVars = ExpressionConstructor::andExpr(
										singleEQualityOnFreshVar,
										equalityOnFreshVars);

								// Next element
								++itNewFresh;
							}
						}
					}
					else
					{
						equalityOnFreshVars = ExpressionConstant::BOOLEAN_TRUE;
					}

					conjunctionOfConditions = ExpressionConstructor::andExpr(
							conjunctionOfConditions,
							equalityOnFreshVars );

					conjunctionOfConditions = ExpressionConstructor::andExpr(
							conjunctionOfConditions,
							anOtherEC->getNodeCondition() );

					if ( SolverFactory::isStrongSatisfiable( conjunctionOfConditions ) )
					{
						deterministic = false;
						return deterministic;
					}
				}
			}
		}
	}

	return deterministic;
}

const RuntimeID & TestCaseHelper::getIORuntimeID(const BF & ioTrace)
{
	if( ioTrace.invalid() )
	{
		return( RuntimeID::REF_NULL );
	}
	else if( ioTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf = ioTrace.to< ExecutionConfiguration >();

		if( aConf.getCode().is< AvmCode >() )
		{
			const AvmCode & ioCode = aConf.getCode().to< AvmCode >();

			if( ioCode.first().is< InstanceOfPort >() ) // Verify whether the first element of ioCode is a port
			{
				return( aConf.getRuntimeID() );
			}

			return( RuntimeID::REF_NULL );
		}
		else if( aConf.getCode().is< InstanceOfPort >() )
		{
			return( aConf.getRuntimeID() );
		}
	}
	else if( ioTrace.is< AvmCode >() )
	{
		// this loop will continue until it finds a port, if it is the case, it returns the port
		for( const auto & itOperand : ioTrace.to< AvmCode >().getOperands() )
		{
			const RuntimeID & RID = getIORuntimeID( itOperand );
			if( RID.valid() )
			{
				return( RID );
			}
		}
	}

	return( RuntimeID::REF_NULL );

}


InstanceOfPort * TestCaseHelper::getIOPort(const BF & ioTrace, RuntimeID & aRID)
{
	if( ioTrace.invalid() )
	{
		aRID = RuntimeID::REF_NULL;
		return( nullptr );
	}
	else if( ioTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf = ioTrace.to< ExecutionConfiguration >();

		if( aConf.getCode().is< AvmCode >() )
		{
			const AvmCode & ioCode = aConf.getCode().to< AvmCode >();

			if( ioCode.first().is< InstanceOfPort >() ) // Verify whether the first element of ioCode is a port
			{
				aRID = aConf.getRuntimeID();
				return( ioCode.first().to_ptr< InstanceOfPort >() );
			}

			aRID = RuntimeID::REF_NULL;
			return( nullptr );
		}
		else if( aConf.getCode().is< InstanceOfPort >() )
		{
			return( aConf.getCode().to_ptr< InstanceOfPort >() );
		}
	}
	else if( ioTrace.is< AvmCode >() )
	{
		InstanceOfPort * aPort;
		// this loop will continue until it finds a port, if it is the case, it returns the port
		for( const auto & itOperand : ioTrace.to< AvmCode >().getOperands() )
		{
			aPort = getIOPort( itOperand , aRID);
			if( aPort != nullptr )
			{
				return( aPort );
			}
		}
	}

	aRID = RuntimeID::REF_NULL;
	return( nullptr );

}


void TestCaseHelper::keepDelayOfTransition(const BF & ioTrace, BFList & newFreshTrace)
{
	if ( ioTrace.invalid() )
	{

	}
	else if ( ioTrace.is<ExecutionConfiguration>() )
	{
		const ExecutionConfiguration & aConf = ioTrace.to<ExecutionConfiguration>();

		if ( aConf.getCode().is<AvmCode>() )
		{
			const AvmCode & ioCode = aConf.getCode().to< AvmCode >();

			if( ioCode.isOpCode(AVM_OPCODE_ASSIGN_NEWFRESH) )
			{
				newFreshTrace.append( ioTrace ) ;
			}
		}
	}
	else if ( ioTrace.is<AvmCode>() )
	{
		const AvmCode & ioCode = ioTrace.to< AvmCode >();

		if( ioCode.isOpCode(AVM_OPCODE_ASSIGN_NEWFRESH) )
		{
			newFreshTrace.append( ioTrace ) ;
		}
		else if( ioTrace.is< AvmCode >() )
		{
			const AvmCode & aCode = ioTrace.to< AvmCode >();

			for( const auto & itOperand : aCode.getOperands() )
			{
				if ( (itOperand.to< ExecutionConfiguration >().getCode().to< AvmCode >()).first().is< InstanceOfData >() )
				{
					keepDelayOfTransition( itOperand, newFreshTrace );

				}
			}
		}
	}
}


BF TestCaseHelper::getDelayOfTransition(const BF & ioTrace)
{
	BF delay;

	if( ioTrace.invalid() )
	{

	}
	else if( ioTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf = ioTrace.to< ExecutionConfiguration >();

		if( aConf.getCode().is< AvmCode >() )
		{
			const AvmCode & ioCode = aConf.getCode().to< AvmCode >();

			if( ioCode.second().is< InstanceOfData >() )
			{
				delay = ioCode.second();
			}
		}
	}
	else if( ioTrace.is< AvmCode >() )
	{
		const AvmCode & aCode = ioTrace.to< AvmCode >();

//		for( const auto & itOperand : aCode.getOperands() )
//		{
		if ( aCode.hasOperand() )
		{
			const BF & anOperand = aCode.getOperands().getArg2();

			if (anOperand.is<ExecutionConfiguration>())
			{
				if ( (anOperand.to< ExecutionConfiguration >()
						.getCode().to< AvmCode >()).first().is< InstanceOfData >() )
				{
					delay = getDelayOfTransition( anOperand );
					return delay;
				}
			}
		}
//		}
	}

	return( delay );
}


BFList TestCaseHelper::getParamsListOfPort(const BF & ioTrace)
{
	BFList paramsList;
	if( ioTrace.invalid() )
	{

	}
	else if( ioTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf = ioTrace.to< ExecutionConfiguration >();

		if( aConf.getCode().is< AvmCode >() )
		{
			const AvmCode & ioCode = aConf.getCode().to< AvmCode >();

			if( ioCode.first().is< InstanceOfPort >() ) // Verify whether the first element of ioCode is a port
			{
				for ( std::size_t index = 1; index < ioCode.size(); ++index )
				{
					if( (not ioCode.operand(index).isBuiltinValue())
						&& ExpressionTypeChecker::isClockTime(ioCode.operand(index)) )
//					if ( ioCode.operand(index).is<InstanceOfData>()
//							&& ioCode.operand(index).to<InstanceOfData>().hasTypedClockTime() )
					{
						// NOTHING
						AVM_OS_DEBUG << "index : " << index << " AND InstanceOfData : " << ioCode.operand(index).str() << std::endl;//TODO
					}
					else
					{
						paramsList.append( ioCode.operand(index) );
					}
				}
			}
		}
	}
	else if( ioTrace.is< AvmCode >() )
	{
		const AvmCode & aCode = ioTrace.to< AvmCode >();

		for( const auto & itOperand : aCode.getOperands() )
		{
			if ( (itOperand.to< ExecutionConfiguration >().getCode().to< AvmCode >()).first().is< InstanceOfPort >() )
			{
				paramsList = getParamsListOfPort( itOperand );
				return paramsList;
			}
		}
	}

	return( paramsList );
}


//BFList TestCaseHelper::getParamsListOfPortForInternal(const BF & ioTrace)
//{
//	BFList paramsList;
//	if( ioTrace.invalid() )
//	{
//
//	}
//	else if( ioTrace.is< ExecutionConfiguration >() )
//	{
//		const ExecutionConfiguration & aConf = ioTrace.to< ExecutionConfiguration >();
//
//		if( aConf.getCode().is< AvmCode >() )
//		{
//			const AvmCode & ioCode = aConf.getCode().to< AvmCode >();
//
//			if( ioCode.first().is< InstanceOfPort >() ) // Verify whether the first element of ioCode is a port
//			{
//				for ( std::size_t index = 1; index < ioCode.size() - 1; ++index )
//				{
//					paramsList.append( ioCode.operand(index) );
//				}
//			}
//		}
//	}
//	else if( ioTrace.is< AvmCode >() )
//	{
//		const AvmCode & aCode = ioTrace.to< AvmCode >();
//
//		for( const auto & itOperand : aCode.getOperands() )
//		{
//			if ( (itOperand.to< ExecutionConfiguration >().getCode().to< AvmCode >()).first().is< InstanceOfPort >() )
//			{
//				paramsList = getParamsListOfPortForInternal( itOperand );
//				return paramsList;
//			}
//		}
//	}
//
//	return( paramsList );
//}

void TestCaseHelper::getTimeVarsNonInstantiatedInGuard(const BF & bigFormula,
		AvmCode::OperandCollectionT & listOfVarsNonInstantiated)
{
	bool newVar = true;

	if ( bigFormula.isExpression() )
	{
		if( bigFormula.is< AvmCode >() )
		{
			const AvmCode & formulas = bigFormula.to< AvmCode >();

			for( const auto & operand : formulas.getOperands() )
			{
				if ( operand.is< InstanceOfData >() )
				{
					for ( const auto & var : listOfVarsNonInstantiated )
					{
						if ( var != operand )
						{
							newVar = true;
						}
						else
						{
							newVar = false;
							break;
						}
					}

					if ( newVar )
					{
						listOfVarsNonInstantiated.append( operand );
					}
				}
				else
				{
					getTimeVarsNonInstantiatedInGuard( operand, listOfVarsNonInstantiated );
				}
			}
		}
	}
	else
	{

	}
}

void TestCaseHelper::getDataVarsNonInstantiatedInGuard(const BF & bigFormula,
		AvmCode::OperandCollectionT & listOfVarsNonInstantiated)
{
	bool newVar = true;

	if ( bigFormula.isExpression() )
	{
		if( bigFormula.is< AvmCode >() )
		{
			const AvmCode & formulas = bigFormula.to< AvmCode >();

			for( const auto & operand : formulas.getOperands() )
			{
				if ( operand.is< InstanceOfData >() )
				{
					for ( const auto & var : listOfVarsNonInstantiated )
					{
						if ( var != operand )
						{
							newVar = true;
						}
						else
						{
							newVar = false;
							break;
						}
					}

					if ( newVar )
					{
						listOfVarsNonInstantiated.append( operand );
					}
				}
				else
				{
					getDataVarsNonInstantiatedInGuard( operand, listOfVarsNonInstantiated );
				}
			}
		}
	}
	else
	{
		// NOTHING
	}
}

BFList TestCaseHelper::getBSenInQuestion(const BFList & BSen,
		AvmCode::OperandCollectionT & listOfVarsNonInstantiated)
{
	BFList bSenFormulas;

	for( const auto & atomicFormula : BSen )
	{
		const AvmCode & formulaAVM = atomicFormula.to< AvmCode >();

		for( const auto & operand : formulaAVM.getOperands() )
		{
			if ( operand.is< InstanceOfData >() )
			{
				for ( const auto & var : listOfVarsNonInstantiated )
				{
					// find formulas which are concerne with variables non instantiated
					// and add it to bSenFormulas. Then, return bSenFormulas.
					if ( var == operand )
					{
						bSenFormulas.append(atomicFormula);
					}
				}
			}
			else
			{
				const AvmCode & term = operand.to< AvmCode >();

				for( const auto & operand : term.getOperands() )
				{
					if ( operand.is< InstanceOfData >() )
					{
						for ( const auto & var : listOfVarsNonInstantiated )
						{
							// find formulas which are concerne with variables non instantiated
							// and add it to bSenFormulas. Then, return bSenFormulas.
							if ( var == operand )
							{
								bSenFormulas.append(atomicFormula);
							}
						}
					}
				}
			}
		}
	}

	return bSenFormulas;
}

BF TestCaseHelper::constructPtCwithoutInobservableDelays (
		BF & newAtomicFormula, const BF & anExpression )
{
	BF newPathTimedCondition;

	bool keepDelay;

	const AvmCode & avmCodeAnExpression = anExpression.to< AvmCode >();

	newAtomicFormula = BF::REF_NULL;


	if ( anExpression == ExpressionConstant::BOOLEAN_TRUE )
	{
		newPathTimedCondition = ExpressionConstant::BOOLEAN_TRUE;
	}
	else
	{
		for ( auto & itOperand : avmCodeAnExpression.getOperands() )
		{
			keepDelay = true;

			if ( not itOperand.isExpression() )
			{
				if ( itOperand.is<InstanceOfData>() )
				{
					for ( const auto & delay : mListOfInobservableDelays )
					{
						if ( itOperand == delay )
						{
							keepDelay = false;
							break;
						}
					}
				}

				if ( keepDelay )
				{
					if ( newAtomicFormula == BF::REF_NULL )
					{
						newAtomicFormula = ExpressionConstructor::newExpr(
								itOperand );
					}
					else
					{
						if ( avmCodeAnExpression.getOperator() == OperatorManager::OPERATOR_PLUS )
						{
							newAtomicFormula = ExpressionConstructor::addExpr(
									newAtomicFormula,
									itOperand );
						}
						else if ( avmCodeAnExpression.getOperator() == OperatorManager::OPERATOR_GT )
						{
							newAtomicFormula = ExpressionConstructor::gtExpr(
									newAtomicFormula,
									itOperand );
						}
						else if ( avmCodeAnExpression.getOperator() == OperatorManager::OPERATOR_GTE )
						{
							newAtomicFormula = ExpressionConstructor::gteExpr(
									newAtomicFormula,
									itOperand );
						}
						else if ( avmCodeAnExpression.getOperator() == OperatorManager::OPERATOR_LT )
						{
							newAtomicFormula = ExpressionConstructor::ltExpr(
									newAtomicFormula,
									itOperand );
						}
						else if ( avmCodeAnExpression.getOperator() == OperatorManager::OPERATOR_LTE )
						{
							newAtomicFormula = ExpressionConstructor::lteExpr(
									newAtomicFormula,
									itOperand );
						}
						else if ( avmCodeAnExpression.getOperator() == OperatorManager::OPERATOR_EQ )
						{
							newAtomicFormula = ExpressionConstructor::eqExpr(
									newAtomicFormula,
									itOperand );
						}
					}
				}
			}
			else
			{
				constructPtCwithoutInobservableDelays( newAtomicFormula, itOperand );

				if ( newPathTimedCondition != BF::REF_NULL )
				{
					if ( avmCodeAnExpression.getOperator() == OperatorManager::OPERATOR_AND )
					{
						newPathTimedCondition = ExpressionConstructor::andExpr(
								newPathTimedCondition,
								newAtomicFormula );
					}
					else if ( avmCodeAnExpression.getOperator() == OperatorManager::OPERATOR_OR )
					{
						newPathTimedCondition = ExpressionConstructor::orExpr(
								newPathTimedCondition,
								newAtomicFormula );
					}
				}
			}

			if ( newPathTimedCondition == BF::REF_NULL )
			{
				if ( newAtomicFormula.isExpression() )
				{
					newPathTimedCondition = newAtomicFormula;
				}
			}
		}
	}

	return newPathTimedCondition;
}


AvmCode::OperandCollectionT TestCaseHelper::getTermListOfPort(const BF & ioTrace)
{
	AvmCode::OperandCollectionT varsList;
	if( ioTrace.invalid() )
	{

	}
	else if( ioTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf = ioTrace.to< ExecutionConfiguration >();

		if( aConf.getCode().is< AvmCode >() )
		{
			const AvmCode & ioCode = aConf.getCode().to< AvmCode >();

			if( ioCode.first().is< InstanceOfPort >() ) // Verify whether the first element of ioCode is a port
			{
				for ( std::size_t index = 1; index < ioCode.size(); ++index ){

					varsList.append( ioCode.operand(index) );
				}
			}
		}
	}
	else if( ioTrace.is< AvmCode >() )
	{
		const AvmCode & aCode = ioTrace.to< AvmCode >();

		for( const auto & itOperand : aCode.getOperands() )
		{
			if ( (itOperand.to< ExecutionConfiguration >().getCode().to< AvmCode >()).first().is< InstanceOfPort >() )
			{
				varsList = getTermListOfPort( itOperand );
				return varsList;
			}
		}
	}


	return( varsList );

}

void TestCaseHelper::setIOMirroring(ExecutionContext & anEC)
{
	BF ioMirrorCode = getIOMirroring(anEC.getIOElementTrace());

//AVM_OS_DEBUG << "Mirror:" << ioMirrorCode.str() << std::endl;

	anEC.getwExecutionData().setIOElementTrace( ioMirrorCode );
}

BF TestCaseHelper::getIOMirroring(const BF & ioTrace)
{
	if( ioTrace.invalid() )
	{
		return( BF::REF_NULL );
	}
	else if( ioTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf =
				ioTrace.to< ExecutionConfiguration >();

		if( aConf.getCode().is< AvmCode >() )
		{
			const AvmCode & ioCode = aConf.getCode().to< AvmCode >();

			switch( ioCode.getOptimizedOpCode() )
			{
				case AVM_OPCODE_INPUT:
				{
					BFCode ioMirroCode( OperatorManager::OPERATOR_INPUT );

					ioMirroCode.append( ioCode.getOperands() );

					return( BF(new ExecutionConfiguration(aConf.getRuntimeID(), ioMirroCode)) );
				}
				case AVM_OPCODE_INPUT_ENV:
				{
					BFCode ioMirroCode( OperatorManager::OPERATOR_OUTPUT_ENV );

					ioMirroCode.append( ioCode.getOperands() );

					return( BF(new ExecutionConfiguration(aConf.getRuntimeID(), ioMirroCode)) );
				}


//				case AVM_OPCODE_INPUT_FROM:
//
//				case AVM_OPCODE_INPUT_SAVE:
//
//				// Optimized version of INPUT
//				case AVM_OPCODE_INPUT_VAR:
//				case AVM_OPCODE_INPUT_FLOW:
//				case AVM_OPCODE_INPUT_BUFFER:
//				case AVM_OPCODE_INPUT_RDV:
//				case AVM_OPCODE_INPUT_MULTI_RDV:
//				case AVM_OPCODE_INPUT_BROADCAST:
//				case AVM_OPCODE_INPUT_DELEGATE:

				case AVM_OPCODE_OUTPUT:
				{
					BFCode ioMirroCode( OperatorManager::OPERATOR_OUTPUT );

					ioMirroCode.append( ioCode.getOperands() );

					return( BF(new ExecutionConfiguration(aConf.getRuntimeID(), ioMirroCode)) );
				}
				case AVM_OPCODE_OUTPUT_ENV:
				{
					BFCode ioMirroCode( OperatorManager::OPERATOR_INPUT_ENV );

					ioMirroCode.append( ioCode.getOperands() );

					return( BF(new ExecutionConfiguration(aConf.getRuntimeID(), ioMirroCode)) );
				}

//				case AVM_OPCODE_OUTPUT_TO:
//				// Optimized version of OUTPUT
//				case AVM_OPCODE_OUTPUT_VAR:
//				case AVM_OPCODE_OUTPUT_FLOW:
//				case AVM_OPCODE_OUTPUT_BUFFER:
//				case AVM_OPCODE_OUTPUT_RDV:
//				case AVM_OPCODE_OUTPUT_MULTI_RDV:
//				case AVM_OPCODE_OUTPUT_BROADCAST:
//				case AVM_OPCODE_OUTPUT_DELEGATE:

				default:
				{
					return( ioTrace );
				}
			}
		}
		else if( aConf.getCode().is< InstanceOfData >() )
		{
			return( aConf.getCode() );
		}
	}
	else if( ioTrace.is< AvmCode >() )
	{
		const AvmCode & aCode = ioTrace.to< AvmCode >();

		BFCode mirroCode( aCode.getOperator() );

		// this loop will continue until it finds a port, if it is the case, it returns the fresh variable
		for( const auto & itOperand : aCode.getOperands() )
		{
			mirroCode.append( getIOMirroring( itOperand ) );
		}

		return( mirroCode );
	}

	return( BF::REF_NULL );

}


void TestCaseHelper::verifyIncontrollablePath(ExecutionContext * childEC)
{
	bool isIncontrollable = false;
	///////////////////////////////////////////////////////////////////////////
	// This piece of code treats controllability of path in TP
	const BF & pathConditionChildEC = childEC->getExecutionData().getPathCondition(); // get Path condition of childEC
	InstanceOfData::Table listOfVar;
	ExpressionFactory::collectVariable(pathConditionChildEC, listOfVar); // put fresh variables appeared in pathConditionChildEC
	// to listOfVar

	const ParametersRuntimeForm & paramsRF = childEC->getExecutionData().getParametersRuntimeForm(); // get fresh variables
	// from beginning to childEC

//	AVM_OS_DEBUG << "PC: " << pathConditionChildEC << std::endl;
//	for( const auto & var : listOfVar )
//	{
//		AVM_OS_DEBUG << TAB << "Fresh variables in PC : " << var.str() << std::endl;
//	}
//
//	for( const auto & param : paramsRF.getParameters() )
//	{
//		AVM_OS_DEBUG << TAB << "EC Param: " << param.str() << std::endl;
//	}

	for( const auto & var : listOfVar )
	{
		for( const auto & param : paramsRF.getParameters() )
		{
			if (var == param){
				isIncontrollable = true;
			}
		}
	}

	if (isIncontrollable)
	{
//		AVM_OS_DEBUG << TAB << "The path is not controllable" << std::endl;
	}
	else
	{
//		AVM_OS_DEBUG << TAB << "The path is controllable" << std::endl;
	}
	// end of 'controllability of path in TP'
	///////////////////////////////////////////////////////////////////////////
}


void  TestCaseHelper::getListOfOutputPorts(
		InstanceOfPort * aPort, Vector<InstanceOfPort *> & listOfPorts)
{
	///////////////////////////////////////////////////////////////////////////
	// This piece of code gets all ports of machine
	for( const auto & symbol : aPort->getContainer()->refExecutable().getPort() )
	{
		if ( symbol.rawPort()->getModifier().isDirectionOutput() ){
			listOfPorts.append( symbol.rawPort() );
		}
	}

//	for( const auto & aPort : listOfPorts )
//	{
//		AVM_OS_DEBUG << TAB << "output port in listOfPorts : " << aPort->str() << std::endl;
//	}
	// end of part for getting all ports of machine
	///////////////////////////////////////////////////////////////////////////
}


void  TestCaseHelper::getListOfInputPorts(
		InstanceOfPort * aPort, Vector<InstanceOfPort *> & listOfPorts)
{
	///////////////////////////////////////////////////////////////////////////
	// This piece of code gets all ports of machine
	for( const auto & symbol : aPort->getContainer()->refExecutable().getPort() )
	{
		if ( symbol.rawPort()->getModifier().isDirectionInput() ){
			listOfPorts.append( symbol.rawPort() );
		}
	}
}


void TestCaseHelper::verifyTreatedOutputPortForFail(
		Vector<InstanceOfPort *> & listOfPorts, InstanceOfPort * aPort)
{
	//	listOfPorts.remove( aPortInList ); // remove aPortInList from listOfPorts

	for( const auto & aPortInList : listOfPorts )
	{
		if (aPortInList == aPort){
			listOfPorts.remove( aPortInList ); // remove aPortInList from listOfPorts
		}
	}
}


void TestCaseHelper::verifyTreatedInputPortForInconc(
		Vector<InstanceOfPort *> & listOfPorts, InstanceOfPort * aPort)
{
	for( const auto & aPortInList : listOfPorts )
	{
		if (aPortInList == aPort){
			listOfPorts.remove( aPortInList ); // remove aPortInList from listOfPorts
		}
	}
}


BF TestCaseHelper::createNotEqualityOnFreshVars(
		ExecutionContext * anEC, RuntimeID portCompRID,
		AvmCode::OperandCollectionT newfreshList, InstanceOfPort * aPort)
{
	BFList paramsList = getParamsListOfPort(anEC->getIOElementTrace());

	/////////////////////////////////////////////////////
	// Create non-equality expression on fresh variables of port

	BF notEqualityOnFreshVars = ExpressionConstant::BOOLEAN_FALSE;

	BF singleExprOnFreshVar;

	if ( newfreshList.nonempty() )
	{
		if ( paramsList.nonempty() )
		{
			auto itNewFresh = newfreshList.begin();
			for ( const auto & itParam : paramsList )
			{

				singleExprOnFreshVar = ExpressionConstructor::newExpr(
						OperatorManager::OPERATOR_NEQ, (*itNewFresh), itParam);

				notEqualityOnFreshVars = ExpressionConstructor::orExpr(singleExprOnFreshVar,
						notEqualityOnFreshVars);

				// Next element
				++itNewFresh;
			}
		}
	}
	else
	{
		notEqualityOnFreshVars = ExpressionConstant::BOOLEAN_FALSE;
	}
	return notEqualityOnFreshVars;
}


BF TestCaseHelper::createEqualityOnFreshVarsForGraph(
		ExecutionContext * anEC, AvmCode::OperandCollectionT newfreshList )
{
	BFList paramsList = getParamsListOfPort(anEC->getIOElementTrace());

	/////////////////////////////////////////////////////
	// Create equality expression on fresh variables of port

	BF equalityOnFreshVars = ExpressionConstant::BOOLEAN_TRUE;

	BF singleEQualityOnFreshVar;

	if ( newfreshList.nonempty() )
	{
		if ( paramsList.nonempty() )
		{
			auto itNewFresh = newfreshList.begin();
			for ( const auto & itParam : paramsList )
			{
				singleEQualityOnFreshVar = ExpressionConstructor::newExpr(
						OperatorManager::OPERATOR_EQ, (*itNewFresh), itParam);

				equalityOnFreshVars = ExpressionConstructor::andExpr(singleEQualityOnFreshVar,
						equalityOnFreshVars);

				// Next element
				++itNewFresh;
			}
		}
	}
	else
	{
		equalityOnFreshVars = ExpressionConstant::BOOLEAN_TRUE;
	}
	return equalityOnFreshVars;
}


BF TestCaseHelper::createEqualityOnFreshVars(
		ExecutionContext * anEC, AvmCode::OperandCollectionT newfreshList,
		BFList & listInstDataVars, BFList paramsList )
{
	/////////////////////////////////////////////////////
	// Create equality expression on fresh variables of port

	BF equalityOnFreshVars = ExpressionConstant::BOOLEAN_TRUE;

	BF singleEqualityOnFreshVar;

	if ( newfreshList.nonempty() )
	{
		if ( paramsList.nonempty() )
		{
			auto itNewFresh = newfreshList.begin();
			for ( const auto & itParam : paramsList )
			{
				listInstDataVars.append( *itNewFresh );

				singleEqualityOnFreshVar = ExpressionConstructor::newExpr(
						OperatorManager::OPERATOR_EQ, (*itNewFresh), itParam);

				equalityOnFreshVars = ExpressionConstructor::andExpr(singleEqualityOnFreshVar,
						equalityOnFreshVars);

				// Next element
				++itNewFresh;
			}
		}
	}
	else
	{
		equalityOnFreshVars = ExpressionConstant::BOOLEAN_TRUE;
	}
	return equalityOnFreshVars;
}


//void TestCaseGenerationHelper::createPassInGraph(ExecutionContext * childEC,
//		ExecutionContext * parentEC, ListOfExecutionContext & listofECToAdd)
//{
//	ExecutionContext * pChildECPass;
//
//	RuntimeID portCompRID;
//	AvmCode::OperandCollectionT newfreshList;
//	InstanceOfPort * aPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
//	BFList paramList;
//
//	ENV.createNewFreshParam(portCompRID, *aPort, newfreshList, paramList);
//
//	BF equalityOnFreshVars = createEqualityOnFreshVars(
//			childEC, portCompRID, newfreshList, aPort );
//
//	pChildECPass = childEC->cloneData(parentEC, true); // clone childEC to a new execution context for verdict Pass
//
//	pChildECPass->getwFlags().setObjectiveAchievedTrace();
//
//	pChildECPass->getwExecutionData().appendParameters( paramList );
//
//	if (aPort->getwModifier().isDirectionOutput())
//	{
//		RoutingData aRoutingData = AvmCommunicationFactory::searchOutputRoutingData(
//				childEC->getExecutionData(), *aPort, portCompRID);
//
//		if (aRoutingData.valid())
//		{
//			if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
//			{
//				portCompRID = getIORuntimeID( childEC->getIOElementTrace() );
//
//				pChildECPass->getwExecutionData().setIOElementTrace(
//						BF( new ExecutionConfiguration(portCompRID,
//								StatementConstructor::newCode(
//										OperatorManager::OPERATOR_OUTPUT_ENV,
//										INCR_BF(aPort), newfreshList)) ) );
//
//			}
//			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_BUFFER_KIND )
//			{
//
//			}
//			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_MULTICAST_KIND )
//			{
//
//			}
//		}
//	}
//	else if (aPort->getwModifier().isDirectionInput())
//	{
//		RoutingData aRoutingData = AvmCommunicationFactory::searchInputRoutingData(
//						childEC->getExecutionData(), *aPort, portCompRID);
//
//		if (aRoutingData.valid())
//		{
//			if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
//			{
//				portCompRID = getIORuntimeID( childEC->getIOElementTrace() );
//
//				pChildECPass->getwExecutionData().setIOElementTrace(
//						BF( new ExecutionConfiguration(portCompRID,
//								StatementConstructor::newCode(
//										OperatorManager::OPERATOR_INPUT_ENV,
//										INCR_BF(aPort), newfreshList)) ) );
//
//			}
//			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_BUFFER_KIND )
//			{
//
//			}
//			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_MULTICAST_KIND )
//			{
//
//			}
//		}
//	}
//
//	// ajout nécessaire pour pouvoir effectuer simplement la projection
//	addRunnableTrace(pChildECPass, portCompRID);
//
//	BF nodeCondition = ExpressionConstructor::newExpr(childEC->getNodeCondition());
//
//	pChildECPass->getwExecutionData().setNodeCondition(
//			ExpressionConstructor::andExpr(
//					nodeCondition,
//					equalityOnFreshVars));
//
//	// get path condition from beginning to parent node anEC
//	BF PCParentEC = parentEC->getExecutionData().getPathCondition();
//
//	// add evaluation of guard of transition leading to pChildECPass to path condition of
//	// node anEC
//	pChildECPass->getwExecutionData().setPathCondition(
//			ExpressionConstructor::andExpr(
//					PCParentEC,
//					pChildECPass->getNodeCondition()));
//
//	listofECToAdd.append( pChildECPass );
//}


//void TestCaseGenerationHelper::createInconcInGraph(ExecutionContext * childEC,
//		ExecutionContext * parentEC, ListOfExecutionContext & listofECToAdd)
//{
//	ExecutionContext * pChildECInconc;
//
//	RuntimeID portCompRID;
//	AvmCode::OperandCollectionT newfreshList;
//	InstanceOfPort * aPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
//	BFList paramList;
//
//	BF equalityOnFreshVars = ExpressionConstant::BOOLEAN_TRUE;
//
//	ENV.createNewFreshParam(portCompRID, *aPort, newfreshList, paramList);
//
//	pChildECInconc = childEC->cloneData(parentEC, true); // clone childEC to a new execution context for verdict Inconc
//
////	ExecutionData & pChildEDInconc = pChildECInconc->getwExecutionData();
////
////	const AvmCode & scheduleCode = pChildEDInconc.getRuntimeFormOnSchedule(mINCONCRID.getPRID()).to< AvmCode >();
////	pChildEDInconc.mwsetRuntimeFormState(scheduleCode.operand(0).bfRID(), PROCESS_DISABLED_STATE);
////
////	pChildEDInconc.mwsetRuntimeFormOnScheduleAndIdle(mINCONCRID);
//
//	pChildECInconc->getwFlags().setObjectiveInconclusiveTrace();
//
//	pChildECInconc->getwExecutionData().appendParameters( paramList );
//
//	if (aPort->getwModifier().isDirectionOutput())
//	{
//		equalityOnFreshVars = createEqualityOnFreshVars(
//				childEC, portCompRID, newfreshList, aPort );
//
//		RoutingData aRoutingData = AvmCommunicationFactory::searchOutputRoutingData(
//					childEC->getExecutionData(), *aPort, portCompRID);
//
//		if (aRoutingData.valid())
//		{
//			switch ( aRoutingData.getProtocol() )
//			{
//				case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
//				{
//					portCompRID = getIORuntimeID( childEC->getIOElementTrace() );
//
//					pChildECInconc->getwExecutionData().setIOElementTrace(
//						BF( new ExecutionConfiguration(portCompRID,
//								StatementConstructor::newCode(
//										OperatorManager::OPERATOR_OUTPUT_ENV,
//										INCR_BF(aPort), newfreshList)) ) );
//
//					break;
//				}
//				case ComProtocol::PROTOCOL_BUFFER_KIND:
//				{
//					break;
//				}
//				case ComProtocol::PROTOCOL_MULTICAST_KIND:
//				{
//					break;
//				}
//				default:
//				{
//					break;
//				}
//			}
//		}
//	}
//	else if (aPort->getwModifier().isDirectionInput())
//	{
//
//	}
//
//	// ajout nécessaire pour pouvoir effectuer simplement la projection
//	addRunnableTrace(pChildECInconc, portCompRID);
//
//	BF nodeCondition = ExpressionConstructor::newExpr(childEC->getNodeCondition());
//
//	pChildECInconc->getwExecutionData().setNodeCondition(
//			ExpressionConstructor::andExpr(
//					nodeCondition,
//					equalityOnFreshVars));
//
//	// get path condition from beginning to parent node anEC
//	BF PCParentEC = parentEC->getExecutionData().getPathCondition();
//
//	// add evaluation of guard of transition leading to pChildECInconc to path condition of
//	// node anEC (that is parent of pChildECInconcOfInconc)
//	pChildECInconc->getwExecutionData().setPathCondition(
//			ExpressionConstructor::andExpr(
//					PCParentEC,
//					pChildECInconc->getNodeCondition()));
//
//	listofECToAdd.append( pChildECInconc );
//}



void TestCaseHelper::addRunnableTrace(ExecutionContext * childEC, const RuntimeID & compRID)
{
	BFList runTrace;

	const BF & activityRunArg = CONST_BF_OPERATOR(RUN);

	for( RuntimeID tmpRID = compRID ; tmpRID.valid() ; tmpRID = tmpRID.getParent() )
	{
		runTrace.push_front( BF(new ExecutionConfiguration(tmpRID, activityRunArg)) );
	}

	BFCode runCode( OperatorManager::OPERATOR_SEQUENCE );
	runCode.append( runTrace );

	childEC->getwExecutionData().setRunnableElementTrace( runCode );
}


void TestCaseHelper::createQuiescenceInGraph(ExecutionContext * childEC,
		ExecutionContext * parentEC, ListOfExecutionContext & listofECToAdd)
{
	ExecutionContext * pChildECInconcForQuiescence;

	BF nodeConditionInconcForQuiescence = childEC->getNodeCondition();

	pChildECInconcForQuiescence = childEC->cloneData(parentEC, true); // clone childEC to a new execution context for verdict Fail

	// Create new instance of ExecutionCongtextFlags to replace old flags
	////////////////////////
	const ExecutionContextFlags * flags = new ExecutionContextFlags();

	pChildECInconcForQuiescence->setFlags( * flags );
	////////////////////////

	pChildECInconcForQuiescence->getwFlags().setObjectiveAbortedTrace();

	RuntimeID portCompRID;
	InstanceOfPort * aPort = getIOPort(childEC->getIOElementTrace(), portCompRID);

	// SET IO TRACE
	pChildECInconcForQuiescence->getwExecutionData().setIOElementTrace(
			BF( new ExecutionConfiguration(portCompRID,
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_OUTPUT_ENV,
							INCR_BF(aPort))) ) );

	// ajout nécessaire pour pouvoir effectuer simplement la projection
	addRunnableTrace(pChildECInconcForQuiescence, portCompRID);

	// get path condition from beginning to parent node anEC
	BF PCParentEC = parentEC->getExecutionData().getPathCondition();

	pChildECInconcForQuiescence->getwExecutionData().setNodeCondition(nodeConditionInconcForQuiescence);

	pChildECInconcForQuiescence->getwExecutionData().setPathCondition(
			ExpressionConstructor::andExpr(
					PCParentEC,
					pChildECInconcForQuiescence->getNodeCondition()));

	listofECToAdd.append( pChildECInconcForQuiescence );
}


BFCode TestCaseHelper::resettingClockTestCase(const BF & clockTestCase)
{
	BFCode resettingClock = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, clockTestCase,
			ExpressionConstant::INTEGER_ZERO );

	return resettingClock;
}

BFCode TestCaseHelper::readingValueOfClockTestCase(const BF & clockTestCase, BF delay)
{
	BFCode readingClock = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, delay, clockTestCase);

	return readingClock;
}


///////////////////////////////////////////////////////////////////////////
// Some useful methods
//
//	getConfiguration().getSpecification(); // xlia parse model AST
//
//	getConfiguration().getExecutableSystem(); // the model after execution phase
//
//	getConfiguration().getExecutionTrace(); // Execution graph, obtained by symbolic execution (Symbolic Tree)
//
//	getExecutionQueue(); // The queue contains the next symbolic states which are not evaluated yet
//
//	getControllerUnitManager(); // Allows the access to all instanciated FAM
//
//	// getControllerUnitManager().getMainProcessor(); // module supervisor
//
//	getConfiguration().getWorkflow(); // Workflow contains user's configurations of symbolic execution
//
//	getSymbexRequestManager().postRequestStop(this); // request stop: stop symbolic execution
//
// end of useful methods
///////////////////////////////////////////////////////////////////////////

}

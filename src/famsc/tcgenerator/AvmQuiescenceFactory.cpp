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

#include "AvmQuiescenceFactory.h"
#include "AvmPathGuidedTestcaseGenerator.h"
#include "AvmTestCaseUtils.h"

#include <fml/builtin/Identifier.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/AvmCodeFactory.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/StatementTypeChecker.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>

#include <sew/Configuration.h>

#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
AvmQuiescenceFactory::AvmQuiescenceFactory(AvmPathGuidedTestcaseGenerator & aProcessor)
: mProcessor(aProcessor),
INFO_QUIESCENCE( new Identifier("QUIESCENCE") ),
INFO_NON_QUIESCENCE( new Identifier("QUIESCENCE INSATISFAIABLE") ),
mNoQuiecenceNumber( 0 ),
mQuiescenceAstPort( &( aProcessor.getConfiguration().getSpecification() ),
		"Quiescence", IComPoint::IO_PORT_NATURE,
		Modifier::PROPERTY_OUTPUT_DIRECTION ),
mQuiescencePort( new InstanceOfPort( nullptr,
		mQuiescenceAstPort, 0, 0, IComPoint::IO_PORT_NATURE) ),
mQuiescenceElementTrace( StatementConstructor::newCode(
		OperatorManager::OPERATOR_OUTPUT, mQuiescencePort) )
{
	//!! NOTHING
}

static const std::string QUIESCENCE_VAR_NAME_PASS = "#";

////////////////////////////////////////////////////////////////////////////////
// BUILD GRAPH
////////////////////////////////////////////////////////////////////////////////

void AvmQuiescenceFactory::buildGraph()
{
AVM_IF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "QUIESCENCE COMPLETION" ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )

	ExecutionContext & rootQuiescenceGraph =
			mProcessor.getConfiguration().getFirstExecutionTrace();

//!@! PREVIOUS GRAPH
	ExecutionContext * symbexGraph = rootQuiescenceGraph.cloneGraph(nullptr, true);
	mProcessor.getConfiguration().appendExecutionTrace(symbexGraph);

	if( mProcessor.mEnableGuardSimplification )
	{
		for( const auto & aChildEC : rootQuiescenceGraph.getChildContexts() )
		{
			recSimplifyQuiescenceOf(*aChildEC);
		}
	}
	else
	{
		for( const auto & aChildEC : rootQuiescenceGraph.getChildContexts() )
		{
			recQuiescenceOf(*aChildEC);
		}
	}

	if( mNoQuiecenceNumber > 0 )
	{
		ExecutionContext * saveGraph = rootQuiescenceGraph.cloneGraph(nullptr, true);
		mProcessor.getConfiguration().appendExecutionTrace(saveGraph);

		removeUnsatisfiableQuiescence(& rootQuiescenceGraph);
	}
}

////////////////////////////////////////////////////////////////////////////////
// RECURSIVE QUIESCENCE OF
////////////////////////////////////////////////////////////////////////////////

bool AvmQuiescenceFactory::recQuiescenceOf(ExecutionContext & anEC)
{
	if( anEC.hasChildContext() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "recQuiescenceOf " + anEC.str() ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		BF quiescenceCondition = ExpressionConstructor::orExpr(
				computeOutputQuiescencePathCondition(anEC),
				computeAdmissibleQuiescencePathCondition(anEC));
		bool isSatisfiable =
				SolverFactory::isStrongSatisfiable(quiescenceCondition, true);

//		if( not isSatisfiable )
//		{
//			for( const auto & aChildEC : anEC.getChildContexts()  )
//			{
//				recQuiescenceOf(*aChildEC);
//			}
//
//			return false;
//		}

		ExecutionContext * aQuiescenceEC = anEC.cloneData(& anEC, true);
		aQuiescenceEC->setHeight(1 + aQuiescenceEC->getHeight());
		aQuiescenceEC->setEvalNumber(0);

		ExecutionData & aQuiescenceED = aQuiescenceEC->getwExecutionData();
		aQuiescenceED.resetVariantBeforeEvaluation();

		aQuiescenceED.setPathCondition(
				ExpressionConstructor::andExpr(
						anEC.getPathCondition(),
						quiescenceCondition));

		aQuiescenceED.syncTimeValues(anEC.firstChildContext()->getExecutionData());

		aQuiescenceEC->getwFlags().unsetAnalysisTrace();
//		aQuiescenceEC->getwFlags().setExecutionTrivialLoopTrace();

		aQuiescenceEC->unsetInformation();
		if( isSatisfiable )
		{
			aQuiescenceEC->addInfo( mProcessor, INFO_QUIESCENCE );
		}
		else
		{
			++mNoQuiecenceNumber;
			aQuiescenceEC->addInfo( mProcessor, INFO_NON_QUIESCENCE);
			aQuiescenceEC->getwFlags().setExecutionDeadlockTrace();
		}

		const BF & deltaTimeValue = aQuiescenceED.getDeltaTimeValue();

//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
//	AVM_OS_DEBUG << "recQuiescenceOf " << anEC.str() << std::endl
//		<< "\tdeltaTimeValue : " << deltaTimeValue.str() << std::endl
//		<< "\torig-deltaTimeValue : " << anEC.firstChildContext()->getExecutionData().getDeltaTimeValue().str() << std::endl
//		<< "\tquiescenceCondition  : " << quiescenceCondition.str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

		aQuiescenceED.setIOElementTrace( BF(
				new ExecutionConfiguration( aQuiescenceED.getSystemRID(),
						mQuiescenceElementTrace, deltaTimeValue) ));

		for( const auto & aChildEC : anEC.getChildContexts()  )
		{
			recQuiescenceOf(*aChildEC);
		}

		anEC.appendChildContext(aQuiescenceEC);

		return true;
	}

	return false;
}

////////////////////////////////////////////////////////////////////////////////
// QUIESCENCE OF
////////////////////////////////////////////////////////////////////////////////

bool AvmQuiescenceFactory::quiescenceOf(ExecutionContext & anEC)
{
	if( anEC.isnotRoot() && anEC.hasChildContext() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "quiescenceOf " + anEC.str() ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		BF quiescenceCondition = ExpressionConstructor::orExpr(
				computeOutputQuiescencePathCondition(anEC),
				computeAdmissibleQuiescencePathCondition(anEC));
		bool isSatisfiable =
				SolverFactory::isStrongSatisfiable(quiescenceCondition, true);

		if( isSatisfiable )
		{
			ExecutionContext * aQuiescenceEC = anEC.cloneData(& anEC, true);
			aQuiescenceEC->setHeight(1 + aQuiescenceEC->getHeight());
			aQuiescenceEC->setEvalNumber(0);

			ExecutionData & aQuiescenceED = aQuiescenceEC->getwExecutionData();
			aQuiescenceED.resetVariantBeforeEvaluation();

			aQuiescenceED.setPathCondition(
					ExpressionConstructor::andExpr(
							anEC.getPathCondition(),
							quiescenceCondition));

			aQuiescenceED.syncTimeValues(anEC.firstChildContext()->getExecutionData());

			aQuiescenceEC->getwFlags().unsetAnalysisTrace();
//			aQuiescenceEC->getwFlags().setExecutionTrivialLoopTrace();

			aQuiescenceEC->unsetInformation();
			if( isSatisfiable )
			{
				aQuiescenceEC->addInfo( mProcessor, INFO_QUIESCENCE );
			}
			else
			{
				++mNoQuiecenceNumber;
				aQuiescenceEC->addInfo( mProcessor, INFO_NON_QUIESCENCE);
				aQuiescenceEC->getwFlags().setExecutionDeadlockTrace();
			}

			const BF & deltaTimeValue = aQuiescenceED.getDeltaTimeValue();

//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
//	AVM_OS_DEBUG << "quiescenceOf " << anEC.str() << std::endl
//		<< "\tdeltaTimeValue : " << deltaTimeValue.str() << std::endl
//		<< "\torig-deltaTimeValue : " << anEC.firstChildContext()->getExecutionData().getDeltaTimeValue().str() << std::endl
//		<< "\tquiescenceCondition  : " << quiescenceCondition.str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

			aQuiescenceED.setIOElementTrace( BF(
					new ExecutionConfiguration( aQuiescenceED.getSystemRID(),
							mQuiescenceElementTrace, deltaTimeValue) ));

			anEC.appendChildContext(aQuiescenceEC);

			return true;
		}
	}

	return false;
}

////////////////////////////////////////////////////////////////////////////////
// RECURSIVE SIMPLIFY QUIESCENCE OF
////////////////////////////////////////////////////////////////////////////////

bool AvmQuiescenceFactory::recSimplifyQuiescenceOf(ExecutionContext & anEC)
{
	if( anEC.hasChildContext() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "recSimplifyQuiescenceOf " + anEC.str() ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		if( simplifyQuiescenceOf(anEC) )
		{

		}

		for( const auto & aChildEC : anEC.getChildContexts()  )
		{
			recSimplifyQuiescenceOf(*aChildEC);
		}

		return true;
	}

	return false;
}

////////////////////////////////////////////////////////////////////////////////
// SIMPLIFY QUIESCENCE OF
////////////////////////////////////////////////////////////////////////////////

bool AvmQuiescenceFactory::simplifyQuiescenceOf(ExecutionContext & anEC)
{
	if( anEC.isnotRoot() && anEC.hasChildContext() )
	{
		return simplifyAdmissibleQuiescenceOf(anEC)
				|| simplifyOutputQuiescenceOf(anEC);
	}

	return false;
}

bool AvmQuiescenceFactory::simplifyAdmissibleQuiescenceOf(ExecutionContext & anEC)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "simplifyAdmissibleQuiescenceOf " + anEC.str() ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	BF quiescenceCondition = computeAdmissibleQuiescenceNodeCondition(anEC);

	bool isSatisfiable = SolverFactory::isStrongSatisfiable(quiescenceCondition, true);
	if( not isSatisfiable )
	{
		return false;
	}

	ExecutionContext * aQuiescenceEC = anEC.cloneData(& anEC, true);
	aQuiescenceEC->setHeight(1 + aQuiescenceEC->getHeight());
	aQuiescenceEC->setEvalNumber(0);

	ExecutionData & aQuiescenceED = aQuiescenceEC->getwExecutionData();
	aQuiescenceED.resetVariantBeforeEvaluation();

	aQuiescenceED.setPathCondition(
			ExpressionConstructor::andExpr(
					anEC.getPathCondition(),
					quiescenceCondition));

	aQuiescenceED.syncTimeValues(anEC.firstChildContext()->getExecutionData());

	aQuiescenceEC->getwFlags().unsetAnalysisTrace();
//	aQuiescenceEC->getwFlags().setExecutionTrivialLoopTrace();

	aQuiescenceEC->unsetInformation();
	if( isSatisfiable )
	{
		aQuiescenceEC->addInfo( mProcessor, INFO_QUIESCENCE );
	}
	else
	{
		++mNoQuiecenceNumber;
		aQuiescenceEC->addInfo( mProcessor, INFO_NON_QUIESCENCE);
		aQuiescenceEC->getwFlags().setExecutionDeadlockTrace();
	}

	const BF & deltaTimeValue = aQuiescenceED.getDeltaTimeValue();

//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
//	AVM_OS_DEBUG << "simplifyAdmissibleQuiescenceOf " << anEC.str() << std::endl
//		<< "\tdeltaTimeValue : " << deltaTimeValue.str() << std::endl
//		<< "\torig-deltaTimeValue : " << anEC.firstChildContext()->getExecutionData().getDeltaTimeValue().str() << std::endl
//		<< "\tquiescenceCondition  : " << quiescenceCondition.str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

	aQuiescenceED.setIOElementTrace( BF(
			new ExecutionConfiguration( aQuiescenceED.getSystemRID(),
					mQuiescenceElementTrace, deltaTimeValue) ));

	anEC.appendChildContext(aQuiescenceEC);

	return true;
}

bool AvmQuiescenceFactory::simplifyOutputQuiescenceOf(ExecutionContext & anEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "simplifyOutputQuiescenceOf " + anEC.str() ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	BF quiescenceCondition = ExpressionConstructor::orExpr(
			computeOutputQuiescenceNodeCondition(anEC),
			computeAdmissibleQuiescenceNodeCondition(anEC));

	bool isSatisfiable = SolverFactory::isStrongSatisfiable(quiescenceCondition, true);
	if( not isSatisfiable )
	{
		return false;
	}

	ExecutionContext * aQuiescenceEC = anEC.cloneData(& anEC, true);
	aQuiescenceEC->setHeight(1 + aQuiescenceEC->getHeight());
	aQuiescenceEC->setEvalNumber(0);

	ExecutionData & aQuiescenceED = aQuiescenceEC->getwExecutionData();
	aQuiescenceED.resetVariantBeforeEvaluation();

	aQuiescenceED.setPathCondition(
			ExpressionConstructor::andExpr(
					anEC.getPathCondition(),
					quiescenceCondition));

	aQuiescenceED.syncTimeValues(anEC.firstChildContext()->getExecutionData());

	aQuiescenceEC->getwFlags().unsetAnalysisTrace();
//	aQuiescenceEC->getwFlags().setExecutionTrivialLoopTrace();

	aQuiescenceEC->unsetInformation();
	if( isSatisfiable )
	{
		aQuiescenceEC->addInfo( mProcessor, INFO_QUIESCENCE );
	}
	else
	{
		++mNoQuiecenceNumber;
		aQuiescenceEC->addInfo( mProcessor, INFO_NON_QUIESCENCE);
		aQuiescenceEC->getwFlags().setExecutionDeadlockTrace();
	}

	const BF & deltaTimeValue = aQuiescenceED.getDeltaTimeValue();

//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
//	AVM_OS_DEBUG << "simplifyOutputQuiescenceOf " << anEC.str() << std::endl
//		<< "\tdeltaTimeValue : " << deltaTimeValue.str() << std::endl
//		<< "\torig-deltaTimeValue : " << anEC.firstChildContext()->getExecutionData().getDeltaTimeValue().str() << std::endl
//		<< "\tquiescenceCondition  : " << quiescenceCondition.str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

	aQuiescenceED.setIOElementTrace( BF(
			new ExecutionConfiguration( aQuiescenceED.getSystemRID(),
					mQuiescenceElementTrace, deltaTimeValue) ));

	anEC.appendChildContext(aQuiescenceEC);

	return true;
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// OUTPUT QUIESCENCE PATH / NODE CONDITION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

BF AvmQuiescenceFactory::computeOutputQuiescencePathCondition(
		const ExecutionContext & tcSourceEC)
{
	AvmCode::OperandCollectionT phiOutput;

	InstanceOfData::Table boundVars;
	AvmTestCaseUtils::newfreshDurationParamsFromEC(tcSourceEC, boundVars);
	AvmTestCaseUtils::newfreshOutputParamsOfEC(tcSourceEC, boundVars);
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
boundVars.strFQN( AVM_OS_DEBUG << "Quiescence Fdur + Fout boundVars  :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
		if( aChildEC->hasIOElementTrace() && aChildEC->hasRunnableElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			if( ! comTrace.valid() )
			{
				continue;
			}

			if( StatementTypeChecker::isOutput(comTrace) )
			{
				const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();
				if( not aChildEC->getPathCondition().isEqualTrue() )
				{

					if( boundVars.nonempty() )
					{
//!@! Remove Type constraint
//						AvmCode::OperandCollectionT timeVarPositiveConditions;
//						for( const auto & boundVar : boundVars)
//						{
//							const BaseTypeSpecifier & type =
//									boundVar.to< InstanceOfData >().getTypeSpecifier();
//							if( type.isTypedPositiveNumber() )
//							{
//								timeVarPositiveConditions.append(
//										ExpressionConstructor::gteExpr(
//												boundVar, ExpressionConstant::INTEGER_ZERO) );
//							}
//						}

//!@! Remove Type constraint
//						if( timeVarPositiveConditions.nonempty() )
//						{
//							phiOutput.append(
//									ExpressionConstructor::forallExpr(boundVars,
//											ExpressionConstructor::impliesExpr(
//													ExpressionConstructor::andExpr(
//															timeVarPositiveConditions),
//												ExpressionConstructor::notExpr(
//														aChildEC->getPathCondition())) ));
//						}
//						else
						{
							phiOutput.append(
									ExpressionConstructor::forallExpr(boundVars,
											ExpressionConstructor::notExpr(
													aChildEC->getPathCondition())) );
						}
					}
					else
					{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "Quiescence condition with out bound variables for Child " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

						phiOutput.append(
								ExpressionConstructor::notExpr(
										aChildEC->getPathCondition()));
					}
				}
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "Quiescence condition for Child " << aChildEC->str() << " for output< " << comPort.getNameID()
		<< " > : " << phiOutput.last().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
			}
		}
	}

	if( phiOutput.populated() )
	{
		return ExpressionConstructor::andExpr(phiOutput);
	}
	else if( phiOutput.nonempty() )
	{
		return phiOutput.first();
	}

	return ExpressionConstant::BOOLEAN_TRUE;
}



BF AvmQuiescenceFactory::computeOutputQuiescenceNodeCondition(
		const ExecutionContext & tcSourceEC)
{
	AvmCode::OperandCollectionT phiOutput;

	InstanceOfData::Table boundVars;
	AvmTestCaseUtils::newfreshDurationParamsFromEC(tcSourceEC, boundVars);
	AvmTestCaseUtils::newfreshOutputParamsOfEC(tcSourceEC, boundVars);
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
boundVars.strFQN( AVM_OS_DEBUG << "Quiescence Fdur + Fout boundVars  :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
		if( aChildEC->hasIOElementTrace() && aChildEC->hasRunnableElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			if( ! comTrace.valid() )
			{
				continue;
			}

			if( StatementTypeChecker::isOutput(comTrace) )
			{
				const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();
				if( not aChildEC->getAllNodeCondition().isEqualTrue() )
				{

					if( boundVars.nonempty() )
					{
//!@! Remove Type constraint
//						AvmCode::OperandCollectionT timeVarPositiveConditions;
//						for( const auto & boundVar : boundVars)
//						{
//							const BaseTypeSpecifier & type =
//									boundVar.to< InstanceOfData >().getTypeSpecifier();
//							if( type.isTypedPositiveNumber() )
//							{
//								timeVarPositiveConditions.append(
//										ExpressionConstructor::gteExpr(
//												boundVar, ExpressionConstant::INTEGER_ZERO) );
//							}
//						}

//!@! Remove Type constraint
//						if( timeVarPositiveConditions.nonempty() )
//						{
//							phiOutput.append(
//									ExpressionConstructor::forallExpr(boundVars,
//											ExpressionConstructor::impliesExpr(
//													ExpressionConstructor::andExpr(
//															timeVarPositiveConditions),
//												ExpressionConstructor::notExpr(
//														aChildEC->getAllNodeCondition())) ));
//						}
//						else
						{
							phiOutput.append(
									ExpressionConstructor::forallExpr(boundVars,
											ExpressionConstructor::notExpr(
													aChildEC->getAllNodeCondition())) );
						}
					}
					else
					{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "Quiescence condition with out bound variables for Child " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

						phiOutput.append(
								ExpressionConstructor::notExpr(
										aChildEC->getAllNodeCondition()));
					}
				}
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "Quiescence condition for Child " << aChildEC->str() << " for output< " << comPort.getNameID()
		<< " > : " << phiOutput.last().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
			}
		}
	}

	if( phiOutput.populated() )
	{
		return ExpressionConstructor::andExpr(phiOutput);
	}
	else if( phiOutput.nonempty() )
	{
		return phiOutput.first();
	}

	return ExpressionConstant::BOOLEAN_TRUE;
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ADMISSIBLE QUIESCENCE PATH / NODE CONDITION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

BF AvmQuiescenceFactory::computeAdmissibleQuiescencePathCondition(
		const ExecutionContext & tcSourceEC)
{
	AvmCode::OperandCollectionT phiOutput_Input;

	const BF & paramElapsedTime =
			AvmTestCaseUtils::newfreshDurationParamFromEC(tcSourceEC);

	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "computeAdmissibleQuiescencePathCondition for " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

		if( aChildEC->hasIOElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			if( ! comTrace.valid() )
			{
				continue;
			}
			const InstanceOfPort & comPort =
					comTrace->first().to< InstanceOfPort >();
			if( StatementTypeChecker::isOutput(comTrace) )
			{
				InstanceOfData::Table boundVars;

				AvmTestCaseUtils::newfreshOutputParamsOfEC(*aChildEC, boundVars);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "computeAdmissibleQuiescencePathCondition for output< " << comPort.getNameID() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

				AvmCode::OperandCollectionT conditions;
//				for( const auto & boundVar : boundVars)
//				{
//!@! Remove Type constraint
//					if( boundVar.to< InstanceOfData >().isTypedPositiveNumber() )
//					{
//						conditions.append(
//								ExpressionConstructor::gteExpr(boundVar,
//										ExpressionConstant::INTEGER_ZERO) );
//					}
//				}

				BF boundVarZ( new InstanceOfData(
						IPointerVariableNature::POINTER_STANDARD_NATURE,
						& ExecutableForm::nullref(), Variable::nullref(),
						paramElapsedTime.to< InstanceOfData >().getTypeSpecifier(),
						QUIESCENCE_VAR_NAME_PASS, 0) );

				boundVars.push_front(boundVarZ);

//!@! Remove Type constraint
//				conditions.append(
//						ExpressionConstructor::gteExpr(boundVarZ,
//								ExpressionConstant::INTEGER_ZERO) );

				conditions.append(
						ExpressionConstructor::ltExpr(paramElapsedTime, boundVarZ));

				BF substPC = AvmTestCaseUtils::substitution(
						aChildEC->getPathCondition(),
						paramElapsedTime, boundVarZ);

				conditions.append(substPC);

				phiOutput_Input.append(
						ExpressionConstructor::existsExpr(boundVars,
								ExpressionConstructor::andExpr(conditions) ));

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << phiOutput_Input.last().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
			}
		}
	}

	if( phiOutput_Input.nonempty() )
	{
		return ExpressionConstructor::orExpr(phiOutput_Input);
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
}


BF AvmQuiescenceFactory::computeAdmissibleQuiescenceNodeCondition(
		const ExecutionContext & tcSourceEC)
{
	AvmCode::OperandCollectionT phiOutput_Input;

	const BF & paramElapsedTime =
			AvmTestCaseUtils::newfreshDurationParamFromEC(tcSourceEC);

	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "computeAdmissibleQuiescenceNodeCondition for " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

		if( aChildEC->hasIOElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			if( ! comTrace.valid() )
			{
				continue;
			}
			const InstanceOfPort & comPort =
					comTrace->first().to< InstanceOfPort >();
			if( StatementTypeChecker::isOutput(comTrace) )
			{
				InstanceOfData::Table boundVars;

				AvmTestCaseUtils::newfreshOutputParamsOfEC(*aChildEC, boundVars);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "computeAdmissibleQuiescenceNodeCondition for output< " << comPort.getNameID() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

				AvmCode::OperandCollectionT conditions;
//				for( const auto & boundVar : boundVars)
//				{
////!@! Remove Type constraint
////					if( boundVar.to< InstanceOfData >().isTypedPositiveNumber() )
////					{
////						conditions.append(
////								ExpressionConstructor::gteExpr(boundVar,
////										ExpressionConstant::INTEGER_ZERO) );
////					}
//				}

				InstanceOfData::Table boundDurationOutputVars(boundVars);
				AvmTestCaseUtils::newfreshDurationParamsOfEC(*aChildEC, boundDurationOutputVars);
				if( aChildEC->getAllNodeCondition().isNotEqualTrue() &&
					AvmTestCaseUtils::containsSomeParameter(aChildEC->getAllNodeCondition(), boundDurationOutputVars) )
				{
//AVM_OS_DEBUG << std::endl << "computeAdmissibleQuiescenceNodeCondition:> boundDurationOutputVars of " << aChildEC->str() << std::endl;
//boundDurationOutputVars.strFQN(AVM_OS_DEBUG);

					BF boundVarZ( new InstanceOfData(
							IPointerVariableNature::POINTER_STANDARD_NATURE,
							& ExecutableForm::nullref(), Variable::nullref(),
							paramElapsedTime.to< InstanceOfData >().getTypeSpecifier(),
							QUIESCENCE_VAR_NAME_PASS, 0) );

					boundVars.push_front(boundVarZ);

//!@! Remove Type constraint
//					conditions.append(
//							ExpressionConstructor::gteExpr(boundVarZ,
//									ExpressionConstant::INTEGER_ZERO) );

					conditions.append(
							ExpressionConstructor::ltExpr(paramElapsedTime, boundVarZ));

					BF substPC = AvmTestCaseUtils::substitution(
							aChildEC->getAllNodeCondition(),
							paramElapsedTime, boundVarZ);

					conditions.append(substPC);

					phiOutput_Input.append(
//							ExpressionConstructor::existsExpr(boundVars,
//									ExpressionConstructor::andExpr(conditions)) );
							AvmTestCaseUtils::existsExpr(boundVars,
									ExpressionConstructor::andExpr(conditions),
									mProcessor.mEnableGuardSimplification) );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << phiOutput_Input.last().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
				}
			}
		}
	}

	if( phiOutput_Input.nonempty() )
	{
		return ExpressionConstructor::orExpr(phiOutput_Input);
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}

//	if( phiOutput_Input.nonempty() )
//	{
//		InstanceOfData::Table boundVars;
//
//		AvmTestCaseUtils::newfreshDurationParamsFromEC(tcSourceEC, boundVars);
//		AvmTestCaseUtils::newfreshOutputParamsFromEC(tcSourceEC, boundVars);
//
//		if( AvmTestCaseUtils::containsSomeParameter(phiOutput_Input, boundVars) )
//		{
//			return ExpressionConstructor::orExpr(phiOutput_Input);
//		}
//	}
//	return( ExpressionConstant::BOOLEAN_TRUE );
}

////////////////////////////////////////////////////////////////////////////////
// END QUIESCENCE
////////////////////////////////////////////////////////////////////////////////


void AvmQuiescenceFactory::removeUnsatisfiableQuiescence(ExecutionContext * anEC)
{
	auto endEC = anEC->getChildContexts().end();
	for( auto it = anEC->getChildContexts().begin() ; it != endEC ; )
	{
		ExecutionContext * itEC = *it;
		if( itEC->getFlags().isExecutionDeadlockTrace() )
		{

			it = anEC->getChildContexts().erase(it);

			delete( itEC );
		}
		else
		{
			if( itEC->hasChildContext() )
			{
				removeUnsatisfiableQuiescence(itEC);
			}
			++it;
		}
	}
}


} /* namespace sep */

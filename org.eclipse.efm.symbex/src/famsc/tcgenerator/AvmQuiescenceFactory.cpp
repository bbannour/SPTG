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
#include "AvmTestCaseUtils.h"

#include <famcore/api/AbstractProcessorUnit.h>

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
AvmQuiescenceFactory::AvmQuiescenceFactory(AbstractProcessorUnit & aProcessor)
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


////////////////////////////////////////////////////////////////////////////////
// QUIESCENCE
////////////////////////////////////////////////////////////////////////////////

void AvmQuiescenceFactory::buildGraph()
{
AVM_IF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "QUIESCENCE COMPLETION" ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )

	ExecutionContext & rootQuiescenceGraph =
			mProcessor.getConfiguration().getFirstExecutionTrace();

	ExecutionContext * symbexGraph = rootQuiescenceGraph.cloneGraph(nullptr, true);

	for( const auto & aChildEC : rootQuiescenceGraph.getChildContexts() )
	{
		recQuiescenceOf(*aChildEC);
	}

	if( mNoQuiecenceNumber > 0 )
	{
		ExecutionContext * saveGraph = rootQuiescenceGraph.cloneGraph(nullptr, true);
		mProcessor.getConfiguration().appendExecutionTrace(saveGraph);

		removeUnsatisfiableQuiescence(& rootQuiescenceGraph);
	}

	mProcessor.getConfiguration().appendExecutionTrace(symbexGraph);
}

bool AvmQuiescenceFactory::recQuiescenceOf(ExecutionContext & anEC)
{
	if( anEC.hasChildContext() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "quiescenceOf " + anEC.str() ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		BF quiescenceCondition = ExpressionConstructor::orExpr(
				computeQuiescenceCondition(anEC),
				computeAdmissibleQuiescenceCondition(anEC));
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

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "quiescenceOf " << anEC.str() << std::endl
		<< "\tdeltaTimeValue : " << deltaTimeValue.str() << std::endl
		<< "\torig-deltaTimeValue : " << anEC.firstChildContext()->getExecutionData().getDeltaTimeValue().str() << std::endl
		<< "\tquiescenceCondition  : " << quiescenceCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

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

bool AvmQuiescenceFactory::quiescenceOf(ExecutionContext & anEC)
{
	if( anEC.isnotRoot() && anEC.hasChildContext() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "quiescenceOf " + anEC.str() ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		BF quiescenceCondition = ExpressionConstructor::orExpr(
				computeQuiescenceCondition(anEC),
				computeAdmissibleQuiescenceCondition(anEC));
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

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "quiescenceOf " << anEC.str() << std::endl
		<< "\tdeltaTimeValue : " << deltaTimeValue.str() << std::endl
		<< "\torig-deltaTimeValue : " << anEC.firstChildContext()->getExecutionData().getDeltaTimeValue().str() << std::endl
		<< "\tquiescenceCondition  : " << quiescenceCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

			aQuiescenceED.setIOElementTrace( BF(
					new ExecutionConfiguration( aQuiescenceED.getSystemRID(),
							mQuiescenceElementTrace, deltaTimeValue) ));

			anEC.appendChildContext(aQuiescenceEC);

			return true;
		}
	}

	return false;
}


BF AvmQuiescenceFactory::computeQuiescenceCondition(
		const ExecutionContext & tcSourceEC)
{
	AvmCode::OperandCollectionT phiOutput;

//	if( not tcSourceEC.getPathCondition().isEqualTrue() )
//	{
//AVM_OS_DEBUG << "phiOutput of " << tcSourceEC.str() << std::endl << tcSourceEC.getPathCondition() << std::endl;
//		phiOutput.append(tcSourceEC.getPathCondition());
//	}

	InstanceOfData::Table boundVars;
	AvmTestCaseUtils::newfreshDurationParamsFromEC(tcSourceEC, boundVars);
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
boundVars.strFQN( AVM_OS_DEBUG << "Quiescence Fdur boundVars  :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

	AvmTestCaseUtils::newfreshInoutParamsFromEC(tcSourceEC, boundVars);
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
boundVars.strFQN( AVM_OS_DEBUG << "Quiescence Fdur + Fout boundVars  :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "Quiescence condition ??? for Child " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

		if( aChildEC->hasIOElementTrace() && aChildEC->hasRunnableElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			if( ! comTrace.valid() )
			{
				continue;
			}

			const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();
			if( StatementTypeChecker::isOutput(comTrace) )
			{
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
	AVM_OS_DEBUG << "Quiescence condition with out bound variables !" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

						phiOutput.append(
								ExpressionConstructor::notExpr(
										aChildEC->getPathCondition()));
					}
				}
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "Quiescence condition for output< " << comPort.getNameID()
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


BF AvmQuiescenceFactory::computeAdmissibleQuiescenceCondition(
		const ExecutionContext & tcSourceEC)
{
	AvmCode::OperandCollectionT phiOutput_Input;
	bool hasOutput_Input = false;

	const BF & paramElapsedTime =
			AvmTestCaseUtils::newfreshDurationParamFromEC(tcSourceEC);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
AVM_OS_DEBUG << "computeAdmissibleQuiescenceCondition paramElapsedTime :\n\t" << paramElapsedTime.strHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "computeAdmissibleQuiescenceCondition for " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

		if( aChildEC->hasIOElementTrace() )
		{
			InstanceOfData::Table boundVars;
			hasOutput_Input = false;

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
				hasOutput_Input = true;

				AvmTestCaseUtils::newfreshInoutParamsFromEC(tcSourceEC, boundVars);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "computeAdmissibleQuiescenceCondition for output< " << comPort.getNameID() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
			}
			else if( StatementTypeChecker::isInput(comTrace) )
			{
				hasOutput_Input = true;

				AvmTestCaseUtils::newfreshInoutParamsFromEC(tcSourceEC, boundVars);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "computeAdmissibleQuiescenceCondition for input< " << comPort.getNameID() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
			}

			if( hasOutput_Input )
			{
				AvmCode::OperandCollectionT conditions;
				for( const auto & boundVar : boundVars)
				{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "computeAdmissibleQuiescenceCondition boundVar : " << boundVar.strHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

//!@! Remove Type constraint
//					if( boundVar.to< InstanceOfData >().isTypedPositiveNumber() )
//					{
//						conditions.append(
//								ExpressionConstructor::gteExpr(boundVar,
//										ExpressionConstant::INTEGER_ZERO) );
//					}
				}

				BF boundVarZ( new InstanceOfData(
						IPointerVariableNature::POINTER_STANDARD_NATURE,
						& ExecutableForm::nullref(), Variable::nullref(),
						paramElapsedTime.to< InstanceOfData >().getTypeSpecifier(),
						"z", 0) );
				boundVars.append(boundVarZ);

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

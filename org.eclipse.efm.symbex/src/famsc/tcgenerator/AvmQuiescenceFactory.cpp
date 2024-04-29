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

	for( const auto & aChildEC : rootQuiescenceGraph.getChildContexts()  )
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

		BF quiescenceCondition = computeQuiescenceCondition(anEC);
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

		BF quiescenceCondition = computeQuiescenceCondition(anEC);
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

	if( not tcSourceEC.getPathCondition().isEqualTrue() )
	{
		phiOutput.append(tcSourceEC.getPathCondition());
	}

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
			const InstanceOfPort & comPort =
					comTrace->first().to< InstanceOfPort >();
			if( StatementTypeChecker::isOutput(comTrace) )
			{
				if( not aChildEC->getPathCondition().isEqualTrue() )
				{

					if( boundVars.nonempty() )
					{
						AvmCode::OperandCollectionT timeVarPositiveConditions;
						for( const auto & boundVar : boundVars)
						{
							const BaseTypeSpecifier & type = boundVar.to< InstanceOfData >().getTypeSpecifier();
							if( type.isTypedPositiveNumber() )
							{
								timeVarPositiveConditions.append(
										ExpressionConstructor::gteExpr(
												boundVar, ExpressionConstant::INTEGER_ZERO) );
							}
						}

						if( timeVarPositiveConditions.nonempty() )
						{
							phiOutput.append(
									ExpressionConstructor::forallExpr(boundVars,
											ExpressionConstructor::impliesExpr(
													ExpressionConstructor::andExpr(
															timeVarPositiveConditions),
												ExpressionConstructor::notExpr(
														aChildEC->getPathCondition())) ));
						}
						else
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

	if( phiOutput.nonempty() )
	{
		return ExpressionConstructor::andExpr(phiOutput);
	}

	return ExpressionConstant::BOOLEAN_TRUE;
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

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

#include "AvmTraceDeterminismFactory.h"
#include "AvmTestCaseUtils.h"

#include <famcore/api/AbstractProcessorUnit.h>

#include <fml/builtin/Identifier.h>

#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionContext.h>

#include <sew/Configuration.h>

#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
AvmTraceDeterminismFactory::AvmTraceDeterminismFactory(AbstractProcessorUnit & aProcessor)
: mProcessor(aProcessor),
INFO_DETERMINISTIC( new Identifier("DETERMINISTIC") ),
INFO_NON_DETERMINISTIC( new Identifier("NON-DETERMINISTIC") ),
mNewfreshInitialParams(),
mNonDeterministicNumber( 0 )
{
	//!! NOTHING
}


////////////////////////////////////////////////////////////////////////////////
// QUIESCENCE
////////////////////////////////////////////////////////////////////////////////

bool AvmTraceDeterminismFactory::checkDeterminism()
{
	ExecutionContext & rootEC =
			mProcessor.getConfiguration().getFirstExecutionTrace();

//!@! PREVIOUS GRAPH
	ExecutionContext * symbexGraph = rootEC.cloneGraph(nullptr, true);
	mProcessor.getConfiguration().appendExecutionTrace(symbexGraph);

	AvmTestCaseUtils::getInitialParameters(rootEC, mNewfreshInitialParams);

AVM_IF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "TRACE DETERMINISM " ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )

	return checkDeterminism(rootEC);
}


bool AvmTraceDeterminismFactory::checkDeterminism(ExecutionContext & anEC)
{
	bool isDeterministic = true;

	auto itChild = anEC.begin();
	const auto & endChild = anEC.end();
	for( ; itChild != endChild ; ++itChild )
	{
		if( (*itChild)->hasChildContext() )
		{
			isDeterministic = checkDeterminism(*(*itChild)) && isDeterministic;
		}

		if( (*itChild)->hasIOElementTrace() )
		{
			const BF & ioTrace = (*itChild)->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();

			auto itSiblingChild = itChild;
			for( ; itSiblingChild != endChild ; ++itSiblingChild )
			{
				if( itSiblingChild != itChild )
				{
					const BF & ioSiblingTrace = (*itSiblingChild)->getIOElementTrace();
					const BFCode & comSiblingTrace =
							BaseEnvironment::searchTraceIO(ioSiblingTrace);
					const InstanceOfPort & comSiblingPort =
							comSiblingTrace->first().to< InstanceOfPort >();
					if( &comPort == &comSiblingPort )
					{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "checkDeterminism " + anEC.str() ) << std::flush
		<< "Port : " << comPort.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

						BF condition;
						if( mNewfreshInitialParams.empty() )
						{
							condition = ExpressionConstructor::andExpr(
									(*itChild)->getPathCondition(),
									(*itSiblingChild)->getPathCondition());
						}
						else
						{
							condition = ExpressionConstructor::andExpr(
									ExpressionConstructor::existsExpr(
											mNewfreshInitialParams,
											(*itChild)->getPathCondition()
									),
									ExpressionConstructor::existsExpr(
											mNewfreshInitialParams,
											(*itSiblingChild)->getPathCondition()
									)
							);
						}

						std::string info = (OSS() << "EC<" << (*itChild)->getIdNumber()
								<< "> , EC<" << (*itSiblingChild)->getIdNumber() << ">");
						if( SolverFactory::isStrongSatisfiable(condition, true) )
						{
							isDeterministic = false;

							anEC.addInfo( mProcessor,
									BF(new Identifier("NON-DETERMINISTIC " + info)) );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "NON-DETERMINISTIC" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
						}
						else
						{
							anEC.addInfo( mProcessor,
									BF(new Identifier("DETERMINISTIC " + info)) );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "DETERMINISTIC" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
						}
					}
				}
			}
		}
	}

	return isDeterministic;
}


bool AvmTraceDeterminismFactory::checkDeterminism(ExecutionContext & tpEC,
		const InstanceOfPort & comPort, const ExecutionContext & aTargetEC)
{
	bool isDeterministic = true;

	for( const auto & itSiblingChild : tpEC.getChildContexts() )
	{
		if( itSiblingChild != (& aTargetEC) )
		{
			const BF & ioSiblingTrace = itSiblingChild->getIOElementTrace();
			const BFCode & comSiblingTrace =
					BaseEnvironment::searchTraceIO(ioSiblingTrace);
			const InstanceOfPort & comSiblingPort =
					comSiblingTrace->first().to< InstanceOfPort >();
			if( &comPort == &comSiblingPort )
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "checkDeterminism " + tpEC.str() ) << std::flush
		<< "Port : " << comPort.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

				BF condition;
				if( mNewfreshInitialParams.empty() )
				{
					condition = ExpressionConstructor::andExpr(
							aTargetEC.getPathCondition(),
							itSiblingChild->getPathCondition());
				}
				else
				{
					condition = ExpressionConstructor::andExpr(
							ExpressionConstructor::existsExpr(
									mNewfreshInitialParams,
									aTargetEC.getPathCondition()
							),
							ExpressionConstructor::existsExpr(
									mNewfreshInitialParams,
									itSiblingChild->getPathCondition()
							)
					);
				}

				std::string info = (OSS() << "EC<" << aTargetEC.getIdNumber()
						<< "> , EC<" << itSiblingChild->getIdNumber() << ">");
				if( SolverFactory::isStrongSatisfiable(condition, true) )
				{
					isDeterministic = false;

					tpEC.addInfo( mProcessor,
							BF(new Identifier("NON-DETERMINISTIC " + info)) );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "NON-DETERMINISTIC" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
				}
				else
				{
					tpEC.addInfo( mProcessor,
							BF(new Identifier("DETERMINISTIC " + info)) );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "DETERMINISTIC" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
				}
			}
		}
	}

	return isDeterministic;
}

} /* namespace sep */

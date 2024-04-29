/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TraceNormalizer.h"

#include "TraceManager.h"

#include <fml/expression/ExpressionConstructor.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// REDUCING API
////////////////////////////////////////////////////////////////////////////////

void TraceNormalizer::reduce(TraceSequence & aTraceElt)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_TRACE << std::endl << "TraceNormalizer::reduce:> start" << std::endl;
	aTraceElt.toStream( AVM_OS_TRACE );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

	TracePoint * prevAssignPoint = nullptr;
	TracePoint * prevTimePoint = nullptr;
	TracePoint * currentTracePoint = nullptr;

	BFList::iterator itPoint = aTraceElt.points.begin();
	BFList::iterator endPoint = aTraceElt.points.end();
	for( ; itPoint != endPoint ; ++itPoint )
	{
		if( (*itPoint).is< TracePoint >() )
		{
			currentTracePoint = (*itPoint).to_ptr< TracePoint >();

			// Reduce Assign Point
			if( currentTracePoint->isAssign() )
			{
				if( (prevAssignPoint != nullptr) &&
					prevAssignPoint->isEQ(*currentTracePoint) )
				{
					itPoint = aTraceElt.points.erase( itPoint ); --itPoint;
				}
				else
				{
					prevAssignPoint = currentTracePoint;

					prevTimePoint = nullptr;
				}
			}

			// Reduce Time Point
			else if( currentTracePoint->isTime() )
			{
				if( (prevTimePoint != nullptr) &&
					(prevTimePoint->object == currentTracePoint->object) )
				{
					prevTimePoint->value = ExpressionConstructor::addExpr(
							prevTimePoint->value, currentTracePoint->value);

					itPoint = aTraceElt.points.erase( itPoint ); --itPoint;
				}
				else
				{
					prevTimePoint = currentTracePoint;
				}
			}

			else if( currentTracePoint->isVirtual() )
			{
				//!! NOTHING
			}
			else
			{
				prevTimePoint = nullptr;
			}
		}

		else if( (*itPoint).is< TraceSequence >() )
		{
			prevTimePoint = nullptr;

			reduce( (*itPoint).to< TraceSequence >() );
		}

		else // Anything else
		{
			prevTimePoint = nullptr;
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_TRACE << std::endl << "TraceNormalizer::reduce:> result" << std::endl;
	aTraceElt.toStream( AVM_OS_TRACE );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
}


void TraceNormalizer::normalize(TraceManager & aTraceManager)
{
	TraceManager::iterator otherIt;

	TraceManager::iterator itTrace = aTraceManager.begin();
	TraceManager::iterator endTrace = aTraceManager.end();
	for( ; itTrace != endTrace ; ++itTrace )
	{
		for( otherIt = aTraceManager.begin() ; otherIt != itTrace ; ++otherIt )
		{
			switch( (*itTrace)->compare(*otherIt) )
			{
				case AVM_OPCODE_EQ:
				{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_COUT << std::endl << "TraceManager::normalize:> "
			<< (*itTrace)->str() << " = " << (*otherIt)->str() << std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		(*itTrace)->toStream(AVM_OS_COUT);
		(*otherIt)->toStream(AVM_OS_COUT);
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

					otherIt = aTraceManager.erase(otherIt);
					--otherIt;
					break;
				}

				case AVM_OPCODE_GT:
				{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_COUT << std::endl << "TraceManager::normalize:> "
			<< (*itTrace)->str() << " > " << (*otherIt)->str() << std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		(*itTrace)->toStream(AVM_OS_COUT);
		(*otherIt)->toStream(AVM_OS_COUT);
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

					otherIt = aTraceManager.erase(otherIt);
					--otherIt;
					break;
				}

				case AVM_OPCODE_LT:
				{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_COUT << std::endl << "TraceManager::normalize:> "
			<< (*itTrace)->str() << " < " << (*otherIt)->str() << std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		(*itTrace)->toStream(AVM_OS_COUT);
		(*otherIt)->toStream(AVM_OS_COUT);
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

					itTrace = aTraceManager.erase(itTrace);
//					--it;
					if( (--itTrace) == otherIt )
					{
						--otherIt;
					}
					break;
				}

				default:
				{
					break;
				}
			}
		}
	}
}


void TraceNormalizer::resetTraceID(TraceManager & aTraceManager)
{
	aTraceManager.resetTID();

	for( auto & itTraceElement : aTraceManager )
	{
		itTraceElement->tid = aTraceManager.newTID();
	}
}

} /* namespace sep */

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

void TraceNormalizer::reduce(TraceSequence * aTraceElt)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_TRACE << std::endl << "TraceNormalizer::reduce:> start" << std::endl;
	aTraceElt->toStream( AVM_OS_TRACE );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

	TracePoint * prevAssignPoint = NULL;
	TracePoint * prevTimePoint = NULL;
	TracePoint * currentTracePoint = NULL;

	BFList::iterator it = aTraceElt->points.begin();
	BFList::iterator endIt = aTraceElt->points.end();
	for(  ; it != endIt ; ++it )
	{
		if( (*it).is< TracePoint >() )
		{
			currentTracePoint = (*it).to_ptr< TracePoint >();

			// Reduce Assign Point
			if( currentTracePoint->isAssign() )
			{
				if( (prevAssignPoint != NULL) &&
					prevAssignPoint->isEQ(*currentTracePoint) )
				{
					aTraceElt->points.erase( it ); --it;
				}
				else
				{
					prevAssignPoint = currentTracePoint;

					prevTimePoint = NULL;
				}
			}

			// Reduce Time Point
			else if( currentTracePoint->isTime() )
			{
				if( (prevTimePoint != NULL) &&
					(prevTimePoint->object == currentTracePoint->object) )
				{
					prevTimePoint->value = ExpressionConstructor::addExpr(
							prevTimePoint->value, currentTracePoint->value);

					aTraceElt->points.erase( it ); --it;
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
				prevTimePoint = NULL;
			}
		}

		else if( (*it).is< TraceSequence >() )
		{
			prevTimePoint = NULL;

			reduce( (*it).to_ptr< TraceSequence >() );
		}

		else // Anything else
		{
			prevTimePoint = NULL;
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_TRACE << std::endl << "TraceNormalizer::reduce:> result" << std::endl;
	aTraceElt->toStream( AVM_OS_TRACE );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
}


void TraceNormalizer::normalize(TraceManager * aTraceManager)
{
	TraceManager::iterator otherIt;

	TraceManager::iterator it = aTraceManager->begin();
	TraceManager::iterator endIt = aTraceManager->end();
	for( ; it != endIt ; ++it )
	{
		for( otherIt = aTraceManager->begin() ; otherIt != it ; ++otherIt )
		{
			switch( (*it)->compare(*otherIt) )
			{
				case AVM_OPCODE_EQ:
				{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_COUT << std::endl << "TraceManager::normalize:> "
			<< (*it)->str() << " = " << (*otherIt)->str() << std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		(*it)->toStream(AVM_OS_COUT);
		(*otherIt)->toStream(AVM_OS_COUT);
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

					otherIt = aTraceManager->erase(otherIt);
					--otherIt;
					break;
				}

				case AVM_OPCODE_GT:
				{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_COUT << std::endl << "TraceManager::normalize:> "
			<< (*it)->str() << " > " << (*otherIt)->str() << std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		(*it)->toStream(AVM_OS_COUT);
		(*otherIt)->toStream(AVM_OS_COUT);
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

					otherIt = aTraceManager->erase(otherIt);
					--otherIt;
					break;
				}

				case AVM_OPCODE_LT:
				{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_COUT << std::endl << "TraceManager::normalize:> "
			<< (*it)->str() << " < " << (*otherIt)->str() << std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		(*it)->toStream(AVM_OS_COUT);
		(*otherIt)->toStream(AVM_OS_COUT);
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

					it = aTraceManager->erase(it);
//					--it;
					if( (--it) == otherIt )
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


void TraceNormalizer::resetTraceID(TraceManager * aTraceManager)
{
	aTraceManager->resetTID();

	TraceManager::iterator it = aTraceManager->begin();
	TraceManager::iterator endIt = aTraceManager->end();
	for( ; it != endIt ; ++it )
	{
		(*it)->tid = aTraceManager->newTID();
	}
}

} /* namespace sep */

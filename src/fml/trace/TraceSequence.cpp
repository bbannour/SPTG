/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TracePoint.h"

#include <collection/Bitset.h>

#include <fml/common/ObjectElement.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/trace/TraceSequence.h>


namespace sep
{


/**
 * [RE]SET TracePoint ID
 */
void TraceSequence::resetTracePointID()
{
	for( auto & itPoint : points )
	{
		if( itPoint.is< TracePoint >() )
		{
			itPoint.to< TracePoint >().tpid = 0;
		}
		else if( itPoint.is< TraceSequence >() )
		{
			itPoint.to< TraceSequence >().resetTracePointID();
		}
	}
}

void TraceSequence::setTracePointID(std::size_t intialTPID)
{
	for( auto & itPoint : points )
	{
		if( itPoint.is< TracePoint >() )
		{
			itPoint.to< TracePoint >().tpid = intialTPID++;
		}
		else if( itPoint.is< TraceSequence >() )
		{
			itPoint.to< TraceSequence >().setTracePointID( intialTPID );
		}
	}
}



/**
 * Contains an Object
 * points
 */
bool TraceSequence::containsObject(const ObjectElement  * anObject) const
{
	for( const auto & itPoint : points )
	{
		if( itPoint.is< TracePoint >() )
		{
			if( itPoint.to< TracePoint >().object == anObject )
			{
				return( true );
			}
		}
		else if( itPoint.is< TraceSequence >() )
		{
			if( itPoint.to< TraceSequence >().containsObject(anObject) )
			{
				return( true );
			}
		}
	}

	return( false );
}


bool TraceSequence::containsPoint(const TracePoint * aPoint, BF & foundPoint) const
{
	for( const auto & itPoint : points )
	{
		if( itPoint.is< TracePoint >() )
		{
			if( itPoint.to< TracePoint >().isEQ(aPoint) )
			{
				foundPoint = itPoint;

				return( true );
			}
		}
		else if( itPoint.is< TraceSequence >() )
		{
			if( itPoint.to< TraceSequence >().
					containsPoint(aPoint, foundPoint) )
			{
				return( true );
			}
		}
	}

	return( false  );
}

bool TraceSequence::containsPoint(const TracePoint * aPoint, bool withValue) const
{
	for( const auto & itPoint : points )
	{
		if( itPoint.is< TracePoint >() )
		{
			if( itPoint.to< TracePoint >().isEQ(aPoint, withValue) )
			{
				return( true );
			}
		}
		else if( itPoint.is< TraceSequence >() )
		{
			if( itPoint.to< TraceSequence >().
					containsPoint(aPoint, withValue) )
			{
				return( true );
			}
		}
	}

	return( false  );
}


/**
 * Comparison
 */
AVM_OPCODE TraceSequence::compare(const TraceSequence * otherTraceElt) const
{
	if( (this != otherTraceElt) && (combinator == otherTraceElt->combinator) )
	{
		BFList::const_iterator it = points.begin();
		BFList::const_iterator endIt = points.end();

		BFList::const_iterator otherIt = otherTraceElt->points.begin();
		BFList::const_iterator otherEndIt = otherTraceElt->points.end();

		TracePoint * aTP = nullptr;
		TracePoint * otherTP = nullptr;

		while( (it != endIt) && (otherIt != otherEndIt) )
		{
			if( (*it).is< TracePoint >() )
			{
				aTP = (*it).to_ptr< TracePoint >();

				if( aTP->isVirtual() )
				{
					++it;

					continue;
				}
				else if( (*otherIt).is< TracePoint >() )
				{
					otherTP = (*otherIt).to_ptr< TracePoint >();

					if( otherTP->isVirtual() )
					{
						++otherIt;

						continue;
					}
					else if( aTP->isNEQ(otherTP) )
					{
						return( AVM_OPCODE_NULL );
					}
				}
				else if( (*otherIt).is< TraceSequence >() )
				{
					return( AVM_OPCODE_NULL );
				}
			}
			else if( (*it).is< TraceSequence >() )
			{
				if( (*otherIt).is< TracePoint >() )
				{
					return( AVM_OPCODE_NULL );
				}
				else if( (*otherIt).is< TraceSequence >() )
				{
					switch( (*it).to< TraceSequence >().compare(
							(*otherIt).to_ptr< TraceSequence >() ) )
					{
						case AVM_OPCODE_EQ:
						{
							break;
						}
						case AVM_OPCODE_LT:
						{
							if( ++it == endIt )
							{
								return( AVM_OPCODE_LT );
							}
							else
							{
								return( AVM_OPCODE_NULL );
							}
						}
						case AVM_OPCODE_GT:
						{
							if( ++otherIt == otherEndIt )
							{
								return( AVM_OPCODE_GT );
							}
							else
							{
								return( AVM_OPCODE_NULL );
							}
						}
						default:
						{
							return( AVM_OPCODE_NULL );
						}
					}
				}
			}

			// Incrementing
			++it; ++otherIt;
		}

		if( it == endIt )
		{
			if( otherIt == otherEndIt )
			{
				return( AVM_OPCODE_EQ );
			}
			else
			{
				return( AVM_OPCODE_LT );
			}
		}
		else
		{
			if( otherIt == otherEndIt )
			{
				return( AVM_OPCODE_GT );
			}
			else
			{
				return( AVM_OPCODE_NULL );
			}
		}
	}

	return( (this == otherTraceElt) ? AVM_OPCODE_EQ : AVM_OPCODE_NULL );
}


////////////////////////////////////////////////////////////////////////////////
// LIFELINE API
////////////////////////////////////////////////////////////////////////////////

std::size_t TraceSequence::toLifeline(
		TraceSequence & lifelineTrace, const RuntimeID & lifelineRID) const
{
	std::size_t lifelineSize = 0;

	TracePoint * currentTracePoint = nullptr;
	TracePoint * lifelineTimePoint = nullptr;

	BF bfTimePoint;

	for( const auto & itPoint : points )
	{
		if( itPoint.is< TracePoint >() )
		{
			currentTracePoint = itPoint.to_ptr< TracePoint >();

			if( lifelineContains(lifelineRID, *currentTracePoint) )
			{
				if( lifelineTimePoint != nullptr )
				{
					lifelineTrace.append( bfTimePoint );
				}

				lifelineTrace.append( itPoint );
				++lifelineSize;

				lifelineTimePoint = nullptr;
			}
			else if( currentTracePoint->isTime() )
			{
				if( lifelineTimePoint != nullptr )
				{
					lifelineTimePoint->value = ExpressionConstructor::addExpr(
							lifelineTimePoint->value, currentTracePoint->value);
				}
				else
				{
					lifelineTimePoint = new TracePoint( *currentTracePoint );
					bfTimePoint = lifelineTimePoint;
				}
			}
		}
		else if( itPoint.is< TraceSequence >() )
		{
			lifelineSize += itPoint.to< TraceSequence >()
					.toLifeline(lifelineTrace, lifelineRID);
		}
	}

	return( lifelineSize );
}


bool TraceSequence::lifelineContains(
		const RuntimeID & lifelineRID, const TracePoint & aPoint) const
{
	if( aPoint.RID.valid() && lifelineRID.isAncestorOf( aPoint.RID ) )
	{
		return( true );
	}
	else if( aPoint.config.isnotNullref()
			&& lifelineRID.isAncestorOf( aPoint.config.getRuntimeID() ) )
	{
		return( true );
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////


void TraceSequence::toStream(OutStream & out, std::size_t printCount) const
{
	out << TAB << "trace#" << tid << "< ";
	if( printCount < points.size() )
	{
		out << "count: " << printCount << " of " << points.size();
	}
	else
	{
		out << "size: " << points.size();
	}

	if( mEC != nullptr )
	{
		out << ", ctx: " << mEC->getIdNumber();
	}
	out << " > { " << combinator->strOp() << EOL_INCR_INDENT;

	for( const auto & itPoint : points )
	{
		if( printCount > 0 )
		{
			printCount = printCount - 1;
		}
		else
		{
			out << TAB << "..." << EOL;
			break;
		}

		if( itPoint.is< TracePoint >() )
		{
			itPoint.to< TracePoint >().toStream(out);
		}
		else if( itPoint.is< TraceSequence >() )
		{
			itPoint.to< TraceSequence >().toStream(out, printCount);
		}
		else
		{
			out << itPoint;
		}
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}

void TraceSequence::toStream(OutStream & out,
		const Bitset & coverageBitSet, std::size_t printCount) const
{
	out << TAB << "trace#" << tid << "< ";
	std::size_t uncCoveredCount = coverageBitSet.size() - coverageBitSet.count();
	if( printCount < uncCoveredCount )
	{
		out << "count: " << printCount << " of " << uncCoveredCount;
	}
	else
	{
		out << "size: " << points.size();
	}

	if( mEC != nullptr )
	{
		out << ", ctx: " << mEC->getIdNumber();
	}
	out << " > { " << combinator->strOp() << EOL_INCR_INDENT;

	for( const auto & itPoint : points )
	{
		if( itPoint.is< TracePoint >() )
		{
			const TracePoint & tracePoint = itPoint.to< TracePoint >();
			if( not coverageBitSet[tracePoint.tpid] )
			{
				if( printCount > 0 )
				{
					printCount = printCount - 1;

					tracePoint.toStream(out);
				}
				else
				{
					out << TAB << "..." << EOL;
					break;
				}
			}
		}
		else if( itPoint.is< TraceSequence >() )
		{
			itPoint.to< TraceSequence >().toStream(out, printCount);
		}
		else
		{
			out << itPoint;
		}
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}


} /* namespace sep */

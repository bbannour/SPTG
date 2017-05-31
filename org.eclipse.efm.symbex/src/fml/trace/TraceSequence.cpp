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

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/trace/TraceSequence.h>


namespace sep
{

/**
 * Contains an Object
 * points
 */
bool TraceSequence::containsObject(BaseCompiledForm  * anObject) const
{
	BFList::const_iterator itPoint = points.begin();
	BFList::const_iterator endPoint = points.end();
	for( ; itPoint != endPoint ; ++itPoint )
	{
		if( (*itPoint).is< TracePoint >() )
		{
			if( (*itPoint).to_ptr< TracePoint >()->object == anObject )
			{
				return( true );
			}
		}
		else if( (*itPoint).is< TraceSequence >() )
		{
			if( (*itPoint).to_ptr< TraceSequence >()->containsObject(anObject) )
			{
				return( true );
			}
		}
	}

	return( false );
}


bool TraceSequence::containsPoint(TracePoint * aPoint, BF & foundPoint) const
{
	BFList::const_iterator itPoint = points.begin();
	BFList::const_iterator endPoint = points.end();
	for( ; itPoint != endPoint ; ++itPoint )
	{
		if( (*itPoint).is< TracePoint >() )
		{
			if( (*itPoint).to_ptr< TracePoint >()->isEQ(aPoint) )
			{
				foundPoint = (*itPoint);

				return( true );
			}
		}
		else if( (*itPoint).is< TraceSequence >() )
		{
			if( (*itPoint).to_ptr< TraceSequence >()->
					containsPoint(aPoint, foundPoint) )
			{
				return( true );
			}
		}
	}

	return( false  );
}

bool TraceSequence::containsPoint(TracePoint * aPoint, bool withValue) const
{
	BFList::const_iterator itPoint = points.begin();
	BFList::const_iterator endPoint = points.end();
	for( ; itPoint != endPoint ; ++itPoint )
	{
		if( (*itPoint).is< TracePoint >() )
		{
			if( (*itPoint).to_ptr< TracePoint >()->isEQ(aPoint, withValue) )
			{
				return( true );
			}
		}
		else if( (*itPoint).is< TraceSequence >() )
		{
			if( (*itPoint).to_ptr< TraceSequence >()->
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

		TracePoint * aTP = NULL;
		TracePoint * otherTP = NULL;

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
					switch( (*it).to_ptr< TraceSequence >()->compare(
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

avm_size_t TraceSequence::toLifeline(
		TraceSequence & lifelineTrace, const RuntimeID & lifelineRID) const
{
	avm_size_t lifelineSize = 0;

	TracePoint * currentTracePoint = NULL;
	TracePoint * lifelineTimePoint = NULL;

	BF bfTimePoint;

	BFList::const_iterator itPoint = points.begin();
	BFList::const_iterator endPoint = points.end();
	for( ; itPoint != endPoint ; ++itPoint )
	{
		if( (*itPoint).is< TracePoint >() )
		{
			currentTracePoint = (*itPoint).to_ptr< TracePoint >();

			if( lifelineContains(lifelineRID, *currentTracePoint) )
			{
				if( lifelineTimePoint != NULL )
				{
					lifelineTrace.append( bfTimePoint );
				}

				lifelineTrace.append( *itPoint );
				++lifelineSize;

				lifelineTimePoint = NULL;
			}
			else if( currentTracePoint->isTime() )
			{
				if( lifelineTimePoint != NULL )
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
		else if( (*itPoint).is< TraceSequence >() )
		{
			lifelineSize += (*itPoint).to_ptr< TraceSequence >()
					->toLifeline(lifelineTrace, lifelineRID);
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
	else if( (aPoint.config != NULL)
			&& lifelineRID.isAncestorOf( aPoint.config->getRuntimeID() ) )
	{
		return( true );
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void TraceSequence::toStream(OutStream & os) const
{
	os << TAB << "trace#" << tid << "<size:" << points.size();
	if( mEC != NULL )
	{
		os << ", ctx:" << mEC->getIdNumber();
	}
	os << "> { " << combinator->strOp() << EOL;

//	os << INCR_INDENT;
//	BFList::const_iterator endIt = points.end();
//	for( BFList::const_iterator it = points.begin() ; it != endIt ; ++it )
//	{
//		os << (*it);
//	}
//	os << DECR_INDENT;

	os << INCR_INDENT << points << DECR_INDENT;

	os << TAB << "}" << EOL_FLUSH;
}


void TraceSequence::traceMinimum(OutStream & os) const
{
	os << TAB << "trace#" << tid << "<size:" << points.size();
	if( mEC != NULL )
	{
		os << ", ctx:" << mEC->getIdNumber();
	}
	os << "> { " << combinator->strOp() << EOL_INCR_INDENT;

	BFList::const_iterator endIt = points.end();
	for( BFList::const_iterator it = points.begin() ; it != endIt ; ++it )
	{
		if( (*it).is< TracePoint >() )
		{
			(*it).to_ptr< TracePoint >()->traceMinimum(os);
		}
		else if( (*it).is< TraceSequence >() )
		{
			(*it).to_ptr< TraceSequence >()->traceMinimum(os);
		}
		else
		{
			os << (*it);
		}
	}

	os << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}


} /* namespace sep */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2014
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "SequenceDiagramTraceBuilder.h"

#include <collection/Typedef.h>

#include <computer/EvaluationEnvironment.h>

#include <fml/executable/ExecutableSystem.h>

#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/TableOfData.h>

#include <fml/template/TimedMachine.h>

#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <fml/type/TypeManager.h>

#include  <famcore/trace/AvmTraceGenerator.h>
#include  <famcore/trace/TraceManager.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>

#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
SequenceDiagramTraceBuilder::SequenceDiagramTraceBuilder(AvmTraceGenerator & aProcessor,
		SolverDef::SOLVER_KIND aSolverKind, TraceFilter & aTracePointFilter)
: BasicTraceBuilder( aProcessor, aSolverKind, aTracePointFilter ),
mMapMessageReceiver()
{
	//!! NOTHING
}



////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////
/*
prototype process::trace_generator as &avm::processor.TRACE_GENERATOR is
 section REPORT
 ...
 endsection REPORT

 section PROPERTY
 ...
 endsection PROPERTY

 section TRACE
  // AND --> conjunctive
  // OR  --> disjunctive
  // XOR --> exclusive
  // NOT --> negative
  @combinator = 'OR';

  @path#condition = "[*]";
  @path#timed#condition = "[*]";

  @time = "$delta";
  @time = "$time";

  @assign = "sens";

  @newfresh = "sens";

  @com    = "env";

  @signal = "sens";
  @port   = "env";

  @input  = "env";
  @output = "env";

  @output = "Thermostat->dt";
  @input  = "Thermostat->equip";
  @output = "Equipment->error";

  @transition = "t8";
  @machine = "m1";
  @procedure = "[*]";
 endsection TRACE

 section FORMAT
 ...
 endsection FORMAT
endprototype
*/
bool SequenceDiagramTraceBuilder::configureImpl(const WObject * wfParameterObject)
{
	bool isOK = BasicTraceBuilder::configureImpl(wfParameterObject);

	mTracePointFilter.pairwiseStepBeginEndSeparator();

	return isOK;
}


////////////////////////////////////////////////////////////////////////////////
// CONSTRUCTION API
////////////////////////////////////////////////////////////////////////////////

void SequenceDiagramTraceBuilder::buildTrace()
{
	BasicTraceBuilder::buildTrace();

	// Analyser la trace, c'est à dire aTraceSequence
	analyse( * aTraceSequence );

	// Traitement pour réduire la trace, c'est à dire aTraceSequence
	reduce( * aTraceSequence );
}

void SequenceDiagramTraceBuilder::analyse(const TraceSequence & aTraceSequence)
{
	for( const auto & itPoint : aTraceSequence.points )
	{
		if( itPoint.is< TracePoint >() )
		{
			analyse( itPoint.to< TracePoint >() );
		}

		else if( itPoint.is< TraceSequence >() )
		{
			analyse( itPoint.to< TraceSequence >() );
		}
	}
}

void SequenceDiagramTraceBuilder::buildTraceVariable(
		const ExecutionContext & anEC, bool isnotRoot)
{
	const ExecutionData & anED = anEC.getExecutionData();
	const ExecutionData & prevED = ( isnotRoot ?
			anEC.getPrevious()->getExecutionData() : ExecutionData::_NULL_ );

	avm_offset_t endOffset = 0;
	avm_offset_t offset = 0;

	BFVector vectorOfAssigns;
	InstanceOfData * aVariable;
	BF aValue;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	RuntimeForm * pRF = nullptr;
	for( ++itRF; (itRF != endRF) ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->hasData() )
		{
			vectorOfAssigns.clear();

			endOffset = pRF->refExecutable().getAllVariables().size();
			for( offset = 0 ; offset < endOffset ; ++offset)
			{
				aVariable = pRF->refExecutable().getAllVariables().rawAt(offset);

				if( mTracePointFilter.pass(pRF->getRID(), (*aVariable)) )
				{
					aValue = pRF->getData(aVariable);

					if( mDataSelectionModifiedFlags && isnotRoot )
					{
						if( aValue == prevED.getRuntime(
								pRF->getRID()).getData(aVariable) )
						{
							continue;
						}
					}

					bfTP = aTracePoint = new TracePoint(anEC,
							ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE,
							AVM_OPCODE_ASSIGN, pRF->getInstance(), nullptr);

					aTracePoint->RID = pRF->getRID();
					aTracePoint->tpid = ++TP_ID;
					aTracePoint->object = aVariable;
					aTracePoint->value  = aValue;

					vectorOfAssigns.append( bfTP );
				}
			}

			if( vectorOfAssigns.nonempty() )
			{
				if( vectorOfAssigns.populated() )
				{
					bfTP = aTracePoint = new TracePoint(anEC,
							ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE,
							AVM_OPCODE_ASSIGN, pRF->getInstance(), nullptr);

					aTracePoint->RID = pRF->getRID();
					aTracePoint->tpid = ++TP_ID;
					aTraceSequence->points.append( bfTP );

					aTracePoint->value = BF( new ArrayBF(vectorOfAssigns) );
				}
				else
				{
					aTraceSequence->points.append( vectorOfAssigns.first() );
				}
			}
		}
	}
}


void SequenceDiagramTraceBuilder::analyse(const TracePoint & aTracePoint)
{
	if( aTracePoint.isCom() && aTracePoint.config.hasIOMessage() )
	{
		const Message & ioMessage = aTracePoint.config.getIOMessage();

		RuntimeID msgReceiverRID;
		if( ioMessage.hasReceiverRID() )
		{
			msgReceiverRID = ioMessage.getReceiverRID();
		}

		else if( aTracePoint.isComInput() )
		{
			msgReceiverRID = aTracePoint.RID;
		}

		if( msgReceiverRID.valid() )
		{
			auto ite = mMapMessageReceiver.find( ioMessage.raw_pointer() );

			if( ite == mMapMessageReceiver.end() )
			{
				mMapMessageReceiver[ ioMessage.raw_pointer() ] =
						List< RuntimeID >( msgReceiverRID );
			}
			else
			{
				(*ite).second.add_unique( msgReceiverRID );
			}
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
// REDUCING API
////////////////////////////////////////////////////////////////////////////////
void SequenceDiagramTraceBuilder::reduce(TraceSequence & aTraceSequence)
{
	TracePoint * currentTracePoint = nullptr;
	TracePoint * prevTracePoint    = nullptr;

	BFList::iterator itPoint = aTraceSequence.points.begin();
	while( itPoint != aTraceSequence.points.end() )
	{
		if( (*itPoint).is< TracePoint >() )
		{
			currentTracePoint = (*itPoint).to_ptr< TracePoint >();

			if( prevTracePoint != nullptr )
			{
				// Reduce empty trace sequence (i.e. STEP#BEGIN, STEP#END etc.)
//				if( prevTracePoint->nature == ENUM_TRACE_POINT::TRACE_STEP_BEGIN_NATURE
//				&& prevTracePoint->nature == ENUM_TRACE_POINT::TRACE_STEP_END_NATURE )
//				{
//					// Erase currentVirtualPoint
//					itPoint = aTraceSequence.points.erase( --itPoint );
//
//					// Erase prevVirtualPoint
//					itPoint = aTraceSequence.points.erase( itPoint );
//
//					prevTracePoint = nullptr;
//					continue;
//				}
				// Reduce pair (output ! msg / input ? message) to output !? msg
//				else
					if( prevTracePoint->isComOutput()
					&& currentTracePoint->isComInput() )
				{
					if ( currentTracePoint->config.getIOMessage().equals(
							prevTracePoint->config.getIOMessage() ) )
					{
						// Erase currentTracePoint
						itPoint = aTraceSequence.points.erase( itPoint );

						prevTracePoint = nullptr;
						continue;
					}
				}
			}

			prevTracePoint = currentTracePoint;
		}
		else // Anything else
		{
			prevTracePoint = nullptr;

			if( (*itPoint).is< TraceSequence >() )
			{
				reduce( (*itPoint).to< TraceSequence >() );
			}
		}

		// Increment iterator
		++itPoint;
	}
}




} /* namespace sep */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Serializer.h"

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>

#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>

#include <fml/type/TypeManager.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <boost/format.hpp>

namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

/**
prototype processor::serializer#graph "serialize graph" as avm::processor.SERIALIZER is
section PROPERTY
	@info#selection = 'ALL';    // ALL | MODIFIED
	@data#selection = 'ALL';	// ALL | MODIFIED
endsection PROPERTY

section FORMAT
	@line#wrap#width = 42;
	@line#wrap#separator = "\\l";
endsection FORMAT

endprototype
*/

bool Serializer::configureImpl()
{
	const WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));
	if( thePROPERTY != WObject::_NULL_ )
	{
		mInfoAllFlags = (Query::getRegexWPropertyString(
				thePROPERTY, CONS_WID2("info", "selection"), "ALL") == "ALL");

		mDataSelectionModifiedFlags = (Query::getRegexWPropertyString(
			thePROPERTY, CONS_WID2("data", "selection"), "MODIFIED") == "MODIFIED");
	}

	const WObject * theFORMAT = Query::getRegexWSequence(getParameterWObject(),
			OR_WID2("format", "FORMAT"), thePROPERTY);
	if( theFORMAT != WObject::_NULL_ )
	{
		if( not mWrapData.configure(theFORMAT) )
		{
			//!!NOTHING
		}

		if( not mMultiValueArrayCSS.configure(theFORMAT,
				"array", DEFAULT_SYMBEX_VALUE_ARRAY_CSS) )
		{
			//!!NOTHING
		}

		if( not mMultiValueParamsCSS.configure(theFORMAT,
				"param(eter)?s?", DEFAULT_SYMBEX_VALUE_PARAMS_CSS) )
		{
			//!!NOTHING
		}

		if( not mMultiValueStructCSS.configure(theFORMAT,
				"struct", DEFAULT_SYMBEX_VALUE_STRUCT_CSS) )
		{
			//!!NOTHING
		}

	}

	return( true );
}



bool Serializer::filterExecutionConfiguration(
		const TraceFilter & mTraceFilter, const ExecutionContext & anEC,
		const ExecutionConfiguration & anExecConf) const
{
	if( anExecConf.isAvmCode() )
	{
		const AvmCode & aCode = anExecConf.toAvmCode();

		std::unique_ptr< TracePoint > aTracePoint;

		ObjectElement * object;
		BF value;

		switch( aCode.getAvmOpCode() )
		{
			case AVM_OPCODE_ASSIGN_NEWFRESH:
			{
				object = aCode.first().to_ptr< BaseInstanceForm >();
				value = aCode.second();

				if( static_cast< BaseInstanceForm * >(object)->hasTypedTime()
					&& mTraceFilter.hasTimePoint() )
				{
					return( mTraceFilter.pass( TracePoint(anEC, anExecConf,
							ENUM_TRACE_POINT::TRACE_TIME_NATURE,
							AVM_OPCODE_TIMED_GUARD,
							anExecConf.getRuntimeID().getInstance(),
							object, value) ) );
				}
				else
				{
					return( mTraceFilter.pass( TracePoint(anEC, anExecConf,
							anExecConf.getRuntimeID(), object, value) ) );
				}

				return( false );
			}

			case AVM_OPCODE_TRACE:
			{
				if( mTraceFilter.hasMetaTracePoint() )
				{
					object = anExecConf.getRuntimeID().getInstance();

					ArrayBF * operands = new ArrayBF(
							TypeManager::UNIVERSAL, aCode.size() );
					value.setPointer(operands);

					std::size_t offset = 0;
					for( const auto & itOperand : aCode.getOperands() )
					{
						operands->set(offset++, itOperand);
					}

					return( mTraceFilter.pass( TracePoint(anEC, anExecConf,
							ENUM_TRACE_POINT::TRACE_META_TRACE_NATURE,
							AVM_OPCODE_TRACE,
							anExecConf.getRuntimeID().getInstance(),
							object, value) ) );
				}

				return( false );
			}

			case AVM_OPCODE_DEBUG:
			{
				if( mTraceFilter.hasMetaTracePoint() )
				{
					object = anExecConf.getRuntimeID().getInstance();

					ArrayBF * operands = new ArrayBF(
							TypeManager::UNIVERSAL, aCode.size() );
					value.setPointer(operands);

					std::size_t offset = 0;
					for( const auto & itOperand : aCode.getOperands() )
					{
						operands->set(offset++, itOperand);
					}

					return( mTraceFilter.pass( TracePoint(anEC, anExecConf,
							ENUM_TRACE_POINT::TRACE_META_DEBUG_NATURE,
							AVM_OPCODE_DEBUG,
							anExecConf.getRuntimeID().getInstance(),
							object, value) ) );

				}

				return( false );
			}

			case AVM_OPCODE_INPUT:

//			case AVM_OPCODE_INPUT_FROM:
//
//			case AVM_OPCODE_INPUT_SAVE:
//
//			// Optimized version of INPUT
//			case AVM_OPCODE_INPUT_ENV:
//			case AVM_OPCODE_INPUT_VAR:
//			case AVM_OPCODE_INPUT_FLOW:
//			case AVM_OPCODE_INPUT_BUFFER:
//			case AVM_OPCODE_INPUT_RDV:
//			case AVM_OPCODE_INPUT_MULTI_RDV:
//			case AVM_OPCODE_INPUT_BROADCAST:
//			case AVM_OPCODE_INPUT_DELEGATE:

			case AVM_OPCODE_OUTPUT:

//			case AVM_OPCODE_OUTPUT_TO:
//			// Optimized version of OUTPUT
//			case AVM_OPCODE_OUTPUT_ENV:
//			case AVM_OPCODE_OUTPUT_VAR:
//			case AVM_OPCODE_OUTPUT_FLOW:
//			case AVM_OPCODE_OUTPUT_BUFFER:
//			case AVM_OPCODE_OUTPUT_RDV:
//			case AVM_OPCODE_OUTPUT_MULTI_RDV:
//			case AVM_OPCODE_OUTPUT_BROADCAST:
//			case AVM_OPCODE_OUTPUT_DELEGATE:

			default:
			{
				if( aCode.first().is< BaseInstanceForm >() )
				{
					object = aCode.first().to_ptr< BaseInstanceForm >();
					value = BF::REF_NULL;

					if( aCode.hasManyOperands() )
					{
						ArrayBF * values = new ArrayBF(
								TypeManager::UNIVERSAL, aCode.size() - 1);
						value.setPointer(values);

						AvmCode::const_iterator itOperand = aCode.begin();
						AvmCode::const_iterator endOperand = aCode.end();
						std::size_t offset = 0;
						for( ++itOperand ; itOperand != endOperand ;
								++offset , ++itOperand )
						{
							values->set(offset, (*itOperand));
						}
					}

					return( mTraceFilter.pass( TracePoint(anEC, anExecConf,
							anExecConf.getRuntimeID(), object, value) ) );
				}

				return( false );
			}
		}
	}

	return( false );
}



} /* namespace sep */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TracePoint.h"

#include <fml/common/ObjectElement.h>
#include <fml/common/SpecifierElement.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/TypeManager.h>

#include <fml/workflow/Query.h>

#include <sew/Configuration.h>

#include <util/avm_string.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
TracePoint::TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature,
		AVM_OPCODE anOP, const BF & aValue)
: Element( CLASS_KIND_T( TracePoint ) ),
tpid( 0 ),

EC( ExecutionContext::_NULL_ ),
config( NULL ),

nature( aNature ),
op( anOP ),

RID( ),

machine( NULL ),

object ( NULL ),
any_object( false ),

value( aValue )
{
	//!! NOTHING
}


TracePoint::TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature,
		AVM_OPCODE anOP, InstanceOfMachine * aMachine,
		ObjectElement * anObject, const BF & aValue)
: Element( CLASS_KIND_T( TracePoint ) ),
tpid( 0 ),

EC( ExecutionContext::_NULL_ ),
config( NULL ),

nature( aNature ),
op( anOP ),

RID( ),

machine( aMachine ),

object( anObject ),
any_object( false ),

value( aValue )
{
	//!! NOTHING
}


TracePoint::TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature,
		AVM_OPCODE anOP, const RuntimeID & aRID,
		ObjectElement * anObject, const BF & aValue)
: Element( CLASS_KIND_T( TracePoint ) ),
tpid( 0 ),

EC( ExecutionContext::_NULL_ ),
config( NULL ),

nature( aNature ),
op( anOP ),

RID( aRID ),

machine( aRID.getInstance() ),

object( anObject ),
any_object( false ),

value( aValue )
{
	//!! NOTHING
}


/**
 * CONSTRUCTOR
 * for Meta point
 * TRACE_COMMENT_NATURE
 * TRACE_SEPARATOR_NATURE
 * TRACE_NEWLINE_NATURE
 * TRACE_STEP_NATURE
 */
TracePoint::TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature,
		const std::string & strSeparator)
: Element( CLASS_KIND_T( TracePoint ) ),
tpid( 0 ),

EC( ExecutionContext::_NULL_ ),
config( NULL ),
nature( aNature ),
op( AVM_OPCODE_NULL ),

machine( NULL ),

object ( NULL ),
any_object( false ),

value( ExpressionConstructor::newString(strSeparator) )
{
	//!! NOTHING
}

TracePoint::TracePoint(const ExecutionContext & anEC,
		ENUM_TRACE_POINT::TRACE_NATURE aNature,
		const std::string & strSeparator)
: Element( CLASS_KIND_T( TracePoint ) ),
tpid( 0 ),

EC( anEC ),
config( NULL ),
nature( aNature ),
op( AVM_OPCODE_NULL ),

machine( NULL ),

object ( NULL ),
any_object( false ),

value( ExpressionConstructor::newString(strSeparator) )
{
	//!! NOTHING
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

void TracePoint::updateRID(const ExecutionData & anED)
{
	if( RID.valid() || ((object == NULL) && (machine == NULL)))
	{
		return;
	}

	else if( object != NULL )
	{
		if( object->is< InstanceOfMachine >() )
		{
			if( object->to< InstanceOfMachine >()->
					getExecutable()->hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( object->to< InstanceOfMachine >() );
			}
		}

		else if( object->is< BaseAvmProgram >() )
		{
			if( object->to< BaseAvmProgram >()->
					getExecutable()->hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID(
						object->to< BaseAvmProgram >()->getExecutable() );
			}
		}

		else if( machine != NULL )
		{
			if( machine->getExecutable()->hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( machine );
			}
		}

		else if( object->is< BaseInstanceForm >() &&
				object->to< BaseInstanceForm >()->hasRuntimeContainerRID() )
		{
			RID = object->to< BaseInstanceForm >()->getRuntimeContainerRID();
		}
	}

	else if( machine != NULL )
	{
		if( machine->getExecutable()->hasSingleRuntimeInstance() )
		{
			RID = anED.getRuntimeID( machine );
		}
	}

	else
	{
		ExecutableForm * anExecutable = getExecutable();

		if( (anExecutable != NULL) && anExecutable->hasSingleRuntimeInstance() )
		{
			RID = anED.getRuntimeID( anExecutable );

			if( RID.valid() )
			{
				machine = RID.getInstance();
			}
		}
	}
}


void TracePoint::updateMachine(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	ExecutableQuery XQuery( aConfiguration );

	if( aQualifiedNameID.find('.') == std::string::npos )
	{
		machine = XQuery.getMachineByNameID(
				Specifier::DESIGN_INSTANCE_KIND, aQualifiedNameID).rawMachine();
		if( machine == NULL )
		{
			machine = XQuery.getMachineByNameID(
				Specifier::DESIGN_MODEL_KIND, aQualifiedNameID).rawMachine();
		}
	}
	else
	{
		machine = XQuery.getMachineByQualifiedNameID(
				Specifier::DESIGN_INSTANCE_KIND, aQualifiedNameID).rawMachine();
		if( machine == NULL )
		{
			machine = XQuery.getMachineByQualifiedNameID(
				Specifier::DESIGN_MODEL_KIND, aQualifiedNameID).rawMachine();
		}
	}
}


bool TracePoint::configurePort(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID,
		ListOfTracePoint & otherTracePoint)
{
	// ENVIRONMENT COMMUNICATION PROTOCOL
	if( aQualifiedNameID == "env" )
	{
		switch( op )
		{
			case AVM_OPCODE_INPUT:
			case AVM_OPCODE_INPUT_ENV:
			{
				op = AVM_OPCODE_INPUT_ENV;
				break;
			}

			case AVM_OPCODE_OUTPUT:
			case AVM_OPCODE_OUTPUT_ENV:
			{
				op = AVM_OPCODE_OUTPUT_ENV;
				break;
			}

			case AVM_OPCODE_NULL:
			default:
			{
				op = AVM_OPCODE_INPUT_ENV;

				TracePoint * newTracePoint = new TracePoint( this );
				newTracePoint->op = AVM_OPCODE_OUTPUT_ENV;

				otherTracePoint.append( newTracePoint );

				break;
			}
		}

		return( true );
	}
	else if( REGEX_MATCH(aQualifiedNameID, CONS_WID2("input", "env")) )
	{
		op = AVM_OPCODE_INPUT_ENV;

		return( true );
	}
	else if( REGEX_MATCH(aQualifiedNameID, CONS_WID2("output", "env")) )
	{
		op = AVM_OPCODE_OUTPUT_ENV;

		return( true );
	}

	// RENDEZ-VOUS COMMUNICATION PROTOCOL
	if( aQualifiedNameID == "rdv" )
	{
		switch( op )
		{
			case AVM_OPCODE_INPUT:
			case AVM_OPCODE_INPUT_RDV:
			{
				op = AVM_OPCODE_INPUT_RDV;
				break;
			}

			case AVM_OPCODE_OUTPUT:
			case AVM_OPCODE_OUTPUT_RDV:
			{
				op = AVM_OPCODE_OUTPUT_RDV;
				break;
			}

			case AVM_OPCODE_NULL:
			default:
			{
				op = AVM_OPCODE_INPUT_RDV;

				TracePoint * newTracePoint = new TracePoint( this );
				newTracePoint->op = AVM_OPCODE_OUTPUT_RDV;

				otherTracePoint.append( newTracePoint );

				break;
			}
		}

		return( true );
	}
	else if( REGEX_MATCH(aQualifiedNameID, CONS_WID2("input", "rdv")) )
	{
		op = AVM_OPCODE_INPUT_RDV;

		return( true );
	}
	else if( REGEX_MATCH(aQualifiedNameID, CONS_WID2("output", "rdv")) )
	{
		op = AVM_OPCODE_OUTPUT_RDV;

		return( true );
	}

	else if( REGEX_MATCH(aQualifiedNameID, CONS_WID2("(inout|com)", "env")) )
	{
		op = AVM_OPCODE_INPUT_ENV;

		TracePoint * newTracePoint = new TracePoint( this );
		newTracePoint->op = AVM_OPCODE_OUTPUT_ENV;

		otherTracePoint.append( newTracePoint );

		return( true );
	}

	else if( REGEX_MATCH(aQualifiedNameID, CONS_WID2("(inout|com)", "rdv")) )
	{
		op = AVM_OPCODE_INPUT_RDV;

		TracePoint * newTracePoint = new TracePoint( this );
		newTracePoint->op = AVM_OPCODE_OUTPUT_RDV;

		otherTracePoint.append( newTracePoint );

		return( true );
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	ExecutableQuery XQuery( aConfiguration );

	ListOfSymbol listofPort;

	std::string::size_type pos = aQualifiedNameID.find("->");

	if( pos != std::string::npos )
	{
		std::string mid = aQualifiedNameID.substr(0, pos);
		std::string obj = aQualifiedNameID.substr(pos + 2);

		updateMachine(aConfiguration, mid);

		if( obj == "[*]" )
		{
			any_object = true;

			return( true );
		}

		if( machine != NULL )
		{
			ExecutableForm * containerExecutable = machine->getExecutable();

			while( containerExecutable != NULL )
			{
				object = containerExecutable->getPort().getByNameID(obj).rawPort();

				if( object == NULL )
				{
					containerExecutable =
							containerExecutable->getExecutableContainer();
				}
				else
				{
					break;
				}
			}
		}
		else
		{
			switch( op )
			{
				case AVM_OPCODE_INPUT:
				case AVM_OPCODE_INPUT_ENV:
				case AVM_OPCODE_INPUT_RDV:
				{
					if( XQuery.getPortByNameID(obj, listofPort,
							Modifier::DIRECTION_INPUT_KIND, false) )
					{
						object = NULL;

						ListOfSymbol::iterator itPort = listofPort.begin();
						ListOfSymbol::iterator endPort = listofPort.end();
						for( ; itPort != endPort ; ++itPort )
						{
							if( (*itPort).getModifier().isDirectionInput() )
							{
								object = (*itPort).rawPort();
								break;
							}
							else if( (object == NULL)
								&& (*itPort).getModifier().isDirectionInout() )
							{
								object = (*itPort).rawPort();
							}
						}
					}

					break;
				}

				case AVM_OPCODE_OUTPUT:
				case AVM_OPCODE_OUTPUT_ENV:
				case AVM_OPCODE_OUTPUT_RDV:
				{
					if( XQuery.getPortByNameID(obj, listofPort,
							Modifier::DIRECTION_OUTPUT_KIND, false) )
					{
						object = NULL;

						ListOfSymbol::iterator itPort = listofPort.begin();
						ListOfSymbol::iterator endPort = listofPort.end();
						for( ; itPort != endPort ; ++itPort )
						{
							if( (*itPort).getModifier().isDirectionOutput() )
							{
								object = (*itPort).rawPort();
								break;
							}
							else if( (object == NULL)
								&& (*itPort).getModifier().isDirectionInout() )
							{
								object = (*itPort).rawPort();
							}
						}
					}

					break;
				}

				default:
				{
					XQuery.getPortByNameID(obj, listofPort);

					configurePort(op, listofPort, otherTracePoint);

					break;
				}
			}

		}
	}

	else if( aQualifiedNameID.find('.') == std::string::npos )
	{
		switch( op )
		{
			case AVM_OPCODE_INPUT:
			case AVM_OPCODE_INPUT_ENV:
			case AVM_OPCODE_INPUT_RDV:
			{
				if( XQuery.getPortByQualifiedNameID(aQualifiedNameID,
						listofPort, Modifier::DIRECTION_INPUT_KIND, false) )
				{
					object = NULL;

					ListOfSymbol::iterator itPort = listofPort.begin();
					ListOfSymbol::iterator endPort = listofPort.end();
					for( ; itPort != endPort ; ++itPort )
					{
						if( (*itPort).getModifier().isDirectionInput() )
						{
							object = (*itPort).rawPort();
							break;
						}
						else if( (object == NULL)
							&& (*itPort).getModifier().isDirectionInout() )
						{
							object = (*itPort).rawPort();
						}
					}
				}

				break;
			}

			case AVM_OPCODE_OUTPUT:
			case AVM_OPCODE_OUTPUT_ENV:
			case AVM_OPCODE_OUTPUT_RDV:
			{
				if( XQuery.getPortByQualifiedNameID(aQualifiedNameID,
						listofPort, Modifier::DIRECTION_OUTPUT_KIND, false) )
				{
					object = NULL;

					ListOfSymbol::iterator itPort = listofPort.begin();
					ListOfSymbol::iterator endPort = listofPort.end();
					for( ; itPort != endPort ; ++itPort )
					{
						if( (*itPort).getModifier().isDirectionOutput() )
						{
							object = (*itPort).rawPort();
							break;
						}
						else if( (object == NULL)
							&& (*itPort).getModifier().isDirectionInout() )
						{
							object = (*itPort).rawPort();
						}
					}
				}

				break;
			}

			default:
			{
				XQuery.getPortByQualifiedNameID(aQualifiedNameID, listofPort);

				configurePort(op, listofPort, otherTracePoint);

				break;
			}
		}
	}

	else
	{
		switch( op )
		{
			case AVM_OPCODE_INPUT:
			case AVM_OPCODE_INPUT_ENV:
			case AVM_OPCODE_INPUT_RDV:
			{
				if( XQuery.getPortByNameID(aQualifiedNameID,
						listofPort,Modifier::DIRECTION_INPUT_KIND, false) )
				{
					object = NULL;

					ListOfSymbol::iterator itPort = listofPort.begin();
					ListOfSymbol::iterator endPort = listofPort.end();
					for( ; itPort != endPort ; ++itPort )
					{
						if( (*itPort).getModifier().isDirectionInput() )
						{
							object = (*itPort).rawPort();
							break;
						}
						else if( (object == NULL)
								&& (*itPort).getModifier().isDirectionInout() )
						{
							object = (*itPort).rawPort();
						}
					}
				}

				break;
			}

			case AVM_OPCODE_OUTPUT:
			case AVM_OPCODE_OUTPUT_ENV:
			case AVM_OPCODE_OUTPUT_RDV:
			{
				if( XQuery.getPortByNameID(
						aQualifiedNameID, listofPort,
						Modifier::DIRECTION_OUTPUT_KIND, false) )
				{
					object = NULL;

					ListOfSymbol::iterator itPort = listofPort.begin();
					ListOfSymbol::iterator endPort = listofPort.end();
					for( ; itPort != endPort ; ++itPort )
					{
						if( (*itPort).getModifier().isDirectionOutput() )
						{
							object = (*itPort).rawPort();
							break;
						}
						else if( (object == NULL)
							&& (*itPort).getModifier().isDirectionInout() )
						{
							object = (*itPort).rawPort();
						}
					}
				}

				break;
			}

			default:
			{
				XQuery.getPortByNameID(aQualifiedNameID, listofPort);

				configurePort(op, listofPort, otherTracePoint);

				break;
			}
		}
	}

	return( object != NULL );
}

void TracePoint::configurePort(AVM_OPCODE opCom,
		ListOfSymbol & listofPort, ListOfTracePoint & otherTracePoint)
{
	if( listofPort.nonempty() )
	{
		op = opCom;
		object = listofPort.front().rawPort();
		listofPort.pop_front();
	}

	while( listofPort.nonempty() )
	{
		TracePoint * newTracePoint = new TracePoint( this );
		newTracePoint->object = listofPort.front().rawPort();
		listofPort.pop_front();

		otherTracePoint.append( newTracePoint );
	}
}


bool TracePoint::configureTransition(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	ExecutableQuery XQuery( aConfiguration );

	std::string::size_type pos = aQualifiedNameID.find("->");

	if( pos != std::string::npos )
	{
		std::string mid = aQualifiedNameID.substr(0, pos);
		std::string obj = aQualifiedNameID.substr(pos + 2);

		updateMachine(aConfiguration, mid);

		if( obj == "[*]" )
		{
			any_object = true;

			return( true );
		}

		if( machine != NULL )
		{
			object = machine->getExecutable()->getTransitionByNameID(
					obj ).to_ptr< ObjectElement >();
		}
		else
		{
			object = XQuery.getTransitionByNameID(
					obj ).to_ptr< ObjectElement >();
		}
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	else if( aQualifiedNameID.find('.') == std::string::npos )
	{
		object = XQuery.getTransitionByNameID(
				aQualifiedNameID ).to_ptr< ObjectElement >();
	}
	else
	{
		object = XQuery.getTransitionByQualifiedNameID(
				aQualifiedNameID ).to_ptr< ObjectElement >();
	}

	return( object != NULL );
}


bool TracePoint::configureRoutine(const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	std::string::size_type pos = aQualifiedNameID.find("->");

	if( pos != std::string::npos )
	{
		std::string mid = aQualifiedNameID.substr(0, pos);
		std::string obj = aQualifiedNameID.substr(pos + 2);

		updateMachine(aConfiguration, mid);

		if( obj == "[*]" )
		{
			any_object = true;

			return( true );
		}

		if( machine != NULL )
		{
			ExecutableForm * anExec = machine->getExecutable();

			if( obj == "init" )
			{
				op = AVM_OPCODE_INIT;
				object = &( anExec->getOnInitRoutine() );
			}
			else if( obj == "final" )
			{
				op = AVM_OPCODE_FINAL;
				object = &( anExec->getOnFinalRoutine() );
			}

			else if( obj == "start" )
			{
				op = AVM_OPCODE_START;
				object = &( anExec->getOnStartRoutine() );
			}
			else if( obj == "stop" )
			{
				op = AVM_OPCODE_STOP;
				object = &( anExec->getOnStopRoutine() );
			}

			else if( obj == "ienable" )
			{
				op = AVM_OPCODE_IENABLE_INVOKE;
				object = &( anExec->getOnIEnableRoutine() );
			}
			else if( obj == "enable" )
			{
				op = AVM_OPCODE_ENABLE_INVOKE;
				object = &( anExec->getOnEnableRoutine() );
			}

			else if( obj == "idisable" )
			{
				op = AVM_OPCODE_IDISABLE_INVOKE;
				object = &( anExec->getOnIDisableRoutine() );
			}
			else if( obj == "disable" )
			{
				op = AVM_OPCODE_DISABLE_INVOKE;
				object = &( anExec->getOnDisableRoutine() );
			}
			else if( obj == "iabort" )
			{
				op = AVM_OPCODE_IABORT_INVOKE;
				object = &( anExec->getOnIAbortRoutine() );
			}
			else if( obj == "abort" )
			{
				op = AVM_OPCODE_ABORT_INVOKE;
				object = &( anExec->getOnAbortRoutine() );
			}

			else if( obj == "irun" )
			{
				op = AVM_OPCODE_IRUN;
				object = &( anExec->getOnIRunRoutine() );
			}
			else if( obj == "run" )
			{
				op = AVM_OPCODE_RUN;
				object = &( anExec->getOnRunRoutine() );
			}
			else if( obj == "rtc" )
			{
				op = AVM_OPCODE_RTC;
				object = &( anExec->getOnRtcRoutine() );
			}

			else if( obj == "schedule" )
			{
				op = AVM_OPCODE_SCHEDULE_INVOKE;
				object = &( anExec->getOnScheduleRoutine() );
			}
			else if( obj == "concurrency" )
			{
				op = AVM_OPCODE_SCHEDULE_INVOKE;
				object = &( anExec->getOnConcurrencyRoutine() );
			}
		}
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	return( object != NULL );
}


bool TracePoint::configureRunnable(const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	std::string::size_type pos = aQualifiedNameID.find("->");

	if( pos != std::string::npos )
	{
		std::string mid = aQualifiedNameID.substr(0, pos);
		std::string obj = aQualifiedNameID.substr(pos + 2);

		updateMachine(aConfiguration, mid);

		if( obj == "[*]" )
		{
			any_object = true;

			return( true );
		}

		if( machine != NULL )
		{
			ExecutableForm * anExec = machine->getExecutable();

			if( obj == "init" )
			{
				op = AVM_OPCODE_INIT;
				object = &( anExec->getOnInitRoutine() );
			}
			else if( obj == "final" )
			{
				op = AVM_OPCODE_FINAL;
				object = &( anExec->getOnFinalRoutine() );
			}

			else if( obj == "start" )
			{
				op = AVM_OPCODE_START;
				object = &( anExec->getOnStartRoutine() );
			}
			else if( obj == "stop" )
			{
				op = AVM_OPCODE_STOP;
				object = &( anExec->getOnStopRoutine() );
			}

			else if( obj == "ienable" )
			{
				op = AVM_OPCODE_IENABLE_INVOKE;
				object = &( anExec->getOnIEnableRoutine() );
			}
			else if( obj == "enable" )
			{
				op = AVM_OPCODE_ENABLE_INVOKE;
				object = &( anExec->getOnEnableRoutine() );
			}

			else if( obj == "idisable" )
			{
				op = AVM_OPCODE_IDISABLE_INVOKE;
				object = &( anExec->getOnIDisableRoutine() );
			}
			else if( obj == "disable" )
			{
				op = AVM_OPCODE_DISABLE_INVOKE;
				object = &( anExec->getOnDisableRoutine() );
			}
			else if( obj == "iabort" )
			{
				op = AVM_OPCODE_IABORT_INVOKE;
				object = &( anExec->getOnIAbortRoutine() );
			}
			else if( obj == "abort" )
			{
				op = AVM_OPCODE_ABORT_INVOKE;
				object = &( anExec->getOnAbortRoutine() );
			}

			else if( obj == "irun" )
			{
				op = AVM_OPCODE_IRUN;
				object = &( anExec->getOnIRunRoutine() );
			}
			else if( obj == "run" )
			{
				op = AVM_OPCODE_RUN;
				object = &( anExec->getOnRunRoutine() );
			}
			else if( obj == "rtc" )
			{
				op = AVM_OPCODE_RTC;
				object = &( anExec->getOnRtcRoutine() );
			}

			else if( obj == "schedule" )
			{
				op = AVM_OPCODE_SCHEDULE_INVOKE;
				object = &( anExec->getOnScheduleRoutine() );
			}
			else if( obj == "concurrency" )
			{
				op = AVM_OPCODE_SCHEDULE_INVOKE;
				object = &( anExec->getOnConcurrencyRoutine() );
			}
		}
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	return( object != NULL );
}


bool TracePoint::configureMachine(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	std::string::size_type pos = aQualifiedNameID.find("->");

	if( pos != std::string::npos )
	{
		std::string mid = aQualifiedNameID.substr(0, pos);
		std::string obj = aQualifiedNameID.substr(pos + 2);

		updateMachine(aConfiguration, mid);

		if( obj == "[*]" )
		{
			any_object = true;

			return( true );
		}

		if( machine != NULL )
		{
			ExecutableForm * containerExecutable = machine->getExecutable();

			while( containerExecutable != NULL )
			{
				object = containerExecutable->getPort().getByNameID(obj).rawPort();

				if( object == NULL )
				{
					containerExecutable =
							containerExecutable->getExecutableContainer();
				}
				else
				{
					break;
				}
			}
		}
		else
		{
			ExecutableQuery XQuery( aConfiguration );

			object = machine = XQuery.getMachineByQualifiedNameID(
				Specifier::DESIGN_INSTANCE_KIND, mid + "." + obj).rawMachine();
		}
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	else
	{
		updateMachine(aConfiguration, aQualifiedNameID);

		object = machine;
	}

	return( object != NULL );
}


bool TracePoint::configureVariable(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	ExecutableQuery XQuery( aConfiguration );

	std::string::size_type pos = aQualifiedNameID.find("->");

	if( pos != std::string::npos )
	{
		std::string mid = aQualifiedNameID.substr(0, pos);
		std::string obj = aQualifiedNameID.substr(pos + 2);

		updateMachine(aConfiguration, mid);

		if( obj == "[*]" )
		{
			any_object = true;

			return( true );
		}

		if( machine != NULL )
		{
			object = machine->getExecutable()->getData().rawByNameID( obj );
		}
		else
		{
			object = XQuery.getDataByNameID( obj ).to_ptr< InstanceOfData >();
		}
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	else if( aQualifiedNameID.find('.') == std::string::npos )
	{
		object = XQuery.getDataByNameID(
				aQualifiedNameID ).to_ptr< InstanceOfData >();
	}
	else
	{
		object = XQuery.getDataByQualifiedNameID(
				aQualifiedNameID ).to_ptr< InstanceOfData >();
	}

	return( object != NULL );
}


bool TracePoint::configureBuffer(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	ExecutableQuery XQuery( aConfiguration );

	std::string::size_type pos = aQualifiedNameID.find("->");

	if( pos != std::string::npos )
	{
		std::string mid = aQualifiedNameID.substr(0, pos);
		std::string obj = aQualifiedNameID.substr(pos + 2);

		updateMachine(aConfiguration, mid);

		if( obj == "[*]" )
		{
			any_object = true;

			return( true );
		}

		if( machine != NULL )
		{
			object = machine->getExecutable()
					->getBuffer().getByNameID(obj).rawBuffer();
		}
		else
		{
			object = XQuery.getBufferByNameID( obj ).rawBuffer();
		}
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	else if( aQualifiedNameID.find('.') == std::string::npos )
	{
		object = XQuery.getBufferByNameID( aQualifiedNameID ).rawBuffer();
	}
	else
	{
		object = XQuery.getBufferByQualifiedNameID(
				aQualifiedNameID ).rawBuffer();
	}

	return( object != NULL );
}



/**
 * GETTER / SETTER
 * op
 */
AVM_OPCODE  TracePoint::to_kind(const std::string & id)
{
	if( id == "time"       ) return AVM_OPCODE_TIMED_GUARD;

	if( id == "formula"    ) return AVM_OPCODE_GUARD;

	if( id == "assign"     ) return AVM_OPCODE_ASSIGN;
	if( id == "newfresh"   ) return AVM_OPCODE_ASSIGN_NEWFRESH;

	if( id == "input"      ) return AVM_OPCODE_INPUT;

	if( REGEX_MATCH(id, CONS_WID2("input", "env")) ) return AVM_OPCODE_INPUT_ENV;
	if( REGEX_MATCH(id, CONS_WID2("input", "rdv")) ) return AVM_OPCODE_INPUT_RDV;

	if( id == "output"     ) return AVM_OPCODE_OUTPUT;

	if( REGEX_MATCH(id, CONS_WID2("output", "env")) ) return AVM_OPCODE_OUTPUT_ENV;
	if( REGEX_MATCH(id, CONS_WID2("output", "rdv")) ) return AVM_OPCODE_OUTPUT_RDV;

	return AVM_OPCODE_NULL;
}


AVM_OPCODE TracePoint::to_op(AVM_OPCODE op)
{
	switch( op )
	{
		case AVM_OPCODE_ASSIGN:
		case AVM_OPCODE_ASSIGN_AFTER:
		case AVM_OPCODE_ASSIGN_OP_AFTER:
		case AVM_OPCODE_ASSIGN_REF:
		case AVM_OPCODE_ASSIGN_MACRO:
		case AVM_OPCODE_ASSIGN_RESET:
		{
			return( AVM_OPCODE_ASSIGN );
		}

		case AVM_OPCODE_INPUT:
		case AVM_OPCODE_INPUT_FROM:
		{
			return( AVM_OPCODE_INPUT );
		}

		case AVM_OPCODE_OUTPUT:
		case AVM_OPCODE_OUTPUT_TO:
		{
			return( AVM_OPCODE_OUTPUT );
		}


		case AVM_OPCODE_INPUT_ENV:
		case AVM_OPCODE_OUTPUT_ENV:

		case AVM_OPCODE_INPUT_RDV:
		case AVM_OPCODE_OUTPUT_RDV:

		case AVM_OPCODE_ASSIGN_NEWFRESH:

		case AVM_OPCODE_TIMED_GUARD:
		case AVM_OPCODE_GUARD:

		case AVM_OPCODE_INVOKE_NEW:
		case AVM_OPCODE_INVOKE_ROUTINE:
		case AVM_OPCODE_INVOKE_TRANSITION:

		case AVM_OPCODE_INIT:
		case AVM_OPCODE_FINAL:

		case AVM_OPCODE_START:
		case AVM_OPCODE_STOP:

		case AVM_OPCODE_IENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_INVOKE:

		case AVM_OPCODE_IDISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_INVOKE:

		case AVM_OPCODE_IABORT_INVOKE:
		case AVM_OPCODE_ABORT_INVOKE:

		case AVM_OPCODE_IRUN:
		case AVM_OPCODE_RUN:
		case AVM_OPCODE_RTC:

		case AVM_OPCODE_SCHEDULE_INVOKE:

		case AVM_OPCODE_DEFER_INVOKE:
		{
			return( op );
		}

		default:
		{
			return( AVM_OPCODE_NULL );
		}
	}
}


std::string  TracePoint::to_string(AVM_OPCODE op)
{
	switch( op )
	{
		case AVM_OPCODE_TIMED_GUARD       : return( "time" );

		case AVM_OPCODE_CHECK_SAT         : return( "check_sat" );
		case AVM_OPCODE_GUARD             : return( "guard"     );

		case AVM_OPCODE_SELECT            : return( "select"    );

		case AVM_OPCODE_ASSIGN            : return( "assign"    );

		case AVM_OPCODE_ASSIGN_NEWFRESH   : return( "newfresh"  );

		case AVM_OPCODE_INPUT             : return( "input"     );
		case AVM_OPCODE_INPUT_ENV         : return( "input#env" );
		case AVM_OPCODE_INPUT_FROM        : return( "input#from" );
		case AVM_OPCODE_INPUT_RDV         : return( "input#rdv" );

		case AVM_OPCODE_OUTPUT            : return( "output"     );
		case AVM_OPCODE_OUTPUT_ENV        : return( "output#env" );
		case AVM_OPCODE_OUTPUT_TO         : return( "output#to" );
		case AVM_OPCODE_OUTPUT_RDV        : return( "output#rdv" );

		case AVM_OPCODE_INVOKE_NEW        : return( "new"               );
		case AVM_OPCODE_INVOKE_ROUTINE    : return( "invoke#routine"    );
		case AVM_OPCODE_INVOKE_TRANSITION : return( "invoke#transition" );

		case AVM_OPCODE_INIT              : return( "init"  );
		case AVM_OPCODE_FINAL             : return( "final" );

		case AVM_OPCODE_START             : return( "start" );
		case AVM_OPCODE_STOP              : return( "stop"  );

		case AVM_OPCODE_IENABLE_INVOKE    : return( "ienable"    );
		case AVM_OPCODE_ENABLE_INVOKE     : return( "enable"     );
		case AVM_OPCODE_ENABLE_SET        : return( "enable#set" );

		case AVM_OPCODE_IDISABLE_INVOKE   : return( "idisable" );
		case AVM_OPCODE_DISABLE_INVOKE    : return( "disable"  );

		case AVM_OPCODE_IABORT_INVOKE     : return( "iabort" );
		case AVM_OPCODE_ABORT_INVOKE      : return( "abort"  );

		case AVM_OPCODE_IRUN              : return( "irun" );
		case AVM_OPCODE_RUN               : return( "run"  );
		case AVM_OPCODE_RTC               : return( "rtc"  );

		case AVM_OPCODE_SCHEDULE_INVOKE   : return( "schedule" );

		case AVM_OPCODE_DEFER_INVOKE      : return( "defer" );

		case AVM_OPCODE_EQ                : return( "eq"  );
		case AVM_OPCODE_SEQ               : return( "seq" );

		case AVM_OPCODE_NOT               : return( "not" );
		case AVM_OPCODE_AND               : return( "and" );
		case AVM_OPCODE_OR                : return( "or"  );
		case AVM_OPCODE_XOR               : return( "xor" );

		case AVM_OPCODE_PARALLEL          : return( ")|,|"   );
		case AVM_OPCODE_STRONG_SYNCHRONOUS: return( "|and|" );

		case AVM_OPCODE_NOP               : return( "nop"   );

		case AVM_OPCODE_NULL              : return( "<?op>" );

		default                           : return( "trace#op<unknown>" );
	}
}



void TracePoint::updateNatureOpcodeRID()
{
	if( (nature == ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE)
		&& (object != NULL) )
	{
		if( object->is< InstanceOfPort >() )
		{
			nature = ENUM_TRACE_POINT::to_nature(
					object->to< InstanceOfPort >()->getComPointNature() );
		}
		else if( object->is< InstanceOfData >() )
		{
			nature = ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE;
		}
	}
	else if( (nature == ENUM_TRACE_POINT::TRACE_MACHINE_NATURE)
			&& object->is< InstanceOfMachine >() )
	{
		InstanceOfMachine * machine = object->to< InstanceOfMachine >();

		if( machine->getSpecifier().isFamilyComponentState() )
		{
			nature = ENUM_TRACE_POINT::TRACE_STATE_NATURE;
		}
		else if( machine->getSpecifier().isComponentStatemachine() )
		{
			nature = ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE;
		}
	}


	if( config != NULL )
	{
		if( (op == AVM_OPCODE_NULL) && config->isAvmCode() )
		{
			op = to_op( config->getOptimizedOpCode() );
		}

		if( RID.invalid() )
		{
			RID = config->getRuntimeID();
		}
	}
}


/**
 * GETTER
 * machine
 * object
 */
ExecutableForm * TracePoint::getExecutable() const
{
	if( object != NULL )
	{
		if( object->is< InstanceOfMachine >() )
		{
			return( object->to< InstanceOfMachine >()->getExecutable() );
		}

		else if( object->is< BaseAvmProgram >() )
		{
			return( object->to< BaseAvmProgram >()->getExecutable() );
		}

		else if( machine != NULL )
		{
			return( machine->getExecutable() );
		}
		else if( object->is< BaseInstanceForm >() )
		{
			return( object->to< BaseInstanceForm >()->
					getContainer()->getExecutable() );
		}
	}

	else if( machine != NULL )
	{
		return( machine->getExecutable() );
	}

	return( NULL );
}


/**
 * GETTER / SETTER
 * value
 * vector of value
 */
void TracePoint::newArrayValue(avm_size_t aSize)
{
	value = new ArrayBF(TypeManager::UNIVERSAL, aSize);
}


const BF & TracePoint::val(avm_size_t offset) const
{
	if( value.invalid() )
	{
		return( BF::REF_NULL );
	}
	else if( value.is< ArrayBF >() )
	{
		if( offset < value.to_ptr< ArrayBF >()->size() )
		{
			return( value.to_ptr< ArrayBF >()->at( offset ) );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Out of range ( offset:" << offset
					<< " >= size:" << value.to_ptr< ArrayBF >()->size()
					<< " ) in read-access on array value of TracePoint !!!"
					<< std::endl
					<< to_stream( this )
					<< SEND_EXIT;

			return( value );
		}
	}
	else if(offset == 0)
	{
		return( value );
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Trying to access value in "
					"non-existing array TracePoint value !!!"
				<< SEND_EXIT;

		return( value );
	}
}


void TracePoint::val(avm_size_t offset, const BF & arg)
{
	if( value.invalid() )
	{
		AVM_OS_FATAL_ERROR_EXIT << "invalid value !!!" << SEND_EXIT;
	}
	else if( value.is< ArrayBF >() )
	{
		if( offset < value.to_ptr< ArrayBF >()->size() )
		{
			value.to_ptr< ArrayBF >()->set( offset, arg );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Out of range ( offset:" << offset
					<< " >= size:" << value.to_ptr< ArrayBF >()->size()
					<< " ) in write-access on array value of TracePoint !!!"
					<< std::endl
					<< to_stream( this )
					<< SEND_EXIT;
		}
	}
	else if( offset == 0 )
	{
		value = arg;
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "TracePoint::val:> Unexpected case !!!"
				<< SEND_EXIT;
	}
}


avm_size_t TracePoint::valCount() const
{
	if( value.invalid() )
	{
//		AVM_OS_FATAL_ERROR_EXIT << "invalid value !!!" << SEND_EXIT;
		return( 0 );
	}
	else if( value.is< ArrayBF >() )
	{
		return( value.to_ptr< ArrayBF >()->size() );
	}
	else
	{
		return( 1 );
	}
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

std::string TracePoint::strUID() const
{
	if( machine != NULL )
	{
		if( object != NULL )
		{
			return( OSS() << "tpid#" << tpid << "->"
					<< machine->getQualifiedNameID() << "->"
					<< object->getNameID() );
		}
	}

	if( object != NULL )
	{
		return( OSS() << "tpid#" << tpid << "->"
				<< object->getQualifiedNameID() );
	}
	else
	{
		return( OSS() << "tpid#" << tpid );
	}
}


void TracePoint::formatValueStream(OutStream & os) const
{
	if( value.invalid() )
	{
//		value.toStream( os );
//		os << "TracePoint::value<null>";
	}
	else if( object->is< InstanceOfData >() )
	{
		object->to< InstanceOfData >()->formatStream(os, value);
	}
	else if( object->is< InstanceOfPort >() )
	{
		object->to< InstanceOfPort >()->formatStream(os, value);
	}

	os << std::flush;
}


void TracePoint::toStream(OutStream & os) const
{
	os << TAB;

	if( RID.valid() )
	{
		os << "(+)";
	}

	if( tpid > 0 )
	{
		os << strID() << " ";
	}

	os << ENUM_TRACE_POINT::to_string(nature);
	switch( nature )
	{
		case ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE:
		case ENUM_TRACE_POINT::TRACE_COM_NATURE:
		case ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE:
		case ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE:
		case ENUM_TRACE_POINT::TRACE_PORT_NATURE:
		case ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE:
		case ENUM_TRACE_POINT::TRACE_TIME_NATURE:
		case ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE:
		case ENUM_TRACE_POINT::TRACE_BUFFER_NATURE:

		case ENUM_TRACE_POINT::TRACE_FORMULA_NATURE:
		case ENUM_TRACE_POINT::TRACE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_DECISION_NATURE:

		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF:

		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF:

		case ENUM_TRACE_POINT::TRACE_STATE_NATURE:
		case ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE:
		case ENUM_TRACE_POINT::TRACE_MACHINE_NATURE:
		{
			os << ":" << to_string(op) << " ";
			break;
		}

		case ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE:

		case ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE:

		case ENUM_TRACE_POINT::TRACE_STEP_HEADER_NATURE:
		case ENUM_TRACE_POINT::TRACE_STEP_BEGIN_NATURE:
		case ENUM_TRACE_POINT::TRACE_STEP_END_NATURE:

		case ENUM_TRACE_POINT::TRACE_INIT_HEADER_NATURE:
		case ENUM_TRACE_POINT::TRACE_INIT_BEGIN_NATURE:
		case ENUM_TRACE_POINT::TRACE_INIT_END_NATURE:

		case ENUM_TRACE_POINT::TRACE_COMMENT_NATURE:
		case ENUM_TRACE_POINT::TRACE_SEPARATOR_NATURE:
		case ENUM_TRACE_POINT::TRACE_NEWLINE_NATURE:
		case ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE:
		default:
		{
			os << " ";
			break;
		}
	}

	if( machine != NULL )
	{
		if( machine->getSpecifier().isDesignModel() )
		{
			os << "<model>" << machine->getFullyQualifiedNameID();
		}
		else if(RID.valid()  )
		{
			os << RID.getFullyQualifiedNameID();
		}
		else
		{
			os << machine->getFullyQualifiedNameID();
		}

		if( (object != NULL) && (object != machine) )
		{
			os << "->" << object->getNameID();
		}
		else if( any_object )
		{
			os << "->[*]";
		}
	}
	else if( object != NULL )
	{
		os << object->getFullyQualifiedNameID();
	}
	else if( any_object )
	{
		os << "[*]";
	}

	if( value.is< ArrayBF >() )
	{
		if( nature != ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE )
		{
			os << value.str();
		}
		else
		{
			os << "{" << EOL_INCR_INDENT;

			ArrayBF * valArray = value.to_ptr< ArrayBF >();
			avm_size_t endOffset = valArray->size();
			for( avm_size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				valArray->at(offset).toStream(os);
			}

			os << DECR_INDENT_TAB << "}";
		}
	}
	else if( value.valid() )
	{
		os << "[ " << value.str() << " ]";
	}


AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , COMPUTING , EC.isnotNull() )
	os << EOL_TAB;
	EC.traceMinimum(os);
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , COMPUTING )

	os << EOL_FLUSH;
}


void TracePoint::traceMinimum(OutStream & os) const
{
	os << TAB;

	if( RID.valid() )
	{
		os << "(+)";
	}

	if( tpid > 0 )
	{
		os << strID() << " ";
	}

	switch( nature )
	{
		case ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE:
		{
			os << to_string(op) << " ";
			break;
		}

		case ENUM_TRACE_POINT::TRACE_COM_NATURE:
		case ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE:
		case ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE:
		case ENUM_TRACE_POINT::TRACE_PORT_NATURE:
		case ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE:
		case ENUM_TRACE_POINT::TRACE_TIME_NATURE:
		case ENUM_TRACE_POINT::TRACE_BUFFER_NATURE:

		case ENUM_TRACE_POINT::TRACE_FORMULA_NATURE:
		case ENUM_TRACE_POINT::TRACE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_DECISION_NATURE:

		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF:

		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF:

		case ENUM_TRACE_POINT::TRACE_STATE_NATURE:
		case ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE:
		case ENUM_TRACE_POINT::TRACE_MACHINE_NATURE:
		{
			os << ENUM_TRACE_POINT::to_string(nature)
					<< ":" << to_string(op) << " ";
			break;
		}

		case ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE:
		{
			os << "var<" << to_string(op) << "> ";
			break;
		}


		case ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE:

		case ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE:

		case ENUM_TRACE_POINT::TRACE_STEP_HEADER_NATURE:
		case ENUM_TRACE_POINT::TRACE_STEP_BEGIN_NATURE:
		case ENUM_TRACE_POINT::TRACE_STEP_END_NATURE:

		case ENUM_TRACE_POINT::TRACE_INIT_HEADER_NATURE:
		case ENUM_TRACE_POINT::TRACE_INIT_BEGIN_NATURE:
		case ENUM_TRACE_POINT::TRACE_INIT_END_NATURE:

		case ENUM_TRACE_POINT::TRACE_COMMENT_NATURE:
		case ENUM_TRACE_POINT::TRACE_SEPARATOR_NATURE:
		case ENUM_TRACE_POINT::TRACE_NEWLINE_NATURE:
		case ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE:
		default:
		{
			break;
		}
	}

	if( machine != NULL )
	{
		if( machine->getSpecifier().isDesignModel() )
		{
			os << "<model>" << machine->getFullyQualifiedNameID();
		}
		else if( RID.valid() )
		{
			os << RID.getFullyQualifiedNameID();
		}
		else
		{
			os << machine->getFullyQualifiedNameID();
		}

		if( (object != NULL) && (object != machine) )
		{
			os << "->" << object->getNameID();
		}
		else if( any_object )
		{
			os << "->[*]";
		}
	}
	else if( object != NULL )
	{
		os << object->getFullyQualifiedNameID();
	}
	else if( any_object )
	{
		os << "[*]";
	}


	if( isCom() && value.is< ArrayBF >() )
	{
		os << value.str();
	}
	else if( value.is< ArrayBF >() )
	{
		os << "{";
		if( nature == ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE )
		{
			os << AVM_STR_INDENT;
		}

		ArrayBF * valArray = value.to_ptr< ArrayBF >();
		avm_size_t endOffset = valArray->size();
		for( avm_size_t offset = 0 ; offset < endOffset ; ++offset )
		{
			if( valArray->at(offset).is< TracePoint >() )
			{
				valArray->at(offset).to_ptr< TracePoint >()->traceMinimum(os);
			}
			else
			{
				os << " " << valArray->at(offset).str();
			}
		}

		if( nature == ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE )
		{
			os << END_INDENT;
		}
		os << " }";
	}
	else if( value.valid() )
	{
		os << "[ " << value.str() << " ]";
	}


AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , COMPUTING , EC.isnotNull() )
	os << EOL_TAB;
	EC.traceMinimum(os);
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , COMPUTING )

	os << EOL_FLUSH;
}


} /* namespace sep */

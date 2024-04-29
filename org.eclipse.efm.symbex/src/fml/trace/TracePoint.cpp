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

EC( ExecutionContext::nullref() ),
config( ExecutionConfiguration::nullref() ),

nature( aNature ),
op( anOP ),

RID( ),

machine( nullptr ),

object ( nullptr ),
any_object( false ),

value( aValue )
{
	//!! NOTHING
}


TracePoint::TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature,
		AVM_OPCODE anOP, bool isAnyObject)
: Element( CLASS_KIND_T( TracePoint ) ),
tpid( 0 ),

EC( ExecutionContext::nullref() ),
config( ExecutionConfiguration::nullref() ),

nature( aNature ),
op( anOP ),

RID( ),

machine( nullptr ),

object ( nullptr ),
any_object( isAnyObject ),

value( BF::REF_NULL )
{
	//!! NOTHING
}


TracePoint::TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature,
		AVM_OPCODE anOP, const InstanceOfMachine * aMachine,
		const ObjectElement * anObject, const BF & aValue)
: Element( CLASS_KIND_T( TracePoint ) ),
tpid( 0 ),

EC( ExecutionContext::nullref() ),
config( ExecutionConfiguration::nullref() ),

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


TracePoint::TracePoint(const ExecutionContext & anEC,
		ENUM_TRACE_POINT::TRACE_NATURE aNature,
		AVM_OPCODE anOP, const InstanceOfMachine * aMachine,
		const ObjectElement * anObject, const BF & aValue)
: Element( CLASS_KIND_T( TracePoint ) ),
tpid( 0 ),

EC( anEC ),
config( ExecutionConfiguration::nullref() ),

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
		const ObjectElement * anObject, const BF & aValue)
: Element( CLASS_KIND_T( TracePoint ) ),
tpid( 0 ),

EC( ExecutionContext::nullref() ),
config( ExecutionConfiguration::nullref() ),

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
 * Other
 */
TracePoint::TracePoint(const ExecutionContext & anEC,
		ENUM_TRACE_POINT::TRACE_NATURE aNature,
		AVM_OPCODE anOP, const BF & aValue)
: Element( CLASS_KIND_T( TracePoint ) ),
tpid( 0 ),

EC( anEC ),
config( ExecutionConfiguration::nullref() ),

nature( aNature ),
op( anOP ),

RID( ),

machine( nullptr ),

object ( nullptr ),
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

EC( ExecutionContext::nullref() ),
config( ExecutionConfiguration::nullref() ),
nature( aNature ),
op( AVM_OPCODE_NULL ),

machine( nullptr ),

object ( nullptr ),
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
config( ExecutionConfiguration::nullref() ),
nature( aNature ),
op( AVM_OPCODE_NULL ),

machine( nullptr ),

object ( nullptr ),
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
	if( RID.valid() || ((object == nullptr) && (machine == nullptr)))
	{
		return;
	}

	else if( object != nullptr )
	{
		if( object->is< InstanceOfMachine >() )
		{
			if( object->to_ptr< InstanceOfMachine >()->
					refExecutable().hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( object->to< InstanceOfMachine >() );
			}
		}

		else if( object->is< BaseAvmProgram >() )
		{
			if( object->to_ptr< BaseAvmProgram >()->
					refExecutable().hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID(
						object->to_ptr< BaseAvmProgram >()->refExecutable() );
			}
		}

		else if( machine != nullptr )
		{
			if( machine->refExecutable().hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( *machine );
			}
		}

		else if( object->is< BaseInstanceForm >() &&
				object->to_ptr< BaseInstanceForm >()->hasRuntimeContainerRID() )
		{
			RID = object->to_ptr< BaseInstanceForm >()->getRuntimeContainerRID();
		}
	}

	else if( machine != nullptr )
	{
		if( machine->refExecutable().hasSingleRuntimeInstance() )
		{
			RID = anED.getRuntimeID( *machine );
		}
	}

	else
	{
		const ExecutableForm & anExecutable = getExecutable();

		if( anExecutable.isnotNullref()
			&& anExecutable.hasSingleRuntimeInstance() )
		{
			RID = anED.getRuntimeID( anExecutable );

			if( RID.valid() )
			{
				machine = RID.getInstance();
			}
		}
	}
}


bool TracePoint::isValidPoint()
{
	if( (machine != nullptr) && (object != nullptr) )
	{
		ObjectElement * container = object->getContainer();
		for( ; container != nullptr ; container = container->getContainer() )
		{
			if( container == machine->getExecutable() )
			{
				return( true );
			}
		}
		return( false );
	}

	return( object != nullptr  );
}


std::size_t TracePoint::updateMachine(const Configuration & aConfiguration,
		const std::string & aQualifiedNameID, ListOfSymbol & listofMachine)
{
	ExecutableQuery XQuery( aConfiguration );

	std::size_t count = XQuery.getMachineByID(
			Specifier::DESIGN_INSTANCE_KIND, aQualifiedNameID, listofMachine);
	if( count == 0 )
	{
		count = XQuery.getMachineByID(
				Specifier::DESIGN_MODEL_KIND, aQualifiedNameID, listofMachine);
	}

	if( count == 1 )
	{
		machine = listofMachine.first().rawMachine();

		if( machine->refExecutable().hasSingleRuntimeInstance() )
		{
			RID = aConfiguration.getMainExecutionData().getRuntimeID( *machine );
		}
	}
	else if( count == 0 )
	{
		RID = aConfiguration.getMainExecutionData()
				.getRuntimeIDByQualifiedNameID(aQualifiedNameID);

		if( RID.valid() )
		{
			machine = RID.getInstance();

			ExecutableForm * executableContainer =
					machine->getExecutable()->getExecutableContainer();

			if( executableContainer != nullptr )
			{
				const Symbol & symbol = executableContainer->getInstanceStatic()
						.getByFQNameID( machine->getFullyQualifiedNameID() );

				if( symbol.valid() )
				{
					listofMachine.append( symbol );

					count = 1;
				}
			}
			else
			{
				const Symbol & symbol = XQuery.getMachine(
						Specifier::DESIGN_INSTANCE_KIND,
						machine->getFullyQualifiedNameID());

				if( symbol.valid() )
				{
					listofMachine.append( symbol );

					count = 1;
				}
			}
		}
	}

	return( count );
}

std::size_t TracePoint::updateMachine(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID,
		std::string & objectID, ListOfSymbol & listofMachine)
{
	std::string::size_type pos = aQualifiedNameID.find("->");
	if( pos != std::string::npos )
	{
		objectID = aQualifiedNameID.substr(pos + 2);

		return( updateMachine(aConfiguration,
				aQualifiedNameID.substr(0, pos), listofMachine) );
	}
	else if( ((pos = aQualifiedNameID.find(":" )) != std::string::npos)
		  || ((pos = aQualifiedNameID.find(".{")) != std::string::npos)
		  || ((pos = aQualifiedNameID.find(".[")) != std::string::npos)
		  || ((pos = aQualifiedNameID.find_last_of('.' )) != std::string::npos) )
	{
		objectID = aQualifiedNameID.substr(pos + 1);

		return( updateMachine(aConfiguration,
				aQualifiedNameID.substr(0, pos), listofMachine) );
	}
	else
	{
		objectID = aQualifiedNameID;

		return 0;
	}
}


bool TracePoint::isRegexPoint(std::string & objectID, AVM_OPCODE & op)
{
	const std::size_t aSize = objectID.size();
	if( aSize >= 4 )
	{
		if( (objectID[0] == '{') && (objectID[aSize - 1] == '}') )
		{
			objectID = objectID.substr(1, aSize - 2);

			op = AVM_OPCODE_OR;

			return true;
		}
		else if( (objectID[0] == '[') && (objectID[aSize - 1] == ']') )
		{
			objectID = objectID.substr(1, aSize - 2);


			op = AVM_OPCODE_AND;

			return true;
		}
	}

	return false;
}

void TracePoint::configureComposite(BFList listofObject,
		std::size_t aSize, AVM_OPCODE regexOpcode, AVM_OPCODE opcode)
{
	if( aSize == 1 )
	{
		this->object = listofObject.first().to_ptr< ObjectElement >();
	}
	else if( aSize >= 2 )
	{
		ArrayBF * anArray = new ArrayBF(TypeManager::UNIVERSAL, aSize);

		TracePoint * newTracePoint = nullptr;
		aSize = 0;
		for( const auto & it : listofObject )
		{
			anArray->set(aSize++, BF(newTracePoint = new TracePoint( this )));

			newTracePoint->op = opcode;
			newTracePoint->object = it.to_ptr< ObjectElement >();

		}

		this->value = anArray;

		this->nature = ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE;
		this->op = regexOpcode;
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

	ExecutableQuery XQuery( aConfiguration );

	ListOfSymbol listofPort;
	std::string objectID;
	AVM_OPCODE regexOpcode;

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
	else if( isRegexPoint(objectID = aQualifiedNameID, regexOpcode) )
	{
		std::size_t count = XQuery.getPortByREGEX(objectID, listofPort);

		if( count > 0 )
		{
			configurePort(op, listofPort, otherTracePoint);

			return( true );
		}

		return( false );
	}

	Modifier::DIRECTION_KIND portDirection;
	switch( op )
	{
		case AVM_OPCODE_INPUT:
		case AVM_OPCODE_INPUT_ENV:
		case AVM_OPCODE_INPUT_RDV:
			portDirection = Modifier::DIRECTION_INPUT_KIND;
			break;

		case AVM_OPCODE_OUTPUT:
		case AVM_OPCODE_OUTPUT_ENV:
		case AVM_OPCODE_OUTPUT_RDV:
			portDirection = Modifier::DIRECTION_OUTPUT_KIND;
			break;

		default:
			portDirection = Modifier::DIRECTION_UNDEFINED_KIND;
			break;
	}

	ListOfSymbol listofMachine;
	if( updateMachine(aConfiguration,
			aQualifiedNameID, objectID, listofMachine) > 0 )
	{
		if( objectID.empty() || (objectID == "[*]") )
		{
			any_object = true;

			return( true );
		}
		else if( isRegexPoint(objectID, regexOpcode) )
		{
			std::size_t count = XQuery.getPortByNameREGEX(
					machine->refExecutable(), objectID, listofPort);

			if( count > 0 )
			{
				configurePort(op, listofPort, otherTracePoint);

				return( true );
			}

			return( false );
		}

		const ExecutionData & anED = aConfiguration.getMainExecutionData();

		do
		{
			machine = listofMachine.pop_first().rawMachine();
			if( machine->refExecutable().hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( *machine );
			}

			ExecutableForm * containerExecutable = machine->getExecutable();

			while( containerExecutable != nullptr )
			{
				object = XQuery.getPortByID(
						(* containerExecutable), objectID ).rawPort();

				if( object == nullptr )
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
		while( listofMachine.nonempty() && (object == nullptr) );
	}

	else if( portDirection != Modifier::DIRECTION_UNDEFINED_KIND )
	{
		if( XQuery.getPortByID(aQualifiedNameID,
				listofPort, portDirection, false) > 0 )
		{
			object = nullptr;

			for( const auto & itPort : listofPort )
			{
				if( itPort.getModifier().isDirectionKind(portDirection) )
				{
					object = itPort.rawPort();
					break;
				}
				else if( (object == nullptr)
					&& itPort.getModifier().isDirectionInout() )
				{
					object = itPort.rawPort();
				}
			}
		}
	}
	else
	{
		XQuery.getPortByID(aQualifiedNameID, listofPort);

		configurePort(op, listofPort, otherTracePoint);
	}

	return( isValidPoint()  );
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

	std::string objectID;
	ListOfSymbol listofMachine;
	AVM_OPCODE regexOpcode;

	if( updateMachine(aConfiguration,
			aQualifiedNameID, objectID, listofMachine) > 0 )
	{
		const ExecutionData & anED = aConfiguration.getMainExecutionData();

		machine = listofMachine.first().rawMachine();
		if( RID.invalid()
			&& machine->refExecutable().hasSingleRuntimeInstance() )
		{
			RID = anED.getRuntimeID( *machine );
		}

		if( objectID.empty() || (objectID == "[*]") )
		{

			any_object = true;

			return( true );
		}
		else if( isRegexPoint(objectID, regexOpcode) )
		{
			BFList listofObject;

			std::size_t count = XQuery.getTransitionByNameREGEX(
					machine->refExecutable(), objectID, listofObject);

			if( count > 0 )
			{
				configureComposite(listofObject, count,
						regexOpcode, AVM_OPCODE_INVOKE_TRANSITION);

				return( true );
			}

			return( false );
		}

		do
		{
			machine = listofMachine.pop_first().rawMachine();
			if( RID.invalid()
				&& machine->refExecutable().hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( *machine );
			}

			BFList listofTransition;

			std::size_t count = XQuery.getTransitionByID( machine->refExecutable(),
					objectID, listofTransition );
			if( count == 1 )
			{
				object = listofTransition.first().to_ptr< ObjectElement >();
			}
		}
		while( listofMachine.nonempty() && (object == nullptr) );

		if( object == nullptr )
		{
			object = XQuery.getTransitionByID(
					objectID ).to_ptr< ObjectElement >();

//			if( (machine != null)
//				&& machine->refExecutable().hasSingleRuntimeInstance() )
//			{
//				machine = nullptr;
//			}
		}
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	else if( isRegexPoint(objectID = aQualifiedNameID, regexOpcode) )
	{
		BFList listofObject;

		std::size_t count = XQuery.getTransitionByREGEX(objectID, listofObject);

		if( count > 0 )
		{
			configureComposite(listofObject, count,
					regexOpcode, AVM_OPCODE_INVOKE_TRANSITION);

			return( true );
		}

		return( false );
	}

	else
	{
		object = XQuery.getTransitionByID(
				aQualifiedNameID ).to_ptr< ObjectElement >();
	}

	return( isValidPoint()  );
}


bool TracePoint::configureRoutine(const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	std::string objectID;
	ListOfSymbol listofMachine;
	if( updateMachine(aConfiguration,
			aQualifiedNameID, objectID, listofMachine) > 0 )
	{
		if( objectID.empty() || (objectID == "[*]") )
		{
			any_object = true;

			return( true );
		}

		const ExecutionData & anED = aConfiguration.getMainExecutionData();

		do
		{
			machine = listofMachine.pop_first().rawMachine();

			const ExecutableForm & anExec = machine->refExecutable();

			if( RID.invalid() && anExec.hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( *machine );
			}

			if( objectID == "init" )
			{
				op = AVM_OPCODE_INIT;
				object = &( anExec.getOnInitRoutine() );
			}
			else if( objectID == "final" )
			{
				op = AVM_OPCODE_FINAL;
				object = &( anExec.getOnFinalRoutine() );
			}

			else if( objectID == "start" )
			{
				op = AVM_OPCODE_START;
				object = &( anExec.getOnStartRoutine() );
			}
			else if( objectID == "stop" )
			{
				op = AVM_OPCODE_STOP;
				object = &( anExec.getOnStopRoutine() );
			}

			else if( objectID == "ienable" )
			{
				op = AVM_OPCODE_IENABLE_INVOKE;
				object = &( anExec.getOnIEnableRoutine() );
			}
			else if( objectID == "enable" )
			{
				op = AVM_OPCODE_ENABLE_INVOKE;
				object = &( anExec.getOnEnableRoutine() );
			}

			else if( objectID == "idisable" )
			{
				op = AVM_OPCODE_IDISABLE_INVOKE;
				object = &( anExec.getOnIDisableRoutine() );
			}
			else if( objectID == "disable" )
			{
				op = AVM_OPCODE_DISABLE_INVOKE;
				object = &( anExec.getOnDisableRoutine() );
			}
			else if( objectID == "iabort" )
			{
				op = AVM_OPCODE_IABORT_INVOKE;
				object = &( anExec.getOnIAbortRoutine() );
			}
			else if( objectID == "abort" )
			{
				op = AVM_OPCODE_ABORT_INVOKE;
				object = &( anExec.getOnAbortRoutine() );
			}

			else if( objectID == "irun" )
			{
				op = AVM_OPCODE_IRUN;
				object = &( anExec.getOnIRunRoutine() );
			}
			else if( objectID == "run" )
			{
				op = AVM_OPCODE_RUN;
				object = &( anExec.getOnRunRoutine() );
			}
			else if( objectID == "rtc" )
			{
				op = AVM_OPCODE_RTC;
				object = &( anExec.getOnRtcRoutine() );
			}

			else if( objectID == "schedule" )
			{
				op = AVM_OPCODE_SCHEDULE_INVOKE;
				object = &( anExec.getOnScheduleRoutine() );
			}
			else if( objectID == "concurrency" )
			{
				op = AVM_OPCODE_SCHEDULE_INVOKE;
				object = &( anExec.getOnConcurrencyRoutine() );
			}
		}
		while( listofMachine.nonempty() && (object == nullptr) );
	}
	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	return( object != nullptr );
}


bool TracePoint::configureRunnable(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	std::string objectID;
	ListOfSymbol listofMachine;
	if( updateMachine(aConfiguration,
			aQualifiedNameID, objectID, listofMachine) > 0 )
	{
		if( objectID.empty() || (objectID == "[*]") )
		{
			any_object = true;

			return( true );
		}

		const ExecutionData & anED = aConfiguration.getMainExecutionData();

		do
		{
			machine = listofMachine.pop_first().rawMachine();

			const ExecutableForm & anExec = machine->refExecutable();

			if( RID.invalid() && anExec.hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( *machine );
			}

			if( objectID == "init" )
			{
				op = AVM_OPCODE_INIT;
				object = &( anExec.getOnInitRoutine() );
			}
			else if( objectID == "final" )
			{
				op = AVM_OPCODE_FINAL;
				object = &( anExec.getOnFinalRoutine() );
			}

			else if( objectID == "start" )
			{
				op = AVM_OPCODE_START;
				object = &( anExec.getOnStartRoutine() );
			}
			else if( objectID == "stop" )
			{
				op = AVM_OPCODE_STOP;
				object = &( anExec.getOnStopRoutine() );
			}

			else if( objectID == "ienable" )
			{
				op = AVM_OPCODE_IENABLE_INVOKE;
				object = &( anExec.getOnIEnableRoutine() );
			}
			else if( objectID == "enable" )
			{
				op = AVM_OPCODE_ENABLE_INVOKE;
				object = &( anExec.getOnEnableRoutine() );
			}

			else if( objectID == "idisable" )
			{
				op = AVM_OPCODE_IDISABLE_INVOKE;
				object = &( anExec.getOnIDisableRoutine() );
			}
			else if( objectID == "disable" )
			{
				op = AVM_OPCODE_DISABLE_INVOKE;
				object = &( anExec.getOnDisableRoutine() );
			}
			else if( objectID == "iabort" )
			{
				op = AVM_OPCODE_IABORT_INVOKE;
				object = &( anExec.getOnIAbortRoutine() );
			}
			else if( objectID == "abort" )
			{
				op = AVM_OPCODE_ABORT_INVOKE;
				object = &( anExec.getOnAbortRoutine() );
			}

			else if( objectID == "irun" )
			{
				op = AVM_OPCODE_IRUN;
				object = &( anExec.getOnIRunRoutine() );
			}
			else if( objectID == "run" )
			{
				op = AVM_OPCODE_RUN;
				object = &( anExec.getOnRunRoutine() );
			}
			else if( objectID == "rtc" )
			{
				op = AVM_OPCODE_RTC;
				object = &( anExec.getOnRtcRoutine() );
			}

			else if( objectID == "schedule" )
			{
				op = AVM_OPCODE_SCHEDULE_INVOKE;
				object = &( anExec.getOnScheduleRoutine() );
			}
			else if( objectID == "concurrency" )
			{
				op = AVM_OPCODE_SCHEDULE_INVOKE;
				object = &( anExec.getOnConcurrencyRoutine() );
			}
		}
		while( listofMachine.nonempty() && (object == nullptr) );
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	return( object != nullptr );
}


bool TracePoint::configureMachine(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	std::string objectID;
	ListOfSymbol listofMachine;
	if( updateMachine(aConfiguration,
			aQualifiedNameID, objectID, listofMachine) > 0 )
	{
		if( objectID.empty() || (objectID == "[*]") )
		{
			any_object = true;

			return( true );
		}

		ExecutableQuery XQuery( aConfiguration );

		const ExecutionData & anED = aConfiguration.getMainExecutionData();

		do
		{
			machine = listofMachine.pop_first().rawMachine();
			if( RID.invalid()
				&& machine->refExecutable().hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( *machine );
			}

			ExecutableForm * containerExecutable = machine->getExecutable();

			while( containerExecutable != nullptr )
			{
				object = XQuery.getMachineByID((* containerExecutable),
						Specifier::DESIGN_INSTANCE_KIND, objectID).rawMachine();

				if( object == nullptr )
				{
					containerExecutable =
							containerExecutable->getExecutableContainer();
				}
				else
				{
					if( machine->refExecutable().hasSingleRuntimeInstance() )
					{
						machine = object->to_ptr< InstanceOfMachine >();

						if( machine->refExecutable().hasSingleRuntimeInstance() )
						{
							RID = anED.getRuntimeID( *machine );
						}
					}

					break;
				}
			}
		}
		while( listofMachine.nonempty() && (object == nullptr) );

		if( object == nullptr )
		{
			ExecutableQuery XQuery( aConfiguration );

			std::string machineID = aQualifiedNameID;
			StringTools::replace(machineID, "->", ".");

			object = machine = XQuery.getMachineByQualifiedNameID(
				Specifier::DESIGN_INSTANCE_KIND, machineID).rawMachine();

			if( (machine != nullptr)
				&& machine->refExecutable().hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( *machine );
			}
		}
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	else
	{
		ListOfSymbol listofMachine;
		updateMachine(aConfiguration, aQualifiedNameID, listofMachine);

		object = machine;
	}

	return( object != nullptr );
}


bool TracePoint::configureVariable(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID,
		ListOfTracePoint & otherTracePoint)
{
	ExecutableQuery XQuery( aConfiguration );

	BFList listofVariable;
	AVM_OPCODE regexOpcode;

	std::string objectID;
	ListOfSymbol listofMachine;
	if( updateMachine(aConfiguration,
			aQualifiedNameID, objectID, listofMachine) > 0 )
	{
		if( objectID.empty() || (objectID == "[*]") )
		{
			any_object = true;

			return( true );
		}
		else if( isRegexPoint(objectID, regexOpcode) )
		{
			std::size_t count = XQuery.getVariableByNameREGEX(
					machine->refExecutable(), objectID, listofVariable);

			if( count > 0 )
			{
				configureVariable(listofVariable, otherTracePoint);

				return( true );
			}

			return( false );
		}

		const ExecutionData & anED = aConfiguration.getMainExecutionData();

		do
		{
			machine = listofMachine.pop_first().rawMachine();
			if( RID.invalid()
				&& machine->refExecutable().hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( *machine );
			}

			object = XQuery.getVariableByID( machine->refExecutable(),
					objectID ).to_ptr< InstanceOfData >();
		}
		while( listofMachine.nonempty() && (object == nullptr) );

		if( object == nullptr )
		{
			object = XQuery.getVariableByID(objectID).to_ptr< InstanceOfData >();

//			if( (machine != null)
//					&& machine->refExecutable().hasSingleRuntimeInstance() )
//			{
//				machine = nullptr;
//			}
		}
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}
	else if( isRegexPoint(objectID = aQualifiedNameID, regexOpcode) )
	{
		std::size_t count = XQuery.getVariableByREGEX(objectID, listofVariable);

		if( count > 0 )
		{
			configureVariable(listofVariable, otherTracePoint);

			return( true );
		}

		return( false );
	}

	else
	{
		XQuery.getVariableByID(aQualifiedNameID, listofVariable);

		configureVariable(listofVariable, otherTracePoint);
	}

	return( isValidPoint()  );
}


void TracePoint::configureVariable(
		BFList & listofVariable, ListOfTracePoint & otherTracePoint)
{
	if( listofVariable.nonempty() )
	{
		object = listofVariable.front().to_ptr< InstanceOfData >();
		listofVariable.pop_front();
	}

	while( listofVariable.nonempty() )
	{
		TracePoint * newTracePoint = new TracePoint( this );
		newTracePoint->object =
				listofVariable.front().to_ptr< InstanceOfData >();
		listofVariable.pop_front();

		otherTracePoint.append( newTracePoint );
	}
}



bool TracePoint::configureBuffer(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID)
{
	ExecutableQuery XQuery( aConfiguration );

	std::string objectID;
	ListOfSymbol listofMachine;
	if( updateMachine(aConfiguration,
			aQualifiedNameID, objectID, listofMachine) > 0 )
	{
		if( objectID.empty() || (objectID == "[*]") )
		{
			any_object = true;

			return( true );
		}

		const ExecutionData & anED = aConfiguration.getMainExecutionData();

		do
		{
			machine = listofMachine.pop_first().rawMachine();
			if( RID.invalid()
				&& machine->refExecutable().hasSingleRuntimeInstance() )
			{
				RID = anED.getRuntimeID( *machine );
			}

			object = XQuery.getBufferByID(
					machine->refExecutable(), objectID ).rawBuffer();
		}
		while( listofMachine.nonempty() && (object == nullptr) );

		if( object == nullptr )
		{
			object = XQuery.getBufferByID( objectID ).rawBuffer();

//			if( (machine != null)
//					&& machine->refExecutable().hasSingleRuntimeInstance() )
//			{
//				machine = nullptr;
//			}
		}
	}

	else if( aQualifiedNameID == "[*]" )
	{
		any_object = true;

		return( true );
	}

	else
	{
		object = XQuery.getBufferByID( aQualifiedNameID ).rawBuffer();
	}

	return( isValidPoint()  );
}


/**
 * TEST
 * nature / op
 */
bool TracePoint::isComposite() const
{
	return( (nature == ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE)
			&& value.is< ArrayBF >() );
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

		case AVM_OPCODE_TRACE:
		case AVM_OPCODE_DEBUG:
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

		case AVM_OPCODE_INFORMAL          : return( "informal" );

		case AVM_OPCODE_TRACE             : return( "@trace" );
		case AVM_OPCODE_DEBUG             : return( "@debug" );

		case AVM_OPCODE_NULL              : return( "<?op>" );

		default                           : return( "trace#op<unknown>" );
	}
}



void TracePoint::updateNatureOpcodeRID()
{
	if( (nature == ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE)
		&& (object != nullptr) )
	{
		if( object->is< InstanceOfPort >() )
		{
			nature = ENUM_TRACE_POINT::to_nature(
					object->to_ptr< InstanceOfPort >()->getComPointNature() );
		}
		else if( object->is< InstanceOfData >() )
		{
			nature = ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE;
		}
	}
	else if( (nature == ENUM_TRACE_POINT::TRACE_MACHINE_NATURE)
			&& object->is< InstanceOfMachine >() )
	{
		const InstanceOfMachine * machine = object->to_ptr< InstanceOfMachine >();

		if( machine->getSpecifier().isFamilyComponentState() )
		{
			nature = ENUM_TRACE_POINT::TRACE_STATE_NATURE;
		}
		else if( machine->getSpecifier().isComponentStatemachine() )
		{
			nature = ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE;
		}
	}


	if( config.isnotNullref() )
	{
		if( (op == AVM_OPCODE_NULL) && config.isAvmCode() )
		{
			op = to_op( config.getOptimizedOpCode() );
		}

		if( RID.invalid() )
		{
			RID = config.getRuntimeID();
		}
	}
}


/**
 * GETTER
 * machine
 * object
 */
const ExecutableForm & TracePoint::getExecutable() const
{
	if( object != nullptr )
	{
		if( object->is< InstanceOfMachine >() )
		{
			return( object->to_ptr< InstanceOfMachine >()->refExecutable() );
		}

		else if( object->is< BaseAvmProgram >() )
		{
			return( object->to_ptr< BaseAvmProgram >()->refExecutable() );
		}

		else if( machine != nullptr )
		{
			return( machine->refExecutable() );
		}
		else if( object->is< BaseInstanceForm >() )
		{
			return( object->to_ptr< BaseInstanceForm >()->
					getContainer()->refExecutable() );
		}
	}

	else if( machine != nullptr )
	{
		return( machine->refExecutable() );
	}

	return( ExecutableForm::nullref() );
}


/**
 * GETTER / SETTER
 * value
 * vector of value
 */
void TracePoint::newArrayValue(std::size_t aSize)
{
	value = new ArrayBF(TypeManager::UNIVERSAL, aSize);
}


const BF & TracePoint::val(std::size_t offset) const
{
	if( value.invalid() )
	{
		return( BF::REF_NULL );
	}
	else if( value.is< ArrayBF >() )
	{
		if( offset < value.to< ArrayBF >().size() )
		{
			return( value.to< ArrayBF >().at( offset ) );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Out of range ( offset:" << offset
					<< " >= size:" << value.to< ArrayBF >().size()
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


void TracePoint::val(std::size_t offset, const BF & arg)
{
	if( value.invalid() )
	{
		AVM_OS_FATAL_ERROR_EXIT << "invalid value !!!" << SEND_EXIT;
	}
	else if( value.is< ArrayBF >() )
	{
		if( offset < value.to< ArrayBF >().size() )
		{
			value.to_ptr< ArrayBF >()->set( offset, arg );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Out of range ( offset:" << offset
					<< " >= size:" << value.to< ArrayBF >().size()
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


std::size_t TracePoint::valCount() const
{
	if( value.invalid() )
	{
//		AVM_OS_FATAL_ERROR_EXIT << "invalid value !!!" << SEND_EXIT;
		return( 0 );
	}
	else if( value.is< ArrayBF >() )
	{
		return( value.to< ArrayBF >().size() );
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
	if( object != nullptr )
	{
		if( (machine != nullptr) && (machine != object) )
		{
			return( OSS() << "tpid#" << tpid << "->"
					<< machine->getQualifiedNameID() << "->"
					<< object->relativeQualifiedNameID(machine->refExecutable()) );
		}
		else if( RID.valid() )
		{
			if( RID.getInstance() != object )
			{
				return( OSS() << "tpid#" << tpid << "->"
						<< RID.getQualifiedNameID() << "->"
						<< object->relativeQualifiedNameID(RID.refExecutable()) );
			}
			else
			{
				return( OSS() << "tpid#" << tpid << "->"
						<< RID.getQualifiedNameID() );

			}
		}
		else
		{
			return( OSS() << "tpid#" << tpid << "->"
					<< object->getQualifiedNameID() );
		}
	}
	else
	{
		return( OSS() << "tpid#" << tpid );
	}
}


void TracePoint::formatValueStream(OutStream & out) const
{
	if( value.invalid() )
	{
//		value.toStream( out );
//		out << "TracePoint::value<null>";
	}
	else if( object->is< InstanceOfData >() )
	{
		object->to_ptr< InstanceOfData >()->formatStream(out, value);
	}
	else if( object->is< InstanceOfPort >() )
	{
		object->to_ptr< InstanceOfPort >()->formatStream(out, value);
	}

	else if( value.is< ArrayBF >() )
	{
		const ArrayBF & arrayValue = value.as< ArrayBF >();

		for( std::size_t offset = 0 ; offset < arrayValue.size() ; ++offset )
		{
			out << arrayValue[offset].str();
		}
	}
	else
	{
		out << value.str();
	}

	out << std::flush;
}


void TracePoint::toStream(OutStream & out) const
{
	out << TAB;

//AVM_IF_DEBUG_ENABLED_OR( tpid > 0 )

	out << strID() << " ";

//AVM_ENDIF_DEBUG_ENABLED

	if( RID.valid() && (nature != ENUM_TRACE_POINT::TRACE_MACHINE_NATURE) )
	{
//		out << "(+)";
		out << RID.strUniqId() << " ";
	}

	const std::string strNature = ENUM_TRACE_POINT::to_string(nature);

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
		{
			out << strNature << ":" << to_string(op) << " ";
			break;
		}

		case ENUM_TRACE_POINT::TRACE_MACHINE_NATURE:
		{
			if( RID.valid() && (machine == object)
				&& (RID.getInstance() == machine) )

			{
				out << strNature
					<< ( (op != AVM_OPCODE_RUN) ? ":" + to_string(op) : "" )
					<< " " << RID.getQualifiedNameID();
			}
			else if( RID.valid() )
			{
				out << RID.strUniqId() << " "
					<< strNature << ":" << to_string(op);
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE:

		case ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE:

		case ENUM_TRACE_POINT::TRACE_EXECUTION_INFORMATION_NATURE:

		case ENUM_TRACE_POINT::TRACE_META_TRACE_NATURE:
		case ENUM_TRACE_POINT::TRACE_META_DEBUG_NATURE:

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
			if( (machine != nullptr)
				|| (object == nullptr)
				|| ( (object != nullptr)
					&& (not StringTools::startsWith(
						object->getFullyQualifiedNameID(), strNature))) )
			{
				out << strNature << " ";
			}
			break;
		}
	}

	if( machine != nullptr )
	{
		if( machine->getSpecifier().isDesignModel() )
		{
			out << "<model>" << machine->getFullyQualifiedNameID();
		}
		else if( RID.valid() && (RID.getInstance() != machine) )
		{
			out << machine->getFullyQualifiedNameID();
		}

		if( (object != nullptr) && (object != machine) )
		{
			out << object->relativeQualifiedNameID( machine->refExecutable() );
		}
		else if( any_object )
		{
			out << "[*]";
		}
	}
	else if( object != nullptr )
	{
		if( RID.valid() && (RID.getInstance() != object) )
		{
			out << RID.getQualifiedNameID() << "->"
				<< object->relativeQualifiedNameID(RID.refExecutable());
		}
		else
		{
			out << object->getFullyQualifiedNameID();
		}
	}
	else if( any_object )
	{
		out << "[*]";
	}

	if( value.is< ArrayBF >() )
	{
		if( nature != ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE )
		{
			out << value.str();
		}
		else
		{
			out << "{" << EOL_INCR_INDENT;

			ArrayBF * valArray = value.to_ptr< ArrayBF >();
			std::size_t endOffset = valArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				valArray->at(offset).toStream(out);
			}

			out << DECR_INDENT_TAB << "}";
		}
	}
	else if( value.valid() )
	{
		out << "[ " << value.str() << " ]";
	}


AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , COMPUTING , EC.isnotNullref() )
	out << EOL_TAB;
	EC.traceMinimum(out);
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , COMPUTING )

	out << EOL_FLUSH;
}


} /* namespace sep */

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

#ifndef TRACEPOINT_H_
#define TRACEPOINT_H_


#include <common/Element.h>
#include <common/BF.h>

#include <collection/BFContainer.h>
#include <collection/List.h>

#include <fml/common/SpecifierElement.h>

#include <fml/lib/ITracePoint.h>

#include <fml/operator/OperatorLib.h>

#include <fml/symbol/Symbol.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{

class Configuration;

class ExecutableForm;
class ExecutionContext;
class ExecutionData;
class ExecutionConfiguration;

class InstanceOfMachine;

class ObjectElement;

class TraceFormatter;
class TracePoint;


/**
 * TYPEDEF
 */
typedef List< TracePoint * >  ListOfTracePoint;


class TracePoint : public Element ,
		AVM_INJECT_STATIC_NULL_REFERENCE( TracePoint ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TracePoint )
{

	AVM_DECLARE_CLONABLE_CLASS( TracePoint )


public:
	/**
	 * ATTRIBUTES
	 */
	std::size_t tpid;

	const ExecutionContext & EC;

	const ExecutionConfiguration & config;

	ENUM_TRACE_POINT::TRACE_NATURE nature;

	AVM_OPCODE op;


	RuntimeID RID;

	const InstanceOfMachine * machine;

	const ObjectElement     * object;
	bool any_object;

	BF value;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature,
			AVM_OPCODE anOP = AVM_OPCODE_NULL,
			const BF & aValue = BF::REF_NULL);

	TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature,
			AVM_OPCODE anOP, bool isAnyObject);

	TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature, AVM_OPCODE anOP,
			const InstanceOfMachine * aMachine, const ObjectElement * anObject,
			const BF & aValue = BF::REF_NULL);


	TracePoint(const ExecutionContext & anEC,
			ENUM_TRACE_POINT::TRACE_NATURE aNature,
			AVM_OPCODE anOP, const InstanceOfMachine * aMachine,
			const ObjectElement * anObject, const BF & aValue = BF::REF_NULL);


	TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature, AVM_OPCODE anOP,
			const RuntimeID & aRID, const ObjectElement * anObject,
			const BF & aValue = BF::REF_NULL);

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TracePoint(const TracePoint & aTracePoint)
	: Element( aTracePoint ),
	tpid( aTracePoint.tpid ),

	EC( aTracePoint.EC ),
	config( aTracePoint.config ),

	nature( aTracePoint.nature ),
	op( aTracePoint.op ),

	RID( aTracePoint.RID ),

	machine( aTracePoint.machine ),

	object( aTracePoint.object ),
	any_object( aTracePoint.any_object ),

	value( aTracePoint.value )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Other
	 */
	TracePoint(const ExecutionContext & anEC,
			ENUM_TRACE_POINT::TRACE_NATURE aNature,
			AVM_OPCODE anOP = AVM_OPCODE_NULL,
			const BF & aValue = BF::REF_NULL);

	TracePoint(const ExecutionContext & anEC,
			const ExecutionConfiguration & aConfig,
			ENUM_TRACE_POINT::TRACE_NATURE aNature,
			AVM_OPCODE anOP, const RuntimeID & aRID,
			const ObjectElement * anObject,
			const BF & aValue = BF::REF_NULL)
	: Element( CLASS_KIND_T( TracePoint ) ),
	tpid( 0 ),

	EC( anEC ),
	config( aConfig ),

	nature( aNature ),
	op( anOP ),

	RID( aRID ),

	machine( aRID.getInstance() ),

	object( anObject ),
	any_object( false ),

	value( aValue )
	{
		updateNatureOpcodeRID();
	}

	TracePoint(const ExecutionContext & anEC,
			const ExecutionConfiguration & aConfig,
			ENUM_TRACE_POINT::TRACE_NATURE aNature,
			AVM_OPCODE anOP, const InstanceOfMachine * aMachine,
			const ObjectElement * anObject, const BF & aValue = BF::REF_NULL)
	: Element( CLASS_KIND_T( TracePoint ) ),
	tpid( 0 ),

	EC( anEC ),
	config( aConfig ),

	nature( aNature ),
	op( anOP ),

	RID( ),

	machine( aMachine ),

	object( anObject ),
	any_object( false ),

	value( aValue )
	{
		updateNatureOpcodeRID();
	}


	TracePoint(const ExecutionContext & anEC,
			const ExecutionConfiguration & aConfig, const RuntimeID & aRID,
			const ObjectElement * anObject, const BF & aValue)
	: Element( CLASS_KIND_T( TracePoint ) ),
	tpid( 0 ),

	EC( anEC ),
	config( aConfig ),

	nature( ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE ),
	op( AVM_OPCODE_NULL ),

	RID( aRID ),

	machine( aRID.getInstance() ),

	object( anObject ),
	any_object( false ),

	value( aValue )
	{
		updateNatureOpcodeRID();
	}

	TracePoint(const TracePoint * aTP)
	: Element( CLASS_KIND_T( TracePoint ) ),
	tpid( 0 ),

	EC( aTP->EC ),
	config( aTP->config ),

	nature( aTP->nature ),
	op( aTP->op ),

	RID( ),

	machine( aTP->machine ),

	object( aTP->object ),
	any_object( false ),

	value( aTP->value )
	{
		updateNatureOpcodeRID();
	}

	/**
	 * CONSTRUCTOR
	 * for Meta point
	 * TRACE_COMMENT_NATURE
	 * TRACE_SEPARATOR_NATURE
	 * TRACE_NEWLINE_NATURE
	 * TRACE_STEP_NATURE
	 */
	TracePoint(ENUM_TRACE_POINT::TRACE_NATURE aNature,
			const std::string & strSeparator);

	TracePoint(const ExecutionContext & anEC,
			ENUM_TRACE_POINT::TRACE_NATURE aNature,
			const std::string & strSeparator);


	static TracePoint * newComposite(
			AVM_OPCODE anOP, const BF & aValue = BF::REF_NULL)
	{
		return( new TracePoint(
				ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE, anOP, aValue) );
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TracePoint()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static TracePoint & nullref()
	{
		static TracePoint _NULL_( ENUM_TRACE_POINT::TRACE_NULL_NATURE );

		return( _NULL_ );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	void updateRID(const ExecutionData & anED);

	bool isValidPoint();

	std::size_t updateMachine(
			const Configuration & aConfiguration,
			const std::string & aQualifiedNameID,
			ListOfSymbol & listofMachine);

	std::size_t updateMachine(
			const Configuration & aConfiguration,
			const std::string & aQualifiedNameID,
			std::string & objectID, ListOfSymbol & listofMachine);

	bool isRegexPoint(std::string & objectID, AVM_OPCODE & op);

	void configureComposite(BFList listofObject,
			std::size_t aSize, AVM_OPCODE regexOpcode, AVM_OPCODE opcode);

	bool configurePort(
			const Configuration & aConfiguration,
			const std::string & aQualifiedNameID,
			ListOfTracePoint & otherTracePoint);

	void configurePort(AVM_OPCODE opCom, ListOfSymbol & listofPort,
			ListOfTracePoint & otherTracePoint);

	bool configureTransition(
			const Configuration & aConfiguration,
			const std::string & aQualifiedNameID);

	bool configureRoutine(
			const Configuration & aConfiguration,
			const std::string & aQualifiedNameID);

	bool configureRunnable(
		const Configuration & aConfiguration,
		const std::string & aQualifiedNameID);

	bool configureMachine(
			const Configuration & aConfiguration,
			const std::string & aQualifiedNameID);

	bool configureVariable(
			const Configuration & aConfiguration,
			const std::string & aQualifiedNameID,
			ListOfTracePoint & otherTracePoint);

	void configureVariable(
			BFList & listofVariable, ListOfTracePoint & otherTracePoint);


	bool configureBuffer(
			const Configuration & aConfiguration,
			const std::string & aQualifiedNameID);


	/**
	 * GETTER / SETTER / TEST
	 * nature / op
	 */
	inline bool isVirtual() const
	{
		switch( nature )
		{
			case ENUM_TRACE_POINT::TRACE_COMMENT_NATURE:
			case ENUM_TRACE_POINT::TRACE_SEPARATOR_NATURE:
			case ENUM_TRACE_POINT::TRACE_NEWLINE_NATURE:

			case ENUM_TRACE_POINT::TRACE_STEP_HEADER_NATURE:
			case ENUM_TRACE_POINT::TRACE_STEP_BEGIN_NATURE:
			case ENUM_TRACE_POINT::TRACE_STEP_END_NATURE:

			case ENUM_TRACE_POINT::TRACE_INIT_HEADER_NATURE:
			case ENUM_TRACE_POINT::TRACE_INIT_BEGIN_NATURE:
			case ENUM_TRACE_POINT::TRACE_INIT_END_NATURE:
			{
				return( true );
			}
			default:
			{
				return( false );
			}
		}
	}

	bool isComposite() const;

	inline bool isAssign() const
	{
		return( (nature == ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE)
				&& (op == AVM_OPCODE_ASSIGN) );
	}

	inline bool isCom() const
	{
		switch( nature )
		{
			case ENUM_TRACE_POINT::TRACE_COM_NATURE:
			case ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE:
			case ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE:
			case ENUM_TRACE_POINT::TRACE_PORT_NATURE:
			case ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE:
			{
				return( true );
			}
			default:
			{
				switch( op )
				{
					case AVM_OPCODE_INPUT:
					case AVM_OPCODE_INPUT_BUFFER:
					case AVM_OPCODE_INPUT_FROM:
					case AVM_OPCODE_INPUT_ENV:
					case AVM_OPCODE_INPUT_MULTI_RDV:
					case AVM_OPCODE_INPUT_RDV:

					case AVM_OPCODE_OUTPUT:
					case AVM_OPCODE_OUTPUT_BUFFER:
					case AVM_OPCODE_OUTPUT_TO:
					case AVM_OPCODE_OUTPUT_ENV:
					case AVM_OPCODE_OUTPUT_MULTI_RDV:
					case AVM_OPCODE_OUTPUT_RDV:
					{
						return( true );
					}

					default:
					{
						return( false );
					}
				}
			}
		}
	}


	inline bool isComInput() const
	{
		switch( op )
		{
			case AVM_OPCODE_INPUT:
			case AVM_OPCODE_INPUT_BUFFER:
			case AVM_OPCODE_INPUT_FROM:
			case AVM_OPCODE_INPUT_ENV:
			case AVM_OPCODE_INPUT_MULTI_RDV:
			case AVM_OPCODE_INPUT_RDV:
			{
				return( true );
			}

			default:
			{
				return( false );
			}
		}
	}

	inline bool isComOutput() const
	{
		switch( op )
		{
			case AVM_OPCODE_OUTPUT:
			case AVM_OPCODE_OUTPUT_BUFFER:
			case AVM_OPCODE_OUTPUT_TO:
			case AVM_OPCODE_OUTPUT_ENV:
			case AVM_OPCODE_OUTPUT_MULTI_RDV:
			case AVM_OPCODE_OUTPUT_RDV:
			{
				return( true );
			}

			default:
			{
				return( false );
			}
		}
	}


	inline bool isCom(AVM_OPCODE opFamily, AVM_OPCODE opSpecific,
			const RuntimeID & rid, const ObjectElement & object) const
	{
		if( ((this->op == opSpecific)
				|| (this->op == opFamily)
				|| (this->op == AVM_OPCODE_NULL))
			&& ((this->object == (& object)) || this->any_object) )
		{
			if( this->RID.valid() )
			{
				return( rid.hasAsAncestor(* this->machine) );
			}
			else if( this->machine != nullptr )
			{
				return( rid.hasAsAncestor(* this->machine) );
			}

			return( true );
		}

		return( false );
	}

	inline bool isOpEnv() const
	{
		return( (op == AVM_OPCODE_INPUT_ENV  )
			|| ( op	== AVM_OPCODE_OUTPUT_ENV ) );

	}

	inline bool isTime() const
	{
		return( (nature == ENUM_TRACE_POINT::TRACE_TIME_NATURE)
				|| (op == AVM_OPCODE_TIMED_GUARD) );
	}

	inline bool isTransition() const
	{
		return( (nature == ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE)
				|| (op == AVM_OPCODE_INVOKE_TRANSITION) );
	}

	inline bool isNodeCondition() const
	{
		return( (nature == ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE  )
			||  (nature == ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE )
			|| (op == AVM_OPCODE_CHECK_SAT) );

	}


	static AVM_OPCODE to_kind(const std::string & id);

	static AVM_OPCODE to_op(AVM_OPCODE op);

	static std::string to_string(AVM_OPCODE direction);

	void updateNatureOpcodeRID();

	/**
	 * GETTER
	 * machine
	 * object
	 */
	const ExecutableForm & getExecutable() const;

	/**
	 * GETTER / SETTER
	 * value
	 */

	inline bool hasValue() const
	{
		return value.valid();
	}

	void newArrayValue(std::size_t aSize);

	const BF & val(std::size_t offset) const;

	void val(std::size_t offset, const BF & arg);

	std::size_t valCount() const;

	/**
	 * Comparison
	 */
	inline bool isEQ(const TracePoint & otherTP, bool withValue = true) const
	{
		return( (this == (& otherTP))
				|| (   (nature  == otherTP.nature )
					&& (op      == otherTP.op     )
					&& (machine == otherTP.machine)
					&& (object  == otherTP.object )
					&& ((not withValue)
						|| value.isEQ(otherTP.value)) ) );
	}

	// Due to [-Woverloaded-virtual=]
	using Element::isEQ;


	inline bool isNEQ(const TracePoint & otherTP) const
	{
		return( (this != (& otherTP))
				&& (   (nature  != otherTP.nature )
					|| (op      != otherTP.op     )
					|| (machine != otherTP.machine)
					|| (object  != otherTP.object )
					|| value.isNEQ( otherTP.value ) ) );
	}

	// Due to [-Woverloaded-virtual=]
	using Element::isNEQ;



	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	inline std::string strID() const
	{
		return( OSS() << "tpid#" << tpid );
	}

	std::string strUID() const;


	inline virtual std::string str() const override
	{
		return( strUID() );
	}

	virtual void formatValueStream(OutStream & out) const;

	virtual void toStream(OutStream & out) const override;

};


/**
 * operator<<
 */
AVM_OS_STREAM( TracePoint )



} /* namespace sep */

#endif /* TRACEPOINT_H_ */

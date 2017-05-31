/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 févr. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef ITYPESPECIFIER_H_
#define ITYPESPECIFIER_H_

#include <string>


namespace sep
{

class BF;


enum TYPE_SPECIFIER
{
	///////////////////
	// UNDEFINED
	///////////////////

	TYPE_UNDEFINED_SPECIFIER,

	//////////////////////////////
	// PRIMITIVE TYPE
	//////////////////////////////

	// ENUMERATION
	TYPE_BOOLEAN_SPECIFIER,

	TYPE_CHARACTER_SPECIFIER,

	TYPE_ENUM_SPECIFIER,

	// STRING
	TYPE_STRING_SPECIFIER,

	TYPE_IDENTIFIER_SPECIFIER,
	TYPE_QUALIFIED_IDENTIFIER_SPECIFIER,

	// NUMERIC
	TYPE_POS_INTEGER_SPECIFIER,

	TYPE_UINTEGER_SPECIFIER,

	TYPE_INTEGER_SPECIFIER,


	TYPE_URATIONAL_SPECIFIER,

	TYPE_RATIONAL_SPECIFIER,


	TYPE_UFLOAT_SPECIFIER,

	TYPE_FLOAT_SPECIFIER,


	TYPE_UREAL_SPECIFIER,

	TYPE_REAL_SPECIFIER,


	///////////////////
	// CLOCK / TIME TYPE
	///////////////////

	TYPE_CLOCK_SPECIFIER,

	TYPE_TIME_SPECIFIER,

	TYPE_CONTINUOUS_TIME_SPECIFIER,

	TYPE_DISCRETE_TIME_SPECIFIER,


	///////////////////
	// INTERVAL TYPE
	///////////////////

	TYPE_INTERVAL_SPECIFIER,


	//////////////////////////////
	// TABLE STRUCTURE
	//////////////////////////////

	// ARRAY
	TYPE_ARRAY_SPECIFIER,

	// BUILTIN ARRAY
//		TYPE_ARRAY_BOOLEAN_SPECIFIER,
//		TYPE_ARRAY_CHARACTER_SPECIFIER,
//		TYPE_ARRAY_INTEGER_SPECIFIER,
//		TYPE_ARRAY_FLOAT_SPECIFIER,
//
//		TYPE_ARRAY_STRING_SPECIFIER,
//		TYPE_ARRAY_IDENTIFIER_SPECIFIER,
//		TYPE_ARRAY_UFI_SPECIFIER,
//		TYPE_ARRAY_ENUM_SPECIFIER,
//
//		TYPE_ARRAY_FORM_SPECIFIER,


	//////////////////////////////
	// CONTAINER TYPE
	//////////////////////////////

	TYPE_FIFO_SPECIFIER,

	TYPE_LIFO_SPECIFIER,


	TYPE_MULTI_FIFO_SPECIFIER,

	TYPE_MULTI_LIFO_SPECIFIER,


	TYPE_RAM_SPECIFIER,


	TYPE_VECTOR_SPECIFIER,

	TYPE_REVERSE_VECTOR_SPECIFIER,

	TYPE_LIST_SPECIFIER,

	TYPE_SET_SPECIFIER,

	TYPE_MULTISET_SPECIFIER,

	//////////////////////////////
	// LAMBDA TYPE
	//////////////////////////////

	TYPE_LAMBDA_SPECIFIER,


	//////////////////////////////
	// COMPOSITE TYPE
	//////////////////////////////

	// USER CLASS STRUCTURE
	TYPE_CLASS_SPECIFIER,

	// USER UNION STRUCTURE
	TYPE_UNION_SPECIFIER,

	// USER CHOICE STRUCTURE
	TYPE_CHOICE_SPECIFIER,



	///////////////////
	// XLIA FORM TYPE
	///////////////////

	// OPERATOR
	TYPE_OPERATOR_SPECIFIER,

	// AVMCODE
	TYPE_AVMCODE_SPECIFIER,

	// CHANNEL
	TYPE_CHANNEL_SPECIFIER,

	// PORT
	TYPE_PORT_SPECIFIER,

	// MESSAGE
	TYPE_MESSAGE_SPECIFIER,

	// SIGNAL
	TYPE_SIGNAL_SPECIFIER,

	// BUFFER
	TYPE_BUFFER_SPECIFIER,

	// CONNECT
	TYPE_CONNECTOR_SPECIFIER,

	// MACHINE
	TYPE_MACHINE_SPECIFIER,


	///////////////////
	// ALIAS TYPEDEF
	///////////////////

	TYPE_ALIAS_SPECIFIER,


	///////////////////
	// UNIVERSAL TYPE
	///////////////////

	TYPE_UNIVERSAL_SPECIFIER,


	///////////////////
	// NULL TYPE
	///////////////////

	TYPE_NULL_SPECIFIER,


};


//typedef std::uint64_t         avm_type_specifier_kind_t;
typedef TYPE_SPECIFIER  avm_type_specifier_kind_t;


class BaseTypeSpecifier;



class ITypeSpecifier
{


public:

	/**
	 * DESTRUCTOR
	 */
	virtual ~ITypeSpecifier()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 */

	virtual const BaseTypeSpecifier * thisTypeSpecifier() const = 0;

	virtual avm_type_specifier_kind_t getTypeSpecifierKind() const = 0;


	//////////////////////////////
	// TYPE ALGEBRA
	//////////////////////////////

	inline bool isTyped(avm_type_specifier_kind_t otherTSK)
	{
		return( getTypeSpecifierKind() == otherTSK );
	}

	bool isTypeFamily(avm_type_specifier_kind_t typeFamily);

	bool weaklyTyped(avm_type_specifier_kind_t otherTSK);


	//////////////////////////////
	// PRIMITIVE TYPE
	//////////////////////////////

	inline bool isTypedEnumeration() const
	{
		switch( getTypeSpecifierKind() )
		{
			case TYPE_BOOLEAN_SPECIFIER:
			case TYPE_CHARACTER_SPECIFIER:
			case TYPE_ENUM_SPECIFIER:
				return( true );

			default:
				return( false );
		}
	}

	inline bool isTypedBoolean() const
	{
		return( getTypeSpecifierKind() == TYPE_BOOLEAN_SPECIFIER );
	}

	inline bool isTypedCharacter() const
	{
		return( getTypeSpecifierKind() == TYPE_CHARACTER_SPECIFIER );
	}

	inline bool isTypedString() const
	{
		return( getTypeSpecifierKind() == TYPE_STRING_SPECIFIER );
	}

	inline bool isTypedEnum() const
	{
		return( getTypeSpecifierKind() == TYPE_ENUM_SPECIFIER );
	}


	inline bool isTypedIdentifier() const
	{
		return( getTypeSpecifierKind() == TYPE_IDENTIFIER_SPECIFIER );
	}

	inline bool isTypedQualifiedIdentifier() const
	{
		return( getTypeSpecifierKind() == TYPE_QUALIFIED_IDENTIFIER_SPECIFIER );
	}

	inline bool weaklyTypedIdentifier() const
	{
		return( (getTypeSpecifierKind() == TYPE_IDENTIFIER_SPECIFIER)
			 || (getTypeSpecifierKind() == TYPE_QUALIFIED_IDENTIFIER_SPECIFIER) );
	}


	bool isTypedNumeric() const;


	///////////////////
	// CLOCK TYPE
	///////////////////

	inline bool hasTypedClock() const
	{
		return( isTypedClock() );
	}

	inline bool isTypedClock() const
	{
		return( getTypeSpecifierKind() == TYPE_CLOCK_SPECIFIER );
	}

	bool weaklyTypedClockInteger() const;

	bool weaklyTypedClockRational() const;

	bool weaklyTypedClockFloat() const;

	bool weaklyTypedClockReal() const;


	///////////////////
	// TIME TYPE
	///////////////////

	inline bool hasTypedTime() const
	{
		return( (getTypeSpecifierKind() == TYPE_TIME_SPECIFIER)
			 || (getTypeSpecifierKind() == TYPE_DISCRETE_TIME_SPECIFIER)
			 || (getTypeSpecifierKind() == TYPE_CONTINUOUS_TIME_SPECIFIER) );
	}

	inline bool isTypedTime() const
	{
		return( getTypeSpecifierKind() == TYPE_TIME_SPECIFIER );
	}

	bool isTypedContinuousTime() const
	{
		return( getTypeSpecifierKind() == TYPE_CONTINUOUS_TIME_SPECIFIER );
	}

	bool isTypedDiscreteTime() const
	{
		return( getTypeSpecifierKind() == TYPE_DISCRETE_TIME_SPECIFIER );
	}

	bool weaklyTypedTimeInteger() const;

	bool weaklyTypedTimeFloat() const;

	bool weaklyTypedTimeRational() const;

	bool weaklyTypedTimeReal() const;


	///////////////////
	// CLOCK/TIME TYPE
	///////////////////

	inline bool hasTypedClockTime() const
	{
		return( hasTypedClock() || hasTypedTime() );
	}

	inline bool isTypedClockTime() const
	{
		return( isTypedClock() || isTypedTime() );
	}

	bool weaklyTypedClockTimeInteger() const;

	bool weaklyTypedClockTimeRational() const;

	bool weaklyTypedClockTimeFloat() const;

	bool weaklyTypedClockTimeReal() const;



	///////////////////
	// INTEGER TYPE
	///////////////////

	inline bool isTypedPosInteger() const
	{
		return( getTypeSpecifierKind() == TYPE_POS_INTEGER_SPECIFIER );
	}

	inline bool isTypedUInteger() const
	{
		return( (getTypeSpecifierKind() == TYPE_UINTEGER_SPECIFIER)
				|| isTypedPosInteger() );
	}

	bool weaklyTypedUInteger() const;

	inline bool isTypedInteger() const
	{
		return( (getTypeSpecifierKind() == TYPE_INTEGER_SPECIFIER)
				|| isTypedUInteger() );
	}

	bool weaklyTypedInteger() const;


	///////////////////
	// RATIONAL TYPE
	///////////////////

	inline bool isTypedURational() const
	{
		return( getTypeSpecifierKind() == TYPE_URATIONAL_SPECIFIER );
	}

	bool weaklyTypedURational() const;

	inline bool isTypedRational() const
	{
		return( (getTypeSpecifierKind() == TYPE_RATIONAL_SPECIFIER)
				|| isTypedURational() );
	}

	bool weaklyTypedRational() const;


	///////////////////
	// FLOAT TYPE
	///////////////////

	inline bool isTypedUFloat() const
	{
		return( getTypeSpecifierKind() == TYPE_UFLOAT_SPECIFIER );
	}

	bool weaklyTypedUFloat() const;

	inline bool isTypedFloat() const
	{
		return( (getTypeSpecifierKind() == TYPE_FLOAT_SPECIFIER)
				|| isTypedUFloat() );
	}

	bool weaklyTypedFloat() const;


	///////////////////
	// REAL TYPE
	///////////////////

	inline bool isTypedUReal() const
	{
		return( getTypeSpecifierKind() == TYPE_UREAL_SPECIFIER );
	}

	bool weaklyTypedUReal() const;

	inline bool isTypedReal() const
	{
		return( (getTypeSpecifierKind() == TYPE_REAL_SPECIFIER)
				|| isTypedUReal() );
	}

	bool weaklyTypedReal() const;


	///////////////////
	// INTERVAL TYPE
	///////////////////

	inline bool isTypedInterval() const
	{
		return( getTypeSpecifierKind() == TYPE_INTERVAL_SPECIFIER );
	}



	///////////////////
	// XKIA FORM TYPE
	///////////////////

	inline bool isTypedOperator() const
	{
		return( getTypeSpecifierKind() == TYPE_OPERATOR_SPECIFIER );
	}

	inline bool isTypedAvmcode() const
	{
		return( getTypeSpecifierKind() == TYPE_AVMCODE_SPECIFIER );
	}

	inline bool isTypedChannel() const
	{
		return( getTypeSpecifierKind() == TYPE_CHANNEL_SPECIFIER );
	}

	inline bool isTypedPort() const
	{
		return( getTypeSpecifierKind() == TYPE_PORT_SPECIFIER );
	}

	inline bool isTypedMessage() const
	{
		return( getTypeSpecifierKind() == TYPE_MESSAGE_SPECIFIER );
	}

	inline bool isTypedSignal() const
	{
		return( getTypeSpecifierKind() == TYPE_SIGNAL_SPECIFIER );
	}

	inline bool isTypedBuffer() const
	{
		return( getTypeSpecifierKind() == TYPE_BUFFER_SPECIFIER );
	}

	inline bool isTypedConnection() const
	{
		return( getTypeSpecifierKind() == TYPE_CONNECTOR_SPECIFIER );
	}

	inline bool isTypedMachine() const
	{
		return( getTypeSpecifierKind() == TYPE_MACHINE_SPECIFIER );
	}


	inline bool hasTypeXliaForm() const
	{
		switch( getTypeSpecifierKind() )
		{
			case TYPE_OPERATOR_SPECIFIER:
			case TYPE_AVMCODE_SPECIFIER:
			case TYPE_PORT_SPECIFIER:
			case TYPE_BUFFER_SPECIFIER:
			case TYPE_SIGNAL_SPECIFIER:
			case TYPE_CONNECTOR_SPECIFIER:
			case TYPE_MACHINE_SPECIFIER:
				return( true );

			default:
				return( false );
		}
	}


	//////////////////////////////
	// ARRAY TYPE
	//////////////////////////////

	inline bool isTypedArray() const
	{
		return( getTypeSpecifierKind() == TYPE_ARRAY_SPECIFIER );
	}


	//////////////////////////////
	// CONTAINER TYPE
	//////////////////////////////

	inline bool isTypedVector() const
	{
		return( getTypeSpecifierKind() == TYPE_VECTOR_SPECIFIER );
	}

	inline bool isTypedReverseVector() const
	{
		return( getTypeSpecifierKind() == TYPE_REVERSE_VECTOR_SPECIFIER );
	}

	inline bool hasTypeVector() const
	{
		switch( getTypeSpecifierKind() )
		{
			case TYPE_VECTOR_SPECIFIER:
			case TYPE_REVERSE_VECTOR_SPECIFIER:
				return( true );

			default:
				return( false );
		}
	}


	inline bool isTypedList() const
	{
		return( getTypeSpecifierKind() == TYPE_LIST_SPECIFIER );
	}

	inline bool isTypedSet() const
	{
		return( getTypeSpecifierKind() == TYPE_SET_SPECIFIER );
	}

	inline bool isTypedMultiset() const
	{
		return( getTypeSpecifierKind() == TYPE_MULTISET_SPECIFIER );
	}


	inline bool isTypedFifo() const
	{
		return( getTypeSpecifierKind() == TYPE_FIFO_SPECIFIER );
	}

	inline bool isTypedLifo() const
	{
		return( getTypeSpecifierKind() == TYPE_LIFO_SPECIFIER );
	}


	inline bool isTypedMultiFifo() const
	{
		return( getTypeSpecifierKind() == TYPE_MULTI_FIFO_SPECIFIER );
	}

	inline bool isTypedMultiLifo() const
	{
		return( getTypeSpecifierKind() == TYPE_MULTI_LIFO_SPECIFIER );
	}


	inline bool isTypedRam() const
	{
		return( getTypeSpecifierKind() == TYPE_RAM_SPECIFIER );
	}


	inline bool hasTypeArrayVector() const
	{
		switch( getTypeSpecifierKind() )
		{
			case TYPE_ARRAY_SPECIFIER:
			case TYPE_VECTOR_SPECIFIER:
			case TYPE_REVERSE_VECTOR_SPECIFIER:
				return( true );

			default:
				return( false );
		}
	}

	inline bool hasTypeQueue() const
	{
		switch( getTypeSpecifierKind() )
		{
			case TYPE_FIFO_SPECIFIER:
			case TYPE_LIFO_SPECIFIER:

			case TYPE_MULTI_FIFO_SPECIFIER:
			case TYPE_MULTI_LIFO_SPECIFIER:

			case TYPE_RAM_SPECIFIER:
				return( true );

			default:
				return( false );
		}
	}


	inline bool hasTypeListCollection() const
	{
		switch( getTypeSpecifierKind() )
		{
			case TYPE_LIST_SPECIFIER:
			case TYPE_SET_SPECIFIER:
			case TYPE_MULTISET_SPECIFIER:
				return( true );

			default:
				return( hasTypeQueue() );
		}
	}

	inline bool hasTypeCollection() const
	{
		return( hasTypeVector() || hasTypeListCollection() );
	}

	inline bool hasTypeContainer() const
	{
		return( isTypedArray() || hasTypeCollection() );
	}


	//////////////////////////////
	// COMPOSITE TYPE
	//////////////////////////////

	inline bool isTypedStructure() const
	{
		return( getTypeSpecifierKind() == TYPE_CLASS_SPECIFIER );
	}

	inline bool isTypedClass() const
	{
		return( getTypeSpecifierKind() == TYPE_CLASS_SPECIFIER );
	}


	inline bool isTypedChoice() const
	{
		return( getTypeSpecifierKind() == TYPE_CHOICE_SPECIFIER );
	}

	inline bool isTypedUnion() const
	{
		return( getTypeSpecifierKind() == TYPE_UNION_SPECIFIER );
	}

	inline bool hasTypeChoiceOrUnion() const
	{
		return( (getTypeSpecifierKind() == TYPE_CHOICE_SPECIFIER)
			 || (getTypeSpecifierKind() == TYPE_UNION_SPECIFIER) );
	}

	inline bool hasTypeStructureOrChoiceOrUnion() const
	{
		return( (getTypeSpecifierKind() == TYPE_CLASS_SPECIFIER  )
			 || (getTypeSpecifierKind() == TYPE_CHOICE_SPECIFIER )
			 || (getTypeSpecifierKind() == TYPE_UNION_SPECIFIER) );
	}


	//////////////////////////////
	// LAMBDA TYPE
	//////////////////////////////

	inline bool isTypedLambda() const
	{
		return( getTypeSpecifierKind() == TYPE_LAMBDA_SPECIFIER );
	}


	//////////////////////////////
	// ALIAS TYPE
	//////////////////////////////

	inline bool isTypedAlias() const
	{
		return( getTypeSpecifierKind() == TYPE_ALIAS_SPECIFIER );
	}


	//////////////////////////////
	// UNIVERSAL TYPE
	//////////////////////////////

	inline bool isTypedUniversal() const
	{
		return( getTypeSpecifierKind() == TYPE_UNIVERSAL_SPECIFIER );
	}


	//////////////////////////////
	// CATEGORY TYPE
	//////////////////////////////

	inline bool hasTypePrimitive() const
	{
		switch( getTypeSpecifierKind() )
		{
			case TYPE_BOOLEAN_SPECIFIER:
			case TYPE_CHARACTER_SPECIFIER:
			case TYPE_STRING_SPECIFIER:

			case TYPE_INTEGER_SPECIFIER:
			case TYPE_RATIONAL_SPECIFIER:
			case TYPE_FLOAT_SPECIFIER:
			case TYPE_REAL_SPECIFIER:

			case TYPE_POS_INTEGER_SPECIFIER:

			case TYPE_UINTEGER_SPECIFIER:
			case TYPE_URATIONAL_SPECIFIER:
			case TYPE_UFLOAT_SPECIFIER:
			case TYPE_UREAL_SPECIFIER:

			case TYPE_CLOCK_SPECIFIER:
			case TYPE_TIME_SPECIFIER:
			case TYPE_CONTINUOUS_TIME_SPECIFIER:
			case TYPE_DISCRETE_TIME_SPECIFIER:
				return( true );

			default:
				return( false );
		}
	}

	inline bool hasTypeBasic() const
	{
		return( isTypedBoolean()   || isTypedNumeric() ||
				isTypedCharacter() || isTypedString()  ||
				hasTypeXliaForm() );
	}

	inline bool hasTypeSimple() const
	{
		return( hasTypeBasic() || isTypedEnum() );
	}

	inline bool hasTypeSimpleOrCollection() const
	{
		return( hasTypeSimple() || hasTypeCollection() );
	}

	inline bool hasTypeArrayOrStructure() const
	{
		return( isTypedArray() || isTypedStructure() );
	}

	inline bool hasTypeComposite() const
	{
		return( hasTypeContainer() || isTypedStructure() );
	}


	inline bool hasTypeEnumOrComposite() const
	{
		return( isTypedEnum() || hasTypeComposite() );
	}


	/**
	 * Serialization
	 */
	std::string strSpecifierKind() const;

};




////////////////////////////////////////////////////////////////////////////////
// INTERVAL::KIND
////////////////////////////////////////////////////////////////////////////////

class IIntervalKind
{

public:

	enum KIND
	{
		CLOSED = 0x00,

		LOPEN  = 0x01,

		ROPEN  = 0x02,

		OPEN   = 0x03,
	};


	/**
	 * DESTRUCTOR
	 */
	virtual ~IIntervalKind()
	{
		//!! NOTHING
	}


	/**
	 * API
	 */
	virtual KIND getIntervalKind() const = 0;


	inline bool isCLOSED()const
	{
		return( getIntervalKind() == CLOSED );
	}

	inline bool isLOPEN()const
	{
		return( getIntervalKind() == LOPEN );
	}

	inline bool isROPEN()const
	{
		return( getIntervalKind() == ROPEN );
	}

	inline bool isOPEN()const
	{
		return( getIntervalKind() == OPEN );
	}


	inline bool isLClosed()const
	{
		return( (getIntervalKind() & LOPEN) == 0 );
	}

	inline bool isLOpen()const
	{
		return( (getIntervalKind() & LOPEN) != 0 );
	}

	inline bool isRClosed()const
	{
		return( (getIntervalKind() & ROPEN) == 0 );
	}

	inline bool isROpen()const
	{
		return( (getIntervalKind() & ROPEN) != 0 );
	}


	/**
	 * STATIC
	 */
	/**
	 * Compute interval nature
	 */
	inline static KIND computeKind(char left, char right)
	{
		bool lOpen = (left == ']') || (left == '(') || (left == ')');
		bool rOpen = (left == '[') || (left == ')') || (left == '(');

		return( lOpen ?
				( rOpen ? IIntervalKind::OPEN  : IIntervalKind::LOPEN  ) :
				( rOpen ? IIntervalKind::ROPEN : IIntervalKind::CLOSED ) );
	}


	static std::string to_string(KIND kind, const BF & inf, const BF & sup);

};


} /* namespace sep */
#endif /* ITYPESPECIFIER_H_ */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/



#include "TypeManager.h"

#include <fml/expression/ExpressionConstant.h>


namespace sep
{


/**
 * TypeManager
 * singleton
 */
const TypeManager & TypeFactory = *( TypeManager::singleton() );


/*
 ***************************************************************************
 * PRIMITE TYPE NAME IDENTIFIER
 ***************************************************************************
 */
const std::string & TypeManager::TYPE_ARRAY_ID     = "array";
const std::string & TypeManager::TYPE_VECTOR_ID    = "vector";
const std::string & TypeManager::TYPE_REVERSE_VECTOR_ID = "rvector";
const std::string & TypeManager::TYPE_LIST_ID      = "list";
const std::string & TypeManager::TYPE_SET_ID       = "set";
const std::string & TypeManager::TYPE_MULTISET_ID  = "multiset";
const std::string & TypeManager::TYPE_BAG_ID       = "bag";

const std::string & TypeManager::TYPE_FIFO_ID      = "fifo";
const std::string & TypeManager::TYPE_LIFO_ID      = "lifo";

const std::string & TypeManager::TYPE_ENUM_ID      = "enum";
const std::string & TypeManager::TYPE_UNION_ID     = "union";
const std::string & TypeManager::TYPE_CHOICE_ID    = "choice";
const std::string & TypeManager::TYPE_STRUCTURE_ID = "struct";
const std::string & TypeManager::TYPE_CLASS_ID     = "class";

const std::string & TypeManager::TYPE_BOOL_ID      = "bool";
const std::string & TypeManager::TYPE_BOOLEAN_ID   = "boolean";

const std::string & TypeManager::TYPE_INT8_ID      = "int8";
const std::string & TypeManager::TYPE_INT16_ID     = "int16";
const std::string & TypeManager::TYPE_INT32_ID     = "int32";
const std::string & TypeManager::TYPE_INT64_ID     = "int64";
const std::string & TypeManager::TYPE_INT128_ID    = "int128";

const std::string & TypeManager::TYPE_INT_ID       = "int";
const std::string & TypeManager::TYPE_INTEGER_ID   = "integer";

const std::string & TypeManager::TYPE_RAT_ID       = "rat";
const std::string & TypeManager::TYPE_RATIONAL_ID  = "rational";

const std::string & TypeManager::TYPE_FLOAT_ID     = "float";
const std::string & TypeManager::TYPE_DOUBLE_ID    = "double";
const std::string & TypeManager::TYPE_REAL_ID      = "real";

const std::string & TypeManager::TYPE_UINT8_ID     = "uint8";
const std::string & TypeManager::TYPE_UINT16_ID    = "uint16";
const std::string & TypeManager::TYPE_UINT32_ID    = "uint32";
const std::string & TypeManager::TYPE_UINT64_ID    = "uint64";
const std::string & TypeManager::TYPE_UINT128_ID   = "uint128";

const std::string & TypeManager::TYPE_UINT_ID      = "uint";
const std::string & TypeManager::TYPE_UINTEGER_ID  = "uinteger";

const std::string & TypeManager::TYPE_POS_INTEGER_ID  = "pos_integer";

const std::string & TypeManager::TYPE_URAT_ID      = "urat";
const std::string & TypeManager::TYPE_URATIONAL_ID = "urational";

const std::string & TypeManager::TYPE_UFLOAT_ID    = "ufloat";
const std::string & TypeManager::TYPE_UDOUBLE_ID   = "udouble";
const std::string & TypeManager::TYPE_UREAL_ID     = "ureal";

const std::string & TypeManager::TYPE_CONTINUOUS_TIME_ID = "ctime";
const std::string & TypeManager::TYPE_DISCRETE_TIME_ID   = "dtime";
const std::string & TypeManager::TYPE_TIME_ID            = "time";
const std::string & TypeManager::TYPE_CLOCK_ID           = "clock";

const std::string & TypeManager::TYPE_CHAR_ID      = "char";
const std::string & TypeManager::TYPE_CHARACTER_ID = "character";
const std::string & TypeManager::TYPE_STRING_ID    = "string";

const std::string & TypeManager::TYPE_INTERVAL_ID  = "interval";


const std::string & TypeManager::TYPE_ARRAY_BOOLEAN_ID   = "array<boolean>";
const std::string & TypeManager::TYPE_ARRAY_CHARACTER_ID = "array<character>";
const std::string & TypeManager::TYPE_ARRAY_INTEGER_ID   = "array<integer>";
const std::string & TypeManager::TYPE_ARRAY_RATIONAL_ID  = "array<rational>";
const std::string & TypeManager::TYPE_ARRAY_FLOAT_ID     = "array<float>";

const std::string & TypeManager::TYPE_ARRAY_STRING_ID     = "array<string>";
const std::string & TypeManager::TYPE_ARRAY_IDENTIFIER_ID = "array<identifier>";
const std::string & TypeManager::TYPE_ARRAY_QUALIFIED_IDENTIFIER_ID =
												"array<qualified_identifier>";
const std::string & TypeManager::TYPE_ARRAY_ENUM_ID       = "array<enum>";

const std::string & TypeManager::TYPE_ARRAY_ANY_ID        = "array<any>";


const std::string & TypeManager::TYPE_LAMBDA_ID       = "lambda";

const std::string & TypeManager::TYPE_OPERATOR_ID     = "operator";
const std::string & TypeManager::TYPE_AVMCODE_ID      = "avmcode";
const std::string & TypeManager::TYPE_EXPRESSION_ID   = "expression";

const std::string & TypeManager::TYPE_PORT_ID         = "port";
const std::string & TypeManager::TYPE_MESSAGE_ID      = "message";
const std::string & TypeManager::TYPE_SIGNAL_ID       = "signal";
const std::string & TypeManager::TYPE_BUFFER_ID       = "buffer";
const std::string & TypeManager::TYPE_CONNECTOR_ID    = "connector";
const std::string & TypeManager::TYPE_MACHINE_ID      = "machine";
const std::string & TypeManager::TYPE_RID_ID          = "RuntimeID";

const std::string & TypeManager::TYPE_UNIVERSAL_ID    = "universal";

const std::string & TypeManager::TYPE_SIMULINK_BUS_ID = "simulinkBus";


/*
 ***************************************************************************
 * PRIMITE TYPE SPECIFIER
 ***************************************************************************
 */
TypeSpecifier TypeManager::BOOL;
TypeSpecifier TypeManager::BOOLEAN;

TypeSpecifier TypeManager::INT8;
TypeSpecifier TypeManager::UINT8;

TypeSpecifier TypeManager::INT16;
TypeSpecifier TypeManager::UINT16;

TypeSpecifier TypeManager::INT32;
TypeSpecifier TypeManager::UINT32;

TypeSpecifier TypeManager::INT64;
TypeSpecifier TypeManager::UINT64;

TypeSpecifier TypeManager::INT128;
TypeSpecifier TypeManager::UINT128;

TypeSpecifier TypeManager::INT;
TypeSpecifier TypeManager::UINT;

TypeSpecifier TypeManager::INTEGER;
TypeSpecifier TypeManager::UINTEGER;
TypeSpecifier TypeManager::POS_INTEGER;

TypeSpecifier TypeManager::RAT;
TypeSpecifier TypeManager::URAT;

TypeSpecifier TypeManager::RATIONAL;
TypeSpecifier TypeManager::URATIONAL;


TypeSpecifier TypeManager::FLOAT;
TypeSpecifier TypeManager::UFLOAT;

TypeSpecifier TypeManager::DOUBLE;
TypeSpecifier TypeManager::UDOUBLE;

TypeSpecifier TypeManager::REAL;
TypeSpecifier TypeManager::UREAL;


TypeSpecifier TypeManager::CLOCK;
TypeSpecifier TypeManager::TIME;
TypeSpecifier TypeManager::CONTINUOUS_TIME;
TypeSpecifier TypeManager::DISCRETE_TIME;

TypeSpecifier TypeManager::CHAR;
TypeSpecifier TypeManager::CHARACTER;
TypeSpecifier TypeManager::STRING;

TypeSpecifier TypeManager::IDENTIFIER;
TypeSpecifier TypeManager::QUALIFIED_IDENTIFIER;

TypeSpecifier TypeManager::LAMBDA;

TypeSpecifier TypeManager::OPERATOR;
TypeSpecifier TypeManager::AVMCODE;
TypeSpecifier TypeManager::EXPRESSION;

TypeSpecifier TypeManager::CHANNEL;
TypeSpecifier TypeManager::PORT;
TypeSpecifier TypeManager::MESSAGE;
TypeSpecifier TypeManager::SIGNAL;
TypeSpecifier TypeManager::BUFFER;
TypeSpecifier TypeManager::CONNECTOR;
TypeSpecifier TypeManager::MACHINE;

TypeSpecifier TypeManager::ARRAY_BOOLEAN;
TypeSpecifier TypeManager::ARRAY_CHARACTER;
TypeSpecifier TypeManager::ARRAY_INTEGER;
TypeSpecifier TypeManager::ARRAY_RATIONAL;
TypeSpecifier TypeManager::ARRAY_FLOAT;

TypeSpecifier TypeManager::ARRAY_STRING;
TypeSpecifier TypeManager::ARRAY_IDENTIFIER;
TypeSpecifier TypeManager::ARRAY_QUALIFIED_IDENTIFIER;
TypeSpecifier TypeManager::ARRAY_ENUM;

TypeSpecifier TypeManager::ARRAY_ANY;

TypeSpecifier TypeManager::ARRAY;
TypeSpecifier TypeManager::VECTOR;
TypeSpecifier TypeManager::LIST;
TypeSpecifier TypeManager::SET;
TypeSpecifier TypeManager::MULTISET;
TypeSpecifier TypeManager::BAG;

TypeSpecifier TypeManager::ENUM;
TypeSpecifier TypeManager::CLASS;
TypeSpecifier TypeManager::STRUCTURE;
TypeSpecifier TypeManager::UNION;
TypeSpecifier TypeManager::CHOICE;
TypeSpecifier TypeManager::INTERVAL;


TypeSpecifier TypeManager::UNIVERSAL;



/**
 * LOADER
 */
void TypeManager::load()
{
	// TypeManager:> TypeSpecifier, CompiledType, Type Size, Data Size
	/*
	 ***************************************************************************
	 * PRIMITE TYPE SPECIFIER
	 ***************************************************************************
	 */
	TypeManager::registerPrimitiveType(
			BOOL = newNumericTypeSpecifier(
					TYPE_BOOL_ID, TYPE_BOOLEAN_SPECIFIER,
					1, 1, ExpressionConstant::BOOLEAN_FALSE ) );

	TypeManager::registerPrimitiveType(
			BOOLEAN = newNumericTypeSpecifier(
					TYPE_BOOLEAN_ID, TYPE_BOOLEAN_SPECIFIER,
					1, 1, ExpressionConstant::BOOLEAN_FALSE ) );


	TypeManager::registerPrimitiveType(
			INT8 = newNumericTypeSpecifier(
					TYPE_INT8_ID, TYPE_INTEGER_SPECIFIER,
					1, 8, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			UINT8 = newNumericTypeSpecifier(
					TYPE_UINT8_ID, TYPE_UINTEGER_SPECIFIER,
					1, 8, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			INT16 = newNumericTypeSpecifier(
					TYPE_INT16_ID, TYPE_INTEGER_SPECIFIER,
					1, 16, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			UINT16 = newNumericTypeSpecifier(
					TYPE_UINT16_ID, TYPE_UINTEGER_SPECIFIER,
					1, 16, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			INT32 = newNumericTypeSpecifier(
					TYPE_INT32_ID, TYPE_INTEGER_SPECIFIER,
					1, 32, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			UINT32 = newNumericTypeSpecifier(
					TYPE_UINT32_ID, TYPE_UINTEGER_SPECIFIER,
					1, 32, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			INT64 = newNumericTypeSpecifier(
					TYPE_INT64_ID, TYPE_INTEGER_SPECIFIER,
					1, 64, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			UINT64 = newNumericTypeSpecifier(
					TYPE_UINT64_ID, TYPE_UINTEGER_SPECIFIER,
					1, 64, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			INT128 = newNumericTypeSpecifier(
					TYPE_INT128_ID, TYPE_INTEGER_SPECIFIER,
					1, 128, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			UINT128 = newNumericTypeSpecifier(
					TYPE_UINT128_ID, TYPE_UINTEGER_SPECIFIER,
					1, 128, ExpressionConstant::INTEGER_ZERO ) );


	TypeManager::registerPrimitiveType(
			INT = newNumericTypeSpecifier(
					TYPE_INT_ID, TYPE_INTEGER_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			INTEGER = newNumericTypeSpecifier(
					TYPE_INTEGER_ID, TYPE_INTEGER_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ZERO ) );


	TypeManager::registerPrimitiveType(
			UINT = newNumericTypeSpecifier(
					TYPE_UINT_ID, TYPE_UINTEGER_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			UINTEGER = newNumericTypeSpecifier(
					TYPE_UINTEGER_ID, TYPE_UINTEGER_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			POS_INTEGER = newNumericTypeSpecifier(
					TYPE_POS_INTEGER_ID, TYPE_POS_INTEGER_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ONE ) );



	TypeManager::registerPrimitiveType(
			RAT = newNumericTypeSpecifier(
					TYPE_RAT_ID, TYPE_RATIONAL_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			RATIONAL = newNumericTypeSpecifier(
					TYPE_RATIONAL_ID, TYPE_RATIONAL_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ZERO ) );


	TypeManager::registerPrimitiveType(
			URAT = newNumericTypeSpecifier(
					TYPE_URAT_ID, TYPE_URATIONAL_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			URATIONAL = newNumericTypeSpecifier(
					TYPE_URATIONAL_ID, TYPE_URATIONAL_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ZERO ) );


	TypeManager::registerPrimitiveType(
			FLOAT = newNumericTypeSpecifier(
					TYPE_FLOAT_ID, TYPE_FLOAT_SPECIFIER,
					1, 32, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			UFLOAT = newNumericTypeSpecifier(
					TYPE_UFLOAT_ID, TYPE_UFLOAT_SPECIFIER,
					1, 32, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			DOUBLE = newNumericTypeSpecifier(
					TYPE_DOUBLE_ID, TYPE_FLOAT_SPECIFIER,
					1, 64, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			UDOUBLE = newNumericTypeSpecifier(
					TYPE_UDOUBLE_ID, TYPE_UFLOAT_SPECIFIER,
					1, 64, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			REAL = newNumericTypeSpecifier(
					TYPE_REAL_ID, TYPE_REAL_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			UREAL = newNumericTypeSpecifier(
					TYPE_UREAL_ID, TYPE_UREAL_SPECIFIER,
					1, 0, ExpressionConstant::INTEGER_ZERO ) );


	TypeManager::registerPrimitiveType(
			CLOCK = newTypeSpecifier(
					TYPE_CLOCK_ID, TYPE_CLOCK_SPECIFIER,
					1, 1, 0, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			TIME = newTypeSpecifier(
					TYPE_TIME_ID, TYPE_TIME_SPECIFIER,
					1, 1, 0, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			CONTINUOUS_TIME = newTypeSpecifier(
					TYPE_CONTINUOUS_TIME_ID, TYPE_CONTINUOUS_TIME_SPECIFIER,
					1, 1, 0, ExpressionConstant::INTEGER_ZERO ) );

	TypeManager::registerPrimitiveType(
			DISCRETE_TIME = newTypeSpecifier(
					TYPE_DISCRETE_TIME_ID, TYPE_DISCRETE_TIME_SPECIFIER,
					1, 1, 0, ExpressionConstant::INTEGER_ZERO ) );


	TypeManager::registerPrimitiveType(
			CHAR = newCharacter(TYPE_CHAR_ID, 1) );

	TypeManager::registerPrimitiveType(
			CHARACTER = newCharacter(TYPE_CHARACTER_ID, 1) );

	TypeManager::registerPrimitiveType(
			STRING = newString( 0 , AVM_NUMERIC_MAX_SIZE_T  ) );

	TypeManager::registerPrimitiveType(
			IDENTIFIER = newTypeSpecifier(
					TYPE_STRING_ID, TYPE_IDENTIFIER_SPECIFIER,
					1, 1, 0, ExpressionConstant::STRING_EMPTY ) );

	TypeManager::registerPrimitiveType(
			QUALIFIED_IDENTIFIER = newTypeSpecifier(
					TYPE_STRING_ID, TYPE_QUALIFIED_IDENTIFIER_SPECIFIER,
					1, 1, 0, ExpressionConstant::STRING_EMPTY ) );

	TypeManager::registerPrimitiveType(
			LAMBDA = newTypeSpecifier(
					TYPE_LAMBDA_ID, TYPE_LAMBDA_SPECIFIER, 1, 1, 0 ) );


	TypeManager::registerPrimitiveType(
			OPERATOR = newTypeSpecifier(
					TYPE_OPERATOR_ID, TYPE_OPERATOR_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			AVMCODE = newTypeSpecifier(
					TYPE_AVMCODE_ID, TYPE_AVMCODE_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			CHANNEL = newTypeSpecifier(
					TYPE_PORT_ID, TYPE_CHANNEL_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			PORT = newTypeSpecifier(
					TYPE_PORT_ID, TYPE_PORT_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			MESSAGE = newTypeSpecifier(
					TYPE_MESSAGE_ID, TYPE_MESSAGE_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			SIGNAL = newTypeSpecifier(
					TYPE_SIGNAL_ID, TYPE_SIGNAL_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			BUFFER = newTypeSpecifier(
					TYPE_BUFFER_ID, TYPE_BUFFER_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			CONNECTOR = newTypeSpecifier(
					TYPE_CONNECTOR_ID, TYPE_CONNECTOR_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			MACHINE = newTypeSpecifier(
					TYPE_MACHINE_ID, TYPE_MACHINE_SPECIFIER, 1, 1, 0 ) );


	TypeManager::registerPrimitiveType(
			ARRAY_BOOLEAN = newArray(
					TYPE_ARRAY_BOOLEAN_ID, BOOLEAN, 0 ) );

	TypeManager::registerPrimitiveType(
			ARRAY_CHARACTER = newArray(
					TYPE_ARRAY_CHARACTER_ID, CHARACTER, 0 ) );

	TypeManager::registerPrimitiveType(
			ARRAY_INTEGER = newArray(
					TYPE_ARRAY_INTEGER_ID, INTEGER, 0 ) );

	TypeManager::registerPrimitiveType(
			ARRAY_RATIONAL = newArray(
					TYPE_ARRAY_RATIONAL_ID, RATIONAL, 0 ) );

	TypeManager::registerPrimitiveType(
			ARRAY_FLOAT = newArray(
					TYPE_ARRAY_FLOAT_ID, FLOAT, 0 ) );

	TypeManager::registerPrimitiveType(
			ARRAY_STRING = newArray(
					TYPE_ARRAY_STRING_ID, STRING, 0 ) );

	TypeManager::registerPrimitiveType(
			ARRAY_IDENTIFIER = newArray(
					TYPE_ARRAY_IDENTIFIER_ID, STRING, 0 ) );

	TypeManager::registerPrimitiveType(
			ARRAY_QUALIFIED_IDENTIFIER = newArray(
					TYPE_ARRAY_QUALIFIED_IDENTIFIER_ID,
					QUALIFIED_IDENTIFIER, 0 ) );

	TypeManager::registerPrimitiveType(
			ARRAY_ENUM = newArray(
					TYPE_ARRAY_ENUM_ID, QUALIFIED_IDENTIFIER, 0 ) );

	TypeManager::registerPrimitiveType(
			ARRAY_ANY = newArray(
					TYPE_ARRAY_ANY_ID, UNIVERSAL, 0 ) );


	TypeManager::registerPrimitiveType(
			ARRAY = newTypeSpecifier(
					TYPE_ARRAY_ID, TYPE_ARRAY_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			VECTOR = newTypeSpecifier(
					TYPE_VECTOR_ID, TYPE_VECTOR_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			LIST = newTypeSpecifier(
					TYPE_LIST_ID, TYPE_LIST_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			SET = newTypeSpecifier(
					TYPE_SET_ID, TYPE_SET_SPECIFIER, 1, 1, 0 ) );

	static TypeSpecifier MULTISET;
	TypeManager::registerPrimitiveType(
			MULTISET = newTypeSpecifier(
					TYPE_MULTISET_ID, TYPE_MULTISET_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			BAG = newTypeSpecifier(
					TYPE_BAG_ID, TYPE_MULTISET_SPECIFIER, 1, 1, 0 ) );


	TypeManager::registerPrimitiveType(
			ENUM = newTypeSpecifier(
					TYPE_ENUM_ID, TYPE_ENUM_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			CLASS = newTypeSpecifier(
					TYPE_CLASS_ID, TYPE_CLASS_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			STRUCTURE = newTypeSpecifier(
					TYPE_STRUCTURE_ID, TYPE_CLASS_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			UNION = newTypeSpecifier(
					TYPE_UNION_ID, TYPE_UNION_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			CHOICE = newTypeSpecifier(
					TYPE_CHOICE_ID, TYPE_CHOICE_SPECIFIER, 1, 1, 0 ) );

	TypeManager::registerPrimitiveType(
			INTERVAL = newTypeSpecifier(
					TYPE_INTERVAL_ID, TYPE_INTERVAL_SPECIFIER, 1, 1, 0 ) );


	TypeManager::registerPrimitiveType(
			UNIVERSAL = newTypeSpecifier(
					TYPE_UNIVERSAL_ID, TYPE_UNIVERSAL_SPECIFIER, 1, 1, 0 ) );
}


TypeSpecifier TypeManager::getTypeInteger(int dim)
{
	switch( dim )
	{
		case   8:  return( INT8   );
		case  16:  return( INT16  );
		case  32:  return( INT32  );
		case  64:  return( INT64  );
		case 128:  return( INT128 );

		default:
		{
			if( dim > 0 )
			{
				TypeSpecifier bfTS( newNumericTypeSpecifier(
						TYPE_INTEGER_ID, TYPE_INTEGER_SPECIFIER,
						1, dim, ExpressionConstant::INTEGER_ZERO) );

				return( bfTS );
			}
			return( INTEGER );
		}
	}
}

TypeSpecifier TypeManager::getTypeUInteger(int dim)
{
	switch( dim )
	{
		case   8:  return( UINT8   );
		case  16:  return( UINT16  );
		case  32:  return( UINT32  );
		case  64:  return( UINT64  );
		case 128:  return( UINT128 );

		default:
		{
			if( dim > 0 )
			{
				TypeSpecifier bfTS( newNumericTypeSpecifier(
						TYPE_UINTEGER_ID, TYPE_UINTEGER_SPECIFIER,
						1, dim, ExpressionConstant::INTEGER_ZERO) );

				return( bfTS );
			}
			return( UINTEGER );
		}
	}
}


TypeSpecifier TypeManager::getTypePosInteger(int dim)
{
	switch( dim )
	{
		case   8:  return( POS_INTEGER );
		case  16:  return( POS_INTEGER );
		case  32:  return( POS_INTEGER );
		case  64:  return( POS_INTEGER );
		case 128:  return( POS_INTEGER );

		default:
		{
			if( dim > 0 )
			{
				TypeSpecifier bfTS( newNumericTypeSpecifier(
						TYPE_POS_INTEGER_ID, TYPE_POS_INTEGER_SPECIFIER,
						1, dim, ExpressionConstant::INTEGER_ONE) );

				return( bfTS );
			}
			return( POS_INTEGER );
		}
	}
}


/**
 * DISPOSER
 */
void TypeManager::dispose()
{
	/*
	 ***************************************************************************
	 * PRIMITE TYPE SPECIFIER
	 ***************************************************************************
	 */
	MapOfTypeSpecifier::iterator itType = getPrimitiveTypeRepository().begin();
	MapOfTypeSpecifier::iterator endType = getPrimitiveTypeRepository().end();
	for( ; itType != endType ; ++itType )
	{
		itType->second.destroy();
	}

	getPrimitiveTypeRepository().clear();


	BOOLEAN.destroy();

	INT8.destroy();
	UINT8.destroy();

	INT16.destroy();
	UINT16.destroy();

	INT32.destroy();
	UINT32.destroy();

	INT64.destroy();
	UINT64.destroy();

	INT128.destroy();
	UINT128.destroy();

	INTEGER.destroy();
	UINTEGER.destroy();
	POS_INTEGER.destroy();

	RATIONAL.destroy();
	URATIONAL.destroy();


	FLOAT.destroy();
	UFLOAT.destroy();

	DOUBLE.destroy();
	UDOUBLE.destroy();

	REAL.destroy();
	UREAL.destroy();

	TIME.destroy();
	CONTINUOUS_TIME.destroy();
	DISCRETE_TIME.destroy();

	CHARACTER.destroy();
	STRING.destroy();

	IDENTIFIER.destroy();
	QUALIFIED_IDENTIFIER.destroy();

	LAMBDA.destroy();

	OPERATOR.destroy();
	AVMCODE.destroy();

	CHANNEL.destroy();
	PORT.destroy();
	MESSAGE.destroy();
	SIGNAL.destroy();
	BUFFER.destroy();
	CONNECTOR.destroy();
	MACHINE.destroy();

	ARRAY_BOOLEAN.destroy();
	ARRAY_CHARACTER.destroy();
	ARRAY_INTEGER.destroy();
	ARRAY_RATIONAL.destroy();
	ARRAY_FLOAT.destroy();

	ARRAY_STRING.destroy();
	ARRAY_IDENTIFIER.destroy();
	ARRAY_QUALIFIED_IDENTIFIER.destroy();
	ARRAY_ENUM.destroy();

	ARRAY_ANY.destroy();

	UNIVERSAL.destroy();
}



}

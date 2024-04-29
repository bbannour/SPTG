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

#ifndef TYPEMANAGER_H_
#define TYPEMANAGER_H_

#include <fml/expression/ExpressionConstant.h>

#include <fml/infrastructure/DataType.h>

#include <fml/type/TypeSpecifier.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/ChoiceTypeSpecifier.h>
#include <fml/type/ClassTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>
#include <fml/type/TypeAliasSpecifier.h>
#include <fml/type/UnionTypeSpecifier.h>

#include <map>


namespace sep
{

class TypeManager;


/**
 * TypeManager
 * singleton
 */
extern const TypeManager & TypeFactory;



class TypeManager
{

public:
	/**
	 * SINGLETON
	 */
	static TypeManager * singleton()
	{
		static TypeManager * instance = new TypeManager();

		return( instance );
	}

private:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TypeManager()
	{
		//!! NOPTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TypeManager(const TypeManager &);

	void operator=(const TypeManager &);


public:
	/**
	 * LOADER - DISPOSER
	 */
	static void load();
	static void dispose();


	////////////////////////////////////////////////////////////////////////////
	// REGISTRY
	////////////////////////////////////////////////////////////////////////////

	typedef std::map< std::string , TypeSpecifier > MapOfTypeSpecifier;

	inline static MapOfTypeSpecifier & getPrimitiveTypeRepository()
	{
		static MapOfTypeSpecifier mPrimitiveTypeSpecifierRepository;

		return( mPrimitiveTypeSpecifierRepository );
	}


	inline static void registerPrimitiveType(const TypeSpecifier & aTS)
	{
		getPrimitiveTypeRepository()[ aTS.getNameID() ] = aTS;
	}

	inline static void registerPrimitiveType(
			const std::string & keyTypeID, const TypeSpecifier & aTS)
	{
		getPrimitiveTypeRepository()[ keyTypeID ] = aTS;
	}


	inline static const TypeSpecifier & getPrimitiveType(
			const std::string & keyTypeID)
	{
		return( getPrimitiveTypeRepository()[ keyTypeID ] );
	}



	/**
	 * GETTER
	 */
	static TypeSpecifier getTypeInteger(int dim);
	static TypeSpecifier getTypeUInteger(int dim);
	static TypeSpecifier getTypePosInteger(int dim);


	/**
	 * CREATOR
	 */
	inline static ContainerTypeSpecifier * newArray(const std::string & aTypeID,
			const TypeSpecifier & aTypeSpecifier, std::size_t aSize)
	{
		return( new ContainerTypeSpecifier(TYPE_ARRAY_SPECIFIER,
				aTypeID, aTypeSpecifier, aSize) );
	}

	inline static ContainerTypeSpecifier * newArray(const BF & astType,
			const TypeSpecifier & aTypeSpecifier, std::size_t aSize)
	{
		return( new ContainerTypeSpecifier(TYPE_ARRAY_SPECIFIER,
				astType.to< DataType >(), aTypeSpecifier, aSize) );
	}


	inline static ClassTypeSpecifier * newClass(const DataType & astType)
	{
		return( new ClassTypeSpecifier(astType) );
	}

	inline static ChoiceTypeSpecifier * newChoice(const DataType & astType)
	{
		return( new ChoiceTypeSpecifier(astType) );
	}

	inline static UnionTypeSpecifier * newUnion(const DataType & astType)
	{
		return( new UnionTypeSpecifier(astType) );
	}


	inline static ContainerTypeSpecifier * newCollection(
			const DataType & astType,
			avm_type_specifier_kind_t aTypeSpecifierKind,
			const TypeSpecifier & aTypeSpecifier, std::size_t aSize)
	{
		return( new ContainerTypeSpecifier(aTypeSpecifierKind,
				astType, aTypeSpecifier, aSize) );
	}


	inline static EnumTypeSpecifier * newEnum(const DataType & astType)
	{
		return( new EnumTypeSpecifier(astType) );
	}

	inline static EnumTypeSpecifier * newEnum(const std::string & aNameID)
	{
		EnumTypeSpecifier * enumT =
				new EnumTypeSpecifier(DataType::nullref());
		enumT->setAllNameID(aNameID, aNameID);

		return( enumT );
	}


	inline static BaseTypeSpecifier * newNumericTypeSpecifier(
			BaseTypeSpecifier * aTypeSpecifier, std::size_t aBitSize,
			const BF & defaultValue)
	{
		return( new BaseTypeSpecifier(
					aTypeSpecifier->getTypeSpecifierKind(),
					aTypeSpecifier->getAstDataType(),
					1, 1, aBitSize, defaultValue) );
	}

	inline static BaseTypeSpecifier * newNumericTypeSpecifier(
			const std::string & aTypeID,
			avm_type_specifier_kind_t aTypeSpecifierKind,
			std::size_t aDataSize, std::size_t aBitSize, const BF & defaultValue)
	{
		return( new BaseTypeSpecifier(aTypeSpecifierKind, aTypeID,
				1, aDataSize, aBitSize, defaultValue) );
	}


	inline static IntervalTypeSpecifier * newInterval(
			const DataType & astType, const TypeSpecifier & aTypeSpecifier,
			IIntervalKind::KIND aNature, const BF & aMin, const BF & aMax)
	{
		return( new IntervalTypeSpecifier(astType,
				aTypeSpecifier, aNature, aMin, aMax) );
	}


	inline static ContainerTypeSpecifier * newClockTime(
			const std::string & aTypeID,
			avm_type_specifier_kind_t aTypeSpecifierKind,
			const TypeSpecifier & aTimeDomain, std::size_t aSize = 1)
	{
		auto * typeSpecifier = new ContainerTypeSpecifier(
				aTypeSpecifierKind, aTypeID, aTimeDomain, aSize);
		typeSpecifier->setDefaultValue( ExpressionConstant::INTEGER_ZERO );

		return( typeSpecifier );
	}

	inline static ContainerTypeSpecifier * newClockTime(
			avm_type_specifier_kind_t aTypeSpecifierKind,
			const TypeSpecifier & aTimeDomain, std::size_t aSize = 1)
	{
		auto * typeSpecifier = new ContainerTypeSpecifier(aTypeSpecifierKind,
				DataType::nullref(), aTimeDomain, aSize);
		typeSpecifier->setDefaultValue( ExpressionConstant::INTEGER_ZERO );

		return( typeSpecifier );
	}


	inline static BaseTypeSpecifier * newCharacter(
			const std::string & aTypeID, std::size_t aSize)
	{
		return( newTypeSpecifier(aTypeID,
				TYPE_CHARACTER_SPECIFIER, aSize, 1, 0,
				ExpressionConstant::CHARACTER_NULL) );
	}

	inline static BaseTypeSpecifier * newString(
			std::size_t minSize, std::size_t maxSize)
	{
		return( newTypeSpecifier(TYPE_STRING_ID, TYPE_STRING_SPECIFIER,
				minSize, maxSize, 1, 0, ExpressionConstant::STRING_EMPTY) );
	}


	inline static TypeAliasSpecifier * newTypeAlias(
			const DataType & astType, const TypeSpecifier & aTypeSpecifier)
	{
		return( new TypeAliasSpecifier(astType, aTypeSpecifier) );
	}


	inline static BaseTypeSpecifier * newTypeSpecifier(
			const std::string & aTypeID,
			avm_type_specifier_kind_t aTypeSpecifierKind,
			std::size_t aSize, std::size_t aDataSize,
			std::size_t aBitSize, const BF & defaultValue = BF::REF_NULL)
	{
		return( new BaseTypeSpecifier(aTypeSpecifierKind, aTypeID,
				aSize, aDataSize, aBitSize, defaultValue) );
	}

	inline static BaseTypeSpecifier * newTypeSpecifier(
			const std::string & aTypeID,
			avm_type_specifier_kind_t aTypeSpecifierKind,
			std::size_t minSize, std::size_t maxSize, std::size_t aDataSize,
			std::size_t aBitSize, const BF & defaultValue = BF::REF_NULL)
	{
		return( new BaseTypeSpecifier(aTypeSpecifierKind, aTypeID,
				minSize, maxSize, aDataSize, aBitSize, defaultValue) );
	}


	/*
	 ***************************************************************************
	 * PRIMITE TYPE NAME IDENTIFIER
	 ***************************************************************************
	 */
	static const std::string & TYPE_ARRAY_ID;

	static const std::string & TYPE_VECTOR_ID;
	static const std::string & TYPE_REVERSE_VECTOR_ID;
	static const std::string & TYPE_LIST_ID;
	static const std::string & TYPE_SET_ID;
	static const std::string & TYPE_MULTISET_ID;
	static const std::string & TYPE_BAG_ID;

	static const std::string & TYPE_FIFO_ID;
	static const std::string & TYPE_LIFO_ID;

	static const std::string & TYPE_ENUM_ID;
	static const std::string & TYPE_UNION_ID;
	static const std::string & TYPE_CHOICE_ID;
	static const std::string & TYPE_STRUCTURE_ID;
	static const std::string & TYPE_CLASS_ID;

	static const std::string & TYPE_BOOL_ID;
	static const std::string & TYPE_BOOLEAN_ID;

	static const std::string & TYPE_INT8_ID;
	static const std::string & TYPE_INT16_ID;
	static const std::string & TYPE_INT32_ID;
	static const std::string & TYPE_INT64_ID;
	static const std::string & TYPE_INT128_ID;

	static const std::string & TYPE_INT_ID;
	static const std::string & TYPE_INTEGER_ID;

	static const std::string & TYPE_RAT_ID;
	static const std::string & TYPE_RATIONAL_ID;

	static const std::string & TYPE_FLOAT_ID;
	static const std::string & TYPE_DOUBLE_ID;
	static const std::string & TYPE_REAL_ID;

	static const std::string & TYPE_UINT8_ID;
	static const std::string & TYPE_UINT16_ID;
	static const std::string & TYPE_UINT32_ID;
	static const std::string & TYPE_UINT64_ID;
	static const std::string & TYPE_UINT128_ID;

	static const std::string & TYPE_UINT_ID;
	static const std::string & TYPE_UINTEGER_ID;
	static const std::string & TYPE_POS_INTEGER_ID;

	static const std::string & TYPE_URAT_ID;
	static const std::string & TYPE_URATIONAL_ID;
	static const std::string & TYPE_POS_RATIONAL_ID;

	static const std::string & TYPE_UFLOAT_ID;
	static const std::string & TYPE_UDOUBLE_ID;
	static const std::string & TYPE_UREAL_ID;

	static const std::string & TYPE_POS_FLOAT_ID;
	static const std::string & TYPE_POS_DOUBLE_ID;
	static const std::string & TYPE_POS_REAL_ID;

	static const std::string & TYPE_CONTINUOUS_TIME_ID;
	static const std::string & TYPE_DENSE_TIME_ID;
	static const std::string & TYPE_DISCRETE_TIME_ID;
	static const std::string & TYPE_TIME_ID;
	static const std::string & TYPE_CLOCK_ID;

	static const std::string & TYPE_CHAR_ID;
	static const std::string & TYPE_CHARACTER_ID;
	static const std::string & TYPE_STRING_ID;

	static const std::string & TYPE_INTERVAL_ID;

	static const std::string & TYPE_ARRAY_BOOLEAN_ID;
	static const std::string & TYPE_ARRAY_CHARACTER_ID;
	static const std::string & TYPE_ARRAY_INTEGER_ID;
	static const std::string & TYPE_ARRAY_RATIONAL_ID;
	static const std::string & TYPE_ARRAY_FLOAT_ID;

	static const std::string & TYPE_ARRAY_STRING_ID;
	static const std::string & TYPE_ARRAY_IDENTIFIER_ID;
	static const std::string & TYPE_ARRAY_QUALIFIED_IDENTIFIER_ID;
	static const std::string & TYPE_ARRAY_ENUM_ID;

	static const std::string & TYPE_ARRAY_ANY_ID;

	static const std::string & TYPE_LAMBDA_ID;

	static const std::string & TYPE_OPERATOR_ID;
	static const std::string & TYPE_AVMCODE_ID;
	static const std::string & TYPE_EXPRESSION_ID;

	static const std::string & TYPE_PORT_ID;
	static const std::string & TYPE_MESSAGE_ID;
	static const std::string & TYPE_SIGNAL_ID;
	static const std::string & TYPE_BUFFER_ID;
	static const std::string & TYPE_CONNECTOR_ID;
	static const std::string & TYPE_MACHINE_ID;
	static const std::string & TYPE_RID_ID;

	static const std::string & TYPE_UNIVERSAL_ID;

	static const std::string & TYPE_SIMULINK_BUS_ID;


	/*
	 ***************************************************************************
	 * PRIMITE TYPE SPECIFIER
	 ***************************************************************************
	 */
	static TypeSpecifier BOOL;
	static TypeSpecifier BOOLEAN;

	static TypeSpecifier INT8;
	static TypeSpecifier UINT8;

	static TypeSpecifier INT16;
	static TypeSpecifier UINT16;

	static TypeSpecifier INT32;
	static TypeSpecifier UINT32;

	static TypeSpecifier INT64;
	static TypeSpecifier UINT64;

	static TypeSpecifier INT128;
	static TypeSpecifier UINT128;

	static TypeSpecifier INT;
	static TypeSpecifier UINT;

	static TypeSpecifier INTEGER;
	static TypeSpecifier UINTEGER;
	static TypeSpecifier POS_INTEGER;

	static TypeSpecifier RAT;
	static TypeSpecifier URAT;

	static TypeSpecifier RATIONAL;
	static TypeSpecifier URATIONAL;
	static TypeSpecifier POS_RATIONAL;

	static TypeSpecifier FLOAT;
	static TypeSpecifier UFLOAT;
	static TypeSpecifier POS_FLOAT;

	static TypeSpecifier DOUBLE;
	static TypeSpecifier UDOUBLE;
	static TypeSpecifier POS_DOUBLE;

	static TypeSpecifier REAL;
	static TypeSpecifier UREAL;
	static TypeSpecifier POS_REAL;


	static TypeSpecifier CLOCK;
	static TypeSpecifier TIME;
	static TypeSpecifier CONTINUOUS_TIME;
	static TypeSpecifier DENSE_TIME;
	static TypeSpecifier DISCRETE_TIME;

	static TypeSpecifier CHAR;
	static TypeSpecifier CHARACTER;
	static TypeSpecifier STRING;

	static TypeSpecifier IDENTIFIER;
	static TypeSpecifier QUALIFIED_IDENTIFIER;

	static TypeSpecifier LAMBDA;

	static TypeSpecifier OPERATOR;
	static TypeSpecifier AVMCODE;
	static TypeSpecifier EXPRESSION;

	static TypeSpecifier CHANNEL;
	static TypeSpecifier PORT;
	static TypeSpecifier MESSAGE;
	static TypeSpecifier SIGNAL;
	static TypeSpecifier BUFFER;
	static TypeSpecifier CONNECTOR;
	static TypeSpecifier MACHINE;

	static TypeSpecifier ARRAY_BOOLEAN;
	static TypeSpecifier ARRAY_CHARACTER;
	static TypeSpecifier ARRAY_INTEGER;
	static TypeSpecifier ARRAY_RATIONAL;
	static TypeSpecifier ARRAY_FLOAT;

	static TypeSpecifier ARRAY_STRING;
	static TypeSpecifier ARRAY_IDENTIFIER;
	static TypeSpecifier ARRAY_QUALIFIED_IDENTIFIER;
	static TypeSpecifier ARRAY_ENUM;

	static TypeSpecifier ARRAY_ANY;

	static TypeSpecifier ARRAY;
	static TypeSpecifier VECTOR;
	static TypeSpecifier LIST;
	static TypeSpecifier SET;
	static TypeSpecifier MULTISET;
	static TypeSpecifier BAG;

	static TypeSpecifier ENUM;
	static TypeSpecifier CLASS;
	static TypeSpecifier STRUCTURE;
	static TypeSpecifier UNION;
	static TypeSpecifier CHOICE;
	static TypeSpecifier INTERVAL;

	static TypeSpecifier UNIVERSAL;

};


}

#endif /* TYPEMANAGER_H_ */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 sept. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXPRESSIONTYPECHECKER_H_
#define EXPRESSIONTYPECHECKER_H_

#include <common/BF.h>

#include <fml/executable/BaseInstanceForm.h>

#include <fml/expression/AvmCode.h>

#include <fml/lib/ITypeSpecifier.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/RuntimeID.h>

#include <fml/type/BaseTypeSpecifier.h>


namespace sep
{


class Element;
class ContainerTypeSpecifier;
class ClassTypeSpecifier;
class EnumTypeSpecifier;


class ExpressionTypeChecker
{
public:

	static bool isFinalSymbolicBasicSymbol(const BF & anElement);

	static bool isFinalSymbolicCompositeSymbol(const BF & anElement);

	static bool isFinalSymbolicCompositeSymbol(BuiltinArray * arrayForm);

	inline static bool isFinalSymbolicSymbol(const BF & anElement)
	{
		return( isFinalSymbolicBasicSymbol(anElement) ||
				isFinalSymbolicCompositeSymbol(anElement) );
	}


	inline static bool isMacro(const BF & anExpr)
	{
		return( (anExpr.is< BaseInstanceForm >() &&
				anExpr.to_ptr< BaseInstanceForm >()->getModifier().hasNatureMacro()) ||
				(anExpr.is< AvmCode >() &&
						isMacro(anExpr.to_ptr< AvmCode >())) );
	}

	inline static bool isMacro(AvmCode * aCode)
	{
		return( OperatorManager::isQuote( aCode->getOperator() ) );
	}


	static bool isMachine(const BF & anExpr);

	inline static bool isPort(const BF & anExpr)
	{
		return( anExpr.is< BaseInstanceForm >() &&
				anExpr.to_ptr< BaseInstanceForm >()->isTypedPort()  );
	}

	inline static bool isBuffer(const BF & anExpr)
	{
		return( anExpr.is< BaseInstanceForm >() &&
				anExpr.to_ptr< BaseInstanceForm >()->isTypedBuffer() );
	}

	inline static bool isMessage(const BF & anExpr)
	{
		return( anExpr.is< BaseInstanceForm >() &&
				anExpr.to_ptr< BaseInstanceForm >()->isTypedMessage() );
	}


	inline static bool isEnumeration(const BF & anExpr)
	{
		return( isEnum(anExpr) || isCharacter(anExpr) || isBoolean(anExpr) );
	}

	static bool isArray(
			ContainerTypeSpecifier * refTypeSpecifier, const BF & anExpr);

	static bool isClass(
			ClassTypeSpecifier * refTypeSpecifier, const BF & anExpr);

	static bool isCollection(
			ContainerTypeSpecifier * refTypeSpecifier, const BF & anExpr);

	static bool isVector(const BF & anExpr);


	static bool isEnum(
			EnumTypeSpecifier * refTypeSpecifier, const BF & anExpr);

	static bool isEnum(const BF & anExpr);

	static bool isCharacter(const BF & anExpr);

	static bool isString(const BF & anExpr);


	static bool isBoolean(const BF & anExpr, bool stronglyTypedFlag = true);

	inline static bool isNumeric(const BF & anExpr)
	{
		return( isReal(anExpr) || isEnum(anExpr) );
//				|| isFloat(anExpr) || isRational(anExpr) || isInteger(anExpr) );
	}

	static bool isInteger(const BF & anExpr);

	static bool isRational(const BF & anExpr);

	static bool isFloat(const BF & anExpr);

	static bool isReal(const BF & anExpr);


	static bool isOperator(const BF & anExpr);

	static bool isAvmCode(const BF & anExpr);


	inline static bool isClock(const BF & anExpr)
	{
		return( isReal(anExpr) );
	}

	inline static bool isTime(const BF & anExpr)
	{
		return( isReal(anExpr) );
	}

	inline static bool isCTime(const BF & anExpr)
	{
		return( isReal(anExpr) );
	}

	inline static bool isDTime(const BF & anExpr)
	{
		return( isInteger(anExpr) );
	}


	inline static bool isCtor(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isCtor(anExpr.to_ptr< AvmCode >()) );
	}

	inline static bool isCtor(AvmCode * aCode)
	{
		return( OperatorManager::isCtor( aCode->getOperator() ) );
	}

	static bool isCtor(BaseTypeSpecifier * refTypeSpecifier, AvmCode * aCode);


	inline static bool isNewfresh(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isNewfresh(anExpr.to_ptr< AvmCode >()) );
	}

	inline static bool isNewfresh(AvmCode * aCode)
	{
		return( OperatorManager::isNewfresh( aCode->getOperator() ) );
	}

	static bool isNewfresh(BaseTypeSpecifier * refTypeSpecifier, AvmCode * aCode);


	inline static bool isLookup(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isLookup(anExpr.to_ptr< AvmCode >()) );
	}

	inline static bool isLookup(AvmCode * aCode)
	{
		return( OperatorManager::isLookup( aCode->getOperator() ) );
	}


	inline static bool isLookup1D(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isLookup1D(anExpr.to_ptr< AvmCode >()) );
	}

	inline static bool isLookup1D(AvmCode * aCode)
	{
		return( OperatorManager::isLookup1D( aCode->getOperator() ) );
	}


	inline static bool isLookup2D(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isLookup2D(anExpr.to_ptr< AvmCode >()) );
	}

	inline static bool isLookup2D(AvmCode * aCode)
	{
		return( OperatorManager::isLookup2D( aCode->getOperator() ) );
	}


	static bool isTyped(BaseTypeSpecifier * refTypeSpecifier,
			BaseTypeSpecifier * aTypeSpecifier);


	inline static bool weaklyTyped(BaseTypeSpecifier * refTypeSpecifier,
			BaseTypeSpecifier * aTypeSpecifier)
	{
		if( isTyped(refTypeSpecifier, aTypeSpecifier) )
		{
			return( true );
		}
		else
		{
			return( refTypeSpecifier->weaklyTyped(
					aTypeSpecifier->getTypeSpecifierKind()) );
		}
	}


	static bool isTyped(BaseTypeSpecifier * refTypeSpecifier, const BF & arg);


};

}

#endif /* EXPRESSIONTYPECHECKER_H_ */

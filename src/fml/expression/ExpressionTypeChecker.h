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
#include <fml/type/TypeSpecifier.h>


namespace sep
{

class BuiltinArray;
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
				anExpr.to< BaseInstanceForm >().getModifier().hasNatureMacro())
			|| (anExpr.is< AvmCode >() &&
						isMacro(anExpr.to< AvmCode >())) );
	}

	inline static bool isMacro(const AvmCode & aCode)
	{
		return( OperatorManager::isQuote( aCode.getOperator() ) );
	}


	static bool isMachine(
			const BaseTypeSpecifier & refTypeSpecifier, const BF & anExpr);

	inline static bool isPort(
			const BaseTypeSpecifier & refTypeSpecifier, const BF & anExpr)
	{
		return( anExpr.is< BaseInstanceForm >() &&
				anExpr.to< BaseInstanceForm >().isTypedPort()  );
	}

	inline static bool isBuffer(
			const BaseTypeSpecifier & refTypeSpecifier, const BF & anExpr)
	{
		return( anExpr.is< BaseInstanceForm >() &&
				anExpr.to< BaseInstanceForm >().isTypedBuffer() );
	}

	inline static bool isMessage(
			const BaseTypeSpecifier & refTypeSpecifier, const BF & anExpr)
	{
		return( anExpr.is< BaseInstanceForm >() &&
				anExpr.to< BaseInstanceForm >().isTypedMessage() );
	}


	inline static bool isEnumeration(const BF & anExpr)
	{
		return( isEnum(anExpr) || isCharacter(anExpr) || isBoolean(anExpr) );
	}

	static bool isArray(
			const ContainerTypeSpecifier & refTypeSpecifier, const BF & anExpr);

	static bool isClass(
			const ClassTypeSpecifier & refTypeSpecifier, const BF & anExpr);

	static bool isCollection(
			const ContainerTypeSpecifier & refTypeSpecifier, const BF & anExpr);

	static bool isCollectionOfTypedElement(
			const BaseTypeSpecifier & refTypeSpecifier, const BF & anExpr);

	static bool isVector(const BF & anExpr);


	static bool isEnum(
			const EnumTypeSpecifier & refTypeSpecifier, const BF & anExpr);

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


	// TIME & CLOCK type checking
	inline static bool isweaklyClock(const BF & anExpr)
	{
		return( isReal(anExpr) );
	}

	inline static bool isweaklyTime(const BF & anExpr)
	{
		return( isReal(anExpr) );
	}

	inline static bool isweaklyCTime(const BF & anExpr)
	{
		return( isReal(anExpr) );
	}

	inline static bool isweaklyDTime(const BF & anExpr)
	{
		return( isInteger(anExpr) );
	}


	inline static bool isClock(
			const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr)
	{
		return( isClockTime(typeSpecifier, anExpr) );
	}

	inline static bool isTime(
			const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr)
	{
		return( isClockTime(typeSpecifier, anExpr) );
	}

	static bool isClockTime(
			const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr);

	static bool isClockTime(const BF & anExpr);

	static bool isContinuousTime(
			const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr);

	static bool isDenseTime(
			const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr);

	static bool isDiscreteTime(
			const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr);


	inline static bool isCtor(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isCtor(anExpr.to< AvmCode >()) );
	}

	inline static bool isCtor(const AvmCode & aCode)
	{
		return( OperatorManager::isCtor( aCode.getOperator() ) );
	}

	static bool isCtor(
			const BaseTypeSpecifier & refTypeSpecifier, const AvmCode & aCode);


	inline static bool isNewfresh(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isNewfresh(anExpr.to< AvmCode >()) );
	}

	inline static bool isNewfresh(const AvmCode & aCode)
	{
		return( OperatorManager::isNewfresh( aCode.getOperator() ) );
	}

	static bool isNewfresh(
			const BaseTypeSpecifier & refTypeSpecifier, const AvmCode & aCode);


	inline static bool isArithmetic(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isArithmetic(anExpr.to< AvmCode >()) );
	}

	inline static bool isArithmetic(const AvmCode & aCode)
	{
		return( OperatorManager::isArithmetic( aCode.getOperator() ) );
	}


	inline static bool isPropositional(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isPropositional(anExpr.to< AvmCode >()) );
	}

	inline static bool isPropositional(const AvmCode & aCode)
	{
		return( OperatorManager::isPropositional( aCode.getOperator() ) );
	}


	inline static bool isQuantifier(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isQuantifier(anExpr.to< AvmCode >()) );
	}

	inline static bool isQuantifier(const AvmCode & aCode)
	{
		return( OperatorManager::isQuantifier( aCode.getOperator() ) );
	}


	inline static bool isLookup(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isLookup(anExpr.to< AvmCode >()) );
	}

	inline static bool isLookup(const AvmCode & aCode)
	{
		return( OperatorManager::isLookup( aCode.getOperator() ) );
	}


	inline static bool isLookup1D(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isLookup1D(anExpr.to< AvmCode >()) );
	}

	inline static bool isLookup1D(const AvmCode & aCode)
	{
		return( OperatorManager::isLookup1D( aCode.getOperator() ) );
	}


	inline static bool isLookup2D(const BF & anExpr)
	{
		return( anExpr.is< AvmCode >() &&
				isLookup2D(anExpr.to< AvmCode >()) );
	}

	inline static bool isLookup2D(const AvmCode & aCode)
	{
		return( OperatorManager::isLookup2D( aCode.getOperator() ) );
	}


	static bool isTyped(const BaseTypeSpecifier & refTypeSpecifier,
			const BaseTypeSpecifier & aTypeSpecifier);

	inline static bool isTyped(const BaseTypeSpecifier & refTypeSpecifier,
			const TypeSpecifier & aTypeSpecifier)
	{
		return( isTyped(refTypeSpecifier, aTypeSpecifier.refType()) );
	}


	inline static bool weaklyTyped(const BaseTypeSpecifier & refTypeSpecifier,
			const BaseTypeSpecifier & aTypeSpecifier)
	{
		if( isTyped(refTypeSpecifier, aTypeSpecifier) )
		{
			return( true );
		}
		else
		{
			return( refTypeSpecifier.weaklyTyped(
					aTypeSpecifier.getTypeSpecifierKind()) );
		}
	}


	static bool isTyped(
			const BaseTypeSpecifier & refTypeSpecifier, const BF & arg);


};

}

#endif /* EXPRESSIONTYPECHECKER_H_ */

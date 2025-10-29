/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BF.h"

#include <fml/common/ObjectElement.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionComparer.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionFactory.h>

//#include <fml/symbol/Symbol.h>
//#include <fml/pointer/Type.h>

#include <fml/runtime/RuntimeID.h>

#include <fml/workflow/UniFormIdentifier.h>


namespace sep
{


/**
 * INSTANCE COUNTER
 */
std::uint64_t BF::INSTANCE_COUNTER_ASP = 0;


/*
 * STATIC
 * ATTRIBUTES
 */

/**
 * DEFAULT NULL
 */
BF BF::REF_NULL;


/**
 * Finalize
 */
void BF::finalize()
{
	if( (mPTR != nullptr) && (mPTR->getRefCount() > 1) )
	{
AVM_IF_DEBUG_FLAG( REFERENCE_COUNTING )
	Element * pbf = /*dynamic_cast< Element * >*/( mPTR );
	if( pbf != nullptr )
	{
		AVM_OS_LOG << "finalize< " << pbf->classKindName()
				<< "> @ " << std::addressof( pbf )
				<< " x " << pbf->getRefCount() << " : " << pbf->str()
				<< std::endl;
	}
AVM_ENDIF_DEBUG_FLAG( REFERENCE_COUNTING )

		mPTR->setRefCount( 1 );
	}

	release( nullptr );
}


/**
 * NUMERIC or SIMPLE TYPE TEST & CAST
 */

bool BF::isBoolean() const
{
	return( ExpressionFactory::isBoolean(*this) );
}

bool BF::toBoolean() const
{
	return( ExpressionFactory::toBoolean(*this) );
}


bool BF::isEqualFalse() const
{
	return( this->isTEQ( ExpressionConstant::BOOLEAN_FALSE ) ||
			ExpressionFactory::isEqualFalse(*this) );
}

bool BF::isNotEqualFalse() const
{
	return( ExpressionFactory::isNotEqualFalse(*this) );
}


bool BF::isEqualTrue() const
{
	return( this->isTEQ( ExpressionConstant::BOOLEAN_TRUE ) ||
			ExpressionFactory::isEqualTrue(*this) );
}

bool BF::isNotEqualTrue() const
{
	return( ExpressionFactory::isNotEqualTrue(*this) );
}





/**
 * GETTER
 * for simple or numeric kind
 */
bool BF::isEqualZero() const
{
	return( this->isTEQ( ExpressionConstant::INTEGER_ZERO ) ||
			(this->is< Number >() && this->to< Number >().isZero()) );
}

bool BF::isEqualOne() const
{
	return( this->isTEQ( ExpressionConstant::INTEGER_ONE ) ||
			(this->is< Number >() && this->to< Number >().isOne()) );
}


bool BF::isNumber() const
{
	return( ExpressionFactory::isNumber(*this) );
}

bool BF::isNumeric() const
{
	return( ExpressionFactory::isNumeric(*this) );
}


bool BF::isExpression() const
{
	return( this->is< AvmCode >() );
}



bool BF::isInt32() const
{
	return( ExpressionFactory::isInt32(*this) );
}

std::int32_t BF::toInt32() const
{
	return( ExpressionFactory::toInt32(*this) );
}


bool BF::isInt64() const
{
	return( ExpressionFactory::isInt64(*this) );
}

std::int64_t BF::toInt64() const
{
	return( ExpressionFactory::toInt64(*this) );
}


bool BF::isInteger() const
{
	return( ExpressionFactory::isInteger(*this) );
}

avm_integer_t BF::toInteger() const
{
	return( ExpressionFactory::toInteger(*this) );
}


bool BF::isPosInteger() const
{
	return( ExpressionFactory::isPosInteger(*this) );
}


bool BF::isUInteger() const
{
	return( ExpressionFactory::isUInteger(*this) );
}

avm_uinteger_t BF::toUInteger() const
{
	return( ExpressionFactory::toUInteger(*this) );
}

bool BF::isRational() const
{
	return( ExpressionFactory::isRational(*this) );
}

avm_integer_t BF::toDenominator() const
{
	return( ExpressionFactory::toDenominator(*this) );
}
avm_integer_t BF::toNumerator() const
{
	return( ExpressionFactory::toNumerator(*this) );
}


bool BF::isFloat() const
{
	return( ExpressionFactory::isFloat(*this) );
}

avm_float_t BF::toFloat() const
{
	return( ExpressionFactory::toFloat(*this) );
}


bool BF::isReal() const
{
	return( ExpressionFactory::isReal(*this) );
}

avm_real_t BF::toReal() const
{
	return( ExpressionFactory::toReal(*this) );
}


bool BF::isCharacter() const
{
	return( ExpressionFactory::isCharacter(*this) );
}

char BF::toCharacter() const
{
	return( ExpressionFactory::toCharacter(*this) );
}


bool BF::isBuiltinString() const
{
	return( ExpressionFactory::isBuiltinString(*this) );
}

std::string BF::toBuiltinString() const
{
	return( ExpressionFactory::toBuiltinString(*this) );
}


bool BF::isIdentifier() const
{
	return( ExpressionFactory::isIdentifier(*this) );
}

std::string BF::toIdentifier() const
{
	return( ExpressionFactory::toIdentifier(*this) );
}


bool BF::isUfi() const
{
	return( ExpressionFactory::isUfi(*this) );
}

std::string BF::toUfi() const
{
	return( ExpressionFactory::toUfi(*this) );
}

std::string BF::toUfid() const
{
	return( ExpressionFactory::toUfid(*this) );
}


bool BF::isEnumSymbol() const
{
	return( ExpressionFactory::isEnumSymbol(*this) );
}

std::string BF::strEnumSymbol() const
{
	return( ExpressionFactory::strEnumSymbol(*this) );
}


bool BF::isUFID() const
{
	return( isUfid() || is< UniFormIdentifier >() );
}


bool BF::isBuiltinValue() const
{
	return( ExpressionFactory::isBuiltinValue(*this) );
}


bool BF::isConstValue() const
{
	return( ExpressionFactory::isConstValue(*this) );
}


/**
 * REFERENCE
 * CAST
 */
BFCode & BF::bfCode()
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( is< AvmCode >() )
			<< "Invalid << BF< AvmCode > >> Type <"
			<< classKindName() << ">( " << str() << " ) Cast !!!"
			<< SEND_EXIT;

	return( static_cast< BFCode & >( *this ) );
}
const BFCode & BF::bfCode() const
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( is< AvmCode >() )
			<< "Invalid << BF< AvmCode > >> Type <"
			<< classKindName() << ">( " << str() << " ) Cast !!!"
			<< SEND_EXIT;

	return( static_cast< const BFCode & >( *this ) );
}

const RuntimeID & BF::bfRID() const
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( is< RuntimeID::raw_value_t >() )
			<< "Invalid << BF< RuntimeID > >> Type <"
			<< classKindName() << ">( " << str() << " ) Cast !!!"
			<< SEND_EXIT;

	return( static_cast< const RuntimeID & >( *this ) );
}


/**
 * BUILD NEW EXPRESSION
 */
BF & BF::opExpr(const Operator * anOperator, const BF & arg)
{
	return( *this = ExpressionConstructor::newCode(anOperator, *this, arg) );
}


BF & BF::eqExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::eqExpr(*this, arg));
}

BF & BF::neqExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::neqExpr(*this, arg) );
}


BF & BF::ltExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::ltExpr(*this, arg) );
}

BF & BF::lteExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::lteExpr(*this, arg) );
}


BF & BF::gtExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::gtExpr(*this, arg) );
}

BF & BF::gteExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::gteExpr(*this, arg) );
}




BF & BF::andExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::andExpr(*this, arg) );
}

BF & BF::orExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::orExpr(*this, arg) );
}

BF & BF::notExpr()
{
	return( *this = ExpressionConstructor::notExpr(*this) );
}


BF & BF::addExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::addExpr(*this, arg) );
}

BF & BF::incrExpr(avm_uinteger_t val)
{
	return( *this = ExpressionConstructor::addExpr(*this, val) );
}


BF & BF::minusExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::minusExpr(*this, arg) );
}

BF & BF::uminusExpr()
{
	return( *this = ExpressionConstructor::uminusExpr(*this) );
}

BF & BF::decrExpr(avm_uinteger_t val)
{
	return( *this = ExpressionConstructor::addExpr(*this, (- val)) );
}


BF & BF::multExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::multExpr(*this, arg) );
}

BF & BF::powExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::powExpr(*this, arg) );
}

BF & BF::divExpr(const BF & arg)
{
	return( *this = ExpressionConstructor::divExpr(*this, arg) );
}

BF & BF::invExpr()
{
	return( *this = ExpressionConstructor::divExpr(
			ExpressionConstructor::newExpr((avm_integer_t) 1), *this) );
}



/**
 * COMPARISON
 */
int BF::compare(const BF & other) const
{
	return( (mPTR == other.mPTR) ? 0 :
			ExpressionComparer::compare(*this, other) );
}

int BF::compare_share(BF & other)
{
	if( mPTR == other.mPTR )
	{
		return( 0 );
	}
	else
	{
		int cmpResult = ExpressionComparer::compare(*this, other);
		if( cmpResult == 0 )
		{
			share( other );
		}
		return( cmpResult );
	}
}


bool BF::isEQ(const BF & other) const
{
	return ExpressionComparer::isEQ(*this, other);
}


///**
// * ASSIGNMENT
// * Symbol
// * Type
// */
//inline BF & BF::operator=(const Symbol & aSymbol)
//{
//	if( mPTR != aSymbol.rawSymbol() )
//	{
//		AVM_ASSIGN_DEBUG_BF_PTR( aSymbol.raw_pointer() )
//
//		release( aSymbol.rawSymbol() );
//	}
//	return( *this );
//}
//
//// Type
//BF & BF::operator=(const Type & aType)
//{
//	if( mPTR != aType.rawType() )
//	{
//		AVM_ASSIGN_DEBUG_BF_PTR( aType.raw_pointer() )
//
//		release( aType.rawType() );
//	}
//	return( *this );
//}



/**
 * strHeader
 */
void BF::strHeader(OutStream & os) const
{
	if( this->is< ObjectElement >() )
	{
		this->to< ObjectElement >().strHeader( os );
	}
	else
	{
		os << this->str();
	}
}


}

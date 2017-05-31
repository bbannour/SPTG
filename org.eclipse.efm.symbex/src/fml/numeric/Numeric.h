/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 1 mars 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_EXPRESSION_NUMERIC_H_
#define FML_EXPRESSION_NUMERIC_H_

#include <base/ClassKindInfo.h>
#include <base/SmartPointer.h>
#include <fml/numeric/Number.h>

#include <util/avm_assert.h>
#include <common/BF.h>


#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

#include <fml/numeric/gmp/NumericImpl.h>

#elif defined( _AVM_BUILTIN_NUMERIC_BOOST_ )

#include <fml/numeric/boost/NumericImpl.h>

#else

#include <fml/numeric/basic/NumericImpl.h>

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>
#include <fml/numeric/Float.h>


namespace sep
{


class Operator;


class Numeric :
		public SmartPointer< Number , DestroyElementPolicy >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Numeric )
{

private:
	/**
	 * TYPEDEF
	 */
	typedef SmartPointer< Number , DestroyElementPolicy >  base_this_type;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Numeric()
	: base_this_type( )
	{
		//!! NOTHING
	}

	Numeric(Number * aNumber)
	: base_this_type( aNumber )
	{
		//!! NOTHING
	}


	Numeric(const Integer & aNumber)
	: base_this_type( new Integer(aNumber) )
	{
		//!! NOTHING
	}

	Numeric(Integer * aNumber)
	: base_this_type( aNumber )
	{
		//!! NOTHING
	}

	Numeric(const Rational & aNumber)
	: base_this_type( new Rational(aNumber) )
	{
		//!! NOTHING
	}

	Numeric(Rational * aNumber)
	: base_this_type( aNumber )
	{
		//!! NOTHING
	}


	Numeric(const Float & aNumber)
	: base_this_type( new Float(aNumber) )
	{
		//!! NOTHING
	}

	Numeric(Float * aNumber)
	: base_this_type( aNumber )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Builtin
	 */
//	// avm_int8_t
//	Numeric(avm_int8_t aNumber)
//	: base_this_type( new Integer( aNumber ) )
//	{
//		//!! NOTHING
//	}
//
//	// avm_uint8_t
//	Numeric(avm_uint8_t aNumber)
//	: base_this_type( new Integer( aNumber ) )
//	{
//		//!! NOTHING
//	}
//
//	// avm_int16_t
//	Numeric(avm_int16_t aNumber)
//	: base_this_type( new Integer( aNumber ) )
//	{
//		//!! NOTHING
//	}
//
//	// avm_uint16_t
//	Numeric(avm_uint16_t aNumber)
//	: base_this_type( new Integer( aNumber ) )
//	{
//		//!! NOTHING
//	}
//
//	// avm_int32_t
//	Numeric(avm_int32_t aNumber)
//	: base_this_type( new Integer( aNumber ) )
//	{
//		//!! NOTHING
//	}
//
//	// avm_uint32_t
//	Numeric(avm_uint32_t aNumber)
//	: base_this_type( new Integer( aNumber ) )
//	{
//		//!! NOTHING
//	}

	// int
	Numeric(int aNumber)
	: base_this_type( new Integer( aNumber ) )
	{
		//!! NOTHING
	}

	// uint32_t
	Numeric(unsigned int aNumber)
	: base_this_type( new Integer( aNumber ) )
	{
		//!! NOTHING
	}

#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// long
	Numeric(long aNumber)
	: base_this_type( new Integer( aNumber ) )
	{
		//!! NOTHING
	}

	// unsigned long
	Numeric(unsigned long aNumber)
	: base_this_type( new Integer( aNumber ) )
	{
		//!! NOTHING
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */

	// avm_integer_t  i.e.  avm_int64_t
	Numeric(avm_integer_t aNumber)
	: base_this_type( new Integer( aNumber ) )
	{
		//!! NOTHING
	}

	Numeric(avm_uinteger_t aNumber)
	: base_this_type( new Integer( aNumber ) )
	{
		//!! NOTHING
	}


	// Integer / Integer
	Numeric(const Integer & aNumerator, const Integer & aDenominator)
	: base_this_type( new Rational(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	// avm_integer_t / avm_integer_t  i.e.  avm_int64_t / avm_int64_t
	Numeric(avm_integer_t aNumerator, avm_integer_t aDenominator)
	: base_this_type( new Rational(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t / avm_integer_t  i.e.  avm_uint64_t / avm_int64_t
	Numeric(avm_uinteger_t aNumerator, avm_integer_t aDenominator)
	: base_this_type( new Rational(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	// avm_integer_t / avm_uinteger_t  i.e.  avm_int64_t / avm_uint64_t
	Numeric(avm_integer_t aNumerator, avm_uinteger_t aDenominator)
	: base_this_type( new Rational(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	// std::string / avm_integer_t  i.e.  std::string / avm_int64_t
	Numeric(const std::string & aNumerator, avm_integer_t aDenominator)
	: base_this_type( new Rational(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	// avm_integer_t / std::string  i.e.  avm_integer_t / std::string
	Numeric(avm_integer_t aNumerator, const std::string & aDenominator)
	: base_this_type( new Rational(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	// std::string / std::string
	Numeric(const std::string & aNumerator, const std::string & aDenominator)
	: base_this_type( new Rational(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}


	// float
	Numeric(float aNumber)
	: base_this_type( new Float( aNumber ) )
	{
		//!! NOTHING
	}

	// avm_float_t  i.e.  double
	Numeric(avm_float_t aNumber)
	: base_this_type( new Float( aNumber ) )
	{
		//!! NOTHING
	}

	// const std::string &
	Numeric(const std::string & aNumber)
	: base_this_type( )
	{
		setStringNumber( aNumber );
	}

	inline void setStringNumber(const std::string & aNumber)
	{
		std::string::size_type pos = aNumber.find('/');
		if( pos != std::string::npos)
		{
			release( new Rational(
					aNumber.substr(0, pos), aNumber.substr(pos+1) ) );
		}
		else if( (pos = aNumber.find('.')) != std::string::npos )
		{
			release( new Float( aNumber ) );

//			replacePointer( new Rational(
//					std::string(aNumber).erase(pos, 1),
//					Integer::pow(10, aNumber.size() - (pos + 1)) ) );
		}
		else
		{
			release( new Integer( aNumber ) );
		}
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Numeric(const Numeric & aNumeric)
	: base_this_type( aNumeric )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Numeric()
	{
		//!! NOTHING
	}


	/**
	 * ACQUIRE POINTER
	 */
	static Numeric acquire(Number * aNumber)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aNumber )
				<< "Number in Numeric::acquire() !!!"
				<< SEND_EXIT;

		aNumber->incrRefCount();
		return( Numeric( aNumber ) );
	}

	/**
	 * GETTER
	 * ClassKindInfo
	 */
	inline class_kind_t classKind() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in Numeric::classKind() !!!"
				<< SEND_EXIT;

		return( mPTR->classKind() );
	}

	inline const std::string & classKindName() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in Numeric::classKindName() !!!"
				<< SEND_EXIT;

		return( mPTR->classKindName() );
	}

	inline std::string classKindInfo() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in Numeric::classKindInfo() !!!"
				<< SEND_EXIT;

		return( mPTR->classKindInfo() );
	}

	// Check if Numeric is a handle to a T, including base classes.
	template<class T >
	inline bool is() const
	{
		return( (mPTR != NULL) && mPTR->is< T >() );
	}

	template< class T >
	inline const T & to_ref() const
	{
		return( mPTR->to_ref< T >() );
	}


	/**
	 * operator= <expression>
	 */
	inline Numeric & operator=(const BF & anExpression)
	{
		if( mPTR != anExpression.raw_pointer() )
		{
			AVM_OS_ASSERT_FATAL_ERROR_EXIT( anExpression.is< Number >() )
					<< "Invalid Assignment Cast of a <BF> to a <Numeric> !!!"
					<< SEND_EXIT;

			release_acquire( anExpression.to_ptr< Number >() );
		}

		return( *this );
	}

	/**
	 * operator=
	 */

	// Integer
	inline Numeric & operator=(const Integer & aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}

	// Rational
	inline Numeric & operator=(const Rational & aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}

	// Float
	inline Numeric & operator=(const Float & aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}

//	// avm_int8_t
//	inline Numeric & operator=(avm_int8_t aNumber)
//	{
//		return( this->operator=( Numeric( aNumber ) ) );
//	}
//
//	// avm_uint8_t
//	inline Numeric & operator=(avm_uint8_t aNumber)
//	{
//		return( this->operator=( Numeric( aNumber ) ) );
//	}
//
//	// avm_int16_t
//	inline Numeric & operator=(avm_int16_t aNumber)
//	{
//		return( this->operator=( Numeric( aNumber ) ) );
//	}
//
//	// avm_uint16_t
//	inline Numeric & operator=(avm_uint16_t aNumber)
//	{
//		return( this->operator=( Numeric( aNumber ) ) );
//	}
//
//	// avm_int32_t
//	inline Numeric & operator=(avm_int32_t aNumber)
//	{
//		return( this->operator=( Numeric( aNumber ) ) );
//	}
//
//	// avm_uint32_t
//	inline Numeric & operator=(avm_uint32_t aNumber)
//	{
//		return( this->operator=( Numeric( aNumber ) ) );
//	}

	// int
	inline Numeric & operator=(int aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}

	// unsigned int
	inline Numeric & operator=(unsigned int aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}

#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// long
	inline Numeric & operator=(long aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}

	// unsigned long
	inline Numeric & operator=(unsigned long aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */

	// avm_integer_t
	inline Numeric & operator=(avm_integer_t aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}

	// avm_uinteger_t
	inline Numeric & operator=(avm_uinteger_t aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}

	// float
	inline Numeric & operator=(float aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}

	// avm_float_t  i.e.  double
	inline Numeric & operator=(avm_float_t aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}


	// const std::string &
	inline Numeric & operator=(const std::string & aNumber)
	{
		return( this->operator=( Numeric( aNumber ) ) );
	}


	/**
	 * SIGN TESTS
	 */
	inline int sign() const
	{
		return( mPTR->sign() );
	}


	inline bool isPositive() const
	{
		return( mPTR->isPositive() );
	}

	inline bool strictlyPositive() const
	{
		return( mPTR->strictlyPositive() );
	}


	inline bool isNegative() const
	{
		return( mPTR->isNegative() );
	}

	inline bool strictlyNegative() const
	{
		return( mPTR->strictlyNegative() );
	}

	/**
	 * BASICS TESTS
	 */
	inline bool isZero() const
	{
		return( mPTR->isZero() );
	}

	inline bool isOne() const
	{
		return( mPTR->isOne() );
	}

	inline bool isNegativeOne() const
	{
		return( mPTR->isNegativeOne() );
	}

	/**
	 * CONVERSION
	 */
	// Int32
	inline bool isInt32() const
	{
		return( mPTR->isInt32() );
	}

	inline avm_int32_t toInt32() const
	{
		return( mPTR->toInt32() );
	}

	// Int64
	inline bool isInt64() const
	{
		return( mPTR->isInt64() );
	}

	inline avm_int64_t toInt64() const
	{
		return( mPTR->toInt64() );
	}

	// Integer
	inline bool isInteger() const
	{
		return( mPTR->isInteger() );
	}

	inline avm_integer_t toInteger() const
	{
		return( mPTR->toInteger() );
	}

	// Rational
	inline bool isRational() const
	{
		return( mPTR->sign() );
	}

	inline avm_integer_t toDenominator() const
	{
		return( mPTR->sign() );
	}

	inline avm_integer_t toNumerator() const
	{
		return( mPTR->sign() );
	}

	// Float
	inline bool isFloat() const
	{
		return( mPTR->sign() );
	}

	inline avm_float_t toFloat() const
	{
		return( mPTR->sign() );
	}

	// Real
	inline bool isReal() const
	{
		return( mPTR->sign() );
	}

	inline avm_real_t toReal() const
	{
		return( mPTR->sign() );
	}


	/**
	 * POINTER TRIVIALLY EQUAL COMPARISON
	 */
	inline bool isTEQ(const Numeric & aNumeric) const
	{
		return( mPTR == aNumeric.mPTR );
	}

	inline bool isTEQ(const Number & aNumber) const
	{
		return( mPTR == &aNumber );
	}

	inline bool isTEQ(const Number * aNumber) const
	{
		return( mPTR == aNumber );
	}

	inline bool isTEQ(const BF & anExpression) const
	{
		return( mPTR == anExpression.raw_pointer() );
	}


	inline bool isNTEQ(const Numeric & aNumeric) const
	{
		return( mPTR != aNumeric.mPTR );
	}

	inline bool isNTEQ(const Number & aNumber) const
	{
		return( mPTR != (& aNumber) );
	}

	inline bool isNTEQ(const Number * aNumber) const
	{
		return( mPTR != aNumber );
	}

	inline bool isNTEQ(const BF & anExpression) const
	{
		return( mPTR != anExpression.raw_pointer() );
	}


	/**
	 * COMPARISON
	 */
	inline bool isEQ(const Numeric & aNumeric) const
	{
		return( this->operator==( aNumeric ) );
	}

	inline bool isEQ(const Number & aNumber) const
	{
		return( this->operator==( aNumber ) );
	}

	inline bool isEQ(const BF & anExpression) const
	{
		return( this->operator==( anExpression.as_ref< Number >() ) );
	}


	inline bool isNEQ(const Numeric & aNumeric) const
	{
		return( this->operator!=( aNumeric ) );
	}

	inline bool isNEQ(const Number & aNumber) const
	{
		return( this->operator!=( aNumber ) );
	}

	inline bool isNEQ(const BF & anExpression) const
	{
		return( this->operator!=( anExpression.as_ref< Number >() ) );
	}


	inline bool strEQ(const Numeric & aNumeric) const
	{
		return( this->operator==( aNumeric ) );
	}

	inline bool strEQ(const Number & aNumber) const
	{
		return( this->operator==( aNumber ) );
	}

	inline bool strEQ(const BF & anExpression) const
	{
		return( this->operator==( anExpression.as_ref< Number >() ) );
	}


	inline bool strNEQ(const Numeric & aNumeric) const
	{
		return( this->operator!=( aNumeric ) );
	}

	inline bool strNEQ(const Number & aNumber) const
	{
		return( this->operator!=( aNumber ) );
	}

	inline bool strNEQ(const BF & anExpression) const
	{
		return( this->operator!=( anExpression.as_ref< Number >() ) );
	}


////////////////////////////////////////////////////////////////////////////////
// bool operator...
////////////////////////////////////////////////////////////////////////////////

#define BOOL_OPERATION_AUX(op, number, numeric) \
	switch( numeric.classKind() ) \
	{ \
		case FORM_BUILTIN_INTEGER_KIND:  \
			return( op(number, numeric.to_ref< Integer  >()) ); \
		case FORM_BUILTIN_RATIONAL_KIND: \
			return( op(number, numeric.to_ref< Rational >()) ); \
		case FORM_BUILTIN_FLOAT_KIND:    \
			return( op(number, numeric.to_ref< Float    >()) ); \
		default: \
		{ \
			AVM_OS_FATAL_ERROR_EXIT << "Unexpected a <Numeric> type info << " \
					<< numeric.classKindInfo() << " >> !!!" << SEND_EXIT; \
			return( false ); \
		} \
	}

#define BOOL_OPERATION(op, N1, N2) \
	switch( N1.classKind() ) \
	{ \
		case FORM_BUILTIN_INTEGER_KIND:  \
			BOOL_OPERATION_AUX(op, N1.to_ref< Integer  >(), N2) \
		case FORM_BUILTIN_RATIONAL_KIND: \
			BOOL_OPERATION_AUX(op, N1.to_ref< Rational >(), N2) \
		case FORM_BUILTIN_FLOAT_KIND:    \
			BOOL_OPERATION_AUX(op, N1.to_ref< Float    >(), N2) \
		default: \
		{ \
			AVM_OS_FATAL_ERROR_EXIT << "Unexpected a <Numeric> type info << " \
					<< N1.classKindInfo() << " >> !!!" << SEND_EXIT; \
			return( false ); \
		} \
	}


	/**
	 * compare
	 */
	int compare(const Numeric & aNumeric) const
	{
		if( mPTR == aNumeric.mPTR )
		{
			return( 0 );
		}

		BOOL_OPERATION( sep::numeric::compare , (*this) , aNumeric )
	}

	int compare(const Number & aNumber) const
	{
		if( mPTR == (& aNumber) )
		{
			return( 0 );
		}

		BOOL_OPERATION( sep::numeric::compare , (*this) , aNumber )
	}

	int compare(const BF & anExpression) const
	{
		if( mPTR == anExpression.raw_pointer() )
		{
			return( 0 );
		}

		BOOL_OPERATION( sep::numeric::compare ,
				(*this) , anExpression.as_ref< Number >() )
	}


	/**
	 * operator==
	 */
	inline bool operator==(const Numeric & aNumeric) const
	{
		if( mPTR == aNumeric.mPTR )
		{
			return( true );
		}

		BOOL_OPERATION( sep::numeric::operator== , (*this) , aNumeric )
	}

	inline bool operator==(const Number & aNumber) const
	{
		if( mPTR == (& aNumber) )
		{
			return( true );
		}

		BOOL_OPERATION( sep::numeric::operator== , (*this) , aNumber )
	}

	inline bool operator==(const BF & anExpression) const
	{
		if( mPTR == anExpression.raw_pointer() )
		{
			return( true );
		}

		BOOL_OPERATION( sep::numeric::operator== ,
				(*this) , anExpression.as_ref< Number >() )
	}


	/**
	 * operator!=
	 */
	inline bool operator!=(const Numeric & aNumeric) const
	{
		if( mPTR == aNumeric.mPTR )
		{
			return( false );
		}

		BOOL_OPERATION( sep::numeric::operator!= , (*this) , aNumeric )
	}

	inline bool operator!=(const Number & aNumber) const
	{
		if( mPTR == (& aNumber) )
		{
			return( false );
		}

		BOOL_OPERATION( sep::numeric::operator!= , (*this) , aNumber )
	}

	inline bool operator!=(const BF & anExpression) const
	{
		if( mPTR == anExpression.raw_pointer() )
		{
			return( false );
		}

		BOOL_OPERATION( sep::numeric::operator!= ,
				(*this) , anExpression.as_ref< Number >() )
	}


	/**
	 * operator<
	 */
	inline bool operator<(const Numeric & aNumeric) const
	{
		if( mPTR == aNumeric.mPTR )
		{
			return( false );
		}

		BOOL_OPERATION( sep::numeric::operator< , (*this) , aNumeric )
	}

	inline bool operator<(const Number & aNumber) const
	{
		if( mPTR == (& aNumber) )
		{
			return( false );
		}

		BOOL_OPERATION( sep::numeric::operator< , (*this) , aNumber )
	}

	inline bool operator<(const BF & anExpression) const
	{
		if( mPTR == anExpression.raw_pointer() )
		{
			return( false );
		}

		BOOL_OPERATION( sep::numeric::operator< ,
				(*this) , anExpression.as_ref< Number >() )
	}

	/**
	 * operator<=
	 */
	inline bool operator<=(const Numeric & aNumeric) const
	{
		if( mPTR == aNumeric.mPTR )
		{
			return( true );
		}

		BOOL_OPERATION( sep::numeric::operator<= , (*this) , aNumeric )
	}

	inline bool operator<=(const Number & aNumber) const
	{
		if( mPTR == (& aNumber) )
		{
			return( true );
		}

		BOOL_OPERATION( sep::numeric::operator<= , (*this) , aNumber )
	}

	inline bool operator<=(const BF & anExpression) const
	{
		if( mPTR == anExpression.raw_pointer() )
		{
			return( true );
		}

		BOOL_OPERATION( sep::numeric::operator<= ,
				(*this) , anExpression.as_ref< Number >() )
	}


	/**
	 * operator>
	 */
	inline bool operator>(const Numeric & aNumeric) const
	{
		if( mPTR == aNumeric.mPTR )
		{
			return( false );
		}

		BOOL_OPERATION( sep::numeric::operator> , (*this) , aNumeric )
	}

	inline bool operator>(const Number & aNumber) const
	{
		if( mPTR == (& aNumber) )
		{
			return( false );
		}

		BOOL_OPERATION( sep::numeric::operator> , (*this) , aNumber )
	}

	inline bool operator>(const BF & anExpression) const
	{
		if( mPTR == anExpression.raw_pointer() )
		{
			return( false );
		}

		BOOL_OPERATION( sep::numeric::operator> ,
				(*this) , anExpression.as_ref< Number >() )
	}


	/**
	 * operator>=
	 */
	inline bool operator>=(const Numeric & aNumeric) const
	{
		if( mPTR == aNumeric.mPTR )
		{
			return( true );
		}

		BOOL_OPERATION( sep::numeric::operator>= , (*this) , aNumeric )
	}

	inline bool operator>=(const Number & aNumber) const
	{
		if( mPTR == (& aNumber) )
		{
			return( true );
		}

		BOOL_OPERATION( sep::numeric::operator>= , (*this) , aNumber )
	}

	inline bool operator>=(const BF & anExpression) const
	{
		if( mPTR == anExpression.raw_pointer() )
		{
			return( true );
		}

		BOOL_OPERATION( sep::numeric::operator>= ,
				(*this) , anExpression.as_ref< Number >() )
	}


////////////////////////////////////////////////////////////////////////////////
// Numeric operator...
////////////////////////////////////////////////////////////////////////////////

#define ARITHMETIC_OPERATION_AUX(op, number, numeric) \
	switch( numeric.classKind() )  \
	{ \
		case FORM_BUILTIN_INTEGER_KIND:  \
			return( Numeric( op(number, numeric.to_ref< Integer  >()) ) ); \
		case FORM_BUILTIN_RATIONAL_KIND: \
			return( Numeric( op(number, numeric.to_ref< Rational >()) ) ); \
		case FORM_BUILTIN_FLOAT_KIND:    \
			return( Numeric( op(number, numeric.to_ref< Float    >()) ) ); \
		default: \
		{ \
			AVM_OS_FATAL_ERROR_EXIT << "Unexpected a <Numeric> type info << " \
					<< numeric.classKindInfo() << " >> !!!" << SEND_EXIT; \
			return( Numeric(0) ); \
		} \
	}

#define ARITHMETIC_OPERATION(op, N1, N2) \
	switch( N1.classKind() )  \
	{ \
		case FORM_BUILTIN_INTEGER_KIND:  \
			ARITHMETIC_OPERATION_AUX(op, N1.to_ref< Integer  >(), N2) \
		case FORM_BUILTIN_RATIONAL_KIND: \
			ARITHMETIC_OPERATION_AUX(op, N1.to_ref< Rational >(), N2) \
		case FORM_BUILTIN_FLOAT_KIND:    \
			ARITHMETIC_OPERATION_AUX(op, N1.to_ref< Float    >(), N2) \
		default: \
		{ \
			AVM_OS_FATAL_ERROR_EXIT << "Unexpected a <Numeric> type info << " \
					<< N1.classKindInfo() << " >> !!!" << SEND_EXIT; \
			return( Numeric(0) ); \
		} \
	}

#define ARITHMETIC_UNARY_OPERATION(op, N) \
	switch( N.classKind() )  \
	{ \
		case FORM_BUILTIN_INTEGER_KIND:  \
			return( Numeric( op(N.to_ref< Integer  >()) ) ); \
		case FORM_BUILTIN_RATIONAL_KIND: \
			return( Numeric( op(N.to_ref< Rational >()) ) ); \
		case FORM_BUILTIN_FLOAT_KIND:    \
			return( Numeric( op(N.to_ref< Float    >()) ) ); \
		default: \
		{ \
			AVM_OS_FATAL_ERROR_EXIT << "Unexpected a <Numeric> type info << " \
					<< N.classKindInfo() << " >> !!!" << SEND_EXIT; \
			return( Numeric(0) ); \
		} \
	}

#define ARITHMETIC_OPERATION_NUM(op, numeric, number) \
	switch( numeric.classKind() )  \
	{ \
		case FORM_BUILTIN_INTEGER_KIND:  \
			return( Numeric( op(numeric.to_ref< Integer  >(), number) ) ); \
		case FORM_BUILTIN_RATIONAL_KIND: \
			return( Numeric( op(numeric.to_ref< Rational >(), number) ) ); \
		case FORM_BUILTIN_FLOAT_KIND:    \
			return( Numeric( op(numeric.to_ref< Float    >(), number) ) ); \
		default: \
		{ \
			AVM_OS_FATAL_ERROR_EXIT << "Unexpected a <Numeric> type info << " \
					<< numeric.classKindInfo() << " >> !!!" << SEND_EXIT; \
			return( Numeric(0) ); \
		} \
	}


	/**
	 * operator+
	 */
	inline Numeric operator+(const Numeric & aNumeric) const
	{
		if( aNumeric.isZero() )
		{
			return( *this );
		}

		ARITHMETIC_OPERATION( sep::numeric::operator+ , (*this) , aNumeric )
	}

	inline Numeric operator+(const Number & aNumber) const
	{
		if( aNumber.isZero() )
		{
			return( *this );
		}

		ARITHMETIC_OPERATION( sep::numeric::operator+ , (*this) , aNumber )
	}

	inline Numeric operator+(const BF & anExpression) const
	{
		return( this->operator+( anExpression.as_ref< Number >() ) );
	}

	// operator+=
	inline Numeric & operator+=(const Numeric & aNumeric)
	{
		this->operator=( this->operator+( aNumeric ) );

		return( *this );
	}

	inline Numeric & operator+=(const BF & anExpression)
	{
		this->operator=( this->operator+( anExpression ) );

		return( *this );
	}


	/**
	 * operator++
	 */
	inline Numeric operator++()
	{
		this->operator=( this->operator+( Integer(1) ) );

		return( *this );
	}

	inline Numeric operator++(int)
	{
		Numeric tmp( *this );

		this->operator=( this->operator+( Integer(1) ) );

		return( tmp );
	}

	/**
	 * operator-
	 */
	inline Numeric operator-() const
	{
		ARITHMETIC_UNARY_OPERATION( sep::numeric::operator- , (*this) )
	}

	/**
	 * operator--
	 */
	inline Numeric operator--()
	{
		this->operator=( this->operator-( Integer(1) ) );

		return( *this );
	}

	inline Numeric operator--(int)
	{
		Numeric tmp( *this );

		this->operator=( this->operator-( Integer(1) ) );

		return( tmp );
	}

	/**
	 * operator-
	 */
	inline Numeric operator-(const Numeric & aNumeric) const
	{
		if( aNumeric.isZero() )
		{
			return( *this );
		}

		ARITHMETIC_OPERATION( sep::numeric::operator- , (*this) , aNumeric )
	}

	inline Numeric operator-(const Number & aNumber) const
	{
		if( aNumber.isZero() )
		{
			return( *this );
		}

		ARITHMETIC_OPERATION( sep::numeric::operator- , (*this) , aNumber )
	}

	inline Numeric operator-(const BF & anExpression) const
	{
		return( this->operator-( anExpression.as_ref< Number >() ) );
	}

	// operator-=
	inline Numeric & operator-=(const Numeric & aNumeric)
	{
		this->operator=( this->operator-( aNumeric ) );

		return( *this );
	}

	inline Numeric & operator-=(const BF & anExpression)
	{
		this->operator=( this->operator-( anExpression ) );

		return( *this );
	}


	/**
	 * operator*
	 */
	inline Numeric operator*(const Numeric & aNumeric) const
	{
		if( aNumeric.isOne() )
		{
			return( *this );
		}

		ARITHMETIC_OPERATION( sep::numeric::operator* , (*this) , aNumeric )
	}

	inline Numeric operator*(const Number & aNumber) const
	{
		if( aNumber.isOne() )
		{
			return( *this );
		}

		ARITHMETIC_OPERATION( sep::numeric::operator* , (*this) , aNumber )
	}

	inline Numeric operator*(const BF & anExpression) const
	{
		return( this->operator*( anExpression.as_ref< Number >() ) );
	}

	// operator*=
	inline Numeric & operator*=(const Numeric & aNumeric)
	{
		this->operator=( this->operator*( aNumeric ) );

		return( *this );
	}

	inline Numeric & operator*=(const BF & anExpression)
	{
		this->operator=( this->operator*( anExpression ) );

		return( *this );
	}


	/**
	 * operator/
	 */
	inline Numeric operator/(const Numeric & aNumeric) const
	{
		if( aNumeric.isOne() )
		{
			return( *this );
		}

		ARITHMETIC_OPERATION( sep::numeric::operator/ , (*this) , aNumeric )
	}

	inline Numeric operator/(const Number & aNumber) const
	{
		if( aNumber.isOne() )
		{
			return( *this );
		}

		ARITHMETIC_OPERATION( sep::numeric::operator/ , (*this) , aNumber )
	}

	inline Numeric operator/(const BF & anExpression) const
	{
		return( this->operator/( anExpression.as_ref< Number >() ) );
	}

	// operator/=
	inline Numeric & operator/=(const Numeric & aNumeric)
	{
		this->operator=( this->operator/( aNumeric ) );

		return( *this );
	}

	inline Numeric & operator/=(const BF & anExpression)
	{
		this->operator=( this->operator/( anExpression ) );

		return( *this );
	}


	/**
	 * COMPARISON OPERATION
	 */
	inline bool eq(const Numeric & arg)
	{
		return( this->operator==( arg ) );
	}

	inline bool neq(const Numeric & arg)
	{
		return( this->operator!=( arg ) );
	}


	inline bool lt(const Numeric & arg)
	{
		return( this->operator<( arg ) );
	}

	inline bool lte(const Numeric & arg)
	{
		return( this->operator<=( arg ) );
	}


	inline bool gt(const Numeric & arg)
	{
		return( this->operator>( arg ) );
	}

	inline bool gte(const Numeric & arg)
	{
		return( this->operator>=( arg ) );
	}


	/**
	 * ARITHMETIC OPERATION
	 */
	inline Numeric add(const Numeric & arg)
	{
		return( this->operator+( arg ) );
	}

	inline Numeric incr(avm_uinteger_t val = 1)
	{
		return( this->operator+( Integer(val) ) );
	}

	inline Numeric minus(const Numeric & arg)
	{
		return( this->operator-( arg ) );
	}

	inline Numeric uminus()
	{
		return( this->operator-() );
	}

	inline Numeric decr(avm_uinteger_t val = 1)
	{
		return( this->operator-( Integer(val) ) );
	}

	inline Numeric mult(const Numeric & arg)
	{
		return( this->operator*( arg ) );
	}

	inline Numeric pow(avm_uinteger_t anExponent)
	{
		ARITHMETIC_OPERATION_NUM( sep::numeric::pow , (*this) , anExponent )
	}

	inline Numeric div(const Numeric & arg)
	{
		return( this->operator/( arg ) );
	}

	inline Numeric inv()
	{
		ARITHMETIC_UNARY_OPERATION( sep::numeric::inverse , (*this) )
	}


	/**
	 * Serialization
	 */
	inline void toStream(OutStream & os) const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in Numeric::toStream(OutStream &) !!!"
				<< SEND_EXIT;

		mPTR->toStream( os );
	}

	inline void toStream(PairOutStream & os) const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in Numeric::toStream(PairOutStream &) !!!"
				<< SEND_EXIT;

		mPTR->toStream( os.OS1 );
		mPTR->toStream( os.OS2 );
	}

	inline void toStream(TripleOutStream & os) const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in Numeric::toStream(TripleOutStream &) !!!"
				<< SEND_EXIT;

		mPTR->toStream( os.OS1 );
		mPTR->toStream( os.OS2 );
		mPTR->toStream( os.OS3 );
	}


	inline std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream oss(indent);

		toStream( oss );

		return( oss.str() );
	}

	inline std::string str() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in Numeric::str() !!!"
				<< SEND_EXIT;

		return( mPTR->str() );
	}


};


/**
 * operator<<
 */
AVM_OS_STREAM( Numeric )


inline OutStream & operator<<(OutStream & os, const Integer & aNumber)
{
	aNumber.toStream( os );

	return( os );
}

/**
 * Serialization
 */
inline OutStream & operator<<(OutStream & os, const Rational & aNumber)
{
	aNumber.toStream( os );

	return( os );
}

/**
 * Serialization
 */
inline OutStream & operator<<(OutStream & os, const Float & aNumber)
{
	aNumber.toStream( os );

	return( os );
}



} /* namespace sep */
#endif /* FML_EXPRESSION_NUMERIC_H_ */

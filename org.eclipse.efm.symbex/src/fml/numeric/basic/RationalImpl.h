/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 mai 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef FML_NUMERIC_BASIC_RATIONALIMPL_H_
#define FML_NUMERIC_BASIC_RATIONALIMPL_H_

#include <fml/numeric/Number.h>

#include <fml/numeric/Integer.h>

#include <cmath>


namespace sep
{


template< typename Num_T , typename Den_T >
class BasicRational
{

public:
	/**
	 * TYPEDEF
	 */
	typedef  Num_T  TNum;
	typedef  Den_T  TDen;


protected:
	/**
	 * ATTRIBUTES
	 */
	Num_T mNumerator;
	Den_T mDenominator;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BasicRational(Num_T aNumerator, Den_T aDenominator)
	: mNumerator( aNumerator ),
	mDenominator( aDenominator )
	{
		simplif();
	}


	BasicRational(const std::string & aNumerator, Den_T aDenominator)
	: mNumerator( sep::string_to< Num_T >(aNumerator, std::dec) ),
	mDenominator( aDenominator )
	{
		simplif();
	}

	BasicRational(Num_T aNumerator, const std::string & aDenominator)
	: mNumerator( aNumerator ),
	mDenominator( sep::string_to< Num_T >(aDenominator, std::dec) )
	{
		simplif();
	}

	BasicRational(const std::string & aNumerator,
			const std::string & aDenominator)
	: mNumerator( sep::string_to< Num_T >(aNumerator  , std::dec) ),
	mDenominator( sep::string_to< Den_T >(aDenominator, std::dec) )
	{
		simplif();
	}

	BasicRational(const std::string & aRational)
	: mNumerator( 0 ),
	mDenominator( 1 )
	{
		fromString(this, aRational);

		simplif();
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BasicRational(const BasicRational & aRational)
	: mNumerator  ( aRational.mNumerator ),
	mDenominator( aRational.mDenominator )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BasicRational()
	{
		//!! NOTHING
	}


	inline static void fromString(BasicRational * rop, const std::string & aValue)
	{
		std::string::size_type pos = aValue.find('/');
		if( pos != std::string::npos)
		{
			rop->mNumerator = sep::string_to< Num_T >(
					aValue.substr(0, pos), std::dec);
			rop->mDenominator = sep::string_to< Num_T >(
					aValue.substr(pos+1), std::dec);
		}
		else if( (pos = aValue.find('.')) != std::string::npos )
		{
			rop->mNumerator = sep::string_to< Num_T >(
					std::string(aValue).erase(pos, 1), std::dec);

			rop->mDenominator = Integer::ipow(10, aValue.size() - (pos + 1));
		}
		else
		{
			rop->mNumerator = sep::string_to< Num_T >(aValue, std::dec);
			rop->mDenominator = 1;
		}
	}

	/**
	 * GETTER - SETTER
	 * ThisNumberClass::mValue
	 */
	inline Den_T gcd(Den_T a, Den_T b)
	{
		Den_T tmp;
		while( b != 0 )
		{
			tmp = b;
			b = a % b;
			a = tmp;
		}

		return( a );
	}

	inline bool simplif()
	{
		if( mDenominator != 1 )
		{
			Den_T d = gcd((mNumerator < 0) ? (-mNumerator) : mNumerator,
					mDenominator);

			if( (d != 0) && (d != 1) )
			{
				mNumerator   = static_cast< Num_T >( mNumerator   / d );
				mDenominator = static_cast< Den_T >( mDenominator / d );
			}
		}

		return( true );
	}


	/**
	 * GETTER - SETTER
	 * ThisNumberClass::mValue
	 */
	inline Num_T rawNumerator() const
	{
		return( mNumerator );
	}

	inline Den_T rawDenominator() const
	{
		return( mDenominator );
	}


	inline void setValue(Num_T aNumerator, Den_T aDenominator)
	{
		mNumerator   = aNumerator;
		mDenominator = aDenominator;

		simplif();
	}

	inline void setValue(Num_T aValue)
	{
		mNumerator   = aValue;
		mDenominator = 1;
	}


	/**
	 * CONVERSION
	 */
	inline virtual avm_float_t toFloat() const
	{
		return( static_cast< avm_float_t >( mNumerator / mDenominator ) );
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	// operator==
	inline bool operator==(const BasicRational & other) const
	{
		return( ( mDenominator == other.mDenominator ) ?
				(mNumerator == other.mNumerator) :
				(mNumerator * other.mDenominator ==
						mDenominator * other.mNumerator) );
	}

	inline bool operator==(avm_integer_t aValue) const
	{
		return( mNumerator == mDenominator * aValue );
	}

	// operator!=
	inline bool operator!=(const BasicRational & other) const
	{
		return( ! operator==(other) );
	}

	inline bool operator!=(avm_integer_t aValue) const
	{
		return( mNumerator != mDenominator * aValue );
	}

	// operator<
	inline bool operator<(const BasicRational & other) const
	{
		return( ( mDenominator == other.mDenominator ) ?
				(mNumerator < other.mNumerator) :
				(mNumerator * other.mDenominator <
						mDenominator * other.mNumerator) );
	}

	inline bool operator<(avm_integer_t aValue) const
	{
		return( mNumerator < mDenominator * aValue );
	}

	// operator<=
	inline bool operator<=(const BasicRational & other) const
	{
		return( ( mDenominator == other.mDenominator ) ?
				(mNumerator <= other.mNumerator) :
				(mNumerator * other.mDenominator <=
						mDenominator * other.mNumerator) );
	}

	inline bool operator<=(avm_integer_t aValue) const
	{
		return( mNumerator <= mDenominator * aValue );
	}

	// operator>
	inline bool operator>(const BasicRational & other) const
	{
		return( ( mDenominator == other.mDenominator ) ?
				(mNumerator > other.mNumerator) :
				(mNumerator * other.mDenominator >
						mDenominator * other.mNumerator) );
	}

	inline bool operator>(avm_integer_t aValue) const
	{
		return( mNumerator > mDenominator * aValue );
	}

	// operator>=
	inline bool operator>=(const BasicRational & other) const
	{
		return( ( mDenominator == other.mDenominator ) ?
				(mNumerator >= other.mNumerator) :
				(mNumerator * other.mDenominator >=
						mDenominator * other.mNumerator) );
	}

	inline bool operator>=(avm_integer_t aValue) const
	{
		return( mNumerator > mDenominator * aValue );
	}


	/**
	 * ARITHMETIC
	 * OPERATOR
	 */
	// operator+
	inline BasicRational operator+(const BasicRational & other)
	{
		return( BasicRational((mNumerator * other.mDenominator) +
					(mDenominator * other.mNumerator) ,
				mDenominator * other.mDenominator) );
	}

	inline BasicRational operator+(avm_integer_t aValue)
	{
		return( BasicRational(mNumerator + mDenominator * aValue ,
				mDenominator) );
	}

	// operator-
	inline BasicRational & operator-()
	{
		return( BasicRational(- mNumerator , mDenominator) );
	}


	inline BasicRational operator-(avm_integer_t aValue)
	{
		return( BasicRational(mNumerator - mDenominator * aValue ,
				mDenominator) );
	}

	inline BasicRational operator-(const BasicRational & other)
	{
		return( BasicRational((mNumerator * other.mDenominator) -
					(mDenominator * other.mNumerator) ,
				mDenominator * other.mDenominator) );
	}

	// operator*
	inline BasicRational operator*(const BasicRational & other)
	{
		return( BasicRational(mNumerator * other.mNumerator ,
				mDenominator * other.mDenominator) );
	}

	inline BasicRational & operator*(avm_integer_t aValue)
	{
		return( BasicRational(mNumerator * aValue , mDenominator) );
	}

	// operator/
	inline BasicRational operator/(const BasicRational & other)
	{
		return( BasicRational(mNumerator * other.mDenominator ,
				mDenominator * other.mNumerator) );
	}

	inline BasicRational operator/(avm_integer_t aValue)
	{
		return( BasicRational(mNumerator , mDenominator * aValue) );
	}


	/**
	 * math function
	 */
	inline void set_pow(avm_uinteger_t anExponent)
	{
		mNumerator   = Integer::ipow(mNumerator, anExponent);
		mDenominator = Integer::ipow(mDenominator, anExponent);
	}

};



class Rational :
		public Number,
		public GenericNumberClass<
				BasicRational< avm_integer_t , avm_integer_t > , Rational >
{

	AVM_DECLARE_CLONABLE_CLASS( Rational )


	/**
	 * TYPEDEF
	 */
public:
	typedef  BasicRational< avm_integer_t , avm_integer_t >  RawValueType;

private:
	typedef GenericNumberClass< RawValueType , Rational >  ThisNumberClass;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Rational(const RawValueType & aValue)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// Integer / Integer
	Rational(const Integer & aNumerator, const Integer & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator.getValue(), aDenominator.getValue()) )
	{
		//!! NOTHING
	}

	Rational(avm_integer_t aNumerator, avm_integer_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	Rational(avm_integer_t aNumerator, avm_uinteger_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	Rational(avm_uinteger_t aNumerator, avm_integer_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	Rational(avm_uinteger_t aNumerator, avm_uinteger_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	Rational(const Integer & aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator.getValue(), 1) )
	{
		//!! NOTHING
	}

	// avm_integer_t  i.e.  avm_int64_t
	Rational(avm_integer_t aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, 1) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  avm_uint64_t
	Rational(avm_uinteger_t aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, 1) )
	{
		//!! NOTHING
	}

#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// long
	Rational(long aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, 1) )
	{
		//!! NOTHING
	}

	// unsigned long
	Rational(unsigned long aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, 1) )
	{
		//!! NOTHING
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */

	// int32_t
	Rational(int aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, 1) )
	{
		//!! NOTHING
	}

	// uint32_t
	Rational(unsigned int aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, 1) )
	{
		//!! NOTHING
	}

	// std::string / avm_integer_t
	Rational(const std::string & aNumerator, avm_integer_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	// avm_integer_t / std::string
	Rational(avm_integer_t aNumerator, const std::string & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	// std::string / std::string
	Rational(const std::string & aNumerator, const std::string & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, aDenominator) )
	{
		//!! NOTHING
	}

	// std::string
	Rational(const std::string & aRational)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aRational) )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Rational(const Rational & aRational)
	: Number( aRational ),
	ThisNumberClass( aRational )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Rational()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * ThisNumberClass::mValue
	 */
	inline Integer getNumerator() const
	{
		return( Integer( ThisNumberClass::mValue.rawNumerator() ) );
	}

	inline Integer getDenominator() const
	{
		return( Integer( ThisNumberClass::mValue.rawDenominator() ) );
	}


	inline Integer::RawValueType rawNumerator() const
	{
		return( ThisNumberClass::mValue.rawNumerator() );
	}

	inline Integer::RawValueType rawDenominator() const
	{
		return( ThisNumberClass::mValue.rawDenominator() );
	}


	inline void setValue(avm_integer_t aNumerator, avm_integer_t aDenominator)
	{
		ThisNumberClass::mValue = RawValueType(aNumerator, aDenominator);
	}

	inline void setValue(avm_integer_t aValue)
	{
		ThisNumberClass::mValue = RawValueType(aValue, 1);
	}


	/**
	 * BASICS TESTS
	 */
	virtual inline int sign() const
	{
		return( (ThisNumberClass::mValue.rawNumerator() < 0) ? -1 :
				(ThisNumberClass::mValue.rawNumerator() > 0) );
	}

	virtual inline bool strictlyPositive() const
	{
		return( ThisNumberClass::mValue.rawNumerator() > 0 );
	}

	virtual inline bool strictlyNegative() const
	{
		return( ThisNumberClass::mValue.rawNumerator() < 0 );
	}

	virtual inline bool isZero() const
	{
		return( ThisNumberClass::mValue.rawNumerator() == 0 );
	}

	virtual inline bool isOne() const
	{
		return( ThisNumberClass::mValue.rawNumerator() ==
				ThisNumberClass::mValue.rawDenominator() );
	}

	virtual inline bool isNegativeOne() const
	{
		return( (ThisNumberClass::mValue.rawNumerator() ==
				ThisNumberClass::mValue.rawDenominator()) &&
				strictlyNegative() );
	}


	/**
	 * CONVERSION
	 */
	inline virtual bool isInt32() const
	{
		return( (ThisNumberClass::mValue.rawDenominator() == 1) &&
				(static_cast< avm_integer_t >(AVM_NUMERIC_MIN_INT) <=
						ThisNumberClass::mValue.rawNumerator()) &&
				(ThisNumberClass::mValue.rawNumerator() <=
						static_cast< avm_integer_t >(AVM_NUMERIC_MAX_INT)) );
	}

	inline virtual avm_int32_t toInt32() const
	{
		return( static_cast< avm_int32_t >(
				ThisNumberClass::mValue.rawNumerator() ) );
	}

	inline virtual bool isInt64() const
	{
		return( (ThisNumberClass::mValue.rawDenominator() == 1) &&
				(static_cast< avm_integer_t >(AVM_NUMERIC_MIN_LONG) <=
						ThisNumberClass::mValue.rawNumerator()) &&
				(ThisNumberClass::mValue.rawNumerator() <=
						static_cast< avm_integer_t >(AVM_NUMERIC_MAX_LONG)) );
	}

	inline virtual avm_int64_t toInt64() const
	{
		return( static_cast< avm_int64_t >(
				ThisNumberClass::mValue.rawNumerator() ) );
	}


	inline virtual bool isInteger() const
	{
		return( ThisNumberClass::mValue.rawDenominator() == 1 );
	}

	inline virtual avm_integer_t toInteger() const
	{
		if( isInteger() )
		{
			return( ThisNumberClass::mValue.rawNumerator() );
		}
		else
		{
			return( static_cast< avm_integer_t >( toFloat() ) );
		}
	}


	inline virtual bool isPosInteger() const
	{
		return( (ThisNumberClass::mValue.rawDenominator() == 1) &&
				(ThisNumberClass::mValue.rawNumerator() >= 0) );
	}


	inline virtual bool isUInteger() const
	{
		return( (ThisNumberClass::mValue.rawDenominator() == 1) &&
				(ThisNumberClass::mValue.rawNumerator() >= 0) );
	}

	inline virtual avm_uinteger_t toUInteger() const
	{
		if( isUInteger() )
		{
			return( static_cast< avm_uinteger_t >(
					ThisNumberClass::mValue.rawNumerator() ) );
		}
		else if( toFloat() >= 0 )
		{
			return( static_cast< avm_uinteger_t >( toFloat() ) );
		}

		return( static_cast< avm_uinteger_t >( -1 ) );
	}


	inline virtual bool isRational() const
	{
		return( true );
	}

	virtual avm_integer_t toDenominator() const
	{
		return( ThisNumberClass::mValue.rawDenominator() );
	}

	virtual avm_integer_t toNumerator() const
	{
		return( ThisNumberClass::mValue.rawNumerator() );
	}


	inline virtual bool isFloat() const
	{
		return( true );
	}

	inline virtual avm_float_t toFloat() const
	{
		return( static_cast< avm_float_t >(
				ThisNumberClass::mValue.rawNumerator() /
				ThisNumberClass::mValue.rawDenominator()) );
	}


	inline virtual bool isReal() const
	{
		return( true );
	}

	inline virtual avm_real_t toReal() const
	{
		return( static_cast< avm_real_t >(
				ThisNumberClass::mValue.rawNumerator() /
				ThisNumberClass::mValue.rawDenominator()) );
	}


	/**
	 * math function
	 */
	inline void set_pow(avm_uinteger_t anExponent)
	{
		ThisNumberClass::mValue.set_pow( anExponent );
	}


	/**
	 * Serialization
	 */
	inline void toStream(OutStream & os) const
	{
		os << TAB << rawNumerator();
		if( rawDenominator() != 1 )
		{
			os << "/" << rawDenominator();
		}
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}

	virtual std::string str() const
	{
		if( rawDenominator() != 1 )
		{
			return( OSS() << rawNumerator() << '/' << rawDenominator() );
		}
		else
		{
			return( OSS() << rawNumerator() );
		}
	}

	inline virtual std::string strNum(
			avm_uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		if( rawDenominator() != 1 )
		{
			return( OSS() << rawNumerator() << '/' << rawDenominator() );
		}
		else
		{
			return( OSS() << rawNumerator() );
		}
	}

	inline virtual std::string strNumerator(
			avm_uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( OSS() << rawNumerator() );
	}

	inline virtual std::string strDenominator(
			avm_uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( OSS() << rawDenominator() );
	}

};


} /* namespace sep */

#endif /* FML_NUMERIC_BASIC_RATIONALIMPL_H_ */

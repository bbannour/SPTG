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

#ifndef FML_NUMERIC_GMP_FLOATIMPL_H_
#define FML_NUMERIC_GMP_FLOATIMPL_H_

#include <gmpxx.h>

#include <fml/numeric/Number.h>

#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>


namespace sep
{


class Float final :
		public Number,
		public GenericNumberClass< mpf_class , Float >
{

	AVM_DECLARE_CLONABLE_CLASS( Float )


	/**
	 * TYPEDEF
	 */
public:
	typedef  mpf_class  RawValueType;

private:
	typedef  GenericNumberClass< RawValueType , Float >  ThisNumberClass;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	// RawValueType
	Float(const RawValueType & aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

	// mpq_class
	Float(const mpq_class & aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

	// mpq_t
	Float(const mpq_t & aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( mpq_class(aValue) ) )
	{
		//!! NOTHING
	}


	// mpz_class
	Float(const mpz_class & aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// mpz_t
	Float(const mpz_t & aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( mpz_class(aValue) ) )
	{
		//!! NOTHING
	}

	// Rational
	Float(const Rational & aRational)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( aRational.getValue() ) )
	//ThisNumberClass( RawValueType( static_cast<sep::BasicRational>(aRational).getValue() ) )
	//ThisNumberClass( RawValueType( reinterpret_cast<__gmp_expr>(aRational).getValue() ) )
	//ThisNumberClass( RawValueType( reinterpret_cast<GenericNumberClass>(aRational).getValue() ) )
	//ThisNumberClass( RawValueType( reinterpret_cast<GenericNumberClass<mpq_class , Rational>>(aRational).getValue() ) )
	{
		//!! NOTHING
	}

	// Integer
	Float(const Integer & anInteger)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( anInteger.getValue() ) )
	//ThisNumberClass( RawValueType( reinterpret_cast<GenericNumberClass>(anInteger).getValue() ) )
	//ThisNumberClass( RawValueType( reinterpret_cast<GenericNumberClass<mpz_class , Integer>>(anInteger).getValue() ) )
	{
		//!! NOTHING
	}

	// avm_float_t
	Float(avm_float_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// avm_integer_t  i.e.  std::int64_t
	Float(avm_integer_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( static_cast< long >(aValue) ) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  std::uint64_t
	Float(avm_uinteger_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( static_cast< unsigned long >(aValue) ) )
	{
		//!! NOTHING
	}

	// long
	Float(long aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

	Float(unsigned long aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

#else

	// avm_integer_t  i.e.  std::int64_t
	Float(avm_integer_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  std::uint64_t
	Float(avm_uinteger_t aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */

	// int32_t
	Float(int aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// uint32_t
	Float(unsigned int aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// std::string
	Float(const std::string & aValue)
	: Number( CLASS_KIND_T( Float ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Float(const Float & aFloat)
	: Number( aFloat ),
	ThisNumberClass( aFloat )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Float()
	{
		//!! NOTHING
	}


	/**
	 * BASICS TESTS
	 */
	inline virtual int sign() const override
	{
		return( mpf_sgn(ThisNumberClass::mValue.get_mpf_t()) );
	}

	inline virtual bool isZero() const override
	{
		return( sign() == 0 );
	}

	inline virtual bool isOne() const override
	{
		return( mpf_cmp_si(ThisNumberClass::mValue.get_mpf_t(), 1) == 0 );
	}

	inline virtual bool isNegativeOne() const override
	{
		return( mpf_cmp_si(ThisNumberClass::mValue.get_mpf_t(), -1) == 0 );
	}


	/**
	 * CONVERSION
	 */
#define MPF_IS_INTEGER(MPF_VAL, INF, SUP)                        \
	(mpf_cmp_si(MPF_VAL.get_mpf_t(), MPF_VAL.get_si()) == 0) &&  \
	(mpf_cmp_si(MPF_VAL.get_mpf_t(), INF) >= 0) &&               \
	(mpf_cmp_ui(MPF_VAL.get_mpf_t(), SUP) <= 0)

#define MPF_IS_POSITIVE_INTEGER(MPF_VAL, SUP)  (sign() >= 0) &&  \
	(mpf_cmp_ui(MPF_VAL.get_mpf_t(), MPF_VAL.get_ui()) == 0) &&  \
	(mpf_cmp_ui(MPF_VAL.get_mpf_t(), SUP) <= 0)


	inline virtual bool isInt32() const override
	{
//		return( MPF_IS_INTEGER(ThisNumberClass::mValue,
//				INT32_MIN, INT32_MAX) );

		return( ThisNumberClass::mValue.fits_sint_p() ) ;
	}

	inline virtual std::int32_t toInt32() const override
	{
		return( static_cast< std::int32_t >(
				ThisNumberClass::mValue.get_si() ) );
	}


	inline virtual bool isInt64() const override
	{
//		return( MPF_IS_INTEGER(ThisNumberClass::mValue,
//				INT64_MIN, INT64_MAX) );

		return( ThisNumberClass::mValue.fits_slong_p() ) ;
	}

	inline virtual std::int64_t toInt64() const override
	{
		return( static_cast< std::int64_t >(
				ThisNumberClass::mValue.get_si() ) );
	}


	inline virtual bool isInteger() const override
	{
//		return( MPF_IS_INTEGER(ThisNumberClass::mValue,
//				AVM_NUMERIC_MIN_INTEGER, AVM_NUMERIC_MAX_INTEGER) );

		return( ThisNumberClass::mValue.fits_slong_p() ) ;
	}

	inline virtual avm_integer_t toInteger() const override
	{
		return( static_cast< avm_integer_t >(
				ThisNumberClass::mValue.get_si() ) );
	}


	inline virtual bool isPosInteger() const
	{
//		return( MPF_IS_POSITIVE_INTEGER(
//				ThisNumberClass::mValue, AVM_NUMERIC_MAX_UINTEGER) );

		return( ThisNumberClass::mValue.fits_ulong_p() ) ;
	}


	inline virtual bool isUInteger() const override
	{
//		return( MPF_IS_POSITIVE_INTEGER(
//				ThisNumberClass::mValue, AVM_NUMERIC_MAX_UINTEGER) );

		return( ThisNumberClass::mValue.fits_ulong_p() ) ;
	}

	inline virtual avm_uinteger_t toUInteger() const override
	{
		return( static_cast< avm_uinteger_t >(
				ThisNumberClass::mValue.get_ui() ) );
	}


	inline virtual bool isRational() const override
	{
		return( true );
	}

	virtual avm_integer_t toDenominator() const override
	{
		return( static_cast< avm_integer_t >(
				mpq_class(ThisNumberClass::mValue).get_den().get_si() ) );
	}

	virtual avm_integer_t toNumerator() const override
	{
		return( static_cast< avm_integer_t >(
				mpq_class(ThisNumberClass::mValue).get_num().get_si() ) );
	}


	inline virtual bool isFloat() const override
	{
		return( true );
	}

	inline virtual avm_float_t toFloat() const override
	{
		return( static_cast< avm_float_t >(
				ThisNumberClass::mValue.get_d() ) );
	}


	inline virtual bool isReal() const override
	{
		return( true );
	}

	inline virtual avm_real_t toReal() const override
	{
		return( static_cast< avm_real_t >(
				ThisNumberClass::mValue.get_d() ) );
	}


	/**
	 * math function
	 */
	inline void set_pow(avm_uinteger_t anExponent)
	{
		RawValueType mpResult;

		mpf_pow_ui( mpResult.get_mpf_t(),
				ThisNumberClass::mValue.get_mpf_t(), anExponent );

		ThisNumberClass::mValue = mpResult;
	}

	inline void set_pow(double aValue, avm_uinteger_t anExponent)
	{
		mpf_pow_ui( ThisNumberClass::mValue.get_mpf_t(),
				RawValueType(aValue).get_mpf_t(), anExponent );
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const override
	{
		os << TAB << OS_FLOAT_PRECISION << mValue;
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}

	virtual std::string str() const override
	{
		return( OSS() /*<< OS_REAL_PRECISION*/ << mValue );
	}

	inline virtual std::string strNum(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const override
	{
		return( OSS() << std::fixed
				<< std::setprecision( precision ) << mValue );
	}

};


} /* namespace sep */

#endif /* FML_NUMERIC_GMP_FLOATIMPL_H_ */

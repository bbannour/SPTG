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

#ifndef FML_NUMERIC_GMP_INTEGERIMPL_H_
#define FML_NUMERIC_GMP_INTEGERIMPL_H_

#include <gmpxx.h>

#include <fml/numeric/Number.h>


namespace sep
{


class Integer final :
		public Number,
		public GenericNumberClass< mpz_class , Integer >
{

	AVM_DECLARE_CLONABLE_CLASS( Integer )


	/**
	 * TYPEDEF
	 */
public:
	typedef  mpz_class  RawValueType;

private:
	typedef  GenericNumberClass< RawValueType , Integer >  ThisNumberClass;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	// RawValueType  i.e.  mpz_class
	Integer(const RawValueType & aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( aValue )
	{
		//!! NOTHING
	}

	// mpz_t
	Integer(const mpz_t & aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}


#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// avm_integer_t  i.e.  std::int64_t
	Integer(avm_integer_t aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType( static_cast< long >( aValue ) ) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  std::uint64_t
	Integer(avm_uinteger_t aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType( static_cast< unsigned long >( aValue ) ) )
	{
		//!! NOTHING
	}


	Integer(avm_uinteger_t aValue, avm_uinteger_t anExponent)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType( static_cast< unsigned long >( aValue ) ) )
	{
		set_pow( anExponent );
	}

	// long
	Integer(long aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

	Integer(unsigned long aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType( aValue ) )
	{
		//!! NOTHING
	}

#else

	// avm_integer_t  i.e.  std::int64_t
	Integer(avm_integer_t aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// avm_uinteger_t  i.e.  std::uint64_t
	Integer(avm_uinteger_t aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	Integer(avm_uinteger_t aValue, avm_uinteger_t anExponent)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		set_pow( anExponent );
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */

	// int32_t
	Integer(int aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// uint32_t
	Integer(unsigned int aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	// std::string
	Integer(const std::string & aValue)
	: Number( CLASS_KIND_T( Integer ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Integer(const Integer & anInteger)
	: Number( anInteger ),
	ThisNumberClass( anInteger )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Integer()
	{
		//!! NOTHING
	}


	/**
	 * BASICS TESTS
	 */
	inline virtual int sign() const override
	{
		return( mpz_sgn(ThisNumberClass::mValue.get_mpz_t()) );
	}

	inline virtual bool isZero() const override
	{
		return( sign() == 0 );
	}

	inline virtual bool isOne() const override
	{
		return( mpz_cmp_si(ThisNumberClass::mValue.get_mpz_t(), 1) == 0 );
	}

	inline virtual bool isNegativeOne() const override
	{
		return( mpz_cmp_si(ThisNumberClass::mValue.get_mpz_t(), -1) == 0 );
	}


	/**
	 * CONVERSION
	 */
#define MPZ_IS_INTEGER(MPZ_VAL, INF, SUP)                        \
	(mpz_cmp_si(MPZ_VAL.get_mpz_t(), MPZ_VAL.get_si()) == 0) &&  \
	(mpz_cmp_si(MPZ_VAL.get_mpz_t(), INF) >= 0) &&               \
	(mpz_cmp_ui(MPZ_VAL.get_mpz_t(), SUP) <= 0)

#define MPZ_IS_POSITIVE_INTEGER(MPZ_VAL, SUP)  \
	(mpz_sgn( MPZ_VAL.get_mpz_t() ) >= 0) &&   \
	(mpz_cmp_ui(MPZ_VAL.get_mpz_t(), MPZ_VAL.get_ui()) == 0) &&  \
	(mpz_cmp_ui(MPZ_VAL.get_mpz_t(), SUP) <= 0)


	inline virtual bool isInt32() const override
	{
//		return( MPZ_IS_INTEGER(ThisNumberClass::mValue,
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
//		return( MPZ_IS_INTEGER(ThisNumberClass::mValue,
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
//		return( MPZ_IS_INTEGER(ThisNumberClass::mValue,
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
//		return( MPZ_IS_POSITIVE_INTEGER(
//				ThisNumberClass::mValue, AVM_NUMERIC_MAX_UINTEGER ) );

		return( ThisNumberClass::mValue.fits_ulong_p() ) ;
	}


	inline virtual bool isUInteger() const override
	{
//		return( MPZ_IS_POSITIVE_INTEGER(
//				ThisNumberClass::mValue, AVM_NUMERIC_MAX_UINTEGER ) );

		return( ThisNumberClass::mValue.fits_ulong_p() ) ;
	}

	inline virtual avm_uinteger_t toUInteger() const override
	{
		return( static_cast< avm_uinteger_t >(
				ThisNumberClass::mValue.get_ui() ) );
	}


	inline virtual bool isRational() const override
	{
		return( isInteger() );
	}

	virtual avm_integer_t toNumerator() const override
	{
		return( static_cast< avm_integer_t >(
				ThisNumberClass::mValue.get_si() ) );
	}

	virtual avm_integer_t toDenominator() const override
	{
		return( static_cast< avm_integer_t >( 1 ) );
	}


#define MPZ_IS_FLOAT(MPZ_VAL, INF, SUP)                        \
	(mpz_cmp_d(MPZ_VAL.get_mpz_t(), MPZ_VAL.get_d()) == 0) &&  \
	(mpz_cmp_d(MPZ_VAL.get_mpz_t(), INF) >= 0) &&              \
	(mpz_cmp_d(MPZ_VAL.get_mpz_t(), SUP) <= 0)


	inline virtual bool isFloat() const override
	{
		return( MPZ_IS_FLOAT(ThisNumberClass::mValue,
				AVM_NUMERIC_MIN_FLOAT_T, AVM_NUMERIC_MAX_FLOAT_T) );
	}

	inline virtual avm_float_t toFloat() const override
	{
		return( static_cast< avm_float_t >(
				ThisNumberClass::mValue.get_d() ) );
	}


	inline virtual bool isReal() const override
	{
		return( MPZ_IS_FLOAT(ThisNumberClass::mValue,
				AVM_NUMERIC_MIN_REAL_T, AVM_NUMERIC_MAX_REAL_T) );
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

		mpz_pow_ui( mpResult.get_mpz_t(),
				ThisNumberClass::mValue.get_mpz_t(), anExponent );

		ThisNumberClass::mValue = mpResult;
	}

	inline void set_pow(avm_uinteger_t aValue, avm_uinteger_t anExponent)
	{
		mpz_ui_pow_ui( ThisNumberClass::mValue.get_mpz_t(), aValue, anExponent );
	}


	inline Integer pow(avm_uinteger_t anExponent) const
	{
		RawValueType mpResult;

		mpz_pow_ui( mpResult.get_mpz_t(),
				ThisNumberClass::mValue.get_mpz_t(), anExponent );

		return( Integer(mpResult) );
	}

	inline static Integer pow(avm_uinteger_t aValue, avm_uinteger_t anExponent)
	{
		RawValueType mpResult;

		mpz_ui_pow_ui( mpResult.get_mpz_t(), aValue, anExponent );

		return( Integer(mpResult) );
	}


	/**
	 * Serialization
	 */
	inline void toStream(OutStream & os) const override
	{
		os << TAB << mValue;
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL << std::flush;
	}

	virtual std::string str() const override
	{
		return( OSS() << mValue );
	}

	inline virtual std::string strNum(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const override
	{
		return( OSS() << mValue );
	}

};

} /* namespace sep */

#endif /* FML_NUMERIC_GMP_INTEGERIMPL_H_ */

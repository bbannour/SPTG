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

#ifndef FML_NUMERIC_GMP_RATIONALIMPL_H_
#define FML_NUMERIC_GMP_RATIONALIMPL_H_

#include <gmpxx.h>

#include <fml/numeric/Number.h>

#include <fml/numeric/Integer.h>

#include <cmath>


namespace sep
{


class Rational :
		public Number,
		public GenericNumberClass< mpq_class , Rational >
{

	AVM_DECLARE_CLONABLE_CLASS( Rational )


	/**
	 * TYPEDEF
	 */
public:
	typedef  mpq_class  RawValueType;

private:
	typedef  GenericNumberClass< RawValueType , Rational >  ThisNumberClass;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	// RawValueType
	Rational(const RawValueType & aValue)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( aValue )
	{
		simplif();
	}

	// mpq_t
	Rational(const mpq_t & aValue)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aValue) )
	{
		simplif();
	}

	// Integer / Integer
	Rational(const Integer & aNumerator, const Integer & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			aNumerator.getValue(), aDenominator.getValue()) )
	{
		simplif();
	}

	// Integer::RawValueType / Integer::RawValueType
	// i.e mpz_class / mpz_class
	Rational(const Integer::RawValueType & aNumerator,
			const Integer::RawValueType & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator, aDenominator) )
	{
		simplif();
	}

	// mpz_t / mpz_t
	Rational(const mpz_t & aNumerator, const mpz_t & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer::RawValueType(aNumerator),
			Integer::RawValueType(aDenominator)) )
	{
		simplif();
	}

	// avm_integer_t / avm_integer_t  i.e.  std::int64_t / std::int64_t
	Rational(avm_integer_t aNumerator, avm_integer_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer( aNumerator ).getValue(),
			Integer( aDenominator ).getValue() ) )
	{
		simplif();
	}

	// avm_integer_t / avm_uinteger_t  i.e.  std::int64_t / std::uint64_t
	Rational(avm_integer_t aNumerator, avm_uinteger_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer( aNumerator ).getValue(),
			Integer( aDenominator ).getValue() ) )
	{
		simplif();
	}

	// avm_uinteger_t / avm_integer_t  i.e.  std::uint64_t / std::int64_t
	Rational(avm_uinteger_t aNumerator, avm_integer_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer( aNumerator ).getValue(),
			Integer( aDenominator ).getValue() ) )
	{
		simplif();
	}

	// avm_uinteger_t / avm_uinteger_t  i.e.  std::uint64_t / std::uint64_t
	Rational(avm_uinteger_t aNumerator, avm_uinteger_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer( aNumerator ).getValue(),
			Integer( aDenominator ).getValue() ) )
	{
		//!! NOTHING
	}

	// std::string / avm_integer_t  i.e.  std::string / std::int64_t
	Rational(const std::string & aNumerator, avm_integer_t aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer( aNumerator ).getValue(),
			Integer( aDenominator ).getValue() ) )
	{
		simplif();
	}

	// avm_integer_t / std::string  i.e.  std::int64_t / std::string
	Rational(avm_integer_t aNumerator, const std::string & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer( aNumerator ).getValue(),
			Integer( aDenominator ).getValue() ) )
	{
		simplif();
	}

	// std::string / std::string
	Rational(const std::string & aNumerator, const std::string & aDenominator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(
			Integer::RawValueType(aNumerator),
			Integer::RawValueType(aDenominator) ) )
	{
		simplif();
	}

	// Integer
	Rational(const Integer & aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( aNumerator.getValue() ) )
	{
		simplif();
	}

	// Integer::RawValueType  i.e.  mpz_class
	Rational(const Integer::RawValueType & aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType(aNumerator) )
	{
		simplif();
	}

	// mpz_t
	Rational(const mpz_t & aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType(aNumerator) ) )
	{
		simplif();
	}

	// avm_integer_t i.e. std::int64_t
	Rational(avm_integer_t aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer( aNumerator ).getValue() ) )
	{
		simplif();
	}

	// avm_uinteger_t i.e. std::uint64_t
	Rational(avm_uinteger_t aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer( aNumerator ).getValue() ) )
	{
		simplif();
	}

#ifdef _AVM_NEED_INT64_T_OVERLOADS_

	// long
	Rational(long aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType(aNumerator) ) )
	{
		simplif();
	}

	// unsigned long
	Rational(unsigned long aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType(aNumerator) ) )
	{
		simplif();
	}

#endif /* _AVM_NEED_INT64_T_OVERLOADS_ */

	// int32_t
	Rational(int aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType(aNumerator) ) )
	{
		simplif();
	}

	// uint32_t
	Rational(unsigned int aNumerator)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( Integer::RawValueType(aNumerator) ) )
	{
		simplif();
	}

	// std::string
	Rational(const std::string & aRational)
	: Number( CLASS_KIND_T( Rational ) ),
	ThisNumberClass( RawValueType( ) )
	{
		fromString(ThisNumberClass::mValue, aRational);

		simplif();
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Rational(const Rational & aRational)
	: Number( aRational ),
	ThisNumberClass( aRational )
	{
		simplif();
	}


	inline static void fromString(RawValueType & rop, const std::string & aValue)
	{
		std::string::size_type pos = aValue.find_first_of("/.");
		if( pos != std::string::npos)
		{
			if( aValue[pos] == '/' )
			{
				rop = RawValueType( aValue );
			}
			else //if( aValue[pos] == '.' )
			{
				Integer aNumer( std::string(aValue).erase(pos, 1) );

				Integer aDenom = Integer::pow(10, aValue.size() - (pos + 1));

				rop = RawValueType( aNumer.getValue(), aDenom.getValue() );
			}
		}
		else
		{
			rop = RawValueType( aValue );
		}
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
	bool simplif()
	{
		ThisNumberClass::mValue.canonicalize();

		return( true );
	}


	/**
	 * GETTER - SETTER
	 * ThisNumberClass::mValue
	 */
	inline Integer getNumerator() const
	{
		return( Integer( ThisNumberClass::mValue.get_num() ) );
	}

	inline Integer getDenominator() const
	{
		return( Integer( ThisNumberClass::mValue.get_den() ) );
	}


	inline const Integer::RawValueType & rawNumerator() const
	{
		return( ThisNumberClass::mValue.get_num() );
	}

	inline const Integer::RawValueType & rawDenominator() const
	{
		return( ThisNumberClass::mValue.get_den() );
	}


	inline void setValue(avm_integer_t aNumerator, avm_integer_t aDenominator)
	{
		ThisNumberClass::mValue = RawValueType(
				Integer( aNumerator ).getValue(),
				Integer( aDenominator ).getValue() );
	}


	inline void setValue(avm_integer_t aValue)
	{
		ThisNumberClass::mValue = RawValueType( Integer( aValue ).getValue() );
	}


	/**
	 * BASICS TESTS
	 */
	inline virtual int sign() const override
	{
		return( mpq_sgn(ThisNumberClass::mValue.get_mpq_t()) );
	}

	inline virtual bool isZero() const override
	{
		return( sign() == 0 );
	}

	inline virtual bool isOne() const override
	{
		return( mpq_cmp_si(
				ThisNumberClass::mValue.get_mpq_t(), 1, 1) == 0 );
	}

	inline virtual bool isNegativeOne() const override
	{
		return( mpq_cmp_si(
				ThisNumberClass::mValue.get_mpq_t(), -1, 1) == 0 );
	}


	/**
	 * CONVERSION
	 */
#define MPQ_IS_INTEGER( MPQ_NUM,  MPQ_DEN, INF, SUP)   \
	(mpz_cmp_si(MPQ_DEN.get_mpz_t(), 1  ) == 0) &&   \
	(mpz_cmp_si(MPQ_NUM.get_mpz_t(), INF) >= 0) &&   \
	(mpz_cmp_ui(MPQ_NUM.get_mpz_t(), SUP) <= 0)

#define MPQ_IS_POSITIVE_INTEGER(MPQ_NUM,  MPQ_DEN, SUP)          \
	(sign() >= 0)                                            &&  \
	(mpz_cmp_si(MPQ_DEN.get_mpz_t(), 1  ) == 0)              &&  \
	(mpz_cmp_ui(MPQ_NUM.get_mpz_t(), MPQ_NUM.get_ui()) == 0) &&  \
	(mpz_cmp_ui(MPQ_NUM.get_mpz_t(), SUP) <= 0)


	inline virtual bool isInt32() const override
	{
//		return( MPQ_IS_INTEGER(rawNumerator(), rawDenominator(),
//				INT32_MIN, INT32_MAX) );

		return( (mpz_cmp_si(rawDenominator().get_mpz_t(), 1  ) == 0)
				&& rawNumerator().fits_sint_p() );
	}

	inline virtual std::int32_t toInt32() const override
	{
		return( static_cast< std::int32_t >( rawNumerator().get_si() ) );
	}

	inline virtual bool isInt64() const override
	{
//		return( MPQ_IS_INTEGER(rawNumerator(), rawDenominator(),
//				INT64_MIN, INT64_MAX) );

		return( (mpz_cmp_si(rawDenominator().get_mpz_t(), 1  ) == 0)
				&& rawNumerator().fits_slong_p() );
	}

	inline virtual std::int64_t toInt64() const override
	{
		return( static_cast< std::int64_t >( rawNumerator().get_si() ) );
	}


	inline virtual bool isInteger() const override
	{
//		return( MPQ_IS_INTEGER(rawNumerator(), rawDenominator(),
//				AVM_NUMERIC_MIN_INTEGER, AVM_NUMERIC_MAX_INTEGER) );

		return( (mpz_cmp_si(rawDenominator().get_mpz_t(), 1  ) == 0)
				&& rawNumerator().fits_slong_p() );
	}

	inline virtual avm_integer_t toInteger() const override
	{
		return( rawNumerator().get_si() );
	}


	inline bool isPosInteger() const
	{
//		return( MPQ_IS_POSITIVE_INTEGER(rawNumerator(),
//				rawDenominator(), AVM_NUMERIC_MAX_UINTEGER) );

		return( (mpz_cmp_si(rawDenominator().get_mpz_t(), 1  ) == 0)
				&& rawNumerator().fits_ulong_p() );
	}


	inline virtual bool isUInteger() const override
	{
//		return( MPQ_IS_POSITIVE_INTEGER(rawNumerator(),
//				rawDenominator(), AVM_NUMERIC_MAX_UINTEGER) );

		return( (mpz_cmp_si(rawDenominator().get_mpz_t(), 1  ) == 0)
				&& rawNumerator().fits_ulong_p() );
	}

	inline virtual avm_uinteger_t toUInteger() const override
	{
		return( static_cast< avm_uinteger_t >( rawNumerator().get_ui() ) );
	}


	inline virtual bool isRational() const override
	{
		return( true );
	}

	virtual avm_integer_t toDenominator() const override
	{
		return( rawDenominator().get_si() );
	}

	virtual avm_integer_t toNumerator() const override
	{
		return( rawNumerator().get_si() );
	}


	inline virtual bool isFloat() const override
	{
		return( true );
	}

	inline virtual avm_float_t toFloat() const override
	{
		return( static_cast< avm_float_t >( ThisNumberClass::mValue.get_d() ) );
	}


	inline virtual bool isReal() const override
	{
		return( true );
	}

	inline virtual avm_real_t toReal() const override
	{
		return( static_cast< avm_real_t >( ThisNumberClass::mValue.get_d() ) );
	}


	/**
	 * math function
	 */
	inline void set_pow(avm_uinteger_t anExponent)
	{
//		RawValueType mpResult;
//
//		mpq_pow_ui( mpResult.get_mpq_t(),
//				ThisNumberClass::mValue.get_mpq_t(), anExponent );
//
//		ThisNumberClass::mValue = mpResult;

		mpz_pow_ui( mpq_numref(ThisNumberClass::mValue.get_mpq_t()),
				mpq_numref(ThisNumberClass::mValue.get_mpq_t()), anExponent );

		mpz_pow_ui( mpq_denref(ThisNumberClass::mValue.get_mpq_t()),
				mpq_denref(ThisNumberClass::mValue.get_mpq_t()), anExponent );
	}


	/**
	 * Serialization
	 */
	inline virtual void toStream(OutStream & os) const override
	{
		os << TAB << rawNumerator();
		if( rawDenominator() != 1 )
		{
			os << "/" << rawDenominator();
		}
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}

	virtual std::string str() const override
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
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const override
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
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( OSS() << rawNumerator() );
	}

	inline virtual std::string strDenominator(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( OSS() << rawDenominator() );
	}

};


} /* namespace sep */

#endif /* FML_NUMERIC_GMP_RATIONALIMPL_H_ */

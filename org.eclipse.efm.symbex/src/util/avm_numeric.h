/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 mars 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVM_NUMERIC_H_
#define AVM_NUMERIC_H_

#include <cstddef>

#include <limits>

//#include <cinttypes>
#define __STDC_FORMAT_MACROS
//#include <inttypes.h>
#undef __STDC_FORMAT_MACROS

#include <stdint.h>
//?#include <cstdint>



#ifdef __AVM_MINGW__ /* NEED INT64_T OVERLOADS */

#define _AVM_NEED_INT64_T_OVERLOADS_

#else //#ifdef __AVM_LINUX__

#undef _AVM_NEED_INT64_T_OVERLOADS_

#endif


namespace sep
{


/* Integers of type char have 8 bits. */
#define avm_char_bitsize        8

/* Integers of type short have 16 bits. */
#define avm_short_bitsize      16

/* Integers of type int have 32 bits. */
#define avm_int_bitsize        32

/* Integers of type long have 32 or 64 bits. */
//#define avm_long_bitsize       32

/* Integers of type long long have 64 bits. */
#define avm_long_long_bitsize  64



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// AVM NUMERIC TYPE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

typedef   int8_t       avm_int8_t;
typedef  uint8_t       avm_uint8_t;

typedef   int16_t      avm_int16_t;
typedef  uint16_t      avm_uint16_t;

typedef   int32_t      avm_int32_t;
typedef  uint32_t      avm_uint32_t;

typedef  uint32_t      avm_offset_t;

typedef   int64_t      avm_int64_t;
typedef  uint64_t      avm_uint64_t;

typedef   int64_t      avm_integer_t;
typedef  uint64_t      avm_uinteger_t;

typedef  double        avm_float_t;

typedef  long double   avm_real_t;


typedef   int64_t      avm_itime_t;
typedef  uint64_t      avm_uitime_t;

typedef  long double   avm_ftime_t;


/**
 * The Address Type
 */
typedef  intptr_t      avm_address_t;


/**
 * The Size Type
 */
typedef std::size_t    avm_size_t;



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// AVM NUMERIC LIMITS
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

#define AVM_NUMERIC_MAX_INT      ( std::numeric_limits<int>::max() )
#define AVM_NUMERIC_MIN_INT      ( std::numeric_limits<int>::min() )

#define AVM_NUMERIC_MAX_UINT     ( std::numeric_limits<unsigned int>::max() )
#define AVM_NUMERIC_MIN_UINT     ( std::numeric_limits<unsigned int>::min() )


#define AVM_NUMERIC_MAX_OFFSET   ( std::numeric_limits<sep::avm_uinteger_t>::max() )
#define AVM_NUMERIC_MIN_OFFSET   ( std::numeric_limits<sep::avm_uinteger_t>::min() )


#define AVM_NO_OFFSET            ( static_cast<sep::avm_offset_t>(-1) )


#define AVM_NUMERIC_MAX_LONG     ( std::numeric_limits<long>::max() )
#define AVM_NUMERIC_MIN_LONG     ( std::numeric_limits<long>::min() )

#define AVM_NUMERIC_MAX_ULONG    ( std::numeric_limits<unsigned long>::max() )
#define AVM_NUMERIC_MIN_ULONG    ( std::numeric_limits<unsigned long>::min() )


#define AVM_NUMERIC_MAX_INT8     ( std::numeric_limits<sep::avm_int8_t>::max() )
#define AVM_NUMERIC_MIN_INT8     ( std::numeric_limits<sep::avm_int8_t>::min() )

#define AVM_NUMERIC_MAX_INT16    ( std::numeric_limits<sep::avm_int16_t>::max() )
#define AVM_NUMERIC_MIN_INT16    ( std::numeric_limits<sep::avm_int16_t>::min() )

#define AVM_NUMERIC_MAX_INT32    ( std::numeric_limits<sep::avm_int32_t>::max() )
#define AVM_NUMERIC_MIN_INT32    ( std::numeric_limits<sep::avm_int32_t>::min() )

#define AVM_NUMERIC_MAX_INT64    ( std::numeric_limits<sep::avm_int64_t>::max() )
#define AVM_NUMERIC_MIN_INT64    ( std::numeric_limits<sep::avm_int64_t>::min() )


#define AVM_NUMERIC_MAX_UINT8    ( std::numeric_limits<sep::avm_uint8_t>::max() )
#define AVM_NUMERIC_MIN_UINT8    ( std::numeric_limits<sep::avm_uint8_t>::min() )

#define AVM_NUMERIC_MAX_UINT16   ( std::numeric_limits<sep::avm_uint16_t>::max() )
#define AVM_NUMERIC_MIN_UINT16   ( std::numeric_limits<sep::avm_uint16_t>::min() )

#define AVM_NUMERIC_MAX_UINT32   ( std::numeric_limits<sep::avm_uint32_t>::max() )
#define AVM_NUMERIC_MIN_UINT32   ( std::numeric_limits<sep::avm_uint32_t>::min() )

#define AVM_NUMERIC_MAX_UINT64   ( std::numeric_limits<sep::avm_uint64_t>::max() )
#define AVM_NUMERIC_MIN_UINT64   ( std::numeric_limits<sep::avm_uint64_t>::min() )


#define AVM_NUMERIC_MAX_SIZE_T   ( std::numeric_limits<sep::avm_size_t>::max() )
#define AVM_NUMERIC_MIN_SIZE_T   ( std::numeric_limits<sep::avm_size_t>::min() )


#define AVM_NUMERIC_MAX_INTEGER  ( std::numeric_limits<sep::avm_integer_t>::max() )
#define AVM_NUMERIC_MIN_INTEGER  ( std::numeric_limits<sep::avm_integer_t>::min() )

#define AVM_NUMERIC_MAX_UINTEGER ( std::numeric_limits<sep::avm_uinteger_t>::max() )
#define AVM_NUMERIC_MIN_UINTEGER ( std::numeric_limits<sep::avm_uinteger_t>::min() )


#define AVM_NUMERIC_MAX_FLOAT    ( std::numeric_limits<float>::max() )
#define AVM_NUMERIC_MIN_FLOAT    ( std::numeric_limits<float>::min() )

#define AVM_NUMERIC_MAX_UFLOAT   ( std::numeric_limits<unsigned float>::max() )
#define AVM_NUMERIC_MIN_UFLOAT   ( std::numeric_limits<unsigned float>::min() )


#define AVM_NUMERIC_MAX_DOUBLE   ( std::numeric_limits<double>::max() )
#define AVM_NUMERIC_MIN_DOUBLE   ( std::numeric_limits<double>::min() )

#define AVM_NUMERIC_MAX_UDOUBLE  ( std::numeric_limits<unsigned double>::max() )
#define AVM_NUMERIC_MIN_UDOUBLE  ( std::numeric_limits<unsigned double>::min() )


#define AVM_NUMERIC_MAX_FLOAT_T  ( std::numeric_limits<sep::avm_float_t>::max() )
#define AVM_NUMERIC_MIN_FLOAT_T  ( std::numeric_limits<sep::avm_float_t>::min() )

#define AVM_NUMERIC_MAX_REAL_T   ( std::numeric_limits<sep::avm_real_t>::max() )
#define AVM_NUMERIC_MIN_REAL_T   ( std::numeric_limits<sep::avm_real_t>::min() )



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// AVM NUMERIC PRECISION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

#define OS_FLOAT_PRECISION    \
		std::setprecision( std::numeric_limits< double >::digits10 + 1 )

#define OS_REAL_PRECISION   \
		std::setprecision( std::numeric_limits< long double >::digits10 + 1 )


#define AVM_MUMERIC_PRECISION  17


struct RANDOM
{

	////////////////////////////////////////////////////////////////////////////
	// NUMERIC RANDOM GENERATOR
	////////////////////////////////////////////////////////////////////////////


	inline static char gen_char()
	{
		return( static_cast< char >( gen_int(
				std::numeric_limits<sep::avm_uint8_t>::min(),
				std::numeric_limits<sep::avm_uint8_t>::max()) ) );
	}


	static avm_uinteger_t gen_uinteger(avm_uinteger_t min, avm_uinteger_t max);
	static avm_integer_t gen_integer(avm_integer_t min, avm_integer_t max);

	inline static avm_integer_t gen_integer()
	{
		return( gen_integer(AVM_NUMERIC_MIN_INTEGER, AVM_NUMERIC_MAX_INTEGER) ) ;
	}

	static avm_uint32_t gen_uint(avm_uint32_t min, avm_uint32_t max);
	static avm_int32_t gen_int(avm_int32_t min, avm_int32_t max);

	inline static avm_int32_t gen_int()
	{
		return( gen_int(AVM_NUMERIC_MIN_INT32, AVM_NUMERIC_MAX_INT32) ) ;
	}

	static double gen_double(double min, double max, avm_uint64_t previous);

	inline static double gen_double(long unsigned int previous)
	{
		return( gen_double(previous) ) ;
	}

};


}

#endif /* AVM_NUMERIC_H_ */

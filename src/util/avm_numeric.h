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

//?#include <stdint.h>
#include <cstdint>



#ifdef __AVM_MINGW__ /* NEED INT64_T OVERLOADS */

#define _AVM_NEED_INT64_T_OVERLOADS_

#else //#ifdef __AVM_LINUX__

#undef _AVM_NEED_INT64_T_OVERLOADS_

#endif


namespace sep
{

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// AVM NUMERIC TYPE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

typedef  std::uint32_t    avm_offset_t;

typedef  std::intmax_t    avm_integer_t;

typedef  std::uintmax_t   avm_uinteger_t;


typedef  double           avm_float_t;

typedef  long double      avm_real_t;


typedef   int64_t         avm_itime_t;
typedef  uint64_t         avm_uitime_t;

typedef  long double      avm_ftime_t;


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// AVM NUMERIC LIMITS
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

#define AVM_NUMERIC_MAX_OFFSET   ( std::numeric_limits<sep::avm_offset_t>::max() )

#define AVM_NO_OFFSET            ( static_cast<sep::avm_offset_t>(-1) )

#define AVM_NUMERIC_MAX_SIZE_T   ( std::numeric_limits<std::size_t>::max() )

#define AVM_NUMERIC_MAX_INTEGER  ( std::numeric_limits<sep::avm_integer_t>::max() )
#define AVM_NUMERIC_MIN_INTEGER  ( std::numeric_limits<sep::avm_integer_t>::min() )

#define AVM_NUMERIC_MAX_UINTEGER ( std::numeric_limits<sep::avm_uinteger_t>::max() )


#define AVM_NUMERIC_MAX_FLOAT    ( std::numeric_limits<float>::max() )
#define AVM_NUMERIC_MIN_FLOAT    ( std::numeric_limits<float>::min() )

#define AVM_NUMERIC_MAX_DOUBLE   ( std::numeric_limits<double>::max() )
#define AVM_NUMERIC_MIN_DOUBLE   ( std::numeric_limits<double>::min() )

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
				std::numeric_limits<std::uint8_t>::min(),
				std::numeric_limits<std::uint8_t>::max()) ) );
	}


	static avm_uinteger_t gen_uinteger(avm_uinteger_t min, avm_uinteger_t max);
	static avm_integer_t gen_integer(avm_integer_t min, avm_integer_t max);

	inline static avm_integer_t gen_integer()
	{
		return( gen_integer(AVM_NUMERIC_MIN_INTEGER, AVM_NUMERIC_MAX_INTEGER) ) ;
	}

	static std::uint32_t gen_uint(std::uint32_t min, std::uint32_t max);
	static std::int32_t gen_int(std::int32_t min, std::int32_t max);

	inline static std::int32_t gen_int()
	{
		return( gen_int(INT32_MIN, INT32_MAX) ) ;
	}

	static double gen_double(double min, double max, std::uint64_t previous);

//!?< LLVM Warning >
//	inline static double gen_double(long unsigned int previous)
//	{
//		return( gen_double(previous) ) ;
//	}

};


}

#endif /* AVM_NUMERIC_H_ */

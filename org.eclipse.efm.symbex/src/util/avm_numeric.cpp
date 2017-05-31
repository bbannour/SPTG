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

#include "avm_numeric.h"

#include <time.h>

#include <boost/random.hpp>

namespace sep
{


avm_uinteger_t RANDOM::gen_uinteger(avm_uinteger_t min, avm_uinteger_t max)
{
	if( min < max )
	{
		// Initialize a random number generator.
		// Boost provides a bunch of these, note that some of them are not meant
		// for direct user usage and you should instead use a specialization
		// (for example, don't use linear_congruential and use minstd_rand or
		// minstd_rand0 instead)

		// This constructor seeds the generator with the current time.
		// As mentioned in Boost's sample program, time(0) is not a great seed,
		// but you can probably get away with it for most situations.
		// Consider using more precise timers such as gettimeofday on *nix or
		// GetTickCount/timeGetTime/QueryPerformanceCounter on Windows.
		boost::mt19937 randGen(static_cast< avm_uint64_t >(clock()));

		// Now we set up a distribution. Boost provides a bunch of these as well.
		// This is the preferred way to generate numbers in a certain range.
		boost::uniform_int<avm_uinteger_t> uIntDist(min, max);

		// Finally, declare a variate_generator which maps the random number
		// generator and the distribution together. This variate_generator
		// is usable like a function call.
		boost::variate_generator< boost::mt19937 & ,
				boost::uniform_int<avm_uinteger_t> > GetRand(randGen, uIntDist);

		// Generate a random number
		return( GetRand() );
	}
	else// if( min == max )
	{
		return( min );
	}
}


avm_integer_t RANDOM::gen_integer(avm_integer_t min, avm_integer_t max)
{
	if( min < max )
	{
		// Initialize a random number generator.
		// Boost provides a bunch of these, note that some of them are not meant
		// for direct user usage and you should instead use a specialization
		// (for example, don't use linear_congruential and use minstd_rand or
		// minstd_rand0 instead)

		// This constructor seeds the generator with the current time.
		// As mentioned in Boost's sample program, time(0) is not a great seed,
		// but you can probably get away with it for most situations.
		// Consider using more precise timers such as gettimeofday on *nix or
		// GetTickCount/timeGetTime/QueryPerformanceCounter on Windows.
		boost::mt19937 randGen(static_cast< avm_uint64_t >(clock()));

		// Now we set up a distribution. Boost provides a bunch of these as well.
		// This is the preferred way to generate numbers in a certain range.
		boost::uniform_int<avm_integer_t> uIntDist(min, max);

		// Finally, declare a variate_generator which maps the random number
		// generator and the distribution together. This variate_generator
		// is usable like a function call.
		boost::variate_generator< boost::mt19937 & ,
				boost::uniform_int<avm_integer_t> > GetRand(randGen, uIntDist);

		// Generate a random number
		return( GetRand() );
	}
	else// if( min == max )
	{
		return( min );
	}
}



avm_uint32_t RANDOM::gen_uint(avm_uint32_t min, avm_uint32_t max)
{
	if( min < max )
	{
		// Initialize a random number generator.
		// Boost provides a bunch of these, note that some of them are not meant
		// for direct user usage and you should instead use a specialization
		// (for example, don't use linear_congruential and use minstd_rand or
		// minstd_rand0 instead)

		// This constructor seeds the generator with the current time.
		// As mentioned in Boost's sample program, time(0) is not a great seed,
		// but you can probably get away with it for most situations.
		// Consider using more precise timers such as gettimeofday on *nix or
		// GetTickCount/timeGetTime/QueryPerformanceCounter on Windows.
		boost::mt19937 randGen(static_cast< avm_uint64_t >(clock()));

		// Now we set up a distribution. Boost provides a bunch of these as well.
		// This is the preferred way to generate numbers in a certain range.
		boost::uniform_int<avm_uint32_t> uIntDist(min, max);

		// Finally, declare a variate_generator which maps the random number
		// generator and the distribution together. This variate_generator
		// is usable like a function call.
		boost::variate_generator< boost::mt19937 & ,
				boost::uniform_int<avm_uint32_t> > GetRand(randGen, uIntDist);

		// Generate a random number
		return( GetRand() );
	}
	else// if( min == max )
	{
		return( min );
	}
}


avm_int32_t RANDOM::gen_int(avm_int32_t min, avm_int32_t max)
{
	if( min < max )
	{
		// Initialize a random number generator.
		// Boost provides a bunch of these, note that some of them are not meant
		// for direct user usage and you should instead use a specialization
		// (for example, don't use linear_congruential and use minstd_rand or
		// minstd_rand0 instead)

		// This constructor seeds the generator with the current time.
		// As mentioned in Boost's sample program, time(0) is not a great seed,
		// but you can probably get away with it for most situations.
		// Consider using more precise timers such as gettimeofday on *nix or
		// GetTickCount/timeGetTime/QueryPerformanceCounter on Windows.
		boost::mt19937 randGen(static_cast< avm_uint64_t >(clock()));

		// Now we set up a distribution. Boost provides a bunch of these as well.
		// This is the preferred way to generate numbers in a certain range.
		boost::uniform_int<avm_int32_t> uIntDist(min, max);

		// Finally, declare a variate_generator which maps the random number
		// generator and the distribution together. This variate_generator
		// is usable like a function call.
		boost::variate_generator< boost::mt19937 & ,
				boost::uniform_int<avm_int32_t> > GetRand(randGen, uIntDist);

		// Generate a random number
		return( GetRand() );
	}
	else// if( min == max )
	{
		return( min );
	}
}



double RANDOM::gen_double(double min, double max, avm_uint64_t previous)
{
	if( min < max )
	{
		// Initialize a random number generator.
		// Boost provides a bunch of these, note that some of them are not meant
		// for direct user usage and you should instead use a specialization
		// (for example, don't use linear_congruential and use minstd_rand or
		// minstd_rand0 instead)

		// This constructor seeds the generator with the current time.
		// As mentioned in Boost's sample program, time(0) is not a great seed,
		// but you can probably get away with it for most situations.
		// Consider using more precise timers such as gettimeofday on *nix or
		// GetTickCount/timeGetTime/QueryPerformanceCounter on Windows.

//		boost::mt19937 randGen(std::time(0));
//		AVM_FLOAT_TIME_TYPE tps0 = ExecutionTime::getClock();
//		AVM_OS_TRACE << OS_FLOAT_PRECISION << "Valeur tps0 = " << tps0
//				<< " clock = " << static_cast<long unsigned int>(clock())
//				<< std::endl;
//		unsigned int tps = (unsigned int)tps0;
//		AVM_OS_TRACE << "Valeur tps = " << tps << std::endl;
		boost::mt19937 randGen(static_cast< avm_uint64_t >(clock()) + previous);

		// Now we set up a distribution. Boost provides a bunch of these as well.
		// This is the preferred way to generate numbers in a certain range.
		boost::uniform_real<double> uRealDist(min, max);

		// Finally, declare a variate_generator which maps the random number
		// generator and the distribution together. This variate_generator
		// is usable like a function call.
		boost::variate_generator< boost::mt19937 & ,
				boost::uniform_real<double> > GetRand(randGen, uRealDist);

		// Generate a random number
		return( GetRand() );
	}
	else// if( min == max )
	{
		return( min );
	}
}


}

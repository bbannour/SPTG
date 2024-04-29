/*******************************************************************************
 * Copyright (c) 2017 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef UTIL_EXECUTIONCHRONO_H_
#define UTIL_EXECUTIONCHRONO_H_

#include <printer/OutStream.h>

#include <util/avm_numeric.h>

#include <chrono>
#include <string>

//#include <boost/chrono.hpp>


namespace sep
{


class ExecutionChrono
{

protected :
	/**
	 * ATTRIBUTES
	 */
	std::chrono::high_resolution_clock::time_point mHighResolutionTimePointStart;
	std::chrono::high_resolution_clock::time_point mHighResolutionTimePointEnd;

	std::chrono::steady_clock::time_point mSteadyTimePointStart;
	std::chrono::steady_clock::time_point mSteadyTimePointEnd;

	std::chrono::system_clock::time_point mSystemTimePointStart;
	std::chrono::system_clock::time_point mSystemTimePointEnd;

	// The Boost version: real - user - system
//	boost::chrono::process_cpu_clock::time_point mBoostCpuTimePointStart;
//	boost::chrono::process_cpu_clock::time_point mBoostCpuTimePointEnd;


public:
	/**
	 * CONSTRUCTOR
	 * DESTRUCTOR
	 */
	ExecutionChrono(bool startNow = false)
	: mHighResolutionTimePointStart( ),
	mHighResolutionTimePointEnd( ),

	mSteadyTimePointStart( ),
	mSteadyTimePointEnd( ),

	mSystemTimePointStart( ),
	mSystemTimePointEnd( )

	// The Boost version: real - user - system
//	mBoostCpuTimePointStart( ),
//	mBoostCpuTimePointEnd( )
	{
		if( startNow )
		{
			startChrono();
		}
	}

	/**
	 * CONSTRUCTOR
	 * DESTRUCTOR
	 */
	virtual ~ExecutionChrono()
	{
		//!! NOTHING
	}


	/**
	 * TIME
	 * CLOCK
	 */
	static std::string current_time();

	static avm_ftime_t getClock();


	/**
	 * DURATION
	 */
	void startChrono();

	void endChrono();


	/**
	 * SERIALIZATION
	 */
	inline std::string str() const
	{
		StringOutStream oss( AVM_STR_INDENT );

		toStream(oss);

		return( oss.str() );
	}


	template<typename Rep, typename Period>
	void toStreamDuration(OutStream & out,
			std::chrono::duration<Rep, Period> duration) const
	{
		if( duration.count() > 0 )
		{
			std::chrono::hours hours =
					std::chrono::duration_cast<std::chrono::hours>(duration);
			duration -= hours;
			std::chrono::minutes minutes =
					std::chrono::duration_cast<std::chrono::minutes>(duration);
			duration -= minutes;
			std::chrono::seconds seconds =
					std::chrono::duration_cast<std::chrono::seconds>(duration);
			duration -= seconds;
			std::chrono::milliseconds milliseconds =
					std::chrono::duration_cast<std::chrono::milliseconds>(duration);
			duration -= milliseconds;
			std::chrono::microseconds microseconds =
					std::chrono::duration_cast<std::chrono::microseconds>(duration);
			duration -= microseconds;
			std::chrono::nanoseconds nanoseconds =
					std::chrono::duration_cast<std::chrono::nanoseconds>(duration);

			if( hours       .count() > 0 ) out << hours.count()        << "h";
			if( minutes     .count() > 0 ) out << minutes.count()      << "m";
			if( seconds     .count() > 0 ) out << seconds.count()      << "s";
			if( milliseconds.count() > 0 ) out << milliseconds.count() << "ms";
			if( microseconds.count() > 0 ) out << microseconds.count() << "us";
			if( nanoseconds .count() > 0 ) out << nanoseconds.count()  << "ns";
		}
		else
		{
			out << "0 ms";
		}
	}


//	template <class Rep, class Period>
//	void toStreamDuration(OutStream & out, const std::string & label,
//			boost::chrono::duration<Rep, Period> duration) const
//	{
//		out << label;
//
//		if( duration.count() > 0 )
//		{
//			boost::chrono::hours hours =
//					boost::chrono::duration_cast<boost::chrono::hours>(duration);
//			duration -= hours;
//			boost::chrono::minutes minutes =
//					boost::chrono::duration_cast<boost::chrono::minutes>(duration);
//			duration -= minutes;
//			boost::chrono::seconds seconds =
//					boost::chrono::duration_cast<boost::chrono::seconds>(duration);
//			duration -= seconds;
//			boost::chrono::milliseconds milliseconds =
//					boost::chrono::duration_cast<boost::chrono::milliseconds>(duration);
//			duration -= milliseconds;
//			boost::chrono::microseconds microseconds =
//					boost::chrono::duration_cast<boost::chrono::microseconds>(duration);
//			duration -= microseconds;
//			boost::chrono::nanoseconds nanoseconds =
//					boost::chrono::duration_cast<boost::chrono::nanoseconds>(duration);
//
//			if( hours       .count() > 0 ) out << hours.count()        << "h";
//			if( minutes     .count() > 0 ) out << minutes.count()      << "m";
//			if( seconds     .count() > 0 ) out << seconds.count()      << "s";
//			if( milliseconds.count() > 0 ) out << milliseconds.count() << "ms";
//			if( microseconds.count() > 0 ) out << microseconds.count() << "us";
//			if( nanoseconds .count() > 0 ) out << nanoseconds.count()  << "ns";
//		}
//		else
//		{
//			out << "0 ms";
//		}
//	}
//
//
//	template <class Rep, class Period>
//	void toStreamDuration(OutStream  & out, const std::string & label_real,
//			const std::string & label_user, const std::string & label_system,
//			boost::chrono::duration<Rep, Period> duration) const
//	{
//		boost::chrono::process_real_cpu_clock::duration duration_real(
//				duration.count().real );
//		toStreamDuration(out, label_real, duration_real);
//
//		boost::chrono::process_user_cpu_clock::duration duration_user(
//				duration.count().user );
//		toStreamDuration(out, label_user, duration_user);
//
//		boost::chrono::process_system_cpu_clock::duration duration_system(
//				duration.count().system );
//		toStreamDuration(out, label_system, duration_system);
//	}


	OutStream & toStream(OutStream & out) const;
};


} /* namespace sep */

#endif /* UTIL_EXECUTIONCHRONO_H_ */

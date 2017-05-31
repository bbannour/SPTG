/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
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
#ifndef UTIL_EXECUTIONTIME_H_
#define UTIL_EXECUTIONTIME_H_

#include <ctime>
#include <string>

#ifdef __AVM_UNIX__

#include <sys/resource.h>

#endif /* __AVM_UNIX__ */

#include <sys/time.h>

//!!! BOOST TODO
//#include <boost/date_time/posix_time/posix_time.hpp>

#include <util/avm_numeric.h>

namespace sep
{


class ExecutionTime
{
public :
	/**
	 * CONSTRUCTOR
	 * DESTRUCTOR
	 */
	ExecutionTime(bool startIt)
	{
		if( startIt )
		{
			start_time();
		}
	}

	/*METHODS*/
	void start_time();
	void finish_time();
	void get_time_usage(int * rtp, int * utp, int * stp);

	std::string format_time_milli(avm_uitime_t milliSecondes);
	std::string format_time_micro(avm_uitime_t microSecondes);
	std::string format_time_nano(avm_uitime_t nanoSecondes);

	std::string time_stat();

	static std::string current_time();

	static avm_ftime_t getClock();


protected :

	/*ATTRIBUTES*/


#ifdef __AVM_UNIX__
	struct timeval start_t;
	struct timeval finish_t;
	struct rusage start_r;
	struct rusage finish_r;
	clock_t finish_clock;
#endif /* __AVM_UNIX__ */

	avm_ftime_t t_depart;
	avm_ftime_t t_fin;

	std::time_t t_start;
	std::time_t t_end;

//!!! BOOST TODO
//	boost::posix_time::ptime time_start;
//	boost::posix_time::ptime time_end;
};


}


#endif /*UTIL_EXECUTIONTIME_H_*/

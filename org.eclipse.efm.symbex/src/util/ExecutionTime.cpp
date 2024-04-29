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
#define BODY_avm_tool_ExecutionTime 1
/***********************************************************
BODY OF THE ExecutionTime CLASS
***********************************************************/

#include "ExecutionTime.h"

#include <sstream>

#include <util/avm_string.h>


namespace sep
{


/**
* ExecutionTime::start_time
*
*/
void ExecutionTime::start_time()
{
#ifdef __AVM_UNIX__
	gettimeofday(&start_t, nullptr);
	getrusage(0, &start_r);
	clock();
#endif /* __AVM_UNIX__ */

	t_depart = getClock();

	t_start = std::time(nullptr);

//!!! BOOST TODO
//	time_start = boost::posix_time::microsec_clock::local_time();
}

/**
* ExecutionTime::finish_time
*
*/
void ExecutionTime::finish_time()
{
#ifdef __AVM_UNIX__
	gettimeofday(&finish_t, nullptr);
	getrusage(0, &finish_r);
	finish_clock = clock();
#endif /* __AVM_UNIX__ */


	t_end = std::time(nullptr);

	t_fin = getClock();

//!!! BOOST TODO
//	time_end =boost::posix_time::microsec_clock::local_time();
}

/**
* ExecutionTime::get_time_usage
*
*/
void ExecutionTime::get_time_usage(int * rtp, int * utp, int * stp)
{
#ifdef __AVM_UNIX__
#define TDIFF(f, s) \
		(((f).tv_sec - (s).tv_sec) * 1000 + \
				((f).tv_usec - (s).tv_usec + 500) / 1000)

	*rtp = TDIFF(finish_t, start_t);
	*utp = TDIFF(finish_r.ru_utime, start_r.ru_utime);
	*stp = TDIFF(finish_r.ru_stime, start_r.ru_stime);
#endif /* __AVM_UNIX__ */
}

/**
* ExecutionTime::format_time_milli
*
*/
std::string ExecutionTime::format_time_milli(avm_uitime_t milliSecondes)
{
	std::ostringstream osTime;

	avm_uitime_t s  = milliSecondes / 1000;
	avm_uitime_t mn = s  / 60;
	avm_uitime_t h  = mn / 60;

	avm_uitime_t ms = milliSecondes % 1000;
	s  = s  % 60;
	mn = mn % 60;

	if (h != 0)
	{
		osTime << h << "h";
	}
	if (mn != 0)
	{
		osTime << mn << "m";
	}
	if (s != 0)
	{
		osTime << s << "s";
	}
	if( (ms != 0) || (milliSecondes == 0) )
	{
		osTime << ms << "ms";
	}

	return( osTime.str() );
}

/**
* ExecutionTime::format_time_micro
*
*/
std::string ExecutionTime::format_time_micro(avm_uitime_t microSecondes)
{
	std::ostringstream osTime;

	avm_uitime_t ms  = microSecondes / 1000;
	avm_uitime_t s   = ms / 1000;
	avm_uitime_t mn  =  s / 60;
	avm_uitime_t h   = mn / 60;

	avm_uitime_t us = microSecondes % 1000;
	ms = ms % 1000;
	s  = s  % 60;
	mn = mn % 60;


	if (h != 0)
	{
		osTime << h << "h";
	}
	if (mn != 0)
	{
		osTime << mn << "m";
	}
	if (s != 0)
	{
		osTime << s << "s";
	}

	if( ms != 0 )
	{
		osTime << ms << "ms";
	}
	if( (us) || (microSecondes == 0) )
	{
		osTime << us << "µs";
	}

	return( osTime.str() );
}

/**
* ExecutionTime::format_time_nano
*
*/
std::string ExecutionTime::format_time_nano(avm_uitime_t nanoSecondes)
{
	std::ostringstream osTime;

	avm_uitime_t us = nanoSecondes / 1000;
	avm_uitime_t ms  = us / 1000;
	avm_uitime_t s   = ms / 1000;
	avm_uitime_t mn  =  s / 60;
	avm_uitime_t h   = mn / 60;

	avm_uitime_t ns = nanoSecondes % 1000;
	us = us % 1000;
	ms = ms % 1000;
	s  = s  % 60;
	mn = mn % 60;

	if (h != 0)
	{
		osTime << h << "h";
	}
	if (mn != 0)
	{
		osTime << mn << "m";
	}
	if (s != 0)
	{
		osTime << s << "s";
	}

	if( ms != 0 )
	{
		osTime << ms << "ms";
	}
	if( us != 0 )
	{
		osTime << us << "us";
	}
	if( (ns != 0) || (nanoSecondes == 0) )
	{
		osTime << ns << "ns";
	}

	return( osTime.str() );
}

/**
* ExecutionTime::print_time_stat
*
*/
std::string  ExecutionTime::time_stat()
{
	std::ostringstream osTime;

#ifdef __AVM_UNIX__
	int rtime, utime, stime;

	get_time_usage(&rtime, &utime, &stime);

	// a cause de: typedef signed long clock_t
	if ((utime + stime) > 2000000/*2147000*/)
	{
		finish_clock = utime + stime;
	}
	else
	{
		finish_clock = finish_clock / 1000;
	}

	osTime << "time:(real: " << format_time_milli(rtime);
	osTime << " cpu: " << format_time_milli(finish_clock);
	osTime << " user: " << format_time_milli(utime);
	osTime << " system: " << format_time_milli(stime) << ")";

//	osTime << "(realTime " << rtime << " cpuTime " << (finish_clock / 1000)
//			<< " userTime " << utime << " systemTime " << stime << "")";
#endif /* __AVM_UNIX__ */


	avm_ftime_t t_duree = (avm_ftime_t)(t_fin - t_depart);
//	osTime << " => " << OS_FLOAT_PRECISION << t_duree;
//	osTime << " --> " << format_time_micro( (avm_uitime_t)( t_duree * 1000000 ) );
	osTime << " --> " << format_time_nano( (avm_uitime_t)( t_duree * 1000000000 ) );

//??	osTime << " ==> " << std::difftime(t_end, t_start) << "s";


//!!! BOOST TODO
//	boost::posix_time::time_duration duration(time_end - time_start);

//	osTime << " => " << duration;
//	osTime << " --> " << format_time_micro( duration.total_microseconds() );

//!!! BOOST TODO
//	osTime << " --> " << format_time_nano( duration.total_nanoseconds() );

	// Date & Heure Courante
	std::time_t t;
	std::time(&t);
	osTime << " @ " << ( std::ctime(&t) );

	return( osTime.str() );
}



std::string  ExecutionTime::current_time()
{
	// Date & Heure Courante
	time_t t;
	time(&t);

	return( sep::to_string(ctime(&t)) );
}



/*
 * Recuperateur de temps :
 */
avm_ftime_t ExecutionTime::getClock ( void )
{
	avm_ftime_t d = 0 ;


#ifndef __linux
#ifdef _WIN32
	struct timeval tval ;
	struct timezone * tz = nullptr ;

	timerclear(&tval);

	if ( gettimeofday(&tval, tz) )
	{
#ifdef VERBOSE
		fprintf (stderr, "\nCLOCK ERROR !!!\n");
#endif
	}
	else
	{
		d = ((avm_ftime_t)(tval.tv_usec)/1000000.0) ;
		d = (avm_ftime_t) tval.tv_sec + d ;
	}
#else
	struct timespec cur_time;

	if (clock_gettime(CLOCK_REALTIME, &cur_time))
	{
#ifdef VERBOSE
		fprintf (stderr, "\nCLOCK ERROR !!!\n");
#endif
	}
	else
	{
		d = ((avm_ftime_t)(cur_time.tv_nsec) / (avm_ftime_t)(CLOCKS_PER_SEC)) / 1000000.0 ;
		d = (avm_ftime_t) cur_time.tv_sec + d ;
	}
#endif
#else
	struct timeval tval ;
	struct timezone * tz = nullptr ;

	timerclear(&tval);

	if ( gettimeofday(&tval, tz) )
	{
#ifdef VERBOSE
		fprintf (stderr, "\nCLOCK ERROR !!!\n");
#endif
	}
	else
	{
		d = ((avm_ftime_t)(tval.tv_usec)/1000000.0) ;
		d = (avm_ftime_t) tval.tv_sec + d ;
	}
#endif

	return d ;
}


/*
 * Programme de test:
 */
//int main( void )
//{
//	int i ;
//	double   t_depart, t_fin, t ;
//	double   duree_en_millisecondes ; /* 1000 pour une seconde, 3600000 pour une heure */
//
//
//	/* Calcul temps de depart */
//	t_depart = GetClock() ;
//
//	t = 0.0 ;
//
//	for ( i = 0 ; i < 500000000 ; ++i )
//		t = t + 1.0 ;
//
//	t_fin = GetClock() ;
//
//	if ( (t_depart*t_fin) < 0.0 )
//		fprintf ( stderr, "\n ATTENTION !!! Une erreur s'est produite\n");
//	else
//		fprintf ( stderr, "\n Temps écoulé %g secondes pour une boucle 500000000 : \n",(t_fin - t_depart));
//
//	t_depart = t_fin ;
//
//	t = 0.0 ;
//
//	for ( i = 0 ; i < 5000000 ; ++i )
//		t = t + 1.0 ;
//
//	t_fin= GetClock() ;
//
//	if ( (t_depart*t_fin) < 0.0 )
//		fprintf ( stderr, "\n ATTENTION !!! Une erreur s'est produite\n");
//	else
//		fprintf ( stderr, "\n Temps écoulé %g secondes pour une boucle 500000 : \n",(t_fin - t_depart));
//
//
//	return EXIT_SUCCESS ;
//}


}

/***END OF THE ExecutionTime CLASS BODY***/

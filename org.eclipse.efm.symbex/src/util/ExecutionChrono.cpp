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

#include "ExecutionChrono.h"

#include <iomanip>

namespace sep
{

/**
 * TIME
 */
std::string ExecutionChrono::current_time()
{
	// Date & Heure Courante
	std::time_t today =
			std::chrono::system_clock::to_time_t(
					std::chrono::system_clock::now() );

	return( OSS() << std::ctime(& today) );
}

avm_ftime_t ExecutionChrono::getClock()
{
	avm_ftime_t d = 0 ;

	return d ;
}


/**
 * DURATION
 */
void ExecutionChrono::startChrono()
{
	mHighResolutionTimePointStart = std::chrono::high_resolution_clock::now();
	mSteadyTimePointStart = std::chrono::steady_clock::now();
	mSystemTimePointStart = std::chrono::system_clock::now();

//	mBoostCpuTimePointStart = boost::chrono::process_cpu_clock::now();
}

void ExecutionChrono::endChrono()
{
	mHighResolutionTimePointEnd = std::chrono::high_resolution_clock::now();
	mSteadyTimePointEnd = std::chrono::steady_clock::now();
	mSystemTimePointEnd = std::chrono::system_clock::now();

//	mBoostCpuTimePointEnd = boost::chrono::process_cpu_clock::now();
}


/**
 * SERIALIZATION
 */
OutStream & ExecutionChrono::toStream(OutStream & out) const
{
	const auto highResolutionTimeDuration =
			mHighResolutionTimePointEnd - mHighResolutionTimePointStart;

	const auto highResolutionTimeDurationMilliseconds =
			std::chrono::duration_cast<std::chrono::milliseconds>(
					highResolutionTimeDuration);

	out << TAB << "$time< "
		<< highResolutionTimeDurationMilliseconds.count() << " ms , ";
	toStreamDuration( out, highResolutionTimeDuration );
	out << " >" << EOL;

	std::time_t today =
			std::chrono::system_clock::to_time_t(
					std::chrono::system_clock::now() );

	out << " @ " << std::ctime(& today) << EOL;


AVM_IF_DEBUG_ENABLED //FLAG( TIME )

//	toStreamDuration( out << TAB << "time:(", "real: ", " user: ", " system: ",
//			mBoostCpuTimePointEnd - mBoostCpuTimePointStart);

	toStreamDuration( out << "\tsteady: ",
			mSteadyTimePointEnd - mSteadyTimePointStart);

	toStreamDuration( out << " , system: ",
			mSystemTimePointEnd - mSystemTimePointStart);

	out << EOL;

AVM_ENDIF_DEBUG_ENABLED //_FLAG( TIME )

	return( out );
}


} /* namespace sep */

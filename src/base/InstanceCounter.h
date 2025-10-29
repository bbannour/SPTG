/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 déc. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASE_INSTANCECOUNTER_H_
#define BASE_INSTANCECOUNTER_H_

#include <printer/OutStream.h>		// printer/OutStream.h


namespace sep
{


template< class T >
class InstanceCounter
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstanceCounter()
	{
		++INSTANCE_CREATED;

		++INSTANCE_ALIVE;
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~InstanceCounter()
	{
		--INSTANCE_ALIVE;
	}


	/**
	 * Serialization
	 */
	inline static void reportCounters(
			OutStream & os, const std::string & className)
	{
		if( INSTANCE_ALIVE > 0 )
		{
			showCounters(os, className);
		}
	}

	inline static void showCounters(
			OutStream & os, const std::string & className)
	{
		int colSize = 32 - className.size();

		os << TAB << className << std::setw( (colSize > 0) ? colSize : 1 )
				<< " :> " << std::setw(6)
				<< INSTANCE_ALIVE << " / " << INSTANCE_CREATED
				<< EOL_FLUSH;
	}


	/**
	 * ATTRIBUTE
	 */
	static std::size_t INSTANCE_CREATED;

	static std::size_t INSTANCE_ALIVE;


};


template< class T >
std::size_t InstanceCounter< T >::INSTANCE_CREATED = 0;

template< class T >
std::size_t InstanceCounter< T >::INSTANCE_ALIVE = 0;



/**
 * Global report counter usage function
 */
void reportInstanceCounterUsage(OutStream & os, const std::string & aMsg, bool forced = false);



} /* namespace sep */
#endif /* BASE_INSTANCECOUNTER_H_ */

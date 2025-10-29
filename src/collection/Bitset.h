/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 nov. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMBITSET_H_
#define AVMBITSET_H_

#include <boost/dynamic_bitset.hpp>

#include <base/Injector.h>
#include <collection/Array.h>
#include <collection/Vector.h>

#include <util/avm_numeric.h>


namespace sep
{


class Bitset final :
		public boost::dynamic_bitset<>,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Bitset )
{

public:
	/**
	 * TYPEDEF
	 */
	typedef boost::dynamic_bitset<>  base_bitset_t;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Bitset()
	: base_bitset_t( )
	{
		//!! NOTHING
	}

	explicit Bitset(std::size_t length, bool isSet)
	: base_bitset_t( length )
	{
		if( isSet )
		{
			set();
		}
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Bitset(const Bitset & aBitset)
	: base_bitset_t( aBitset )
	{
		//!! NOTHING
	}


	Bitset(const base_bitset_t & aBitset)
	: base_bitset_t( aBitset )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Bitset()
	{
		//!! NOTHING
	}


	inline bool allTrue() const
	{
		return( base_bitset_t::count() == base_bitset_t::size() );
	}

	inline bool anyTrue() const
	{
		return( base_bitset_t::any() );
	}


	inline bool allFalse() const
	{
		return( base_bitset_t::none() );
	}

	inline bool anyFalse() const
	{
		return( base_bitset_t::count() != base_bitset_t::size() );
	}

};



////////////////////////////////////////////////////////////////////////////////
// COLEECTION TYPE DEFINITION
////////////////////////////////////////////////////////////////////////////////

typedef Array< Bitset * >  ArrayOfBitset;

typedef Vector< Bitset  >  VectorOfBitset;


}

#endif /* AVMBITSET_H_ */

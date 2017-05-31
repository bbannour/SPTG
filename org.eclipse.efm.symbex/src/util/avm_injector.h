/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVM_INJECTOR_H_
#define AVM_INJECTOR_H_

#include <base/InstanceCounter.h>


namespace sep
{

/**
 * Macro for instance counter management
 */
#define AVM_INJECT_INSTANCE_COUNTER_CLASS( ClassName )  \
		public InstanceCounter< ClassName >


/**
 * Macro for clonable object
 */
template< class T >
struct AvmClonableClass
{
	// DESTRUCTOR
	virtual ~AvmClonableClass()
	{
		//!! NOTHING
	}

	// CLONE API
	inline virtual T * clone() const
	{
		return( new T(*this) );
	}

};

#define AVM_INJECT_CLONABLE_CLASS( ClassName )  \
		public AvmClonableClass< ClassName >


/**
 * Macro for unclonable object
 */
template< class T >
struct AvmUnclonableClass
{
	// DESTRUCTOR
	virtual ~AvmUnclonableClass()
	{
		//!! NOTHING
	}

	// CLONE API
	inline virtual T * clone() const
	{
		return( const_cast< T * >(this) );
	}

};

#define AVM_INJECT_UNCLONABLE_CLASS( ClassName )  \
		public AvmUnclonableClass< ClassName >



/**
 * Generics Macros
 */
#define AVM_INJECT_CLONABLE_INSTANCE_COUNTER( ClassName )  \
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ClassName ) ,  \
		AVM_INJECT_CLONABLE_CLASS( ClassName )


#define AVM_INJECT_UNCLONABLE_INSTANCE_COUNTER( ClassName )  \
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ClassName ) ,  \
		AVM_INJECT_UNCLONABLE_CLASS( ClassName )



}

#endif /* AVM_INJECTOR_H_ */

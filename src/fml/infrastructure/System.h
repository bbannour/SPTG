/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 17 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SYSTEM_H_
#define SYSTEM_H_

#include <iostream>

#include <fml/infrastructure/Machine.h>

#include <collection/BFContainer.h>

#include <fml/infrastructure/Package.h>

namespace sep
{

////////////////////////////////////////////////////////////////////////////////
// SYSTEM POINTER
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// SYSTEM SMART POINTER
////////////////////////////////////////////////////////////////////////////////



class System final :
		public Machine,
		AVM_INJECT_STATIC_NULL_REFERENCE( System ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( System )
{

	AVM_DECLARE_CLONABLE_CLASS( System )


protected:
	/**
	 * ATTRIBUTES
	 */
	BFList mPackages;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	System(const std::string & aNameID,
			const Specifier & aSpecifier = Specifier::COMPONENT_SYSTEM_SPECIFIER)
	: Machine(CLASS_KIND_T( System ), nullptr, "spec::" + aNameID,
			aNameID, aNameID, aSpecifier),
	mPackages( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~System()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static System & nullref()
	{
		static System _NULL_("$null<System>", Specifier::OBJECT_NULL_SPECIFIER);
		_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );
		_NULL_.setSpecifier( Specifier::OBJECT_NULL_SPECIFIER );

		return( _NULL_ );
	}


	/**
	 * GETTER
	 * the machine container
	 * LC[R]A
	 */
	inline virtual Machine * getContainerMachine() const override
	{
		return( hasContainer() ? getContainer()->to_ptr< Machine >() : nullptr );
	}


	/**
	 * GETTER - SETTER
	 * mPackages
	 */
	inline BFList & getPackages()
	{
		return( mPackages );
	}

	inline const BFList & getPackages() const
	{
		return( mPackages );
	}

	inline void appendPackage(const BF & aPackage)
	{
		mPackages.append( aPackage );
	}


	/**
	 * Serialization
	 */
	virtual void strHeader(OutStream & out) const override;

	virtual void toStream(OutStream & out) const override;



};



}

#endif /* SYSTEM_H_ */

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



class System :
		public Machine,
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
	System(const std::string & aNameID)
	: Machine(CLASS_KIND_T( System ), NULL, "spec::" + aNameID,
			aNameID, aNameID, Specifier::COMPONENT_SYSTEM_SPECIFIER),
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
	 * the machine container
	 * LC[R]A
	 */
	inline virtual Machine * getContainerMachine() const
	{
		return( hasContainer() ? getContainer()->to< Machine >() : NULL );
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
	void strHeader(OutStream & os) const;

	void toStream(OutStream & os) const;

};


}

#endif /* SYSTEM_H_ */

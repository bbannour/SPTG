/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef LIBRARY_H_
#define LIBRARY_H_

#include <fml/infrastructure/Machine.h>

#include <fml/common/SpecifierElement.h>

#include <collection/BFContainer.h>

#include <common/BF.h>


namespace sep
{

class Machine;


class Package final : public Machine ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Package )
{

	AVM_DECLARE_CLONABLE_CLASS( Package )

protected:
	/**
	 * ATTRIBUTES
	 */
	TableOfMachine mPackages;

	std::string mLocation;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Package(const std::string & id)
	: Machine(CLASS_KIND_T( Package ), nullptr, "pack::" + id,
			id, id, Specifier::COMPONENT_PACKAGE_SPECIFIER),
	mPackages( ),
	mLocation( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Package()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mLocation
	 */
	inline std::string getLocation() const
	{
		return( mLocation );
	}

	inline void setLocation(const std::string & aLocation)
	{
		mLocation = aLocation;
	}


	/**
	 * GETTER - SETTER
	 * mPackages
	 */
	inline const TableOfMachine & getPackages() const
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
	virtual void strHeader(OutStream & os) const override;

	virtual void toStream(OutStream & os) const override;

};


}

#endif /* LIBRARY_H_ */

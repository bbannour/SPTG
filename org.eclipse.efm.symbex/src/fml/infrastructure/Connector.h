/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_INFRASTRUCTURE_CONNECTOR_H_
#define FML_INFRASTRUCTURE_CONNECTOR_H_

#include <fml/common/ObjectElement.h>
#include <fml/infrastructure/ComProtocol.h>

#include <common/AvmPointer.h>

#include <collection/Typedef.h>


#include <fml/infrastructure/ComRoute.h>


namespace sep
{


class InteractionPart;


class Connector :
		public ObjectElement,
		public ComProtocol,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Connector )
{

	AVM_DECLARE_CLONABLE_CLASS( Connector )

protected:
	/**
	 * TYPEDEF
	 */
	typedef APList < ComRoute * > APListOfComRoute;

public:
	/**
	 * TYPEDEF
	 */
	typedef APListOfComRoute::const_iterator  route_iterator;


protected:
	/**
	 * ATTRIBUTES
	 */
	APListOfComRoute mComRoutes;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Connector(const InteractionPart & anInteractionPart);

	/**
	 * DESTRUCTOR
	 */
	virtual ~Connector()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mComRoutes
	 */
	inline route_iterator begin() const
	{
		return( mComRoutes.begin() );
	}

	inline route_iterator end() const
	{
		return( mComRoutes.end() );
	}


	inline APListOfComRoute & getComRoutes()
	{
		return( mComRoutes );
	}

	inline const APListOfComRoute & getComRoutes() const
	{
		return( mComRoutes );
	}

	inline void appendComRoute(ComRoute * aComRoute)
	{
		mComRoutes.append( aComRoute );
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const;


public:

	/**
	 * ATTRIBUTES
	 */
	static std::string ANONYM_ID;

	inline bool isAnonymID() const
	{
		return( getNameID().empty() || (getNameID().find(ANONYM_ID) == 0) );
	}

};


}

#endif /* FML_INFRASTRUCTURE_CONNECTOR_H_ */

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

#include <fml/infrastructure/ComRoute.h>

#include <list>


namespace sep
{


class InteractionPart;
class Port;

class Connector final :
		public ObjectElement,
		public ComProtocol,
		AVM_INJECT_STATIC_NULL_REFERENCE( Connector ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Connector )
{

	AVM_DECLARE_CLONABLE_CLASS( Connector )

public:
	/**
	 * TYPEDEF
	 */
	typedef std::list< ComRoute > CollectionOfComRoute_t;

protected:
	/**
	 * ATTRIBUTES
	 */
	CollectionOfComRoute_t  mComRoutes;


protected:
	/**
	 * CONSTRUCTOR
	 * for null reference
	 */
	Connector()
	: ObjectElement( CLASS_KIND_T( Connector ), nullptr),
	ComProtocol( PROTOCOL_UNDEFINED_KIND ),
	mComRoutes( )
	{
		//!! NOTHING
	}


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Connector(const InteractionPart * anInteractionPart);

	/**
	 * DESTRUCTOR
	 */
	virtual ~Connector()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	static Connector & nullref()
	{
		static Connector _NULL_;
		_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );
		_NULL_.setAllNameID( "$null<connector>" , "$null<connector>" );

		return( _NULL_ );
	}


	/**
	 * GETTER - SETTER
	 * mComRoutes
	 */
	ComRoute & appendComRoute(const Modifier & aModifier)
	{
		return mComRoutes.emplace_back(const_cast< Connector * >(this), aModifier);
	}

	ComRoute & appendComRoute(Port * aPort, const Modifier & aModifier)
	{
		ComRoute &  newRoute =
				mComRoutes.emplace_back(const_cast< Connector * >(this), aModifier);

		newRoute.appendComPoint(aPort);

		return( newRoute );
	}

	inline const CollectionOfComRoute_t & getComRoutes() const
	{
		return( mComRoutes );
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const override;


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

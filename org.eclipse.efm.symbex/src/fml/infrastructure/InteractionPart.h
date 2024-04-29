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

#ifndef FML_INFRASTRUCTURE_INTERACTIONPART_H_
#define FML_INFRASTRUCTURE_INTERACTIONPART_H_

#include <fml/common/ObjectClassifier.h>

#include <fml/infrastructure/ComProtocol.h>

#include <collection/BFContainer.h>

#include <fml/infrastructure/Connector.h>

#include <list>

namespace sep
{


class Machine;


class InteractionPart :
		public ObjectClassifier,
		public ComProtocol,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( InteractionPart )
{

	AVM_DECLARE_CLONABLE_CLASS( InteractionPart )


public:
	/**
	 * TYPEDEF
	 */
	typedef std::list< Connector > CollectionOfConnector_t;


protected:
	/**
	 * ATTRIBUTES
	 */
	CollectionOfConnector_t mConnectors;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InteractionPart(Machine * aContainer, const std::string & aNameID = "com");

	/**
	 * DESTRUCTOR
	 */
	virtual ~InteractionPart()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mConnectorsOLD
	 */
	inline const CollectionOfConnector_t & getConnectors() const
	{
		return( mConnectors );
	}

	inline bool hasConnector() const
	{
		return( not mConnectors.empty() );
	}

	inline Connector & appendConnector(
			PROTOCOL_KIND aProtocol = PROTOCOL_UNDEFINED_KIND)
	{
		Connector & newConnector =  mConnectors.emplace_back( this );

		newConnector.setProtocol(aProtocol);

		return( newConnector );
	}

	inline bool empty() const
	{
		return( mConnectors.empty() );
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const override;

};


}

#endif /* FML_INFRASTRUCTURE_INTERACTIONPART_H_ */

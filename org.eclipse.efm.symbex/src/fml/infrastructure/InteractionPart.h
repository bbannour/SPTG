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
	typedef TableOfBF_T< Connector >  TableOfConnector;

	typedef TableOfConnector::raw_iterator        connector_iterator;
	typedef TableOfConnector::const_raw_iterator  const_connector_iterator;


protected:
	/**
	 * ATTRIBUTES
	 */
	TableOfConnector mConnectors;


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
	 * mConnectors
	 */
	inline const TableOfConnector & getConnectors() const
	{
		return( mConnectors );
	}

	inline bool hasConnector() const
	{
		return( mConnectors.empty() );
	}

	inline void appendConnector(const BF & aConnector)
	{
		mConnectors.append( aConnector );
	}

	inline void saveConnector(Connector * aConnector)
	{
		mConnectors.append( BF(aConnector) );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_connector_iterator connector_begin() const
	{
		return( mConnectors.begin() );
	}

	inline const_connector_iterator connector_end() const
	{
		return( mConnectors.end() );
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const;

};


}

#endif /* FML_INFRASTRUCTURE_INTERACTIONPART_H_ */

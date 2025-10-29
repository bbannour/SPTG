/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 oct. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef COMROUTE_H_
#define COMROUTE_H_

#include <fml/common/ObjectElement.h>
#include <fml/infrastructure/ComProtocol.h>

#include <fml/infrastructure/ComPoint.h>
#include <fml/infrastructure/Port.h>

#include <fml/lib/AvmLang.h>

#include <list>


namespace sep
{

class Connector;
class Modifier;


class ComRoute final :
		public ObjectElement,
		public ComProtocol,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ComRoute )
{

	AVM_DECLARE_CLONABLE_CLASS( ComRoute )

public:
	/**
	 * TYPEDEF
	 */
	typedef std::list< ComPoint > CollectionOfComComPoint_t;


protected:
	/**
	 * ATTRIBUTES
	 */
	CollectionOfComComPoint_t mComPoints;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ComRoute(Connector * aContainer,
			const Modifier & aModifier = Modifier::PROPERTY_INOUT_DIRECTION);

	/**
	 * DESTRUCTOR
	 */
	virtual ~ComRoute()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mComPoints
	 */
	inline const CollectionOfComComPoint_t & getComPoints() const
	{
		return( mComPoints );
	}


	ComPoint & appendComPoint()
	{
		return( mComPoints.emplace_back() );
	}

	ComPoint & appendComPoint(Machine * aMachine, Port * aPort)
	{
		return mComPoints.emplace_back(aMachine, aPort);
	}

	ComPoint & appendComPoint(
			Machine * aMachine, const BF & aPortQualifiedNameID)
	{
		return mComPoints.emplace_back(aMachine, aPortQualifiedNameID);
	}

	ComPoint & appendComPoint(Port * aPort)
	{
		return mComPoints.emplace_back(aPort->getContainerMachine(), aPort);
	}

	ComPoint & appendAllComPoint(Machine * aMachine)
	{
		if( getModifier().isDirectionUndefined() )
		{
			getwModifier().setDirectionKind(
					sep::Modifier::DIRECTION_INOUT_KIND );
		}

		return mComPoints.emplace_back(aMachine, XLIA_SYNTAX::ID_ALL);;
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const override;

};


} /* namespace sep */

#endif /* COMROUTE_H_ */

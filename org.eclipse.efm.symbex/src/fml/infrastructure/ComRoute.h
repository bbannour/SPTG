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

#include <collection/BFContainer.h>

#include <fml/infrastructure/ComPoint.h>
#include <fml/infrastructure/Port.h>


namespace sep
{

class Connector;
class Modifier;


class ComRoute :
		public ObjectElement,
		public ComProtocol,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ComRoute )
{

	AVM_DECLARE_CLONABLE_CLASS( ComRoute )


protected:
	/**
	 * ATTRIBUTES
	 */
	BFList mComPoints;


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
	inline const BFList & getComPoints() const
	{
		return( mComPoints );
	}

	inline void appendComPoint(const BF & aComPoint)
	{
		mComPoints.append( aComPoint );
	}

	inline void saveComPoint(ComPoint * aComPoint)
	{
		mComPoints.append( BF(aComPoint) );
	}

	void setComPoint(ComPoint * aComPoint,
			Modifier::DIRECTION_KIND ioDirection);


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const;

};


} /* namespace sep */

#endif /* COMROUTE_H_ */

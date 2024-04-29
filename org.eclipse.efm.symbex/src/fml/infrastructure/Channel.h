/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef CHANNEL_H_
#define CHANNEL_H_

#include <fml/common/PropertyElement.h>

#include <fml/infrastructure/ComProtocol.h>


namespace sep
{

class BF;
class Machine;
class Modifier;
class ObjectElement;
class PropertyPart;


class Channel :
		public PropertyElement,
		public ComProtocol,
		AVM_INJECT_STATIC_NULL_REFERENCE( Channel ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Channel )
{

	AVM_DECLARE_CLONABLE_CLASS( Channel )


protected:
	/**
	 * ATTRIBUTES
	 */
	PropertyPart * mParameterPart;

public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Channel(const PropertyPart & aPropertyPart, const std::string & aNameID,
			const Modifier & aModifier = Modifier::PROPERTY_INOUT_DIRECTION);

	/**
	 * CONSTRUCTOR
	 * Null
	 */
	Channel(const std::string & aNameID, const Modifier & aModifier)
	: PropertyElement(CLASS_KIND_T( Channel ), nullptr, aModifier, aNameID),
	ComProtocol( PROTOCOL_UNDEFINED_KIND , IComPoint::IO_UNDEFINED_NATURE),
	mParameterPart( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Channel()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static Channel & nullref()
	{
		static Channel _NULL_("$null<Channel>",
				Modifier::OBJECT_NULL_MODIFIER);
		_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );

		return( _NULL_ );
	}


	/**
	 * GETTER
	 * the container
	 */
	virtual Machine * getContainerMachine() const override;


	/**
	 * GETTER - SETTER
	 * mParameterPart
	 */
	PropertyPart & getParameterPart() const;


	/**
	 * GETTER - SETTER
	 * mParameterPart
	 * Signals
	 */
	void appendSignal(const Modifier & aModifier, const BF & aSignal);

	BF getSignal(Modifier::DIRECTION_KIND ioDirection, const BF & aSignal) const;


	/**
	 * Serialization
	 */
	void strHeader(OutStream & out) const override
	{
		out << str_indent( this );
	}

	void toStream(OutStream & out) const override;

};


} /* namespace sep */

#endif /* CHANNEL_H_ */

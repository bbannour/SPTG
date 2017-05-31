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

#ifndef PORT_H_
#define PORT_H_

#include <fml/common/PropertyElement.h>

#include <fml/lib/IComPoint.h>

#include <common/BF.h>

#include <fml/infrastructure/Variable.h>


namespace sep
{


class Channel;
class Machine;
class Modifier;
class ObjectElement;
class PropertyPart;


/**
 * TYPEDEF
 */
class Port;

typedef Port  Signal;



class Port :
		public PropertyElement,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Port )
{

	AVM_DECLARE_CLONABLE_CLASS( Port )


protected:
	/**
	 * ATTRIBUTES
	 */
	BF mModel;

	IComPoint::ENUM_IO_NATURE mComPointNature;

	bool mComposite;

	PropertyPart * mContents;

	Channel * mRoutingChannel;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Port(const PropertyPart & aPropertyPart,
			const std::string & aNameID, IComPoint::ENUM_IO_NATURE aNature,
			const Modifier & aModifier = Modifier::PROPERTY_INOUT_DIRECTION);

	Port(Channel * aChannel,
			const Modifier & aModifier, const BF & aPortPattern);

	/**
	 * DESTRUCTOR
	 */
	virtual ~Port()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * the container
	 */
	virtual Machine * getContainerMachine();


	/**
	 * GETTER - SETTER
	 * mModel
	 */
	inline Signal * getSignalModel() const
	{
		return( mModel.to_ptr< Port >() );
	}

	inline bool hasSignalModel() const
	{
		return( mModel.is< Port >() );
	}


	/**
	 * mComPointNature
	 */
	inline IComPoint::ENUM_IO_NATURE getComPointNature() const
	{
		return( mComPointNature );
	}

	inline bool isSignal() const
	{
		return( mComPointNature == IComPoint::IO_SIGNAL_NATURE );
	}


	/**
	 * isComposite
	 */
	inline bool isComposite() const
	{
		return( mComposite );
	}

	inline bool isBasic() const
	{
		return( not mComposite );
	}


	/**
	 * GETTER - SETTER
	 * mContents
	 */
	inline PropertyPart * getContents() const
	{
		return( mContents );
	}

	bool hasContents() const;

	inline void setContents(PropertyPart * aContents)
	{
		mContents = aContents;
	}


	/**
	 * GETTER - SETTER
	 * mParameters
	 */
	const TableOfVariable & getParameters() const;

	avm_size_t getParametersCount() const;

	avm_offset_t getParameterOffset(const std::string & label) const;

	void appendParameter(const BF & aParam);

	void saveParameter(Variable * aParam);


	/**
	 * GETTER - SETTER
	 * mRoutingChannel
	 */
	inline Channel * getRoutingChannel() const
	{
		return( mRoutingChannel );
	}

	inline bool hasRoutingChannel() const
	{
		return( mRoutingChannel != NULL );
	}

	inline void setRoutingChannel(Channel * aRoutingChannel)
	{
		mRoutingChannel = aRoutingChannel;
	}


	/**
	 * Serialization
	 */
	void strHeader(OutStream & out) const
	{
		out << str_indent( this );
	}

	void toStream(OutStream & out) const;

};


}

#endif /* PORT_H_ */

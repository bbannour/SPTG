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
		AVM_INJECT_STATIC_NULL_REFERENCE( Port ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Port )
{

	AVM_DECLARE_CLONABLE_CLASS( Port )

	AVM_TYPEDEF_TABLE_CLASS( Port )

protected:
	/**
	 * ATTRIBUTES
	 */
	BF mModel;

	IComPoint::ENUM_IO_NATURE mComPointNature;

	bool mComposite;

	PropertyPart * mParameterPart;

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
	 * CONSTRUCTOR
	 * Binding
	 */
	Port(Machine * aContainer,
			const std::string & aNameID, IComPoint::ENUM_IO_NATURE aNature,
			const Modifier & aModifier = Modifier::PROPERTY_INOUT_DIRECTION);

	/**
	 * CONSTRUCTOR
	 * Null
	 */
	Port(const std::string & aNameID, const Modifier & aModifier)
	: PropertyElement(CLASS_KIND_T( Port ), nullptr, aModifier , aNameID),
	mModel( ),
	mComPointNature( IComPoint::IO_UNDEFINED_NATURE ),

	mComposite( false ),

	mParameterPart( nullptr ),
	mRoutingChannel( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Port()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static Port & nullref()
	{
		static Port _NULL_("$null<Port>", Modifier::OBJECT_NULL_MODIFIER);
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
	 * mModel
	 */
	inline const Signal & getSignalModel() const
	{
		return( mModel.to< Signal >() );
	}

	inline bool hasSignalModel() const
	{
		return( mModel.is< Signal >() );
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
	 * mParameterPart
	 */
	PropertyPart & getParameterPart() const;


	/**
	 * GETTER - SETTER
	 * mParameters
	 */
	const TableOfVariable & getParameters() const;

	std::size_t getParametersCount() const;

	avm_offset_t getParameterOffset(const std::string & label) const;

	void appendParameter(const BF & aParam);

	void saveParameter(Variable * aParam);

	void setParameters(const TableOfVariable & paramVars);

	// Raw parameter
	void appendParameter(const TypeSpecifier& aType,
			const std::string paramNameID = "",
			const BF & defaultValueL = BF::REF_NULL);


	// Signature Comparison
	bool sameSignature(const Port & aPort) const;

	inline bool isConnectablebleWith(const Port & aPort) const
	{
		return( sameSignature(aPort) );
	}


	/**
	 * GETTER - SETTER
	 * mRoutingChannel
	 */
	inline const Channel & getRoutingChannel() const
	{
		return( * mRoutingChannel );
	}

	inline bool hasRoutingChannel() const
	{
		return( mRoutingChannel != nullptr );
	}

	inline void setRoutingChannel(Channel * aRoutingChannel)
	{
		mRoutingChannel = aRoutingChannel;
	}


	/**
	 * Serialization
	 */
	virtual void strHeader(OutStream & out) const override
	{
		out << str_indent( this );
	}

	virtual void toStream(OutStream & out) const override;

};


}

#endif /* PORT_H_ */

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

#include "Channel.h"

#include <util/avm_assert.h>

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/PropertyPart.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
Channel::Channel(const PropertyPart & aPropertyPart,
		const std::string & aNameID, const Modifier & aModifier)
: PropertyElement(CLASS_KIND_T( Channel ),
		aPropertyPart.getContainer(), aModifier, aNameID),
ComProtocol( PROTOCOL_UNDEFINED_KIND , IComPoint::IO_CHANNEL_NATURE ),
mContents( new PropertyPart(this, "contents") )
{
	//!! NOTHING
}



/**
 * GETTER
 * the container
 */
Machine * Channel::getContainerMachine() const
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( getContainer()->is< Machine >() )
			<< "Invalid << Channel Container >> Type <"
			<< getContainer()->classKindName() << "> Cast !!!"
			<< SEND_EXIT;

	return( getContainer()->to< Machine >() );
}


/**
 * GETTER
 * mContents
 */
bool Channel::hasContents() const
{
	return( (mContents != NULL) && mContents->nonempty() );
}

/**
 * GETTER - SETTER
 * mContents
 * Signals
 */
void Channel::appendSignal(const Modifier & aModifier, const BF & aSignal)
{
	mContents->appendSignal( BF( new Signal(this, aModifier, aSignal) ) );
}

BF Channel::getSignal(Modifier::DIRECTION_KIND ioDirection, const BF & aSignal)
{
	PropertyPart::TableOfSignal::const_raw_iterator itSignal =
			mContents->getSignals().begin();
	PropertyPart::TableOfSignal::const_raw_iterator endSignal =
			mContents->getSignals().end();
	for( ; itSignal != endSignal ; ++itSignal )
	{
		if( (aSignal == (itSignal)->getSignalModel())
			&& (itSignal)->getModifier().isDirectionKind(ioDirection) )
		{
			return( *itSignal );
		}
	}

	return( BF::REF_NULL );
}


/**
 * Serialization
 */
void Channel::toStream(OutStream & out) const
{
	out << TAB << getModifier().toString(Modifier::DISABLE_DIRECTION_FIELD)
		<< "channel";

	toStreamProtocolCast( out , false );

	if( not getModifier().isDirectionInout() )
	{
		out << " " << getModifier().strDirection();
	}

	out << " " << getNameID() << " {" << EOL;

	if( hasContents() )
	{
		getContents()->toStream(out);
	}

	out << TAB << "}" << EOL_FLUSH;
}


} /* namespace sep */

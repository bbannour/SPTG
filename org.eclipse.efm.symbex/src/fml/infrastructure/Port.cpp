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

#include "Port.h"

#include <fml/infrastructure/Channel.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/PropertyPart.h>

#include <fml/type/TypeManager.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
Port::Port(const PropertyPart & aPropertyPart, const std::string & aNameID,
		IComPoint::ENUM_IO_NATURE aNature, const Modifier & aModifier)
: PropertyElement( CLASS_KIND_T( Port ),
		aPropertyPart.getContainer() , aModifier , aNameID ),
mModel( ),
mComPointNature( aNature ),
mComposite( false ),

mContents( new PropertyPart(this, "contents") ),

mRoutingChannel( NULL )
{
	//!! NOTHING
}


Port::Port(Channel * aChannel,
		const Modifier & aModifier, const BF & portPattern)
: PropertyElement(CLASS_KIND_T( Port ), aChannel, portPattern.to_ref< Port >()),
mModel( portPattern ),
mComPointNature( portPattern.to_ptr< Port >()->mComPointNature ),
mComposite( false ),

mContents( new PropertyPart(this, "contents") ),

mRoutingChannel( aChannel )
{
	getwModifier().override_ifdef( aModifier );
}


/**
 * GETTER
 * mContents
 */
bool Port::hasContents() const
{
	return( (mContents != NULL) && mContents->nonempty() );
}


/**
 * GETTER - SETTER
 * mParameters
 */
const TableOfVariable & Port::getParameters() const
{
	return( mContents->getVariables() );
}

avm_size_t Port::getParametersCount() const
{
	return( mContents->getVariables().size() );
}

avm_offset_t Port::getParameterOffset(const std::string & label) const
{
	return( mContents->getVariables().getOffsetByNameID(label) );
}

void Port::appendParameter(const BF & aParam)
{
	mContents->appendVariable( aParam );
}

void Port::saveParameter(Variable * aParam)
{
	mContents->saveOwnedVariable( aParam );
}


/**
 * GETTER
 * the container
 */
Machine * Port::getContainerMachine()
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( getContainer()->is< Machine >() )
			<< "Invalid << Port Container >> Type <"
			<< getContainer()->classKindName() << "> Cast !!!"
			<< SEND_EXIT;

	return( getContainer()->to< Machine >() );
}


/**
 * Serialization
 */
void Port::toStream(OutStream & out) const
{
	out << TAB << getModifier().toString()
		<< IComPoint::str_nature( getComPointNature() );

	if( hasSignalModel() )
	{
		out << "< " << getSignalModel()->getNameID() << " >";
	}

	out << " " << getNameID();

	if( mContents->hasVariable() )
	{
		TableOfVariable::const_raw_iterator it =
				mContents->getVariables().begin();
		TableOfVariable::const_raw_iterator endIt =
				mContents->getVariables().end();

		out << "(";
		for( std::string sep = "" ; it != endIt ; ++it )
		{
			out << sep; if( sep.empty() ) { sep = ", "; }

			if( (it)->getModifier().hasNatureParameterBind() )
			{
				out << "#bind " << (it)->strValue();
			}
			else if( (it)->getModifier().hasNatureParameter() )
			{
				out << (it)->strTypeSpecifier();

				if( not (it)->getNameID().empty() )
				{
					out << " " << (it)->getNameID();

					if( (it)->hasValue() )
					{
						out << " = " << (it)->strValue();
					}
				}
				else if( (it)->hasValue() )
				{
					out << " " << (it)->strValue();
				}
			}
			else
			{
				out << str_header( *it );
			}
		}
		out << ")";
	}

	out << ";" << EOL_FLUSH;
}


}

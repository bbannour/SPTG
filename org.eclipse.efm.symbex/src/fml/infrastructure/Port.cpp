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

#include <fml/expression/ExpressionTypeChecker.h>

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

mParameterPart( new PropertyPart(this, "contents") ),

mRoutingChannel( nullptr )
{
	//!! NOTHING
}


Port::Port(Channel * aChannel,
		const Modifier & aModifier, const BF & portPattern)
: PropertyElement(CLASS_KIND_T( Port ), aChannel, portPattern.to< Port >()),
mModel( portPattern ),
mComPointNature( portPattern.to< Port >().mComPointNature ),
mComposite( false ),

mParameterPart( new PropertyPart(this, "contents") ),

mRoutingChannel( aChannel )
{
	getwModifier().override_ifdef( aModifier );
}


/**
 * CONSTRUCTOR
 * Binding
 */
Port::Port(Machine * aContainer, const std::string & aNameID,
		IComPoint::ENUM_IO_NATURE aNature, const Modifier & aModifier)
: PropertyElement( CLASS_KIND_T( Port ), aContainer , aModifier , aNameID ),
mModel( ),
mComPointNature( aNature ),
mComposite( false ),

mParameterPart( new PropertyPart(this, "contents") ),

mRoutingChannel( nullptr )
{
	//!! NOTHING
}


/**
 * GETTER
 * mParameterPart
 */
PropertyPart & Port::getParameterPart() const
{
	return( *mParameterPart );
}


/**
 * GETTER - SETTER
 * mParameters
 */
const TableOfVariable & Port::getParameters() const
{
	return( mParameterPart->getVariables() );
}

std::size_t Port::getParametersCount() const
{
	return( mParameterPart->getVariables().size() );
}

avm_offset_t Port::getParameterOffset(const std::string & label) const
{
	return( mParameterPart->getVariables().getOffsetByNameID(label) );
}

void Port::appendParameter(const BF & aParam)
{
	mParameterPart->appendVariable( aParam );
}

void Port::saveParameter(Variable * aParam)
{
	mParameterPart->saveOwnedVariable( aParam );
}

void Port::setParameters(const TableOfVariable & paramVars)
{
	mParameterPart->appendVariable(paramVars);
}

// Raw parameter
void Port::appendParameter(const TypeSpecifier& aType,
		const std::string paramNameID, const BF & defaultValue)
{
	saveParameter( new Variable(this,
			Modifier::PROPERTY_PARAMETER_MODIFIER,
			aType, paramNameID, defaultValue) );
}

// Signature Comparison
bool Port::sameSignature(const Port & aPort) const
{
	if( getParametersCount() != aPort.getParametersCount() ) {
		return false;
	}
	else if( mParameterPart->hasVariable() )
	{
		TableOfVariable::const_raw_iterator it =
				mParameterPart->getVariables().begin();
		TableOfVariable::const_raw_iterator endIt =
				mParameterPart->getVariables().end();

		TableOfVariable::const_raw_iterator itOther =
				aPort.mParameterPart->getVariables().begin();

		for( ; it != endIt ; ++it , ++itOther )
		{
				if( not ExpressionTypeChecker::isTyped
					(it->getTypeSpecifier(), itOther->getTypeSpecifier()) )
				{
					return false;
				}
		}
	}

	return true;
}


/**
 * GETTER
 * the container
 */
Machine * Port::getContainerMachine() const
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( isContainerMachine() )
			<< "Invalid << Port Container >> Type <"
			<< getContainer()->classKindName() << "> Cast !!!"
			<< SEND_EXIT;

	return( getContainer()->to_ptr< Machine >() );
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
		out << "< " << getSignalModel().getNameID() << " >";
	}

	out << " " << getNameID();

	if( hasReallyUnrestrictedName() )
	{
		out << " \"" << getUnrestrictedName() << "\"";
	}

	if( mParameterPart->hasVariable() )
	{
		TableOfVariable::const_raw_iterator it =
				mParameterPart->getVariables().begin();
		TableOfVariable::const_raw_iterator endIt =
				mParameterPart->getVariables().end();

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

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "UniFormIdentifier.h"

#include <common/NamedElement.h>

#include <fml/expression/ExpressionConstructor.h>
#include <fml/builtin/Identifier.h>

#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableForm.h>

#include <fml/runtime/RuntimeID.h>

#include <fml/type/BaseTypeSpecifier.h>


namespace sep
{


BF UniFormIdentifier::ANONYM_LOCATION( new Identifier("") );


std::string UniFormIdentifier::SEPARATOR_ID       = ".";

std::string UniFormIdentifier::SEPARATOR_LOCATION = ":";

std::string UniFormIdentifier::SEPARATOR_LOCATOR  = FQN_ID_ROOT_SEPARATOR;


/**
 * BUILD FROM QUALIFIED NAME ID
 */
void UniFormIdentifier::build(const std::string & aQualifiedNameID)
{
	ListOfString strList;

	std::string::size_type sepPos =
			aQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);
	if( sepPos != std::string::npos )
	{
		setLocator(aQualifiedNameID.substr(0, sepPos));
		NamedElement::collectNameID(strList, aQualifiedNameID, sepPos + 2);
	}
	else
	{
		NamedElement::collectNameID(strList, aQualifiedNameID);
	}

	ListOfString::iterator endIt = strList.end();
	for( ListOfString::iterator it = strList.begin() ; it != endIt ; ++it )
	{
		appendField( *it );
	}
}



/**
* LOADER
*/
void UniFormIdentifier::load()
{
	ANONYM_LOCATION = ExpressionConstructor::newIdentifier("");
}


/**
* DISPOSER
*/
void UniFormIdentifier::dispose()
{
	ANONYM_LOCATION.destroy();
}


/**
 * GETTER - SETTER
 */
void UniFormIdentifier::appendField(
		const std::string & aQualifiedNameID, avm_ufi_scheme_t scheme)
{
	ListOfField::append( UfiField(
			ExpressionConstructor::newIdentifier(aQualifiedNameID), scheme) );
	mScheme |= scheme;

	updateAllNameID();
}

void UniFormIdentifier::appendField(const BF & field)
{
	avm_ufi_scheme_t scheme = UFI_SCHEME_UNDEFINED;
	switch( field.classKind() )
	{
		case FORM_XFSP_VARIABLE_KIND:
		{
			scheme = UFI_SCHEME_VARIABLE;
			break;
		}

		case FORM_XFSP_MACHINE_KIND:
		case FORM_XFSP_SYSTEM_KIND:
		{
			scheme = UFI_SCHEME_MACHINE;
			break;
		}

//		case FORM_XFSP_INSTANCE_KIND:
//		{
//			scheme = UFI_SCHEME_INSTANCE;
//			break;
//		}

		case FORM_XFSP_PORT_KIND:
		{
			scheme = UFI_SCHEME_PORT;
			break;
		}
		case FORM_XFSP_BUFFER_KIND:
		{
			scheme = UFI_SCHEME_BUFFER;
			break;
		}
//		case FORM_XFSP_CONNECTOR_KIND:
//		{
//			scheme = UFI_SCHEME_CONNECTOR;
//			break;
//		}
		default:
		{
			scheme = UFI_SCHEME_FIELD;
			break;
		}
	}

	appendField( field , scheme );
}


void UniFormIdentifier::setLocator(const std::string & aLocationId)
{
	mLocator = ExpressionConstructor::newIdentifier(aLocationId);
}


/**
 * COMPARISON
 * OPERATOR
 */
int UniFormIdentifier::compare(const UniFormIdentifier & other) const
{
	if( this == &other )
	{
		return( 0 );
	}
	else
	{
		int  cmpResult = 0;

		UniFormIdentifier::const_iterator it = begin();
		UniFormIdentifier::const_iterator endIt = end();

		UniFormIdentifier::const_iterator itOther = other.begin();
		UniFormIdentifier::const_iterator endOther = other.end();

		for( ; (it != endIt) && (itOther != endOther) ; ++it , ++itOther )
		{
			cmpResult = (*it).compare( *itOther );
			if( cmpResult != 0  )
			{
				return( cmpResult );
			}
		}

		return( (it == endIt)
				? ( (itOther == endOther) ? 0 : 1)
				: ( (it == endIt) ? 1 : 0 ) );
	}
}

bool UniFormIdentifier::isEQ(const UniFormIdentifier & other) const
{
	UniFormIdentifier::const_iterator it = begin();
	UniFormIdentifier::const_iterator endIt = end();

	UniFormIdentifier::const_iterator itOther = other.begin();
	UniFormIdentifier::const_iterator endOther = other.end();

	for( ; (it != endIt) && (itOther != endOther) ; ++it , ++itOther )
	{
		if( not (*it).isEQ( *itOther ) )
		{
			return( false );
		}
	}

	return( (it == endIt) && (itOther == endOther) );
}



/**
 * Serialization
 */
void UniFormIdentifier::toStream(OutStream & out) const
{
	out << TAB << AVM_NO_INDENT;

	if( hasLocator() )
	{
		getLocator().toStream(out);
		out << SEPARATOR_LOCATOR;
	}

	toStreamLocation(out);

	AVM_DEBUG_REF_COUNTER(out);

	out << END_INDENT << EOL << std::flush;
}

std::string UniFormIdentifier::str() const
{
	StringOutStream oss( AVM_NO_INDENT );

	if( hasLocator() )
	{
		oss << getLocator().str();

		oss << SEPARATOR_LOCATOR;
	}


	ListOfField::const_iterator it = ListOfField::begin();
	ListOfField::const_iterator itEnd = ListOfField::end();
	if( (it != itEnd) && (*it).valid() )
	{
		if( (*it).is< BaseInstanceForm >() )
		{
AVM_IF_DEBUG_FLAG( QUALIFIED_NAME_ID )
			oss << (*it).to_ptr< BaseInstanceForm >()->getFullyQualifiedNameID();
AVM_ELSE
			oss << (*it).to_ptr< BaseInstanceForm >()->getNameID();
AVM_ENDIF_DEBUG_FLAG( QUALIFIED_NAME_ID )
		}

		else if( (*it).is< RuntimeID >())
		{
AVM_IF_DEBUG_FLAG( QUALIFIED_NAME_ID )
			oss << (*it).bfRID().getFullyQualifiedNameID();
AVM_ELSE
			oss << (*it).bfRID().strUniqId();
AVM_ENDIF_DEBUG_FLAG( QUALIFIED_NAME_ID )
		}

		else if( (*it).is< ObjectElement >() )
		{
			oss << "&"
				<< (*it).to_ptr< ObjectElement >()->getFullyQualifiedNameID();
		}

		else if( (*it).isIdentifier() )
		{
			oss << (*it).str();
		}

		else if( (*it).is< AvmCode >() )
		{
			oss << "${ ufi";
			for( ; it != itEnd ; ++it )
			{
				oss << " ";
				oss << (*it).str();
			}
			oss << " }";

			return( oss.str() );
		}

		else if( (*it).is< UniFormIdentifier >() )
		{
			oss << "${ ufi "
					<< (*it).to_ptr< UniFormIdentifier >()->str() << " }";
		}
		else
		{
			(*it).toStream( oss );
		}


		for( ++it ; it != itEnd ; ++it )
		{
			if( (*it).scheme == UFI_SCHEME_INDEX )
			{
				oss << "[";

				if( (*it).is< ObjectElement >() )
				{
					oss << "&" << (*it).to_ptr<
							ObjectElement >()->getFullyQualifiedNameID();
				}
				else if( (*it).is< BaseInstanceForm >() )
				{
					oss << "&" << (*it).to_ptr<
							BaseInstanceForm >()->getFullyQualifiedNameID();
				}
				else
				{
					oss << (*it).str();
				}

				oss << "]";
			}
			else if( (*it).scheme == UFI_SCHEME_PARAMETER )
			{
				oss << "(";

				if( (*it).is< ObjectElement >() )
				{
					oss << "&" << (*it).to_ptr<
							ObjectElement >()->getFullyQualifiedNameID();
				}
				else if( (*it).is< BaseInstanceForm >() )
				{
					oss << "&" << (*it).to_ptr<
							BaseInstanceForm >()->getFullyQualifiedNameID();
				}
				else
				{
					oss << (*it).str();
				}

				oss << ")";
			}

			else if( (*it).isIdentifier() )
			{
				oss << SEPARATOR_ID;
				oss << (*it).str();
			}

			else if( (*it).is< ObjectElement >() )
			{
				oss << SEPARATOR_LOCATION << "&" << (*it).to_ptr<
						ObjectElement >()->getFullyQualifiedNameID();
			}

			else if( (*it).is< BaseInstanceForm >() )
			{
				oss << SEPARATOR_LOCATION << "&" << (*it).to_ptr<
						BaseInstanceForm >()->getFullyQualifiedNameID();
			}

			else if( (*it).is< RuntimeID >() )
			{
				oss << SEPARATOR_LOCATION << "&"
					<< (*it).bfRID().getFullyQualifiedNameID();
			}
		}
	}

	return( oss.str() );
}


void UniFormIdentifier::toStreamLocator(OutStream & out) const
{
	if( hasLocator() )
	{
		out << AVM_NO_INDENT;
		getLocator().toStream(out);
		out << END_INDENT;
	}
}


void UniFormIdentifier::toStreamLocation(OutStream & out) const
{
	toStreamLocation(out, ListOfField::begin(), ListOfField::end());
}


void UniFormIdentifier::toStreamLocation(OutStream & out,
		ListOfField::const_iterator it, ListOfField::const_iterator itEnd) const
{
	if( (it != itEnd) && (*it).valid() )
	{
		if( (*it).is< BaseInstanceForm >() )
		{
AVM_IF_DEBUG_FLAG( QUALIFIED_NAME_ID )
			out << (*it).to_ptr< BaseInstanceForm >()->getFullyQualifiedNameID();
AVM_ELSE
			out << (*it).to_ptr< BaseInstanceForm >()->getNameID();
AVM_ENDIF_DEBUG_FLAG( QUALIFIED_NAME_ID )
		}

		else if( (*it).is< RuntimeID >())
		{
AVM_IF_DEBUG_FLAG( QUALIFIED_NAME_ID )
			out << (*it).bfRID().getFullyQualifiedNameID();
AVM_ELSE
			out << (*it).bfRID().strUniqId();
AVM_ENDIF_DEBUG_FLAG( QUALIFIED_NAME_ID )
		}

		else if( (*it).is< ObjectElement >() )
		{
			out << "&" << (*it).to_ptr<
					ObjectElement >()->getFullyQualifiedNameID();
		}

		else if( (*it).isIdentifier() )
		{
			(*it).toStream(out);
		}

		else if( (*it).is< AvmCode >() )
		{
			out << "${ ufi";
			for( ; it != itEnd ; ++it )
			{
				out << " ";
				(*it).toStream(out);
			}
			out << " }";

			return;
		}

		else if( (*it).is< UniFormIdentifier >() )
		{
			out << "${ ufi "
				<< (*it).to_ptr< UniFormIdentifier >()->str() << " }";
		}

		else
		{
			out << no_indent( *it );
		}


		for( ++it ; it != itEnd ; ++it )
		{
			if( (*it).scheme == UFI_SCHEME_INDEX )
			{
				out << "[";

				if( (*it).is< ObjectElement >() )
				{
					out << "&" << (*it).to_ptr<
							ObjectElement >()->getFullyQualifiedNameID();
				}
				else if( (*it).is< BaseInstanceForm >() )
				{
					out << "&" << (*it).to_ptr<
							BaseInstanceForm >()->getFullyQualifiedNameID();
				}
				else
				{
					(*it).toStream(out);
				}

				out << "]";
			}
			else if( (*it).scheme == UFI_SCHEME_PARAMETER )
			{
				out << "(";

				if( (*it).is< ObjectElement >() )
				{
					out << "&" << (*it).to_ptr<
							ObjectElement >()->getFullyQualifiedNameID();
				}
				else
				{
					(*it).toStream(out);
				}

				out << ")";
			}

			else if( (*it).isIdentifier() )
			{
				out << SEPARATOR_ID;
				(*it).toStream(out);
			}

			else if( (*it).is< ObjectElement >() )
			{
				out << SEPARATOR_LOCATION << "&" << (*it).to_ptr<
						ObjectElement >()->getFullyQualifiedNameID();
			}

			else if( (*it).is< BaseInstanceForm >() )
			{
				out << SEPARATOR_LOCATION << "&" << (*it).to_ptr<
						BaseInstanceForm >()->getFullyQualifiedNameID();
			}

			else if( (*it).is< RuntimeID >() )
			{
				out << SEPARATOR_LOCATION << "&"
					<< (*it).bfRID().getFullyQualifiedNameID();
			}
		}
	}
}


std::string UniFormIdentifier::toStringContainer() const
{
	StringOutStream oss(AVM_NO_INDENT);

	if( hasLocator() )
	{
		getLocator().toStream(oss);

		oss << SEPARATOR_LOCATOR;
	}

	if( ListOfField::nonempty() )
	{
		ListOfField::const_iterator it = ListOfField::begin();
		ListOfField::const_iterator itEnd = ListOfField::end();
		if( it != itEnd ) { --itEnd; }

		toStreamLocation(oss, it, itEnd);
	}

	return( oss.str() );
}


std::string UniFormIdentifier::toStringId() const
{
	if( ListOfField::nonempty() )
	{
		if( ListOfField::last().valid() )
		{
			if( ListOfField::last().is< BaseInstanceForm >() )
			{
				return( ListOfField::last().to_ptr< BaseInstanceForm >()->getNameID() );
			}

			else if( ListOfField::last().is< RuntimeID >() )
			{
				return( ListOfField::last().bfRID().getNameID() );
			}

			else if( ListOfField::last().is< ObjectElement >() )
			{
				return( ListOfField::last().to_ptr<
						ObjectElement >()->getNameID() );
			}

			else
			{
				return( ListOfField::last().str() );
			}
		}
		else
		{
			return( "ID<null>" );
		}
	}

	return( "" );
}


void UniFormIdentifier::toStreamAvm(OutStream & out) const
{
	out << TAB << AVM_NO_INDENT;

	if( hasLocator() )
	{
		getLocator().toStream(out);

		out << SEPARATOR_LOCATOR;
	}

	out << "${ ufi";

	ListOfField::const_iterator it = ListOfField::begin();
	ListOfField::const_iterator itEnd = ListOfField::end();
	for( ; it != itEnd ; ++it )
	{
		out << " ";

		// CASE OBJECT ELEMENT
		if( (*it).is< ObjectElement >() )
		{
			out << "&" << (*it).to_ptr< ObjectElement >()->getFullyQualifiedNameID();
		}

		// CASE INSTANCE ELEMENT
		else if( (*it).is< BaseInstanceForm >() )
		{
			out << "&" << (*it).to_ptr< BaseInstanceForm >()->getFullyQualifiedNameID();
		}

		// CASE RUNTIME_FORM_ID ELEMENT
		else if( (*it).is< RuntimeID >() )
		{
			out << "&" << (*it).bfRID().getFullyQualifiedNameID();
		}

		// CASE IDENTIFIER ELEMENT
		else if( (*it).isIdentifier() )
		{
			(*it).toStream(out);
		}

		else
		{
			(*it).toStream(out);
		}
	}

	out << END_INDENT << " } " << EOL_FLUSH;
}


}

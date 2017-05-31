/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Buffer.h"

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/PropertyPart.h>


namespace sep
{

std::string Buffer::ANONYM_ID = "_#buffer";


/**
 * CONSTRUCTOR
 * Default
 */
Buffer::Buffer(Machine * aContainer, const std::string & id,
		avm_type_specifier_kind_t aSpecifierKind, int aSize)
: PropertyElement(CLASS_KIND_T( Buffer ), aContainer, id),
mPolicySpecifierKind( aSpecifierKind ),
mSize( aSize ),
mMessage( )
{
	//!! NOTHING
}

Buffer::Buffer(const PropertyPart & aPropertyPart, const std::string & id,
		avm_type_specifier_kind_t aSpecifierKind, int aSize)
: PropertyElement(CLASS_KIND_T( Buffer ), aPropertyPart.getContainer(), id),
mPolicySpecifierKind( aSpecifierKind ),
mSize( aSize ),
mMessage( )
{
	//!! NOTHING
}


/**
 * Serialization
 */
std::string Buffer::str(avm_type_specifier_kind_t aSpecifierKind)
{
	std::ostringstream os;

	switch( aSpecifierKind )
	{
		case TYPE_FIFO_SPECIFIER:
		{
			os << "fifo";
			break;
		}
		case TYPE_LIFO_SPECIFIER:
		{
			os << "lifo";
			break;
		}

		case TYPE_MULTI_FIFO_SPECIFIER:
		{
			os << "multififo";
			break;
		}
		case TYPE_MULTI_LIFO_SPECIFIER:
		{
			os << "multilifo";
			break;
		}

		case TYPE_MULTISET_SPECIFIER:
		{
			os << "multiset";
			break;
		}

		case TYPE_SET_SPECIFIER:
		{
			os << "set";
			break;
		}

		case TYPE_RAM_SPECIFIER:
		{
			os << "ram";
			break;
		}

		case TYPE_UNDEFINED_SPECIFIER:
		{
			os << "undefined<buffer#kind>";
			break;
		}
		default:
		{
			os << "unknown<buffer#kind>";
			break;
		}
	}

	return( os.str() );
}


std::string Buffer::str(avm_type_specifier_kind_t aSpecifierKind, long aSize)
{
	std::ostringstream os;
	switch( aSpecifierKind )
	{
		case TYPE_FIFO_SPECIFIER:
		{
			os << "fifo<";
			break;
		}
		case TYPE_LIFO_SPECIFIER:
		{
			os << "lifo<";
			break;
		}

		case TYPE_MULTI_FIFO_SPECIFIER:
		{
			os << "multififo<";
			break;
		}
		case TYPE_MULTI_LIFO_SPECIFIER:
		{
			os << "multilifo<";
			break;
		}

		case TYPE_MULTISET_SPECIFIER:
		{
			os << "multiset<";
			break;
		}

		case TYPE_SET_SPECIFIER:
		{
			os << "set<";
			break;
		}

		case TYPE_RAM_SPECIFIER:
		{
			os << "ram";
			break;
		}

		case TYPE_UNDEFINED_SPECIFIER:
		{
			os << "undefined<buffer#kind , ";
			break;
		}
		default:
		{
			os << "unknown<buffer#kind , ";
			break;
		}
	}

	if( aSpecifierKind != TYPE_RAM_SPECIFIER )
	{
		if( aSize > 0 )
		{
			os << aSize << ">";
		}
		else
		{
			os << "*>";
		}
	}

	return( os.str() );
}


void Buffer::strMessage(OutStream & os) const
{
	if( mMessage.nonempty() )
	{
		BFList::const_iterator it = mMessage.begin();
		BFList::const_iterator endIt = mMessage.end();

		os << "[ " << (*it).str();
		for( ++it ; it != endIt ; ++it )
		{
			os << " , " << (*it).str();
		}
		os << " ]";
	}
}


void Buffer::strHeader(OutStream & os) const
{
	os << getModifier().toString() << "buffer "
			<< Buffer::str(mPolicySpecifierKind, mSize)
			<< " " << getNameID() ;

	strMessage( os );
}


void Buffer::toStream(OutStream & os) const
{
	os << TAB << getModifier().toString() << "buffer "
			<< Buffer::str(mPolicySpecifierKind, mSize)
			<< " " << getNameID();

	strMessage( os );

	os << ";" << EOL_FLUSH;
}


}

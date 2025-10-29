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
#include "BaseBufferQueue.h"

#include <fml/executable/InstanceOfMachine.h>

#include <fml/infrastructure/Buffer.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{

/**
 * Comparison
 * operator==
 */
bool BaseBufferQueue::equals(const BaseBufferForm & aBuffer) const
{
	if( this == &aBuffer )
	{
		return( true );
	}
	else if( aBuffer.is< BaseBufferQueue >()
		&& (this->size() == aBuffer.size()) )
	{
		ListOfMessage::const_iterator itOther =
				aBuffer.to< BaseBufferQueue >().beginMessages();
		for( const auto & itMessage : mMessages )
		{
			if( (itMessage != (*itOther))
				&& (not itMessage.equals( *itOther )) )
			{
				return( false );
			}
		}

		return( true );
	}

	return( false );
}


/**
 * Serialization
 */
void BaseBufferQueue::toStream(OutStream & out) const
{
	out << TAB << "buffer "
		<< Buffer::str(getInstance().getPolicySpecifierKind(), realCapacity())
		<< " " << getInstance().getFullyQualifiedNameID()
		<< " {";

	if( nonempty() )
	{
		AVM_DEBUG_REF_COUNTER(out);
		out << EOL_INCR_INDENT;

		for( const auto & itMessage : mMessages )
		{
AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
itMessage.toStream(out);
AVM_ELSE
			itMessage.toStreamValue(out);
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
		}
		out << DECR_INDENT_TAB << "}";
	}
	else
	{
		out << " }";
		AVM_DEBUG_REF_COUNTER(out);
	}
	out << EOL_FLUSH;
}


void BaseBufferQueue::toStreamValue(OutStream & out) const
{
	out << TAB << Buffer::str(getInstance().getPolicySpecifierKind())
//		<< "buffer "
//		<< Buffer::str(getInstance().getPolicySpecifierKind(), realCapacity())
		<< " {";

	if( nonempty() )
	{
		AVM_DEBUG_REF_COUNTER(out);
		out << EOL_INCR_INDENT;

		for( const auto & itMessage : mMessages )
		{
			itMessage.toStreamValue(out);
		}
		out << DECR_INDENT_TAB << "}";
	}
	else
	{
		out << " }";
		AVM_DEBUG_REF_COUNTER(out);
	}
	out << EOL_FLUSH;
}


void BaseBufferQueue::toFscn(OutStream & out,
		const RuntimeID & aRID, const BaseBufferForm * prevBuf) const
{
	StringOutStream oss( out.INDENT , out );

	if(prevBuf == nullptr)
	{
		if(size()==0)
		{
			oss << " ";
		}
		else
		{
			for( const auto & itMessage : mMessages )
			{
				itMessage.toFscn(oss);
			}
		}
	}
	else if(prevBuf->is< BaseBufferQueue >())
	{
		bool hasDifference = false;
		const BaseBufferQueue* prev = prevBuf->to_ptr< BaseBufferQueue >();
		hasDifference = (size()!=prev->size());
		if( not hasDifference )
		{
			ListOfMessage::const_iterator itPrev = prev->mMessages.begin();
			ListOfMessage::const_iterator itPrevEnd = prev->mMessages.end();
			ListOfMessage::const_iterator it = mMessages.begin();
			ListOfMessage::const_iterator itEnd = mMessages.end();
			for( ; (it != itEnd) && (itPrev != itPrevEnd) && (!hasDifference) ;
				++it , ++itPrev )
			{
				hasDifference = (it != itPrev);
			}
		}
		if(hasDifference)
		{
			if(size()==0)
			{
				oss << " ";
			}
			else
			{
				for( const auto & itMessage : mMessages )
				{
					itMessage.toFscn(oss);
				}
			}
		}
	}

	if( not oss.str().empty() )
	{
		std::string bufferkind;
		switch( classKind() )
		{
			case FORM_BUFFER_FIFO_KIND:
			{
				bufferkind = "FIFO";
				break;
			}
			case FORM_BUFFER_LIFO_KIND:
			{
				bufferkind = "LIFO";
				break;
			}
			case FORM_BUFFER_MULTISET_KIND:
			{
				bufferkind = "MULTISET";
				break;
			}
			case FORM_BUFFER_SET_KIND:
			{
				bufferkind = "SET";
				break;
			}
			default:
			{
				break;
			}
		}

		std::ostringstream osName;
		if( getInstance().hasRuntimeContainerRID() )
		{
			osName << getInstance().getRuntimeContainerRID().
							getInstance()->getNameID()
					<< "." << getInstance().getNameID();
		}
		else
		{
			osName << ":" << aRID.strPid() << ":" << getInstance().getNameID();
		}

		out << TAB << osName.str() << ":"
			<< "<" << bufferkind << ">#" << getInstance().getOffset() << "{";

		if(oss.str().compare(" ")==0)
		{
			out << " }" << EOL_FLUSH;
		}
		else
		{
			out << EOL << oss.str()
				<< TAB << "}" << EOL_FLUSH;
		}
	}
}



}

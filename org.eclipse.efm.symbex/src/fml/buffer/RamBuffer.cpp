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
#include "RamBuffer.h"

#include <fml/runtime/RuntimeID.h>


namespace sep
{


void RamBuffer::toStream(OutStream & os) const
{
	os << TAB << "buffer ram "
			<< ( hasInstance() ? getInstance()->getFullyQualifiedNameID() : "_")
			<< " {";
	AVM_DEBUG_REF_COUNTER(os);
	os << EOL_INCR_INDENT;

	if( nonempty() )
	{
		mMessage.toStream(os);
	}

	os << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}


void RamBuffer::toFscn(OutStream & os,
		const RuntimeID & aRID, const BaseBufferForm * prevBuf) const
{
	bool hasDifference = (prevBuf == NULL);

	if( (not hasDifference)
		&& (prevBuf->classKind() == classKind())
		&& prevBuf->is< RamBuffer >() )
	{
		const RamBuffer* prev = prevBuf->to< RamBuffer >();
		if(prev->mMessage!=mMessage)
		{
			hasDifference = true;
		}
	}

	StringOutStream oss;

	if( hasDifference )
	{
		if( nonempty() )
		{
			mMessage.toFscn(oss << AVM_STR_INDENT);
			oss << END_INDENT;
		}
		else
		{
			oss << " ";
		}

	}

	if( not oss.str().empty() )
	{
		std::string bufferkind;
		switch( classKind() )
		{
			case FORM_BUFFER_RAM_KIND:
			{
				bufferkind = "RAM";
				break;
			}

			default:
			{
				break;
			}
		}

		os << TAB << ":pid#" << aRID.getRid() << ":" << "<"
				<< bufferkind << ">#" << getInstance()->getOffset() << "{";

		if(oss.str().compare(" ")==0)
		{
			os << " }" << EOL_FLUSH;
		}
		else
		{
			os << oss.str() << " }" << EOL_FLUSH;
		}
	}
}


}

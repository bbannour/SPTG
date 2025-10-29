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


void RamBuffer::toStream(OutStream & out) const
{
	out << TAB << "buffer ram "
			<< getInstance().getFullyQualifiedNameID()
			<< " {";
	AVM_DEBUG_REF_COUNTER(out);
	out << EOL_INCR_INDENT;

	if( nonempty() )
	{
		mMessage.toStream(out);
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}


void RamBuffer::toStreamValue(OutStream & out) const
{
	out << TAB << "ram {";
	AVM_DEBUG_REF_COUNTER(out);
	out << EOL_INCR_INDENT;

	if( nonempty() )
	{
		mMessage.toStreamValue(out);
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}


void RamBuffer::toFscn(OutStream & out,
		const RuntimeID & aRID, const BaseBufferForm * prevBuf) const
{
	bool hasDifference = (prevBuf == nullptr);

	if( (not hasDifference)
		&& (prevBuf->classKind() == classKind())
		&& prevBuf->is< RamBuffer >() )
	{
		const RamBuffer* prev = prevBuf->to_ptr< RamBuffer >();
		if(prev->mMessage!=mMessage)
		{
			hasDifference = true;
		}
	}

	StringOutStream oss( out );

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

		out << TAB << ":pid#" << aRID.getRid() << ":" << "<"
			<< bufferkind << ">#" << getInstance().getOffset() << "{";

		if(oss.str().compare(" ")==0)
		{
			out << " }" << EOL_FLUSH;
		}
		else
		{
			out << oss.str() << " }" << EOL_FLUSH;
		}
	}
}


}

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
#include "BroadcastBuffer.h"

#include <fml/runtime/RuntimeID.h>


namespace sep
{


void BroadcastBuffer::toStream(OutStream & out) const
{
	out << TAB << "buffer broadcast "
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


void BroadcastBuffer::toStreamValue(OutStream & out) const
{
	out << TAB << "broadcast {";
	AVM_DEBUG_REF_COUNTER(out);
	out << EOL_INCR_INDENT;

	if( nonempty() )
	{
		mMessage.toStreamValue(out);
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}


void BroadcastBuffer::toFscn(OutStream & out,
		const RuntimeID & aRID, const BaseBufferForm * prevBuf) const
{
	if( nonempty() )
	{
		bool hasDifference = (prevBuf == nullptr);

		if( (not hasDifference)
			&& prevBuf->is< BroadcastBuffer >() )
		{
			const BroadcastBuffer * prev = prevBuf->to_ptr< BroadcastBuffer >();
			if(prev->mMessage!=mMessage)
			{
				hasDifference = true;
			}
		}

		if( hasDifference )
		{
			out << TAB << ":" << aRID.strPid() << ":" << "<BROADCAST>#"
					<< getInstance().getOffset() << "{" << EOL_INCR_INDENT;

			mMessage.toFscn(out);

			out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
		}
	}
}


}

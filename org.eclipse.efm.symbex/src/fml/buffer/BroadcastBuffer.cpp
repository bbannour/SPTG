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


void BroadcastBuffer::toStream(OutStream & os) const
{
	os << TAB << "buffer broadcast "
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


void BroadcastBuffer::toFscn(OutStream & os,
		const RuntimeID & aRID, const BaseBufferForm * prevBuf) const
{
	if( nonempty() )
	{
		bool hasDifference = (prevBuf == NULL);

		if( (not hasDifference)
			&& prevBuf->is< BroadcastBuffer >() )
		{
			const BroadcastBuffer * prev = prevBuf->to< BroadcastBuffer >();
			if(prev->mMessage!=mMessage)
			{
				hasDifference = true;
			}
		}

		if( hasDifference )
		{
			os << TAB << ":pid#" << aRID.getRid() << ":" << "<BROADCAST>#"
					<< getInstance()->getOffset() << "{" << EOL_INCR_INDENT;

			mMessage.toFscn(os);

			os << DECR_INDENT_TAB << "}" << EOL_FLUSH;
		}
	}
}


}

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 oct. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExecutionLocation.h"

#include <fml/runtime/RuntimeID.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION
////////////////////////////////////////////////////////////////////////////////

void ExecutionLocation::toStream(OutStream & os) const
{
	os << TAB << "execution#location {" << EOL;

	os << TAB2 << "rid = " << mRID.str() << ";" << EOL_INCR_INDENT;

	if( mCODE.valid() )
	{
		os << TAB << "@code{" << EOL_INCR_INDENT;
		mCODE.toStream(os);
		os << DECR_INDENT_TAB << "}" << EOL;

		if( itCode != endCode )
		{
			os << TAB << "@begin{" << EOL_INCR2_INDENT;
			(*itCode).toStream(os);
			os << DECR_INDENT_TAB << "}" << EOL;

			os << TAB << "begin = " << (*itCode).raw_address()  << ";" << EOL;
			os << TAB << "end   = " << (*endCode).raw_address() << ";" << EOL;
		}
	}

	os << DECR_INDENT_TAB <<  "}" << EOL_FLUSH;
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION
////////////////////////////////////////////////////////////////////////////////

void ExecutionLocationQueue::toStream(OutStream & os) const
{
	List< BF >::const_iterator it = mQueue.begin();
	List< BF >::const_iterator endIt = mQueue.end();
	for( ; it != endIt ; ++it )
	{
		(*it).toStream(os);
	}
}


}

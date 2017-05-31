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

#include "LocalRuntime.h"
#include <fml/expression/BuiltinArray.h>


namespace sep
{


/**
 * Serialization
 */
void LocalRuntimeElement::toStream(OutStream & os) const
{
	if( os.preferablyFQN() )
	{
		os << TAB << mProgram.getFullyQualifiedNameID();
		return;
	}

	os << TAB << "runtime" << mProgram.getFullyQualifiedNameID()
			<< " as program {";

	AVM_DEBUG_REF_COUNTER(os);
	os << EOL_FLUSH;

	if( mDataTable.nonempty() )
	{
		os << EOL;
		os << TAB << "data";
		mDataTable.AVM_DEBUG_REF_COUNTER(os);
		os << EOL;

		TableOfData::const_iterator it = mDataTable.begin();
		TableOfData::const_iterator itEnd = mDataTable.end();
		for( avm_size_t i = 0 ; it != itEnd ; ++it , ++i )
		{
			os << TAB2 << (*it).AVM_DEBUG_REF_COUNTER() << "${ := ";

//			os << mRID.getVariables().get(i)->getFullyQualifiedNameID();
			os << mProgram.getData().rawAt(i)->getNameID()
					<< str_indent( *it ) << " }" << EOL_FLUSH;
		}
	}

	os << TAB << "}" << EOL_FLUSH;
}


}

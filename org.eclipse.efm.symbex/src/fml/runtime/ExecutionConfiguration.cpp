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
#include "ExecutionConfiguration.h"


namespace sep
{


/**
 * Serialization
 */
std::string ExecutionConfiguration::str() const
{
	if( is< Operator >() )
	{
		return( OSS() << getRuntimeID().str()
				<< FQN_ID_ROOT_SEPARATOR << getOperator()->strOp() );
	}
	else
	{
		StringOutStream oss( AVM_STR_INDENT );

		toStream( oss << IGNORE_FIRST_TAB );

		return( oss.str() );
	}
}

void ExecutionConfiguration::toStream(OutStream & os) const
{
	std::string str4Program;

	os << TAB << "(:pid#" << getRuntimeID().getRid() << " ,"; // << " |= ";

	if( isWeakProgram() )
	{
		os << " " << toProgram()->getNameID();
	}
	else if( isAvmCode() )
	{
		toAvmCode()->toStreamPrefix( os << AVM_STR_INDENT );
		os << END_INDENT;
	}
	else
	{
		os << str_indent( getCode() );
	}

	AVM_DEBUG_REF_COUNTER(os);

	os << ")" << EOL_FLUSH;
}


}

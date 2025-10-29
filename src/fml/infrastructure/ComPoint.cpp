/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 juil. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ComPoint.h"

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>


namespace sep
{

/**
 * Serialization
 */
void ComPoint::toStream(OutStream & out) const
{
	if( mMachinePortQualifiedNameID.valid() )
	{
		if( mMachine != nullptr )
		{
//			out << mMachine->getFullyQualifiedNameID() << "->";
			out << mMachine->getNameID() << "->";
		}

		toStreamProtocolCast( out << mMachinePortQualifiedNameID.str() );
	}
	else if( mPort != nullptr )
	{
		if( (mMachine != nullptr) )
		{
			out << mMachine->getNameID()//getFullyQualifiedNameID()
				<< "->" << mPort->getNameID();
		}
		else
		{
			out << mPort->getNameID();//getFullyQualifiedNameID();
		}

		toStreamProtocolCast( out );
	}
	else
	{
		out << "ComPoint<null>";
	}
}


} /* namespace sep */

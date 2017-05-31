/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 oct. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include <fml/executable/ComRouteData.h>

#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/infrastructure/ComProtocol.h>
#include <fml/infrastructure/Port.h>


namespace sep
{


static void strPM(OutStream & os, PairMachinePort * mp)
{
//	if( (mp->first() == NULL) || mp->first()->isThis() ||
//			NamedElement::fqnStartsWith(mp->second()->getFullyQualifiedNameID(),
//					mp->first()->getFullyQualifiedNameID()) )
//	{
//		os << mp->second()->getFullyQualifiedNameID();
//	}
//	else
//	{
//		os << mp->first()->getFullyQualifiedNameID()
//				<< "->" << mp->second()->getNameID();
//	}

	if( mp != NULL )
	{
		os << ( (mp->first() != NULL) ?	mp->first()->getNameID() : "machine<null> " )
				<< "->"	<< ( (mp->second() != NULL) ?
						mp->second()->getNameID() : "port<null>" );
	}
	else
	{
		os << "(machine->port)<null>";
	}
}


/**
 * Serialization
 */
void ComRouteData::toStream(OutStream & out) const
{
	out << TAB << getModifier().strDirection();
	if( hasCast() )
	{
		out << "< " << ComProtocol::to_string( getCast() ) << " >";
	}

	if( getMachinePorts().singleton() )
	{
		out << " ";
		strPM(out, getMachinePorts().first());
		out << ";" << EOL_FLUSH;
	}
	else if( getMachinePorts().nonempty() )
	{
		out << " {" << EOL;
		VectorOfPairMachinePort::const_iterator it = getMachinePorts().begin();
		VectorOfPairMachinePort::const_iterator endIt = getMachinePorts().end();
		for( ; it != endIt ; ++it )
		{
			out << TAB2;
			strPM(out, (*it));
			out << ";" << EOL;
		}
		out << TAB << "}" << EOL_FLUSH;
	}
}



} /* namespace sep */

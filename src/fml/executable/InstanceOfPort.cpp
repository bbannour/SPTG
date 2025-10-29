/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "InstanceOfPort.h"

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/expression/BuiltinArray.h>

#include <fml/runtime/RuntimeID.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/TypeManager.h>

#include <fml/infrastructure/Port.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
InstanceOfPort::InstanceOfPort(BaseAvmProgram * aContainer,
		const PropertyElement & astPort, avm_offset_t anOffset,
		std::size_t aParameterCount, ENUM_IO_NATURE aNature)
: BaseInstanceForm( CLASS_KIND_T( InstanceOfPort ),
		aContainer, astPort, TypeManager::PORT, anOffset),
mRouteOffset( anOffset ),
mComPointNature( aNature ),

mParameters(aParameterCount),
mContents( ),

mRoutingChannel( nullptr ),

mInputRoutingData( ),
mOutputRoutingData( )
{
//	AVM_OS_TRACE << "port::new :> " << getFullyQualifiedNameID() << std::endl;
}


/**
 * Format a value w.r.t. its type
 */
void InstanceOfPort::formatStream(
		OutStream & out, const BF & bfValue) const
{
	if( bfValue.is< ArrayBF >() )
	{
		formatStream(out, bfValue.as< ArrayBF >());
	}
	else if( hasParameterType(0) )
	{
		getParameterType(0).formatStream(out, bfValue);
	}
	else
	{
		out << bfValue.str();
	}

}

void InstanceOfPort::formatStream(
		OutStream & out, const ArrayBF & arrayValue) const
{
	out << out.VALUE_PARAMS_CSS.BEGIN;

	if( hasParameterType(0) )
	{
		getParameterType(0).formatStream(out, arrayValue[0]);
	}
	else
	{
		out << arrayValue[0].str();
	}
	for( std::size_t offset = 1 ; offset < arrayValue.size() ; ++offset )
//	for( std::size_t offset = 1 ; offset < (arrayValue.size() - 1) ; ++offset )
	{
		out << out.VALUE_PARAMS_CSS.SEPARATOR;

		if( hasParameterType(offset) )
		{
			getParameterType(offset).formatStream(out, arrayValue[offset]);
		}
		else
		{
			out << arrayValue[offset].str();
		}
	}

	out << out.VALUE_PARAMS_CSS.END;
}

/**
 * Serialization
 */

void InstanceOfPort::strParameter(OutStream & out, const BF & aParameter) const
{
	if( aParameter.is< BaseTypeSpecifier >() )
	{
		out << aParameter.to< BaseTypeSpecifier >().strT();
	}
	else if( aParameter.is< InstanceOfData >() )
	{
		InstanceOfData * aVar = aParameter.to_ptr< InstanceOfData >();

		out << aVar->strHeaderId();
		if( aVar->hasValue() )
		{
			out << " = " << aVar->strValue();
		}
	}
	// #bind expression parameter
	else
	{
		out << "#bind " << aParameter.str();
	}
}

void InstanceOfPort::strParameter(OutStream & out) const
{
	if( hasParameter() )
	{
		ArrayOfBF::const_iterator it = getParameters().begin();
		ArrayOfBF::const_iterator endIt = getParameters().end();

		out << "[ ";
		strParameter(out, (*it));
		for( ++it ; it != endIt ; ++it )
		{
			out << " , ";
			strParameter(out, (*it));
		}
		out << " ]";
	}
}




void InstanceOfPort::strHeader(OutStream & out) const
{
	out << getModifier().toString() << strComPointNature()
		<< "< id:" << getOffset() << " , route:" << getRouteOffset()
		<< " > " << getFullyQualifiedNameID();

	strParameter(out);
}


std::string InstanceOfPort::strArg() const
{
	StringOutStream oss;

	oss << getFullyQualifiedNameID();// << " '" << getNameID() << "'";

	if( mRoutingChannel != nullptr )
	{
		oss << "< #via " << mRoutingChannel->getFullyQualifiedNameID() << " >";
	}

	return( oss.str() );
}


void InstanceOfPort::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	bool isEmpty = true;

	out << TAB << getModifier().toString() << strComPointNature()
		<< "< id:" << getOffset() << " , route:" << getRouteOffset()
		<< " > " << getFullyQualifiedNameID();

	AVM_DEBUG_REF_COUNTER(out);

AVM_IF_DEBUG_FLAG( COMPILING )
	out << " {" << EOL; isEmpty = false;

	if( hasAstElement() )
	{
		out << TAB2 << "//compiled = "
			<< getAstFullyQualifiedNameID() << ";" << EOL;
	}

	out << TAB2 << "//container = "
		<< (hasContainer() ? getContainer()->getFullyQualifiedNameID() : "nullptr")
		<< ";" << EOL;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	if( hasAliasTarget() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "target = "
			<< str_header( getAliasTarget()->as_ptr< InstanceOfPort >() )
			<< ";" << EOL;
	}

	if( hasCreatorContainerRID() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "rid#creator = " << getCreatorContainerRID().str()
			<< ";" << EOL;
	}

	if( hasRuntimeContainerRID() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "rid#container = " << getRuntimeContainerRID().str()
			<< ";" << EOL;
	}

	if( hasInputRoutingData() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "routing#input#data = "
			<< getInputRoutingData().str() << ";" << EOL;
	}

	if( hasOutputRoutingData() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "routing#output#data = "
			<< getOutputRoutingData().str() << ";" << EOL;
	}

//	os << TAB2 << "offset = " << getOffset() << ";" << EOL;

	if( hasMachinePath() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		out << TAB << "path#machine:" << EOL;
		ArrayOfInstanceOfMachine::const_iterator it = getMachinePath()->begin();
		ArrayOfInstanceOfMachine::const_iterator endIt = getMachinePath()->end();
		for( ; it != endIt ; ++it )
		{
			out << TAB2 << (*it)->getFullyQualifiedNameID() << EOL;
		}
	}

	if( hasParameter() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		out << TAB << "parameter:" << EOL;
		for( const auto & itParam : getParameters() )
		{
			if( itParam.is< BaseTypeSpecifier >() )
			{
				out << TAB2 << itParam.to< BaseTypeSpecifier >().strT()
					<< ";" << EOL;
			}
			else if( itParam.is< InstanceOfData >() )
			{
				InstanceOfData * aVar = itParam.to_ptr< InstanceOfData >();

				out << TAB2 << aVar->strHeaderId();
				if( aVar->hasValue() )
				{
					out << " = " << aVar->strValue();
				}
				out << ";" << EOL;
			}
			// #bind expression parameter
			else
			{
				out << TAB2 << "#bind " << itParam.str() << ";" << EOL;
			}
		}
	}

	if( hasContent() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		out << TAB << "contents:" << EOL;
		for( const auto & itSymbol : getContents() )
		{
			out << TAB2 << str_header( itSymbol ) << EOL;
		}
	}

	( isEmpty ? (out << ";") : (out << TAB << "}") ) << EOL_FLUSH;
}


void InstanceOfPort::toStream(OutStream & out,
		const ListOfInstanceOfPort & iePorts)
{
	for( const auto & itPort : iePorts )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , COMMUNICATION )
		out << TAB2 << str_header( itPort ) << EOL;
AVM_ELSE
		out << TAB2 << itPort->getFullyQualifiedNameID() << EOL;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , COMMUNICATION )
	}
}


}

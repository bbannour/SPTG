/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 déc. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Function.h"

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Variable.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
Function::Function(const PropertyPart & aPropertyPart, const std::string & aNameID)
: PropertyElement( CLASS_KIND_T( Function ), aPropertyPart.getContainer(), aNameID ),

mParameterPart( new PropertyPart(this , "signature") ),

mCode( )
{
	//!! NOTHING
}

Function::Function(ObjectElement * aContainer, const std::string & aNameID)
: PropertyElement( CLASS_KIND_T( Function ), aContainer, aNameID ),

mParameterPart( new PropertyPart(this , "signature") ),

mCode( )
{
	//!! NOTHING
}

/**
 * GETTER
 * Unique Null Reference
 */
Function & Function::nullref()
{
	static Function _NULL_(Machine::nullref_ptr(), "$null<Function>");

	_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );

	return( _NULL_ );
}


/**
 * GETTER - SETTER
 * mPropertyPart
 */
PropertyPart & Function::getParameterPart() const
{
	return( *mParameterPart );
}


/**
 * Serialization
 */
void Function::strParameters(OutStream & out, const std::string & sep) const
{
	BFVector::const_iterator itVarParam =
			getParameterPart().getVariableParameters().begin();
	BFVector::const_iterator endVarParam =
			getParameterPart().getVariableParameters().end();

	out << "(";
	if( (*itVarParam).is< Variable >() )
	{
		out << "$" << (*itVarParam).to< Variable >().getRuntimeOffset()
			<< ": ";
		(*itVarParam).to< Variable >().strParameter(out);
	}
	else
	{
		out << (*itVarParam).str();
	}
	for( ++itVarParam ; itVarParam != endVarParam ; ++itVarParam )
	{
		out << ", ";
		if( (*itVarParam).is< Variable >() )
		{
			out << "$" << (*itVarParam).to< Variable >().getRuntimeOffset()
				<< ": ";
			(*itVarParam).to< Variable >().strParameter(out);
		}
		else
		{
			out << (*itVarParam).str();
		}
	}
	out << ")";
}

void Function::strReturns(OutStream & out, const std::string & sep) const
{
	BFVector::const_iterator itVarReturn =
			getParameterPart().getVariableReturns().begin();
	BFVector::const_iterator endVarReturn =
			getParameterPart().getVariableReturns().end();

	out << "(";
	if( (*itVarReturn).is< Variable >() )
	{
		out << "$" << (*itVarReturn).to< Variable >().getRuntimeOffset()
			<< ": ";
		(*itVarReturn).to< Variable >().strReturn(out);
	}
	else
	{
		out << (*itVarReturn).str();
	}
	for( ++itVarReturn ; itVarReturn != endVarReturn ; ++itVarReturn )
	{
		out << ", ";
		if( (*itVarReturn).is< Variable >() )
		{
			out << "$" << (*itVarReturn).to< Variable >().getRuntimeOffset()
				<< ": ";
			(*itVarReturn).to< Variable >().strReturn(out);
		}
		else
		{
			out << (*itVarReturn).str();
		}
	}
	out << ")";
}


void Function::strHeader(OutStream & out) const
{
	out << getModifier().toString() << "fun ";

	out << getNameID();

	if( getParameterPart().hasVariableParameter() )
	{
		strParameters(out);
	}
	if( getParameterPart().hasVariableReturn() )
	{
		out << " --> ";

		strReturns(out);
	}
}


void Function::toStream(OutStream & out) const
{
	strHeader( out << TAB );

	if( mCode.valid() )
	{
		out << "{";
		mCode->toStreamRoutine( out << INCR_INDENT ) << DECR_INDENT_TAB;
		out << "}" << EOL_FLUSH;
	}
}



void Function::strInvokeParameters(
		OutStream & out, const std::string & sep) const
{
	BFVector::const_iterator it =
			getParameterPart().getVariableParameters().begin();
	BFVector::const_iterator endIt =
			getParameterPart().getVariableParameters().end();

	out << "(";
	AvmCode::toStream(out, *it);
	for( ++it ; it != endIt ; ++it )
	{
		out << ", ";
		AvmCode::toStream(out, *it);
	}
	out << ")";
}

void Function::strInvokeReturns(OutStream & out, const std::string & sep) const
{
	BFVector::const_iterator it = getParameterPart().getVariableReturns().begin();
	BFVector::const_iterator endIt = getParameterPart().getVariableReturns().end();

	out << "(";
	AvmCode::toStream(out, *it);
	for( ++it ; it != endIt ; ++it )
	{
		out << ", ";
		AvmCode::toStream(out, *it);
	}
	out << ")";
}


void Function::toStreamInvoke(OutStream & out, const std::string & sep) const
{
	out << TAB << getNameID() << AVM_NO_INDENT;

	if( getParameterPart().hasVariableParameter() )
	{
		strInvokeParameters(out, sep);
	}
	else
	{
		out << "()";
	}

	if( getParameterPart().hasVariableReturn() )
	{
		out << " --> ";
		strInvokeReturns(out, sep);
	}

	AVM_DEBUG_REF_COUNTER(out);

	out << END_INDENT << EOL_FLUSH;
}


} /* namespace sep */

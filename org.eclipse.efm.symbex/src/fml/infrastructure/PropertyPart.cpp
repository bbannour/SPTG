/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "PropertyPart.h"


namespace sep
{

/**
 * DISPATCH
 * mOwnedElements
 */
void PropertyPart::dispatchOwnedElement(const BF & anElement)
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anElement )
			<< "Executable Machine owned element !!!"
			<< SEND_EXIT;

	switch( anElement.classKind() )
	{
		// PROPERTY ELEMENT
		case FORM_XFSP_VARIABLE_KIND:
		{
			dispatchOwnedVariable( anElement );

			break;
		}

		case FORM_XFSP_DATATYPE_KIND:
		{
			mDataTypes.append( anElement );
			break;
		}

		case FORM_XFSP_BUFFER_KIND:
		{
			mBuffers.append( anElement );
			break;
		}

		case FORM_XFSP_CHANNEL_KIND:
		{
			mChannels.append( anElement );
			break;
		}

		case FORM_XFSP_PORT_KIND:
		{
			mPorts.append( anElement );
			break;
		}


		default:
		{ // TODO
			AVM_OS_FATAL_ERROR_EXIT
					<< "dispatchOwnedElement() unexpected object, typeinfo: "
					<< anElement.classKindInfo() << "\n\t<< "
					<< anElement.to_ptr< ObjectElement >()->strHeader()
					<< " >> !!!"
					<< SEND_EXIT;
			break;
		}
	}
}


/**
 * DISPATCH - SAVE
 * using Variable::Modifier
 * mVariables
 * mVariableParameters
 * mVariableReturns
 */
void PropertyPart::dispatchOwnedVariable(const BF & aVariable)
{
	mVariables.append( aVariable );

	const Modifier & aModifier =
			aVariable.to_ptr< Variable >()->getModifier();

	if( aModifier.hasNatureParameter() )
	{
		if( aModifier.isDirectionReturn() )
		{
			mVariableReturns.append( aVariable );
		}
		else //if( aModifier.hasDirectionOtheThanReturn() )
		{
			mVariableParameters.append( aVariable );
		}
	}
}


/**
 * Serialization
 */
void PropertyPart::strVariableParameters(OutStream & os,
		const std::string & begin, const std::string & end,
		const std::string & sep) const
{
	if( mVariableParameters.nonempty() )
	{
		os << begin;

		const_variable_iterator it = var_parameter_begin();
		const_variable_iterator endIt = var_parameter_end();

		(it)->strParameter(os);
		for( ++it ; it != endIt ; ++it )
		{
			(it)->strParameter( os << sep );
		}

		os << end;
	}
}

void PropertyPart::strVariableReturns(OutStream & os,
		const std::string & begin, const std::string & end,
		const std::string & sep) const
{
	if( mVariableReturns.nonempty() )
	{
		os << begin;

		const_variable_iterator it = var_return_begin();
		const_variable_iterator endIt = var_return_end();

		(it)->strReturn(os);
		for( ++it ; it != endIt ; ++it )
		{
			(it)->strReturn( os << sep );
		}

		os << end;
	}
}


void PropertyPart::toStream(OutStream & os) const
{
	os << TAB << "@" << getNameID() << ":" << EOL_INCR_INDENT;

	if( mOwnedElements.nonempty() )
	{
		mOwnedElements.toStream(os);
	}

//	if( mDataTypes.nonempty() )
//	{
//		mDataTypes.toStream(os);
//	}
//
//	if( mBuffers.nonempty() )
//	{
//		mBuffers.toStream(os);
//	}
//
//	if( mPorts.nonempty() )
//	{
//		mPorts.toStream(os);
//	}
//
//	if( mSignals.nonempty() )
//	{
//		mSignals.toStream(os);
//	}
//
//	if( mChannels.nonempty() )
//	{
//		mChannels.toStream(os);
//	}
//
//	if( mVariables.nonempty() )
//	{
//		mVariables.toStream(os);
//	}

	os << DECR_INDENT << std::flush;
}


}

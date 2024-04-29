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

#include <fml/expression/ExpressionConstant.h>

#include <fml/infrastructure/Machine.h>

#include <fml/type/TypeSpecifier.h>


namespace sep
{

/**
 * TIME CONSTANT
 */
std::string PropertyPart::VAR_ID_TIME( "$time"  );

// $time#initial
std::string PropertyPart::VAR_ID_TIME_INITIAL( "$time#initial" );

// $time#initial#value
BF PropertyPart::VAR_TIME_INITIAL_VALUE;


// $time#delta
std::string PropertyPart::VAR_ID_DELTA_TIME( "$delta" );

// $time#delta#initial
std::string PropertyPart::VAR_ID_DELTA_TIME_INITIAL( "$delta#initial" );

// $time#delta#initial#value
BF PropertyPart::VAR_DELTA_TIME_INITIAL_VALUE;


/**
 * DISPATCH
 * mOwnedElements
 */
void PropertyPart::dispatchOwnedElement(BF & anElement)
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anElement )
			<< "Executable Machine owned element !!!"
			<< SEND_EXIT;

	ObjectElement & objElement = anElement.to< ObjectElement >();

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
			objElement.setRuntimeOffset( mDataTypes.size() );

			mDataTypes.append( anElement );
			break;
		}

		case FORM_XFSP_FUNCTION_KIND:
		{
			objElement.setRuntimeOffset( mFunctions.size() );

			mFunctions.append( anElement );
			break;
		}

		case FORM_XFSP_BUFFER_KIND:
		{
			objElement.setRuntimeOffset( mBuffers.size() );

			mBuffers.append( anElement );
			break;
		}

		case FORM_XFSP_CHANNEL_KIND:
		{
			objElement.setRuntimeOffset( mChannels.size() );

			mChannels.append( anElement );
			break;
		}

		case FORM_XFSP_PORT_KIND:
		{
			objElement.setRuntimeOffset( mPorts.size() );

			mPorts.append( anElement );
			break;
		}


		default:
		{ // TODO
			AVM_OS_FATAL_ERROR_EXIT
					<< "dispatchOwnedElement() unexpected object, typeinfo: "
					<< anElement.classKindInfo() << "\n\t<< "
					<< anElement.to< ObjectElement >().strHeader()
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
void PropertyPart::dispatchOwnedVariable(BF & bfVariable)
{
	mVariables.append( bfVariable );

	Variable & aVariable = bfVariable.to< Variable >();

	const Modifier & aModifier = aVariable.getModifier();

	if( aModifier.hasNatureParameter() )
	{
		if( aModifier.isDirectionReturn() )
		{
			aVariable.setRuntimeOffset( mVariableReturns.size() );

			mVariableReturns.append( bfVariable );

		}
		else //if( aModifier.hasDirectionOtheThanReturn() )
		{
			aVariable.setRuntimeOffset( mVariableParameters.size() );

			mVariableParameters.append( bfVariable );
		}
	}
}

const BF & PropertyPart::saveOwnedVariable(Variable * aVariable)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aVariable )
			<< "Property Variable owned element !!!"
			<< SEND_EXIT;

	// Should be set by the executable machine container !
	aVariable->setOwnedOffset( mOwnedElements.size() );

	mOwnedElements.append( INCR_BF( aVariable ) );

	dispatchOwnedVariable( mOwnedElements.last() );

	return( mOwnedElements.last() );
}

/**
 * SAVE
 * mVariableParameters
 */
const BF & PropertyPart::saveOwnedVariableParameter(Variable * aVariable)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aVariable )
			<< "Property Variable owned element !!!"
			<< SEND_EXIT;

	// Should be set by the executable machine container !
	aVariable->setOwnedOffset( mOwnedElements.size() );

	mOwnedElements.append( INCR_BF( aVariable ) );

	aVariable->setRuntimeOffset( mVariableParameters.size() );

	mVariableParameters.append( mOwnedElements.last() );

	return( mOwnedElements.last() );
}

/**
 * SAVE
 * mVariableReturns
 */
const BF & PropertyPart::saveOwnedVariableReturn(Variable * aVariable)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aVariable )
			<< "Property Variable owned element !!!"
			<< SEND_EXIT;

	// Should be set by the executable machine container !
	aVariable->setOwnedOffset( mOwnedElements.size() );

	mOwnedElements.append( INCR_BF( aVariable ) );

	aVariable->setRuntimeOffset( mVariableReturns.size() );

	mVariableReturns.append( mOwnedElements.last() );

	return( mOwnedElements.last() );
}


/**
 * ADD
 * [ delta ]time property
 */
Variable * PropertyPart::addTimeSupport(const TypeSpecifier & timeType)
{
	mTimeVariable = new Variable(this->getContainer(),
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER,
			timeType, VAR_ID_TIME_INITIAL, VAR_TIME_INITIAL_VALUE);

	mExprTimeInitialConstant = saveOwnedVariable( mTimeVariable );

	Modifier mdfrTimed;

	mTimeVariable = new Variable(this->getContainer(), mdfrTimed,
			timeType, VAR_ID_TIME, mExprTimeInitialConstant);

	mExprTimeVariable = saveOwnedVariable( mTimeVariable );

	return( mTimeVariable );

}

Variable * PropertyPart::addDeltaTimeSupport(const TypeSpecifier & deltaType)
{
	mDeltaTimeVariable = new Variable(this->getContainer(),
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER,
			deltaType, VAR_ID_DELTA_TIME_INITIAL, VAR_DELTA_TIME_INITIAL_VALUE);

	mExprDeltaTimeInitialConstant = saveOwnedVariable( mDeltaTimeVariable );

	Modifier mdfrTimed;//( Modifier::FEATURE_UNSAFE_KIND ); // or SAFE ?

	mDeltaTimeVariable = new Variable(this->getContainer(), mdfrTimed,
			deltaType, VAR_ID_DELTA_TIME, mExprDeltaTimeInitialConstant);

	mExprDeltaTimeVariable = saveOwnedVariable( mDeltaTimeVariable );

	return( mDeltaTimeVariable );
}


/**
 * GETTER - SETTER
 * mDataTypes
 */
const BF & PropertyPart::getEnumDataType(const std::string & aQualifiedNameID) const
{
	const BF & dataType = getDataType(aQualifiedNameID);

	if( dataType.is< DataType >() && dataType.to< DataType >().isTypedEnum() )
	{
		return dataType;
	}
	else
	{
		return BF::REF_NULL;
	}
}

const BF & PropertyPart::getSemEnumDataType(const std::string & aQualifiedNameID) const
{
	const BF & enumDataType = getEnumDataType(aQualifiedNameID);
	if( enumDataType.valid() )
	{
		return enumDataType;
	}
	else if( hasContainerMachine() )
	{
		const Machine * containerMachine = getContainerMachine();
		while( containerMachine->isContainerMachine() )
		{
			containerMachine = containerMachine->getContainer()->to_ptr< Machine >();

			const BF & enumDataType =
					containerMachine->getPropertyPart().getEnumDataType(aQualifiedNameID);
			if( enumDataType.valid() )
			{
				return enumDataType;
			}
		}
	}
	return BF::REF_NULL;
}



/**
 * Serialization
 */
void PropertyPart::strVariableParameters(OutStream & out,
		const std::string & begin, const std::string & end,
		const std::string & sep) const
{
	if( mVariableParameters.nonempty() )
	{
		out << begin;

		const_variable_iterator it = var_parameter_begin();
		const_variable_iterator endIt = var_parameter_end();

		(it)->strParameter(out);
		for( ++it ; it != endIt ; ++it )
		{
			(it)->strParameter( out << sep );
		}

		out << end;
	}
}

void PropertyPart::strVariableReturns(OutStream & out,
		const std::string & begin, const std::string & end,
		const std::string & sep) const
{
	if( mVariableReturns.nonempty() )
	{
		out << begin;

		const_variable_iterator it = var_return_begin();
		const_variable_iterator endIt = var_return_end();

		(it)->strReturn(out);
		for( ++it ; it != endIt ; ++it )
		{
			(it)->strReturn( out << sep );
		}

		out << end;
	}
}

void PropertyPart::strHeader(OutStream & out) const
{
	if( hasContainer() )
	{
		getContainerMachine()->strHeader( out );
	}
}


void PropertyPart::toStream(OutStream & out) const
{
	out << TAB << "@" << getNameID() << ":" << EOL_INCR_INDENT;

	if( mOwnedElements.nonempty() )
	{
		mOwnedElements.toStream(out);
	}

//	if( mDataTypes.nonempty() )
//	{
//		mDataTypes.toStream(out);
//	}
//
//	if( mBuffers.nonempty() )
//	{
//		mBuffers.toStream(out);
//	}
//
//	if( mPorts.nonempty() )
//	{
//		mPorts.toStream(out);
//	}
//
//	if( mSignals.nonempty() )
//	{
//		mSignals.toStream(out);
//	}
//
//	if( mChannels.nonempty() )
//	{
//		mChannels.toStream(out);
//	}
//
//	if( mVariables.nonempty() )
//	{
//		mVariables.toStream(out);
//	}

	out << DECR_INDENT << std::flush;
}


}

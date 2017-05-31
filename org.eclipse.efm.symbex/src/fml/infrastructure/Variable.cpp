/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 17 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Variable.h"

#include <fml/type/BaseTypeSpecifier.h>

#include <fml/infrastructure/DataType.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/PropertyPart.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
Variable::Variable(const PropertyPart & aPropertyPart,
		const Modifier & aModifier, const BF & aType,
		const std::string & aNameID, const BF & aValue)
: PropertyElement( CLASS_KIND_T( Variable ),
		aPropertyPart.getContainer(), aModifier, aNameID ),
mType( aType ),
mValue( aValue ),

mBinding( ),

onWriteRoutine( NULL )
{
	//!! NOTHING
}


Variable::Variable(Machine * aContainer, const Modifier & aModifier,
		const Variable * aVariablePattern, const BF & aParam)
: PropertyElement( CLASS_KIND_T( Variable ) ,
		aContainer , aModifier , (*aVariablePattern) ),
mType( aVariablePattern->getType() ),
mValue( aParam ),

mBinding( aVariablePattern->mBinding  ),

onWriteRoutine( aVariablePattern->onWriteRoutine )
{
	setModifier( aVariablePattern->getModifier() );
}


/**
 * str Type
 */
std::string Variable::strT()
{
	if( getType().is< BaseTypeSpecifier >() )
	{
		return( getType().to_ptr< BaseTypeSpecifier >()->strT() );
	}
	else if( getType().is< DataType >() )
	{
		return( getType().to_ptr< DataType >()->strT() );
	}
	if( getType().is< ObjectElement >() )
	{
		return( getType().to_ptr< ObjectElement >()->getNameID() );
	}
	else
	{
		return( getType().str() );
	}
}


/**
 * UTIL
 */
Operator * Variable::getAssignOperator() const
{
	if( getModifier().hasNatureMacro() )
	{
		return( OperatorManager::OPERATOR_ASSIGN_MACRO );
	}
	else if( getModifier().hasNatureReference() )
	{
		return( OperatorManager::OPERATOR_ASSIGN_REF );
	}

	return( OperatorManager::OPERATOR_ASSIGN );
}


/**
 * GETTER
 * BehavioralPart Routine Container
 */
BehavioralPart * Variable::getContainerOfRoutines() const
{
	const ObjectElement * container = this->getContainer();
	for( ; container != NULL ; container = container->getContainer() )
	{
		if( container->is< Machine >() )
		{
			return( container->to< Machine >()->getBehaviorPart() );
		}
		else if( container->is< DataType >() )
		{
			return( container->to< DataType >()->getBehaviorPart() );
		}
	}

	return( NULL );
}

BehavioralPart * Variable::getUniqContainerOfRoutines() const
{
	ObjectElement * container = this->getContainer();
	for( ; container != NULL ; container = container->getContainer() )
	{
		if( container->is< Machine >() )
		{
			return( container->to< Machine >()->getUniqBehaviorPart() );
		}
		else if( container->is< DataType >() )
		{
			return( container->to< DataType >()->getUniqBehaviorPart() );
		}
	}

	return( NULL );
}


/**
 * Serialization
 */
void Variable::toStream(OutStream & os) const
{
	os << TAB << getModifier().toString_not( Modifier::FEATURE_CONST_KIND )
			<< ( getModifier().hasFeatureConst() ? "const" /*"val"*/ : "var" )
			<< " " << strTypeSpecifier() << " " << getNameID();

	if( mValue.valid() )
	{
//		os << " " << getAssignOperator()->str() << " " << mValue.str();
		os << " = " << mValue.str();
	}

	if( onWriteRoutine != NULL )
	{
		os << " { " << EOL_INCR_INDENT;

		onWriteRoutine->toStream(os);

		os << DECR_INDENT_TAB << "}";
	}
	else
	{
		os << ";";
	}

	os << EOL << std::flush;
}


void Variable::toStreamParameter(OutStream & os) const
{
	os << TAB << getModifier().toString()
			<< strTypeSpecifier() << " " << getNameID();

	if( mValue.valid() )
	{
		os << " = " << mValue.str();
	}

	os << EOL_FLUSH;
}



}

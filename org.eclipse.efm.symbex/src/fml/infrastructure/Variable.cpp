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
#include <fml/type/TypeManager.h>

#include <fml/infrastructure/DataType.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/PropertyPart.h>
#include <fml/infrastructure/Routine.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{

/**
 * GETTER
 * Unique Null Reference
 */
Variable & Variable::nullref()
{
	static Variable _NULL_(nullptr, TypeManager::UNIVERSAL,
			"$null<Variable>" , "$null<Variable>");
	_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );

	return( _NULL_ );
}


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

onWriteRoutine( nullptr )
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


std::string Variable::getUniqNameID() const
{
	std::string name = mNameID;
	std::replace(name.begin(), name.end(), '#', '_');

	const auto aContainer = getContainer();
	avm_offset_t parentOffset = aContainer->getRuntimeOffset();

	if( parentOffset == 0 )
	{
		return( OSS() << "_" << getOwnedOffset() << "_" << name );
	}
	else
	{
		return( OSS() << "_" << parentOffset
					<< "_" << getOwnedOffset() << "_" << name );
	}
}


/**
 * str Type
 */
std::string Variable::strT()
{
	if( getType().is< BaseTypeSpecifier >() )
	{
		return( getType().to< BaseTypeSpecifier >().strT() );
	}
	else if( getType().is< DataType >() )
	{
		return( getType().to< DataType >().strT() );
	}
	if( getType().is< ObjectElement >() )
	{
		return( getType().to< ObjectElement >().getNameID() );
	}
	else
	{
		return( getType().str() );
	}
}


/**
 * UTIL
 */
const Operator * Variable::getAssignOperator() const
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
	for( ; container != nullptr ; container = container->getContainer() )
	{
		if( container->is< Machine >() )
		{
			return( container->to_ptr< Machine >()->getBehaviorPart() );
		}
		else if( container->is< DataType >() )
		{
			return( container->to_ptr< DataType >()->getBehaviorPart() );
		}
	}

	return( nullptr );
}

BehavioralPart * Variable::getUniqContainerOfRoutines() const
{
	ObjectElement * container = this->getContainer();
	for( ; container != nullptr ; container = container->getContainer() )
	{
		if( container->is< Machine >() )
		{
			return( container->to_ptr< Machine >()->getUniqBehaviorPart() );
		}
		else if( container->is< DataType >() )
		{
			return( container->to_ptr< DataType >()->getUniqBehaviorPart() );
		}
	}

	return( nullptr );
}

/**
 * GETTER
 * onWrite
 */
const Routine & Variable::getOnWriteRoutine() const
{
	return( * onWriteRoutine );
}

/**
 * Serialization
 */
void Variable::toStream(OutStream & out) const
{
	out << TAB << getModifier().toString_not( Modifier::FEATURE_CONST_KIND )
		<< ( getModifier().hasFeatureConst() ? "const" /*"val"*/ : "var" )
		<< " " << strTypeSpecifier() << " " << getNameID();

	if( hasReallyUnrestrictedName() )
	{
		out << " \"" << getUnrestrictedName() << "\"";
	}

	if( mValue.valid() )
	{
//		out << " " << getAssignOperator()->str() << " " << mValue.str();
		out << " = " << mValue.str();
	}

	if( onWriteRoutine != nullptr )
	{
		out << " { " << EOL_INCR_INDENT;

		onWriteRoutine->toStream(out);

		out << DECR_INDENT_TAB << "}";
	}
	else
	{
		out << ";";
	}

	out << EOL << std::flush;
}


void Variable::toStreamParameter(OutStream & out) const
{
	out << TAB << getModifier().toString()
			<< strTypeSpecifier() << " " << getNameID();

	if( mValue.valid() )
	{
		out << " = " << mValue.str();
	}

	out << EOL_FLUSH;
}



}

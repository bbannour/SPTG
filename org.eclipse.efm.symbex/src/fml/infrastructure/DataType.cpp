/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "DataType.h"

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/TypeManager.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/PropertyPart.h>
#include <fml/infrastructure/Routine.h>


namespace sep
{


std::string DataType::ANONYM_ID = "_#type";


/**
 * CONSTRUCTOR
 * Interval
 */
DataType::DataType(Machine * aContainer, const std::string & aNameID,
		const BF & aTypeSpecifier, IIntervalKind::KIND anIntervalKind,
		const BF & anInfimum, const BF & aSupremum)
: ObjectElement(CLASS_KIND_T( DataType ), aContainer, aNameID),
mSpecifierKind( TYPE_INTERVAL_SPECIFIER ),
mTypeSpecifier( aTypeSpecifier ),
mConstraintRoutine( nullptr ),

mMinimumSize( 1 ),
mMaximumSize( 1 ),

mPropertyPart( nullptr ),
mBehavioralSpecification( nullptr ),

mIntervalKind( anIntervalKind ),
mInfimum( anInfimum ),
mSupremum( aSupremum )
{
//!! NOTHING
}

/**
 * CONSTRUCTOR
 * Container
 * Alias
 */
DataType::DataType(ObjectElement * aContainer,
		const std::string & aNameID,
		avm_type_specifier_kind_t aSpecifierKind,
		const BF & aTypeSpecifier, long maxSize)
: ObjectElement(CLASS_KIND_T( DataType ), aContainer, aNameID),
mSpecifierKind( aSpecifierKind ),
mTypeSpecifier( aTypeSpecifier ),
mConstraintRoutine( nullptr ),

mMinimumSize( 0 ),
mMaximumSize( maxSize ),

mPropertyPart( nullptr ),
mBehavioralSpecification( nullptr ),

mIntervalKind( IIntervalKind::CLOSED ),
mInfimum( ),
mSupremum( )
{
	//!! NOTHING
}

/**
 * CONSTRUCTOR
 * Enum
 * Structure
 * Union
 */
DataType::DataType(ObjectElement * aContainer, const std::string & aNameID,
		avm_type_specifier_kind_t aSpecifierKind, const BF & aTypeSpecifier)
: ObjectElement(CLASS_KIND_T( DataType ), aContainer, aNameID),
mSpecifierKind( aSpecifierKind ),
mTypeSpecifier( aTypeSpecifier ),
mConstraintRoutine( nullptr ),

mMinimumSize( 1 ),
mMaximumSize( 1 ),

mPropertyPart( nullptr ),
mBehavioralSpecification( nullptr ),

mIntervalKind( IIntervalKind::CLOSED ),
mInfimum( ),
mSupremum( )
{
	//!! NOTHING
}


/**
 * CONSTRUCTOR
 * Copy
 */
DataType::DataType(const DataType & aDataType)
: ObjectElement( aDataType ),
mSpecifierKind( aDataType.mSpecifierKind ),
mTypeSpecifier( aDataType.mTypeSpecifier ),
mConstraintRoutine( aDataType.mConstraintRoutine ),

mMinimumSize( aDataType.mMinimumSize ),
mMaximumSize( aDataType.mMaximumSize ),

mPropertyPart( (aDataType.mPropertyPart == nullptr) ?
	nullptr : new PropertyPart( *(aDataType.mPropertyPart) ) ),

mBehavioralSpecification( (aDataType.mBehavioralSpecification == nullptr) ?
	nullptr : new BehavioralPart( *(aDataType.mBehavioralSpecification) ) ),


mIntervalKind( aDataType.mIntervalKind ),
mInfimum( aDataType.mInfimum ),
mSupremum( aDataType.mSupremum )
{
	//!! NOTHING
}


/**
 * DESTRUCTOR
 */
DataType::~DataType()
{
	delete( mPropertyPart );

	delete( mBehavioralSpecification );
}


/**
 * GETTER
 * ITypeSpecifier API
 */
const BaseTypeSpecifier & DataType::thisTypeSpecifier() const
{
	return( BaseTypeSpecifier::nullref() );
}


/**
 * GETTER - SETTER
 * mConstraint
 */
const Routine & DataType::getConstraintRoutine() const
{
	return( * mConstraintRoutine );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// INTERVAL
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
/**
 * CONSTRUCTOR
 * Interval
 */
DataType * DataType::newInterval(
		Machine * aContainer, const std::string & aNameID,
		const BF & aTypeSpecifier, IIntervalKind::KIND anIntervalKind,
		const BF & anInfimum, const BF & aSupremum)
{
	return( new DataType(aContainer, aNameID, aTypeSpecifier,
			anIntervalKind, anInfimum, aSupremum) );
}

/**
 * GETTER
 * Interval Length
 */
avm_integer_t DataType::getIntervalLength() const
{
	avm_integer_t infBound = AVM_NUMERIC_MIN_INTEGER;
	avm_integer_t supBound = AVM_NUMERIC_MAX_INTEGER;

	if( mInfimum.isUInteger() )
	{
		infBound = mInfimum.toUInteger();
	}
	else if( mInfimum.is< Variable >() )
	{
		const Variable & aVar = mInfimum.to< Variable >();

		if( aVar.hasValue() && aVar.getValue().isUInteger() )
		{
			infBound = aVar.getValue().toUInteger();
		}
		else
		{
			return( -1 );
		}
	}
	else
	{
		return( -1 );
	}


	if( mSupremum.isUInteger() )
	{
		supBound = mSupremum.toUInteger();
	}
	else if( mSupremum.is< Variable >() )
	{
		Variable * aVar = mSupremum.to_ptr< Variable >();

		if( aVar->hasValue() && aVar->getValue().isUInteger() )
		{
			supBound = aVar->getValue().toUInteger();
		}
		else
		{
			return( -1 );
		}
	}
	else
	{
		return( -1 );
	}


	return( supBound - infBound + ( isCLOSED() ? 1 : 0 ) );
}



/**
 * Serialization
 */
void DataType::toStreamInterval(OutStream & out) const
{
	out << " interval< " << getTypeSpecifier().str()
		<< strIso_Interval() << " >";

	if( hasConstraintRoutine() )
	{
		out << " {" << EOL_INCR_INDENT;
		getConstraintRoutine().toStream(out);
		out << DECR_INDENT_TAB << "}";
	}
	else
	{
		out << ";";
	}
}



////////////////////////////////////////////////////////////////////////////////
// CONTAINER
////////////////////////////////////////////////////////////////////////////////

/**
 * CONSTRUCTOR
 * Container
 */
DataType * DataType::newContainer(
		Machine * aContainer, const std::string & aNameID,
		avm_type_specifier_kind_t aSpecifierKind, long aSize)
{
	return( new DataType(aContainer, aNameID,
			aSpecifierKind, TypeManager::UNIVERSAL, aSize) );
}

DataType * DataType::newContainer(
		Machine * aContainer, const std::string & aNameID,
		avm_type_specifier_kind_t aSpecifierKind,
		const BF & aTypeSpecifier, long aSize)
{
	return( new DataType(aContainer, aNameID,
			aSpecifierKind, aTypeSpecifier, aSize) );
}


/**
 * Serialization
 */
std::string DataType::strContainerId(
		avm_type_specifier_kind_t aSpecifierKind, const BF & baseT, long aSize)
{
	std::ostringstream oss;

	if( aSpecifierKind != TYPE_ARRAY_SPECIFIER )
	{
		oss << ContainerTypeSpecifier::strSpecifierKing(aSpecifierKind) << "<";
	}

	if( baseT.valid() )
	{
		if( baseT == TypeManager::UNIVERSAL)
		{
			oss << "<universal>";
		}
		else if( baseT.is< BaseTypeSpecifier >() )
		{
			oss << baseT.to< BaseTypeSpecifier >().strT();
		}
		else if( baseT.is< DataType >() )
		{
			oss << baseT.to< DataType >().strT();
		}
		else if( baseT.is< ObjectElement >() )
		{
			oss << baseT.to< ObjectElement >().getNameID();
		}
		else
		{
			oss << "<type>";
		}
	}
	else
	{
		oss << "<null>";
	}

	if( aSpecifierKind != TYPE_ARRAY_SPECIFIER )
	{
		if( aSize >= 0 )
		{
			oss << " , "  << aSize << ">";
		}
		else
		{
			oss << " , *>";
		}
	}
	else
	{
		oss << "[ "  << aSize << " ]";
	}

	return( oss.str() );
}


std::string DataType::strContainerId(
		avm_type_specifier_kind_t aSpecifierKind, long aSize)
{
	std::ostringstream oss;

	oss << ContainerTypeSpecifier::strSpecifierKing(aSpecifierKind);

	if( aSize >= 0 )
	{
		oss << "<" << aSize << ">";
	}
	else
	{
		oss << "<*>";
	}

	return( oss.str() );
}


std::string DataType::strContainerType() const
{
	std::ostringstream oss;

	if( isTypedArray() )
	{
		if( mTypeSpecifier.is< BaseTypeSpecifier >() )
		{
			oss << mTypeSpecifier.to< BaseTypeSpecifier >().strT();
		}
		else if( mTypeSpecifier.is< DataType >() )
		{
			oss << mTypeSpecifier.to< DataType >().strT();
		}

		oss << "[ " << mMaximumSize << " ]";
	}
	else
	{
		oss << ContainerTypeSpecifier::strSpecifierKing(mSpecifierKind);

		if( mTypeSpecifier.valid() )
		{
			if( mTypeSpecifier.is< BaseTypeSpecifier >() )
			{
				oss << "< " << mTypeSpecifier.to<
						BaseTypeSpecifier >().strT();
			}
			else if( mTypeSpecifier.is< DataType >() )
			{
				oss << "< " << mTypeSpecifier.to< DataType >().strT();
			}
			else if( mTypeSpecifier.is< ObjectElement >() )
			{
				oss << "< "
					<< mTypeSpecifier.to< ObjectElement >().getNameID();
			}
			else
			{
				oss << "< ?";
			}
		}
		else
		{
			oss << "< $null<type>";
		}

		if( mMaximumSize >= 0 )
		{
			oss << " , " << mMaximumSize;
		}

		oss << " >";
	}

	return( oss.str() );
}


void DataType::toStreamContainer(OutStream & out) const
{
	out << " " << strContainerType();

	if( hasConstraintRoutine() )
	{
		out << " {" << EOL_INCR_INDENT;
		getConstraintRoutine().toStream(out);
		out << DECR_INDENT_TAB << "}";
	}
	else
	{
		out << ";";
	}
}


////////////////////////////////////////////////////////////////////////////////
// ENUMERATIOIN
// STRUCTURE
// UNION
////////////////////////////////////////////////////////////////////////////////
/**
 * GETTER
 * mPropertyPart
 */
bool DataType::hasProperty() const
{
	return( (mPropertyPart != nullptr)
			&& mPropertyPart->nonempty() );
}

/**
 * GETTER - SETTER
 * mBehavioralSpecification
 */
BehavioralPart * DataType::getUniqBehaviorPart()
{
	if( mBehavioralSpecification == nullptr )
	{
		mBehavioralSpecification = new BehavioralPart(this, "moe");
	}

	return( mBehavioralSpecification );
}



////////////////////////////////////////////////////////////////////////////////
// ENUMERATIOIN
////////////////////////////////////////////////////////////////////////////////

/**
 * CONSTRUCTOR
 * Enum
 */
DataType * DataType::newEnum(const PropertyPart & aPropertyPart,
		const std::string & aNameID, const BF & superEnumerationType)
{
	DataType * newDataType = new DataType(aPropertyPart.getContainer(),
			aNameID, TYPE_ENUM_SPECIFIER, superEnumerationType );

	newDataType->setPropertyPart( new PropertyPart(newDataType, "symbol") );

	return( newDataType );
}

const BF & DataType::getEnumSymbol(const std::string & aNameID) const
{
	return (mPropertyPart != nullptr) ?
			mPropertyPart->getVariable(aNameID) : BF::REF_NULL;
}


/**
 * GETTER
 * Enumeration Size
 * Interval Length
 */
std::size_t DataType::getEnumSize() const
{
	return( (mPropertyPart != nullptr) ?
			mPropertyPart->getVariables().size() : 0 );
}

/**
 * GETTER - SETTER
 * mVariables
 */
void DataType::appendVariable(const BF & aVariable)
{
	mPropertyPart->appendVariable( aVariable );
}

void DataType::saveVariable(Variable * aVariable)
{
	mPropertyPart->saveOwnedVariable( aVariable );
}


/**
 * Serialization
 */
void DataType::toStreamEnum(OutStream & out) const
{
	out << " enum";
	if( hasSuperTypeSpecifier() )
	{
		out  << "< " << getTypeSpecifier().to< DataType >().strT() << " >";
	}
	out << " {" << EOL_FLUSH;

	if( mPropertyPart->hasVariable() )
	{
		TableOfVariable::const_raw_iterator it =
				mPropertyPart->getVariables().begin();
		TableOfVariable::const_raw_iterator endIt =
				mPropertyPart->getVariables().end();

		out << TAB2 << (it)->getNameID();
		if( (it)->hasReallyUnrestrictedName() )
		{
			out << " \"" << (it)->getUnrestrictedName() << "\"";
		}
		if( (it)->hasValue() )
		{
			out << " = " << (it)->strValue();
		}
		for( ++it ; it != endIt ; ++it )
		{
			out << "," << EOL;

			out << TAB2 << (it)->getNameID();
			if( (it)->hasReallyUnrestrictedName() )
			{
				out << " \"" << (it)->getUnrestrictedName() << "\"";
			}
			if( (it)->hasValue() )
			{
				out << " = " << (it)->strValue();
			}
		}
		out << EOL;
	}

	out << TAB << "}";
}


////////////////////////////////////////////////////////////////////////////////
// STRUCTURE
////////////////////////////////////////////////////////////////////////////////
/**
 * CONSTRUCTOR
 * Structure
 */
DataType * DataType::newStructure(
		const PropertyPart & aPropertyPart, const std::string & aNameID)
{
	DataType * newDataType = new DataType(
			aPropertyPart.getContainer(), aNameID, TYPE_CLASS_SPECIFIER );

	newDataType->setPropertyPart( new PropertyPart(newDataType, "property") );

	return( newDataType );
}

/**
 * Serialization
 */
void DataType::toStreamStructure(OutStream & out) const
{
	out << " struct {" << EOL_FLUSH;

	if( hasProperty() )
	{
		mPropertyPart->toStream(out);
	}

	if( hasBehavior() && mBehavioralSpecification->hasAnyRoutine() )
	{
		mBehavioralSpecification->toStreamAnyRoutine( out << EOL );
	}

	out << TAB << "}";
}



////////////////////////////////////////////////////////////////////////////////
// CHOICE
////////////////////////////////////////////////////////////////////////////////
/**
 * CONSTRUCTOR
 * Choice
 */
DataType * DataType::newChoice(
		const PropertyPart & aPropertyPart, const std::string & aNameID)
{
	DataType * newDataType = new DataType(
			aPropertyPart.getContainer(), aNameID, TYPE_CHOICE_SPECIFIER );

	newDataType->setPropertyPart( new PropertyPart(newDataType, "property") );

	return( newDataType );
}

/**
 * Serialization
 */
void DataType::toStreamChoice(OutStream & out) const
{
	out << " choice {" << EOL_FLUSH;

	if( hasProperty() )
	{
		mPropertyPart->toStream(out);
	}

	out << TAB << "}";
}


////////////////////////////////////////////////////////////////////////////////
// UNION
////////////////////////////////////////////////////////////////////////////////
/**
 * CONSTRUCTOR
 * Union
 */
DataType * DataType::newUnion(
		const PropertyPart & aPropertyPart, const std::string & aNameID)
{
	DataType * newDataType = new DataType(
			aPropertyPart.getContainer(), aNameID, TYPE_UNION_SPECIFIER );

	newDataType->setPropertyPart( new PropertyPart(newDataType, "property") );

	return( newDataType );
}

/**
 * Serialization
 */
void DataType::toStreamUnion(OutStream & out) const
{
	out << " union {" << EOL_FLUSH;

	if( hasProperty() )
	{
		mPropertyPart->toStream(out);
	}

	out << TAB << "}";
}


////////////////////////////////////////////////////////////////////////////////
// ALIAS
////////////////////////////////////////////////////////////////////////////////

/**
 * CONSTRUCTOR
 * Alias
 */
DataType * DataType::newAlias(const PropertyPart & aPropertyPart,
		const std::string & aNameID, const BF & aTypeSpecifier)
{
	return( new DataType(aPropertyPart.getContainer(),
			aNameID, TYPE_ALIAS_SPECIFIER, aTypeSpecifier, 1) );
}

/**
 * Serialization
 */
void DataType::toStreamAlias(OutStream & out) const
{
	if( mTypeSpecifier.is< BaseTypeSpecifier >() )
	{
		out << " " << mTypeSpecifier.to< BaseTypeSpecifier >().strT();
	}
	else if( mTypeSpecifier.is< DataType >() )
	{
		out << " " << mTypeSpecifier.to< DataType >().strT();
	}
	else
	{
		out << str_indent( mTypeSpecifier );
	}

	if( mConstraintRoutine!= nullptr )
	{
		out << " {" << EOL_INCR_INDENT;
		mConstraintRoutine->toStream(out);
		out << DECR_INDENT_TAB << "}";
	}
	else
	{
		out << ";";
	}
}




/**
 * Serialization
 */
std::string DataType::strTypeSpecifier(const BF & aTypeSpecifier)
{
	if( aTypeSpecifier.valid() )
	{
		if( aTypeSpecifier.is< BaseTypeSpecifier >() )
		{
			return aTypeSpecifier.to< BaseTypeSpecifier >().strT();
		}
		else if( aTypeSpecifier.is< DataType >() )
		{
			return aTypeSpecifier.to< DataType >().strT();
		}
		else
		{
			return( OSS() << "type< " << aTypeSpecifier.str() << ">" );
		}
	}
	else
	{
		return( "type<null>" );
	}
}


void DataType::strHeader(OutStream & out) const
{
	out << getModifier().toString()
		<< "type " << getFullyQualifiedNameID(); //<< getNameID();

	if( hasUnrestrictedName() )
	{
		out << " \"" << getUnrestrictedName() << "\"";
	}
}


void DataType::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	out << TAB << getModifier().toString() << "type " << getNameID();


	if( hasTypeContainer() )
	{
		toStreamContainer(out);
	}
	else if( isTypedInterval() )
	{
		toStreamInterval(out);
	}
	else if( isTypedEnum() )
	{
		toStreamEnum(out);
	}
	else if( isTypedStructure() )
	{
		toStreamStructure(out);
	}

	else if( isTypedChoice() )
	{
		toStreamChoice(out);
	}

	else if( isTypedUnion() )
	{
		toStreamUnion(out);
	}

	else// if( isDataTypeAlias() )
	{
		toStreamAlias(out);
	}


	out << EOL_FLUSH;
}


} /* namespace sep */

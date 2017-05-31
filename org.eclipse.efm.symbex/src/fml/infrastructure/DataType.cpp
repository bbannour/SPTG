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
mConstraintRoutine( NULL ),

mMinimumSize( 1 ),
mMaximumSize( 1 ),

mPropertyPart( NULL ),
mBehavioralSpecification( NULL ),

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
mConstraintRoutine( NULL ),

mMinimumSize( 0 ),
mMaximumSize( maxSize ),

mPropertyPart( NULL ),
mBehavioralSpecification( NULL ),

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
DataType::DataType(ObjectElement * aContainer,
		const std::string & aNameID,
		avm_type_specifier_kind_t aSpecifierKind)
: ObjectElement(CLASS_KIND_T( DataType ), aContainer, aNameID),
mSpecifierKind( aSpecifierKind ),
mTypeSpecifier( ),
mConstraintRoutine( NULL ),

mMinimumSize( 1 ),
mMaximumSize( 1 ),

mPropertyPart( NULL ),
mBehavioralSpecification( NULL ),

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

mPropertyPart( (aDataType.mPropertyPart == NULL) ?
	NULL : new PropertyPart( *(aDataType.mPropertyPart) ) ),

mBehavioralSpecification( (aDataType.mBehavioralSpecification == NULL) ?
	NULL : new BehavioralPart( *(aDataType.mBehavioralSpecification) ) ),


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
avm_integer_t DataType::getIntervalLength()
{
	avm_integer_t infBound = AVM_NUMERIC_MIN_INTEGER;
	avm_integer_t supBound = AVM_NUMERIC_MAX_INTEGER;

	if( mInfimum.isUInteger() )
	{
		infBound = mInfimum.toUInteger();
	}
	else if( mInfimum.is< Variable >() )
	{
		Variable * aVar = mInfimum.to_ptr< Variable >();

		if( aVar->hasValue() && aVar->getValue().isUInteger() )
		{
			infBound = aVar->getValue().toUInteger();
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
void DataType::toStreamInterval(OutStream & os) const
{
	os << " interval< " << getTypeSpecifier().str() << strIso_Interval() << " >";

	if( hasConstraintRoutine() )
	{
		os << " {" << EOL_INCR_INDENT;
		getConstraintRoutine()->toStream(os);
		os << DECR_INDENT_TAB << "}";
	}
	else
	{
		os << ";";
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
			oss << baseT.to_ptr< BaseTypeSpecifier >()->strT();
		}
		else if( baseT.is< DataType >() )
		{
			oss << baseT.to_ptr< DataType >()->strT();
		}
		else if( baseT.is< ObjectElement >() )
		{
			oss << baseT.to_ptr< ObjectElement >()->getNameID();
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
			oss << " , * >";
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
	std::ostringstream os;

	os << ContainerTypeSpecifier::strSpecifierKing(aSpecifierKind);

	if( aSize >= 0 )
	{
		os << "<" << aSize << ">";
	}
	else
	{
		os << "<*>";
	}

	return( os.str() );
}


std::string DataType::strContainerType() const
{
	std::ostringstream oss;

	if( isTypedArray() )
	{
		if( mTypeSpecifier.is< BaseTypeSpecifier >() )
		{
			oss << mTypeSpecifier.to_ptr< BaseTypeSpecifier >()->strT();
		}
		else if( mTypeSpecifier.is< DataType >() )
		{
			oss << mTypeSpecifier.to_ptr< DataType >()->strT();
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
				oss << "< " << mTypeSpecifier.to_ptr<
						BaseTypeSpecifier >()->strT();
			}
			else if( mTypeSpecifier.is< DataType >() )
			{
				oss << "< " << mTypeSpecifier.to_ptr< DataType >()->strT();
			}
			else if( mTypeSpecifier.is< ObjectElement >() )
			{
				oss << "< "
					<< mTypeSpecifier.to_ptr< ObjectElement >()->getNameID();
			}
			else
			{
				oss << "< ?";
			}
		}
		else
		{
			oss << "< null<type>";
		}

		if( mMaximumSize >= 0 )
		{
			oss << " , " << mMaximumSize;
		}

		oss << " >";
	}

	return( oss.str() );
}


void DataType::toStreamContainer(OutStream & os) const
{
	os << " " << strContainerType();

	if( hasConstraintRoutine() )
	{
		os << " {" << EOL_INCR_INDENT;
		getConstraintRoutine()->toStream(os);
		os << DECR_INDENT_TAB << "}";
	}
	else
	{
		os << ";";
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
	return( (mPropertyPart != NULL)
			&& mPropertyPart->nonempty() );
}

/**
 * GETTER - SETTER
 * mBehavioralSpecification
 */
BehavioralPart * DataType::getUniqBehaviorPart()
{
	if( mBehavioralSpecification == NULL )
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
DataType * DataType::newEnum(
		const PropertyPart & aPropertyPart, const std::string & aNameID)
{
	DataType * newDataType = new DataType(
			aPropertyPart.getContainer(), aNameID, TYPE_ENUM_SPECIFIER );

	newDataType->setPropertyPart( new PropertyPart(newDataType, "symbol") );

	return( newDataType );
}

/**
 * GETTER
 * Enumeration Size
 * Interval Length
 */
avm_size_t DataType::getEnumSize()
{
	return( (mPropertyPart != NULL) ? mPropertyPart->getVariables().size() : 0 );
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
void DataType::toStreamEnum(OutStream & os) const
{
	os << " enum {" << EOL_FLUSH;

	if( mPropertyPart->hasVariable() )
	{
		TableOfVariable::const_raw_iterator it =
				mPropertyPart->getVariables().begin();
		TableOfVariable::const_raw_iterator endIt =
				mPropertyPart->getVariables().end();

		os << TAB2 << (it)->getNameID();
		if( (it)->hasValue() )
		{
			os << " = " << (it)->strValue();
		}
		for( ++it ; it != endIt ; ++it )
		{
			os << "," << EOL;

			os << TAB2 << (it)->getNameID();
			if( (it)->hasValue() )
			{
				os << " = " << (it)->strValue();
			}
		}
		os << EOL;
	}

	os << TAB << "}";
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
void DataType::toStreamStructure(OutStream & os) const
{
	os << " struct {" << EOL_FLUSH;

	if( hasProperty() )
	{
		mPropertyPart->toStream(os);
	}

	if( hasBehavior() && mBehavioralSpecification->hasAnyRoutine() )
	{
		mBehavioralSpecification->toStreamAnyRoutine( os << EOL );
	}

	os << TAB << "}";
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
void DataType::toStreamChoice(OutStream & os) const
{
	os << " choice {" << EOL_FLUSH;

	if( hasProperty() )
	{
		mPropertyPart->toStream(os);
	}

	os << TAB << "}";
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
void DataType::toStreamUnion(OutStream & os) const
{
	os << " union {" << EOL_FLUSH;

	if( hasProperty() )
	{
		mPropertyPart->toStream(os);
	}

	os << TAB << "}";
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
void DataType::toStreamAlias(OutStream & os) const
{
	if( mTypeSpecifier.is< BaseTypeSpecifier >() )
	{
		os << " " << mTypeSpecifier.to_ptr< BaseTypeSpecifier >()->strT();
	}
	else if( mTypeSpecifier.is< DataType >() )
	{
		os << " " << mTypeSpecifier.to_ptr< DataType >()->strT();
	}
	else
	{
		os << str_indent( mTypeSpecifier );
	}

	if( mConstraintRoutine!= NULL )
	{
		os << " {" << EOL_INCR_INDENT;
		mConstraintRoutine->toStream(os);
		os << DECR_INDENT_TAB << "}";
	}
	else
	{
		os << ";";
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
			return aTypeSpecifier.to_ptr< BaseTypeSpecifier >()->strT();
		}
		else if( aTypeSpecifier.is< DataType >() )
		{
			return aTypeSpecifier.to_ptr< DataType >()->strT();
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


void DataType::strHeader(OutStream & os) const
{
	os << getModifier().toString()
			<< "type " << getFullyQualifiedNameID(); //<< getNameID();

	if( hasUnrestrictedName() )
	{
		os << " \"" << getUnrestrictedName() << "\"";
	}
}


void DataType::toStream(OutStream & os) const
{
	if( os.preferablyFQN() )
	{
		os << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(os);

		return;
	}

	os << TAB << getModifier().toString() << "type " << getNameID();


	if( hasTypeContainer() )
	{
		toStreamContainer(os);
	}
	else if( isTypedInterval() )
	{
		toStreamInterval(os);
	}
	else if( isTypedEnum() )
	{
		toStreamEnum(os);
	}
	else if( isTypedStructure() )
	{
		toStreamStructure(os);
	}

	else if( isTypedChoice() )
	{
		toStreamChoice(os);
	}

	else if( isTypedUnion() )
	{
		toStreamUnion(os);
	}

	else// if( isTypedAlias() )
	{
		toStreamAlias(os);
	}


	os << EOL_FLUSH;
}


} /* namespace sep */

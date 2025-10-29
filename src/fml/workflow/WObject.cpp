/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "WObject.h"

#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/StatementTypeChecker.h>
#include <fml/operator/Operator.h>


namespace sep
{

/**
 * STATIC
 * _NULL_
 */
WObject * WObject::_NULL_ = nullptr;

const std::string & WObject::FML_FQN_SCHEME = "fml";

const std::string & WObject::FML_FQN_ROOT   =
			WObject::FML_FQN_SCHEME + FQN_ID_SCHEME_PATH_SEPARATOR;

const std::string & WObject::SEW_FQN_SCHEME = "sew";

const std::string & WObject::SEW_FQN_ROOT   =
			WObject::SEW_FQN_SCHEME + FQN_ID_SCHEME_PATH_SEPARATOR;


/**
 * DESTROY
 */
void WObject::destroyOwnedElement()
{
	if( mOwnedElements.nonempty() )
	{
		const WObject * wfObject = WObject::_NULL_;

		std::size_t ownedCount = mOwnedElements.size();

//AVM_IF_DEBUG_ENABLED
//	AVM_OS_DEBUG << "@" << this->raw_address() << ": ref< "
//			<< this->getRefCount() << " > " << this->strUniqId() << std::endl;
//	for( std::size_t offset = 0 ; offset < ownedCount ; ++offset)
//	{
//		wfObject = mOwnedElements[ offset ];
//
//	AVM_OS_DEBUG << wfObject->getOffset() << " @" << wfObject->raw_address()
//			<< ": ref< " << wfObject->getRefCount()  << " > "
//			<< wfObject->strUniqId() << std::endl;
//	}
//AVM_ENDIF_DEBUG_ENABLED

		for( std::size_t offset = ownedCount ; offset > 0 ; --offset)
		{
			wfObject = mOwnedElements[ offset - 1 ];

			if( wfObject == WObject::_NULL_ )
			{
AVM_IF_DEBUG_ENABLED
	AVM_OS_WARN << "Unexpected <null> as Owned WObject for destruction !"
			<< std::endl;
AVM_ENDIF_DEBUG_ENABLED
			}
			else if( wfObject->getContainer() == this )
			{
				if( wfObject->isUnique() )
				{
					// NORMAL SITUATION
					wfObject = WObject::_NULL_;
				}
				else if( wfObject->isMultiple() )
				{
AVM_IF_DEBUG_ENABLED
	AVM_OS_WARN << "Unexpected Owned WObject <"
			<< wfObject->strUniqId() << "> with refcount < "
			<< wfObject->getRefCount()
			<< " > for destruction !" << std::endl;
AVM_ENDIF_DEBUG_ENABLED
				}

				else
				{
AVM_IF_DEBUG_ENABLED
	AVM_OS_WARN << "Unexpected Owned WObject <pos " << offset << ": " << std::endl;
	AVM_OS_WARN << wfObject->strUniqId() << "> with refCount == 0 !!!" << std::endl;
AVM_ENDIF_DEBUG_ENABLED
				}
			}

			else
			{
AVM_IF_DEBUG_ENABLED
	AVM_OS_WARN << "Unexpected non-Owned WObject <"
			<< wfObject->strUniqId() << "> with refcount < "
			<< wfObject->getRefCount()
			<< " > for destruction !" << std::endl;
AVM_ENDIF_DEBUG_ENABLED
			}
		}

		mOwnedElements.clear();
	}
}


/**
 * DESTROY
 */
void WObjectManager::destroyManagedElement()
{
	mTableOfRegisteredWObject.clear();

	if( mTableOfManagedElement.nonempty() )
	{
		WObject * wfObject = WObject::_NULL_;

		std::size_t managedCount = mTableOfManagedElement.size();

//AVM_IF_DEBUG_ENABLED
//	for( std::size_t offset = 0 ; offset < managedCount ; ++offset)
//	{
//		wfObject = mTableOfManagedElement[ offset ];
//
//	AVM_OS_DEBUG << wfObject->getOffset() << " @" << wfObject->raw_address()
//			<< ": ref< " << wfObject->getRefCount()  << " > "
//			<< wfObject->strUniqId() << std::endl;
//	}
//AVM_ENDIF_DEBUG_ENABLED

		std::size_t destroyedCount = 0;
		for( std::size_t offset = managedCount ; offset > 0 ; --offset)
		{
			wfObject = mTableOfManagedElement[ offset - 1 ];

			if( wfObject == WObject::_NULL_ )
			{
AVM_IF_DEBUG_ENABLED
	AVM_OS_WARN << "Unexpected <null> as Managed WObject for destruction !"
			<< std::endl;
AVM_ENDIF_DEBUG_ENABLED
			}
			else if( wfObject->isUnique() )
			{
				++destroyedCount;

				delete( wfObject );

				wfObject = WObject::_NULL_;
			}

			else if( wfObject->isMultiple() )
			{
AVM_IF_DEBUG_ENABLED
	AVM_OS_WARN << "Indestructible Managed WObject <pos "
			<< wfObject->getOwnedOffset() << ": " << std::flush;
	AVM_OS_WARN << wfObject->strUniqId() << "> with refcount < "
			<< wfObject->getRefCount() << " > for destruction !" << std::endl;
AVM_ENDIF_DEBUG_ENABLED

				wfObject->decrRefCount();
			}

			else
			{
AVM_IF_DEBUG_ENABLED
AVM_OS_WARN << ">>> Unexpected Managed WObject <" << wfObject->strUniqId()
		<< "> with refCount == 0 !!!" << std::endl;
AVM_ENDIF_DEBUG_ENABLED
			}
		}

AVM_IF_DEBUG_ENABLED_AND( destroyedCount < managedCount )
	AVM_OS_WARN << "Managed WObject destruction count < " << destroyedCount
			<< " / " << managedCount << " > !" << std::endl;
AVM_ENDIF_DEBUG_ENABLED
	}
}


/**
 * FACTORY
 * container of WObject
 * !UNUSED!
const WObject * WObject::container() const
{
	const WObject * wfContainer = WObject::_NULL_;

	ObjectElement * aContainer = this->getContainer();
	while( aContainer != nullptr )
	{
		if( aContainer->is< WObject >() )
		{
			wfContainer = aContainer->to_ptr< WObject >();
			if( wfContainer->isWTypedObject()
				|| wfContainer->isWSequence() )
			{
				return( wfContainer );
			}
		}

		aContainer = aContainer->getContainer();
	}

	return( WObject::_NULL_ );
}

const WObject * WObject::sequenceContainerOf() const
{
	const WObject * wfContainer = WObject::_NULL_;

	ObjectElement * aContainer = this->getContainer();
	while( aContainer != nullptr )
	{
		if( aContainer->is< WObject >() )
		{
			wfContainer = aContainer->to_ptr< WObject >();

			if( wfContainer->isWSequence() )
			{
				return( wfContainer );
			}
			else if( wfContainer->isWTypedObject() )
			{
				return( WObject::_NULL_ );
			}
		}

		aContainer = aContainer->getContainer();
	}

	return( WObject::_NULL_ );
}
* !UNUSED!
*/

const WObject * WObject::objectContainer() const
{
	const WObject * wfContainer = WObject::_NULL_;

	const ObjectElement * aContainer = this->getContainer();
	while( aContainer != nullptr )
	{
		wfContainer = aContainer->to_ptr< WObject >();

		if( wfContainer->isWTypedObject() )
		{
			return( wfContainer );
		}

		aContainer = aContainer->getContainer();
	}

	return( WObject::_NULL_ );
}


/**
 * Serialization
 */

std::string WObject::strPropertyValue() const
{
	switch( mKind )
	{
		case WOBJECT_PROPERTY_OPERATOR_KIND:
			AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mOperatorValue )
					<< "Operator value as alias < " << strUniqId() << " > !"
					<< SEND_EXIT;
			return( (OSS() << "<op> " << mOperatorValue->str()).str() );

		case WOBJECT_PROPERTY_WREFERENCE_KIND:
			AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mWOjectReferenceValue )
					<< "WOject reference value as alias < "
					<< strUniqId() << " > !"
					<< SEND_EXIT;
			return( (OSS() << "<ref> "
					<< mWOjectReferenceValue->strHeader()).str() );

		case WOBJECT_PROPERTY_BOOLEAN_KIND:
			return( (OSS() << "<bool> " << mValue.str()).str() );

		case WOBJECT_PROPERTY_CHARACTER_KIND:
			return( (OSS() << "<char> " << mValue.str()).str() );

		case WOBJECT_PROPERTY_INTEGER_KIND:
			return( (OSS() << "<int> " << mValue.str()).str() );

		case WOBJECT_PROPERTY_RATIONAL_KIND:
			return( (OSS() << "<rat> " << mValue.str()).str() );

		case WOBJECT_PROPERTY_FLOAT_KIND:
			return( (OSS() << "<float> " << mValue.str()).str() );

		case WOBJECT_PROPERTY_IDENTIFIER_KIND:
			return( (OSS() << "<id> " << mValue.str()).str() );

		case WOBJECT_PROPERTY_QUALIFIED_IDENTIFIER_KIND:
			return( (OSS() << "<qid> " << mValue.str()).str() );

		case WOBJECT_PROPERTY_UNIQ_FORM_IDENTIFIER_KIND:
			return( (OSS() << "<ufi> " << mValue.str()).str() );

		case WOBJECT_PROPERTY_SINGLE_QUOTE_STRING_KIND:
			return( (OSS() << "<sqs> " << mValue.str()).str() );

		case WOBJECT_PROPERTY_DOUBLE_QUOTE_STRING_KIND:
		case WOBJECT_PROPERTY_STRING_KIND:
			return( (OSS() << "<dqs> " << mValue.str()).str() );

		case WOBJECT_PROPERTY_KIND:
		default:
			return( mValue.str() );
	}
}



void WObject::strHeader(OutStream & os) const
{
	if( isWProperty() )
	{
		os << "property " << getNameID();

		if( hasReallyUnrestrictedName() )
		{
			os << " \"" << getUnrestrictedName() << "\"";
		}

		os << " = " << strPropertyValue();
	}

	else if( isWSequence() )
	{
		os << "sequence " << getNameID();

		if( hasReallyUnrestrictedName() )
		{
			os << " \"" << getUnrestrictedName() << "\"";
		}
	}

	else
	{
		os << "object";
		if( hasQualifiedTypeNameID() )
		{
			os << "< " << getQualifiedTypeNameID() << " >";
		}

		os << " " << ( hasFullyQualifiedNameID() ?
				getFullyQualifiedNameID() : getNameID() );

		if( hasReallyUnrestrictedName() )
		{
			os << " \"" << getUnrestrictedName() << "\"";
		}
	}
}


static std::string strSpecifierOperator(AVM_OPCODE opcode)
{
	switch( opcode )
	{
		case AVM_OPCODE_EQ   :   return( "="   );

		case AVM_OPCODE_NEQ  :   return( "!="  );
		case AVM_OPCODE_SEQ  :   return( "===" );
		case AVM_OPCODE_NSEQ :   return( "=/=" );

		case AVM_OPCODE_BAND :   return( "&=" );
		case AVM_OPCODE_BOR  :   return( "|=" );
		case AVM_OPCODE_BXOR :   return( "^=" );
		case AVM_OPCODE_BNOT :   return( "~=" );

		case AVM_OPCODE_PLUS :   return( "+=" );
		case AVM_OPCODE_MINUS:   return( "-=" );
		case AVM_OPCODE_MOD  :   return( "%=" );
		case AVM_OPCODE_MULT :   return( "*=" );
		case AVM_OPCODE_DIV  :   return( "/=" );

		case AVM_OPCODE_LTE  :   return( "<=" );
		case AVM_OPCODE_GTE  :   return( ">=" );

		case AVM_OPCODE_ASSIGN:  return( ":=" );

		case AVM_OPCODE_ASSIGN_MACRO:  return( "::=" );

		default:  return( "opcode#unknown" );
	}
}


void WObject::toStreamWProperty(OutStream & os) const
{
	os << TAB;// << getNameID();

// TRACE LINE
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PARSING )
	os << traceLine("", false) << " ";
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PARSING )

	os << getNameID();

	if( hasValue() )
	{
		if( getValue().is< AvmCode >() )
		{
			const AvmCode & aCode = getValue().to< AvmCode >();

			if( StatementTypeChecker::isSchedule(aCode) )
			{
				os << " = $" << IGNORE_FIRST_TAB;
				aCode.toStream(os);
			}
			else
			{
				os << " = ${" << EOL_INCR_INDENT;
				getValue().toStream(os);
				os << DECR_INDENT_TAB << "}";
			}
		}
		else
		{
			os << " " << strSpecifierOperator( mSpecifierOp );
			if( getValue().is< Operator >() )
			{
				getValue().to< Operator >().standardSymbol();
			}
			else if( isWPropertyWReference() )
			{
				os << " &" << getWReferenceValue()->getFullyQualifiedNameID();
			}
			else
			{
				os << " " << strPropertyValue();
			}
		}
	}
	else
	{
		os << " " << strPropertyValue();
	}


// TRACE LINE
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PARSING )
//	os << traceLine(" ");
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PARSING )

	AVM_DEBUG_REF_COUNTER(os);

	os << EOL_FLUSH;
}


void WObject::toStreamOwnedElement(OutStream & os,
		const std::string & beginDelimiter,
		const std::string & endDelimiter) const
{
	os << beginDelimiter;  AVM_DEBUG_REF_COUNTER(os);

// TRACE LINE
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PARSING )
	os << traceLine(" ");
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PARSING )

	os << EOL_INCR_INDENT;

	for( const auto & itElement : mOwnedElements )
	{
		if( itElement != nullptr )
		{
			if( itElement->getContainer() != this )
			{
				os << TAB << "&" << itElement
						->getFullyQualifiedNameID()
//				os << TAB << itElement->getNameID()
						<< EOL_FLUSH;
			}
			else
			{
				itElement->toStream(os);
			}
		}
		else
		{
			os << TAB << "nullptr" << EOL_FLUSH;
		}
	}

	os << DECR_INDENT_TAB << endDelimiter;

	// TRACE LINE
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PARSING )
	os << traceLine(" ");
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PARSING )
}




/**
 * return FullyQualifiedNameID + '.' aNameID
 */
std::string WObjectManager::makeFQN(
		const WObject * wfObject, const std::string & aNameID) const
{
	if( wfObject == WObject::_NULL_ )
	{
		return( aNameID );
	}
	else if( wfObject == &(ROOT_WOBJECT) )
	{
		return( ROOT_WOBJECT.getFullyQualifiedNameID() + aNameID );
	}
	else if( wfObject->isWTypedObject() )
	{
		return( wfObject->getFullyQualifiedNameID() + "." + aNameID );
	}
	else
	{
		const ObjectElement * aContainer = wfObject->getContainer();
		while( aContainer != nullptr )
		{
			if( aContainer->to_ptr< WObject >()->isWTypedObject() )
			{
				return( aContainer->getFullyQualifiedNameID()
						+ "." + aNameID );
			}

			aContainer = aContainer->getContainer();
		}
	}

	return( aNameID );
}



////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
// PROPERTY CREATION FACTORY
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////

/**
 * create Workflow-Property
 */
WObject * WObjectManager::newWPropertyExpression(WObject * wfContainer,
		const std::string & aNameID, const BF & value)
{
	WObject * wfObject = WObject::_NULL_;

	switch( value.classKind() )
	{
		case FORM_BUILTIN_BOOLEAN_KIND:
		{
			wfObject = new WObject( (*this), wfContainer,
					WObject::WOBJECT_PROPERTY_BOOLEAN_KIND, aNameID, value );

			break;
		}

		case FORM_BUILTIN_CHARACTER_KIND:
		{
			wfObject = new WObject( (*this), wfContainer,
					WObject::WOBJECT_PROPERTY_CHARACTER_KIND, aNameID, value );

			break;
		}

		case FORM_BUILTIN_INTEGER_KIND:
		{
			wfObject = new WObject( (*this), wfContainer,
					WObject::WOBJECT_PROPERTY_INTEGER_KIND, aNameID, value );

			break;
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			wfObject = new WObject( (*this), wfContainer,
					WObject::WOBJECT_PROPERTY_RATIONAL_KIND, aNameID, value );

			break;
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			wfObject = new WObject( (*this), wfContainer,
					WObject::WOBJECT_PROPERTY_FLOAT_KIND, aNameID, value );

			break;
		}

		case FORM_BUILTIN_STRING_KIND:
		{
			wfObject = new WObject( (*this), wfContainer,
					value.to< String >().isSingleQuote()
						? WObject::WOBJECT_PROPERTY_SINGLE_QUOTE_STRING_KIND
						: WObject::WOBJECT_PROPERTY_DOUBLE_QUOTE_STRING_KIND,
					aNameID, value );

			break;
		}

		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			wfObject = new WObject( (*this), wfContainer,
					WObject::WOBJECT_PROPERTY_IDENTIFIER_KIND, aNameID, value );

			break;
		}
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			wfObject = new WObject( (*this), wfContainer,
					WObject::WOBJECT_PROPERTY_QUALIFIED_IDENTIFIER_KIND,
					aNameID, value );

			break;
		}

		case FORM_UFI_KIND:
		{
			if( value.to< UniFormIdentifier >().isPureIdentifier() )
			{
				wfObject = new WObject( (*this), wfContainer,
						WObject::WOBJECT_PROPERTY_IDENTIFIER_KIND,
						aNameID, value );
			}
			else
			{
				wfObject = new WObject( (*this), wfContainer,
						WObject::WOBJECT_PROPERTY_UNIQ_FORM_IDENTIFIER_KIND,
						aNameID, value );
			}

			break;
		}

		case FORM_WOBJECT_KIND:
		{
			value.incrRefCount();

			wfObject = new WObject( (*this), wfContainer,
					aNameID, value.to_ptr< WObject >() );

			break;
		}

		case FORM_ARRAY_BOOLEAN_KIND:
		case FORM_ARRAY_CHARACTER_KIND:
		case FORM_ARRAY_INTEGER_KIND:
		case FORM_ARRAY_RATIONAL_KIND:
		case FORM_ARRAY_FLOAT_KIND:
		case FORM_ARRAY_STRING_KIND:
		case FORM_ARRAY_IDENTIFIER_KIND:
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:
		case FORM_ARRAY_BF_KIND:
		{
			wfObject = new WObject( (*this), wfContainer,
					WObject::WOBJECT_PROPERTY_ARRAY_KIND, aNameID, value );

			break;
		}

		case FORM_XFSP_VARIABLE_KIND:
		case FORM_INSTANCE_DATA_KIND:
		case FORM_AVMCODE_KIND:
		default:
		{
			wfObject = new WObject( (*this), wfContainer, aNameID, value );

			break;
		}
	}

	return( manage( wfObject ) );
}

WObject * WObjectManager::newWPropertyBoolean(WObject * wfContainer,
		const std::string & aNameID, bool aBooleanValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_BOOLEAN_KIND, aNameID,
			ExpressionConstructor::newBoolean(aBooleanValue) );

	return( manage( wfObject ) );
}

WObject * WObjectManager::newWPropertyCharacter(WObject * wfContainer,
		const std::string & aNameID, char aCharacterValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_CHARACTER_KIND, aNameID,
			ExpressionConstructor::newChar(aCharacterValue) );

	return( manage( wfObject ) );
}


WObject * WObjectManager::newWPropertyInteger(WObject * wfContainer,
		const std::string & aNameID, avm_integer_t anIntegerValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_INTEGER_KIND, aNameID,
			ExpressionConstructor::newInteger(anIntegerValue) );

	return( manage( wfObject ) );
}

WObject * WObjectManager::newWPropertyInteger(WObject * wfContainer,
		const std::string & aNameID, const std::string & anIntegerValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_INTEGER_KIND, aNameID,
			ExpressionConstructor::newInteger(anIntegerValue) );

	return( manage( wfObject ) );
}


WObject * WObjectManager::newWPropertyFloat(WObject * wfContainer,
		const std::string & aNameID, double aFloatValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_FLOAT_KIND, aNameID,
			ExpressionConstructor::newFloat(aFloatValue) );

	return( manage( wfObject ) );
}

WObject * WObjectManager::newWPropertyFloat(WObject * wfContainer,
		const std::string & aNameID, const std::string & aFloatValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_FLOAT_KIND, aNameID,
			ExpressionConstructor::newFloat(aFloatValue) );

	return( manage( wfObject ) );
}


WObject * WObjectManager::newWPropertySingleQuoteString(WObject * wfContainer,
		const std::string & aNameID, const std::string & aStringValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_SINGLE_QUOTE_STRING_KIND, aNameID,
			ExpressionConstructor::newSingleQuoteString(aStringValue) );

	return( manage( wfObject ) );
}

WObject * WObjectManager::newWPropertyDoubleQuoteString(WObject * wfContainer,
		const std::string & aNameID, const std::string & aStringValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_DOUBLE_QUOTE_STRING_KIND, aNameID,
			ExpressionConstructor::newDoubleQuoteString(aStringValue) );

	return( manage( wfObject ) );
}

WObject * WObjectManager::newWPropertyString(WObject * wfContainer,
		const std::string & aNameID, const std::string & aStringValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_DOUBLE_QUOTE_STRING_KIND, aNameID,
			ExpressionConstructor::newDoubleQuoteString(aStringValue) );

	return( manage( wfObject ) );
}


WObject * WObjectManager::newWPropertyIdentifier(WObject * wfContainer,
		const std::string & aNameID, const std::string & aStringValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_IDENTIFIER_KIND, aNameID,
			ExpressionConstructor::newIdentifier(aStringValue) );

	return( manage( wfObject ) );
}

WObject * WObjectManager::newWPropertyQualifiedIdentifier(WObject * wfContainer,
		const std::string & aNameID, const std::string & aStringValue)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_QUALIFIED_IDENTIFIER_KIND, aNameID,
			ExpressionConstructor::newQualifiedIdentifier(aStringValue) );

	return( manage( wfObject ) );
}

WObject * WObjectManager::newWPropertyUniFormIdentifier(WObject * wfContainer,
		const std::string & aNameID, UniFormIdentifier * anUFI)
{
	WObject * wfObject = new WObject( (*this), wfContainer,
			WObject::WOBJECT_PROPERTY_UNIQ_FORM_IDENTIFIER_KIND,
			aNameID, BF(anUFI) );

	return( manage( wfObject ) );
}


WObject * WObjectManager::newWPropertyParsedIdentifier(WObject * wfContainer,
		const std::string & aNameID, const BF & value)
{
	WObject * wfObject = getRegisteredWObject( value.str() );
	if( wfObject != WObject::_NULL_ )
	{
		return( newWPropertyReference(wfContainer, aNameID, wfObject) );
	}
	else
	{
		return( newWPropertyExpression(wfContainer, aNameID, value) );
	}

}


} /* namespace sep */

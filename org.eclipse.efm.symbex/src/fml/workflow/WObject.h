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

#ifndef FML_WORKFLOW_WOBJECT_H_
#define FML_WORKFLOW_WOBJECT_H_

#include <fml/common/ObjectElement.h>
#include <fml/workflow/WPropertyImpl.h>

#include <common/AvmPointer.h>
#include <common/BF.h>

#include <collection/Vector.h>

//#include <fml/builtin/Identifier.h>
//#include <fml/builtin/QualifiedIdentifier.h>
//#include <fml/builtin/String.h>
//
//#include <fml/numeric/Float.h>
//#include <fml/numeric/Integer.h>
//#include <fml/numeric/Rational.h>

#include <fml/operator/OperatorLib.h>

#include <util/avm_string.h>

#include <map>


namespace sep
{

class BuiltinForm;

class Operator;

class PairOutStream;

class Query;
class WObject;
class WObjectManager;

class UniFormIdentifier;


////////////////////////////////////////////////////////////////////////////////
// SYSTEM SMART POINTER
////////////////////////////////////////////////////////////////////////////////

class WObject :
	public ObjectElement,
	public WPropertyImpl,
	AVM_INJECT_INSTANCE_COUNTER_CLASS( WObject )
{

	friend class Query;
	friend class WObjectManager;

	AVM_DECLARE_CLONABLE_CLASS( WObject )

public:
	/**
	 * TYPEDEF
	 */
	typedef Vector< WObject * >                  TableOfOwnedElement;

	typedef TableOfOwnedElement::const_iterator  const_iterator;

protected:
	/**
	 * ENUM
	 */
	enum ENUM_WOBJECT_KIND
	{
		// UNDEFINED
		WOBJECT_UNDEFINED_KIND                     = 0x000,


		WOBJECT_PROPERTY_BOOLEAN_KIND              = 0x001,

		WOBJECT_PROPERTY_CHARACTER_KIND            = 0x002,

		WOBJECT_PROPERTY_INTEGER_KIND              = 0x003,

		WOBJECT_PROPERTY_RATIONAL_KIND             = 0x004,

		WOBJECT_PROPERTY_FLOAT_KIND                = 0x005,


		WOBJECT_PROPERTY_IDENTIFIER_KIND           = 0x006,

		WOBJECT_PROPERTY_QUALIFIED_IDENTIFIER_KIND = 0x007,

		WOBJECT_PROPERTY_UNIQ_FORM_IDENTIFIER_KIND = 0x008,


		WOBJECT_PROPERTY_OPERATOR_KIND             = 0x009,

		WOBJECT_PROPERTY_ARRAY_KIND                = 0x00A,


		WOBJECT_PROPERTY_SINGLE_QUOTE_STRING_KIND  = 0x010,

		WOBJECT_PROPERTY_DOUBLE_QUOTE_STRING_KIND  = 0x020,

		WOBJECT_PROPERTY_STRING_KIND = WOBJECT_PROPERTY_SINGLE_QUOTE_STRING_KIND
		                             | WOBJECT_PROPERTY_DOUBLE_QUOTE_STRING_KIND,


		WOBJECT_PROPERTY_WREFERENCE_KIND           = 0x040,

		WOBJECT_PROPERTY_KIND                      = 0x0FF,


		WOBJECT_SEQUENCE_KIND                      = 0x100,

		WOBJECT_SEQUENCE_OR_REFERENCE_KIND = WOBJECT_SEQUENCE_KIND
		                                   | WOBJECT_PROPERTY_WREFERENCE_KIND,

		WOBJECT_TYPED_KIND                         = 0x200,

		WOBJECT_TYPED_OR_REFERENCE_KIND    = WOBJECT_TYPED_KIND
		                                   | WOBJECT_PROPERTY_WREFERENCE_KIND,

		WOBJECT_TYPED_OR_SEQUENCE_KIND     = WOBJECT_TYPED_KIND
		                                   | WOBJECT_SEQUENCE_KIND,

	};


public:
	/**
	 * STATIC ATTRIBUTE
	 */
	static WObject * _NULL_;

	static const std::string & FML_FQN_SCHEME;

	static const std::string & FML_FQN_ROOT;

	static const std::string & SEW_FQN_SCHEME;

	static const std::string & SEW_FQN_ROOT;


protected:
	/**
	 * ATTRIBUTES
	 */
	WObjectManager & mWObjectManager;

	ENUM_WOBJECT_KIND mKind;

	std::string mQualifiedTypeNameID;

	TableOfOwnedElement mOwnedElements;

	// WORKFLOW-PROPERTY VALUE
	AVM_OPCODE mSpecifierOp;

	union
	{
		Operator * mOperatorValue;

		WObject  * mWOjectReferenceValue;
	};

	BF mValue;




protected:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WObject(WObjectManager & aWObjectManager, WObject * wfContainer,
			ENUM_WOBJECT_KIND aKind, const std::string & aNameID)
	: ObjectElement( CLASS_KIND_T( WObject ) , wfContainer , aNameID ),
	mWObjectManager( aWObjectManager ),
	mKind( aKind ),
	mQualifiedTypeNameID( ),
	mOwnedElements( ),
	mSpecifierOp( AVM_OPCODE_EQ ),

	mValue( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Workflow-Property
	 */
	WObject(WObjectManager & aWObjectManager, WObject * wfContainer,
			const std::string & aNameID, const BF & aValue)
	: ObjectElement( CLASS_KIND_T( WObject ) , wfContainer , aNameID ),
	mWObjectManager( aWObjectManager ),
	mKind( WOBJECT_PROPERTY_KIND ),
	mQualifiedTypeNameID( ),
	mOwnedElements( ),
	mSpecifierOp( AVM_OPCODE_EQ ),

	mValue( aValue )
	{
		//!! NOTHING
	}

	WObject(WObjectManager & aWObjectManager, WObject * wfContainer,
			const std::string & aNameID, AVM_OPCODE anOp, const BF & aValue)
	: ObjectElement( CLASS_KIND_T( WObject ) , wfContainer , aNameID ),
	mWObjectManager( aWObjectManager ),
	mKind( WOBJECT_PROPERTY_KIND ),
	mQualifiedTypeNameID( ),
	mOwnedElements( ),
	mSpecifierOp( anOp ),

	mValue( aValue )
	{
		//!! NOTHING
	}

	WObject(WObjectManager & aWObjectManager, WObject * wfContainer,
			ENUM_WOBJECT_KIND aKind, const std::string & aNameID,
			const BF & aValue)
	: ObjectElement( CLASS_KIND_T( WObject ) , wfContainer , aNameID ),
	mWObjectManager( aWObjectManager ),
	mKind( aKind ),
	mQualifiedTypeNameID( ),
	mOwnedElements( ),
	mSpecifierOp( AVM_OPCODE_EQ ),

	mValue( aValue )
	{
		//!! NOTHING
	}

	WObject(WObjectManager & aWObjectManager, WObject * wfContainer,
			const std::string & aNameID, Operator * anOperator)
	: ObjectElement( CLASS_KIND_T( WObject ) , wfContainer , aNameID ),
	mWObjectManager( aWObjectManager ),
	mKind( WOBJECT_PROPERTY_OPERATOR_KIND ),
	mQualifiedTypeNameID( ),
	mOwnedElements( ),
	mSpecifierOp( AVM_OPCODE_EQ ),

	mOperatorValue( anOperator ),
	mValue( )
	{
		//!! NOTHING
	}

	WObject(WObjectManager & aWObjectManager, WObject * wfContainer,
			const std::string & aNameID, WObject * aWOjectReference)
	: ObjectElement( CLASS_KIND_T( WObject ) , wfContainer , aNameID ),
	mWObjectManager( aWObjectManager ),
	mKind( WOBJECT_PROPERTY_WREFERENCE_KIND ),
	mQualifiedTypeNameID( ),
	mOwnedElements( ),
	mSpecifierOp( AVM_OPCODE_EQ ),

	mWOjectReferenceValue( aWOjectReference ),
	mValue( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Typed WObject
	 */
	WObject(WObjectManager & aWObjectManager, WObject * wfContainer,
			const std::string & aNameID, const std::string & aTypeNameID)
	: ObjectElement( CLASS_KIND_T( WObject ) , wfContainer , aNameID ),
	mWObjectManager( aWObjectManager ),
	mKind( WOBJECT_TYPED_KIND ),
	mQualifiedTypeNameID( aTypeNameID ),
	mOwnedElements( ),
	mSpecifierOp( AVM_OPCODE_EQ ),

	mValue( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	explicit WObject(const WObject & anObject)
	: ObjectElement( anObject ),
	mWObjectManager( anObject.mWObjectManager ),
	mKind( anObject.mKind ),
	mQualifiedTypeNameID( anObject.mQualifiedTypeNameID ),
	mOwnedElements( anObject.mOwnedElements ),
	mSpecifierOp( anObject.mSpecifierOp ),

	mWOjectReferenceValue( anObject.mWOjectReferenceValue ),
	mValue( anObject.mValue )
	{
		//!! NOTHING
	}

public:
	/**
	 * DESTRUCTOR
	 */
	virtual ~WObject()
	{
		// See WObjectManager::destroyManagedElement
//		destroyOwnedElement();
	}

	/**
	 * DESTROY
	 */
	void destroyOwnedElement();


	/**
	 * TEST
	 * mKind
	 */
	inline bool isKind(ENUM_WOBJECT_KIND aKind) const
	{
		return( (mKind == aKind)
				|| ((aKind == WOBJECT_PROPERTY_KIND)
					&& (mKind < aKind))
				|| ((aKind == WOBJECT_PROPERTY_STRING_KIND)
					&& ((mKind & aKind) != 0)) );
	}

	/**
	 * TEST
	 * mKind for Composite
	 */
	inline bool isWTypedObject() const
	{
		return( mKind == WOBJECT_TYPED_KIND );
	}

	inline bool isWTypedOrReference() const
	{
		return( (mKind & WOBJECT_TYPED_OR_REFERENCE_KIND) != 0 );
	}

	inline bool isWTypedOrSequence() const
	{
		return( (mKind & WOBJECT_TYPED_OR_SEQUENCE_KIND) != 0 );
	}


	inline bool isWSequence() const
	{
		return( mKind == WOBJECT_SEQUENCE_KIND );
	}

	inline bool isWSequenceOrReference() const
	{
		return( (mKind & WOBJECT_SEQUENCE_OR_REFERENCE_KIND) != 0 );
	}


	inline bool isRegexWSequence(const std::string & aRegexSequenceID) const
	{
		return( (mKind == WOBJECT_SEQUENCE_KIND)
				&& REGEX_MATCH(getNameID(), aRegexSequenceID) );
	}

	/**
	 * TEST
	 * mKind for Property
	 */
	inline bool isWProperty() const
	{
		return( mKind <= WOBJECT_PROPERTY_KIND );
	}

	inline bool isWPropertyboolean() const
	{
		return( mKind == WOBJECT_PROPERTY_BOOLEAN_KIND );
	}

	inline bool isWPropertyCharacter() const
	{
		return( mKind == WOBJECT_PROPERTY_CHARACTER_KIND );
	}

	inline bool isWPropertyInteger() const
	{
		return( mKind == WOBJECT_PROPERTY_INTEGER_KIND );
	}

	inline bool isWPropertyRational() const
	{
		return( mKind == WOBJECT_PROPERTY_RATIONAL_KIND);
	}

	inline bool isWPropertyFloat() const
	{
		return( mKind == WOBJECT_PROPERTY_FLOAT_KIND );
	}

	inline bool isWPropertyIdentifier() const
	{
		return( mKind == WOBJECT_PROPERTY_IDENTIFIER_KIND );
	}

	inline bool isWPropertyQualifiedIdentifier() const
	{
		return( mKind == WOBJECT_PROPERTY_QUALIFIED_IDENTIFIER_KIND );
	}

	inline bool isWPropertyUFI() const
	{
		return( mKind == WOBJECT_PROPERTY_UNIQ_FORM_IDENTIFIER_KIND );
	}

	inline bool isWPropertyOperator() const
	{
		return( mKind == WOBJECT_PROPERTY_OPERATOR_KIND );
	}

	inline bool isWPropertyWReference() const
	{
		return( mKind == WOBJECT_PROPERTY_WREFERENCE_KIND );
	}

	inline bool isWPropertyArray() const
	{
		return( mKind == WOBJECT_PROPERTY_ARRAY_KIND );
	}

	inline bool isWPropertySingleQuoteString() const
	{
		return( mKind == WOBJECT_PROPERTY_SINGLE_QUOTE_STRING_KIND );
	}

	inline bool isWPropertyDoubleQuoteString() const
	{
		return( mKind == WOBJECT_PROPERTY_DOUBLE_QUOTE_STRING_KIND );
	}

	inline bool isWPropertyString() const
	{
		return( (mKind & WOBJECT_PROPERTY_STRING_KIND) != 0 );
	}


	/**
	 * GETTER
	 * mQualifiedTypeNameID
	 */
	inline const std::string & getQualifiedTypeNameID() const
	{
		return( mQualifiedTypeNameID );
	}

	inline bool hasQualifiedTypeNameID() const
	{
		return( not mQualifiedTypeNameID.empty() );
	}

	inline bool isWTypedID(const std::string & aQualifiedNameID) const
	{
		return( mQualifiedTypeNameID == aQualifiedNameID );
	}

	inline void setQualifiedTypeNameID(const std::string & aQualifiedNameID)
	{
		mQualifiedTypeNameID = aQualifiedNameID;
	}

	inline std::string strType() const
	{
		return( mQualifiedTypeNameID );
	}

	inline const std::string & strT() const
	{
		return( mQualifiedTypeNameID );
	}


	/**
	 * GETTER
	 * mSpecifierOp
	 */
	inline AVM_OPCODE getSpecifierOp() const
	{
		return( mSpecifierOp );
	}

	inline void setSpecifierOp(AVM_OPCODE aSpecifierOp)
	{
		mSpecifierOp = aSpecifierOp;
	}


	/**
	 * GETTER - SETTER
	 * mOwnedElements
	 */
	inline const TableOfOwnedElement & getOwnedElement() const
	{
		return( mOwnedElements );
	}

	inline bool hasOwnedElement() const
	{
		return( mOwnedElements.nonempty() );
	}

	inline bool hasnoOwnedElement() const
	{
		return( mOwnedElements.empty() );
	}

	inline avm_size_t ownedSize() const
	{
		return( mOwnedElements.size() );
	}


	inline void append(WObject * wfElement)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( wfElement )
				<< "element !!!"
				<< SEND_EXIT;

// Set by the WObjectManager !
//		wfElement->setOffset( mOwnedElements.size() );

		mOwnedElements.append(wfElement);

		if( wfElement->getContainer() == this )
		{
			//!! NOTHING
		}
		else if( wfElement->getContainer() != NULL )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected WObject <" << wfElement->strUniqId()
					<< "> with container <" << this->strUniqId()
					<< "> where old container is <"
					<< wfElement->getContainer()->to< WObject >()->strUniqId()
					<< ">"
					<< SEND_EXIT;
		}
	}

	/**
	 * GETTER - SETTER
	 * mOwnedElements [const] iterator
	 */
	inline const_iterator owned_begin() const
	{
		return( mOwnedElements.begin() );
	}

	inline const_iterator owned_end() const
	{
		return( mOwnedElements.end() );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// PROPERTY GETTER - SETTER
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	/**
	 * GETTER - SETTER
	 * mWOjectReferenceValue
	 */
	inline WObject * getWReferenceValue() const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isWPropertyWReference() )
				<< "WObject << " << strPropertyValue()
				<< " >> is not a Property WReference !"
				<< SEND_EXIT;
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mWOjectReferenceValue )
				<< "WOject reference value as alias < " << strUniqId() << " > !"
				<< SEND_EXIT;

		return( mWOjectReferenceValue );
	}

	/**
	 * GETTER - SETTER
	 * mOperatorValue
	 */
	inline Operator * getOperatorValue() const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isWPropertyWReference() )
				<< "WObject << " << strPropertyValue()
				<< " >> is not a Property WReference !"
				<< SEND_EXIT;
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mWOjectReferenceValue )
				<< "WOject reference value as alias < " << strUniqId() << " > !"
				<< SEND_EXIT;

		return( mOperatorValue );
	}


	/**
	 * GETTER - SETTER
	 * mValue
	 */
	inline const BF & getValue() const
	{
		return( mValue );
	}

	inline bool hasValue() const
	{
		return( mValue.valid() );
	}

	inline void setValue(const BF & aValue)
	{
		mValue = aValue;
	}

	/**
	 * FACTORY
	 * container of WObject
	 * !UNUSED!*
	WObject * container() const;

	WObject * sequenceContainerOf() const;
	* !UNUSED!
	*/

	const WObject * objectContainer() const;

	/**
	 * Serialization
	 */
	inline std::string strUniqId() const
	{
		return( (isWProperty() ? "wpro:" : (isWSequence() ? "wseq:" : ""))
				+ ( hasFullyQualifiedNameID() ? getFullyQualifiedNameID()
					: ( hasNameID() ? getNameID()
						: ( hasUnrestrictedName()
							? ("'" + getUnrestrictedName() + "'")
							: ( hasQualifiedTypeNameID()
								? (mQualifiedTypeNameID + ".<anonym>")
								: "<null-wobject-id>" ) ) ) ) );
	}

	// str Property Value
	std::string strPropertyValue() const;

	/**
	 * Serialisation
	 */
	inline virtual std::string str() const
	{
		return( strUniqId() );
	}


	inline virtual std::string strHeader() const
	{
		StringOutStream oss;

		strHeader( oss );

		return( oss.str() );
	}

	virtual void strHeader(OutStream & os) const;

	inline virtual void toStream(OutStream & os) const
	{
		if( isWProperty() )
		{
			toStreamWProperty(os);
		}
		else if( isWSequence() )
		{
			toStreamWSequence(os);
		}
		else
		{
			toStreamWObject(os);
		}
	}

	void toStreamWProperty(OutStream & os) const;

	inline void toStreamWSequence(OutStream & os) const
	{
		os << TAB/* << "sequence "*/ << getNameID();// << ":";

		if( hasReallyUnrestrictedName() )
		{
			os << " '" << getUnrestrictedName() << "'";
		}

		toStreamOwnedElement( os << " " , "[" , "] // " + getNameID() );

		os << EOL_FLUSH;
	}

	inline void toStreamWObject(OutStream & os) const
	{
		os << TAB;

		if( hasQualifiedTypeNameID() )
		{
			os << getQualifiedTypeNameID() << " ";
		}

		os << getFullyQualifiedNameID(); //or getNameID();

		if( hasReallyUnrestrictedName() )
		{
			os << " '" << getUnrestrictedName() << "'";
		}

		toStreamOwnedElement( os << " " , "{" , "} // " + getNameID() );

		os << EOL_FLUSH;
	}


	void toStreamOwnedElement(OutStream & os,
			const std::string & beginDelimiter = "{",
			const std::string & endDelimiter = "}" ) const;

};


class WObjectManager
{

protected:
	/**
	 * ATTRIBUTE
	 */
	Vector< WObject * >  mTableOfManagedElement;

	std::map< std::string , WObject * > mTableOfRegisteredWObject;

public:
	WObject ROOT_WOBJECT;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WObjectManager(const std::string & fqnRoot)
	: mTableOfManagedElement( ),
	mTableOfRegisteredWObject( ),
	ROOT_WOBJECT( *this , NULL, "virtual#root", "virtual#root" )
	{
		ROOT_WOBJECT.mFullyQualifiedNameID = fqnRoot;
	}

	/**
	 * DESTRUCTOR
	 * mOwnedElements
	 */
	virtual ~WObjectManager()
	{
		destroyManagedElement();
	}

	/**
	 * DESTROY
	 */
	void destroyManagedElement();

	/**
	 * return FullyQualifiedNameID + '.' aNameID
	 */
	std::string makeFQN(WObject * wfObject, const std::string & aNameID) const;


	/**
	 * Manage WObject
	 */
	inline WObject * manage(WObject * wfObject)
	{
		if( wfObject != WObject::_NULL_ )
		{
			wfObject->setOffset( mTableOfManagedElement.size() );

			mTableOfManagedElement.append( wfObject );
		}

		return( wfObject );
	}

	/**
	 * Registered WObject
	 */
	inline WObject * getRegisteredWObject(const std::string & key)
	{
		return( mTableOfRegisteredWObject[ key ] );
	}

	inline BF bfRegisteredWObject(const std::string & key)
	{
		return( toBF( mTableOfRegisteredWObject[ key ] ) );
	}


	inline void registerWObject(WObject * wfObject, const std::string & key)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( wfObject ) << "WObject !!!"
				<< SEND_EXIT;

		mTableOfRegisteredWObject[ key ] = wfObject;
	}

	inline void registerWObject(WObject * wfObject)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( wfObject ) << "WObject !!!"
				<< SEND_EXIT;

		mTableOfRegisteredWObject[
				wfObject->getFullyQualifiedNameID() ] = wfObject;
	}


	/**
	 * Cast
	 */
	inline static bool is(const BF & anElement)
	{
		return( anElement.is< WObject >() );
	}

	inline static WObject * from(const BF & anElement)
	{
		return( anElement.to_ptr< WObject >() );
	}

	inline static BF toBF(WObject * wfObject)
	{
		if( wfObject != WObject::_NULL_ )
		{
			wfObject->ObjectElement::incrRefCount();
		}

		return( BF( wfObject ) );
	}


	/**
	 * FACTORY
	 * create WObject
	 */
	inline WObject * newWObject(WObject * wfContainer,
			const std::string & aNameID)
	{
		WObject * wfObject = new WObject( (*this), wfContainer,
				WObject::WOBJECT_TYPED_KIND, aNameID );

		return( manage( wfObject ) );
	}


	inline WObject * newWObject(WObject * wfContainer,
			const std::string & aNameID, const std::string & aTypeNameID)
	{
		WObject * wfObject = new WObject( (*this), wfContainer,
				aNameID, aTypeNameID );

		return( manage( wfObject ) );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// PROPERTY CREATION FACTORY
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	inline WObject * newWPropertyOperator(WObject * wfContainer,
			const std::string & aNameID, Operator * anOperator)
	{
		WObject * wfObject = new WObject( (*this), wfContainer,
				aNameID, anOperator );

		return( manage( wfObject ) );
	}

	inline WObject * newWPropertyReference(WObject * wfContainer,
			const std::string & aNameID, WObject * aWOjectReference)
	{
		WObject * wfObject = new WObject( (*this), wfContainer,
				aNameID, aWOjectReference );

		return( manage( wfObject ) );
	}

	inline WObject * newWPropertyArray(WObject * wfContainer,
			const std::string & aNameID, const BF & value)
	{
		WObject * wfObject = new WObject( (*this), wfContainer,
				WObject::WOBJECT_PROPERTY_ARRAY_KIND, aNameID, value );

		return( manage( wfObject ) );
	}


	inline WObject * newWProperty(
			WObject * wfContainer, const std::string & aNameID)
	{
		WObject * wfObject = new WObject( (*this), wfContainer,
				WObject::WOBJECT_PROPERTY_KIND, aNameID );

		return( manage( wfObject ) );
	}

	inline WObject * newWProperty(
			WObject * wfContainer, const std::string & aNameID,
			AVM_OPCODE aSpecifierOp, const BF & value)
	{
		WObject * wfObject = new WObject( (*this), wfContainer,
				aNameID, aSpecifierOp, value );

		return( manage( wfObject ) );
	}


	inline WObject * newWProperty(WObject * wfContainer,
			const std::string & aNameID, const BF & value)
	{
		WObject * wfObject = new WObject( (*this), wfContainer,
				WObject::WOBJECT_PROPERTY_KIND, aNameID, value );

		return( manage( wfObject ) );
	}

	inline WObject * newWProperty(WObject * wfContainer,
			WObject::ENUM_WOBJECT_KIND aKind,
			const std::string & aNameID, const BF & value)
	{
		WObject * wfObject = new WObject( (*this), wfContainer,
				aKind, aNameID, value );

		return( manage( wfObject ) );
	}

	WObject * newWPropertyExpression(WObject * wfContainer,
			const std::string & aNameID, const BF & value);


	WObject * newWPropertyBoolean(WObject * wfContainer,
			const std::string & aNameID, bool aBooleanValue);

	WObject * newWPropertyCharacter(WObject * wfContainer,
			const std::string & aNameID, char aCharacterValue);

	WObject * newWPropertyInteger(WObject * wfContainer,
			const std::string & aNameID, avm_integer_t anIntegerValue);

	WObject * newWPropertyInteger(WObject * wfContainer,
			const std::string & aNameID, const std::string & anIntegerValue);

	WObject * newWPropertyFloat(WObject * wfContainer,
			const std::string & aNameID, double aFloatValue);

	WObject * newWPropertyFloat(WObject * wfContainer,
			const std::string & aNameID, const std::string & aFloatValue);

	WObject * newWPropertySingleQuoteString(WObject * wfContainer,
			const std::string & aNameID, const std::string & aStringValue);

	WObject * newWPropertyDoubleQuoteString(WObject * wfContainer,
			const std::string & aNameID, const std::string & aStringValue);

	WObject * newWPropertyString(WObject * wfContainer,
			const std::string & aNameID, const std::string & aStringValue);


	WObject * newWPropertyIdentifier(WObject * wfContainer,
			const std::string & aNameID, const std::string & aStringValue);

	WObject * newWPropertyQualifiedIdentifier(WObject * wfContainer,
			const std::string & aNameID, const std::string & aStringValue);


	WObject * newWPropertyUniFormIdentifier(WObject * wfContainer,
			const std::string & aNameID, UniFormIdentifier * anUFI);


	WObject * newWPropertyParsedIdentifier(WObject * wfContainer,
			const std::string & aNameID, const BF & value);


	/**
	 * FACTORY
	 * create Group old Section
	 */
	inline WObject * newWSequence(WObject * wfContainer,
			const std::string & aNameID)
	{
		WObject * wfObject = new WObject( (*this), wfContainer,
				WObject::WOBJECT_SEQUENCE_KIND, aNameID );

		return( manage( wfObject ) );
	}

};


} /* namespace sep */

#endif /* FML_WORKFLOW_WOBJECT_H_ */

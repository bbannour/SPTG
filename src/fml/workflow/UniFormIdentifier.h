/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#ifndef UFI_H_
#define UFI_H_

#include <common/NamedElement.h>
#include <fml/common/TraceableElement.h>

#include <fml/common/ObjectElement.h>

#include <base/ClassKindInfo.h>
#include <common/BF.h>

#include <fml/builtin/Identifier.h>
#include <collection/List.h>


namespace sep
{

class Element;


typedef std::uint8_t         avm_ufi_scheme_t;

enum {
	UFI_SCHEME_UNDEFINED  = 0x00,

	UFI_SCHEME_MACHINE    = 0x01,
	UFI_SCHEME_INSTANCE   = 0x02,
	UFI_SCHEME_PORT       = 0x04,
	UFI_SCHEME_BUFFER     = 0x08,
	UFI_SCHEME_VARIABLE   = 0x10,
//	UFI_SCHEME_CONNECTOR = 0x20,

	UFI_SCHEME_INVOKABLE  = 0x20,

	UFI_SCHEME_FIELD      = UFI_SCHEME_MACHINE
	                      | UFI_SCHEME_INSTANCE
	                      | UFI_SCHEME_PORT
	                      | UFI_SCHEME_BUFFER
	                      | UFI_SCHEME_VARIABLE,
//	                      | UFI_SCHEME_CONNECTOR,
//	                      | UFI_SCHEME_INVOKABLE,


	UFI_SCHEME_INDEX      = 0x40,

	UFI_SCHEME_ARRAY      = UFI_SCHEME_INDEX,


	UFI_SCHEME_PARAMETER  = 0x80,


	UFI_SCHEME_ARGUMENT   = UFI_SCHEME_ARRAY
	                      | UFI_SCHEME_PARAMETER,


	UFI_SCHEME_HYBRID     = UFI_SCHEME_FIELD
	                      | UFI_SCHEME_INDEX
						  | UFI_SCHEME_ARRAY,

	UFI_SCHEME_MASK_ALL   = 0xFF
};



class UfiField final :  public BF
{

public:
	/**
	 * ATTRIBUTE
	 */
	avm_ufi_scheme_t scheme;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	UfiField(const BF & bf, avm_ufi_scheme_t aScheme)
	: BF( bf ),
	scheme( aScheme )
	{
		// NOTHING
	}

	UfiField(Element * bf, avm_ufi_scheme_t aScheme)
	: BF( bf ),
	scheme( aScheme )
	{
		// NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	UfiField(const UfiField & atom)
	: BF( atom ),
	scheme( atom.scheme )
	{
		// NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~UfiField()
	{
		//!! NOTHING
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	inline bool operator==(const UfiField & other) const
	{
		return( (scheme == other.scheme) && (*this == other) );
	}

	inline bool operator!=(const UfiField & other) const
	{
		return( (scheme != other.scheme) || (*this != other) );
	}


	/**
	 * GETTER - SETTER
	 * for mScheme
	 */
	inline void addScheme(avm_ufi_scheme_t aScheme)
	{
		scheme |= aScheme;
	}

	inline avm_ufi_scheme_t getScheme() const
	{
		return( scheme );
	}

	inline bool isFieldIndex() const
	{
		return( scheme & UFI_SCHEME_INDEX );
	}

	inline bool isFieldMachine() const
	{
		return( scheme & UFI_SCHEME_MACHINE );
	}

	inline bool isFieldBuffer() const
	{
		return( scheme & UFI_SCHEME_BUFFER );
	}

	inline bool isFieldPort() const
	{
		return( scheme & UFI_SCHEME_PORT );
	}

	inline bool isFieldVariable() const
	{
		return( scheme & UFI_SCHEME_VARIABLE );
	}

	inline bool isFieldInvokable() const
	{
		return( scheme & UFI_SCHEME_INVOKABLE );
	}

	inline bool isFieldParameter() const
	{
		return( scheme & UFI_SCHEME_PARAMETER );
	}


	inline void setScheme(avm_ufi_scheme_t aScheme)
	{
		scheme = aScheme;
	}

};


class UniFormIdentifier final :
		public NamedElement,
		public TraceableElement,
		public List< UfiField >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( UniFormIdentifier )
{

	AVM_DECLARE_CLONABLE_CLASS( UniFormIdentifier )


public:
	typedef List< UfiField >    ListOfField;


	static BF ANONYM_LOCATION;

	static std::string SEPARATOR_ID;
	static std::string SEPARATOR_LOCATION;
	static std::string SEPARATOR_LOCATOR;


protected:
	/**
	 * ATTRIBUTES
	 */
	avm_ufi_scheme_t mScheme;

	BF mLocator;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	UniFormIdentifier(bool anonymLocation)
	: NamedElement( CLASS_KIND_T( UniFormIdentifier ) ),
	TraceableElement( ),
	ListOfField( ),
	mScheme( UFI_SCHEME_UNDEFINED ),
	mLocator( ( anonymLocation )? ANONYM_LOCATION : BF::REF_NULL )
	{
		//!! NOTHING
	}

	UniFormIdentifier(const BF & aLocator)
	: NamedElement( CLASS_KIND_T( UniFormIdentifier ) ),
	TraceableElement( ),
	ListOfField( ),
	mScheme( UFI_SCHEME_UNDEFINED ),
	mLocator( aLocator )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	UniFormIdentifier(const std::string & aQualifiedNameID)
	: NamedElement( CLASS_KIND_T( UniFormIdentifier ), aQualifiedNameID ),
	TraceableElement( ),
	ListOfField( ),
	mScheme( UFI_SCHEME_UNDEFINED ),
	mLocator( )
	{
		build( aQualifiedNameID );
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	UniFormIdentifier(const UniFormIdentifier & anUFI)
	: NamedElement( anUFI ),
	TraceableElement( anUFI ),
	ListOfField( anUFI ),
	mScheme( anUFI.mScheme ),
	mLocator( anUFI.mLocator )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~UniFormIdentifier()
	{
		//!! NOTHING
	}


	/**
	 * BUILD FROM QUALIFIED NAME ID
	 */
	void build(const std::string & aQualifiedNameID);

	/**
	 * LOADER - DISPOSER
	 */
	static void load();
	static void dispose();


	/**
	 * ListOfField
	 */
	inline virtual std::size_t size() const override
	{
		return( ListOfField::size() );
	}


	/**
	 * GETTER - SETTER
	 * for mScheme
	 */
	inline void addScheme(avm_ufi_scheme_t aScheme)
	{
		mScheme |= aScheme;
	}


	inline avm_ufi_scheme_t getScheme() const
	{
		return( mScheme );
	}

	inline bool hasScheme() const
	{
		return( mScheme != UFI_SCHEME_UNDEFINED );
	}

	inline bool isScheme(avm_ufi_scheme_t aScheme) const
	{
		return( (mScheme & aScheme) == aScheme );
	}


	inline bool isFields() const
	{
		return( (mScheme & (UFI_SCHEME_ARGUMENT)) == 0 );
	}

	inline bool isAbsoluteFullFields() const
	{
		return( (mLocator.valid()
					|| (nonempty() && first().is< ObjectElement >()))
				&& ((mScheme & UFI_SCHEME_ARGUMENT) == 0) );
	}

	inline bool isFullOffset() const
	{
		return( (mScheme & UFI_SCHEME_PARAMETER) == 0 );
	}

	inline bool hasArray() const
	{
		return( mScheme & UFI_SCHEME_ARRAY );
	}

	inline bool hasInvokable() const
	{
		return( mScheme & UFI_SCHEME_INVOKABLE );
	}

	inline bool hasParameter() const
	{
		return( mScheme & UFI_SCHEME_PARAMETER );
	}


	inline void setScheme(avm_ufi_scheme_t aScheme)
	{
		mScheme = aScheme;
	}



	/**
	 * GETTER - SETTER
	 * for mLocator
	 */
	inline BF & getLocator()
	{
		return( mLocator );
	}

	inline const BF & getLocator() const
	{
		return( mLocator );
	}

	inline bool hasLocator() const
	{
		return( mLocator.valid() );
	}


	void setLocator(const std::string & aLocationId);

//	inline void setLocator(const BF & aLocation)
//	{
//		mLocator = aLocation;
//	}


	inline bool isAnonymLocation() const
	{
		return( mLocator.isTEQ( ANONYM_LOCATION ) );
	}

	inline void setAnonymLocation()
	{
		mLocator = ANONYM_LOCATION;
	}

	inline void setAbsolute()
	{
		if( not hasLocator() )
		{
			setAnonymLocation();
		}
	}


	/**
	 * GETTER - SETTER
	 * FIELD UNDEFINED
	 */
	inline void appendUndef(const BF & field)
	{
		ListOfField::append( UfiField(field, UFI_SCHEME_UNDEFINED) );
	}

	/**
	 * GETTER - SETTER
	 * FIELD INDEX
	 */
	inline void appendIndex(const BF & idx)
	{
		ListOfField::append( UfiField(idx, UFI_SCHEME_INDEX) );
		mScheme |= UFI_SCHEME_ARRAY;
	}


	/**
	 * GETTER - SETTER
	 * FIELD
	 */
	inline void updateAllNameID()
	{
		const std::string strID = str();

		setAllNameID( strID , strID , strID );
	}



	inline void appendField(Element * field, avm_ufi_scheme_t scheme)
	{
		ListOfField::append( UfiField(field, scheme) );
		mScheme |= scheme;

		updateAllNameID();
	}

	inline void appendField(const BF & field, avm_ufi_scheme_t scheme)
	{
		ListOfField::append( UfiField(field, scheme) );
		mScheme |= scheme;

		updateAllNameID();
	}

	void appendField(const std::string & aQualifiedNameID,
			avm_ufi_scheme_t scheme);

	void appendField(const BF & field);

	inline void appendField(const std::string & aQualifiedNameID)
	{
		appendField( aQualifiedNameID , UFI_SCHEME_FIELD );
	}


	/**
	 * GETTER - SETTER
	 * FIELD MACHINE
	 */
	inline void appendFieldMachine(const BF & field)
	{
		appendField( field , UFI_SCHEME_MACHINE );
	}

	inline void appendFieldMachine(const std::string & aQualifiedNameID)
	{
		appendField( aQualifiedNameID , UFI_SCHEME_MACHINE );
	}


	/**
	 * GETTER - SETTER
	 * FIELD VARIABLE
	 */
	inline void appendFieldVariable(const BF & field)
	{
		appendField( field , UFI_SCHEME_VARIABLE );
	}

	inline void appendFieldVariable(const std::string & aQualifiedNameID)
	{
		appendField( aQualifiedNameID , UFI_SCHEME_VARIABLE );
	}


	/**
	 * GETTER - SETTER
	 * FIELD FUNCTION
	 */
	inline void appendFieldInvokable(const BF & field)
	{
		appendField( field , UFI_SCHEME_INVOKABLE );
	}

	inline void appendFieldInvokable(const std::string & aQualifiedNameID)
	{
		appendField( aQualifiedNameID , UFI_SCHEME_INVOKABLE );
	}


	/**
	 * GETTER - SETTER
	 * FIELD PARAMETER
	 */
	inline void appendFieldParameter(const BF & field)
	{
		appendField( field , UFI_SCHEME_PARAMETER );
	}

	inline void appendFieldParameter(const std::string & aQualifiedNameID)
	{
		appendField( aQualifiedNameID , UFI_SCHEME_PARAMETER );
	}


	/**
	 * TEST
	 */
	inline bool isPureIdentifier() const
	{
		return( ListOfField::singleton() && mLocator.invalid() &&
				isScheme(UFI_SCHEME_FIELD) &&
				ListOfField::back().is< Identifier >() );
	}

	inline BF popIdentifier()
	{
		return( ListOfField::pop_first() );
	}

	inline const BF & toIdentifier() const
	{
		return( ListOfField::back() );
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	int compare(const UniFormIdentifier & other) const;

	inline bool operator==(const UniFormIdentifier & other) const
	{
		return( UniFormIdentifier::isEQ( other ) );
	}

	bool isEQ(const UniFormIdentifier & other) const;

	// Due to [-Woverloaded-virtual=]
	using Element::isEQ;


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const override;

	virtual std::string str() const override;


	void toStreamLocator(OutStream & out) const;

	inline std::string toStringLocator() const
	{
		StringOutStream oss(AVM_NO_INDENT);

		toStreamLocator(oss);

		return( oss.str() );
	}


	void toStreamLocation(OutStream & out) const;

	inline std::string toStringLocation() const
	{
		StringOutStream oss(AVM_NO_INDENT);

		toStreamLocation(oss);

		return( oss.str() );
	}


	void toStreamLocation(OutStream & out, ListOfField::const_iterator it,
			ListOfField::const_iterator itEnd) const;

	std::string toStringContainer() const;

	std::string toStringId() const;


	void toStreamAvm(OutStream & out) const;

};


}

#endif /*UFI_H_*/

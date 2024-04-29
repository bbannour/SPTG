/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef COMMON_NAMEDELEMENT_H_
#define COMMON_NAMEDELEMENT_H_

#include <common/Element.h>

#include <algorithm>
#include <regex>

#include <collection/Collection.h>



namespace sep
{


/**
 * DEFAULT
 * Fully Qualified Name ID SchemeSeparator
 */
#define FQN_ID_SCHEME_PATH_SEPARATOR  ":/"

#define FQN_ID_ROOT_SEPARATOR         "::"


class NamedElement : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( NamedElement )
{

public:
/**
 * TYPEDEF
 */
	typedef std::uint8_t               op_comparer_t;

	enum {
		OP_STRICT_COMPARER            = 0x001,

		OP_ABSOLUTE_COMPARER          = 0x002, // Ignore LOCATOR

		OP_RELATIVE_COMPARER          = 0x004,

		OP_NAME_ID_COMPARER           = 0x008,

		OP_UNRESTRICTED_NAME_COMPARER = 0x010,

		OP_STRONG_COMPARER            = OP_STRICT_COMPARER
		                              | OP_ABSOLUTE_COMPARER,

		OP_QUALIFIED_NAME_ID_COMPARER = OP_STRICT_COMPARER
		                              | OP_ABSOLUTE_COMPARER
		                              | OP_RELATIVE_COMPARER
		                              | OP_NAME_ID_COMPARER,

		OP_WEAK_COMPARER              = OP_QUALIFIED_NAME_ID_COMPARER
		                              | OP_UNRESTRICTED_NAME_COMPARER,

		OP_ANY_COMPARER               = OP_STRONG_COMPARER
		                              | OP_WEAK_COMPARER
	};


	/**
	* GLOBALS
	* NAME ID SEPARATOR
	*/
	static std::string NAME_ID_SEPARATOR;

	static const std::regex REGEX_DOT_or_DIESE;
	static const std::regex REGEX_DOT_or_COLON_or_DIESE;

protected:
	/**
	 * ATTRIBUTES
	 */
	static const std::string UNNAMED_ID;

	std::string mFullyQualifiedNameID;
	std::string mNameID;
	std::string mUnrestrictedName;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	NamedElement(class_kind_t aClassKind)
	: Element( aClassKind ),
	mFullyQualifiedNameID( ),
	mNameID( ),
	mUnrestrictedName( )
	{
		//!! NOTHING
	}

	NamedElement(class_kind_t aClassKind, const std::string & aNameID)
	: Element( aClassKind ),
	mFullyQualifiedNameID( ),
	mNameID( aNameID ),
	mUnrestrictedName( aNameID )
	{
		//!! NOTHING
	}

	NamedElement(class_kind_t aClassKind,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & anUnrestrictedName)
	: Element( aClassKind ),
	mFullyQualifiedNameID( aFullyQualifiedNameID ),
	mNameID( aNameID ),
	mUnrestrictedName( anUnrestrictedName )
	{
		//!! NOTHING
	}

	NamedElement(class_kind_t aClassKind,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID)
	: Element( aClassKind ),
	mFullyQualifiedNameID( aFullyQualifiedNameID ),
	mNameID( aNameID ),
	mUnrestrictedName( aNameID )
	{
		//!! NOTHING
	}


	NamedElement(class_kind_t aClassKind, const NamedElement & anElement)
	: Element( aClassKind ),
	mFullyQualifiedNameID( ),
	mNameID( ),
	mUnrestrictedName( )
	{
		setAllName( anElement );
	}

	NamedElement(class_kind_t aClassKind, const NamedElement * anElement)
	: Element( aClassKind ),
	mFullyQualifiedNameID( ),
	mNameID( ),
	mUnrestrictedName( )
	{
		setAllName( anElement );
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	NamedElement(const NamedElement & anElement)
	: Element( anElement ),
	mFullyQualifiedNameID( anElement.mFullyQualifiedNameID ),
	mNameID( anElement.mNameID ),
	mUnrestrictedName( anElement.mUnrestrictedName )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~NamedElement()
	{
		//!! NOTHING
	}


	/**
	 * Loacation
	 * Locator
	 */
	inline static std::string location(const std::string & aQualifiedNameID)
	{
		std::string::size_type pos =
				aQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);

		return( (pos != std::string::npos) ?
				aQualifiedNameID.substr(pos + 2 ) : aQualifiedNameID );
	}

	inline static std::string locator(const std::string & aQualifiedNameID)
	{
		std::string::size_type pos =
				aQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);

		return( (pos != std::string::npos) ?
				aQualifiedNameID.substr(0, pos) : "" );
	}

	/**
	 * GETTER - SETTER
	 * mFullyQualifiedNameID
	 */
	inline virtual const std::string & getFullyQualifiedNameID() const
	{
		return( mFullyQualifiedNameID );
	}

	inline bool hasFullyQualifiedNameID() const
	{
		return( not mFullyQualifiedNameID.empty() );
	}

	inline void setFullyQualifiedNameID(
			const std::string & aFullyQualifiedNameID)
	{
		mFullyQualifiedNameID = aFullyQualifiedNameID;

		updateNameID( aFullyQualifiedNameID );
	}

	inline void setFullyQualifiedNameContainer(const NamedElement & anElement)
	{
		mFullyQualifiedNameID =
				( OSS() << anElement.getFullyQualifiedNameID()
						<< '.' << getNameID() );
	}

	// LocactionID
	inline std::string getLocationID() const
	{
		return( NamedElement::location( mFullyQualifiedNameID ) );
	}

	inline bool isLocationID(const std::string & aLocationID) const
	{
		return( NamedElement::location(mFullyQualifiedNameID)
				== NamedElement::location(aLocationID) );
	}

	/////////////////////////////////////////////
	// ASSERT PORTABILITY or UNICITY for Solver...
	inline virtual std::string getPortableQualifiedNameID() const
	{
		return std::regex_replace(
				NamedElement::getQualifiedNameID(),
				REGEX_DOT_or_COLON_or_DIESE, "__" );
	}

	inline virtual std::string getUniqFullyQualifiedNameID() const
	{
		return( OSS() << std::regex_replace(
					NamedElement::getQualifiedNameID(),
					REGEX_DOT_or_COLON_or_DIESE, "__")
					  << "__" << raw_address() );
	}

	inline virtual std::string getUniqQualifiedNameID() const
	{
		std::string locationID = NamedElement::getLocationID();
		std::string::size_type pos = locationID.find_first_of('.');
		if( pos != std::string::npos )
		{
			locationID = locationID.substr(pos + 1);
		}
		return( OSS() << std::regex_replace(locationID,
					REGEX_DOT_or_COLON_or_DIESE, "__")
					  << "__" << raw_address() );
	}


	inline virtual std::string getPortableLocationdID() const
	{
		return std::regex_replace(getLocationID(),
				REGEX_DOT_or_COLON_or_DIESE, "__");
	}

	inline virtual std::string getPortableFullyQualifiedNameID() const
	{
		return std::regex_replace(
				mFullyQualifiedNameID, REGEX_DOT_or_COLON_or_DIESE, "__");
	}


	/**
	 * GETTER - SETTER
	 * mNameID
	 */

	inline virtual const std::string & getNameID() const
	{
		return( mNameID );
	}

	inline bool hasNameID() const
	{
		return( not mNameID.empty() );
	}

	inline void setNameID(const std::string & aNameID)
	{
		mNameID = aNameID;
	}

	inline void setNames(const std::string & aNameID)
	{
		mUnrestrictedName = mNameID = aNameID;
	}

	inline void setNames(const std::string & aNameID,
			const std::string & aUnrestrictedName)
	{
		mNameID = aNameID;
		mUnrestrictedName = aUnrestrictedName;
	}

	inline void updateNameID(const std::string & aQualifiedNameID)
	{
		mNameID = NamedElement::extractNameID( aQualifiedNameID );

		if( mUnrestrictedName.empty() )
		{
			mUnrestrictedName = mNameID;
		}
	}


	/////////////////////////////////////////////
	// ASSERT PORTABILITY or UNICITY for Solver...
	inline virtual std::string getPortableNameID() const
	{
		std::string name = mNameID;
		std::replace(name.begin(), name.end(), '#', '_');

		return( name );
	}

	inline virtual std::string getUniqNameID() const
	{
		std::string name = mNameID;
		std::replace(name.begin(), name.end(), '#', '_');

		return( OSS() << name << "__" << raw_address() );
	}


	/*
	 * UTIL
	 * return suffix of <container-id>.<name-id> i.e. <name-id>
	 */
	static std::string extractNameID(const std::string & aQualifiedNameID);

	/**
	 * GETTER - SETTER
	 * mFullyQualifiedNameID
	 */
	inline void setAllNameID(const std::string & aFullyQualifiedNameID,
			const std::string & aNameID)
	{
		mFullyQualifiedNameID = aFullyQualifiedNameID;

		mUnrestrictedName = mNameID = aNameID;
	}

	inline void setAllNameID(const std::string & aFullyQualifiedNameID,
			const std::string & aNameID, const std::string & unrestrictedName)
	{
		mFullyQualifiedNameID = aFullyQualifiedNameID;

		mNameID = aNameID;

		mUnrestrictedName = unrestrictedName;
	}


	/**
	 * UTILS
	 */
	inline bool isNamed() const
	{
		return( not isUnamed() );
	}

	inline bool isUnamed() const
	{
		return( mFullyQualifiedNameID.empty() &&
				mNameID.empty() && mUnrestrictedName.empty() );
	}


	inline void setAllName(const NamedElement & anElement)
	{
		mFullyQualifiedNameID = anElement.mFullyQualifiedNameID;
		mNameID = anElement.mNameID;
		mUnrestrictedName = anElement.mUnrestrictedName;
	}

	inline void setAllName(const NamedElement * anElement)
	{
		if( anElement != nullptr )
		{
			mFullyQualifiedNameID = anElement->mFullyQualifiedNameID;
			mNameID = anElement->mNameID;
			mUnrestrictedName = anElement->mUnrestrictedName;
		}
	}

	std::string relativeQualifiedNameID(const NamedElement & anElement) const;


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	inline int compareFQN(const NamedElement & other) const
	{
		return( mFullyQualifiedNameID.compare( other.mFullyQualifiedNameID ) );
	}

	// STRICT:> compare LOCATOR & LOCATION [true:- retry only only LOCATION]
	inline bool fqnEquals(const std::string & aFullyQualifiedNameID,
			bool enabledOnlyLocationComparisonElse = false) const
	{
		return( (mFullyQualifiedNameID == aFullyQualifiedNameID)
				|| (enabledOnlyLocationComparisonElse
					&& this->isLocationID(aFullyQualifiedNameID)) );
	}

	inline bool fqnEndsWith(const std::string & aQualifiedNameID) const
	{
		return( (mNameID == aQualifiedNameID)
				|| NamedElement::fqnEndsWith(
						mFullyQualifiedNameID, aQualifiedNameID) );
	}

	inline bool fqnStartsWith(const std::string & aQualifiedNameID) const
	{
		return( mFullyQualifiedNameID.find(aQualifiedNameID) == 0 );
	}


	/**
	 * REGEX MATCH
	 */
	bool fqnRegexMatch(const std::string & aRegex) const;

	bool nameRegexMatch(const std::string & aRegex) const;

	/**
	 * GETTER
	 * Qualified Name IDentifier
	 * QualifiedNameID
	 */
	inline virtual std::string getQualifiedNameID() const
	{
		return( NamedElement::makeQualifiedNameID(
				mFullyQualifiedNameID , mNameID ) );
	}


	inline bool isRelative() const
	{
		return( NamedElement::isRelative(mFullyQualifiedNameID) );
	}


	/**
	 * UTIL
	 * return <container-id>.<name-id>
	 */
	static std::string makeQualifiedNameID(
			const std::string & aQualifiedNameID);

	static std::string makeQualifiedNameID(
			const std::string & aQualifiedNameID, const std::string & aNameID);

	static std::string makeFullyQualifiedNameID(
			const std::string & aFullyQualifiedNameID,
			const std::string & aQualifiedNameID, bool preserveLocator = true);

	static std::string makeFullyRegexQualifiedNameID(
			const std::string & aFullyQualifiedNameID,
			const std::string & aQualifiedNameID, bool preserveLocator = true);

	static std::string getContainerQualifiedNameID(
			const std::string & aQualifiedNameID);

	/**
	 * isAbsolute
	 * isRelative
	 */
	inline static bool isAbsolute(const std::string & aQualifiedNameID)
	{
		return( aQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR)
				!= std::string::npos );
	}

	inline static bool isRelative(const std::string & aQualifiedNameID)
	{
		return( aQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR)
				== std::string::npos );
	}


	inline static bool isNullNameID(const std::string & aQualifiedNameID)
	{
		return( (not aQualifiedNameID.empty())
				&& (aQualifiedNameID[ 0 ] == '<')
				&& (aQualifiedNameID.find_last_of(":null")
						!= std::string::npos) );
	}

	inline static bool isSimpleNameID(const std::string & aQualifiedNameID)
	{
		return( (aQualifiedNameID.find_last_of('.') == std::string::npos)
				&& (aQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR)
					== std::string::npos) );
	}


	/**
	 * GETTER
	 * "name" of a USER FORM
	 */
	inline const std::string & getUnrestrictedName() const
	{
		return( mUnrestrictedName );
	}

	inline bool hasUnrestrictedName() const
	{
		return( not mUnrestrictedName.empty() );
	}

	inline bool hasReallyUnrestrictedName() const
	{
		return( (not mUnrestrictedName.empty()) &&
				(mUnrestrictedName != mNameID ) );
	}

	inline void setUnrestrictedName(const std::string & name)
	{
		mUnrestrictedName = name;
	}


	/*
	 ***************************************************************************
	 * COMPARER  FOR  QUALIFIED NAME ID  STRING
	 ***************************************************************************
	 */
	bool isEqualsID(const std::string & aQualifiedNameID,
			op_comparer_t op) const;


	inline static bool fqnStartsWith(
			const std::string & aFullyQualifiedNameID,
			const std::string & aQualifiedNameID)
	{
		return( aFullyQualifiedNameID.find(aQualifiedNameID) == 0 );
	}

	inline static bool fqnEndsWith(
			const std::string & aFullyQualifiedNameID,
			const std::string & aQualifiedNameID)
	{
		std::size_t rpos = aFullyQualifiedNameID.rfind(aQualifiedNameID);

		return( (rpos != std::string::npos)
				&& (rpos == (aFullyQualifiedNameID.length()
						- aQualifiedNameID.length()))
				&& ( (rpos == 0)
					|| (aFullyQualifiedNameID[rpos-1] == '.')
					|| (aFullyQualifiedNameID[rpos-1] == ':') ) );
	}


	/*
	 ***************************************************************************
	 * LIST of ID of QUALIFIED NAME ID
	 ***************************************************************************
	 */
	static std::size_t collectNameID(Collection< std::string > & listNameID,
			const std::string & aQualifiedNameID, std::string::size_type pos);

	inline static std::size_t collectNameID(
			Collection< std::string > & listNameID,
		const std::string & aQualifiedNameID, const std::string & ignorePrefix)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT(
				aQualifiedNameID.find(ignorePrefix) == 0 )
				<< "Bad prefix string in NamedElement::listofID("
				<< aQualifiedNameID << ", " << ignorePrefix << ") !!!"
				<< SEND_EXIT;

		return NamedElement::collectNameID(listNameID,
				aQualifiedNameID, ignorePrefix.size());
	}

	static std::size_t collectNameID(Collection< std::string > & listNameID,
			const std::string & aQualifiedNameID);


	/**
	 * Serialization
	 */
	inline virtual std::string strFQN(
			const std::string & defaultFQN = "<unamed-element>") const
	{
		return( hasFullyQualifiedNameID() ? mFullyQualifiedNameID
				: ( hasNameID() ? mNameID
					: ( hasUnrestrictedName() ? ("'" + mUnrestrictedName + "'")
						: defaultFQN ) ) );

		return( defaultFQN );
	}

	inline virtual void strFQN(OutStream & os) const
	{
		os << strFQN();
	}


	/**
	 * Serialization
	 */
	inline virtual std::string str() const override
	{
		if( not getFullyQualifiedNameID().empty() )
		{
			return( getFullyQualifiedNameID() );
		}
		else if( not getNameID().empty() )
		{
			return( getNameID() );
		}
		return( getUnrestrictedName() );
	}

};


} /* namespace sep */

#endif /* COMMON_NAMEDELEMENT_H_ */

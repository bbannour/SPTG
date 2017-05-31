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

#include <collection/Collection.h>



namespace sep
{


/**
 * DEFAULT
 * Fully Qualified Name ID SchemeSeparator
 */
#define FQN_ID_SCHEME_PATH_SEPARATOR  ":/"

#define FQN_ID_ROOT_SEPARATOR         "::"


class NamedElement :
		public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( NamedElement )
{

public:
/**
 * TYPEDEF
 */
	typedef avm_uint8_t               op_comparer_t;

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

	NamedElement(class_kind_t aClassKind, NamedElement * anElement)
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

		extractSetNameID( aFullyQualifiedNameID );
	}

	inline void setFullyQualifiedNameContainer( NamedElement * anElement)
	{
		mFullyQualifiedNameID =
				( OSS() << anElement->getFullyQualifiedNameID()
						<< '.' << getNameID() );
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

	inline void extractSetNameID(const std::string & aQualifiedNameID)
	{
		mNameID = NamedElement::extractNameID( aQualifiedNameID );
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

		setNameID( aNameID );
	}

	inline void setAllNameID(const std::string & aFullyQualifiedNameID,
			const std::string & aNameID, const std::string & name)
	{
		mFullyQualifiedNameID = aFullyQualifiedNameID;

		mNameID = aNameID;

		mUnrestrictedName = name;
	}


	/**
	 * UTIL
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

	inline void setAllName(NamedElement * anElement)
	{
		if( anElement != NULL )
		{
			mFullyQualifiedNameID = anElement->mFullyQualifiedNameID;
			mNameID = anElement->mNameID;
			mUnrestrictedName = anElement->mUnrestrictedName;
		}
	}


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
					&& NamedElement::compareLocation(
							this, aFullyQualifiedNameID)) );
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

	static std::string getContainerQualifiedNameID(
			const std::string & aQualifiedNameID);

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


	inline static bool compareID(
			const std::string & aQualifiedNameID_1,
			const std::string & aQualifiedNameID_2)
	{
		return( aQualifiedNameID_1 == aQualifiedNameID_2 );
	}

	inline static bool compareLocation(
			const std::string & aQualifiedNameID_1,
			const std::string & aQualifiedNameID_2)
	{
		return( NamedElement::location(aQualifiedNameID_1)
				== NamedElement::location(aQualifiedNameID_2) );
	}

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


	inline static bool isNull(const std::string & aQualifiedNameID)
	{
		return( (not aQualifiedNameID.empty())
				&& (aQualifiedNameID[ 0 ] == '<')
				&& (aQualifiedNameID.find_last_of(":null")
						!= std::string::npos) );
	}

	inline static bool isSimplenameID(const std::string & aQualifiedNameID)
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
	bool compareID(const std::string & aQualifiedNameID,
			op_comparer_t op) const;

	/*
	 * !UNUSED!
	static bool compareID(const std::string & aFullyQualifiedNameID,
			const std::string & aQualifiedNameID, op_comparer_t op);

	inline static bool compareFullyQualifiedNameID(
			const NamedElement * anElement,
			const std::string & aQualifiedNameID)
	{
		return( anElement->compareID(aQualifiedNameID, OP_STRONG_COMPARER) );
	}
	* !UNUSED!
	*/

	inline static bool compareLocation(const NamedElement * anElement,
			const std::string & aQualifiedNameID)
	{
		return( anElement->compareID(aQualifiedNameID, OP_ABSOLUTE_COMPARER) );
	}

	/*
	 * !UNUSED!
	inline static bool compareQualifiedNameID(
			const NamedElement * anElement,
			const std::string & aQualifiedNameID)
	{
		return( compareID(anElement,
				aQualifiedNameID, OP_QUALIFIED_NAME_ID_COMPARER) );
	}
	* !UNUSED!
	*/

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
	static avm_size_t collectNameID(Collection< std::string > & listNameID,
			const std::string & aQualifiedNameID, std::string::size_type pos);

	inline static avm_size_t collectNameID(
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

	static avm_size_t collectNameID(Collection< std::string > & listNameID,
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

	inline void virtual strFQN(OutStream & os) const
	{
		os << strFQN();
	}


	/**
	 * Serialization
	 */
	inline virtual std::string str() const
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

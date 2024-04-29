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
#ifndef FACTORY_H_
#define FACTORY_H_


#include <collection/Collection.h>
#include <collection/List.h>

#include <common/BF.h>

#include <fml/expression/AvmCode.h>

#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
#include <fml/builtin/Identifier.h>
#include <fml/builtin/String.h>

#include <fml/operator/Operator.h>

#include <fml/workflow/WObject.h>

#include <functional>

namespace sep
{


class Query
{

public:

	////////////////////////////////////////////////////////////////////////////
	// ERROR / WARNING  REPORTING
	////////////////////////////////////////////////////////////////////////////

	inline static void reportErrorAttribute(const WObject * wfObject,
			const std::string & anID, const std::string & msg)
	{
		const WObject * wfProperty = Query::getWProperty(wfObject, anID);

		if( wfProperty != WObject::_NULL_ )
		{
			wfProperty->errorLocation(AVM_OS_WARN) << msg << std::endl;
		}
		else
		{
			wfObject->errorLocation(AVM_OS_WARN)
					<< "Unfound <" << anID << "> property : " << msg
					<< " w.r.t. wfobject< " << wfObject->strUniqId() << " > !"
					<< std::endl;
		}
	}


	/*
	 ***************************************************************************
	 * FIND WOBJECT  BY NameID
	 ***************************************************************************
	 */
	static const WObject * getWObjectByNameID(
			const WObject * wfObject, const std::string & aNameID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getRegexWObjectByNameID(
			const WObject * wfObject, const std::string & aRegexNameID,
			const WObject * theDefaultValue = WObject::_NULL_);


	static const WObject * getWTypedObjectByFQNameID(
			const WObject * wfObject, const std::string & fqnID);


	/*
	 ***************************************************************************
	 * FIND IN COMPOSITE FORM  BY TYPE
	 ***************************************************************************
	 */

	static const WObject * getWObject(const WObject * wfObject,
			bool (*isEqualFQN)(const WObject & wfObject));

	static void getWObjectByTypeNameID(const WObject * wfObject,
			const std::string & aTypeID, List< WObject * > & aContainer);


	/**
	 ***************************************************************************
	 * GETTER for WSequence
	 ***************************************************************************
	 */
	static const WObject * getWSequence(
			const WObject * wfObject, const std::string & sectionID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getrecWSequence(
			const WObject * wfObject, const std::string & sectionID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getRegexWSequence(
			const WObject * wfObject, const std::string & aRegexSectionID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getparentRegexWSequence(
			const WObject * wfObject, const std::string & aRegexSectionID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getrecRegexWSequence(
			const WObject * wfObject, const std::string & aRegexSectionID,
			const WObject * theDefaultValue = WObject::_NULL_);


	inline static bool hasWSequence(
			const WObject * wfObject, const std::string & sectionID)
	{
		return( (wfObject != WObject::_NULL_)
				&& (getWSequence(wfObject, sectionID) != WObject::_NULL_) );
	}


	// For compatibility when ID has changed !!!
	static const WObject * getWSequenceOrElse(const WObject * wfObject,
			const std::string & sectionID, const std::string & elseWSequenceID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getRegexWSequenceOrElse(
			const WObject * wfObject, const std::string & aRegexSectionID,
			const std::string & elseRegexSectionID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getrecWSequenceOrElse(const WObject * wfObject,
			const std::string & sectionID, const std::string & elseWSequenceID,
			const WObject * theDefaultValue = WObject::_NULL_);


	/**
	 ***************************************************************************
	 * GETTER for WSequence or WReference
	 ***************************************************************************
	 */
	static const WObject * getWSequenceOrReference(
			const WObject * wfObject, const std::string & sectionID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getRegexWSequenceOrReference(
			const WObject * wfObject, const std::string & aRegexSectionID,
			const WObject * theDefaultValue = WObject::_NULL_);


	/**
	 ***************************************************************************
	 * GETTER for FORM in a Container
	 ***************************************************************************
	 */
	static void getListWObject(
			const WObject * wfObject, List< WObject * > & aContainer);

	static void getRegexWObjectInSequence(
			const WObject * wfObject, const std::string & aRegexSectionID,
			List< WObject * > & aContainer);


	/**
	 ***************************************************************************
	 * GETTER for FORM ATTRIBUTE of a given NAME
	 ***************************************************************************
	 */

	static const WObject * getWProperty(
			const WObject * wfObject, const std::string & anID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getRegexWProperty(
			const WObject * wfObject, const std::string & anID,
			const WObject * theDefaultValue = WObject::_NULL_);


	inline static bool hasWProperty(
			const WObject * wfObject, const std::string & anID)
	{
		return( (wfObject != WObject::_NULL_)
				&& (getWProperty(wfObject, anID) != WObject::_NULL_) );
	}

	inline static bool hasRegexWProperty(
			const WObject * wfObject, const std::string & anID)
	{
		return( (wfObject != WObject::_NULL_)
				&& (getRegexWProperty(wfObject, anID) != WObject::_NULL_) );
	}


	/**
	 ***************************************************************************
	 * GETTER for FORM ATTRIBUTE of a given NAME && a given KIND
	 ***************************************************************************
	 */

	static const WObject * getWProperty(const WObject * wfObject,
			WObject::ENUM_WOBJECT_KIND aKind, const std::string & anID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getrecWProperty(const WObject * wfObject,
			WObject::ENUM_WOBJECT_KIND aKind, const std::string & anID,
			const WObject * theDefaultValue = WObject::_NULL_);


	static const WObject * getRegexWProperty(const WObject * wfObject,
			WObject::ENUM_WOBJECT_KIND aKind, const std::string & aRegex,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getrecRegexWProperty(const WObject * wfObject,
			WObject::ENUM_WOBJECT_KIND aKind, const std::string & aRegex,
			const WObject * theDefaultValue = WObject::_NULL_);


	template< class T , class U >
	static U getBuiltinWProperty(const WObject * wfObject,
			const std::string & anID, const U theDefaultValue)
	{
		if( wfObject != WObject::_NULL_ )
		{
			WObject::const_iterator itWfO = wfObject->owned_begin();
			WObject::const_iterator endWfO = wfObject->owned_end();
			for( ; itWfO != endWfO ; ++itWfO )
			{
				if( (*itWfO)->isWProperty() )
				{
					if( (*itWfO)->getValue().is< T >()
						&& ((*itWfO)->getNameID() == anID) )
					{
						return( (*itWfO)->getValue().to< T >().getValue() );
					}
				}
			}
		}

		return( theDefaultValue );
	}


	template< class T , class U >
	static U getBuiltinWPropertyOrElse(const WObject * wfObject,
			const std::string & anID, const std::string & elseID,
			const U theDefaultValue)
	{
		if( wfObject != WObject::_NULL_ )
		{
			T * elseAttribute = nullptr;
			WObject::const_iterator itWfO = wfObject->owned_begin();
			WObject::const_iterator endWfO = wfObject->owned_end();
			for( ; itWfO != endWfO ; ++itWfO )
			{
				if( (*itWfO)->isWProperty() )
				{
					if( (*itWfO)->getValue().is< T >()
						&& ((*itWfO)->getNameID() == anID) )
					{
						return( (*itWfO)->getValue().to< T >().getValue() );
					}
					else if( (elseAttribute == nullptr)
							&& (*itWfO)->getValue().is< T >()
							&& ((*itWfO)->getNameID() == elseID) )
					{
						elseAttribute = (*itWfO)->getValue().to_ptr< T >();
					}
				}
			}

			return( (elseAttribute != nullptr) ?
					elseAttribute->getValue() : theDefaultValue );
		}

		return( theDefaultValue );
	}


	template< class T , class U >
	static U getRegexBuiltinWProperty(const WObject * wfObject,
			const std::string & aRegex, const U theDefaultValue)
	{
		if( wfObject != WObject::_NULL_ )
		{
			WObject::const_iterator itWfO = wfObject->owned_begin();
			WObject::const_iterator endWfO = wfObject->owned_end();
			for( ; itWfO != endWfO ; ++itWfO )
			{
				if( (*itWfO)->isWProperty() )
				{
					if( (*itWfO)->getValue().is< T >()
						&& REGEX_MATCH((*itWfO)->getNameID(), aRegex) )
					{
						return( (*itWfO)->getValue().to< T >().getValue() );
					}
				}
			}
		}

		return( theDefaultValue );
	}

	static void getWProperty(
			const WObject * wfObject, WObject::ENUM_WOBJECT_KIND aKind,
			const std::string & anID, Collection< BF > & aContainer);

	static void getRegexWProperty(
			const WObject * wfObject, WObject::ENUM_WOBJECT_KIND aKind,
			const std::string & aRegex, Collection< BF > & aContainer);


	template< class T , class U >
	static void getBuiltinWProperty(const WObject * wfObject,
			const std::string & anID, Collection< U > & aContainer)
	{
		if( wfObject != WObject::_NULL_ )
		{
			WObject::const_iterator itWfO = wfObject->owned_begin();
			WObject::const_iterator endWfO = wfObject->owned_end();
			for( ; itWfO != endWfO ; ++itWfO )
			{
				if( (*itWfO)->isWProperty() )
				{
					if( (*itWfO)->getValue().is< T >()
						&& ((*itWfO)->getNameID() == anID) )
					{
						aContainer.push_back(
								(*itWfO)->getValue().to< T >().getValue() );
					}
				}
			}
		}
	}


	template< class T , class U >
	static void getRegexBuiltinWProperty(const WObject * wfObject,
			const std::string & aRegex, Collection< U > & aContainer)
	{
		if( wfObject != WObject::_NULL_ )
		{
			WObject::const_iterator itWfO = wfObject->owned_begin();
			WObject::const_iterator endWfO = wfObject->owned_end();
			for( ; itWfO != endWfO ; ++itWfO )
			{
				if( (*itWfO)->isWProperty() )
				{
					if( (*itWfO)->getValue().is< T >()
						&& REGEX_MATCH((*itWfO)->getNameID(), aRegex) )
					{
						aContainer.push_back(
								(*itWfO)->getValue().to< T >().getValue() );
					}
				}
			}
		}
	}


	static bool hasWPropertyValue(const WObject * wfObject,
			WObject::ENUM_WOBJECT_KIND aKind, const std::string & anID)
	{
		return( (wfObject != WObject::_NULL_) &&
				(getWProperty(wfObject, aKind, anID, WObject::_NULL_)
				!= WObject::_NULL_) );
	}

	static bool hasRegexWPropertyValue(const WObject * wfObject,
			WObject::ENUM_WOBJECT_KIND aKind, const std::string & aRegex)
	{
		return( (wfObject != WObject::_NULL_) &&
				(getRegexWProperty(wfObject, aKind, aRegex, WObject::_NULL_)
						!= WObject::_NULL_) );
	}


	/**
	 ***************************************************************************
	 * GETTER getWPropertyValue
	 ***************************************************************************
	 */
	static const BF & getWPropertyValue(
			const WObject * wfObject, const std::string & anID,
			const BF & theDefaultValue = BF::REF_NULL);

	static const BF & getRegexWPropertyValue(
			const WObject * wfObject, const std::string & aRegexID,
			const BF & theDefaultValue = BF::REF_NULL);


	inline static const BF & getWPropertyValue(const WObject * wfObject,
			WObject::ENUM_WOBJECT_KIND aKind, const std::string & anID,
			const BF & theDefaultValue = BF::REF_NULL)
	{
		const WObject * theAttribute = getWProperty(wfObject, aKind, anID);

		return( ( theAttribute != WObject::_NULL_ ) ?
			theAttribute->getValue() : theDefaultValue );
	}


	/**
	 ***************************************************************************
	 * GETTER  getWPropertyForm
	 ***************************************************************************
	 */
	static const WObject * getWPropertyWReference(
			const WObject * wfObject, const std::string & anID,
			const WObject * theDefaultValue = WObject::_NULL_);

	static const WObject * getRegexWPropertyWReference(
			const WObject * wfObject, const std::string & aRegex,
			const WObject * theDefaultValue = WObject::_NULL_);


	/**
	 ***************************************************************************
	 * GETTER getWPropertyBoolean
	 ***************************************************************************
	 */
	static bool getWPropertyBoolean(const WObject * wfObject,
			const std::string & anID, bool theDefaultValue)
	{
		return( getBuiltinWProperty< Boolean , bool >(
				wfObject, anID, theDefaultValue) );
	}

	static bool getRegexWPropertyBoolean(const WObject * wfObject,
			const std::string & aRegex, bool theDefaultValue)
	{
		return( getRegexBuiltinWProperty< Boolean , bool >(
				wfObject, aRegex, theDefaultValue) );
	}


	/**
	 ***************************************************************************
	 * GETTER getWPropertyInteger
	 ***************************************************************************
	 */
	static std::size_t getWPropertyPosSizeT(const WObject * wfObject,
			const std::string & anID, std::size_t theDefaultValue,
			std::size_t theNegativeValue = AVM_NUMERIC_MAX_SIZE_T);

	static std::size_t getRegexWPropertyPosSizeT(const WObject * wfObject,
			const std::string & anID, std::size_t theDefaultValue,
			std::size_t theNegativeValue = AVM_NUMERIC_MAX_SIZE_T);


	static std::size_t getWPropertySizeT(const WObject * wfObject,
			const std::string & anID, std::size_t theDefaultValue,
			std::size_t theNegativeValue = AVM_NUMERIC_MAX_SIZE_T);

	static std::size_t getRegexWPropertySizeT(const WObject * wfObject,
			const std::string & anID, std::size_t theDefaultValue,
			std::size_t theNegativeValue = AVM_NUMERIC_MAX_SIZE_T);


	static avm_integer_t getWPropertyInteger(const WObject * wfObject,
			const std::string & anID, avm_integer_t theDefaultValue);


	static int getWPropertyInt(const WObject * wfObject,
			const std::string & anID, int theDefaultValue);

	static int getRegexWPropertyInt(const WObject * wfObject,
			const std::string & anID, int theDefaultValue);


	static long getWPropertyLong(const WObject * wfObject,
			const std::string & anID, long theDefaultValue);


	/**
	 ***************************************************************************
	 * GETTER getWPropertyString
	 ***************************************************************************
	 */
	static bool hasWPropertyString(
			const WObject * wfObject, const std::string & anID)
	{
		return( hasWPropertyValue(wfObject,
				WObject::WOBJECT_PROPERTY_STRING_KIND, anID) );
	}

	static bool hasRegexWPropertyString(
			const WObject * wfObject, const std::string & aRegex)
	{
		return( hasRegexWPropertyValue(wfObject,
				WObject::WOBJECT_PROPERTY_STRING_KIND, aRegex) );
	}

	static std::string getWPropertyString(const WObject * wfObject,
			const std::string & anID, std::string theDefaultValue)
	{
		return( getBuiltinWProperty< String , std::string >(
				wfObject, anID, theDefaultValue) );
	}

	static std::string getWPropertyStringOrElse(const WObject * wfObject,
			const std::string & anID, const std::string & elseID,
			std::string theDefaultValue)
	{
		return( getBuiltinWPropertyOrElse< String , std::string >(
				wfObject, anID, elseID, theDefaultValue) );
	}

	static std::string getRegexWPropertyString(const WObject * wfObject,
			const std::string & aRegex, std::string theDefaultValue)
	{
		return( getRegexBuiltinWProperty< String , std::string >(
				wfObject, aRegex, theDefaultValue) );
	}


	static void getWPropertyString(const WObject * wfObject,
			const std::string & anID, Collection< std::string > & aContainer)
	{
		getBuiltinWProperty< String , std::string >(wfObject, anID, aContainer);
	}

	static void getRegexWPropertyString(const WObject * wfObject,
			const std::string & regex, Collection< std::string > & aContainer)
	{
		getRegexBuiltinWProperty< String , std::string >(
				wfObject, regex, aContainer);
	}

};


}

#endif /*FACTORY_H_*/

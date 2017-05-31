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


#define WID_SEPARATOR              "[^a-zA-Z\\s]?"

#define CONS_WID2(w1, w2)          w1  WID_SEPARATOR  w2

#define CONS_WID3(w1, w2, w3)      w1  WID_SEPARATOR  w2  WID_SEPARATOR  w3

#define CONS_WID4(w1, w2, w3, w4)  \
				w1  WID_SEPARATOR  w2  WID_SEPARATOR  w3  WID_SEPARATOR  w4


#define PREFIX_WID(w1, w2)          "(" w1  WID_SEPARATOR ")?(" w2 ")"

#define SUFFIX_WID(w1, w2)          "(" w1 ")(" WID_SEPARATOR  w2 ")?"


#define OP_OR 					 "|"

#define OR_WID2(w1, w2)          w1  OP_OR  w2

#define OR_WID3(w1, w2, w3)      w1  OP_OR  w2  OP_OR  w3

#define OR_WID4(w1, w2, w3, w4)  w1  OP_OR  w2  OP_OR  w3  OP_OR  w4




class IProcessorUnitRegistration;


class Query
{

public:

	////////////////////////////////////////////////////////////////////////////
	// ERROR / WARNING  REPORTING
	////////////////////////////////////////////////////////////////////////////

	inline static void reportErrorAttribute(const WObject * wfObject,
			const std::string & anID, const std::string & msg)
	{
		WObject * wfProperty = Query::getWProperty(wfObject, anID);

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
	static WObject * getWObjectByNameID(
			const WObject * wfObject, const std::string & aNameID,
			WObject * theDefaultValue = WObject::_NULL_);

	static WObject * getRegexWObjectByNameID(
			const WObject * wfObject, const std::string & aRegexNameID,
			WObject * theDefaultValue = WObject::_NULL_);


	static WObject * getWTypedObjectByFQNameID(
			const WObject * wfObject, const std::string & fqnID);


	/*
	 ***************************************************************************
	 * FIND IN COMPOSITE FORM  BY TYPE
	 ***************************************************************************
	 */

	static WObject * getRegisterWObject(const WObject * wfObject,
			const IProcessorUnitRegistration & aRegisterTool);

	static void getWObjectByTypeNameID(const WObject * wfObject,
			const std::string & aTypeID, List< WObject * > & aContainer);


	/**
	 ***************************************************************************
	 * GETTER for WSequence
	 ***************************************************************************
	 */
	static WObject * getWSequence(
			const WObject * wfObject, const std::string & sectionID,
			WObject * theDefaultValue = WObject::_NULL_);

	static WObject * getRegexWSequence(
			const WObject * wfObject, const std::string & aRegexSectionID,
			WObject * theDefaultValue = WObject::_NULL_);


	inline static bool hasWSequence(
			const WObject * wfObject, const std::string & sectionID)
	{
		return( (wfObject != WObject::_NULL_)
				&& (getWSequence(wfObject, sectionID) != WObject::_NULL_) );
	}


	// For compatibility when ID has changed !!!
	static WObject * getWSequenceOrElse(const WObject * wfObject,
			const std::string & sectionID, const std::string & elseWSequenceID,
			WObject * theDefaultValue = WObject::_NULL_);


	/**
	 ***************************************************************************
	 * GETTER for WSequence or WReference
	 ***************************************************************************
	 */
	static WObject * getWSequenceOrReference(
			const WObject * wfObject, const std::string & sectionID,
			WObject * theDefaultValue = WObject::_NULL_);

	static WObject * getRegexWSequenceOrReference(
			const WObject * wfObject, const std::string & aRegexSectionID,
			WObject * theDefaultValue = WObject::_NULL_);


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

	static WObject * getWProperty(
			const WObject * wfObject, const std::string & anID,
			WObject * theDefaultValue = WObject::_NULL_);

	static WObject * getRegexWProperty(
			const WObject * wfObject, const std::string & anID,
			WObject * theDefaultValue = WObject::_NULL_);

	static WObject * getWPropertyOrElse(const WObject * wfObject,
			const std::string & anID, const std::string & elseID,
			WObject * theDefaultValue = WObject::_NULL_);


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

	static WObject * getWProperty(const WObject * wfObject,
			WObject::ENUM_WOBJECT_KIND aKind, const std::string & anID,
			WObject * theDefaultValue = WObject::_NULL_);

	static WObject * getWProperty(
			const WObject * wfObject, WObject::ENUM_WOBJECT_KIND aKind,
			const std::string & anID, const std::string & elseID,
			WObject * theDefaultValue = WObject::_NULL_);

	static WObject * getWPropertyOrElse(
			const WObject * wfObject, WObject::ENUM_WOBJECT_KIND aKind,
			const std::string & anID, const std::string & elseID,
			WObject * theDefaultValue = WObject::_NULL_);

	static WObject * getRegexWProperty(const WObject * wfObject,
			WObject::ENUM_WOBJECT_KIND aKind, const std::string & aRegex,
			WObject * theDefaultValue = WObject::_NULL_);


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
						return( (*itWfO)->getValue().to_ptr< T >()->getValue() );
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
			T * elseAttribute = NULL;
			WObject::const_iterator itWfO = wfObject->owned_begin();
			WObject::const_iterator endWfO = wfObject->owned_end();
			for( ; itWfO != endWfO ; ++itWfO )
			{
				if( (*itWfO)->isWProperty() )
				{
					if( (*itWfO)->getValue().is< T >()
						&& ((*itWfO)->getNameID() == anID) )
					{
						return( (*itWfO)->getValue().to_ptr< T >()->getValue() );
					}
					else if( (elseAttribute == NULL)
							&& (*itWfO)->getValue().is< T >()
							&& ((*itWfO)->getNameID() == elseID) )
					{
						elseAttribute = (*itWfO)->getValue().to_ptr< T >();
					}
				}
			}

			return( (elseAttribute != NULL) ?
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
						return( (*itWfO)->getValue().to_ptr< T >()->getValue() );
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
	static void getBuiltinWProperty(
			const WObject * wfObject, const std::string & anID,
			Collection< U > & aContainer)
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
								(*itWfO)->getValue().to_ptr< T >()->getValue() );
					}
				}
			}
		}
	}


	template< class T , class U >
	static void getBuiltinWProperty(const WObject * wfObject,
			const std::string & anID, const std::string & elseID,
			Collection< U > & aContainer)
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
						&& (((*itWfO)->getNameID() == anID)
							|| ((*itWfO)->getNameID() == elseID)) )
					{
						aContainer.push_back(
							(*itWfO)->getValue().to_ptr< T >()->getValue() );
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
								(*itWfO)->getValue().to_ptr< T >()->getValue() );
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

	static bool hasWPropertyValue(
			const WObject * wfObject, WObject::ENUM_WOBJECT_KIND aKind,
			const std::string & anID, const std::string & elseID)
	{
		return( (wfObject != WObject::_NULL_) &&
				(getWProperty(wfObject, aKind, anID, elseID, WObject::_NULL_)
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

	static const BF & getWPropertyValueOrElse(const WObject * wfObject,
			const std::string & anID, const std::string & elseID,
			const BF & theDefaultValue = BF::REF_NULL);


	inline static const BF & getWPropertyValue(const WObject * wfObject,
			WObject::ENUM_WOBJECT_KIND aKind, const std::string & anID,
			const BF & theDefaultValue = BF::REF_NULL)
	{
		WObject * theAttribute = getWProperty(wfObject, aKind, anID);

		return( ( theAttribute != WObject::_NULL_ ) ?
			theAttribute->getValue() : theDefaultValue );
	}


	/**
	 ***************************************************************************
	 * GETTER  getWPropertyForm
	 ***************************************************************************
	 */
	static WObject * getWPropertyWReference(
			const WObject * wfObject, const std::string & anID,
			WObject * theDefaultValue = WObject::_NULL_);

	static WObject * getWPropertyWReferenceOrElse(const WObject * wfObject,
			const std::string & anID, const std::string & elseID,
			WObject * theDefaultValue = WObject::_NULL_);


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
	static avm_size_t getWPropertyPosSizeT(const WObject * wfObject,
			const std::string & anID, avm_size_t theDefaultValue,
			avm_size_t theNegativeValue = AVM_NUMERIC_MAX_SIZE_T);

	static avm_size_t getRegexWPropertyPosSizeT(const WObject * wfObject,
			const std::string & anID, avm_size_t theDefaultValue,
			avm_size_t theNegativeValue = AVM_NUMERIC_MAX_SIZE_T);


	static avm_size_t getWPropertySizeT(const WObject * wfObject,
			const std::string & anID, avm_size_t theDefaultValue,
			avm_size_t theNegativeValue = AVM_NUMERIC_MAX_SIZE_T);

	static avm_size_t getRegexWPropertySizeT(const WObject * wfObject,
			const std::string & anID, avm_size_t theDefaultValue,
			avm_size_t theNegativeValue = AVM_NUMERIC_MAX_SIZE_T);


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

	static bool hasWPropertyString(const WObject * wfObject,
			const std::string & anID, const std::string & elseID)
	{
		return( hasWPropertyValue(wfObject,
				WObject::WOBJECT_PROPERTY_STRING_KIND, anID, elseID) );
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

	static void getWPropertyString(const WObject * wfObject,
			const std::string & anID, const std::string & elseID,
			Collection< std::string > & aContainer)
	{
		getBuiltinWProperty< String , std::string >(
				wfObject, anID, elseID, aContainer);
	}

};


}

#endif /*FACTORY_H_*/

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

#include "Query.h"

#include <fam/api/ProcessorUnitAutoRegistration.h>

#include <fml/numeric/Float.h>
#include <fml/numeric/Integer.h>

namespace sep
{


/*
 ***************************************************************************
 * FIND WOBJECT  BY NameID
 ***************************************************************************
 */
WObject * Query::getWObjectByNameID(const WObject * wfObject,
		const std::string & aNameID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->getNameID() == aNameID )
			{
				return( *itWfO );
			}
		}
	}

	return( theDefaultValue );
}

WObject * Query::getRegexWObjectByNameID(const WObject * wfObject,
		const std::string & aRegexNameID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( REGEX_MATCH((*itWfO)->getNameID(), aRegexNameID) )
			{
				return( *itWfO );
			}
		}
	}

	return( theDefaultValue );
}


WObject * Query::getWTypedObjectByFQNameID(
		const WObject * wfObject, const std::string & fqnID)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWTypedObject()
				&& ((*itWfO)->fqnEquals( fqnID ) ) )
			{
				return( *itWfO );
			}
			else if( (*itWfO)->isWSequence() )
			{
				WObject * foundWObject =
						getWTypedObjectByFQNameID(*itWfO, fqnID);
				if( foundWObject != WObject::_NULL_ )
				{
					return( foundWObject );
				}
			}
		}
	}
	return( WObject::_NULL_ );
}


/*
 ***************************************************************************
 * FIND IN COMPOSITE FORM  BY TYPE
 ***************************************************************************
 */

WObject * Query::getRegisterWObject(const WObject * wfObject,
		const IProcessorUnitRegistration & aRegisterTool)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWTypedObject()
				&& aRegisterTool.isTypeID( *(*itWfO) ) )
			{
				return( *itWfO );
			}
		}
	}

	return( WObject::_NULL_ );
}


void Query::getWObjectByTypeNameID(const WObject * wfObject,
		const std::string & aTypeID, List< WObject * > & aContainer)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWTypedObject()
				&& (*itWfO)->isWTypedID(aTypeID) )
			{
				aContainer.push_back( *itWfO );
			}
		}
	}
}


/**
 ***************************************************************************
 * GETTER getWSequence
 ***************************************************************************
 */
WObject * Query::getWSequence(const WObject * wfObject,
		const std::string & sectionID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWSequence()
				&& ((*itWfO)->getNameID() == sectionID) )
			{
				return( *itWfO );
			}
		}
	}

	return( theDefaultValue );
}

WObject * Query::getRegexWSequence(const WObject * wfObject,
		const std::string & aRegexSectionID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWSequence()
				&& REGEX_MATCH((*itWfO)->getNameID(), aRegexSectionID) )
			{
				return( *itWfO );
			}
		}
	}

	return( theDefaultValue );
}


// For compatibility when ID has changed !!!
WObject * Query::getWSequenceOrElse(
		const WObject * wfObject, const std::string & sectionID,
		const std::string & elseSequenceID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject * elseWSequence = WObject::_NULL_;

		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWSequence() )
			{
				if( ((*itWfO)->getNameID() == sectionID) )
				{
					return( (*itWfO) );
				}
				else if( (elseWSequence == WObject::_NULL_)
						&& ((*itWfO)->getNameID() == elseSequenceID) )
				{
					// Save the first elseSequence !
					elseWSequence = (*itWfO);
				}
			}
		}
		return( (elseWSequence != WObject::_NULL_) ?
				elseWSequence : theDefaultValue );
	}
	return( theDefaultValue );
}


/**
 *******************************************************************************
 * GETTER for WSequence or WReference
 *******************************************************************************
 */
WObject * Query::getWSequenceOrReference(const WObject * wfObject,
		const std::string & sectionID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWSequenceOrReference()
				&& ((*itWfO)->getNameID() == sectionID) )
			{
				return( (*itWfO)->isWSequence() ? (*itWfO)
						: (*itWfO)->getWReferenceValue() );
			}
		}
	}

	return( theDefaultValue );
}

WObject * Query::getRegexWSequenceOrReference(const WObject * wfObject,
		const std::string & aRegexSectionID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWSequenceOrReference()
				&& REGEX_MATCH((*itWfO)->getNameID(), aRegexSectionID) )
			{
				return( (*itWfO)->isWSequence() ? (*itWfO)
						: (*itWfO)->getWReferenceValue() );
			}
		}
	}

	return( theDefaultValue );
}


/**
 *******************************************************************************
 * GETTER for FORM in a Container
 *******************************************************************************
 */
void Query::getListWObject(
		const WObject * wfObject, List< WObject * > & aContainer)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWTypedObject() )
			{
				aContainer.push_back( *itWfO );
			}
		}
	}
}


void Query::getRegexWObjectInSequence(const WObject * wfObject,
		const std::string & aRegexSectionID, List< WObject * > & aContainer)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWSequence()
				&& REGEX_MATCH((*itWfO)->getNameID(), aRegexSectionID) )
			{
				getListWObject( *itWfO , aContainer );
			}
		}
	}

}


/**
 ***************************************************************************
 * GETTER for FORM ATTRIBUTE of a given NAME
 ***************************************************************************
 */

WObject * Query::getWProperty(const WObject * wfObject,
		const std::string & anID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty()
			&& ((*itWfO)->getNameID() == anID) )
			{
				return( *itWfO );
			}
		}
	}
	return( theDefaultValue );
}

WObject * Query::getRegexWProperty(const WObject * wfObject,
		const std::string & aRegexID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty()
			&& REGEX_MATCH((*itWfO)->getNameID(), aRegexID) )
			{
				return( *itWfO );
			}
		}
	}
	return( theDefaultValue );
}

WObject * Query::getWPropertyOrElse(
		const WObject * wfObject, const std::string & anID,
		const std::string & elseID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject * elseWObject = WObject::_NULL_;
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( ((*itWfO)->getNameID() == anID) )
				{
					return( *itWfO );
				}
				else if( (elseWObject == WObject::_NULL_)
					&& ((*itWfO)->getNameID() == elseID) )
				{
					// Save the first elseWObject !
					elseWObject = (*itWfO);
				}
			}
		}

		return( (elseWObject != WObject::_NULL_) ?
				elseWObject : theDefaultValue );
	}
	return( theDefaultValue );
}


/**
 ***************************************************************************
 * GETTER for FORM ATTRIBUTE of a given NAME && a given KIND
 ***************************************************************************
 */

WObject * Query::getWProperty(const WObject * wfObject,
		WObject::ENUM_WOBJECT_KIND aKind,
		const std::string & anID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( (*itWfO)->isKind( aKind )
					&& ((*itWfO)->getNameID() == anID) )
				{
					return( *itWfO );
				}
			}
		}
	}

	return( theDefaultValue );
}

WObject * Query::getWProperty(const WObject * wfObject,
		WObject::ENUM_WOBJECT_KIND aKind, const std::string & anID,
		const std::string & elseID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( (*itWfO)->isKind( aKind )
					&& ((*itWfO)->getNameID() == anID)
					&& ((*itWfO)->getNameID() == elseID) )
				{
					return( *itWfO );
				}
			}
		}
	}

	return( theDefaultValue );
}


WObject * Query::getWPropertyOrElse(const WObject * wfObject,
		WObject::ENUM_WOBJECT_KIND aKind, const std::string & anID,
		const std::string & elseID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject * elseAttribute = WObject::_NULL_;
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( (*itWfO)->isKind( aKind ) )
				{
					if( (*itWfO)->getNameID() == anID )
					{
						return( *itWfO );
					}
					else if( (elseAttribute == WObject::_NULL_)
							&& ((*itWfO)->getNameID() == elseID) )
					{
						elseAttribute = (*itWfO);
					}
				}
			}
		}

		return( (elseAttribute != WObject::_NULL_) ?
				elseAttribute : theDefaultValue );
	}

	return( theDefaultValue );
}


WObject * Query::getRegexWProperty(
		const WObject * wfObject, WObject::ENUM_WOBJECT_KIND aKind,
		const std::string & aRegex, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( (*itWfO)->isKind( aKind )
					&& REGEX_MATCH((*itWfO)->getNameID(), aRegex) )
				{
					return( *itWfO );
				}
			}
		}
	}

	return( theDefaultValue );
}


void Query::getWProperty(
		const WObject * wfObject, WObject::ENUM_WOBJECT_KIND aKind,
		const std::string & anID, Collection< BF > & aContainer)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( (*itWfO)->isKind( aKind )
					&& ((*itWfO)->getNameID() == anID) )
				{
					aContainer.push_back( (*itWfO)->getValue() );
				}
			}
		}
	}
}


void Query::getRegexWProperty(
		const WObject * wfObject, WObject::ENUM_WOBJECT_KIND aKind,
		const std::string & aRegex, Collection< BF > & aContainer)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( (*itWfO)->isKind( aKind )
					&& REGEX_MATCH((*itWfO)->getNameID(), aRegex) )
				{
					aContainer.push_back( (*itWfO)->getValue() );
				}
			}
		}
	}
}


/**
 ***************************************************************************
 * GETTER getAttributeValue
 ***************************************************************************
 */
const BF & Query::getWPropertyValue(const WObject * wfObject,
		const std::string & anID, const BF & theDefaultValue)
{
	WObject * theAttribute = Query::getWProperty(wfObject, anID);
	if( theAttribute != WObject::_NULL_ )
	{
		return( theAttribute->getValue() );
	}
	else
	{
		return( theDefaultValue );
	}
}

const BF & Query::getRegexWPropertyValue(const WObject * wfObject,
		const std::string & aRegexID, const BF & theDefaultValue)
{
	WObject * theAttribute = Query::getRegexWProperty(wfObject, aRegexID);
	if( theAttribute != WObject::_NULL_ )
	{
		return( theAttribute->getValue() );
	}
	else
	{
		return( theDefaultValue );
	}
}

const BF & Query::getWPropertyValueOrElse(const WObject * wfObject,
		const std::string & anID, const std::string & elseID,
		const BF & theDefaultValue)
{
	WObject * theAttribute = Query::getWPropertyOrElse(wfObject, anID, elseID);
	if( theAttribute != WObject::_NULL_ )
	{
		return( theAttribute->getValue() );
	}
	else
	{
		return( theDefaultValue );
	}
}


/**
 *******************************************************************************
 * GETTER  getWPropertyForm
 *******************************************************************************
 */
WObject * Query::getWPropertyWReference(const WObject * wfObject,
		const std::string & anID, WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWPropertyWReference() )
			{
				return( (*itWfO)->getWReferenceValue() );
			}
/*
 * !UNUSED!
 * !DELETE!
			if( (*itWfO)->isWProperty() )
			{
				if( (*itWfO)->isValueWObject()
					&& ((*itWfO)->getNameID() == anID) )
				{
					return( (*itWfO)->getValueWObject() );
				}
			}
* !UNUSED!
*/
		}
	}

	return( theDefaultValue );
}

WObject * Query::getWPropertyWReferenceOrElse(const WObject * wfObject,
		const std::string & anID, const std::string & elseID,
		WObject * theDefaultValue)
{
	if( wfObject != WObject::_NULL_ )
	{
		WObject * elseAttribute = WObject::_NULL_;

		WObject::const_iterator itWfO = wfObject->owned_begin();
		WObject::const_iterator endWfO = wfObject->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWPropertyWReference() )
			{
				if( (*itWfO)->getNameID() == anID )
				{
					return( (*itWfO)->getWReferenceValue() );
				}
				else if( (elseAttribute != WObject::_NULL_)
					&& ((*itWfO)->getNameID() == elseID) )
				{
					elseAttribute = (*itWfO)->getWReferenceValue();
				}
			}
/*
 * !UNUSED!
 * !DELETE!
			if( (*itWfO)->isWProperty() )
			{
				if( (*itWfO)->isValueWObject()
					&& ((*itWfO)->getNameID() == anID) )
				{
					return( (*itWfO)->getValueWObject() );
				}
				else if( (elseAttribute != WObject::_NULL_)
					&& (*itWfO)->isValueWObject()
					&& ((*itWfO)->getNameID() == elseID) )
				{
					elseAttribute = (*itWfO)->getValueWObject();
				}
			}
* !UNUSED!
*/
		}

		return( ( elseAttribute != WObject::_NULL_ ) ?
				elseAttribute : theDefaultValue );
	}
	return( theDefaultValue );
}

/**
 ***************************************************************************
 * GETTER getAttributeInteger
 ***************************************************************************
 */
avm_size_t Query::getWPropertyPosSizeT(
		const WObject * wfObject, const std::string & anID,
		avm_size_t theDefaultValue, avm_size_t theNegativeValue)
{
	WObject * theAttribute = Query::getWProperty(wfObject,
			WObject::WOBJECT_PROPERTY_INTEGER_KIND, anID);
	if( theAttribute != WObject::_NULL_ )
	{
		avm_integer_t value = theAttribute->getIntegerValue();

		return( (value > 0) ? value : theNegativeValue );
	}
	else
	{
		return( (theDefaultValue > 0) ? theDefaultValue : theNegativeValue );
	}
}

avm_size_t Query::getRegexWPropertyPosSizeT(
		const WObject * wfObject, const std::string & aRegexID,
		avm_size_t theDefaultValue, avm_size_t theNegativeValue)
{
	WObject * theAttribute =
			Query::getRegexWProperty(wfObject,
					WObject::WOBJECT_PROPERTY_INTEGER_KIND, aRegexID);
	if( theAttribute != WObject::_NULL_ )
	{
		avm_integer_t value = theAttribute->getIntegerValue();

		return( (value > 0) ? value : theNegativeValue );
	}
	else
	{
		return( (theDefaultValue > 0) ? theDefaultValue : theNegativeValue );
	}
}


avm_size_t Query::getWPropertySizeT(
		const WObject * wfObject, const std::string & anID,
		avm_size_t theDefaultValue, avm_size_t theNegativeValue)
{
	WObject * theAttribute = Query::getWProperty(wfObject,
			WObject::WOBJECT_PROPERTY_INTEGER_KIND, anID);
	if( theAttribute != WObject::_NULL_ )
	{
		avm_integer_t value = theAttribute->getIntegerValue();

		return( (value >= 0) ? value : theNegativeValue );
	}
	else
	{
		return( (theDefaultValue >= 0) ? theDefaultValue : theNegativeValue );
	}
}

avm_size_t Query::getRegexWPropertySizeT(
		const WObject * wfObject, const std::string & aRegexID,
		avm_size_t theDefaultValue, avm_size_t theNegativeValue)
{
	WObject * theAttribute = Query::getRegexWProperty(wfObject,
			WObject::WOBJECT_PROPERTY_INTEGER_KIND, aRegexID);
	if( theAttribute != WObject::_NULL_ )
	{
		avm_integer_t value = theAttribute->getIntegerValue();

		return( (value >= 0) ? value : theNegativeValue );
	}
	else
	{
		return( (theDefaultValue >= 0) ? theDefaultValue : theNegativeValue );
	}
}


avm_integer_t Query::getWPropertyInteger(const WObject * wfObject,
		const std::string & anID, avm_integer_t theDefaultValue)
{
	WObject * theAttribute = Query::getWProperty(wfObject,
			WObject::WOBJECT_PROPERTY_INTEGER_KIND, anID);
	if( theAttribute != WObject::_NULL_ )
	{
		return( theAttribute->getIntegerValue() );
	}
	else
	{
		return( theDefaultValue );
	}
}


int Query::getWPropertyInt(const WObject * wfObject,
		const std::string & anID, int theDefaultValue)
{
	WObject * theAttribute = Query::getWProperty(wfObject,
			WObject::WOBJECT_PROPERTY_INTEGER_KIND, anID);
	if( theAttribute != WObject::_NULL_ )
	{
		return( theAttribute->getInt32Value() );
	}
	else
	{
		return( theDefaultValue );
	}
}

int Query::getRegexWPropertyInt(const WObject * wfObject,
		const std::string & aRegexID, int theDefaultValue)
{
	WObject * theAttribute = Query::getRegexWProperty(wfObject,
					WObject::WOBJECT_PROPERTY_INTEGER_KIND, aRegexID);
	if( theAttribute != WObject::_NULL_ )
	{
		return( theAttribute->getInt32Value() );
	}
	else
	{
		return( theDefaultValue );
	}
}


long Query::getWPropertyLong(const WObject * wfObject,
		const std::string & anID, long theDefaultValue)
{
	WObject * theAttribute = Query::getWProperty(wfObject,
			WObject::WOBJECT_PROPERTY_INTEGER_KIND, anID);
	if( theAttribute != WObject::_NULL_ )
	{
		return( theAttribute->getInt64Value() );
	}
	else
	{
		return( theDefaultValue );
	}
}


}

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 8 avr. 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef FML_COMMON_PROPERTYELEMENT_H_
#define FML_COMMON_PROPERTYELEMENT_H_

#include <fml/common/ObjectElement.h>

#include <base/ClassKindInfo.h>


namespace sep
{

class Machine;
class Modifier;

class PropertyElement :
		public ObjectElement,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( PropertyElement )
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	PropertyElement(class_kind_t aClassKind, ObjectElement * aContainer,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID, const std::string & anUnrestrictedName)
	: ObjectElement( aClassKind , aContainer ,
			aFullyQualifiedNameID , aNameID , anUnrestrictedName )
	{
		//!! NOTHING
	}

	PropertyElement(class_kind_t aClassKind, ObjectElement * aContainer,
			const Modifier & aModifier, const std::string & aNameID)
	: ObjectElement( aClassKind , aContainer , aModifier , aNameID )
	{
		//!! NOTHING
	}

	PropertyElement(class_kind_t aClassKind,
			ObjectElement * aContainer, const std::string & aNameID)
	: ObjectElement( aClassKind , aContainer , aNameID )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Other
	 */
	PropertyElement(class_kind_t aClassKind,
			PropertyElement * aContainer, const PropertyElement & aPattern)
	: ObjectElement( aClassKind , aContainer , aPattern )
	{
		//!! NOTHING
	}

	PropertyElement(class_kind_t aClassKind, Machine * aContainer,
			const Modifier & aModifier, const PropertyElement & aPattern);


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	PropertyElement(const PropertyElement & aProperty)
	: ObjectElement( aProperty )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~PropertyElement()
	{
		//!! NOTHING
	}

};


} /* namespace sep */

#endif /* FML_COMMON_PROPERTYELEMENT_H_ */

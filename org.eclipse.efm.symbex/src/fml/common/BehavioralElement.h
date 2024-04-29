/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 21 févr. 2017
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef FML_COMMON_BEHAVIORAL_ELEMENT_H_
#define FML_COMMON_BEHAVIORAL_ELEMENT_H_

#include <fml/common/ObjectElement.h>

#include <base/ClassKindInfo.h>


namespace sep
{


class BehavioralElement :
		public ObjectElement,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BehavioralElement )
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BehavioralElement(class_kind_t aClassKind, BehavioralElement & aContainer)
	: ObjectElement( aClassKind , (& aContainer) )
	{
		//!! NOTHING
	}

	BehavioralElement(class_kind_t aClassKind, BehavioralElement * aContainer,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & anUnrestrictedName)
	: ObjectElement( aClassKind , aContainer , aFullyQualifiedNameID,
			aNameID , anUnrestrictedName)
	{
		//!! NOTHING
	}

	BehavioralElement(class_kind_t aClassKind,
			ObjectElement * aContainer, const std::string & aNameID)
	: ObjectElement( aClassKind , aContainer , aNameID )
	{
		//!! NOTHING
	}

	BehavioralElement(class_kind_t aClassKind, BehavioralElement & aContainer,
			const Modifier & aModifier, const std::string & aNameID)
	: ObjectElement( aClassKind , (& aContainer) , aModifier , aNameID )
	{
		//!! NOTHING
	}

	BehavioralElement(class_kind_t aClassKind,
			BehavioralElement & aContainer, const BehavioralElement & aPattern)
	: ObjectElement( aClassKind , (& aContainer) , aPattern )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BehavioralElement()
	{
		//!! NOTHING
	}

};


} /* namespace sep */

#endif /* FML_COMMON_BEHAVIORAL_ELEMENT_H_ */

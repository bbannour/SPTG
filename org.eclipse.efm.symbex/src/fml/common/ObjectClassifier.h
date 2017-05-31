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

#ifndef FML_COMMON_OBJECT_CLASSIFIER_H_
#define FML_COMMON_OBJECT_CLASSIFIER_H_

#include <common/NamedElement.h>
#include <fml/common/TraceableElement.h>

#include <base/ClassKindInfo.h>


namespace sep
{

class Machine;
class ObjectElement;


class ObjectClassifier :
		public NamedElement ,
		public TraceableElement,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ObjectClassifier )
{

protected:
	/**
	 * ATTRIBUTES
	 */
	ObjectElement * mContainer;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ObjectClassifier(class_kind_t aClassKind,
			ObjectElement * aContainer, const std::string & aNameID)
	: NamedElement( aClassKind , aNameID , aNameID , aNameID ),
	TraceableElement( ),
	mContainer( aContainer )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ObjectClassifier()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mContainer
	 */
	inline ObjectElement * getContainer() const
	{
		return( mContainer );
	}

	inline bool hasContainer() const
	{
		return( mContainer != NULL );
	}

	inline void setContainer(ObjectElement * aContainer)
	{
		mContainer = aContainer;
	}

	const Machine * getContainerMachine() const;


};

} /* namespace sep */

#endif /* FML_COMMON_OBJECT_CLASSIFIER_H_ */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 juin 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef FML_TYPE_CHOICETYPESPECIFIER_H_
#define FML_TYPE_CHOICETYPESPECIFIER_H_

#include <fml/type/BaseSymbolTypeSpecifier.h>


namespace sep
{

class DataType;


class ChoiceTypeSpecifier : public BaseSymbolTypeSpecifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( UnionTypeSpecifier )
{

	AVM_DECLARE_UNCLONABLE_CLASS(ChoiceTypeSpecifier)


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ChoiceTypeSpecifier(DataType * aCompiledType)
	: BaseSymbolTypeSpecifier(CLASS_KIND_T( ChoiceTypeSpecifier ),
			TYPE_UNION_SPECIFIER, aCompiledType, 1, 1, 0)
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ChoiceTypeSpecifier()
	{
		//!!! NOTHING
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const;


};

} /* namespace sep */

#endif /* FML_TYPE_CHOICETYPESPECIFIER_H_ */

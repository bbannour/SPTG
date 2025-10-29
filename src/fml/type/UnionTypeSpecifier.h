/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 janv. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef UNIONTYPESPECIFIER_H_
#define UNIONTYPESPECIFIER_H_

#include <fml/type/BaseSymbolTypeSpecifier.h>


namespace sep
{

class DataType;


class UnionTypeSpecifier final : public BaseSymbolTypeSpecifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( UnionTypeSpecifier )
{

	AVM_DECLARE_UNCLONABLE_CLASS(UnionTypeSpecifier)


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	UnionTypeSpecifier(const DataType & astType)
	: BaseSymbolTypeSpecifier(CLASS_KIND_T( UnionTypeSpecifier ),
			TYPE_UNION_SPECIFIER, astType, 1, 1, 0)
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~UnionTypeSpecifier()
	{
		//!!! NOTHING
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const override;

};


} /* namespace sep */
#endif /* UNIONTYPESPECIFIER_H_ */

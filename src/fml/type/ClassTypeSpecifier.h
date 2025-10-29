/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef CLASSTYPESPECIFIER_H_
#define CLASSTYPESPECIFIER_H_

#include <fml/type/BaseSymbolTypeSpecifier.h>


namespace sep
{

class ArrayBF;

class DataType;


class ClassTypeSpecifier final : public BaseSymbolTypeSpecifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ClassTypeSpecifier )
{

	AVM_DECLARE_UNCLONABLE_CLASS(ClassTypeSpecifier)


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ClassTypeSpecifier(const DataType & astType,
			avm_type_specifier_kind_t aSpecifierKind = TYPE_CLASS_SPECIFIER)
	: BaseSymbolTypeSpecifier(CLASS_KIND_T( ClassTypeSpecifier ),
			aSpecifierKind, astType, 1, 1, 0)
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ClassTypeSpecifier()
	{
		//!!! NOTHING
	}


	/**
	 * Format a value w.r.t. its type
	 */
	virtual void formatStream(
			OutStream & out, const ArrayBF & arrayValue) const override;

	// Due to [-Woverloaded-virtual=]
	using BaseSymbolTypeSpecifier::formatStream;


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const override;

};


}

#endif /* CLASSTYPESPECIFIER_H_ */

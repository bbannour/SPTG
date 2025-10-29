/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 déc. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML__INFRASTRUCTURE_FUNCTION_H_
#define FML__INFRASTRUCTURE_FUNCTION_H_

#include <fml/common/PropertyElement.h>

#include <fml/expression/AvmCode.h>


namespace sep
{

class ObjectElement;

class PropertyPart;


class Function final :
		public PropertyElement,
		AVM_INJECT_STATIC_NULL_REFERENCE( Function ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Function )
{

	AVM_DECLARE_CLONABLE_CLASS( Function )

protected:
	/**
	* ATTRIBUTES
	*/
	PropertyPart * mParameterPart;

	BFCode mCode;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Function(const PropertyPart & aPropertyPart, const std::string & aNameID);

	Function(ObjectElement * aContainer, const std::string & aNameID);

	/**
	 * DESTRUCTOR
	 */
	virtual ~Function()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	static Function & nullref();


	/**
	 * GETTER - SETTER
	 * mPropertyPart
	 */
	PropertyPart & getParameterPart() const;


	/**
	 * GETTER - SETTER
	 * mCode
	 */
	inline const BFCode & getCode() const
	{
		return( mCode );
	}

	inline bool hasCode() const
	{
		return( mCode.valid() );
	}

	inline void setCode(const BFCode & aCode)
	{
		mCode = aCode;
	}


	/**
	 * Serialization
	 */
	void strParameters(OutStream & out, const std::string & sep = ", ") const;

	void strReturns(OutStream & out, const std::string & sep = ", ") const;

	virtual void strHeader(OutStream & out) const override;

	virtual void toStream(OutStream & out) const override;


	void strInvokeParameters(
			OutStream & out, const std::string & sep = ", ") const;

	void strInvokeReturns(
			OutStream & out, const std::string & sep = ", ") const;

	void toStreamInvoke(OutStream & out, const std::string & sep = ", ") const;

};


} /* namespace sep */
#endif /* FML__INFRASTRUCTURE_FUNCTION_H_ */

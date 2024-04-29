/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 mars 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef PROCESSORUNITAUTOREGISTRATION_H_
#define PROCESSORUNITAUTOREGISTRATION_H_

#include <util/avm_string.h>


namespace sep
{

class OutStream;
class BF;

class WObject;

class AbstractProcessorUnit;
class SymbexControllerUnitManager;


class IProcessorUnitRegistration
{

protected:
	/**
	 * ATTRIBUTE
	 */
	std::string mProcessorTypeID;

	// For deprecated Type Qualified Name/Alias ID
	std::string mProcessorTypeAliasID_1;
	std::string mProcessorTypeAliasID_2;
	std::string mProcessorTypeAliasID_3;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	IProcessorUnitRegistration(const std::string & aMainTypeID,
			const std::string & aTypeAliasID_1 = "",
			const std::string & aTypeAliasID_2 = "",
			const std::string & aTypeAliasID_3 = "");

	/**
	 * DESTRUCTOR
	 */
	virtual ~IProcessorUnitRegistration()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// API for Processor Unit Registration
	////////////////////////////////////////////////////////////////////////////

	// Equals Comparison
	inline virtual bool isEquals(
			const IProcessorUnitRegistration & aRegisterTool) const
	{
		return( this == (& aRegisterTool) );
	}


	// API for ProcessorUnitRepository::register(...)
	inline const std::string & getTypeID() const
	{
		return( mProcessorTypeID );
	}

	inline bool isTypeID(const std::string & aTypeID) const
	{
		return( (not aTypeID.empty()) &&
				(  REGEX_MATCH(aTypeID , mProcessorTypeID)
				|| REGEX_MATCH(aTypeID , mProcessorTypeAliasID_1)
				|| REGEX_MATCH(aTypeID , mProcessorTypeAliasID_2)
				|| REGEX_MATCH(aTypeID , mProcessorTypeAliasID_3) ) );
	}


	bool isTypeID(const WObject & wfObject) const;

	// API for ProcessorUnitRepository::create(...)
	virtual AbstractProcessorUnit * newInstance(
			SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject) = 0;

};



template< class ProcessorT >
class ProcessorUnitRegistrationImpl  :  public IProcessorUnitRegistration
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ProcessorUnitRegistrationImpl(const std::string & aMainTypeID,
			const std::string & aTypeAliasID_1 = "",
			const std::string & aTypeAliasID_2 = "",
			const std::string & aTypeAliasID_3 = "")
	: IProcessorUnitRegistration(aMainTypeID,
			aTypeAliasID_1, aTypeAliasID_2, aTypeAliasID_3)
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ProcessorUnitRegistrationImpl()
	{
		//!! NOTHING
	}

	////////////////////////////////////////////////////////////////////////////
	// API for ProcessorUnitRepository
	////////////////////////////////////////////////////////////////////////////

	// API for ProcessorUnitRepository::create(...)
	virtual AbstractProcessorUnit * newInstance(
			SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject) override
	{
		return( new ProcessorT(aControllerUnitManager, wfParameterObject) );
	}

};


} /* namespace sep */

#endif /* PROCESSORUNITAUTOREGISTRATION_H_ */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 déc. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef PROCESSORUNITREPOSITORY_H_
#define PROCESSORUNITREPOSITORY_H_

#include <map>
#include <string>
#include <vector>


namespace sep
{


class AbstractProcessorUnit;
class OutStream;

class IProcessorUnitRegistration;

class SymbexControllerUnitManager;

class WObject;

class ProcessorUnitRepository
{


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ProcessorUnitRepository()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	~ProcessorUnitRepository()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// REGISTRY
	////////////////////////////////////////////////////////////////////////////

	typedef std::map< std::string ,
					IProcessorUnitRegistration * >  MapOfProcessorFactory;

	inline static MapOfProcessorFactory & getRepository()
	{
		static MapOfProcessorFactory mProcessorRepository;

		return( mProcessorRepository );
	}


	inline static void registerProcessorFactory(const std::string & aTypeUFI,
			IProcessorUnitRegistration * aProcessorRegistration)
	{
		getRepository()[ aTypeUFI ] = aProcessorRegistration;
	}

	static IProcessorUnitRegistration * getProcessorFactory(
			const std::string & aTypeID);


	inline static bool containsFam(const std::string & aFamID)
	{
		return( getRepository()[ aFamID ] != nullptr );
	}


	// All FAM_ID of all FAM, with maybe more than one FAM_ID for a FAM
	// A FAM has a main FAM_ID and up to 3 aliases ID
	static std::vector<std::string> getAllAvailableFamID();

	// One and only one FAM_ID, his main ID, of all FAM
	static std::vector<std::string> getAvailableFamID();


	static void toStreamKeys(OutStream & out,
			const std::string & header = "processors");

	static void toStreamAll(OutStream & out,
			const std::string & header = "processors");


	/**
	 * CREATION
	 */
	static AbstractProcessorUnit * create(
		SymbexControllerUnitManager & aManager, const WObject * wfProcessObject);

};


} /* namespace sep */

#endif /* PROCESSORUNITREPOSITORY_H_ */

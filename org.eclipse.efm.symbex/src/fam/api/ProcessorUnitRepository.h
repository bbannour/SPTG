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

#include <common/BF.h>


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

	inline static IProcessorUnitRegistration * getProcessorFactory(
			const std::string & aTypeID)
	{
		return( getRepository()[ aTypeID ] );
	}

	static void toStreamKeys(OutStream & out,
			const std::string & header = "processors");

	static void toStreamAll(OutStream & out,
			const std::string & header = "processors");

	static void toStreamExported(OutStream & out,
			const std::string & header = "export processors");



	/**
	 * CREATION
	 */
	static AbstractProcessorUnit * create(
			SymbexControllerUnitManager & aManager, WObject * wfProcessObject);

};


} /* namespace sep */

#endif /* PROCESSORUNITREPOSITORY_H_ */

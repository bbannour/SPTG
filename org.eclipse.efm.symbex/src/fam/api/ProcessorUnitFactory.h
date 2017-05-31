/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef PROCESSORUNITFACTORY_H_
#define PROCESSORUNITFACTORY_H_

#include <collection/List.h>
#include <fam/api/AbstractProcessorUnit.h>


namespace sep
{

class CompositeControllerUnit;
class SymbexControllerUnitManager;
class WObject;


class ProcessorUnitFactory
{

public:

	////////////////////////////////////////////////////////////////////////////
	// LOADER / DISPOSER  API
	////////////////////////////////////////////////////////////////////////////
	static void load();
	static void dispose();


	////////////////////////////////////////////////////////////////////////////
	// CREATION
	////////////////////////////////////////////////////////////////////////////
	static AbstractProcessorUnit * create(
			SymbexControllerUnitManager & aManager, WObject * wfProcessObject);

	static bool createList(SymbexControllerUnitManager & aManager,
			List< WObject * > & listOfProcessWObject);


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE  API
	////////////////////////////////////////////////////////////////////////////
	static bool configure(SymbexControllerUnitManager & aPluginProcessorManager ,
			WObject * wfDirectorObject, WObject * moeProfile);

	static bool configureProcessorScheduler(
			avm_computing_process_stage_t aRequirement,
			CompositeControllerUnit & processorScheduler,
			const BF & aScheduler);

};



} /* namespace sep */
#endif /* PROCESSORUNITFACTORY_H_ */

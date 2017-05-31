/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 mars 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXTENDERPROCESSORUNIT_H_
#define EXTENDERPROCESSORUNIT_H_

#include <fam/api/AbstractProcessorUnit.h>

#include <collection/Typedef.h>

#include <fml/executable/ExecutableForm.h>

#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionContext.h>

#include <fml/trace/TraceChecker.h>


namespace sep
{

class SymbexControllerUnitManager;


class ExtenderProcessorUnit  :
		public AutoRegisteredProcessorUnit< ExtenderProcessorUnit >
{

	AVM_DECLARE_CLONABLE_CLASS( ExtenderProcessorUnit )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3(
			"symbex.extender",
			"avm::processor.EXECUTION_CHAIN",
			"avm::core.process.EXECUTION_CHAIN" )
	// end registration


protected:
	/**
	 * ATTRIBUTE
	 */
	ExecutableForm mLocalExecutableForm;

	AvmCode mTraceObjective;

	TraceChecker mTraceChecker;

public:
	ExtenderProcessorUnit(SymbexControllerUnitManager & aControllerUnitManager,
			WObject * wfParameterObject);

	virtual ~ExtenderProcessorUnit()
	{
		//!! NOTHING
	}


	/**
	 * CONFIGURE
	 */
	virtual bool configureImpl();


	/**
	 * REPORT TRACE
	 */
	inline virtual void reportSilent(OutStream & os) const
	{
		// SILENT => NOTHING
	}

	virtual void reportDefault(OutStream & os) const;


	/**
	 * POST PROCESS
	 */
	virtual bool preprocess();

	void collectContext(
			ListOfExecutionContext & inputContext, ExecutionContext & anEC);

	void appendIfRequiredExtension(
			ListOfExecutionContext & inputContext, ExecutionContext & anEC);
};


}

#endif /* EXTENDERPROCESSORUNIT_H_ */

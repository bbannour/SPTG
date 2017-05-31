/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 janv. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMDEBUGPROCESSOR_H_
#define AVMDEBUGPROCESSOR_H_

#include <fam/api/AbstractProcessorUnit.h>

#include <fam/debug/IDebugProcessorProvider.h>


namespace sep
{

class SymbexControllerUnitManager;


class AvmDebugProcessor  :
		public AutoRegisteredProcessorUnit< AvmDebugProcessor >,
		public IDebugProcessorProvider
{

	AVM_DECLARE_CLONABLE_CLASS( AvmDebugProcessor )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY(
			"avm::processor.DEBUGGER" )
	// end registration


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmDebugProcessor(SymbexControllerUnitManager & aControllerUnitManager,
			WObject * wfParameterObject = NULL)
	: RegisteredProcessorUnit(aControllerUnitManager ,
			wfParameterObject , PRECEDENCE_OF_MAIN_PROCESSOR),
	IDebugProcessorProvider( this )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmDebugProcessor()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl();


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void reportSilent(OutStream & os) const
	{
		// SILENT => NOTHING
	}

	virtual void reportMinimum(OutStream & os) const;

	virtual void reportDefault(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

	virtual bool preprocess();

	virtual bool postprocess();


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API
	////////////////////////////////////////////////////////////////////////////

	virtual bool filteringInitialize();
	virtual bool filteringInitialize(ExecutionContext * anEC);

	virtual bool finalizeFiltering();
	virtual bool finalizeFiltering(ExecutionContext * anEC);


	////////////////////////////////////////////////////////////////////////////
	// ( PRE / POST ) FILTER  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool prefilter();
	virtual bool prefilter(ExecutionContext & anEC);

	bool finalizePrefiltering();

	virtual bool postfilter();
	virtual bool postfilter(ExecutionContext & anEC);

	bool finalizePostfiltering();


	////////////////////////////////////////////////////////////////////////////
	// DEBUG PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	inline virtual bool debugEvalCommandImpl()
	{
		return( false );
	}


	/**
	 * EVAL TRACE
	 */
	virtual void traceMinimumPreEval(
			OutStream & os, const ExecutionContext & anEC) const;

	virtual void traceDefaultPreEval(
			OutStream & os, const ExecutionContext & anEC) const;


	virtual void traceMinimumPostEval(
			OutStream & os, const ExecutionContext & anEC) const;

	virtual void traceDefaultPostEval(
			OutStream & os, const ExecutionContext & anEC) const;

	virtual void reportEval(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void toStream(OutStream & os) const
	{
		if( mParameterWObject != NULL )
		{
			mParameterWObject->toStream(os);
		}
	}

};


} /* namespace sep */

#endif /* AVMDEBUGPROCESSOR_H_ */

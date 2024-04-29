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

#include  <famcore/api/AbstractProcessorUnit.h>

#include  <famcore/debug/IDebugProcessorProvider.h>


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
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3(
			"symbex#debugger",
			"interactive#debugger",
			"avm::processor.DEBUGGER" )
	// end registration


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmDebugProcessor(SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject = nullptr)
	: RegisteredProcessorUnit(aControllerUnitManager, wfParameterObject ,
			AVM_COMPUTING_ALL_STAGE, PRECEDENCE_OF_MAIN_PROCESSOR),
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

	virtual bool configureImpl() override;


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void reportSilent(OutStream & os) const override
	{
		// SILENT => NOTHING
	}

	virtual void reportMinimum(OutStream & os) const override;

	virtual void reportDefault(OutStream & os) const override;


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

	virtual bool preprocess() override;

	virtual bool postprocess() override;


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API
	////////////////////////////////////////////////////////////////////////////

	virtual bool filteringInitialize() override;
	virtual bool filteringInitialize(ExecutionContext * anEC);

	virtual bool finalizeFiltering();
	virtual bool finalizeFiltering(ExecutionContext * anEC);


	////////////////////////////////////////////////////////////////////////////
	// ( PRE / POST ) FILTER  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool prefilter() override;
	virtual bool prefilter(ExecutionContext & anEC) override;

	bool finalizePrefiltering();

	virtual bool postfilter() override;
	virtual bool postfilter(ExecutionContext & anEC) override;

	bool finalizePostfiltering();


	////////////////////////////////////////////////////////////////////////////
	// DEBUG PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	inline virtual bool debugEvalCommandImpl() override
	{
		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void toStream(OutStream & os) const override
	{
		if( mParameterWObject != nullptr )
		{
			mParameterWObject->toStream(os);
		}
	}

};


} /* namespace sep */

#endif /* AVMDEBUGPROCESSOR_H_ */

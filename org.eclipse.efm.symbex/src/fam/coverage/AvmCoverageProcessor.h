/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 nov. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCOVERAGEPROCESSOR_H_
#define AVMCOVERAGEPROCESSOR_H_

#include <fam/coverage/BaseCoverageFilter.h>
#include <fam/debug/IDebugProcessorProvider.h>

#include <fam/coverage/AvmCoverageHeuristicProperty.h>
#include <fam/coverage/AvmCoverageOneTraceDriver.h>
#include <fam/coverage/AvmCoverageTransitionView.h>

#include <fml/common/SpecifierElement.h>

#include <fml/runtime/ExecutionContext.h>

#include <sew/SymbexControllerRequestStatus.h>


namespace sep
{

class SymbexControllerUnitManager;
class WaitingStrategy;


class AvmCoverageProcessor  :
		public AutoRegisteredCoverageProcessorUnit< AvmCoverageProcessor >,
		public SymbexControllerRequestStatus,
		public IDebugProcessorProvider
{

	AVM_DECLARE_CLONABLE_CLASS( AvmCoverageProcessor )

	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_2(
			"avm::processor.COVERAGE",
			"avm::processor.COVERAGE_PROCESSOR")
	// end registration


	/**
	 * ATTRIBUTES
	 */
public:
	Specifier::DESIGN_KIND mScope;

	AvmCoverageHeuristicProperty mHeuristicProperty;

	AvmCoverageTransitionView  mTransitionCoverage;

	AvmCoverageOneTraceDriver  mOneTraceDriver;

//	AvmCoverageManyTraceDriver mManyTraceDriver;
	AvmCoverageOneTraceDriver  mManyTraceDriver;

protected:
	////////////////////////////////////////////////////////////////////////////
	// Computing variable
	ExecutionContext::child_iterator itChildEC;
	ExecutionContext::child_iterator endChildEC;



public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCoverageProcessor(SymbexControllerUnitManager & aControllerUnitManager,
			WObject * wfParameterObject)
	: RegisteredCoverageProcessorUnit( aControllerUnitManager , wfParameterObject,
			AVM_PREPOST_FILTERING_STAGE,
			PRECEDENCE_OF_ACTIVE_COVERAGE_PROCESSOR ),
	SymbexControllerRequestStatus( REQUEST_UNDEFINED_STATUS ),
	IDebugProcessorProvider( this ),

	mScope( Specifier::DESIGN_MODEL_KIND ),

	mHeuristicProperty( ),

	mTransitionCoverage( *this , wfParameterObject ),
	mOneTraceDriver ( *this , ENV ),
	mManyTraceDriver( *this , ENV ),

	////////////////////////////////////////////////////////////////////////////
	// Computing variable
	itChildEC( ),
	endChildEC( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmCoverageProcessor()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// PLUGIN PROCESSOR API
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl();


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	virtual void reportMinimum(OutStream & os) const;

	virtual void reportDefault(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

	virtual bool preprocess();

	virtual bool postprocess();


	////////////////////////////////////////////////////////////////////////////
	// FILTER API
	////////////////////////////////////////////////////////////////////////////

	virtual bool prefilter();

	virtual bool postfilter();


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API
	////////////////////////////////////////////////////////////////////////////
	/**
	 * STOP  | RELEASE
	 * RESET | RESTART | CONTINUE
	 * REQUEUE_WAITING | REQUEUE_RESERVE
	 * HEURISTIC | GOAL_ACHIEVED
	 */
	virtual void handleRequestRequeueWaitingTable(
			WaitingStrategy & aWaitingStrategy,
			avm_uint8_t aWeightMin, avm_uint8_t aWeightMax);


	////////////////////////////////////////////////////////////////////////////
	// DEBUG PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	virtual bool debugEvalCommandImpl();

	void dbgCommandDirectiveTransition();


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////
	virtual void toStream(OutStream & os) const
	{
		if( mParameterWObject != NULL )
		{
			mParameterWObject->toStream(os);
		}
	}



};

} /* namespace sep */

#endif /* AVMCOVERAGEPROCESSOR_H_ */

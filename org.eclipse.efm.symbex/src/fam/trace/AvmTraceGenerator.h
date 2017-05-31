/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMTRACEGENERATOR_H_
#define AVMTRACEGENERATOR_H_

#include <fam/api/AbstractProcessorUnit.h>

#include "TraceManager.h"
#include "TraceNumerizer.h"

#include <fml/trace/TraceFilter.h>


namespace sep
{


class AbstractTraceBuilder;
class AbstractTraceFormatter;

class ExecutableSystem;

class SymbexControllerUnitManager;


class AvmTraceGenerator  :
		public AutoRegisteredProcessorUnit< AvmTraceGenerator >
{

	AVM_DECLARE_CLONABLE_CLASS( AvmTraceGenerator )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3(
			"serializer#symbex#trace#basic",
			"serializer#symbex#trace#ttcn",
			"avm::processor.TRACE_GENERATOR" )
	// end registration


protected:
	/**
	 * ATTRIBUTE
	 */
	TraceManager mTraceManager;

	SolverDef::SOLVER_KIND mSolverKind;

	bool mNormalizedFlag;

	std::string mTraceTypeID;

	TraceFilter mTracePointFilter;

	AbstractTraceBuilder * mTraceBuilder;

	TraceNumerizer mTraceNumerizer;

	AbstractTraceFormatter * mTraceFormatter;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmTraceGenerator(SymbexControllerUnitManager & aControllerUnitManager,
			WObject * wfParameterObject)
	: RegisteredProcessorUnit( aControllerUnitManager ,
			wfParameterObject , AVM_POST_PROCESSING_STAGE ,
			DEFAULT_PRECEDENCE_OF_SERIALIZER_PROCESSOR ),
	mTraceManager( ),

	mSolverKind( SolverDef::SOLVER_UNDEFINED_KIND ),
	mNormalizedFlag( false ),
	mTraceTypeID( "" ),

	mTracePointFilter( ),
	mTraceBuilder( NULL ),
	mTraceNumerizer( ENV ),
	mTraceFormatter( NULL )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmTraceGenerator();


	/**
	 * mTracePointFilter
	 */
	TraceFilter & getTraceFilter()
	{
		return( mTracePointFilter );
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

	virtual void reportDefault(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddRegressionReportImpl(OutStream & os);

	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

	virtual bool postprocess();


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

#endif /* AVMTRACEGENERATOR_H_ */

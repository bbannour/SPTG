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

#include  <famcore/api/AbstractProcessorUnit.h>

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
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_4(
			"serializer#symbex#trace#basic",
			"serializer#symbex#trace#ttcn",
			"serializer#symbex#trace#sequencediagram",
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
			const WObject * wfParameterObject)
	: RegisteredProcessorUnit( aControllerUnitManager ,
			wfParameterObject , AVM_POST_PROCESSING_STAGE ,
			DEFAULT_PRECEDENCE_OF_SERIALIZER_PROCESSOR ),
	mTraceManager( ),

	mSolverKind( SolverDef::SOLVER_UNDEFINED_KIND ),
	mNormalizedFlag( false ),
	mTraceTypeID( "" ),

	mTracePointFilter( (wfParameterObject != WObject::_NULL_) ?
			wfParameterObject->getNameID() : "AvmTraceGenerator" ),
	mTraceBuilder( nullptr ),
	mTraceNumerizer( ENV ),
	mTraceFormatter( nullptr )
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

	/**
	 * mTraceBuilder
	 */
	AbstractTraceBuilder & getTraceBuilder()
	{
		return( * mTraceBuilder );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl() override;


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void reportSilent(OutStream & out) const override
	{
		// SILENT => NOTHING
	}

	virtual void reportDefault(OutStream & out) const override;


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddRegressionReportImpl(OutStream & out) const override;

	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

	virtual bool postprocess() override;


	////////////////////////////////////////////////////////////////////////////
	// FACTORY API used by PYTHON BINDINGS
	////////////////////////////////////////////////////////////////////////////

	bool configureDefaultImpl(const std::string & traceTypeID = "BASIC",
			bool showAssign = false, bool showTransition = false,
			bool enabledNumerization = false);

	void generate(OutStream & out, const ListOfExecutionContext & rootECs);


	static void generate(SymbexControllerUnitManager & aManager,
			OutStream & out, const std::string & traceTypeID,
			const ListOfExecutionContext & rootECs,
			bool showAssign, bool showTransition, bool enabledNumerization);

	inline static void generateUserTextualFormat(
			SymbexControllerUnitManager & aManager,
			OutStream & out, const ListOfExecutionContext & rootECs,
			bool showAssign, bool showTransition, bool enabledNumerization)
	{
		generate(aManager, out, "BASIC", rootECs,
				showAssign, showTransition, enabledNumerization);
	}

	inline static void generateSequenceDiagram(
			SymbexControllerUnitManager & aManager,
			OutStream & out, const ListOfExecutionContext & rootECs,
			bool showAssign, bool showTransition, bool enabledNumerization)
	{
		generate(aManager, out, "SEQUENCE_DIAGRAM", rootECs,
				showAssign, showTransition, enabledNumerization);
	}


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	virtual void toStream(OutStream & out) const override
	{
		if( mParameterWObject != nullptr )
		{
			mParameterWObject->toStream(out);
		}
	}

};


} /* namespace sep */

#endif /* AVMTRACEGENERATOR_H_ */

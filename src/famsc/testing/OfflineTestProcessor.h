/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: fev 2012
 *
 * Contributors:
 *  Jose Escobedo   (CEA LIST) jose.escobedo@cea.fr
 *  Mathilde Arnaud (CEA LIST) mathilde.arnaud@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef OFFLINETESTPROCESSOR_H_
#define OFFLINETESTPROCESSOR_H_

#include <famcore/api/AbstractProcessorUnit.h>

#include <famsc/testing/OfflineTestHelper.h>

#include <common/BF.h>

#include <collection/Typedef.h>
#include <collection/Bitset.h>

#include <fml/builtin/Identifier.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/runtime/ExecutionData.h>

#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <solver/api/SolverDef.h>


namespace sep
{


// list of port, sens, value or tvar, value
// RESTRICTION: PORTS AND VARIABLES CANNOT SHARE THE SAME NAMESPACE!!!
// this base structure is used to store observations of the form
// CHANNEL [?, !] [VALUE, VARIABLE]
//typedef List <BF> OneObs;
//typedef TracePoint OneObs;
/** TODO 2014/03/05
Création d'une structure de donnée ad'hoc pour les << points d'observation >>
*/

// vector of obs
// this structure stores a sequence (vector) of observations
// it is used to store the trace of observations, as well
// as a single observation (since we "can" have multiple communication channels,
// a "single observation" can consists of multiple structures of type OneObs)
//typedef Vector < OneObs > TraceOfObs;
//typedef TraceSequence TraceOfObs;


class RuntimeID;
class SymbexControllerUnitManager;
class TraceFactory;


class OfflineTestProcessor final :
		public AutoRegisteredProcessorUnit< OfflineTestProcessor > ,
		public OfflineTestHelper
{

	AVM_DECLARE_CLONABLE_CLASS( OfflineTestProcessor )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3(
			"test#offline",
			"avm::processor.OFFLINE_TESTER",
			"avm::processor.OFFLINETEST" )
	// end registration

	/**
	 * TYPEDEF
	 */
	enum VERDICT_KIND
	{
		VERDICT_PASS_KIND,

		VERDICT_WEAK_PASS_KIND,

		VERDICT_INCONCr_KIND,
		VERDICT_INCONCi_KIND,

		VERDICT_FAIL_KIND,

		VERDICT_ABORT_KIND,
		VERDICT_UNDEFINED_KIND
	};


public:
	/**
	 * INFO DATA
	 */
	BF INFO_OFFLINETEST_DATA;
	BF INFO_OFFLINETEST_DATA_PASS;
	BF INFO_OFFLINETEST_DATA_INCONC;
	BF INFO_OFFLINETEST_DATA_FAIL;
	BF INFO_OFFLINETEST_TP_PATH;
	BF INFO_OFFLINETEST_TARGET_STATE;

	/**
	 * ATTRIBUTE
	 */
	VERDICT_KIND theVerdictKind;

protected:
	// The user SOLVER choice
	SolverDef::SOLVER_KIND theSolverKind;

	// Trace step scheduling, in anEC->ioTrace, if folding is true
	bool mFoldingFlag;
	AVM_OPCODE mStepScheduler;

	// the trace is represented as a vector of lists
	TraceSequence theTrace;
//	TraceSequence theMergeTrace;

	// Vector of timed vars, so we know when there is an observation of "time"
	VectorOfString theTimedVarsVector;

	// counter that will tell us how many paths in the tree have accepted the "trace"
	std::size_t traceInPath;

	// we know if we have emitted a verdict by using this boolean (init to false)
	bool verdictEmitted;
	std::string theVerdict;

	List< ExecutionContext * > thePassEC;


	// test purpose given as a sequence of transition identifiers
	// (associated with the symbolic execution tree)
	TraceSequence theTestPurpose;

	// timed var param
	InstanceOfData * theTimeVarInstance;

	// post-process/emission of verdicts
	// Liste des ExecutionContext feuilles
	ListOfExecutionContext theLeavesECVector;

	const ExecutionContext * theSmallestTraceEC;

	Bitset theTraceCoverageBitSet;

	std::size_t theUncoverageTraceReportingCount;

	// time of reference (tau and projection)
	InstanceOfData * timeReferenceInstance;

	// the observable signals to do the projection "à la volée"
	TraceSequence theObsSignals;

	//the controllable signals to compute correctly verdicts inconc/fail
	TraceFilter theTraceFilter;

	// erased nodes
	int theErasedNodes;

	// flag set to true if the system is timed
	bool timedFlag;

	const ExecutionData & theMainExecutionData;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	OfflineTestProcessor(
			SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject);

	/**
	 * DESTRUCTOR
	 */
	virtual ~OfflineTestProcessor()
	{
		//!! NOTHING
	}


	/**
	 * mStepScheduler
	 */
	inline bool isStepOrdered() const
	{
		return( mStepScheduler == AVM_OPCODE_SEQUENCE );
	}

	inline bool isStepUnordered() const
	{
		return( mStepScheduler == AVM_OPCODE_INTERLEAVING );
	}

	inline bool isParallel() const
	{
		return( mStepScheduler == AVM_OPCODE_PARALLEL );
	}

	inline std::string strStepScheduler() const
	{
		return( OperatorLib::to_string(mStepScheduler) );
	}

	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// PLUGIN PROCESSOR API
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////
	virtual bool configureImpl() override;

	/**
	 * SPIDER TRACE
	 */
	virtual void traceInitSpider(OutStream & os) const override;

	virtual void traceStepSpider(OutStream & os,
			const ExecutionContext & anEC) const override;

	virtual void traceStopSpider(OutStream & os) const override;

	/**
	 * EVAL TRACE
	 */
	virtual void traceMinimumPreEval(
			OutStream & os, const ExecutionContext & anEC) const override;

	virtual void traceDefaultPreEval(
			OutStream & os, const ExecutionContext & anEC) const override;


	virtual void traceBoundEval(OutStream & os) const override;

	virtual void reportEval(OutStream & os) const override;


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////
//	TODO: fix bug to decomment this
	virtual void reportDefault(OutStream & out) const override;


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////
	virtual void tddRegressionReportImpl(OutStream & os) const override;

	////////////////////////////////////////////////////////////////////////////
	// FINAL SLICING TOOLS
	////////////////////////////////////////////////////////////////////////////

	virtual bool isSliceableContext(ExecutionContext & anEC) const override;

	bool finalSlicing();

	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////
	virtual bool preprocess() override;

	virtual bool postprocess() override;

	void searchLeaves(const ExecutionContext & anEC);

	/**
	 * EXIT API
	 */
	virtual bool exitImpl() override;


	////////////////////////////////////////////////////////////////////////////
	// FILTERING UTILS
	////////////////////////////////////////////////////////////////////////////

	bool AssignValuesIfObservable(
			ExecutionContext & anExecutionContext,
			TraceSequence & theLocalTrace);

	bool matchesIO(const BF & anElement,
			ExecutionContext & anExecutionContext,
			TraceSequence & theLocalTrace);

	bool matchesIO(const ExecutionConfiguration & anExecutionConfiguration,
			ExecutionContext & anExecutionContext,
			TraceSequence & theLocalTrace);

	bool updateTime(TracePoint * aTracePoint,
			ExecutionContext & anExecutionContext,
			TraceSequence * localTrace);

	bool lookupValue(AvmCode * anAC, ExecutionContext & anExecutionContext,
			const ExecutionConfiguration & anExecutionConfiguration,
			const InstanceOfPort & aPort,	AVM_OPCODE opcode,
			TraceSequence & theLocalTrace);

	bool lookupDelay(ExecutionContext & anExecutionContext,
			TraceSequence & theLocalTrace);

	bool hasObservableSignal(const BF & anElement);

	bool hasObservableSignal(const BF & anElement,
			const ExecutionConfiguration & anExexConf);

	bool portInObsSignals(
			const RuntimeID & runtimeCtx, const InstanceOfPort & port,
			AVM_OPCODE ioOpcodeFamily, AVM_OPCODE ioOpcodeSpecific);

	bool portInCtrlSignals(const TracePoint & portTP);

	bool assignValue(AvmCode * anAC, ExecutionContext & anExecutionContext,
			const ExecutionConfiguration & anExecutionConfiguration,
			InstanceOfPort * aPort, TraceSequence & localTrace, int offset = -1);

	bool assignValue(AvmCode * anAC, ExecutionContext & anExecutionContext,
			const BF & variableInstance, TracePoint * aTracePoint, int paramNb);

//	bool assignValue(AvmCode * anAC,
//			ExecutionContext & anExecutionContext,
//			const ExecutionConfiguration & anExecutionConfiguration,
//			BF dataVar, const InstanceOfPort * aPort,
//			TraceSequence & theLocalTrace, int offset = -1);

//	bool reAssignValue(AvmCode * anAC, EvaluationEnvironment theEnv,
//			ExecutionContext & anExecutionContext, BF aValue,
//			const InstanceOfPort * aPort, VectorOfPairOfVariableValue * aTable,
//			int offset = -1);


	////////////////////////////////////////////////////////////////////////////
	// FILTER API
	////////////////////////////////////////////////////////////////////////////
	virtual bool prefilter() override;
	virtual bool prefilter(ExecutionContext & anEC) override;

	virtual bool postfilter() override;
	virtual bool postfilter(ExecutionContext & anEC) override;



	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////
	virtual void toStream(OutStream & os) const override
	{
		if( mParameterWObject != WObject::_NULL_  )
		{
			mParameterWObject->toStream(os);
		}
	}


};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// OfflineTestProcessor Information
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class OfflineTestProcessorInfo : public Element,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( OfflineTestProcessorInfo )
{

	AVM_DECLARE_CLONABLE_CLASS( OfflineTestProcessorInfo )

protected:
	/**
	 * ATTRIBUTE
	 */
	// each node has an associated local copy of the trace
	TraceSequence theLocalTrace;
	// each node has associated a last observation, used later to emit verdicts
	TraceSequence theLastObs;
	// each node has associated a last transition name, used later to emit verdicts
	BF theLastTransition;
	// boolean to indicate that a path should not be analyzed anymore
	bool theAnalyzedMark;
	// time reference to compute delays
	BF theTimeReference;

	BF theTimeElapsing;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	OfflineTestProcessorInfo()
	: Element( CLASS_KIND_T( OfflineTestProcessorInfo ) ),
	theLocalTrace( ),
	theLastObs( ),
	theLastTransition( ),
	theAnalyzedMark( false ),
	theTimeReference( ),
	theTimeElapsing( ExpressionConstant::INTEGER_ZERO )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	OfflineTestProcessorInfo(const OfflineTestProcessorInfo & anInfo)
	: Element( anInfo ),
	theLocalTrace( anInfo.theLocalTrace ),
	theLastObs( anInfo.theLastObs ),
	theLastTransition( anInfo.theLastTransition ),
	theAnalyzedMark( anInfo.theAnalyzedMark ),
	theTimeReference( anInfo.theTimeReference ),
	theTimeElapsing( anInfo.theTimeElapsing )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~OfflineTestProcessorInfo()
	{
		//!! NOTHING
	}

	/*
	 * GETTER -- SETTER
	 * theFormulaTable
	 */
	inline TraceSequence & getLocalTrace()
	{
		return ( theLocalTrace );
	}

	inline void setLocalTrace(TraceSequence & aLocalTrace)
	{
		theLocalTrace = aLocalTrace;
	}

	//////////////

	inline TraceSequence & getLastObs()
	{
		return ( theLastObs );
	}

	inline void setLastObs(TraceSequence & anObs)
	{
		theLastObs = anObs;
	}

	//////////////

	inline BF & getLastTransition()
	{
		return ( theLastTransition );
	}

	inline const BF & getLastTransition() const
	{
		return ( theLastTransition );
	}

	inline void setLastTransition(const BF & aTrans)
	{
		theLastTransition = aTrans;
	}

	//////////////

	inline BF & getTimeReference()
	{
		return ( theTimeReference );
	}

	inline const BF & getTimeReference() const
	{
		return ( theTimeReference );
	}

	inline void setTimeReference(const BF & aReference)
	{
		theTimeReference = aReference;
	}

	//////////////

	inline const BF & getTimeElapsing()
	{
		return ( theTimeElapsing );
	}

	inline void addTimeElapsingDelta(const BF & aDelta)
	{
		theTimeElapsing = ExpressionConstructor::addExpr(theTimeElapsing, aDelta);
	}

	inline void setTimeElapsing(const BF & aTimeElapsing)
	{
		theTimeElapsing = aTimeElapsing;
	}

	//////////////


	inline bool isAnalyzedMark()
	{
		return ( theAnalyzedMark );
	}

	inline void setAnalyzedMark(bool mark)
	{
		theAnalyzedMark = mark;
	}

	/**
	 * Serialization
	*/
	void toStream(OutStream & os) const override;

	void toFscn(OutStream & os) const;

};





} /* namespace sep */
#endif /* OFFLINETESTPROCESSOR_H_ */

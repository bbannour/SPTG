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

#include <fam/api/AbstractProcessorUnit.h>

#include <common/BF.h>

#include <collection/Typedef.h>

#include <fml/executable/InstanceOfData.h>
#include <fml/expression/AvmCode.h>
#include <fml/builtin/Identifier.h>

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


class OfflineTestProcessor  :
		public AutoRegisteredProcessorUnit< OfflineTestProcessor >
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

	// the trace is represented as a vector of lists
	TraceSequence theTrace;
	TraceSequence theMergeTrace;

	// Vector of timed vars, so we know when there is an observation of "time"
	VectorOfString theTimedVarsVector;

	// counter that will tell us how many paths in the tree have accepted the "trace"
	int traceInPath;

	// we know if we have emitted a verdict by using this boolean (init to false)
	bool verdictEmitted;
	std::string theVerdict;

	// test purpose given as a sequence of transition identifiers
	// (associated with the symbolic execution tree)
	TraceSequence theTestPurpose;

	// timed var param
	BF theTimeVarInstance;

	// post-process/emission of verdicts
	// Liste des ExecutionContext feuilles
	ListOfExecutionContext theLeavesECVector;

	// time of reference (tau and projection)
	BF timeReferenceInstance;

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
			WObject * wfParameterObject);

	/**
	 * DESTRUCTOR
	 */
	virtual ~OfflineTestProcessor()
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
//	TODO: fix bug to decomment this
	virtual void reportDefault(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////
	virtual void tddRegressionReportImpl(OutStream & os);

	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////
	virtual bool preprocess();

	virtual bool postprocess();

	/**
	 * EXIT API
	 */
	virtual bool exitImpl();

	////////////////////////////////////////////////////////////////////////////
	// FILTER API
	////////////////////////////////////////////////////////////////////////////
	bool AssignValuesIfObservable(
			ExecutionContext & anExecutionContext,
			TraceSequence & theLocalTrace);

	bool hasIO(const BF & anElement,
			ExecutionContext & anExecutionContext,
			TraceSequence & theLocalTrace);

	bool hasIO(ExecutionConfiguration * anExecutionConfiguration,
			ExecutionContext & anExecutionContext,
			TraceSequence & theLocalTrace);

	bool updateTime(TracePoint * aTracePoint,
			ExecutionContext & anExecutionContext,
			TraceSequence * localTrace);

	bool lookupValue(AvmCode * anAC, ExecutionContext & anExecutionContext,
			ExecutionConfiguration * anExecutionConfiguration,
			InstanceOfPort * aPort,	AVM_OPCODE opcode,
			TraceSequence & theLocalTrace);

	bool hasIO(const BF & anElement);

	bool hasObservableSignal(const BF & anElement);

	bool hasObservableSignal(const BF & anElement,
			const ExecutionConfiguration * anExexConf);

	bool portInObsSignals(const RuntimeID & runtimeCtx,
			InstanceOfPort * port, AVM_OPCODE ioOpcode);

	bool portInCtrlSignals(TracePoint * portTP);

	virtual bool prefilter();
	virtual bool prefilter(ExecutionContext & anEC);

	virtual bool postfilter();
	virtual bool postfilter(ExecutionContext & anEC);

	bool assignValue(AvmCode * anAC, ExecutionContext & anExecutionContext,
			ExecutionConfiguration * anExecutionConfiguration,
			InstanceOfPort * aPort, TraceSequence & localTrace, int offset = -1);

	bool assignValue(AvmCode * anAC, ExecutionContext & anExecutionContext,
			const BF & variableInstance, TracePoint * aTracePoint, int paramNb);

//	bool assignValue(AvmCode * anAC,
//			ExecutionContext & anExecutionContext,
//			ExecutionConfiguration * anExecutionConfiguration,
//			BF dataVar, InstanceOfPort * aPort,
//			TraceSequence & theLocalTrace, int offset = -1);

//	bool reAssignValue(AvmCode * anAC, EvaluationEnvironment theEnv,
//			ExecutionContext & anExecutionContext, BF aValue,
//			InstanceOfPort * aPort, VectorOfPairOfVariableValue * aTable,
//			int offset = -1);


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////
	virtual void toStream(OutStream & os) const
	{
		if( mParameterWObject != WObject::_NULL_  )
		{
			mParameterWObject->toStream(os);
		}
	}

	void printTrace(const TraceSequence & aTrace,
			const std::string & title = "The (local) trace:",
			const std::string & tab = "\t")
	{
		AVM_OS_LOG << tab << title << std::endl;
		aTrace.toStream( AVM_OS_LOG << AVM_TAB_INDENT );
		AVM_OS_LOG << END_INDENT << std::endl;
//		TraceSequence::const_iterator it = aTrace.begin();
//		for( ; it != aTrace.end() ; ++it )
//		{
////		if ( (*it).first().is< InstanceOfData >()
//				&& (theTimedVarsVector.getAstNameID()
//					== (*it).first().to_ptr<
//							InstanceOfData >()->getAstNameID()) )
////		{
////			AVM_OS_LOG << TAB << "XXXXXXXXXXXXXXtimevar: "
////						<< (*it).first().str() << std::endl;
////		}
//			//AVM_OS_LOG << TAB << "XXXXXXXXXXXXXX22222: "
//					<< (*it).first().to_ptr<
//							InstanceOfData >()->getAstNameID()
//					<< std::endl;
//			if ( (*it).first().is< InstanceOfData >()
//				&& (theTimeVarInstance->getAstNameID()
//					== (*it).first().to_ptr<
//							InstanceOfData >()->getAstNameID()) )
//			{
//				// it is a time var, print first and second values
//				AVM_OS_LOG << tab << "timevar: " << (*it).first().str() << std::endl
//						<< tab << "value: " << (*it).second().str() <<  std::endl
//						<< tab << REPEAT("==========", 5) << std::endl;
//			}
//			else
//			{
//				// it is a port, sens, value observation
//			AVM_OS_LOG << tab << "port: " << (*it).first().str() << std::endl
//					<< tab << "sens: " << (*it).second().str() <<  std::endl
//					<< tab << "value: " << (*it).at(3).str() << std::endl
//					<< tab << REPEAT("==========", 5) << std::endl;
//			}
//		}
	}

	void makeLocalObs(TraceSequence & anObs, TraceSequence & aTrace)
	{
		/*
		 * Creates a single observation from the trace aTrace.
		 * A single observation can consist of multiple structures of type
		 * OneObs, since we may have multiple communication channels
		 */

//		anObs.clear();
		anObs.points.clear();

		// If the system is timed, a single observation consists of
		// the time delay
		// all communication actions occurring before the next time delay
		if (aTrace.points.nonempty() && timedFlag)
		{
			// start with time obs
			anObs.points.append( aTrace.points.first() );

			BFList::raw_iterator< TracePoint > itPoint = aTrace.points.begin();
			BFList::raw_iterator< TracePoint > endPoint = aTrace.points.end();
			for( ++itPoint ; (itPoint != endPoint) ; ++itPoint )
			{
				if( itPoint->isTime() )
				{
					break;
				}
				else
				{
					anObs.points.append(*itPoint);
				}
			}
		}

		else if (aTrace.points.nonempty())
		{
			anObs.copyTrace(aTrace);
		}

//		if (aTrace.points.size() >0)
//		{
//
//		}

	}

	void removeOneObs(TraceSequence & aTrace)
	{
		/*
		 * Deletes one observation from the trace.
		 * We assume that one observation consists of a delay and
		 * of one or more inputs/outputs (up to the next delay).
		 */

		if (aTrace.points.size() >0)
		{
			// start with time obs
			aTrace.points.remove_first();

			if (aTrace.points.size() >0)
			{
				BFList::const_iterator itPoint = aTrace.points.begin();
				BFList::const_iterator endPoint = aTrace.points.end();
				TracePoint * aTracePoint = (*itPoint).to_ptr< TracePoint >();
				while ( (itPoint != endPoint) && !aTracePoint->isTime())
				{
					aTrace.points.remove_first();
					aTracePoint = (*itPoint).to_ptr< TracePoint >();
				}

			}
		}
	}


	bool parseMergedTrace(const std::string & filePath,
			TraceSequence & aTrace, const BF & theTimeVar);

	bool parseMergedTrace(
			TraceFactory & aTraceFactory, const std::string & filePath,
			TraceSequence & aMergeTrace, const BF & theTimeVar);

	bool parseMergedTrace(TraceFactory & aTraceFactory,
			const std::string &format, const std::string & filePath,
			TraceSequence & aMergeTrace, const BF & theTimeVar);

	bool parseTestPurpose(
			const std::string & filePath, TraceSequence & testPurpose);

	static void transitionInList(
			const BF & aFF, TraceSequence & aTestPurpose, bool & flag);

	// post-process API

	void searchLeaves(const ExecutionContext & anEC);

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// OfflineTestProcessor Information
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class OfflineTestProcessorInfo :
		public Element,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( OfflineTestProcessorInfo )
{

	AVM_DECLARE_CLONABLE_CLASS( OfflineTestProcessorInfo )


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
	theTimeReference( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	OfflineTestProcessorInfo(const OfflineTestProcessorInfo & anInfo)
	: Element( anInfo ),
	theLocalTrace(anInfo.theLocalTrace),
	theLastObs(anInfo.theLastObs),
	theLastTransition(anInfo.theLastTransition),
	theAnalyzedMark(anInfo.theAnalyzedMark),
	theTimeReference(anInfo.theTimeReference)
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
		//aReference.makeWritable();
		theTimeReference = aReference;
	}

	//////////////


	inline bool getTheAnalyzedMark()
	{
		return ( theAnalyzedMark );
	}

	inline void setTheAnalyzedMark(bool mark)
	{
		theAnalyzedMark = mark;
	}

	/**
	 * Serialization
	*/
	void toStream(OutStream & os) const;

	void toFscn(OutStream & os) const;


protected:

	/*ATTRIBUTES*/

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

};





} /* namespace sep */
#endif /* OFFLINETESTPROCESSOR_H_ */

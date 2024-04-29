/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: mai 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SECURITY_ANALYSISPROCESSOR_H_
#define SECURITY_ANALYSISPROCESSOR_H_

#include <string>

#include  <famcore/api/AbstractProcessorUnit.h>


namespace sep
{

class BF;

class ExecutionConfiguration;
class ExecutionData;

class SymbexControllerUnitManager;


// attacker actions for parsing purposes: tuples port and direction (sens)
typedef std::pair<std::string, std::string> str_pair__;
typedef std::vector<str_pair__> str_pair_vec__;
typedef str_pair_vec__::iterator str_pair_vec_iter__;

enum SECURITY_ANALYSIS_MARK
{
	NOT_MARKED,
	NOT_ROBUST,
	ROBUST
};


class SecurityAnalysisProcessor  :
		public AutoRegisteredProcessorUnit< SecurityAnalysisProcessor >
{

	AVM_DECLARE_CLONABLE_CLASS( SecurityAnalysisProcessor )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_2(
			"avm::processor.SECURITY_ANALYSIS",
			CONS_WID2("security", "analysis") )
	// end registration



public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SecurityAnalysisProcessor(
			SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject);

	/**
	 * DESTRUCTOR
	 */
	virtual ~SecurityAnalysisProcessor()
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
	virtual bool configureImpl() override;

	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////
	virtual void reportDefault(OutStream & os) const override;


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////
	virtual bool preprocess() override;

	virtual bool postprocess() override;

	////////////////////////////////////////////////////////////////////////////
	// FILTER API
	////////////////////////////////////////////////////////////////////////////

	bool hasAttackerAction(const BF & anElement);

	bool hasAttackerAction(const BF & anElement,
			const ExecutionConfiguration * anExC);

	bool portInAttackerActions(const std::string & attMachineName,
			const std::string & swdMachineName,
			const std::string & portName,
			const std::string & sens);

	virtual bool prefilter() override;
	virtual bool prefilter(ExecutionContext & anEC) override;

	virtual bool postfilter() override;
	virtual bool postfilter(ExecutionContext & anEC) override;


	bool recursiveAnalyseElement(const BF & aBF,
			VectorOfAvmTransition & observedSequence,
			avm_integer_t & localK,
			SECURITY_ANALYSIS_MARK & analyzedMark);

	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////
	virtual void toStream(OutStream & os) const override
	{
		if( mParameterWObject != WObject::_NULL_ )
		{
			mParameterWObject->toStream(os);
		}
	}

	void printSequence(VectorOfString & aSequence,
			const std::string & title = "The (global) sequence:",
			const std::string & TAB = "\t")
	{
		AVM_OS_LOG << TAB << title << std::endl;
		for( VectorOfString::iterator it = aSequence.begin() ;
				it != aSequence.end() ; ++it)
		{
			AVM_OS_LOG << TAB << "transition: " << (*it) << std::endl;
		}
		AVM_OS_LOG << TAB << REPEAT("==========", 5) << std::endl;
	}

	/**
	 * initTransitionList
	 */
	virtual bool initSequenceOfTransitions(VectorOfString & namesVector,
			VectorOfAvmTransition & avmTransitionsVector,
			const std::string & sectionName);

	// post-process API

	void searchLeavesWithPositiveK(ExecutionContext * anEC);

protected:

	// the sequence of action names to be performed by the attacker
	VectorOfString theAttackSequenceTransitionNameVector;
	// the sequence of actions to be performed by the attacker
	VectorOfAvmTransition theAttackSequenceTransitionVector;

	// the sequence of action names of swd warnings
	VectorOfString theWarningsTransitionNameVector;
	// the sequence of actions of swd warnings
	VectorOfAvmTransition theWarningsTransitionVector;

	// Vector of timed vars, so we know when there is an observation of "time" (WILL WE HANDLE TIME?)
	// VectorOfString theTimedVarsVector;

	// The emitted verdict
	std::string theVerdict;
	// Flag to know when to stop the execution
	bool theVerdictEmited;

	// timed var param (WILL WE HANDLE TIME?)
	// BF theTimeVarInstance;

	// post-process/emission of verdicts
	// List of leaves with positive K (the attacker intervened in the path)
	ListOfExecutionContext theLeavesECVector;

	// time of reference (tau and projection) (WILL WE HANDLE TIME?)
	// BF timeReferenceInstance;

	// erased nodes
	int theErasedNodes;

	// k actions parameter
	avm_integer_t theKActions;

	// SWD and attacker machine names
	std::string theSwdMachineName, theAttMachineName;

	const ExecutionData & theMainExecutionData;
};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// SecurityAnalysisProcessor Information
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class SecurityAnalysisProcessorInfo : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( SecurityAnalysisProcessorInfo )
{

	AVM_DECLARE_CLONABLE_CLASS( SecurityAnalysisProcessorInfo )


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */

	SecurityAnalysisProcessorInfo()
	: Element( CLASS_KIND_T( SecurityAnalysisProcessorInfo ) ),
	theObservedSequenceVector( ),
	theLocalK( 0 ),
	theAnalyzedMark( NOT_MARKED )
	//theTimeReference( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	SecurityAnalysisProcessorInfo(const SecurityAnalysisProcessorInfo & anInfo)
	: Element( anInfo ),
	theObservedSequenceVector(anInfo.theObservedSequenceVector),
	theLocalK(anInfo.theLocalK),
	theAnalyzedMark(anInfo.theAnalyzedMark)
	//theTimeReference(anInfo.theTimeReference)
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~SecurityAnalysisProcessorInfo()
	{
		//!! NOTHING
	}

	/*
	 * GETTER -- SETTER
	 * theFormulaTable
	 */
	inline VectorOfAvmTransition & getObservedSequence()
	{
		return ( theObservedSequenceVector );
	}

	inline void setObservedSequence(VectorOfAvmTransition & anObservedSequence)
	{
		theObservedSequenceVector = anObservedSequence;
	}

	//////////////

	inline avm_integer_t & getLocalK()
	{
		return ( theLocalK );
	}

	inline void setLocalK(const int & aLocalK)
	{
		theLocalK = aLocalK;
	}

	//////////////
/* (WILL WE HANDLE TIME?)
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
*/
	//////////////


	inline SECURITY_ANALYSIS_MARK getTheAnalyzedMark()
	{
		return ( theAnalyzedMark );
	}

	inline std::string strTheAnalyzedMark()
	{
		switch ( theAnalyzedMark )
		{
		case NOT_MARKED:
			return "Not marked";
		case NOT_ROBUST:
			return "Not robust";
		case ROBUST:
			return "Robust";
		default:
			return "Error: strTheAnalyzedMark: invalid mark!";
		}
	}

	inline void setTheAnalyzedMark(SECURITY_ANALYSIS_MARK mark)
	{
		theAnalyzedMark = mark;
	}

	inline bool isMarked()
	{
		return ( theAnalyzedMark != NOT_MARKED );
	}
	/**
	 * Serialization
	*/
	void toStream(OutStream & os) const override;

	void toFscn(OutStream & os) const;


protected:

	/*ATTRIBUTES*/

	// each node has an associated local copy of the so-far observed sequence of attacker actions
//	VectorOfString theObservedSequenceName;
	VectorOfAvmTransition theObservedSequenceVector;

	// each node has a copy of the observed actions from the attacker
	// (it is just the difference between len(theAttacksSequence) and len(theObservedSequence))
	avm_integer_t theLocalK;
	// boolean to indicate that a path should not be analyzed anymore
	SECURITY_ANALYSIS_MARK theAnalyzedMark;
	// time reference to compute delays (WILL WE HANDLE TIME?)
	//BF theTimeReference;

};





} /* namespace sep */
#endif /* SECURITY_ANALYSISPROCESSOR_H_ */

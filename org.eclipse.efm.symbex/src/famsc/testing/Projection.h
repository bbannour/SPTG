/*
 * TestCaseGeneration.h
 *
 *  Created on: 13 sept. 2017
 *      Author: NN245105
 */

#ifndef FAM_TESTING_TESTCASEGENERATION_H_
#define FAM_TESTING_TESTCASEGENERATION_H_

#include <common/AvmPointer.h>
#include <famcore/api/AbstractProcessorUnit.h>

#include <fml/expression/AvmCode.h>
#include <fml/workflow/WObject.h>

#include <sew/Workflow.h>
#include <fml/trace/TraceChecker.h>
#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>
#include <fml/symbol/TableOfSymbol.h>

namespace sep{

class ExecutionContext;
class InstanceOfPort;
class OutStream;


class Projection : public AutoRegisteredProcessorUnit < Projection >
{
    // MANDATORY for Smart Pointer services
    AVM_DECLARE_CLONABLE_CLASS( Projection )

    /**
     * MyFAM
     * for automatic registration in the FAM repository
     * the UFID key
     * need for instanciation from the SEW specification file
     */
//    AVM_INJECT_AUTO_REGISTER_UFID_KEY( "TestCaseGeneration" )
    AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY(
    			"Projection" )
    // end registration

protected:
    /**
     * ATTRIBUTE
     */

	//the controllable signals to compute correctly verdicts inconc/fail
	AvmCode mTPasTransitionSequence;

	AvmCode mIOSequence;

	AvmCode mPRESERVED;

	AvmCode mQUIESCENCE;

	avm_offset_t mCurrentTraceIndex;

	TraceChecker mTraceChecker;

	//the controllable signals to compute correctly verdicts inconc/fail
	TraceFilter mProjection;

	TableOfSymbol mTableOfPort;

	ListOfExecutionContext mNewGeneratedChildEC;

	Vector<std::pair<InstanceOfPort *,
	    		BF>> mListOfOutputPortsWithNodeConditions;

public:
    /**
     * CONSTRUCTOR
     */
	Projection(SymbexControllerUnitManager & aManager, const WObject * aParameterForm)
    : AutoRegisteredProcessorUnit(aManager, aParameterForm,
	AVM_PRE_FILTERING_STAGE | AVM_POST_FILTERING_STAGE | AVM_POST_PROCESSING_STAGE ),
	mTPasTransitionSequence( OperatorManager::OPERATOR_SEQUENCE ),
	mIOSequence( OperatorManager::OPERATOR_SEQUENCE ),
	mPRESERVED( OperatorManager::OPERATOR_OR ),
	mQUIESCENCE( OperatorManager::OPERATOR_OR ),
	mCurrentTraceIndex(0),
	mTraceChecker(this->ENV),
	mProjection( "Projection" ),
	mTableOfPort(),
	mNewGeneratedChildEC(),
	mListOfOutputPortsWithNodeConditions()
    {

    }

   ~Projection()
	{

	}

    /**
     * CONFIGURE allows to take into account user's parameters: at the moment, it takes as input ... à compléter
     */
    virtual bool configureImpl() override;

    /**
     * REPORT TRACE
     */
    virtual void reportDefault(OutStream & os) const override;

    ////////////////////////////////////////////////////////////////////////////
    // PROCESSING API
    ////////////////////////////////////////////////////////////////////////////

    /**
     * preProcessing
     */
    virtual bool preprocess() override;

    /**
     * postprocessing
     */
    virtual bool postprocess() override;

    ////////////////////////////////////////////////////////////////////////////
    // FILTERING API
    ////////////////////////////////////////////////////////////////////////////

    /**
     * preFiltering
     */
    virtual bool prefilter(ExecutionContext & anEC) override;

    /**
     * postFiltering
     * Every post filter has to implement this method
     */
    virtual bool postfilter() override;

    virtual bool postfilter(ExecutionContext & anEC) override;

    /**
     * UTILS
     */

};

}

#endif /* FAM_TESTING_TESTCASEGENERATION_H_ */

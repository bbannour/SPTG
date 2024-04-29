/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 June. 2018
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_TESTING_PROJECTION_H_
#define FAM_TESTING_PROJECTION_H_

#include <common/AvmPointer.h>
#include <famcore/api/AbstractProcessorUnit.h>

#include <fml/expression/AvmCode.h>
#include <fml/workflow/WObject.h>

#include <sew/Workflow.h>
#include <fml/trace/TraceChecker.h>
#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>
#include <fml/symbol/TableOfSymbol.h>
#include <famsc/testing/TestCaseHelper.h>
#include <famsc/testing/UnitaryTestCaseGeneratorProvider.h>

namespace sep{

class ExecutionContext;
class InstanceOfPort;
class OutStream;


class CoverageTestPurpose :
		public AutoRegisteredProcessorUnit < CoverageTestPurpose >,
		public TestCaseHelper
{
    // MANDATORY for Smart Pointer services
    AVM_DECLARE_CLONABLE_CLASS( CoverageTestPurpose )

    /**
     * MyFAM
     * for automatic registration in the FAM repository
     * the UFID key
     * need for instanciation from the SEW specification file
     */
    AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY(
    			"CoverageTestPurpose" )
    // end registration

protected:
    /**
     * ATTRIBUTE
     */

	//the controllable signals to compute correctly verdicts inconc/fail
	AvmCode mTPasSequence;

	avm_offset_t mCurrentTraceIndex;

	TraceChecker mTraceChecker;

	ExecutionContext * mRootOfGraphBeforeProjection;

	ListOfExecutionContext mListOfECToAddInProjection;

//	ListOfExecutionContext mListOfECToAppendAsChildsOfParentEC;

	ListOfExecutionContext mListECToDelete;

	ListOfExecutionContext mListECHavingSamePortAfterProjection;

	RuntimeID mQuiescenceRID;
	RuntimeID mFailRID;
	RuntimeID mINCONCRID;

public:
    /**
     * CONSTRUCTOR
     */
	CoverageTestPurpose(SymbexControllerUnitManager & aManager, const WObject * aParameterForm)
    : AutoRegisteredProcessorUnit(aManager, aParameterForm,
	AVM_PRE_FILTERING_STAGE | AVM_POST_FILTERING_STAGE | AVM_POST_PROCESSING_STAGE ),
	mTPasSequence( OperatorManager::OPERATOR_SEQUENCE ),
	mCurrentTraceIndex(0),
	mTraceChecker(this->ENV),
	mRootOfGraphBeforeProjection(),
	mListOfECToAddInProjection( ),
//	mListOfECToAppendAsChildsOfParentEC( ),
	mListECToDelete ( ),
	mListECHavingSamePortAfterProjection ( ),
	mQuiescenceRID( ),
	mFailRID( ),
	mINCONCRID( )
    {

    }

   ~CoverageTestPurpose()
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
	 * filteringInitialize
	 */
	virtual bool filteringInitialize() override;

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

	void getECsHavingSamePortAfterProjection(  ExecutionContext & anEC );

	void deleteECsHavingSamePortAfterProjection();

	void deleteECsAfterProjection();

	void projection(ExecutionContext & anEC, BF projComponentFilter);

	void synchronizeDelaysAfterProjection( ExecutionContext & anEC );

};

}

#endif /* FAM_TESTING_PROJECTION_H_ */

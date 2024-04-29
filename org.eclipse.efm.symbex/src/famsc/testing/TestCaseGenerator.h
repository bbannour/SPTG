/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 Sep. 2017
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_TESTING_TESTCASEGENERATOR_H_
#define FAM_TESTING_TESTCASEGENERATOR_H_

#include <common/AvmPointer.h>
#include <famcore/api/AbstractProcessorUnit.h>
#include <famsc/testing/TestCaseHelper.h>
#include <fml/expression/AvmCode.h>
#include <fml/workflow/WObject.h>

#include <sew/Workflow.h>
#include <fml/trace/TraceChecker.h>
#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>
#include <fml/symbol/TableOfSymbol.h>
#include <algorithm>


#include <map>

namespace sep{

class ExecutionContext;
class InstanceOfPort;
class OutStream;
class AbstractTestCaseGeneratorProvider;


class TestCaseGenerator :
		public AutoRegisteredProcessorUnit < TestCaseGenerator >,
		public TestCaseHelper
{
	// MANDATORY for Smart Pointer services
	AVM_DECLARE_CLONABLE_CLASS( TestCaseGenerator )

	/**
	 * MyFAM
	 * for automatic registration in the FAM repository
	 * the UFID key
	 * need for instanciation from the SEW specification file
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY(
			"TestCaseGeneration" )
	// end registration

protected:

	AbstractTestCaseGeneratorProvider * mTestCaseFacet;

public:
	/**
	 * CONSTRUCTOR
	 */
	TestCaseGenerator(SymbexControllerUnitManager & aManager,
			const WObject * aParameterForm)
	: AutoRegisteredProcessorUnit(aManager, aParameterForm,
	AVM_PRE_FILTERING_STAGE | AVM_POST_FILTERING_STAGE | AVM_POST_PROCESSING_STAGE ),
	mTestCaseFacet ( nullptr )
	{

	}

	~TestCaseGenerator()
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
//	virtual bool filteringInitialize() override;

	/**
	 * preFiltering
	 */
	virtual bool prefilter(ExecutionContext & anEC) override;

};

}

#endif /* FAM_TESTING_TESTCASEGENERATOR_H_ */

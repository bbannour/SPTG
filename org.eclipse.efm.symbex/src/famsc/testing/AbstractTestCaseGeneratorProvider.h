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

#ifndef FAM_TESTING_ABSTRACTTESTCASEGENERATORPROVIDER_H_
#define FAM_TESTING_ABSTRACTTESTCASEGENERATORPROVIDER_H_


namespace sep
{

class Configuration;

class EvaluationEnvironment;

class ExecutionContext;

class TestCaseGenerator;

class WObject;


class AbstractTestCaseGeneratorProvider
{

protected:
	/**
	 * ATTRIBUTES
	 */
	TestCaseGenerator & mTestCaseGenerator;

	EvaluationEnvironment & ENV;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AbstractTestCaseGeneratorProvider(TestCaseGenerator & aTestCaseGenerator);

	/**
	 * DESTRUCTOR
	 */
	virtual ~AbstractTestCaseGeneratorProvider()
	{
		//!! NOTHING
	}

	Configuration & getConfiguration() const;


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configure(const WObject * wfParameterObject);

	virtual bool configureImpl(const WObject * wfParameterObject) = 0;
	/**
	 * CONFIGURE allows to take into account user's parameters: at the moment, it takes as input ... à compléter
	 */

	/**
	 * REPORT TRACE
	 */
//	virtual void reportDefault(OutStream & os) const;



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
	virtual bool prefilter(ExecutionContext & anEC)
	{
		return true;
	}

	/**
	 * postFiltering
	 * Every post filter has to implement this method
	 */
//	virtual bool postfilter() override;
//
//	virtual bool postfilter(ExecutionContext & anEC) override;

	////////////////////////////////////////////////////////////////////////////
	// PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * preProcessing
	 */
	virtual bool preprocess()
	{
		return true;
	}

	/**
	 * postprocessing
	 */
	bool postprocess();

	virtual bool postprocessImpl() = 0;

};


} /* namespace sep */

#endif /* ABSTRACTTRACEFORMATTER_H_ */

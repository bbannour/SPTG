/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 24 mars 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef IPROCESSORUNITTEST_H_
#define IPROCESSORUNITTEST_H_

#include <printer/OutStream.h>


namespace sep
{

class AbstractProcessorUnit;


class IProcessorUnitTest
{

private:
	/**
	 * ATTRIBUTES
	 */
	AbstractProcessorUnit & mProcessorUnit;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	IProcessorUnitTest(AbstractProcessorUnit & aProcessorUnit)
	: mProcessorUnit( aProcessorUnit )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~IProcessorUnitTest()
	{
		//!! NOTHING
	}


	/**
	 * LOCAL CONFIGURATION
	 */
	virtual bool tddConfigureImpl();


	/**
	 * ProcessorUnit
	 * report beginning / ending
	 */
	virtual void tddReportBeginning(OutStream & os) const;

	virtual void tddReportEnding(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// UNIT TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddUnitReport(OutStream & os) const
	{
		tddReportBeginning(os);

		os << INCR_INDENT;
		tddUnitReportImpl(os);
		os << DECR_INDENT;

		tddReportEnding(os);
	}

	virtual void tddUnitReportImpl(OutStream & os) const
	{
		//!! TO IMPLEMENT
	}


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddRegressionReport(OutStream & os) const
	{
		tddReportBeginning(os);

		os << INCR_INDENT;
		tddRegressionReportImpl(os);
		os << DECR_INDENT;

		tddReportEnding(os);
	}

	virtual void tddRegressionReportImpl(OutStream & os) const
	{
		//!! TO IMPLEMENT
	}

};


} /* namespace sep */

#endif /* IPROCESSORUNITTEST_H_ */

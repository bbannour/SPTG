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

#include "IProcessorUnitTest.h"

#include <util/avm_vfs.h>

#include <fam/api/AbstractProcessorUnit.h>

#include <sew/Configuration.h>
#include <sew/Workflow.h>


namespace sep
{


/**
 * LOCAL CONFIGURATION
 */
// TEST DRIVEN DEVELOPMENT
//section TDD
//	@report = "avm.tdd";
//
//	@regression = true;
//	@unit = true;
//endsection TDD

bool IProcessorUnitTest::tddConfigureImpl()
{
	WObject * theTDD = Query::getRegexWSequence(
			mProcessorUnit.getParameterWObject(), OR_WID2("tdd", "TDD"));
	if( theTDD != WObject::_NULL_ )
	{
		// Locally enable or not non-regression testing
		bool isRegressionTesting = Query::getWPropertyBoolean(
				mProcessorUnit.getConfiguration().getWorkflow().getTDD(),
				"regression", false);

		isRegressionTesting = Query::getWPropertyBoolean(
				theTDD, "regression", isRegressionTesting);

		// Locally enable or not Unit testing
		bool isUnitTesting = Workflow::INSTANCE->isTddUnitTesting();
		isUnitTesting = Query::getWPropertyBoolean(
				theTDD, "unit", isUnitTesting);

		// Locally report file location
		if( isRegressionTesting || isUnitTesting )
		{
			std::string tddLocation =
					Query::getWPropertyString(theTDD, "report", "");
			if( not tddLocation.empty() )
			{
				tddLocation = VFS::native_path(tddLocation, VFS::ProjectTddPath);
			}
		}
	}

	return( true );
}

/**
 * ProcessorUnit
 * report beginning / ending
 */
void IProcessorUnitTest::tddReportBeginning(OutStream & os) const
{
	if( mProcessorUnit.hasParameterWObject() )
	{
		os << TAB << "processor "
				<< mProcessorUnit.getParameterWObject()->getFullyQualifiedNameID()
				<< std::endl;
	}
}

void IProcessorUnitTest::tddReportEnding(OutStream & os) const
{
	if( mProcessorUnit.hasParameterWObject() )
	{
		os << TAB << "// end processor "
				<< mProcessorUnit.getParameterWObject()->getFullyQualifiedNameID()
				<< std::endl << std::endl;
	}
}


} /* namespace sep */

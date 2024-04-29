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

#include "AbstractTestCaseGeneratorProvider.h"

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>
#include    <famsc/testing/TestCaseGenerator.h>
#include <computer/EvaluationEnvironment.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
AbstractTestCaseGeneratorProvider::AbstractTestCaseGeneratorProvider(TestCaseGenerator & aTestCaseGenerator)
: mTestCaseGenerator( aTestCaseGenerator ),
  ENV( aTestCaseGenerator.getENV() )
{
	//!! NOTHING
}

Configuration & AbstractTestCaseGeneratorProvider::getConfiguration() const
{
	return mTestCaseGenerator.getConfiguration();
}

bool AbstractTestCaseGeneratorProvider::configure(const WObject * wfParameterObject)
{
	const WObject * thePROPERTY = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{

	}

	const WObject * theFORMAT = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("format", "FORMAT"));

	if( theFORMAT == WObject::_NULL_ ) {
		theFORMAT = Query::getRegexWSequence(wfParameterObject,
				OR_WID2("property", "PROPERTY"), wfParameterObject);
	}

	return( configureImpl(wfParameterObject) );
}

bool AbstractTestCaseGeneratorProvider::postprocess()
{
	return postprocessImpl();
}


} /* namespace sep */

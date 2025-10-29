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

#include  <famcore/api/AbstractProcessorUnit.h>

#include <sew/Configuration.h>
#include <sew/SymbexEngine.h>
#include <sew/WorkflowParameter.h>


namespace sep
{

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

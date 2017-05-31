/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 mars 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ProcessorUnitAutoRegistration.h"

#include <common/BF.h>

#include <fam/api/ProcessorUnitRepository.h>

#include <fml/workflow/WObject.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
IProcessorUnitRegistration::IProcessorUnitRegistration(
		const std::string & aMainTypeID   , const std::string & aTypeAliasID_1,
		const std::string & aTypeAliasID_2, const std::string & aTypeAliasID_3)
: mProcessorTypeID( aMainTypeID ),
  mProcessorTypeAliasID_1( aTypeAliasID_1 ),
  mProcessorTypeAliasID_2( aTypeAliasID_2 ),
  mProcessorTypeAliasID_3( aTypeAliasID_3 )
{
	ProcessorUnitRepository::registerProcessorFactory(aMainTypeID, this);

	if( not aTypeAliasID_1.empty() )
	{
		ProcessorUnitRepository::registerProcessorFactory(aTypeAliasID_1, this);
	}
	if( not aTypeAliasID_2.empty() )
	{
		ProcessorUnitRepository::registerProcessorFactory(aTypeAliasID_2, this);
	}
	if( not aTypeAliasID_3.empty() )
	{
		ProcessorUnitRepository::registerProcessorFactory(aTypeAliasID_3, this);
	}
}

// API for ProcessorUnitRepository::register(...)
bool IProcessorUnitRegistration::isTypeID(const WObject & wfObject) const
{
	return( isTypeID( wfObject.getQualifiedTypeNameID() ) );
}



} /* namespace sep */

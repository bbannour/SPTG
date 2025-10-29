/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "CompositeControllerUnit.h"


#include  <famcore/api/MainProcessorUnit.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>

#include <sew/SymbexControllerUnitManager.h>


namespace sep
{


/**
 * PROCESSOR FACTORY
 * for automatic registration in the processor repository
 * AbstractProcessorUnit::REGISTER_TOOL() is a pure virtual method
 */
IProcessorUnitRegistration & CompositeControllerUnit::REGISTER_TOOL() const
{
	return( MainProcessorUnit::AUTO_REGISTER_TOOL );
}


/**
 * CONSTRUCTOR
 * Default
 */
CompositeControllerUnit::CompositeControllerUnit(
		SymbexControllerUnitManager & aControllerUnitManager,
		const WObject * wfParameterObject)
: AbstractProcessorUnit(CLASS_KIND_T( CompositeControllerUnit ),
		aControllerUnitManager, wfParameterObject),
ListOfControllerUnits( ),
theOperator( OperatorManager::OPERATOR_SEQUENCE ),

////////////////////////////////////////////////////////////////////////////
// Computing Variables
processorIt( ),
processorItEnd( )
{
	mComputingStageEnabled |= AVM_COMPUTING_COMPOSITE_STAGE;
}



////////////////////////////////////////////////////////////////////////////
// CONFIGURE  API
////////////////////////////////////////////////////////////////////////////

bool CompositeControllerUnit::configureControllerUnits()
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->preConfigure() )
		{
			if( not (*processorIt)->configure() )
			{
				AVM_OS_WARN << "Failed to configuring Controller Unit << "
						<< (*processorIt)->getParameterWObject()
								->getFullyQualifiedNameID()
						<< " >> " << std::endl;

				return( false );
			}
		}
	}

	return true;
}


////////////////////////////////////////////////////////////////////////////
// REGISTER FOMAL ANALYSIS MODULE a.k.a. CONTROLLER UNIT  API
////////////////////////////////////////////////////////////////////////////

AbstractProcessorUnit * CompositeControllerUnit::getControllerUnit(
		const IProcessorUnitRegistration & aRegisterTool)
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isRegisterTool( aRegisterTool ) )
		{
			return( (*processorIt) );
		}
	}

	return( nullptr );
}


AbstractProcessorUnit * CompositeControllerUnit::getControllerUnit(
		const WObject * wfProcessorObject)
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->getParameterWObject() == wfProcessorObject )
		{
			return( (*processorIt) );
		}
	}

	return( nullptr );
}


AbstractProcessorUnit * CompositeControllerUnit::getControllerUnit(
		const std::string & aFullyQualifiedNameID)
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->getParameterWObject()
				->fqnEquals( aFullyQualifiedNameID ) )
		{
			return( (*processorIt) );
		}
	}

	return( nullptr );
}


bool CompositeControllerUnit::registerPreprocessor(AbstractProcessorUnit * aFAM)
{
	processorIt = begin();
	processorItEnd = end();
	iterator processorPosition = processorItEnd;
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt) == aFAM )
		{
			return false;
		}
		else if( processorPosition == processorItEnd )
		{
			if( (*processorIt)->getPrecedenceOfPreProcess() >
					aFAM->getPrecedenceOfPreProcess() )
			{
				processorPosition = processorIt;
			}
		}
	}

	ListOfControllerUnits::insert(processorPosition, aFAM);

	return true;
}


bool CompositeControllerUnit::registerPostprocessor(AbstractProcessorUnit * aFAM)
{
	processorIt = begin();
	processorItEnd = end();
	iterator processorPosition = processorItEnd;
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt) == aFAM )
		{
			return false;
		}
		else if( processorPosition == processorItEnd )
		{
			if( (*processorIt)->getPrecedenceOfPostProcess() >
					aFAM->getPrecedenceOfPostProcess() )
			{
				processorPosition = processorIt;
			}
		}
	}

	ListOfControllerUnits::insert(processorPosition, aFAM);

	return true;
}


bool CompositeControllerUnit::registerPrefilter(AbstractProcessorUnit * aFAM)
{
	processorIt = begin();
	processorItEnd = end();
	iterator processorPosition = processorItEnd;
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt) == aFAM )
		{
			return false;
		}
		else if( processorPosition == processorItEnd )
		{
			if( (*processorIt)->getPrecedenceOfPreFilter() >
					aFAM->getPrecedenceOfPreFilter() )
			{
				processorPosition = processorIt;
			}
		}
	}

	ListOfControllerUnits::insert(processorPosition, aFAM);

	return true;
}


bool CompositeControllerUnit::registerPostfilter(AbstractProcessorUnit * aFAM)
{
	processorIt = begin();
	processorItEnd = end();
	iterator processorPosition = processorItEnd;
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt) == aFAM )
		{
			return false;
		}
		else if( processorPosition == processorItEnd )
		{
			if( (*processorIt)->getPrecedenceOfPostFilter() >
					aFAM->getPrecedenceOfPostFilter() )
			{
				processorPosition = processorIt;
			}
		}
	}

	ListOfControllerUnits::insert(processorPosition, aFAM);

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// INIT / EXIT  API
////////////////////////////////////////////////////////////////////////////////

bool CompositeControllerUnit::initImpl()
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isEnablePlugin() )
		{
			if( not (*processorIt)->init() )
			{
				AVM_OS_CLOG  << "Failed to initing Controller Unit << "
						<< ( *processorIt)->getParameterWObject()
								->getFullyQualifiedNameID()
						<< " >> " << std::endl;

				return( false );
			}
		}
	}

	return true;
}

bool CompositeControllerUnit::exitImpl()
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isEnablePlugin() )
		{
			if( not (*processorIt)->exit() )
			{
				AVM_OS_CLOG  << "Failed to exiting Controller Unit << "
						<< ( *processorIt)->getParameterWObject()
								->getFullyQualifiedNameID()
						<< " >> " << std::endl;

				return( false );
			}
		}
	}

	return true;
}

////////////////////////////////////////////////////////////////////////////////
// ( PRE / POST ) PROCESS  API
////////////////////////////////////////////////////////////////////////////////

bool CompositeControllerUnit::preprocess()
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isEnablePreprocess()  )
		{
			if( not (*processorIt)->preprocess() )
			{
				AVM_OS_CLOG  << "Failed to preprocessing Controller Unit << "
						<< ( *processorIt)->getParameterWObject()
								->getFullyQualifiedNameID()
						<< " >> " << std::endl;

				return( false );
			}
		}
	}

	return( true );
}

bool CompositeControllerUnit::postprocess()
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isEnablePostprocess() )
		{
			if( not (*processorIt)->postprocess() )
			{
				AVM_OS_CLOG  << "Failed to postprocessing Controller Unit << "
						<< ( *processorIt)->getParameterWObject()
								->getFullyQualifiedNameID()
						<< " >> " << std::endl;

				return( false );
			}
		}
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// FILTERING  API
////////////////////////////////////////////////////////////////////////////////

bool CompositeControllerUnit::filteringInitialize()
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isWeakEnableFilter() )
		{
			if( not (*processorIt)->filteringInitialize() )
			{
				return( false );
			}
		}
	}

	return( true );
}

bool CompositeControllerUnit::filteringFinalize()
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isWeakEnableFilter() )
		{
			if( not (*processorIt)->filteringFinalize() )
			{
				return( false );
			}
		}
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// ( PRE / POST ) FILTER  API
////////////////////////////////////////////////////////////////////////////////

bool CompositeControllerUnit::prefilter()
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isEnablePrefilter() &&
			(*processorIt)->isLifecycleRunnable() )
		{
			if( not (*processorIt)->prefilter() )
			{
				return( false );
			}
		}
	}

	return( mControllerUnitManager.getExecutionQueue().hasReady() );
}


bool CompositeControllerUnit::postfilter()
{
	processorIt = begin();
	processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isEnablePostfilter() &&
			(*processorIt)->isLifecycleRunnable() )
		{
			if( not (*processorIt)->postfilter() )
			{
				return( false );
			}
		}
	}

	return( mControllerUnitManager.getExecutionQueue().hasResult()  );
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void CompositeControllerUnit::toStream(
		OutStream & os, const std::string & header) const
{
//	if( mParameterWObject != WObject::_NULL_ )
//	{
//		mParameterWObject->toStream(os);
//	}

	os << TAB << header << "{ "
			<< ( (theOperator != nullptr) ? theOperator->str() : "" )
			<< EOL;

	const_iterator processorIt = begin();
	const_iterator processorItEnd = end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		os << TAB2 << (*processorIt)->strUniqId() << EOL;
	}
	os << TAB << "}" << EOL_FLUSH;
}



} /* namespace sep */

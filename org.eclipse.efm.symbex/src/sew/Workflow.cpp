/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Workflow.h"
#include "WorkflowParameter.h"

#include <collection/List.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <printer/OutStream.h>

#include <sew/SymbexEngine.h>


namespace sep
{


/**
 * LOADER
 */
bool Workflow::load()
{
	return( true );
}


/**
 * DISPOSER
 */
void Workflow::dispose()
{
	mCurrentSymbexEngine = mMainSymbexEngine;
	for( ; mCurrentSymbexEngine != nullptr ;
			mCurrentSymbexEngine = mMainSymbexEngine )
	{
		mMainSymbexEngine = mMainSymbexEngine->getNextCore();

		sep::destroy( mCurrentSymbexEngine );

		mCurrentSymbexEngine = nullptr;
	}
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

/*
 * Case WObjectManager::is( mocRuntime ) )
 * with  mocRuntime ::= moc = engine::main
 *
 * Old legacy FAVM format for single Engine core
 *
	section MOC
		prototype engine::main "the main Model Of Computation" as avm::core.Engine is
		....
		endprototype

		moc = engine::main;
	endsection MOC

 *
 * case mocRuntime.is< AvmCode >()
 * with  mocRuntime ::= moc = ${ |;| ... }
 *
 * Old legacy FAVM format for multiple Engine core
 *
	section MOC
		prototype engine::main "the main Model Of Computation" as avm::core.Engine is
			....
		endprototype

		prototype engine::io_continuation "io_continuation" as &avm::core.Engine is
			....
		endprototype

		moc = ${ |;|
			&engine::main
			&engine::io_continuation
		};
	endsection MOC

 *
 * Case ELSE
 *
 * New SEW format for Sequential Engine core
 *
	director trace#coverage  'as main execution objective'  {
		...
	}

	director io#continuation 'as IO continuation objective' {
		...
	}

 */


bool Workflow::configure(const WorkflowParameter & aWorkflowParameter)
{
	mMainSymbexEngine = nullptr;

	const WObject * sequenceDIRECTOR = aWorkflowParameter.getDIRECTOR();

	const BF & mocRuntime = Query::getRegexWPropertyValue(
			sequenceDIRECTOR, OR_WID2("moe", "moc"));

	if( WObjectManager::is( mocRuntime ) )
	{
		mMainSymbexEngine =
				new SymbexEngine(WObjectManager::from( mocRuntime ));

		if(not  mMainSymbexEngine->configure() )
		{
			delete( mMainSymbexEngine );

			mMainSymbexEngine = nullptr;

			return( false );
		}
	}
	else if( mocRuntime.is< AvmCode >() )
	{
		SymbexEngine * nextEngine = nullptr;
		SymbexEngine * prevEngine = nullptr;

		for( const auto & itEngine : mocRuntime.to< AvmCode >().getOperands() )
		{
			if( WObjectManager::is( itEngine ) )
			{
				nextEngine = new SymbexEngine(WObjectManager::from( itEngine ));

				nextEngine->setPreviousCore( prevEngine );

				if( nextEngine->configure() )
				{
					if( mMainSymbexEngine == nullptr )
					{
						mMainSymbexEngine = nextEngine;
					}

					if( prevEngine != nullptr )
					{
						prevEngine->setNextCore( nextEngine );
					}
					prevEngine = nextEngine;
				}
				else
				{
					delete( nextEngine );

					return( false );
				}
			}
			else
			{
				return( false );
			}
		}
	}
	else
	{
		SymbexEngine * nextEngine = nullptr;
		SymbexEngine * prevEngine = nullptr;

		List< WObject * > engineList;
		Query::getListWObject(sequenceDIRECTOR, engineList);

		for( const auto & woEngine : engineList )
		{
			nextEngine = new SymbexEngine(woEngine);

			nextEngine->setPreviousCore( prevEngine );

			if( nextEngine->configure() )
			{
				if( mMainSymbexEngine == nullptr )
				{
					mMainSymbexEngine = nextEngine;
				}

				if( prevEngine != nullptr )
				{
					prevEngine->setNextCore( nextEngine );
				}
				prevEngine = nextEngine;
			}
			else
			{
				delete( nextEngine );

				return( false );
			}
		}
	}

	return( true );
}


/**
 * START
 */
bool Workflow::start()
{
	////////////////////////////////////////////////////////////////////////////
	///// START SEQUENTIALLY ENGINE CORE
	////////////////////////////////////////////////////////////////////////////

	for( mCurrentSymbexEngine = mMainSymbexEngine ;
			mCurrentSymbexEngine != nullptr ;
			mCurrentSymbexEngine = mCurrentSymbexEngine->getNextCore() )
	{
		if( not mCurrentSymbexEngine->startComputing() )
		{
			return( false );
		}
	}

	return( true );
}


/**
 * EXIT
 */
bool Workflow::exitImpl()
{
//	bool isCasManager_OK =  mAvmConfiguration.getCasManager().exit();
//
//	return( RunnableElement::exit() && isCasManager_OK );

	return( true );
}


/**
 * REPORT TRACE
 */
void Workflow::report(OutStream & os) const
{
//	mAvmConfiguration.getCasManager().report(os);
//
//	mAvmConfiguration.getCasManager().report(AVM_OS_COUT);
}


/**
 * COMPUTING
 *
 */
bool Workflow::startComputing()
{
	AVM_OS_LOG << std::endl << _SEW_ << "< start > Computing ..." << std::endl;

	////////////////////////////////////////////////////////////////////////////
	///// INITIALIZATION
	////////////////////////////////////////////////////////////////////////////

	if( not init() )
	{
		avm_set_exit_code( AVM_EXIT_INITIALIZING_ERROR_CODE );

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	///// PRE PROCESSING
	////////////////////////////////////////////////////////////////////////////

	if( not preprocess() )
	{
		avm_set_exit_code( AVM_EXIT_PRE_PROCESSING_ERROR_CODE );

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	///// START
	////////////////////////////////////////////////////////////////////////////

	if( not start() )
	{
		avm_set_exit_code( AVM_EXIT_PROCESSING_ERROR_CODE );

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	///// POST PROCESSING
	////////////////////////////////////////////////////////////////////////////

	if( not postprocess() )
	{
		avm_set_exit_code( AVM_EXIT_POST_PROCESSING_ERROR_CODE );

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	///// EXITING
	////////////////////////////////////////////////////////////////////////////

	if( not exit() )
	{
		avm_set_exit_code( AVM_EXIT_FINALIZING_ERROR_CODE );

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	///// REPORTING
	////////////////////////////////////////////////////////////////////////////

	AVM_OS_LOG << std::endl;

	report(AVM_OS_LOG);

	AVM_OS_LOG << std::endl;


	////////////////////////////////////////////////////////////////////////////
	///// SERIALIZATION
	////////////////////////////////////////////////////////////////////////////

	//serializeResult();

	AVM_OS_LOG << _SEW_ << "< end >Computing ... done." << std::endl;

	return( true );
}


/**
 * SERIALIZATION
 */
void Workflow::toStream(OutStream & os) const
{
	os << TAB << "workflow {" << EOL;

	if( mParameterWObject != WObject::_NULL_ )
	{
		mParameterWObject->toStream(os);
	}

	os << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}

} /* namespace sep */

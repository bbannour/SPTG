/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 28 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SEW_SYMBEX_CONTROLLER_UNIT_MANAGER_H_
#define SEW_SYMBEX_CONTROLLER_UNIT_MANAGER_H_

#include  <famcore/api/AbstractProcessorUnit.h>

#include <collection/Typedef.h>

#include  <famcore/api/CompositeControllerUnit.h>
#include  <famcore/api/MainProcessorUnit.h>
#include  <famcore/api/ProcessorUnitAutoRegistration.h>

#include  <famcore/queue/ExecutionQueue.h>

#include  <famcore/redundancy/RedundancyFilter.h>


namespace sep
{


class AvmPrimitiveProcessor;
class Builder;
class Configuration;
class SymbexEngine;
class WObject;


class SymbexControllerUnitManager  :  public RunnableElement
{

	AVM_DECLARE_CLONABLE_CLASS( SymbexControllerUnitManager )

protected:
	/**
	 * TYPEDEF
	 */
	typedef List< AbstractProcessorUnit * > ListOfControllerUnits;

public:
	typedef ListOfControllerUnits::iterator        rw_controller_iterator;
	typedef ListOfControllerUnits::const_iterator  controller_iterator;


protected:
	/**
	 * ATTRIBUTE
	 */
	SymbexEngine & mSymbexEngine;

	bool mAutoConfigure;
	bool mAutoStart;

	ExecutionQueue mQueueProcessor;

	MainProcessorUnit mMainProcessor;

	RedundancyFilter mRedundancyProcessor;

	CompositeControllerUnit mControllerUnits;

	CompositeControllerUnit mPreprocessorControllerUnits;
	CompositeControllerUnit mPostprocessorControllerUnits;

	CompositeControllerUnit mPrefilterControllerUnits;
	CompositeControllerUnit mPostfilterControllerUnits;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	rw_controller_iterator processorIt;
	rw_controller_iterator processorItEnd;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexControllerUnitManager(
			SymbexEngine & anEngine, const WObject * wfParameterObject)
	: RunnableElement(
			CLASS_KIND_T( SymbexControllerUnitManager ), wfParameterObject),

	mSymbexEngine( anEngine ),

	mAutoConfigure( false ),
	mAutoStart( false ),

	mQueueProcessor( *this ),
	mMainProcessor( *this ),
	mRedundancyProcessor( *this ),

	mControllerUnits( *this ),

	mPreprocessorControllerUnits( *this ),
	mPostprocessorControllerUnits( *this ),

	mPrefilterControllerUnits( *this ),
	mPostfilterControllerUnits( *this ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	processorIt( ),
	processorItEnd( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbexControllerUnitManager()
	{
		AbstractProcessorUnit * itProcessor = nullptr;

		while( mControllerUnits.nonempty() )
		{
			itProcessor = mControllerUnits.pop_last();

			// Don't delete << mMainProcessor | mQueueProcessor >>
			if( (itProcessor != (& mMainProcessor ))
				&& (itProcessor != (& mQueueProcessor))
				&& (itProcessor != (& mRedundancyProcessor)) )
			{
				delete( itProcessor );
			}
		}
	}


	inline virtual void append(AbstractProcessorUnit * aProcessor)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aProcessor )
				<< "Processor Unit !!!"
				<< SEND_EXIT;

//!![MIGRATION]
//		AVM_OS_ASSERT_WARNING_ALERT( aProcessor != (& mMainProcessor) )
//				<< "Unexpected MainProcessor !!!"
//				<< SEND_ALERT;
//		AVM_OS_ASSERT_WARNING_ALERT( aProcessor != (& mQueueProcessor) )
//				<< "Unexpected QueueProcessor !!!"
//				<< SEND_ALERT;
//		AVM_OS_ASSERT_WARNING_ALERT( aProcessor != (& mRedundancyProcessor) )
//				<< "Unexpected QueueProcessor !!!"
//				<< SEND_ALERT;

		// Don't append << mMainProcessor | mQueueProcessor >>
		if( (aProcessor != (& mMainProcessor))
			&& (aProcessor != (& mQueueProcessor))
			&& (aProcessor != (& mRedundancyProcessor)) )
		{
			mControllerUnits.append( aProcessor );
		}
	}

	/**
	 * GETTER
	 * mSymbexEngine
	 * Configuration
	 */
	inline SymbexEngine & getSymbexEngine()
	{
		return( mSymbexEngine );
	}

	inline const SymbexEngine & getSymbexEngine() const
	{
		return( mSymbexEngine );
	}

	/**
	 * GETTER
	 * Configuration
	 */
	Configuration & getConfiguration() const;

	/**
	 * GETTER
	 * Builder
	 */
	Builder & getBuilder();

	/**
	 * GETTER
	 * AvmPrimitiveProcessor
	 */
	AvmPrimitiveProcessor & getPrimitiveProcessor();


	/**
	 * GETTER
	 * mAutoConfigure
	 * mAutoStart
	 */
	inline bool isAutoConfigure() const
	{
		return( mAutoConfigure );
	}

	inline bool isAutoStart() const
	{
		return( mAutoStart );
	}


	/**
	 * GETTER
	 * mExecutionQueue
	 */
	inline ExecutionQueue & getExecutionQueue()
	{
		return( mQueueProcessor );
	}


	/**
	 * GETTER
	 * mMainProcessor
	 */
	inline MainProcessorUnit & getMainProcessor()
	{
		return( mMainProcessor );
	}

	inline const MainProcessorUnit & getMainProcessor() const
	{
		return( mMainProcessor );
	}

	/**
	 * GETTER
	 * mRedundancyProcessor
	 */
	inline RedundancyFilter & getRedundancyProcessor()
	{
		return( mRedundancyProcessor );
	}


	/**
	 * GETTER
	 * mControllerUnits
	 */
	inline const CompositeControllerUnit & getControllerUnits() const
	{
		return( mControllerUnits );
	}

	/**
	 * GETTER
	 * mControllerUnits
	 * by parameter WObject / FullyQualifiedNameID
	 */
	inline AbstractProcessorUnit * getControllerUnit(
			const IProcessorUnitRegistration & aRegisterTool)
	{
		if( mMainProcessor.isRegisterTool( aRegisterTool ) )
		{
			return( & mMainProcessor );
		}
		else if( mQueueProcessor.isRegisterTool( aRegisterTool ) )
		{
			return( & mQueueProcessor );
		}
		else if( mRedundancyProcessor.isRegisterTool( aRegisterTool ) )
		{
			return( & mRedundancyProcessor );
		}
		else
		{
			return( mControllerUnits.getControllerUnit( aRegisterTool ) );
		}
	}

	inline AbstractProcessorUnit * getControllerUnit(
			const WObject * wfProcessorObject)
	{
		if( mMainProcessor.getParameterWObject() == wfProcessorObject )
		{
			return( & mMainProcessor );
		}
		else if( mQueueProcessor.getParameterWObject() == wfProcessorObject )
		{
			return( & mQueueProcessor );
		}
		else if( mRedundancyProcessor.getParameterWObject() == wfProcessorObject )
		{
			return( & mRedundancyProcessor );
		}
		else
		{
			return( mControllerUnits.getControllerUnit( wfProcessorObject ) );
		}
	}

	inline AbstractProcessorUnit * getControllerUnit(
			const std::string & aFullyQualifiedNameID)
	{
		if( mMainProcessor.getParameterWObject()
				->fqnEquals( aFullyQualifiedNameID ) )
		{
			return( & mMainProcessor );
		}
		else if( mQueueProcessor.getParameterWObject()
				->fqnEquals( aFullyQualifiedNameID ) )
		{
			return( & mQueueProcessor );
		}
		else if( mRedundancyProcessor.getParameterWObject()
				->fqnEquals( aFullyQualifiedNameID ) )
		{
			return( & mRedundancyProcessor );
		}
		else
		{
			return( mControllerUnits.getControllerUnit( aFullyQualifiedNameID ) );
		}
	}


	/**
	 * GETTER
	 * mPreprocessor
	 * mPreprocessorControllerUnits
	 */
	inline CompositeControllerUnit & getPreprocessor()
	{
		return( mPreprocessorControllerUnits );
	}

	inline void addPreprocessor(AbstractProcessorUnit * aFAM)
	{
		mPreprocessorControllerUnits.addControllerUnit( aFAM );
	}

	inline void appendPreprocessor(AbstractProcessorUnit * aFAM)
	{
		mPreprocessorControllerUnits.appendControllerUnit( aFAM );
	}

	inline bool registerPreprocessor(AbstractProcessorUnit * aFAM)
	{
		return( mPreprocessorControllerUnits.registerPreprocessor( aFAM ) );
	}


	/**
	 * GETTER
	 * mPostprocessor
	 * mPostprocessorControllerUnits
	 */
	inline CompositeControllerUnit & getPostprocessor()
	{
		return( mPostprocessorControllerUnits );
	}

	inline void addPostprocessor(AbstractProcessorUnit * aFAM)
	{
		mPostprocessorControllerUnits.addControllerUnit( aFAM );
	}

	inline void appendPostprocessor(AbstractProcessorUnit * aFAM)
	{
		mPostprocessorControllerUnits.appendControllerUnit( aFAM );
	}

	inline bool registerPostprocessor(AbstractProcessorUnit * aFAM)
	{
		return( mPostprocessorControllerUnits.registerPostprocessor( aFAM ) );
	}


	/**
	 * GETTER
	 * mPrefilter
	 * mPrefilterControllerUnits
	 */
	inline CompositeControllerUnit & getPrefilter()
	{
		return( mPrefilterControllerUnits );
	}

	inline void addPrefilter(AbstractProcessorUnit * aFAM)
	{
		mPrefilterControllerUnits.addControllerUnit( aFAM );
	}

	inline void appendPrefilter(AbstractProcessorUnit * aFAM)
	{
		mPrefilterControllerUnits.appendControllerUnit( aFAM );
	}

	inline bool registerPrefilter(AbstractProcessorUnit * aFAM)
	{
		return( mPrefilterControllerUnits.registerPrefilter( aFAM ) );
	}


	/**
	 * GETTER
	 * mPostfilter
	 * mPostfilterControllerUnits
	 */
	inline CompositeControllerUnit & getPostfilter()
	{
		return( mPostfilterControllerUnits );
	}

	inline void addPostfilter(AbstractProcessorUnit * aFAM)
	{
		mPostfilterControllerUnits.addControllerUnit( aFAM );
	}

	inline void appendPostfilter(AbstractProcessorUnit * aFAM)
	{
		mPostfilterControllerUnits.appendControllerUnit( aFAM );
	}

	inline bool registerPostfilter(AbstractProcessorUnit * aFAM)
	{
		return( mPostfilterControllerUnits.registerPostfilter( aFAM ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool preConfigure();

	virtual bool configure() override;

	virtual bool configureImpl()
	{
		return( true );
	}

	inline bool configureControllerUnits()
	{
		return( mControllerUnits.configureControllerUnits() );
	}

	////////////////////////////////////////////////////////////////////////////
	// INIT / EXIT  API
	////////////////////////////////////////////////////////////////////////////
	virtual bool initImpl() override;

	virtual bool exitImpl() override;

	////////////////////////////////////////////////////////////////////////////
	// ( PRE / POST ) PROCESS  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool preprocess() override;

	virtual bool postprocess() override;


	////////////////////////////////////////////////////////////////////////////
	// FILTERING  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool filteringInitialize();

	virtual bool filteringFinalize();

	////////////////////////////////////////////////////////////////////////////
	// ( PRE / POST ) FILTER  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool prefilter();

	bool finalizePrefiltering();


	virtual bool postfilter();

	bool finalizePostfiltering();


	/**
	 * Has Work
	 */
	inline bool hasWork() const
	{
		return( mQueueProcessor.hasWork() );
	}

	inline bool hasReadyWork() const
	{
		return( mQueueProcessor.hasReadyWork() );
	}


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API
	////////////////////////////////////////////////////////////////////////////
	/**
	 * REQUEST_STOP_STATUS
	 */
	inline virtual void handleRequestStop()
	{
		mQueueProcessor.handleRequestStop();
	}

	/**
	 * REQUEST_RELEASE_STATUS
	 */
	inline virtual void handleRequestRelease()
	{
		mQueueProcessor.handleRequestRelease();
	}

	inline void handleRequestRelease(AbstractProcessorUnit * aRequestor)
	{
		mPrefilterControllerUnits.handleRequestRelease(aRequestor);

		mPostfilterControllerUnits.handleRequestRelease(aRequestor);

		aRequestor->handleRequestRelease();
	}

	/**
	 * REQUEST_RESET_STATUS
	 */
	inline virtual void handleRequestReset()
	{
		mQueueProcessor.handleRequestReset();
	}

	/**
	 * REQUEST_RESTART_STATUS
	 */
	inline virtual void handleRequestRestart()
	{
		mQueueProcessor.handleRequestRestart();
	}

	/**
	 * REQUEST_CONTINUE_STATUS
	 */
	inline virtual void handleRequestContinue()
	{
		mQueueProcessor.handleRequestContinue();
	}

	/**
	 * REQUEST_REQUEUE_WAITING_STATUS
	 */
	inline virtual void handleRequestRequeueWaiting(
			AbstractProcessorUnit * aRequestor)
	{
		mQueueProcessor.handleRequestRequeueWaiting( aRequestor );
	}

	/**
	 * REQUEST_REQUEUE_RESERVE_STATUS
	 */
	inline virtual void handleRequestRequeueReserve(
			AbstractProcessorUnit * aRequestor)
	{
		mQueueProcessor.handleRequestRequeueReserve( aRequestor );
	}


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	virtual void report(OutStream & os) const override;

	// Due to [-Woverloaded-virtual=]
	using RunnableElement::report;


	/**
	 * EVAL TRACE
	 */
	virtual void traceBoundEval(OutStream & os) const;


	virtual void traceInitSpider(OutStream & os) const;

	virtual void traceStepSpider(OutStream & os,
			const ExecutionContext & anEC) const;

	virtual void traceStopSpider(OutStream & os) const;


	virtual void tracePreEval(OutStream & os,
			const ExecutionContext & anEC) const;

	virtual void tracePostEval(OutStream & os,
			const ExecutionContext & anEC) const;

	virtual void reportEval(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// UNIT TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddUnitReport(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddRegressionReport(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	virtual void toStream(OutStream & os) const override;

};


} /* namespace sep */

#endif /* SEW_SYMBEX_CONTROLLER_UNIT_MANAGER_H_ */

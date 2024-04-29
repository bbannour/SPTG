/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 9 mars 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SEW_SYMBEX_ENGINE_H_
#define SEW_SYMBEX_ENGINE_H_

#include <common/RunnableElement.h>

#include <builder/Builder.h>
#include <builder/Loader.h>

#include <computer/primitive/AvmPrimitiveProcessor.h>

#include <sew/SymbexDispatcher.h>


#include <sew/Configuration.h>
#include <sew/SymbexControllerUnitManager.h>

#include <util/ExecutionChrono.h>
#include <util/ExecutionTime.h>


namespace sep
{

class WObject;

class WorkflowParameter;


class SymbexEngine  :  public RunnableElement
{

	AVM_DECLARE_UNCLONABLE_CLASS(SymbexEngine)


protected :
	/**
	 * ATTRIBUTES
	 */
	Configuration mConfiguration;

	AvmPrimitiveProcessor mPrimitiveProcessor;

	Builder mBuilder;
	Loader  mLoader;

	SymbexControllerUnitManager mControllerUnitManager;

	SymbexDispatcher mSymbexDispatcher;

	ExecutionChrono mExecutionChronoManager;
	ExecutionTime mExecutionTimeManager;

	SymbexEngine * mPreviousEngine;
	SymbexEngine * mNextEngine;

public:
	std::size_t mErrorCount;
	std::size_t mWarningCount;



public :
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexEngine(const WObject * wfParameterObject);

	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbexEngine()
	{
		//!! NOTHING
	}


	/**
	 * CONFIGURE
	 */
	bool configure() override;

	/**
	 * Setting CURRENT ACTIVE CONFIGURATION
	 */
	void setCurrentActiveConfiguration() const
	{
		mConfiguration.setActive();
	}


	/**
	 * REPORT TRACE
	 */
	void preReport (OutStream & os) const;
	void dynReport (OutStream & os) const;
	void postReport(OutStream & os) const;

	void report(OutStream & os) const override;

	// Due to [-Woverloaded-virtual=]
	using RunnableElement::report;

	void failedReport();


	/**
	 * INIT * PRE-PROCESS
	 */
	virtual bool initImpl() override;

	virtual bool preprocess() override;

	/**
	 * START
	 */
	bool start();

	void reportTimeElapsing(OutStream & out);

	/**
	 * POST-PROCESS
	 * INIT
	 */
	virtual bool postprocess() override;

	virtual bool exitImpl() override;


	/*
	 * PROCESSING
	 */
	bool startParsing();
	bool startParsing(const std::string & rawText);

	bool startBuilding();
	bool startComputing();

	/*
	 * for RPC PURPUSE
	 */
	bool initComputing();

	bool runPostProcessor();


	inline void serializeBuildingResult() const
	{
		mConfiguration.serializeBuildingResult();
	}

	inline void serializeLoadingResult()
	{
		mConfiguration.serializeLoadingResult();
	}

	inline void serializeComputingResult() const
	{
		mConfiguration.serializeComputingResult();
	}



	/**
	 * GETTER
	 * mPrimitiveProcessor
	 */
	inline AvmPrimitiveProcessor & getPrimitiveProcessor()
	{
		return( mPrimitiveProcessor );
	}

	/**
	 * GETTER
	 * mBuilder
	 */
	inline Builder & getBuilder()
	{
		return( mBuilder );
	}

	/**
	 * GETTER
	 * mLoader
	 */
	inline Loader & getLoader()
	{
		return( mLoader );
	}

	/**
	 * GETTER
	 * mControllerUnitManager
	 */
	inline SymbexControllerUnitManager & getControllerUnitManager()
	{
		return( mControllerUnitManager );
	}


	/**
	 * GETTER
	 * mSymbexDispatcher
	 */
	inline SymbexDispatcher & getSymbexDispatcher()
	{
		return( mSymbexDispatcher );
	}

	inline const SymbexDispatcher & getSymbexDispatcher() const
	{
		return( mSymbexDispatcher );
	}


	/**
	 * GETTER - SETTER
	 * mPreviousEngine
	 * mNextEngine
	 * SymbexEngine
	 */
	inline SymbexEngine * getPreviousCore()
	{
		return( mPreviousEngine );
	}

	inline void setPreviousCore(SymbexEngine * aPreviousCore)
	{
		mPreviousEngine = aPreviousCore;
	}


	inline SymbexEngine * getNextCore()
	{
		return( mNextEngine );
	}

	inline void setNextCore(SymbexEngine * aNextCore)
	{
		mNextEngine = aNextCore;
	}


	/**
	 * GETTER
	 * mConfiguration
	 */
	inline Configuration & getConfiguration()
	{
		return( mConfiguration );
	}



	////////////////////////////////////////////////////////////////////////////
	// TEST DRIVEN DEVELOPMENT
	////////////////////////////////////////////////////////////////////////////

	void tddStart();

	////////////////////////////////////////////////////////////////////////////
	// UNIT TEST API
	////////////////////////////////////////////////////////////////////////////

	void tddUnitReport(OutStream & os) const;

	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	void tddRegressionReport(OutStream & os) const;

};


} /* namespace sep */

#endif /* SEW_SYMBEX_ENGINE_H_ */

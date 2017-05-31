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
#ifndef REDUNDANCYFILTER_H_
#define REDUNDANCYFILTER_H_

#include <fam/api/AbstractProcessorUnit.h>
#include <sew/SymbexEventManager.h>

#include <common/BF.h>

#include <fml/builtin/Identifier.h>


namespace sep
{

class BaseConfigurationComparator;
class BaseDataComparator;
class BasePathScopeIterator;

class SymbexControllerUnitManager;


class RedundancyFilter :
		public AutoRegisteredProcessorUnit< RedundancyFilter >,
		public IHandlerEventDestroyCtx
{

	AVM_DECLARE_CLONABLE_CLASS( RedundancyFilter )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3(
			"symbex.redundancy",
			"avm::processor.REDUNDANCY",
			"avm::core.filter.REDUNDANCY")
	// end registration


protected:
	/**
	 * ATTRIBUTES
	 */
	bool mTrivialLoopDetectionFlag;


	bool mRedundancyConfigurationFlag;
	bool mRedundancyEnabledFlag;

	BaseConfigurationComparator * mConfigurationComparator;

	BasePathScopeIterator       * mPathScopeIterator;

	BaseDataComparator          * mExecutionDataComparator;

	avm_size_t mTrivialLoopTest;
	avm_size_t mTrivialLoopCount;

	avm_size_t mRedundancyTest;
	avm_size_t mRedundancyCount;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variable
	const ExecutionContext * mCandidateEC;


public:

	/**
	 * CONSTRUCTOR
	 */
	RedundancyFilter(SymbexControllerUnitManager & aControllerUnitManager,
			WObject * wfParameterObject = NULL)
	: RegisteredProcessorUnit(aControllerUnitManager, wfParameterObject,
			AVM_PRE_FILTERING_STAGE, PRECEDENCE_OF_REDUNDANCY),
	mTrivialLoopDetectionFlag( false ),
	mRedundancyConfigurationFlag( false ),
	mRedundancyEnabledFlag( false ),

	mConfigurationComparator( NULL ),
	mPathScopeIterator( NULL ),
	mExecutionDataComparator( NULL ),

	mTrivialLoopTest( 0 ),
	mTrivialLoopCount( 0 ),

	mRedundancyTest( 0 ),
	mRedundancyCount( 0 ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variable
	mCandidateEC( NULL )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~RedundancyFilter();

	void destroy();

	/**
	 * mRedundancyEnabledFlag
	 * mTrivialLoopDetectionFlag
	 */
	inline void setEnabledRedundancyDetection(bool bEnabled = true )
	{
		// Enabling only if it was configured,
		// i.e. mRedundancyConfigurationFlag is true !
		mRedundancyEnabledFlag = (bEnabled && mRedundancyConfigurationFlag);
	}

	inline void setEnabledTrivialLoopDetection(bool bEnabled = true )
	{
		mTrivialLoopDetectionFlag = bEnabled;
	}


	/**
	 * CONFIGURE
	 */
	bool configureImpl();


	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddRegressionReportImpl(OutStream & os);

	/**
	 * preFilter
	 * Every pre filter has to implement this method
	 */
	virtual bool prefilter();

	virtual bool prefilter(ExecutionContext & anEC);

	bool trivialLoopDetection(ExecutionContext & anEC);


	/* GETTER - SETTER
	 * mConfigurationComparator
	 */
	inline BaseConfigurationComparator * getConfigurationComparator()
	{
		return( mConfigurationComparator );
	}

	inline bool hasConfigurationComparator() const
	{
		return( mConfigurationComparator != NULL );
	}

	inline void setConfigurationComparator(
			BaseConfigurationComparator * aConfigurationComparator)
	{
		mConfigurationComparator = aConfigurationComparator;
	}


	/* GETTER - SETTER
	 * mPathScopeIterator
	 */
	inline BasePathScopeIterator * getPathScopeIterator()
	{
		return( mPathScopeIterator );
	}

	inline bool hasPathScopeIterator() const
	{
		return( mPathScopeIterator != NULL );
	}

	inline void setPathScopeIterator(BasePathScopeIterator * aPathScopeIterator)
	{
		mPathScopeIterator = aPathScopeIterator;
	}


	/* GETTER - SETTER
	 * mExecutionDataComparator
	 */
	inline BaseDataComparator * getExecutionDataComparator()
	{
		return( mExecutionDataComparator );
	}

	inline bool hasExecutionDataComparator() const
	{
		return( mExecutionDataComparator != NULL );
	}

	inline void setExecutionDataComparator(
			BaseDataComparator * anExecutionDataComparator)
	{
		mExecutionDataComparator = anExecutionDataComparator;
	}


	/**
	 * IHandlerEventDestroyCtx API
	 * Destroy Execution Context
	 */
	virtual void handleEventDestroyCtx(ExecutionContext * anEC);

};


}

#endif /*REDUNDANCYFILTER_H_*/

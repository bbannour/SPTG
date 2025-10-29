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

#include  <famcore/api/AbstractProcessorUnit.h>
#include <common/BF.h>

#include <fml/builtin/Identifier.h>
#include <sew/SymbexControllerEventManager.h>


namespace sep
{

class BaseConfigurationComparator;
class BaseDataComparator;
class BasePathScopeIterator;

class SymbexControllerUnitManager;


class RedundancyFilter final :
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

	std::size_t mTrivialLoopTest;
	std::size_t mTrivialLoopCount;

	std::size_t mRedundancyTest;
	std::size_t mRedundancyCount;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variable
	const ExecutionContext * mCandidateEC;


public:

	/**
	 * CONSTRUCTOR
	 */
	RedundancyFilter(SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject = nullptr)
	: RegisteredProcessorUnit(aControllerUnitManager, wfParameterObject,
			AVM_PRE_FILTERING_STAGE, PRECEDENCE_OF_REDUNDANCY),
	mTrivialLoopDetectionFlag( false ),
	mRedundancyConfigurationFlag( false ),
	mRedundancyEnabledFlag( false ),

	mConfigurationComparator( nullptr ),
	mPathScopeIterator( nullptr ),
	mExecutionDataComparator( nullptr ),

	mTrivialLoopTest( 0 ),
	mTrivialLoopCount( 0 ),

	mRedundancyTest( 0 ),
	mRedundancyCount( 0 ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variable
	mCandidateEC( nullptr )
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
	virtual bool configureImpl() override;


	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(OutStream & os) const override;


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddRegressionReportImpl(OutStream & os) const override;

	/**
	 * preFilter
	 * Every pre filter has to implement this method
	 */
	virtual bool prefilter() override;

	virtual bool prefilter(ExecutionContext & anEC) override;

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
		return( mConfigurationComparator != nullptr );
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
		return( mPathScopeIterator != nullptr );
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
		return( mExecutionDataComparator != nullptr );
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
	virtual void handleEventDestroyCtx(ExecutionContext * anEC) override;

};


}

#endif /*REDUNDANCYFILTER_H_*/

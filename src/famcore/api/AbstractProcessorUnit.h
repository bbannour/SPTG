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

#ifndef ABSTRACTPROCESSORUNIT_H_
#define ABSTRACTPROCESSORUNIT_H_

#include <common/RunnableElement.h>
#include  <famcore/api/IProcessorUnitTest.h>
#include  <famcore/api/ProcessorUnitAutoRegistration.h>

#include <computer/EvaluationEnvironment.h>

#include <fml/runtime/ExecutionContext.h>

#include <fml/workflow/WObject.h>


namespace sep
{


typedef std::uint8_t  avm_computing_process_stage_t;

enum {
	AVM_UNDEFINED_STAGE            = 0x0000,

	AVM_PRE_PROCESSING_STAGE       = 0x0001,
	AVM_POST_PROCESSING_STAGE      = 0x0002,

	AVM_PREPOST_PROCESSING_STAGE   = AVM_PRE_PROCESSING_STAGE
	                               | AVM_POST_PROCESSING_STAGE,

	AVM_PRE_FILTERING_STAGE        = 0x0004,
	AVM_POST_FILTERING_STAGE       = 0x0008,

	AVM_PREPOST_FILTERING_STAGE    = AVM_PRE_FILTERING_STAGE
	                               | AVM_POST_FILTERING_STAGE,

	AVM_COMPUTING_ALL_STAGE        = AVM_PREPOST_PROCESSING_STAGE
	                               | AVM_PREPOST_FILTERING_STAGE,

	AVM_COMPUTING_COMPOSITE_STAGE  = 0x0010,

};



class WaitingStrategy;
class AvmPrimitiveProcessor;

class Builder;

class Configuration;

class ExecutableForm;
class ExecutionContext;
class ExecutionQueue;

class MainProcessorUnit;

class SymbexDispatcher;
class SymbexControllerRequestManager;
class SymbexControllerUnitManager;
class SymbexEngine;
class SymbexControllerEventManager;


////////////////////////////////////////////////////////////////////////////////
// FORMAL ANALYSIS MODULE POINTER
////////////////////////////////////////////////////////////////////////////////

class AbstractProcessorUnit :
		public RunnableElement ,
		public IProcessorUnitTest ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( AbstractProcessorUnit )
{

public:
	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 */
	virtual const IProcessorUnitRegistration & REGISTER_TOOL() const = 0;

	inline bool isRegisterTool(
			const IProcessorUnitRegistration & aRegisterTool) const
	{
		return( REGISTER_TOOL().isEquals( aRegisterTool ) );
	}


protected:
	/**
	 * ATTRIBUTES
	 */
	SymbexControllerUnitManager & mControllerUnitManager;

	EvaluationEnvironment ENV;

	avm_computing_process_stage_t mComputingStageRequired;
	avm_computing_process_stage_t mComputingStageEnabled;

	bool mAutoConfigure;
	bool mAutoStart;

	std::uint8_t mPrecedenceOfPreProcess;
	std::uint8_t mPrecedenceOfPostProcess;

	std::uint8_t mPrecedenceOfInitFilter;

	std::uint8_t mPrecedenceOfPreFilter;
	std::uint8_t mPrecedenceOfPostFilter;

	std::size_t mBeginningStepTimout;

	bool mStopFlag;
	bool mBreakFlag;

	bool mSliceFlag;
	std::size_t mSliceCount;


	// For symbex trace spider position format
	std::string mSpiderInitTraceFormatter;
	std::string mSpiderStepTraceFormatter;
	std::string mSpiderStopTraceFormatter;

	// For eval / report Trace format
	std::string mPreEvalTraceFormatter;
	std::string mPostEvalTraceFormatter;

	std::string mBoundEvalTraceFormatter;
	std::string mReportEvalTraceFormatter;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	ListOfExecutionContext * ecQueue;

	ListOfExecutionContext::iterator ecQueueIt;
	ListOfExecutionContext::iterator ecQueueItEnd;

	ExecutionContext::rw_child_iterator ecChildIt;
	ExecutionContext::rw_child_iterator ecChildItEnd;


public:
	/*
	 * Precedence for processor, based on resource consumption,
	 * used to order processor in the Diversity process !
	 * For info: 0 for minimum resource requirement reserved by STOP CRITERIA FILTER,
	 * and 255 maximum value for example REDUNDANCY FILTER
	 * Default value is the max !
	 * Processing: pre  = 255  , post = 255
	 * Filtering : init = 255
	 * Filtering : pre  = 255  , post = 255
	 */
	static const std::uint8_t DEFAULT_PRECEDENCE_OF_PROCESSOR[5];

	static const std::uint8_t DEFAULT_PRECEDENCE_OF_MAIN_PROCESSOR[5];


	static const std::uint8_t PRECEDENCE_OF_ACTIVE_COVERAGE_PROCESSOR[5];

	static const std::uint8_t PRECEDENCE_OF_PASSIVE_COVERAGE_PROCESSOR[5];


	static const std::uint8_t PRECEDENCE_OF_MAIN_PROCESSOR[5];

	static const std::uint8_t PRECEDENCE_OF_EXTENDER_PROCESSOR[5];

	static const std::uint8_t PRECEDENCE_OF_REDUNDANCY[5];


	static const std::uint8_t PRECEDENCE_OF_TRANSITION_COVERAGE[5];

	static const std::uint8_t PRECEDENCE_OF_HIT_OR_JUMP[5];


	static const std::uint8_t PRECEDENCE_OF_FORMULA_COVERAGE[5];

	static const std::uint8_t PRECEDENCE_OF_MACHINE_COVERAGE[5];

	static const std::uint8_t PRECEDENCE_OF_TEST_OFFLINE[5];


	static const std::uint8_t DEFAULT_PRECEDENCE_OF_SERIALIZER_PROCESSOR[5];


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AbstractProcessorUnit(
			SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject,
			avm_computing_process_stage_t requiredStage,
			const std::uint8_t * aPrecedence = DEFAULT_PRECEDENCE_OF_PROCESSOR);

	AbstractProcessorUnit(
			SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject,
			const std::uint8_t * aPrecedence = DEFAULT_PRECEDENCE_OF_PROCESSOR);

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	AbstractProcessorUnit(class_kind_t aClassKind,
			SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject);

	AbstractProcessorUnit(class_kind_t aClassKind, SymbexEngine & anEngine,
			SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject);


	/**
	 * DESTRUCTOR
	 */
	virtual ~AbstractProcessorUnit()
	{
		//!! NOTHING
	}


	/**
	 * GETTERS
	 * mPrecedenceOfPreProcess
	 * mPrecedenceOfPostProcess
	 */
	std::uint8_t getPrecedenceOfPreProcess() const
	{
		return mPrecedenceOfPreProcess;
	}

	std::uint8_t getPrecedenceOfPostProcess() const
	{
		return mPrecedenceOfPostProcess;
	}

	/**
	 * GETTERS
	 * mPrecedenceOfInitFilter
	 * mPrecedenceOfPreFilter
	 * mPrecedenceOfPostFilter
	 */
	std::uint8_t getPrecedenceOfInitFilter() const
	{
		return mPrecedenceOfInitFilter;
	}

	std::uint8_t getPrecedenceOfPreFilter() const
	{
		return mPrecedenceOfPreFilter;
	}

	std::uint8_t getPrecedenceOfPostFilter() const
	{
		return mPrecedenceOfPostFilter;
	}


	/**
	 * new local ExecutableForm for ProcessorT usage
	 */
	ExecutableForm * newLocalExecutableForm();


	/**
	 * GETTER
	 * mProcessorManager
	 */
	inline SymbexControllerUnitManager & getControllerUnitManager()
	{
		return( mControllerUnitManager );
	}

	inline const SymbexControllerUnitManager & getControllerUnitManager() const
	{
		return( mControllerUnitManager );
	}

	/**
	 * GETTER
	 * SymbexEngine
	 * Configuration
	 * SymbexDispatcher
	 *
	 */
	SymbexEngine & getSymbexEngine() const;

	Configuration & getConfiguration() const;

	SymbexDispatcher & getSymbexDispatcher() const;

	SymbexControllerEventManager & getSymbexEventManager() const;

	SymbexControllerRequestManager & getSymbexRequestManager() const;


//	/**
//	 * GETTER
//	 * mProcessorManager
//	 */
//	MainProcessorUnit & getMainProcessor();
//
//	const MainProcessorUnit & getMainProcessor() const;
//
//
//	/**
//	 * GETTER
//	 * the Builder
//	 */
//	Builder & getBuilder();
//
//	/**
//	 * GETTER
//	 * AvmPrimitiveProcessor
//	 */
//	AvmPrimitiveProcessor & getPrimitiveProcessor();


	/**
	 * GETTER - SETTER
	 * theExecutionQueue
	 */
	ExecutionQueue & getExecutionQueue();


	/**
	 * GETTER
	 * EvaluationEnvironment ENV
	 */
	inline EvaluationEnvironment & getENV()
	{
		return( ENV );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// PLUGIN PROCESSOR KIND
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER
	 * mAutoConfigure
	 */
	inline bool isAutoConfigure() const
	{
		return( mAutoConfigure );
	}

	/**
	 * GETTER - SETTER
	 * mComputingStageEnabled
	 */
#define DISABLE_PLUGIN( kind , FLAG )  kind &= ( ~ ( FLAG ) )

#define ENABLE_PLUGIN( kind , FLAG )   kind |= ( FLAG )


#define IS_DISABLE_PLUGIN( kind , FLAG )        ( (kind & ( FLAG )) == 0 )

#define IS_ENABLE_PLUGIN( kind , FLAG )         ( (kind & ( FLAG )) != 0 )

#define IS_STRONG_ENABLE_PLUGIN( kind , FLAG )  ( (kind & ( FLAG )) == ( FLAG ) )


	inline void enablePlugin(avm_computing_process_stage_t requiredStage,
			bool bEnabled = true)
	{
		if( bEnabled )
		{
			ENABLE_PLUGIN( mComputingStageEnabled , requiredStage );
		}
		else
		{
			DISABLE_PLUGIN( mComputingStageEnabled , requiredStage );
		}
	}

	inline bool isDisablePlugin() const
	{
		return( mComputingStageEnabled == AVM_UNDEFINED_STAGE );
	}

	inline bool isEnablePlugin() const
	{
		return( mComputingStageEnabled != AVM_UNDEFINED_STAGE );
	}

	inline bool isDisablePlugin(
			avm_computing_process_stage_t requiredStage) const
	{
		return( IS_DISABLE_PLUGIN(
				mComputingStageEnabled, requiredStage) );
	}

	inline bool isEnablePlugin(
			avm_computing_process_stage_t requiredStage) const
	{
		return( IS_STRONG_ENABLE_PLUGIN(
				mComputingStageEnabled, requiredStage) );
	}


	////////////////////////////////////////////////////////////////////////////
	// PRE PROCESS
	////////////////////////////////////////////////////////////////////////////

	inline void enablePreprocess(bool bEnabled = true)
	{
		enablePlugin( AVM_PRE_PROCESSING_STAGE , bEnabled );
	}

	void enablePreprocess(AbstractProcessorUnit * aProcessor);

	inline bool isDisablePreprocess() const
	{
		return( IS_DISABLE_PLUGIN(
				mComputingStageEnabled, AVM_PRE_PROCESSING_STAGE) );
	}

	inline bool isEnablePreprocess() const
	{
		return( IS_STRONG_ENABLE_PLUGIN(
				mComputingStageEnabled, AVM_PRE_PROCESSING_STAGE) );
	}


	// POST PROCESS
	inline void enablePostprocess(bool bEnabled = true)
	{
		enablePlugin( AVM_POST_PROCESSING_STAGE , bEnabled );
	}

	void enablePostprocess(AbstractProcessorUnit * aProcessor);

	inline bool isEnablePostprocess() const
	{
		return( IS_STRONG_ENABLE_PLUGIN(
				mComputingStageEnabled, AVM_POST_PROCESSING_STAGE) );
	}

	inline bool isDisablePostprocess() const
	{
		return( IS_DISABLE_PLUGIN(
				mComputingStageEnabled, AVM_POST_PROCESSING_STAGE) );
	}


	// PROCESS
	inline void enableProcess(bool bEnabled)
	{
		enablePlugin( AVM_PREPOST_PROCESSING_STAGE , bEnabled );
	}

	inline bool isStrongDisableProcess() const
	{
		return( IS_DISABLE_PLUGIN(
				mComputingStageEnabled, AVM_PREPOST_PROCESSING_STAGE) );
	}


	inline bool isStrongEnableProcess() const
	{
		return( IS_STRONG_ENABLE_PLUGIN(
				mComputingStageEnabled, AVM_PREPOST_PROCESSING_STAGE) );
	}

	inline bool isWeakEnableProcess() const
	{
		return( IS_ENABLE_PLUGIN(
				mComputingStageEnabled, AVM_PREPOST_PROCESSING_STAGE) );
	}


	////////////////////////////////////////////////////////////////////////////
	// PRE FILTER
	////////////////////////////////////////////////////////////////////////////

	inline void enablePrefilter(bool bEnabled = true)
	{
		enablePlugin( AVM_PRE_FILTERING_STAGE , bEnabled );
	}

	void enablePrefilter(AbstractProcessorUnit * aProcessor);

	inline bool isDisablePrefilter() const
	{
		return( IS_DISABLE_PLUGIN(
				mComputingStageEnabled, AVM_PRE_FILTERING_STAGE) );
	}

	inline bool isEnablePrefilter() const
	{
		return( IS_STRONG_ENABLE_PLUGIN(
				mComputingStageEnabled, AVM_PRE_FILTERING_STAGE) );
	}



	// POST FILTER
	inline void enablePostfilter(bool bEnabled = true)
	{
		enablePlugin( AVM_POST_FILTERING_STAGE , bEnabled );
	}

	void enablePostfilter(AbstractProcessorUnit * aProcessor);

	inline bool isEnablePostfilter() const
	{
		return( IS_STRONG_ENABLE_PLUGIN(
				mComputingStageEnabled, AVM_POST_FILTERING_STAGE) );
	}

	inline bool isDisablePostfilter() const
	{
		return( IS_DISABLE_PLUGIN(
				mComputingStageEnabled, AVM_POST_FILTERING_STAGE) );
	}



	// FILTER
	inline void enableFilter(bool bEnabled)
	{
		enablePlugin( AVM_PREPOST_FILTERING_STAGE , bEnabled );
	}

	inline bool isDisableFilter() const
	{
		return( IS_DISABLE_PLUGIN(
				mComputingStageEnabled, AVM_PREPOST_FILTERING_STAGE) );
	}

	inline bool isStrongEnableFilter() const
	{
		return( IS_STRONG_ENABLE_PLUGIN(
				mComputingStageEnabled, AVM_PREPOST_FILTERING_STAGE) );
	}

	inline bool requiresStrongEnableFilter() const
	{
		return( IS_STRONG_ENABLE_PLUGIN(
				mComputingStageRequired, AVM_PREPOST_FILTERING_STAGE) );
	}


	inline bool isWeakEnableFilter() const
	{
		return( IS_ENABLE_PLUGIN(
				mComputingStageEnabled, AVM_PREPOST_FILTERING_STAGE) );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// PLUGIN PROCESSOR API
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	/**
	 * FORMATTER
	 * SPIDER TRACE POSITION
	 */
	inline virtual std::string getDefaultSpiderTraceFormatter() const
	{
		return( "" );
	}

	inline virtual std::string getDefaultSpiderInitTraceFormatter() const
	{
		return( getDefaultSpiderTraceFormatter() );
	}
	inline virtual std::string getDefaultSpiderStepTraceFormatter() const
	{
		return( getDefaultSpiderTraceFormatter() );
	}
	inline virtual std::string getDefaultSpiderStopTraceFormatter() const
	{
		return( getDefaultSpiderTraceFormatter() );
	}


	/**
	 * FORMATTER
	 * EVALUATION TRACE INFORMATION
	 */
	inline virtual std::string getDefaultEvalTraceFormatter() const
	{
		return( "" );
	}

	inline virtual std::string getDefaultBoundEvalTraceFormatter() const
	{
		return( getDefaultEvalTraceFormatter() );
	}

	inline virtual std::string getDefaultPreEvalTraceFormatter() const
	{
		return( getDefaultEvalTraceFormatter() );
	}

	inline virtual std::string getDefaultPostEvalTraceFormatter() const
	{
		return( getDefaultEvalTraceFormatter() );
	}

	inline virtual std::string getDefaultReportEvalTraceFormatter() const
	{
		return( getDefaultEvalTraceFormatter() );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool preConfigure();

	virtual bool configure() override;

	virtual bool configureImpl() = 0;


	bool configureCommon();

	bool configureLog();

	bool checkingConfiguration();

	/**
	 * API
	 * Auto configure Model Of Execution in CPU
	 */
	virtual bool autoConfigureMOE();

	virtual bool autoConfigureMOEImpl();// = 0;


	////////////////////////////////////////////////////////////////////////////
	// INIT / EXIT  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool initImpl() override
	{
		//!! NOTHING
		return true;
	}

	virtual bool exitImpl() override
	{
		//!! NOTHING
		return true;
	}


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API
	////////////////////////////////////////////////////////////////////////////

	inline virtual bool filteringInitialize()
	{
		//!! NOTHING
		return( true );
	}

	inline virtual bool filteringFinalize()
	{
		//!! NOTHING
		return( true );
	}


	virtual bool prefilter();
	inline virtual bool prefilter(ExecutionContext & anEC)
	{
		//!! NOTHING
		return( true );
	}

	virtual bool postfilter();
	inline virtual bool postfilter(ExecutionContext & anEC)
	{
		//!! NOTHING
		return( true );
	}


	/**
	 * REPORT
	 */
	void reportHeader(OutStream & os, const std::string & processorName) const;

	virtual void reportDefault(OutStream & os) const override;


	/**
	 * SPIDER TRACE POSITION
	 */
	inline virtual void traceInitSpider(OutStream & os) const
	{
		//!! NOTHING
	}

	inline virtual void traceStepSpider(
			OutStream & os, const ExecutionContext & anEC) const
	{
		//!! NOTHING
	}

	inline virtual void traceStopSpider(OutStream & os) const
	{
		//!! NOTHING
	}


	/**
	 * EVAL TRACE INFORMATION
	 */
	inline virtual void tracePreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		AVM_VERBOSITY_SWITCH_SILENT

			traceSilentPreEval(os, anEC);

		AVM_VERBOSITY_SWITCH_CASE_MINIMUM

			traceMinimumPreEval(os, anEC);

		AVM_VERBOSITY_SWITCH_CASE_MEDIUM

			traceMediumPreEval(os, anEC);

		AVM_VERBOSITY_SWITCH_CASE_MAXIMUM

			traceMaximumPreEval(os, anEC);

		AVM_VERBOSITY_SWITCH_END
	}


	inline virtual void traceSilentPreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		// SILENT => NOTHING
	}

	inline virtual void traceMinimumPreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		traceDefaultPreEval(os, anEC);
	}

	inline virtual void traceMediumPreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		traceDefaultPreEval(os, anEC);
	}

	inline virtual void traceMaximumPreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		traceDefaultPreEval(os, anEC);
	}

	inline virtual void traceDefaultPreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		//!! NOTHING
	}


	inline virtual void tracePostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		AVM_VERBOSITY_SWITCH_SILENT

			traceSilentPostEval(os, anEC);

		AVM_VERBOSITY_SWITCH_CASE_MINIMUM

			traceMinimumPostEval(os, anEC);

		AVM_VERBOSITY_SWITCH_CASE_MEDIUM

			traceMediumPostEval(os, anEC);

		AVM_VERBOSITY_SWITCH_CASE_MAXIMUM

			traceMaximumPostEval(os, anEC);

		AVM_VERBOSITY_SWITCH_END
	}


	inline virtual void traceSilentPostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		// SILENT => NOTHING
	}

	inline virtual void traceMinimumPostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		traceDefaultPostEval(os, anEC);
	}

	inline virtual void traceMediumPostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		traceDefaultPostEval(os, anEC);
	}

	inline virtual void traceMaximumPostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		traceDefaultPostEval(os, anEC);
	}

	inline virtual void traceDefaultPostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		//!! NOTHING
	}


	inline virtual void traceBoundEval(OutStream & os) const
	{
		//!! NOTHING
	}

	inline virtual void reportEval(OutStream & os) const
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * STOP  | RELEASE
	 * RESET | RESTART | CONTINUE
	 * REQUEUE_WAITING | REQUEUE_RESERVE
	 * HEURISTIC | GOAL_ACHIEVED
	 */
	inline virtual void handleRequestStop()
	{
		//!! NOTHING
	}

	inline virtual void handleRequestRelease()
	{
		RunnableElement::setLifecycleReleased();
	}


	inline virtual void handleRequestReset()
	{
		//!! NOTHING
	}

	inline virtual void handleRequestRestart()
	{
		//!! NOTHING
	}

	inline virtual void handleRequestContinue()
	{
		//!! NOTHING
	}


	// the Waiting Queue Table
	inline virtual void handleRequestRequeueWaitingTable(
			WaitingStrategy & aWaitingStrategy,
			std::uint8_t aWeightMin, std::uint8_t aWeightMax)
	{
		//!! NOTHING
	}

	virtual void handleRequestRequeueReserveTable(
			WaitingStrategy & aWaitingStrategy,
			ListOfExecutionContext & aReserveQueue,
			std::uint8_t aWeightMin, std::uint8_t aWeightMax);


	inline virtual void handleRequestHeuristic()
	{
		//!! NOTHING
	}


	inline virtual void handleRequestGoalAchieved()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// REMOVE EC TOOLS
	////////////////////////////////////////////////////////////////////////////

	std::size_t remove(ExecutionContext * anEC,
			OutStream & logger = AVM_OS_TRACE, const std::string & msg = "");


	////////////////////////////////////////////////////////////////////////////
	// FINAL SLICING TOOLS
	////////////////////////////////////////////////////////////////////////////
	virtual bool isSliceableContext(ExecutionContext & anEC) const;

	void computeLeafEC(const ListOfExecutionContext & listOfRootEC,
			ListOfExecutionContext & listOfLeafEC);

	void slice(ListOfExecutionContext & listOfLeafEC);

	void slice(ListOfExecutionContext & listOfLeafEC,
			ExecutionContext * leafEC);


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	virtual std::string strTypeId() const
	{
		return( OSS() << "[p:" << (int)mPrecedenceOfPreProcess << ']'
				<< ( (mParameterWObject == WObject::_NULL_)
						? "fqn<process#unknown>"
						: mParameterWObject->hasQualifiedTypeNameID()
								? mParameterWObject->getQualifiedTypeNameID()
								: mParameterWObject->strUniqId() ) );
	}

	virtual std::string strUniqId() const override
	{
		return( OSS() << "[p:" << (int)mPrecedenceOfPreProcess << ']'
				<< ( (mParameterWObject == nullptr)
						? strFQN("null<WObject>")
						: mParameterWObject->strFQN("<unamed-fam>") ) );
	}

	virtual void toStream(OutStream & os) const override
	{
		if( mParameterWObject != nullptr )
		{
			mParameterWObject->toStream(os);
		}
		else
		{
			os << TAB << "null<WObject as Parameter>" << EOL;
		}
	}

};


////////////////////////////////////////////////////////////////////////////////
// FORMAL ANALYSIS MODULE SMART POINTER
////////////////////////////////////////////////////////////////////////////////

class FAM :
		public SmartPointer< AbstractProcessorUnit , DestroyElementPolicy >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( FAM )
{

private:
	/**
	 * TYPEDEF
	 */
	typedef SmartPointer< AbstractProcessorUnit ,
							DestroyElementPolicy >  base_this_type;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	FAM()
	: base_this_type( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	explicit FAM(AbstractProcessorUnit * aFAM)
	: base_this_type( aFAM )
	{
		//!! NOTHING
	}

public:
	/**
	 * DESTRUCTOR
	 */
	virtual ~FAM()
	{
		//!! NOTHING
	}



	////////////////////////////////////////////////////////////////////////////
	// COMPUTING STAGE ENABLED API
	////////////////////////////////////////////////////////////////////////////

	inline void enablePlugin(
			avm_computing_process_stage_t requiredStage,
			bool bEnabled = true)
	{
		mPTR->enablePlugin(requiredStage, bEnabled);
	}

	inline bool isDisablePlugin() const
	{
		return( mPTR->isDisablePlugin() );
	}

	inline bool isEnablePlugin() const
	{
		return( mPTR->isEnablePlugin() );
	}


	inline bool isEnablePreprocess() const
	{
		return( mPTR->isEnablePreprocess() );
	}

	inline bool isEnablePostprocess() const
	{
		return( mPTR->isEnablePostprocess() );
	}


	inline bool isEnablePrefilter() const
	{
		return( mPTR->isEnablePrefilter() );
	}

	inline bool isEnablePostfilter() const
	{
		return( mPTR->isEnablePostfilter() );
	}


	inline bool isWeakEnableFilter() const
	{
		return( mPTR->isWeakEnableFilter() );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE  API
	////////////////////////////////////////////////////////////////////////////

	inline const WObject * getParameterWObject() const
	{
		return mPTR->getParameterWObject();
	}


	inline bool configure()
	{
		return mPTR->configure();
	}


	////////////////////////////////////////////////////////////////////////////
	// INIT / EXIT  API
	////////////////////////////////////////////////////////////////////////////

	inline bool init()
	{
		return mPTR->init();
	}

	inline bool exit()
	{
		return mPTR->exit();
	}


	////////////////////////////////////////////////////////////////////////////
	// ( PRE / POST ) PROCESS  API
	////////////////////////////////////////////////////////////////////////////

	inline bool preprocess()
	{
		return mPTR->preprocess();
	}

	inline bool postprocess()
	{
		return mPTR->postprocess();
	}


	////////////////////////////////////////////////////////////////////////////
	// FILTERING  API
	////////////////////////////////////////////////////////////////////////////

	inline bool filteringInitialize()
	{
		return mPTR->filteringInitialize();
	}

	inline bool filteringFinalize()
	{
		return mPTR->filteringFinalize();
	}


	////////////////////////////////////////////////////////////////////////////
	// ( PRE / POST ) FILTER  API
	////////////////////////////////////////////////////////////////////////////

	inline bool prefilter()
	{
		return mPTR->prefilter();
	}

	inline bool prefilter(ExecutionContext & anEC)
	{
		return mPTR->prefilter( anEC );
	}


	inline bool postfilter()
	{
		return mPTR->postfilter();
	}

	inline bool postfilter(ExecutionContext & anEC)
	{
		return mPTR->postfilter( anEC );
	}


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	inline void report(OutStream & os) const
	{
		mPTR->report( os );
	}


	////////////////////////////////////////////////////////////////////////////
	// UNIT TEST API
	////////////////////////////////////////////////////////////////////////////

	inline void tddUnitReport(OutStream & os) const
	{
		mPTR->tddUnitReport( os );
	}


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	inline void tddRegressionReport(OutStream & os) const
	{
		mPTR->tddRegressionReport( os );
	}


	/**
	 * REPORT
	 */
	inline void reportHeader(
			OutStream & os, const std::string & processorName) const
	{
		mPTR->reportHeader(os, processorName);
	}


	/**
	 * EVAL TRACE
	 */
	inline void tracePreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->tracePreEval(os, anEC);
	}


	inline void traceSilentPreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->traceSilentPreEval(os, anEC);
	}

	inline void traceMinimumPreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->traceMinimumPreEval(os, anEC);
	}

	inline void traceMediumPreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->traceMediumPreEval(os, anEC);
	}

	inline void traceMaximumPreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->traceMaximumPreEval(os, anEC);
	}

	inline void traceDefaultPreEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->traceDefaultPreEval(os, anEC);
	}



	inline void tracePostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->tracePostEval(os, anEC);
	}


	inline void traceSilentPostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->traceSilentPostEval(os, anEC);
	}

	inline void traceMinimumPostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->traceMinimumPostEval(os, anEC);
	}

	inline void traceMediumPostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->traceMediumPostEval(os, anEC);
	}

	inline void traceMaximumPostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->traceMaximumPostEval(os, anEC);
	}

	inline void traceDefaultPostEval(
			OutStream & os, const ExecutionContext & anEC) const
	{
		mPTR->traceDefaultPostEval(os, anEC);
	}


	inline void traceBoundEval(OutStream & os) const
	{
		mPTR->traceBoundEval( os );
	}

	inline void reportEval(OutStream & os) const
	{
		mPTR->reportEval( os );
	}


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * STOP  | RELEASE
	 * RESET | RESTART | CONTINUE
	 * REQUEUE_WAITING | REQUEUE_RESERVE
	 * HEURISTIC | GOAL_ACHIEVED
	 */
	inline virtual void handleRequestStop()
	{
		mPTR->handleRequestStop();
	}

	inline virtual void handleRequestRelease()
	{
		mPTR->handleRequestRelease();
	}


	inline virtual void handleRequestReset()
	{
		mPTR->handleRequestReset();
	}

	inline virtual void handleRequestRestart()
	{
		mPTR->handleRequestRestart();
	}

	inline virtual void handleRequestContinue()
	{
		mPTR->handleRequestContinue();
	}


	// the Waiting Queue Table
	inline virtual void handleRequestRequeueWaitingTable(
			WaitingStrategy & aWaitingStrategy,
			std::uint8_t aWeightMin, std::uint8_t aWeightMax)
	{
		mPTR->handleRequestRequeueWaitingTable(
				aWaitingStrategy, aWeightMin, aWeightMax);
	}

	virtual void handleRequestRequeueReserveTable(
			WaitingStrategy & aWaitingStrategy,
			ListOfExecutionContext & aReserveQueue,
			std::uint8_t aWeightMin, std::uint8_t aWeightMax)
	{
		mPTR->handleRequestRequeueReserveTable(
				aWaitingStrategy, aReserveQueue, aWeightMin, aWeightMax);
	}


	inline virtual void handleRequestHeuristic()
	{
		mPTR->handleRequestHeuristic();
	}


	inline virtual void handleRequestGoalAchieved()
	{
		mPTR->handleRequestGoalAchieved();
	}

	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	inline std::string strTypeId() const
	{
		return mPTR->strTypeId();
	}

	inline std::string strUniqId() const
	{
		return mPTR->strUniqId();
	}

	inline void toStream(OutStream & os) const
	{
		mPTR->toStream( os );
	}

};


////////////////////////////////////////////////////////////////////////////////
// PROCESSOR UNIT AUTO REGISTRATION FACTORY
// for automatic registration in the processor repository
////////////////////////////////////////////////////////////////////////////////

template< class ProcessorT >
class AutoRegisteredProcessorUnit :  public  AbstractProcessorUnit
{

public:
	/**
	 * TYPDEDEF
	 */
	typedef AutoRegisteredProcessorUnit< ProcessorT >  RegisteredProcessorUnit;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AutoRegisteredProcessorUnit(SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject,
			avm_computing_process_stage_t requiredStage,
			const std::uint8_t * aPrecedence = DEFAULT_PRECEDENCE_OF_PROCESSOR)
	: AbstractProcessorUnit(aManager,
			wfParameterObject, requiredStage, aPrecedence)
	{
		//!! NOTHING
	}

	AutoRegisteredProcessorUnit(SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject,
			const std::uint8_t * aPrecedence = DEFAULT_PRECEDENCE_OF_PROCESSOR)
	: AbstractProcessorUnit(aManager, wfParameterObject, aPrecedence)
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	AutoRegisteredProcessorUnit(class_kind_t aClassKind,
			SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject)
	: AbstractProcessorUnit(aClassKind, aManager, wfParameterObject)
	{
		//!! NOTHING
	}

	AutoRegisteredProcessorUnit(class_kind_t aClassKind, SymbexEngine & anEngine,
			SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject)
	: AbstractProcessorUnit(aClassKind, anEngine, aManager, wfParameterObject)
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AutoRegisteredProcessorUnit()
	{
		// Force Instanciate
		(void) & AUTO_REGISTER_TOOL;
	}


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 */
	static struct AutoRegisterProcessorFactory  :
			public ProcessorUnitRegistrationImpl< ProcessorT >
	{
		AutoRegisterProcessorFactory()
		: ProcessorUnitRegistrationImpl< ProcessorT >(
				ProcessorT::QNID() , ProcessorT::QNID1() ,
				ProcessorT::QNID2(), ProcessorT::QNID3() )
		{
			//!! NOTHING
		}

	}  AUTO_REGISTER_TOOL;
	// end registration


	inline IProcessorUnitRegistration & REGISTER_TOOL() const override
	{
		return( AUTO_REGISTER_TOOL );
	}

	inline bool isRegisterTool(
			const IProcessorUnitRegistration & aRegisterTool) const
	{
		return( AUTO_REGISTER_TOOL.isEquals( aRegisterTool ) );
	}

};


template< class ProcessorT > typename
AutoRegisteredProcessorUnit< ProcessorT >::AutoRegisterProcessorFactory
AutoRegisteredProcessorUnit< ProcessorT >::AUTO_REGISTER_TOOL;


#define AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY( qnid ) \
	public: \
		static std::string QNID () { return( qnid  ); } \
		static std::string QNID1() { return( ""    ); } \
		static std::string QNID2() { return( ""    ); } \
		static std::string QNID3() { return( ""    ); }

#define AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_2( qnid , qnid1 ) \
	public: \
		static std::string QNID () { return( qnid  ); } \
		static std::string QNID1() { return( qnid1 ); } \
		static std::string QNID2() { return( ""    ); } \
		static std::string QNID3() { return( ""    ); }

#define AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3( qnid , qnid1 , qnid2 ) \
	public: \
		static std::string QNID () { return( qnid  ); } \
		static std::string QNID1() { return( qnid1 ); } \
		static std::string QNID2() { return( qnid2 ); } \
		static std::string QNID3() { return( ""    ); }

#define AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_4(qnid, qnid1, qnid2, qnid3) \
	public: \
		static std::string QNID () { return( qnid  ); } \
		static std::string QNID1() { return( qnid1 ); } \
		static std::string QNID2() { return( qnid2 ); } \
		static std::string QNID3() { return( qnid3 ); }



} /* namespace sep */
#endif /* ABSTRACTPROCESSORUNIT_H_ */

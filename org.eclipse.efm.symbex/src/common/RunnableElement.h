/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 1 déc. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef COMMON_RUNNABLEELEMENT_H_
#define COMMON_RUNNABLEELEMENT_H_

#include <common/NamedElement.h>
#include <common/SerializerFeature.h>


namespace sep
{


enum ExecCmdStatus
{
	EXEC_CMD_UNKNOWN,
	EXEC_CMD_OK,
	EXEC_CMD_EXIT,
	EXEC_CMD_FAILED
};


class WObject;


class RunnableElement :
		public NamedElement,
		public SerializerFeature,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( RunnableElement )
{


public:
	/**
	 * TYPEDEF
	 */
	typedef avm_uint16_t     lifecycle_status_t;

	enum {
		RUNNABLE_UNDEFINED_STATE       = 0x0000,


		RUNNABLE_CONFIGURED_STATE      = 0x0001,

		RUNNABLE_INITIALIZED_STATE     = 0x0002,

		RUNNABLE_STARTED_STATE         = 0x0004,

		RUNNABLE_RELEASED_STATE        = 0x0008,


		RUNNABLE_READY_STATE           = 0x0010,

		RUNNABLE_STANDBY_STATE         = 0x0020,


		RUNNABLE_IDLE_STATE            = 0x0040,

		RUNNABLE_RUNNING_STATE         = 0x0080,


		RUNNABLE_WAITING_STATE         = 0x0100,

		RUNNABLE_SUSPENDED_STATE       = 0x0200,


		RUNNABLE_STOPPED_STATE         = 0x0400,

		RUNNABLE_EXITED_STATE          = 0x0800,

		// ALIASES
		RUNNABLE_STATIC_READY_STATE    = RUNNABLE_INITIALIZED_STATE
		                               | RUNNABLE_STARTED_STATE
		                               | RUNNABLE_READY_STATE,

		RUNNABLE_DYNAMIC_READY_STATE   = RUNNABLE_IDLE_STATE
		                               | RUNNABLE_RUNNING_STATE,

		RUNNABLE_ACTIVE_STATE          = RUNNABLE_STARTED_STATE
		                               | RUNNABLE_READY_STATE
		                               | RUNNABLE_IDLE_STATE
		                               | RUNNABLE_RUNNING_STATE
		                               | RUNNABLE_WAITING_STATE
		                               | RUNNABLE_SUSPENDED_STATE,

		RUNNABLE_INACTIVE_STATE        = RUNNABLE_STANDBY_STATE
		                               | RUNNABLE_STOPPED_STATE
		                               | RUNNABLE_RELEASED_STATE
		                               | RUNNABLE_EXITED_STATE
	};


	struct AutoRunningIdleSwitcher
	{
		RunnableElement & mRunnableElement;

		AutoRunningIdleSwitcher(RunnableElement & aRunnableElement)
		:mRunnableElement( aRunnableElement )
		{
			mRunnableElement.setLifecycleRunning();
		}

		~AutoRunningIdleSwitcher()
		{
			mRunnableElement.setLifecycleIdle();
		}
	};


protected:
	/**
	 * ATTRIBUTE
	 */
	WObject * mParameterWObject;

	//Indicateur du bon déroulement de la procédure << configure() >>
	bool mConfigFlag;

	//Indicateur pour afficher un rapport final
	bool mReportPrintFlag;

	lifecycle_status_t mStartupLifecycleStatus;

	lifecycle_status_t mStaticLifecycleStatus;

	lifecycle_status_t mDynamicLifecycleStatus;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	RunnableElement(WObject * wfParameterObject);

	RunnableElement(class_kind_t aClassKind, WObject * wfParameterObject);

	/**
	 * CONSTRUCTOR
	 * Copy
	 * Abstract pur
	 */
	RunnableElement(const RunnableElement & aRunnable)
	: NamedElement( aRunnable ),
	SerializerFeature( aRunnable ),
	mParameterWObject( aRunnable.mParameterWObject ),
	mConfigFlag( aRunnable.mConfigFlag ),

	mReportPrintFlag( aRunnable.mReportPrintFlag ),

	mStartupLifecycleStatus( aRunnable.mStartupLifecycleStatus ),
	mStaticLifecycleStatus ( aRunnable.mStaticLifecycleStatus  ),
	mDynamicLifecycleStatus( aRunnable.mDynamicLifecycleStatus )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~RunnableElement()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mParameterWObject
	 */
	inline WObject * getParameterWObject() const
	{
		return( mParameterWObject );
	}

	inline bool hasParameterWObject() const
	{
		return( mParameterWObject != NULL /*WObject::_NULL_*/ );
	}

	void setParameterWObject(WObject * wfParameterObject);


	////////////////////////////////////////////////////////////////////////////
	// RUNNABLE LIFECYCLE API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * mStaticLifecycleStatus
	 */
	inline bool isLifecycleConfigured() const
	{
		return( (mStaticLifecycleStatus & RUNNABLE_CONFIGURED_STATE) != 0 );
	}

	inline void setLifecycleConfigured()
	{
		mStaticLifecycleStatus = RUNNABLE_CONFIGURED_STATE;
	}


	inline bool isLifecycleInitialized() const
	{
		return( (mStaticLifecycleStatus & RUNNABLE_INITIALIZED_STATE) != 0 );
	}

	inline void setLifecycleInitialized()
	{
		mStaticLifecycleStatus = RUNNABLE_INITIALIZED_STATE;
	}


	inline bool isLifecycleStarted() const
	{
		return( (mStaticLifecycleStatus & RUNNABLE_STARTED_STATE) != 0 );
	}

	inline void setLifecycleStarted()
	{
		mStaticLifecycleStatus = RUNNABLE_STARTED_STATE;
	}


	inline bool isLifecycleReleased() const
	{
		return( (mStaticLifecycleStatus & RUNNABLE_RELEASED_STATE) != 0 );
	}

	inline void setLifecycleReleased()
	{
		mStaticLifecycleStatus = RUNNABLE_RELEASED_STATE;
	}


	inline bool isLifecycleStopped() const
	{
		return( (mStaticLifecycleStatus & RUNNABLE_STOPPED_STATE) != 0 );
	}

	inline void setLifecycleStopped()
	{
		mStaticLifecycleStatus = RUNNABLE_STOPPED_STATE;
	}


	inline bool isLifecycleExited() const
	{
		return( (mStaticLifecycleStatus & RUNNABLE_EXITED_STATE) != 0 );
	}

	inline void setLifecycleExited()
	{
		mStaticLifecycleStatus = RUNNABLE_EXITED_STATE;
	}


	inline bool isLifecycleReady() const
	{
		return( (mStaticLifecycleStatus & RUNNABLE_READY_STATE) != 0 );
	}

	inline void setLifecycleReady()
	{
		mStaticLifecycleStatus = RUNNABLE_READY_STATE;
	}


	inline bool isLifecycleStandby() const
	{
		return( (mStaticLifecycleStatus & RUNNABLE_STANDBY_STATE) != 0 );
	}

	inline void setLifecycleStandby()
	{
		mStaticLifecycleStatus = RUNNABLE_STANDBY_STATE;
	}


	/**
	 * GETTER - SETTER
	 * mStaticLifecycleStatus
	 */
	inline bool isLifecycleIdle() const
	{
		return( (mDynamicLifecycleStatus & RUNNABLE_IDLE_STATE) != 0 );
	}

	inline void setLifecycleIdle()
	{
		mDynamicLifecycleStatus = RUNNABLE_IDLE_STATE;
	}


	inline bool isLifecycleRunning() const
	{
		return( (mDynamicLifecycleStatus & RUNNABLE_RUNNING_STATE) != 0 );
	}

	inline void setLifecycleRunning()
	{
		mDynamicLifecycleStatus = RUNNABLE_RUNNING_STATE;
	}


	inline bool isLifecycleWaiting() const
	{
		return( (mDynamicLifecycleStatus & RUNNABLE_WAITING_STATE) != 0 );
	}

	inline void setLifecycleWaiting()
	{
		mDynamicLifecycleStatus = RUNNABLE_WAITING_STATE;
	}


	inline bool isLifecycleSuspended() const
	{
		return( (mDynamicLifecycleStatus & RUNNABLE_SUSPENDED_STATE) != 0 );
	}

	inline void setLifecycleSuspended()
	{
		mDynamicLifecycleStatus = RUNNABLE_SUSPENDED_STATE;
	}


	/**
	 * TESTER
	 * LifecycleStatus
	 */
	inline bool isLifecycleActive() const
	{
		return( (mStaticLifecycleStatus & RUNNABLE_ACTIVE_STATE) != 0 );
	}

	inline bool isLifecycleInactive() const
	{
		return( (mStaticLifecycleStatus & RUNNABLE_INACTIVE_STATE) != 0 );
	}


	inline virtual bool isLifecycleRunnable()const
	{
		return( ((mDynamicLifecycleStatus & RUNNABLE_DYNAMIC_READY_STATE) != 0)
			&& ((mStaticLifecycleStatus & RUNNABLE_STATIC_READY_STATE) != 0) );
	}


	////////////////////////////////////////////////////////////////////////////
	// START / STOP / KILL / SUSPEND / RESUME  API
	////////////////////////////////////////////////////////////////////////////

//	virtual int start()
//	{
//		//!! NOTHING
//		return( true );
//	}

	inline virtual int stop()
	{
		setLifecycleStopped();

		//!! NOTHING
		return( 0 );
	}


	inline virtual int kill()
	{
		setLifecycleStopped();

		//!! NOTHING
		return( 0 );
	}


	inline virtual bool suspend()
	{
		setLifecycleSuspended();

		//!! NOTHING
		return( true );
	}

	inline virtual bool resume()
	{
		setLifecycleIdle();

		//!! NOTHING
		return( true );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configure();

	bool configureLifecycleState();

	virtual void configureDebug();


	////////////////////////////////////////////////////////////////////////////
	// INIT API
	////////////////////////////////////////////////////////////////////////////

	virtual bool initImpl() = 0;

	inline virtual bool init()
	{
		if( initImpl() )
		{
			setLifecycleInitialized();

			return( true );
		}

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	// EXIT API
	////////////////////////////////////////////////////////////////////////////

	virtual bool exitImpl() = 0;

	inline virtual bool exit()
	{
		if( exitImpl() )
		{
			setLifecycleExited();

			return( true );
		}

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void report(OutStream & os) const
	{
		if( mReportPrintFlag )
		{
			AVM_VERBOSITY_SWITCH_SILENT

				reportSilent(os);

			AVM_VERBOSITY_SWITCH_CASE_MINIMUM

				reportMinimum(os);

			AVM_VERBOSITY_SWITCH_CASE_MEDIUM

				reportMedium(os);

			AVM_VERBOSITY_SWITCH_CASE_MAXIMUM

				reportMaximum(os);

			AVM_VERBOSITY_SWITCH_END
		}
	}

	inline virtual void report(PairOutStream & os) const
	{
		report( os.OS1 );
		report( os.OS2 );
	}

	inline virtual void report(TripleOutStream & os) const
	{
		report( os.OS1 );
		report( os.OS2 );
		report( os.OS3 );
	}


	inline virtual void reportSilent(OutStream & os) const
	{
		reportMinimum(os);
	}

	inline virtual void reportMinimum(OutStream & os) const
	{
		reportDefault(os);
	}

	inline virtual void reportMedium(OutStream & os) const
	{
		reportDefault(os);
	}

	inline virtual void reportMaximum(OutStream & os) const
	{
		reportDefault(os);
	}

	inline virtual void reportDefault(OutStream & os) const
	{
		//!! NOTHING
	}



	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

	inline virtual bool preprocess()
	{
		//!! NOTHING
		return( true );
	}

	inline virtual bool postprocess()
	{
		//!! NOTHING
		return( true );
	}


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	static std::string strLifecycle(lifecycle_status_t aLifecycleStatus);

	static lifecycle_status_t toLifecycle(std::string aLifecycle);

	inline std::string strDynamicLifecycleStatus() const
	{
		return( strLifecycle(mDynamicLifecycleStatus) );
	}

	inline std::string strStaticLifecycleStatus() const
	{
		return( strLifecycle(mStaticLifecycleStatus) );
	}

	inline OutStream & strLifecycleStatus(OutStream & os) const
	{
		os << "< dynamic:" << strLifecycle(mStaticLifecycleStatus)
			<< " , static:" << strLifecycle(mDynamicLifecycleStatus) << " >";

		return( os );
	}

	virtual std::string strUniqId() const;

	inline virtual void toStream(OutStream & os) const
	{
		//!! NOTHING
	}

};


} /* namespace sep */

#endif /* COMMON_RUNNABLEELEMENT_H_ */

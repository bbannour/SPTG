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

#include "RunnableElement.h"

#include <fml/workflow/Query.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
RunnableElement::RunnableElement(const WObject * wfParameterObject)
: NamedElement( CLASS_KIND_T( RunnableElement ) , wfParameterObject ),
SerializerFeature( ),
mParameterWObject( wfParameterObject ),
mConfigFlag( false ),

mReportPrintFlag( true ),

mStartupLifecycleStatus( RUNNABLE_IDLE_STATE ),
mStaticLifecycleStatus ( RUNNABLE_UNDEFINED_STATE ),
mDynamicLifecycleStatus( RUNNABLE_UNDEFINED_STATE )
{
	//!! NOTHING
}

RunnableElement::RunnableElement(
		class_kind_t aClassKind, const WObject * wfParameterObject)
: NamedElement( aClassKind , wfParameterObject ),
SerializerFeature( ),
mParameterWObject( wfParameterObject ),
mConfigFlag( false ),

mReportPrintFlag( true ),

mStartupLifecycleStatus( RUNNABLE_IDLE_STATE ),
mStaticLifecycleStatus ( RUNNABLE_UNDEFINED_STATE ),
mDynamicLifecycleStatus( RUNNABLE_UNDEFINED_STATE )
{
	//!! NOTHING
}


/**
 * SETTER
 * mParameterWObject
 */
bool RunnableElement::hasParameterWObject() const
{
	return( mParameterWObject != WObject::_NULL_ );
}

void RunnableElement::setParameterWObject(const WObject * wfParameterObject)
{
	mParameterWObject = wfParameterObject;

	if( (mParameterWObject != WObject::_NULL_)
		&& isUnamed() )
	{
		setAllName( mParameterWObject );
	}
}


/**
 * CONFIGURE
 */
bool RunnableElement::configure()
{
	// INITIALIZATION
	configureDebug();

	mConfigFlag = true;

	if( getParameterWObject() != WObject::_NULL_ )
	{
		mConfigFlag = SerializerFeature::configure( getParameterWObject() );

		mReportPrintFlag = Query::getWPropertyBoolean(
				Query::getRegexWSequenceOrElse(getParameterWObject(),
						OR_WID2("report", "REPORT"),
						OR_WID2("property", "PROPERTY")),
				"reporting", true);
	}

	return( mConfigFlag );
}

/**
 *******************************************************************************
prototype process::... as &avm::processor... is
	section SCHEDULING
		@startup = 'waiting';
	endsection SCHEDULING
endprototype
 *******************************************************************************
 */
bool RunnableElement::configureLifecycleState()
{
	mStartupLifecycleStatus = RUNNABLE_IDLE_STATE;

	const WObject * theLIFECYCLE =
			Query::getRegexWSequence(getParameterWObject(),
				OR_WID4("lifecycle", "LIFECYCLE", "scheduling", "SCHEDULING"));

	if( theLIFECYCLE != WObject::_NULL_ )
	{
		std::string strStartupStatus =
				Query::getWPropertyString(theLIFECYCLE, "startup", "ready");

		mStartupLifecycleStatus =
				RunnableElement::toLifecycle(strStartupStatus);

		StringTools::tolower( strStartupStatus );

		if( (mStartupLifecycleStatus != RUNNABLE_READY_STATE)
			&& (mStartupLifecycleStatus != RUNNABLE_STANDBY_STATE) )
		{
			AVM_OS_WARN << "RunnableElement::configureLifecycleState:> "
					"Unexpected lifecycle other than READY or STANDBY status "
					"for startup !!!"
					<< std::endl;

			return( false );
		}
	}

	mDynamicLifecycleStatus = mStartupLifecycleStatus;

	mStaticLifecycleStatus = RUNNABLE_CONFIGURED_STATE;

	return( true );
}


void RunnableElement::configureDebug()
{
AVM_IF_DEBUG_FLAG_AND( CONFIGURING, (getParameterWObject() != WObject::_NULL_) )

	AVM_OS_LOG << std::endl;

	AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PARSING)

		getParameterWObject()->toStream(AVM_OS_LOG);

	AVM_DEBUG_ELSE

		AVM_OS_LOG << str_header( getParameterWObject() ) << std::endl;

	AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PARSING )

AVM_ENDIF_DEBUG_FLAG_AND( CONFIGURING )
}


/**
 * SERIALIZATION API
 */
std::string RunnableElement::strLifecycle(lifecycle_status_t aLifecycleStatus)
{
	switch( aLifecycleStatus)
	{
		case RUNNABLE_IDLE_STATE        : return( "IDLE"        );
		case RUNNABLE_RUNNING_STATE     : return( "RUNNING"     );

		case RUNNABLE_WAITING_STATE     : return( "WAITING"     );
		case RUNNABLE_SUSPENDED_STATE   : return( "SUSPENDED"   );
		case RUNNABLE_STOPPED_STATE     : return( "STOPPED"     );
		case RUNNABLE_EXITED_STATE      : return( "EXITED"      );

		case RUNNABLE_CONFIGURED_STATE  : return( "CONFIGURED"  );
		case RUNNABLE_INITIALIZED_STATE : return( "INITIALIZED" );
		case RUNNABLE_STARTED_STATE     : return( "STARTED"     );
		case RUNNABLE_RELEASED_STATE    : return( "RELEASED"    );

		case RUNNABLE_READY_STATE       : return( "READY"       );
		case RUNNABLE_STANDBY_STATE     : return( "STANDBY"     );

		case RUNNABLE_UNDEFINED_STATE   : return( "UNDEFINED"   );

		default                         : return( "UNKNOWN"     );
	}
}


RunnableElement::lifecycle_status_t
RunnableElement::toLifecycle(std::string aLifecycle)
{
	StringTools::toupper( aLifecycle );

#define TO_LIFECYCLE( lifecycle )  \
		if( aLifecycle == #lifecycle )  return( RUNNABLE_##lifecycle##_STATE );

	TO_LIFECYCLE( IDLE        )
	TO_LIFECYCLE( RUNNING     )

	TO_LIFECYCLE( WAITING     )
	TO_LIFECYCLE( SUSPENDED   )
	TO_LIFECYCLE( STOPPED     )
	TO_LIFECYCLE( EXITED      )

	TO_LIFECYCLE( CONFIGURED  )
	TO_LIFECYCLE( INITIALIZED )
	TO_LIFECYCLE( STARTED     )
	TO_LIFECYCLE( RELEASED    )

	TO_LIFECYCLE( READY       )
	TO_LIFECYCLE( STANDBY     )

	return( RUNNABLE_UNDEFINED_STATE );
}


std::string RunnableElement::strUniqId() const
{
	return( (mParameterWObject != WObject::_NULL_) ?
			mParameterWObject->strUniqId() : "<null-thread-id>" );
}


} /* namespace sep */

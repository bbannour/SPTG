/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASICTRACEFORMATTER_H_
#define BASICTRACEFORMATTER_H_

#include "AbstractTraceFormatter.h"


namespace sep
{


class AvmTraceGenerator;
class BF;
class ExecutionContext;
class RuntimeID;
class TraceManager;
class TracePoint;
class TraceSequence;
class WObject;


class BasicTraceFormatter  :  public AbstractTraceFormatter
{

protected:
	/**
	 * CONSTANTS
	 */
	static const std::string & DEFAULT_ASSIGN_PATTERN;

	static const std::string & DEFAULT_NEWFRESH_PATTERN;

	static const std::string & DEFAULT_INPUT_PATTERN;
	static const std::string & DEFAULT_OUTPUT_PATTERN;

	static const std::string & DEFAULT_INPUT_ENV_PATTERN;
	static const std::string & DEFAULT_OUTPUT_ENV_PATTERN;

	static const std::string & DEFAULT_INPUT_RDV_PATTERN;
	static const std::string & DEFAULT_OUTPUT_RDV_PATTERN;

	static const std::string & DEFAULT_MACHINE_PATTERN;

	static const std::string & DEFAULT_TRANSITION_PATTERN;

	static const std::string & DEFAULT_ROUTINE_PATTERN;


	/**
	 * ATTRIBUTES
	 */
	std::string mFileHeaderPattern;
	std::string mFileBeginPattern;
	std::string mFileEndPattern;

	std::string mExecutionContextUfidPattern;

	std::string mTestcaseHeaderPattern;
	std::string mTestcaseBeginPattern;
	std::string mTestcaseEndPattern;

	std::string mLifelineHeaderPattern;
	std::string mLifelineBeginPattern;
	std::string mLifelineEndPattern;

	std::string mLifelineIdPattern;

	std::string mInitializationHeaderPattern;
	std::string mInitializationBeginPattern;
	std::string mInitializationEndPattern;

	std::string mStepHeaderPattern;
	std::string mStepBeginPattern;
	std::string mStepEndPattern;

	std::string mCommentPattern;
	std::string mSeparatorPattern;
	std::string mNewlinePattern;

	std::string mPathConditionPattern;
	std::string mPathTimedConditionPattern;

	std::string mNodeConditionPattern;
	std::string mNodeTimedConditionPattern;

	std::string mTimePattern;

	std::string mAssignPattern;

	std::string mNewfreshPattern;

	std::string mInputPattern;
	std::string mOutputPattern;

	std::string mInputEnvPattern;
	std::string mOutputEnvPattern;

	std::string mInputRdvPattern;
	std::string mOutputRdvPattern;

	std::string mMachinePattern;
	std::string mTransitionPattern;
	std::string mRoutinePattern;

	std::string mRunnablePattern;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	TraceSequence * aTraceElement;
	StringOutStream ossValue;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BasicTraceFormatter(AvmTraceGenerator & aTraceGenerator)
	: AbstractTraceFormatter( aTraceGenerator ),
	mFileHeaderPattern( "" ),
	mFileBeginPattern( "" ),
	mFileEndPattern( "" ),

	mExecutionContextUfidPattern( "ctx< %1% > %6%" ),

	mTestcaseHeaderPattern( "TRACE NUMBER %1%\n" ),
	mTestcaseBeginPattern( "" ),
	mTestcaseEndPattern( "\n" ),

	mLifelineHeaderPattern( "LIFELINE %3% {\n" ),
	mLifelineBeginPattern( "" ),
	mLifelineEndPattern( "} // end lifeline %3%\n" ),

	mLifelineIdPattern( "%3%" ),

	mInitializationHeaderPattern( "\t// Initialization parameter values:\n" ),
	mInitializationBeginPattern( "" ),
	mInitializationEndPattern( "\n" ),

	mStepHeaderPattern( "#step#header %1%\n" ),
	mStepBeginPattern ( "#step#begin %1%\n"  ),
	mStepEndPattern   ( "#step#end %1%\n"    ),

	mCommentPattern  ( "// %1%\n" ),
	mSeparatorPattern( "%1%"   ),
	mNewlinePattern  ( "\n%1%" ),

	mPathConditionPattern( /*"PC: %1%"*/ ),
	mPathTimedConditionPattern( /*"PtC: %1%"*/ ),

	mNodeConditionPattern( /*"NC: %1%"*/ ),
	mNodeTimedConditionPattern( /*"NtC: %1%"*/ ),

	mTimePattern( "\t%3%\n" ),

	mAssignPattern( DEFAULT_ASSIGN_PATTERN ),

	mNewfreshPattern( DEFAULT_NEWFRESH_PATTERN ),

	mInputPattern ( DEFAULT_INPUT_PATTERN  ),
	mOutputPattern( DEFAULT_OUTPUT_PATTERN ),

	mInputEnvPattern ( DEFAULT_INPUT_ENV_PATTERN  ),
	mOutputEnvPattern( DEFAULT_OUTPUT_ENV_PATTERN ),

	mInputRdvPattern ( DEFAULT_INPUT_RDV_PATTERN  ),
	mOutputRdvPattern( DEFAULT_OUTPUT_RDV_PATTERN ),

	mMachinePattern   ( "\trun  %1%\n" ),
	mTransitionPattern( "\tfire %1%->%2%\n" ),
	mRoutinePattern   ( "\teval %1%->%2%\n" ),

	mRunnablePattern   ( "\trun %1%->%2%\n" ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	aTraceElement( NULL ),
	ossValue( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BasicTraceFormatter()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configure(WObject * FORMAT, std::string & formatPattern,
			const std::string & id, bool isRegex = false);

	bool configureImpl(WObject * wfParameterObject);


	////////////////////////////////////////////////////////////////////////////
	// FORMAT API
	////////////////////////////////////////////////////////////////////////////

	void format(TraceManager & aTraceManager);

	void format(OutStream & os, TraceManager & aTraceManager);

	void formatLifelines(OutStream & os, const TraceSequence & aTraceElt);

	std::string strFormatExecutionContextUfid(const ExecutionContext & anEC);

	void formatTraceID(OutStream & os, const TraceSequence & aTraceElt,
			const std::string & pattern);

	void formatLifelineID(OutStream & os, const RuntimeID & aLifeline,
			const std::string & pattern);

	void formatString(OutStream & os, const TracePoint & aTracePoint,
			const std::string & pattern);

	void formatStep(OutStream & os, const TracePoint & aTracePoint,
			const std::string & pattern);

	void format(OutStream & os, const TraceSequence & aTraceElt);

	void format(OutStream & os, const TracePoint & aTracePoint);

	void format(OutStream & os, const TracePoint & aTracePoint,
			const std::string & pattern);

	void formatIO(OutStream & os, const TracePoint & aTracePoint,
			const std::string & pattern);

	void wrap_format(OutStream & os, const TracePoint & aTracePoint,
			const std::string & pattern);

	void dotFormatCondition(OutStream & os,
			const std::string & formatPattern, const BF & aCode);

};


} /* namespace sep */

#endif /* BASICTRACEFORMATTER_H_ */

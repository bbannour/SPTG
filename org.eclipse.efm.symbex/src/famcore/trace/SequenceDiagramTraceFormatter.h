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
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SEQUENCEDIAGRAMTRACEFORMATTER_H_
#define SEQUENCEDIAGRAMTRACEFORMATTER_H_

#include "AbstractTraceFormatter.h"

#include <collection/Vector.h>

#include <fml/runtime/Message.h>

#include <map>


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


class SequenceDiagramTraceFormatter  :  public AbstractTraceFormatter
{

protected:
	/**
	 * CONSTANTS
	 * DEFAULT PROFILE
	 */
	static const std::string & DEFAULT_GLOBAL_HEADER_PATTERN;

	static const std::string & DEFAULT_GLOBAL_END_PATTERN;

	static const std::string & DEFAULT_EXECUTION_CONTEXT_PATTERN;

	static const std::string & DEFAULT_CONTEXT_ACTION_PATTERN;

	static const std::string & DEFAULT_BOX_HEADER_PATTERN;

	static const std::string & DEFAULT_BOX_END_PATTERN;

	static const std::string & DEFAULT_PARTICIPANT_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_SEPARATION_PATTERN;

	static const std::string & DEFAULT_PATH_HEADER_PATTERN;

	static const std::string & DEFAULT_PATH_END_PATTERN;

	static const std::string & DEFAULT_LIFELINE_HEADER_PATTERN;

	static const std::string & DEFAULT_LIFELINE_END_PATTERN;

	static const std::string & DEFAULT_LIFELINE_ID_PATTERN;

	static const std::string & DEFAULT_INIT_HEADER_PATTERN;

	static const std::string & DEFAULT_INIT_END_PATTERN;

	static const std::string & DEFAULT_STEP_HEADER_PATTERN;

	static const std::string & DEFAULT_STEP_BEGIN_PATTERN;

	static const std::string & DEFAULT_STEP_END_PATTERN;

	static const std::string & DEFAULT_PATH_CONDITION_PATTERN;

	static const std::string & DEFAULT_PATH_TIMED_CONDITION_PATTERN;

	static const std::string & DEFAULT_NODE_CONDITION_PATTERN;

	static const std::string & DEFAULT_NODE_TIMED_CONDITION_PATTERN;




	static const std::string & DEFAULT_ASSIGN_PATTERN;

	static const std::string & DEFAULT_TIME_PATTERN;

	static const std::string & DEFAULT_NEWFRESH_PATTERN;

	static const std::string & DEFAULT_INPUT_PATTERN;
	static const std::string & DEFAULT_OUTPUT_PATTERN;

	static const std::string & DEFAULT_INPUT_ENV_PATTERN;
	static const std::string & DEFAULT_OUTPUT_ENV_PATTERN;

	static const std::string & DEFAULT_INPUT_RDV_PATTERN;
	static const std::string & DEFAULT_OUTPUT_RDV_PATTERN;

	static const std::string & DEFAULT_MACHINE_PATTERN;

	static const std::string & DEFAULT_STATE_MACHINE_PATTERN;

	static const std::string & DEFAULT_STATE_PATTERN;

	static const std::string & DEFAULT_TRANSITION_PATTERN;

	static const std::string & DEFAULT_ROUTINE_PATTERN;

	static const std::string & DEFAULT_META_TRACE_PATTERN;
	static const std::string & DEFAULT_META_DEBUG_PATTERN;




	static unsigned int mIndexOfMessageInMap;

	static const std::string & RED_COLOR;

	static const std::string & GREEN_COLOR;

	static const std::string & BLUE_COLOR;

	static const std::string & ORANGE_COLOR;

	static const std::string & PURPLE_COLOR;

	static const std::string & TEAL_COLOR;

	static const std::string & MAROON_COLOR;

	static const std::string & OLIVE_COLOR;

	/**
	 * ATTRIBUTES
	 */
	std::string mFileHeaderPattern;
	std::string mFileBeginPattern;
	std::string mFileEndPattern;

	std::string mBoxHeaderPattern;

	std::string mBoxEndPattern;

	std::string mParticipantPattern;

	std::string mExecutionContextUfidPattern;

	std::string mPathHeaderPattern;
	std::string mPathBeginPattern;
	std::string mPathEndPattern;

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

	std::string mLifelineStatePattern;
	std::string mStateKindPattern;

	std::string mMachinePattern;
	std::string mStatemachinePattern;
	std::string mStatePattern;

	std::string mTransitionPattern;
	std::string mRoutinePattern;

	std::string mRunnablePattern;

	std::string mExecutionInformationPattern;

	std::string mMetaTracePattern;
	std::string mMetaDebugPattern;

	std::string mWrapDataSeparator;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	StringOutStream ossValue;

	const TraceSequence * mTraceSequence;

	Vector< std::pair< Message, int  > > mMapOfLifelineAndId;

	std::map< int, std::string > mMapOfColors;

	std::list<std::string> mListOfParticipants;

	const std::map< Message::pointer_t , List< RuntimeID> > & mMapMessageReceiver;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SequenceDiagramTraceFormatter(AvmTraceGenerator & aTraceGenerator);

	/**
	 * DESTRUCTOR
	 */
	virtual ~SequenceDiagramTraceFormatter()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configure(const WObject * FORMAT, std::string & formatPattern,
			const std::string & id, bool isRegex = false);

	virtual bool configureImpl(const WObject * wfParameterObject) override;


	////////////////////////////////////////////////////////////////////////////
	// FORMAT API
	////////////////////////////////////////////////////////////////////////////

	virtual void formatHeader(OutStream & os) override;
	virtual void formatTrace(OutStream & os, const TraceSequence & aTraceElt) override;
	virtual void formatFooter(OutStream & os) override;

	void formatBoxHeader(OutStream & out);

	void formatParticipant(OutStream & out);

	void formatLifelines(OutStream & os, const TraceSequence & aTraceElt);

	std::string formatLifelineId(
			const RuntimeID & aLifeline, const std::string & pattern);


	std::size_t toLifeline( const TraceSequence & lifelineInput,
			TraceSequence & lifelineTrace, const RuntimeID & lifelineRID) const;

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

	void formatOutput(OutStream & os,
			const TracePoint & aTracePoint, const std::string & outputPattern);

	void format(OutStream & os, const TracePoint & aTracePoint,
			const std::string & pattern);

	void formatIO(OutStream & os, const TracePoint & aTracePoint,
			const std::string & pattern);

	void formatOutput(OutStream & os, const TracePoint & aTracePoint,
			const std::string & pattern, List< RuntimeID > aListOfReceiverRID );

	void collectRuntimeReceiver(const TraceSequence & aTraceSequence,
			const Message & ioMessage, List< RuntimeID > & aListOfReceiverRID );

	void formatBuffer(OutStream & os, const TracePoint & aTracePoint,
			const std::string & pattern);

	void formatAssign(OutStream & os, const TracePoint & aTracePoint,
			const std::string & pattern);

	void formatCondition(OutStream & os,
			const std::string & formatPattern, const TracePoint & aTracePoint );

	void formatExecutionInformation(OutStream & os,
			const TracePoint & aTracePoint, const std::string & pattern);

	void formatNodeCondition( OutStream & os,
			const std::string & formatPattern, const TracePoint & aTracePoint );

	/**
	 * META
	 * @trace{ ... }
	 * @debug{ ... }
	 * @informal{ ... }
	 */
	void formatMetaElement(OutStream & os,
			const TracePoint & aTracePoint, const std::string & pattern);

	RuntimeID getLifelineRuntimeID(const BF & ioTrace) const;

	bool lifelineContains(const RuntimeID & lifelineRID,
			const TracePoint & aTracePoint) const;

	bool lifelineContains(
			const RuntimeID & lifelineRID, const BF & aRunTrace) const;


};


} /* namespace sep */

#endif /* SEQUENCEDIAGRAMTRACEFORMATTER_H_ */

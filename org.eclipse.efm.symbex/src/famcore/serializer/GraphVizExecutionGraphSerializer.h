/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_SERIALIZER_GRAPHVIZEXECUTIONGRAPHSERIALIZER_H_
#define FAM_SERIALIZER_GRAPHVIZEXECUTIONGRAPHSERIALIZER_H_

#include  <famcore/serializer/Serializer.h>

#include <fml/trace/TraceFilter.h>


namespace sep
{

class BF;
class RuntimeID;

class OutStream;

class AvmCode;
class AvmProgram;
class AvmTransition;
class AvmSerializerProcessor;

class Configuration;

class ExecutionContext;
class ExecutionData;

class GenericInfoData;
class InstanceOfBuffer;
class InstanceOfData;


class GraphVizExecutionGraphSerializer :
		public AutoRegisteredSerializerProcessorUnit< GraphVizExecutionGraphSerializer >
{

	AVM_DECLARE_CLONABLE_CLASS( GraphVizExecutionGraphSerializer )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_2(
			"serializer#symbex#graphviz",
			"GraphVizExecutionGraphSerializer")
	// end registration


protected:
	/**
	 * CONSTANTS
	 * DEFAULT PROFILE
	 */
	static const std::string & DEFAULT_GLOBAL_HEADER_PATTERN;

	static const std::string & DEFAULT_GLOBAL_END_PATTERN;


	static const std::string & DEFAULT_CONTEXT_NODE_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_LABEL_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_CSS_ATTRIBUTES;


	static const std::string & DEFAULT_CONTEXT_EDGE_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_HEADER_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_DATA_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_INFO_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_FIRED_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_TRACE_PATTERN;

	static const std::string & DEFAULT_INFO_PATTERN;

	static const std::string & DEFAULT_PATH_CONDITION_PATTERN;

	static const std::string & DEFAULT_PATH_TIMED_CONDITION_PATTERN;

	static const std::string & DEFAULT_NODE_CONDITION_PATTERN;

	static const std::string & DEFAULT_NODE_TIMED_CONDITION_PATTERN;

	static const std::string & DEFAULT_ASSIGN_BUFFER_PATTERN;

	static const std::string & DEFAULT_ASSIGN_VARIABLE_PATTERN;

	static const std::string & DEFAULT_NEWFRESH_PATTERN;

	static const std::string & DEFAULT_INPUT_PATTERN;
	static const std::string & DEFAULT_OUTPUT_PATTERN;

	static const std::string & DEFAULT_INPUT_ENV_PATTERN;
	static const std::string & DEFAULT_OUTPUT_ENV_PATTERN;

	static const std::string & DEFAULT_INPUT_RDV_PATTERN;
	static const std::string & DEFAULT_OUTPUT_RDV_PATTERN;


	static const std::string & DEFAULT_LIFELINE_STATE_PATTERN;

	static const std::string & DEFAULT_STATE_KIND_PATTERN;

	static const std::string & DEFAULT_MACHINE_PATTERN;

	static const std::string & DEFAULT_STATEMACHINE_PATTERN;

	static const std::string & DEFAULT_STATE_PATTERN;

	static const std::string & DEFAULT_TRANSITION_PATTERN;

	static const std::string & DEFAULT_ROUTINE_PATTERN;

	static const std::string & DEFAULT_VARIABLE_PATTERN;

	static const std::string & DEFAULT_BUFFER_PATTERN;

	/**
	 * CONSTANTS
	 * STANDARD PROFILE
	 */
	static const std::string & STANDARD_INFO_PATTERN;

	/**
	 * CONSTANTS
	 * CSS PROFILE
	 * COLOR / SHAPE / STYLE
	 */
	static const std::string & CONTEXT_NODE_CSS_COLOR;
	static const std::string & CONTEXT_NODE_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_CSS_STYLE;

	static const std::string & CONTEXT_NODE_PASSED_CSS_COLOR;
	static const std::string & CONTEXT_NODE_PASSED_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_PASSED_CSS_STYLE;

	static const std::string & CONTEXT_NODE_FAILED_CSS_COLOR;
	static const std::string & CONTEXT_NODE_FAILED_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_FAILED_CSS_STYLE;

	static const std::string & CONTEXT_NODE_INCONCLUSIVE_CSS_COLOR;
	static const std::string & CONTEXT_NODE_INCONCLUSIVE_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_INCONCLUSIVE_CSS_STYLE;

	static const std::string & CONTEXT_NODE_ABORTED_CSS_COLOR;
	static const std::string & CONTEXT_NODE_ABORTED_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_ABORTED_CSS_STYLE;

	static const std::string & CONTEXT_NODE_TIMEOUT_CSS_COLOR;
	static const std::string & CONTEXT_NODE_TIMEOUT_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_TIMEOUT_CSS_STYLE;

	static const std::string & CONTEXT_NODE_WARNING_CSS_COLOR;
	static const std::string & CONTEXT_NODE_WARNING_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_WARNING_CSS_STYLE;

	static const std::string & CONTEXT_NODE_ERROR_CSS_COLOR;
	static const std::string & CONTEXT_NODE_ERROR_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_ERROR_CSS_STYLE;

	static const std::string & CONTEXT_NODE_ALERT_CSS_COLOR;
	static const std::string & CONTEXT_NODE_ALERT_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_ALERT_CSS_STYLE;

	static const std::string & CONTEXT_NODE_EXIT_CSS_COLOR;
	static const std::string & CONTEXT_NODE_EXIT_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_EXIT_CSS_STYLE;

	static const std::string & CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_COLOR;
	static const std::string & CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_STYLE;

	static const std::string & CONTEXT_NODE_REDUNDANCY_TARGET_CSS_COLOR;
	static const std::string & CONTEXT_NODE_REDUNDANCY_TARGET_CSS_SHAPE;
	static const std::string & CONTEXT_NODE_REDUNDANCY_TARGET_CSS_STYLE;


	static const std::string & CONTEXT_PATH_PASSED_CSS_COLOR;
	static const std::string & CONTEXT_PATH_PASSED_CSS_SHAPE;
	static const std::string & CONTEXT_PATH_PASSED_CSS_STYLE;


protected:
	/**
	 * ATTRIBUTES
	 */
	TraceFilter mTraceFilter;

	std::string mGlobalHeaderPattern;
	std::string mGlobalEndPattern;

	std::string mContextNodePattern;
	std::string mContextNodeLabelPattern;
	std::string mContextNodeCssAttributes;

	std::string mContextNodeCssColor;
	std::string mContextNodeCssShape;
	std::string mContextNodeCssStyle;

	std::string mContextNodeSeparator;

	std::string mContextNodePassedCssColor;
	std::string mContextNodePassedCssShape;
	std::string mContextNodePassedCssStyle;

	std::string mContextNodeFailedCssColor;
	std::string mContextNodeFailedCssShape;
	std::string mContextNodeFailedCssStyle;

	std::string mContextNodeInconclusiveCssColor;
	std::string mContextNodeInconclusiveCssShape;
	std::string mContextNodeInconclusiveCssStyle;

	std::string mContextNodeAbortedCssColor;
	std::string mContextNodeAbortedCssShape;
	std::string mContextNodeAbortedCssStyle;

	std::string mContextNodeTimeoutCssColor;
	std::string mContextNodeTimeoutCssShape;
	std::string mContextNodeTimeoutCssStyle;

	std::string mContextNodeWarningCssColor;
	std::string mContextNodeWarningCssShape;
	std::string mContextNodeWarningCssStyle;

	std::string mContextNodeErrorCssColor;
	std::string mContextNodeErrorCssShape;
	std::string mContextNodeErrorCssStyle;

	std::string mContextNodeAlertCssColor;
	std::string mContextNodeAlertCssShape;
	std::string mContextNodeAlertCssStyle;

	std::string mContextNodeExitCssColor;
	std::string mContextNodeExitCssShape;
	std::string mContextNodeExitCssStyle;

	std::string mContextNodeRedundancySourceCssColor;
	std::string mContextNodeRedundancySourceCssShape;
	std::string mContextNodeRedundancySourceCssStyle;

	std::string mContextNodeRedundancyTargetCssColor;
	std::string mContextNodeRedundancyTargetCssShape;
	std::string mContextNodeRedundancyTargetCssStyle;

	std::string mContextPathPassedCssColor;
	std::string mContextPathPassedCssShape;
	std::string mContextPathPassedCssStyle;

	std::string mContextPathInconclusiveCssColor;
	std::string mContextPathInconclusiveCssShape;
	std::string mContextPathInconclusiveCssStyle;

	std::string mContextPathFailedCssColor;
	std::string mContextPathFailedCssShape;
	std::string mContextPathFailedCssStyle;

	std::string mContextPathAbortedCssColor;
	std::string mContextPathAbortedCssShape;
	std::string mContextPathAbortedCssStyle;

	std::string mContextPathTimeoutCssColor;
	std::string mContextPathTimeoutCssShape;
	std::string mContextPathTimeoutCssStyle;

	std::string mContextEdgePattern;

	std::string mContextNodeHeaderPattern;
	std::string mContextNodeDataPattern;
	std::string mContextNodeInfoPattern;
	std::string mContextNodeTraceRunPattern;
	std::string mContextNodeTraceIOPattern;

	std::string mInfoPattern;
	std::string mInfoJustification;
	std::string mInfoSeparator;

	std::string mPathConditionPattern;
	std::string mPathTimedConditionPattern;

	std::string mNodeConditionPattern;
	std::string mNodeTimedConditionPattern;

	std::string mAssignBufferPattern;

	std::string mAssignVariablePattern;
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
	std::string mVariablePattern;
	std::string mBufferPattern;

	bool mUsedSingleExecutionContextNodeFlag;

	bool mShowNodeHeaderFlag;
	bool mShowNodeDataFlag;
	bool mShowNodeInfoFlag;

	////////////////////////////////////////////////////////////////////////////
	// COMPUTING VARIABLE
	ListOfConstExecutionContext mDotFormatNodeWaitingQueue;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	GraphVizExecutionGraphSerializer(
			SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject)
	: RegisteredSerializerProcessorUnit(aManager, wfParameterObject,
			AVM_POST_PROCESSING_STAGE, DEFAULT_PRECEDENCE_OF_SERIALIZER_PROCESSOR),

	mTraceFilter( (wfParameterObject != WObject::_NULL_) ?
			wfParameterObject->getNameID() : "GraphVizExecutionGraphSerializer"),
	mGlobalHeaderPattern( DEFAULT_GLOBAL_HEADER_PATTERN ),
	mGlobalEndPattern( DEFAULT_GLOBAL_END_PATTERN ),

	mContextNodePattern( DEFAULT_CONTEXT_NODE_PATTERN ),
	mContextNodeLabelPattern( DEFAULT_CONTEXT_NODE_LABEL_PATTERN ),
	mContextNodeCssAttributes( DEFAULT_CONTEXT_NODE_CSS_ATTRIBUTES ),

	mContextNodeCssColor( CONTEXT_NODE_CSS_COLOR   ),
	mContextNodeCssShape( CONTEXT_NODE_CSS_SHAPE   ),
	mContextNodeCssStyle( CONTEXT_NODE_CSS_STYLE   ),

	mContextNodeSeparator( "\\n" ),

	mContextNodePassedCssColor( CONTEXT_NODE_PASSED_CSS_COLOR ),
	mContextNodePassedCssShape( CONTEXT_NODE_PASSED_CSS_SHAPE ),
	mContextNodePassedCssStyle( CONTEXT_NODE_PASSED_CSS_STYLE ),

	mContextNodeFailedCssColor( CONTEXT_NODE_FAILED_CSS_COLOR ),
	mContextNodeFailedCssShape( CONTEXT_NODE_FAILED_CSS_SHAPE ),
	mContextNodeFailedCssStyle( CONTEXT_NODE_FAILED_CSS_STYLE ),

	mContextNodeInconclusiveCssColor( CONTEXT_NODE_INCONCLUSIVE_CSS_COLOR ),
	mContextNodeInconclusiveCssShape( CONTEXT_NODE_INCONCLUSIVE_CSS_SHAPE ),
	mContextNodeInconclusiveCssStyle( CONTEXT_NODE_INCONCLUSIVE_CSS_STYLE ),

	mContextNodeAbortedCssColor( CONTEXT_NODE_ABORTED_CSS_COLOR ),
	mContextNodeAbortedCssShape( CONTEXT_NODE_ABORTED_CSS_SHAPE ),
	mContextNodeAbortedCssStyle( CONTEXT_NODE_ABORTED_CSS_STYLE ),

	mContextNodeTimeoutCssColor( CONTEXT_NODE_TIMEOUT_CSS_COLOR ),
	mContextNodeTimeoutCssShape( CONTEXT_NODE_TIMEOUT_CSS_SHAPE ),
	mContextNodeTimeoutCssStyle( CONTEXT_NODE_TIMEOUT_CSS_STYLE ),

	mContextNodeWarningCssColor( CONTEXT_NODE_WARNING_CSS_COLOR ),
	mContextNodeWarningCssShape( CONTEXT_NODE_WARNING_CSS_SHAPE ),
	mContextNodeWarningCssStyle( CONTEXT_NODE_WARNING_CSS_STYLE ),

	mContextNodeErrorCssColor( CONTEXT_NODE_ERROR_CSS_COLOR ),
	mContextNodeErrorCssShape( CONTEXT_NODE_ERROR_CSS_SHAPE ),
	mContextNodeErrorCssStyle( CONTEXT_NODE_ERROR_CSS_STYLE ),

	mContextNodeAlertCssColor( CONTEXT_NODE_ALERT_CSS_COLOR ),
	mContextNodeAlertCssShape( CONTEXT_NODE_ALERT_CSS_SHAPE ),
	mContextNodeAlertCssStyle( CONTEXT_NODE_ALERT_CSS_STYLE ),

	mContextNodeExitCssColor( CONTEXT_NODE_EXIT_CSS_COLOR ),
	mContextNodeExitCssShape( CONTEXT_NODE_EXIT_CSS_SHAPE ),
	mContextNodeExitCssStyle( CONTEXT_NODE_EXIT_CSS_STYLE ),

	mContextNodeRedundancySourceCssColor( CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_COLOR ),
	mContextNodeRedundancySourceCssShape( CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_SHAPE ),
	mContextNodeRedundancySourceCssStyle( CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_STYLE ),

	mContextNodeRedundancyTargetCssColor( CONTEXT_NODE_REDUNDANCY_TARGET_CSS_COLOR ),
	mContextNodeRedundancyTargetCssShape( CONTEXT_NODE_REDUNDANCY_TARGET_CSS_SHAPE ),
	mContextNodeRedundancyTargetCssStyle( CONTEXT_NODE_REDUNDANCY_TARGET_CSS_STYLE ),

	mContextPathPassedCssColor( CONTEXT_PATH_PASSED_CSS_COLOR ),
	mContextPathPassedCssShape( CONTEXT_PATH_PASSED_CSS_SHAPE ),
	mContextPathPassedCssStyle( CONTEXT_PATH_PASSED_CSS_STYLE ),

	mContextPathInconclusiveCssColor( CONTEXT_NODE_INCONCLUSIVE_CSS_COLOR ),
	mContextPathInconclusiveCssShape( CONTEXT_NODE_INCONCLUSIVE_CSS_SHAPE ),
	mContextPathInconclusiveCssStyle( CONTEXT_NODE_INCONCLUSIVE_CSS_STYLE ),

	mContextPathFailedCssColor( CONTEXT_NODE_FAILED_CSS_COLOR ),
	mContextPathFailedCssShape( CONTEXT_NODE_FAILED_CSS_SHAPE ),
	mContextPathFailedCssStyle( CONTEXT_NODE_FAILED_CSS_STYLE ),

	mContextPathAbortedCssColor( CONTEXT_NODE_ABORTED_CSS_COLOR ),
	mContextPathAbortedCssShape( CONTEXT_NODE_ABORTED_CSS_SHAPE ),
	mContextPathAbortedCssStyle( CONTEXT_NODE_ABORTED_CSS_STYLE ),

	mContextPathTimeoutCssColor( CONTEXT_NODE_TIMEOUT_CSS_COLOR ),
	mContextPathTimeoutCssShape( CONTEXT_NODE_TIMEOUT_CSS_SHAPE ),
	mContextPathTimeoutCssStyle( CONTEXT_NODE_TIMEOUT_CSS_STYLE ),

	mContextEdgePattern( DEFAULT_CONTEXT_EDGE_PATTERN ),

	mContextNodeHeaderPattern( DEFAULT_CONTEXT_NODE_HEADER_PATTERN ),

	mContextNodeDataPattern( DEFAULT_CONTEXT_NODE_DATA_PATTERN ),

	mContextNodeInfoPattern( DEFAULT_CONTEXT_NODE_INFO_PATTERN ),

	mContextNodeTraceRunPattern( DEFAULT_CONTEXT_NODE_FIRED_PATTERN ),
	mContextNodeTraceIOPattern ( DEFAULT_CONTEXT_NODE_TRACE_PATTERN ),

	mInfoPattern( DEFAULT_INFO_PATTERN ),
	mInfoJustification( "\\l" ),
	mInfoSeparator( "" ),

	mPathConditionPattern( DEFAULT_PATH_CONDITION_PATTERN ),
	mPathTimedConditionPattern( DEFAULT_PATH_TIMED_CONDITION_PATTERN ),

	mNodeConditionPattern( DEFAULT_NODE_CONDITION_PATTERN ),
	mNodeTimedConditionPattern( DEFAULT_NODE_TIMED_CONDITION_PATTERN ),

	mAssignBufferPattern( DEFAULT_ASSIGN_BUFFER_PATTERN ),

	mAssignVariablePattern( DEFAULT_ASSIGN_VARIABLE_PATTERN ),
	mNewfreshPattern( DEFAULT_NEWFRESH_PATTERN ),

	mInputPattern ( DEFAULT_INPUT_PATTERN  ),
	mOutputPattern( DEFAULT_OUTPUT_PATTERN ),

	mInputEnvPattern ( DEFAULT_INPUT_ENV_PATTERN  ),
	mOutputEnvPattern( DEFAULT_OUTPUT_ENV_PATTERN ),

	mInputRdvPattern ( DEFAULT_INPUT_RDV_PATTERN  ),
	mOutputRdvPattern( DEFAULT_OUTPUT_RDV_PATTERN ),

	mLifelineStatePattern( DEFAULT_LIFELINE_STATE_PATTERN ),
	mStateKindPattern( DEFAULT_STATE_KIND_PATTERN ),

	mMachinePattern( DEFAULT_MACHINE_PATTERN ),
	mStatemachinePattern( DEFAULT_STATEMACHINE_PATTERN ),
	mStatePattern( DEFAULT_STATE_PATTERN ),

	mTransitionPattern( DEFAULT_TRANSITION_PATTERN ),
	mRoutinePattern( DEFAULT_ROUTINE_PATTERN ),
	mVariablePattern( DEFAULT_VARIABLE_PATTERN ),
	mBufferPattern( DEFAULT_BUFFER_PATTERN ),

	mUsedSingleExecutionContextNodeFlag( true ),

	mShowNodeHeaderFlag( true ),
	mShowNodeDataFlag( true ),
	mShowNodeInfoFlag( true ),

	////////////////////////////////////////////////////////////////////////////
	// COMPUTING VARIABLE
	mDotFormatNodeWaitingQueue( )
	{
		mWrapData.SEPARATOR = "\\l";
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~GraphVizExecutionGraphSerializer()
	{
		//!! NOTHING
	}


	/**
	 * CONFIGURE
	 */
	virtual bool configureImpl() override;

	bool configureFormatter(const WObject * FORMAT, std::string & formatPattern,
			const std::string & id, bool isRegex = false);

	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(OutStream & out) const override;


	/**
	 * FILTERING API
	 */
	virtual bool prefilter() override;
	virtual bool postfilter() override;

	/**
	 * POST-PROCESSING API
	 */
	virtual bool postprocess() override;


	////////////////////////////////////////////////////////////////////////////
	// FACTORY API used by PYTHON BINDINGS
	////////////////////////////////////////////////////////////////////////////

	bool configureDefaultImpl(bool showTransition = true,
			bool showCommunication = true, bool showAssign = false);

	static void format(SymbexControllerUnitManager & aManager,
			OutStream & out, const ListOfExecutionContext & rootECs,
			bool showTransition = true, bool showCommunication = true,
			bool showAssign = true);


	////////////////////////////////////////////////////////////////////////////
	// FORMAT API
	////////////////////////////////////////////////////////////////////////////

	void dotFormat(OutStream & out, const ListOfExecutionContext & rootECs);

	void doFormatHeader(OutStream & out);
	void doFormatEnd(OutStream & out);

	void dotFormatNode(OutStream & out, const ExecutionContext & anEC);

	std::string dotNodeColor(const ExecutionContext & anEC);
	std::string dotNodeShape(const ExecutionContext & anEC);
	std::string dotNodeStyle(const ExecutionContext & anEC);

	void dotFormatEdge(OutStream & out,
			const ExecutionContext & srcEC, const ExecutionContext & tgtEC);

	void dotFormatNodeHeader(OutStream & out, const ExecutionContext & anEC);

	void dotFormatNodeData(OutStream & out, const ExecutionContext & anEC);

	void dotFormatNodeInfo(OutStream & out, const ExecutionContext & anEC);

	void dotFormatNodeRunnableTrace(
			OutStream & out, const ExecutionContext & anEC);

	void dotFormatNodeIOTrace(OutStream & out, const ExecutionContext & anEC);

	/**
	 * INFO
	 */
	void dotFormatInfo(OutStream & out, const GenericInfoData & anInfo);

	/**
	 * FIRED
	 * run machine
	 * fired transition
	 * invoke routine
	 */
	void dotFormatRunnableTrace(OutStream & out, const BF & aFired);

	void dotFormatMachine(OutStream & out,
			const RuntimeID & aRID, const std::string & pattern);

	void dotFormatTransition(OutStream & out,
			const RuntimeID & aRID, const AvmTransition & aTransition);

	void dotFormatRoutine(OutStream & out,
			const RuntimeID & aRID, const AvmProgram & aRoutine);

	/**
	 * TRACE
	 * input  ( port | signal | message ) [ values ]
	 * output ( port | signal | message ) [ values ]
	 * newfresh variable <- value
	 */
	void dotFormatIOTrace(OutStream & out,
			const ExecutionContext & anEC, const BF & aTrace);

	void dotFormatInputOutput(OutStream & out,
			const std::string & pattern,
			const ExecutionConfiguration & anExecConf);

	void dotFormatNewfresh(OutStream & out,
			const ExecutionConfiguration & anExecConf);

	void dotFormatAssignBuffer(OutStream & out,
			const ExecutionContext & anEC, bool isnotRoot);

	void dotFormatAssignBuffer(OutStream & out, const RuntimeID & aRID,
		const InstanceOfBuffer & aBuffer, const BaseBufferForm & aBufferValue);

	/**
	 * DATA
	 * [ Timed ] Path Condition
	 * Assignment: var = value
	 */
	void dotFormatCondition(OutStream & out,
			const std::string & formatPattern, const BF & aCondition);

	void dotFormatAssignVariable(OutStream & out,
			const ExecutionContext & anEC, bool isnotRoot);

	void dotFormatAssignVariable(OutStream & out, const RuntimeID & aRID,
			const InstanceOfData & aVar, const BF & aValue);

};


} /* namespace sep */

#endif /* FAM_SERIALIZER_GRAPHVIZEXECUTIONGRAPHSERIALIZER_H_ */

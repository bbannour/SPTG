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

#ifndef FAM_SERIALIZER_COMMON_EXECUTION_GRAPH_H_
#define FAM_SERIALIZER_COMMON_EXECUTION_GRAPH_H_

#include <fml/runtime/ExecutionContext.h>

#include <fml/trace/TraceFilter.h>

#include <sew/WorkflowParameter.h>


namespace sep
{

class EvaluationEnvironment;

class WrapData;


class CommonExecutionGraphSerializer
{

protected:
	/**
	 * CONSTANTS
	 * DEFAULT PROFILE
	 */
	static const std::string & DEFAULT_CONTEXT_NODE_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_LABEL_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_CSS_ATTRIBUTES;


	static const std::string & DEFAULT_CONTEXT_EDGE_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_HEADER_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_DATA_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_INFO_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_FIRED_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_TRACE_PATTERN;

	static const std::string & DEFAULT_CONTEXT_NODE_FLAGS_PATTERN;

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

	std::string mContextNodeFlagsPattern;

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
	CommonExecutionGraphSerializer(const WObject * wfParameterObject,
			const std::string & aGlobalHeaderPattern,
			const std::string & aGlobalEndPattern)
	: mTraceFilter( (wfParameterObject != WObject::_NULL_) ?
			wfParameterObject->getNameID() : "CommonExecutionGraphSerializer"),
	mGlobalHeaderPattern( aGlobalHeaderPattern ),
	mGlobalEndPattern( aGlobalEndPattern ),

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

	mContextNodeFlagsPattern( DEFAULT_CONTEXT_NODE_PATTERN ),

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
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~CommonExecutionGraphSerializer()
	{
		//!! NOTHING
	}

	/**
	 * CONFIGURE
	 */
	virtual bool configureImpl(const WObject * wfParameterObject,
			EvaluationEnvironment & ENV, WrapData & aWrapData);

	bool configureFormatter(const WObject * FORMAT, std::string & formatPattern,
			const std::string & id, bool isRegex = false);

	////////////////////////////////////////////////////////////////////////////
	// FACTORY API used by PYTHON BINDINGS
	////////////////////////////////////////////////////////////////////////////

	bool configureDefaultImpl(bool showTransition = true,
			bool showCommunication = true, bool showAssign = false);

};


} /* namespace sep */

#endif /* FAM_SERIALIZER_COMMON_EXECUTION_GRAPH_H_ */

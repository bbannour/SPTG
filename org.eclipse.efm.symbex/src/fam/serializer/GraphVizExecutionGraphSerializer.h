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

#include <fam/serializer/Serializer.h>

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

	static const std::string & DEFAULT_CONTEXT_NODE_CSS_PATTERN;


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

	static const std::string & DEFAULT_ASSIGN_PATTERN;

	static const std::string & DEFAULT_NEWFRESH_PATTERN;

	static const std::string & DEFAULT_INPUT_PATTERN;
	static const std::string & DEFAULT_OUTPUT_PATTERN;

	static const std::string & DEFAULT_INPUT_ENV_PATTERN;
	static const std::string & DEFAULT_OUTPUT_ENV_PATTERN;

	static const std::string & DEFAULT_INPUT_RDV_PATTERN;
	static const std::string & DEFAULT_OUTPUT_RDV_PATTERN;


	static const std::string & DEFAULT_LIFELINE_STATE_PATTERN;

	static const std::string & DEFAULT_MACHINE_PATTERN;

	static const std::string & DEFAULT_TRANSITION_PATTERN;

	static const std::string & DEFAULT_ROUTINE_PATTERN;

	static const std::string & DEFAULT_VARIABLE_PATTERN;

	/**
	 * CONSTANTS
	 * STANDARD PROFILE
	 */
	static const std::string & STANDARD_INFO_PATTERN;

	/**
	 * CONSTANTS
	 * CSS PROFILE
	 */
	static const std::string & DEFAULT_CONTEXT_NODE_COLOR;

	static const std::string & WARNING_CONTEXT_NODE_COLOR;
	static const std::string & ERROR_CONTEXT_NODE_COLOR;
	static const std::string & ALERT_CONTEXT_NODE_COLOR;

	static const std::string & OBJECTIVE_ACHIEVED_CONTEXT_NODE_COLOR;
	static const std::string & OBJECTIVE_ACHIEVED_CONTEXT_NODE_SHAPE;

	static const std::string & OBJECTIVE_FAILED_CONTEXT_NODE_COLOR;
	static const std::string & OBJECTIVE_FAILED_CONTEXT_NODE_SHAPE;

	static const std::string & OBJECTIVE_ABORTED_CONTEXT_NODE_COLOR;
	static const std::string & OBJECTIVE_ABORTED_CONTEXT_NODE_SHAPE;

	static const std::string & COVERAGE_ELEMENT_CONTEXT_NODE_COLOR;

	static const std::string & REDUNDANCY_CONTEXT_NODE_COLOR;
	static const std::string & REDUNDANCY_CONTEXT_NODE_SHAPE;

	static const std::string & REDUNDANCY_TARGET_CONTEXT_NODE_COLOR;
	static const std::string & REDUNDANCY_TARGET_CONTEXT_NODE_SHAPE;

	static const std::string & DEFAULT_CONTEXT_NODE_SHAPE;
	static const std::string & STATEMENT_EXIT_CONTEXT_NODE_SHAPE;

	static const std::string & DEFAULT_CONTEXT_NODE_STYLE;


protected:
	/**
	 * ATTRIBUTES
	 */
	TraceFilter mTraceFilter;

	std::string mGlobalHeaderPattern;
	std::string mGlobalEndPattern;

	std::string mContextNodePattern;
	std::string mContextNodeLabelPattern;
	std::string mContextNodeCssPattern;
	std::string mContextNodeColor;
	std::string mContextNodeShape;
	std::string mContextNodeStyle;
	std::string mContextNodeSeparator;

	std::string mContextEdgePattern;

	std::string mContextNodeHeaderPattern;
	std::string mContextNodeDataPattern;
	std::string mContextNodeInfoPattern;
	std::string mContextNodeFiredPattern;
	std::string mContextNodeTracePattern;

	std::string mInfoPattern;
	std::string mInfoJustification;
	std::string mInfoSeparator;

	std::string mPathConditionPattern;
	std::string mPathTimedConditionPattern;

	std::string mNodeConditionPattern;
	std::string mNodeTimedConditionPattern;

	std::string mAssignPattern;
	std::string mNewfreshPattern;

	std::string mInputPattern;
	std::string mOutputPattern;

	std::string mInputEnvPattern;
	std::string mOutputEnvPattern;

	std::string mInputRdvPattern;
	std::string mOutputRdvPattern;

	std::string mLifelineStatePattern;

	std::string mMachinePattern;
	std::string mTransitionPattern;
	std::string mRoutinePattern;
	std::string mVariablePattern;

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
			SymbexControllerUnitManager & aManager, WObject * wfParameterObject)
	: RegisteredSerializerProcessorUnit(aManager, wfParameterObject,
			AVM_POST_PROCESSING_STAGE, DEFAULT_PRECEDENCE_OF_SERIALIZER_PROCESSOR),

	mGlobalHeaderPattern( DEFAULT_GLOBAL_HEADER_PATTERN ),
	mGlobalEndPattern( DEFAULT_GLOBAL_END_PATTERN ),

	mContextNodePattern( DEFAULT_CONTEXT_NODE_PATTERN ),
	mContextNodeLabelPattern( DEFAULT_CONTEXT_NODE_LABEL_PATTERN ),
	mContextNodeCssPattern( DEFAULT_CONTEXT_NODE_CSS_PATTERN ),

	mContextNodeColor  ( DEFAULT_CONTEXT_NODE_COLOR   ),
	mContextNodeShape  ( DEFAULT_CONTEXT_NODE_SHAPE   ),
	mContextNodeStyle  ( DEFAULT_CONTEXT_NODE_STYLE   ),
	mContextNodeSeparator( "\\n" ),

	mContextEdgePattern( DEFAULT_CONTEXT_EDGE_PATTERN ),

	mContextNodeHeaderPattern( DEFAULT_CONTEXT_NODE_HEADER_PATTERN ),

	mContextNodeDataPattern( DEFAULT_CONTEXT_NODE_DATA_PATTERN ),

	mContextNodeInfoPattern( DEFAULT_CONTEXT_NODE_INFO_PATTERN ),

	mContextNodeFiredPattern( DEFAULT_CONTEXT_NODE_FIRED_PATTERN ),
	mContextNodeTracePattern( DEFAULT_CONTEXT_NODE_TRACE_PATTERN ),

	mInfoPattern( DEFAULT_INFO_PATTERN ),
	mInfoJustification( "\\l" ),
	mInfoSeparator( "" ),

	mPathConditionPattern( DEFAULT_PATH_CONDITION_PATTERN ),
	mPathTimedConditionPattern( DEFAULT_PATH_TIMED_CONDITION_PATTERN ),

	mNodeConditionPattern( DEFAULT_NODE_CONDITION_PATTERN ),
	mNodeTimedConditionPattern( DEFAULT_NODE_TIMED_CONDITION_PATTERN ),

	mAssignPattern( DEFAULT_ASSIGN_PATTERN ),
	mNewfreshPattern( DEFAULT_NEWFRESH_PATTERN ),

	mInputPattern ( DEFAULT_INPUT_PATTERN  ),
	mOutputPattern( DEFAULT_OUTPUT_PATTERN ),

	mInputEnvPattern ( DEFAULT_INPUT_ENV_PATTERN  ),
	mOutputEnvPattern( DEFAULT_OUTPUT_ENV_PATTERN ),

	mInputRdvPattern ( DEFAULT_INPUT_RDV_PATTERN  ),
	mOutputRdvPattern( DEFAULT_OUTPUT_RDV_PATTERN ),

	mLifelineStatePattern( DEFAULT_LIFELINE_STATE_PATTERN ),

	mMachinePattern( DEFAULT_MACHINE_PATTERN ),
	mTransitionPattern( DEFAULT_TRANSITION_PATTERN ),
	mRoutinePattern( DEFAULT_ROUTINE_PATTERN ),
	mVariablePattern( DEFAULT_VARIABLE_PATTERN ),

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
	virtual bool configureImpl();

	bool configureFormatter(WObject * FORMAT, std::string & formatPattern,
			const std::string & id, bool isRegex = false);

	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(OutStream & os) const;


	/**
	 * FILTERING API
	 */
	virtual bool prefilter();
	virtual bool postfilter();

	/**
	 * POST-PROCESSING API
	 */
	virtual bool postprocess();


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT FORMAT API
	////////////////////////////////////////////////////////////////////////////

	static void format(SymbexControllerUnitManager & aManager,
			OutStream & out, const ExecutionContext & rootEC);


	////////////////////////////////////////////////////////////////////////////
	// FORMAT API
	////////////////////////////////////////////////////////////////////////////

	void dotFormat(OutStream & os, const ExecutionContext & rootEC);

	void doFormatHeader(OutStream & os);
	void doFormatEnd(OutStream & os);

	void dotFormatNode(OutStream & os, const ExecutionContext & anEC);

	std::string dotNodeColor(const ExecutionContext & anEC);
	std::string dotNodeShape(const ExecutionContext & anEC);
	std::string dotNodeStyle(const ExecutionContext & anEC);

	void dotFormatEdge(OutStream & os,
			const ExecutionContext & srcEC, const ExecutionContext & tgtEC);

	void dotFormatNodeHeader(OutStream & os, const ExecutionContext & anEC);

	void dotFormatNodeData(OutStream & os, const ExecutionContext & anEC);

	void dotFormatNodeInfo(OutStream & os, const ExecutionContext & anEC);

	void dotFormatNodeRunnableTrace(
			OutStream & os, const ExecutionContext & anEC);

	void dotFormatNodeIOTrace(OutStream & os, const ExecutionContext & anEC);

	/**
	 * INFO
	 */
	void dotFormatInfo(OutStream & os, GenericInfoData * anInfo);

	/**
	 * FIRED
	 * run machine
	 * fired transition
	 * invoke routine
	 */
	void dotFormatRunnableTrace(OutStream & os, const BF & aFired);

	void dotFormatMachine(OutStream & os, const RuntimeID & aRID);

	void dotFormatTransition(OutStream & os,
			const RuntimeID & aRID, AvmTransition * aTransition);

	void dotFormatRoutine(OutStream & os,
			const RuntimeID & aRID, AvmProgram * aRoutine);

	/**
	 * TRACE
	 * input  ( port | signal | message ) [ values ]
	 * output ( port | signal | message ) [ values ]
	 * newfresh variable <- value
	 */
	void dotFormatIOTrace(OutStream & os, const BF & aTrace);

	void dotFormatInputOutput(OutStream & os, const std::string & pattern,
			const RuntimeID & aRID, AvmCode * aCode);

	void dotFormatNewfresh(OutStream & os,
			const RuntimeID & aRID, AvmCode * aCode);

	/**
	 * DATA
	 * [ Timed ] Path Condition
	 * Assignment: var = value
	 */
	void dotFormatCondition(OutStream & os,
			const std::string & formatPattern, const BF & aCondition);

	void dotFormatAssign(OutStream & os,
			const ExecutionData & anED, bool isnotRoot = true);

	void dotFormatAssign(OutStream & os, const RuntimeID & aRID,
			InstanceOfData * aVar, const BF & aValue);

};


} /* namespace sep */

#endif /* FAM_SERIALIZER_GRAPHVIZEXECUTIONGRAPHSERIALIZER_H_ */

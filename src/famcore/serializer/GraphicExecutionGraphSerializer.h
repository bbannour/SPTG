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

#ifndef FAM_SERIALIZER_GRAPHIC_EXECUTION_GRAPHSER_H_
#define FAM_SERIALIZER_GRAPHIC_EXECUTION_GRAPHSER_H_

#include  <famcore/serializer/Serializer.h>

#include  "CommonExecutionGraphSerializer.h"


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


class GraphicExecutionGraphSerializer final :
		public AutoRegisteredSerializerProcessorUnit< GraphicExecutionGraphSerializer >,
		public CommonExecutionGraphSerializer
{

	AVM_DECLARE_CLONABLE_CLASS( GraphicExecutionGraphSerializer )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_2(
			"serializer#symbex#graphic",
			"GraphicExecutionGraphSerializer")
	// end registration

protected:
	/**
	 * CONSTANTS
	 * DEFAULT PROFILE
	 */
	static const std::string & DEFAULT_GLOBAL_HEADER_PATTERN;

	static const std::string & DEFAULT_GLOBAL_END_PATTERN;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	GraphicExecutionGraphSerializer(
			SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject)
	: RegisteredSerializerProcessorUnit(aManager, wfParameterObject,
			AVM_POST_PROCESSING_STAGE, DEFAULT_PRECEDENCE_OF_SERIALIZER_PROCESSOR),
	CommonExecutionGraphSerializer( wfParameterObject ,
			DEFAULT_GLOBAL_HEADER_PATTERN, DEFAULT_GLOBAL_END_PATTERN )
	{
		mWrapData.SEPARATOR = "\\l";
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~GraphicExecutionGraphSerializer()
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

#endif /* FAM_SERIALIZER_GRAPHIC_EXECUTION_GRAPHSER_H_ */

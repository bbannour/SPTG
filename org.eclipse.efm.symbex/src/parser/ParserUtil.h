/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 9 juil. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef PARSER_UTIL_H_
#define PARSER_UTIL_H_

#include <common/BF.h>

#include <collection/BFContainer.h>
#include <collection/Typedef.h>

#include <fml/common/ModifierElement.h>

#include <fml/lib/IComPoint.h>

#include<stack>


namespace sep
{

class BFCode;

class ObjectElement;
class TraceableElement;

class InstanceOfMachine;

class Machine;
class Port;
class PropertyPart;
class Routine;
class System;
class Transition;


class ParserUtil
{

public:

	////////////////////////////////////////////////////////////////////////////
	// Current Parse Context :
	// System -> Machine -> Routine
	struct AvmParseContext
	{
		System * system = nullptr;

		Machine * machine = nullptr;

		Machine * dynamic = nullptr;

		Routine * routine = nullptr;

		PropertyPart * local = nullptr;
	};

	static AvmParseContext _CTX_;

	static std::stack< AvmParseContext > _CTX_STACK_;

	static void pushCTX(System * system);

	inline static void pushCTX(Machine * machine)
	{
		_CTX_.machine = machine;

		_CTX_STACK_.push( _CTX_ );
	}

	inline static void pushDynamicCTX(Machine * dynamic)
	{
		_CTX_.dynamic = dynamic;

		_CTX_STACK_.push( _CTX_ );
	}

	inline static void pushCTX(Routine * routine)
	{
		_CTX_.routine = routine;

		_CTX_STACK_.push( _CTX_ );
	}

	inline static void pushCTX(PropertyPart * local)
	{
		_CTX_.local = local;

		_CTX_STACK_.push( _CTX_ );
	}

	inline static void popCTX(Machine * & machine, Routine * & routine)
	{
		if( not _CTX_STACK_.empty() )
		{
			_CTX_STACK_.pop();

			if( not _CTX_STACK_.empty() )
			{
				_CTX_ = _CTX_STACK_.top();

				machine = _CTX_.machine;
				routine = _CTX_.routine;
			}
		}
	}



	////////////////////////////////////////////////////////////////////////////
	// XLIA_SYNTAX_ERROR_COUNT
	static std::size_t XLIA_SYNTAX_ERROR_COUNT;

	/**
	 * OutStream Manipulator
	 * SYNTAX_ERROR_EOL
	 */
	inline static void SYNTAX_ERROR_EOL(OutStream & os)
	{
		os << " !!!" << std::endl;
	}


	inline static WarnOutstreamT & avm_syntax_error(
			const std::string & rule, std::size_t line)
	{
		++XLIA_SYNTAX_ERROR_COUNT;

		AVM_OS_WARN << "Error[line:" << line
				<< "] in rule '" << rule << "' :> ";

		return( AVM_OS_WARN );
	}

	inline static WarnOutstreamT & avm_syntax_error(const std::string & rule)
	{
		++XLIA_SYNTAX_ERROR_COUNT;

		AVM_OS_WARN << "Error in rule '" << rule << "' :> ";

		return( AVM_OS_WARN );
	}


	////////////////////////////////////////////////////////////////////////////
	// SET LOCATION IN TRACEABLE FORM
	static void setLocation(TraceableElement * aModelingElement,
			std::size_t bLine, std::size_t eLine);

	static void setLocation(TraceableElement & aModelingElement,
			std::size_t bLine, std::size_t eLine);

	////////////////////////////////////////////////////////////////////////////
	// PROLOGUE OPTION
	static void setPrologueOption(const std::string & id, BF value);

	////////////////////////////////////////////////////////////////////////////
	// GET OBJECT BY [Qualified] Name ID
	static const BF & getObjectByNameID(const std::string & id);

	static const BF & getObjectByQualifiedNameID(
			const std::string & qnid, std::size_t count);


	////////////////////////////////////////////////////////////////////////////
	// GET VARIABLE BY [ [ Fully ] Qualified ] Name ID
	static const BF & getvar(const std::string & qnid, std::size_t count);

	static BF getVariable(const std::string & qnid, std::size_t count);

	static BF getDataType(const std::string & qnid, std::size_t count);

	static BF getDataTypeQueue(const std::string & qnid, std::size_t count);

	static BF getVarTime();
	static BF getVarDeltaTime();


	////////////////////////////////////////////////////////////////////////////
	// GET CONSTANT BY [ [ Fully ] Qualified ] Name ID
	static const BF & getConstant(
			const std::string & qnid, std::size_t count);

	static std::size_t getIntegerConstant(
			const std::string & qnid, std::size_t count);

	static avm_float_t getFloatConstant(
			const std::string & qnid, std::size_t count);


	////////////////////////////////////////////////////////////////////////////
	// GET BUFFER BY [ [ Fully ] Qualified ] Name ID
	static BF getBuffer(Machine * machine,
			const std::string & qnid, std::size_t count);

	static BF getvarBuffer(const std::string & qnid, std::size_t count);


	////////////////////////////////////////////////////////////////////////////
	// GET CHANNEL BY [ [ Fully ] Qualified ] Name ID
	static BF getChannel(const std::string & qnid, std::size_t count);

	static BF getDataTypeChannel(
			const std::string & qnid, std::size_t count);

	static void updateSignalRoutingChannel(Modifier::DIRECTION_KIND ioDirection,
			const BFCode & ioCode, const std::string & qnid, std::size_t count);


	////////////////////////////////////////////////////////////////////////////
	// GET PORT BY [ [ Fully ] Qualified ] Name ID
	inline static const BF & getComPort(
			const std::string & qnid, std::size_t count)
	{
		return( getComPort(_CTX_.machine, qnid, count) );
	}

	static const BF & getComPort(Machine * machine,
			const std::string & qnid, std::size_t count);

	static BF getvarPort(const std::string & qnid, std::size_t count);

	static void appendPortParameter(Port * port,
			const std::string & label, BFVector & labelledParams,
			BFList & positionalParams, const BF & param);

	static void computePortParameter(
			Port * port, const BFCode & ioStatement,
			BFVector & labelledParams, BFList & positionalParams);


	////////////////////////////////////////////////////////////////////////////
	// GET SIGNAL BY [ [ Fully ] Qualified ] Name ID
	inline static const BF & getComSignal(
			const std::string & qnid, std::size_t count)
	{
		return( getComSignal(_CTX_.machine, qnid, count) );
	}

	static const BF & getComSignal(Machine * machine,
			const std::string & qnid, std::size_t count);

	static BF getvarSignal(const std::string & qnid, std::size_t count);


	////////////////////////////////////////////////////////////////////////////
	// GET PORT / SIGNAL BY [ [ Fully ] Qualified ] Name ID
	static const BF & getComPortSignal(
			const std::string & qnid, std::size_t count)
	{
		return( getComPortSignal(_CTX_.machine, qnid, count) );
	}

	static const BF & getComPortSignal(Machine * machine,
			const std::string & qnid, std::size_t count);

	static BF getvarPortSignal(const std::string & qnid, std::size_t count);


	////////////////////////////////////////////////////////////////////////////
	// GET ROUTINE BY [ [ Fully ] Qualified ] Name ID
	static Routine * getRoutine(const std::string & id);

	static BF getvarRoutine(const std::string & id);

	////////////////////////////////////////////////////////////////////////////
	// GET PROCEDURE BY [ [ Fully ] Qualified ] Name ID
	static Machine * getProcedure(const std::string & id);

	static BF getvarProcedure(const std::string & id);


	////////////////////////////////////////////////////////////////////////////
	// GET MACHINE BY [ [ Fully ] Qualified ] Name ID
	static Machine * getMachine(Machine * machine,
			const std::string & qnid, std::size_t count);

	static BF getvarMachine(const std::string & qnid, std::size_t count);

	static BF getExecutableMachine(const std::string & qnid, std::size_t count);

	static BF getSelfExecutableMachine(const std::string & id);


	static void appendInstanceMachineParameter(Machine * machine,
			const std::string & label, BFVector & labelledParams,
			BFList & positionalParams, const BF & param);

	static void computeInstanceMachineParameter(Machine * machine,
			BFVector & labelledParams, BFList & positionalParams);

	static void appendInstanceMachineReturn(Machine * machine,
			const std::string & label, BFVector & labelledReturns,
			BFList & positionalReturns, const BF & param);

	static void computeInstanceMachineReturn(Machine * machine,
			BFVector & labelledReturns, BFList & positionalReturns);


	static void appendInstanceDynamicPositionalParameter(
			Machine * anInstance, const BF & rvParameter, std::size_t position);


	////////////////////////////////////////////////////////////////////////////
	// ROUTINE Parameters / Returns arguments
	static void appendRoutineParameters(Routine * routine,
			const std::string & label, BFVector & labelledParams,
			BFList & positionalParams, const BF & param);

	static void appendRoutineReturns(Routine * routine,
			const std::string & label, BFVector & labelledReturns,
			BFList & positionalReturns, const BF & param);

	static void computeRoutineParamReturn(const BF & ctxMachine,
			Routine * routine, BFCode & activityStatement,
			BFVector & labelledParams, BFList & positionalParams,
			BFVector & labelledReturns, BFList & positionalReturns);


	////////////////////////////////////////////////////////////////////////////
	// ACTIVITY ROUTINE Parameters / Returns arguments
	static Machine * getActivityMachine(const BF & ctxMachine);

	static void computeActivityRoutineParamReturn(const BF & ctxMachine,
			Routine * routine, BFCode & activityStatement,
			BFVector & labelledParams, BFList & positionalParams,
			BFVector & labelledReturns, BFList & positionalReturns);

	static void computeActivityRoutineInput(Machine * ctxMachine,
			Routine * routine, BFCode & invokeSequende,
			BFVector & labelledParams, BFList & positionalParams);

	static void computeActivityRoutineDefaultOutput(Machine * ctxMachine,
			Routine * routine, BFCode & invokeSequende,
			BFVector & labelledReturns, BFList & positionalReturns);

	static void computeActivityRoutineOutput(Machine * ctxMachine,
			Routine * routine, BFCode & invokeSequende,
			BFVector & labelledReturns, BFList & positionalReturns);


	////////////////////////////////////////////////////////////////////////////
	// GET INVOKABLE BY ID
	static BF getInvokable(const BF & target, const std::string & id);


	////////////////////////////////////////////////////////////////////////////
	// DECLARE DEFAULT STATE  #final, #terminal, #return  if need
	static void declareDefaultEndingStateIfNeed(
			ListOfMachine & needDefaultStateFinal,
			ListOfMachine & needDefaultStateTerminal,
			ListOfMachine & needDefaultStateReturn);


	////////////////////////////////////////////////////////////////////////////
	// INLINE PROCEDURE CALL IN TRANSITION
	static void checkProcedureCompositeMocKind(Machine * aProcedure);

	static void inlineTransitionProcedureCall(
			Transition * transition, const std::string & refId);

};


} /* namespace sep */

#endif /* PARSER_UTIL_H_ */

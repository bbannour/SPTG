/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 sept. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TraceFactory.h"

#include <fstream>

#include <boost/algorithm/string.hpp>

#include <builder/Builder.h>

#include <collection/BFContainer.h>

#include <computer/EvaluationEnvironment.h>

#include <fml/expression/AvmCode.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>

#include <fml/executable/AvmTransition.h>
#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/ExecutableSystem.h>

#include <fml/expression/StatementFactory.h>

#include <fml/operator/OperatorManager.h>

#include <fml/trace/BasicTraceParser.h>
#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>

#include <util/avm_string.h>


namespace sep
{

////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

/*
 // Declaration part
 section POINT
  @assign = "sens";

  @newfresh = "sens";

  @signal#sens = "sens";

  @port = "env";

  @input = "env";
  @output = "env";

  @output = "Thermostat->dt";
  @input  = "Thermostat->equip";
  @output2 = "Equipment->error";
 endsection POINT

 section TRACE
  @trace = ${ && "signal#sens" "output2" };
  @trace = [ "signal#sens" , "output2" ];
  @point = ( "signal#sens" || "output2" );
  @composite = ${ xor "signal#sens" "output2" };


  @assign = "sens";

  @newfresh = "sens";

  @signal = "sens";

  @port = "env";

  @input = "env";
  @output = "env";

  @output = "Thermostat->dt";
  @input  = "Thermostat->equip";
  @output = "Equipment->error";

  @transition = "Thermostat->transition#2#MSGm1#in";
  @routine = "Thermostat->transition#2#MSGm1#in";

  @machine = "Thermostat";

  @state = "Thermostat->s4";

  @formula = <expression>;


 endsection TRACE

*/

static ENUM_TRACE_POINT::TRACE_NATURE to_nature(const std::string & id)
{
	if( id.find("composite" ) == 0 ) return ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE;
	if( id.find("comp"      ) == 0 ) return ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE;
	if( id.find("expression") == 0 ) return ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE;
	if( id.find("expr"      ) == 0 ) return ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE;
	if( id.find("trace"     ) == 0 ) return ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE;
	if( id.find("point"     ) == 0 ) return ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE;

	if( id.find("communication") == 0 ) return ENUM_TRACE_POINT::TRACE_COM_NATURE;
	if( id.find("com"       ) == 0 ) return ENUM_TRACE_POINT::TRACE_COM_NATURE;
	if( id.find("inout"     ) == 0 ) return ENUM_TRACE_POINT::TRACE_COM_NATURE;

	if( id.find("channel"   ) == 0 ) return ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE;

	if( id.find("message"   ) == 0 ) return ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE;

	if( id.find("port"      ) == 0 ) return ENUM_TRACE_POINT::TRACE_PORT_NATURE;

	if( id.find("signal"    ) == 0 ) return ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE;

	if( id.find("time"      ) == 0 ) return ENUM_TRACE_POINT::TRACE_TIME_NATURE;

	if( id.find("var"       ) == 0 ) return ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE;
	if( id.find("variable"  ) == 0 ) return ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE;
//	if( id.find("assign"    ) == 0 ) return ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE;
//	if( id.find("newfresh"  ) == 0 ) return ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE;

	if( id.find("buffer"    ) == 0 ) return ENUM_TRACE_POINT::TRACE_BUFFER_NATURE;

	if( id.find("formula"   ) == 0 ) return ENUM_TRACE_POINT::TRACE_FORMULA_NATURE;
	if( id.find("condition" ) == 0 ) return ENUM_TRACE_POINT::TRACE_CONDITION_NATURE;
	if( id.find("decision"  ) == 0 ) return ENUM_TRACE_POINT::TRACE_DECISION_NATURE;

	if( REGEX_MATCH(id, CONS_WID2("path", "condition")) ) {
		return ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE;
	}
	if( REGEX_MATCH(id, CONS_WID2("node", "condition")) ) {
		return ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE;
	}

	if( REGEX_MATCH(id, CONS_WID3("path", "condition", "leaf")) ) {
		return ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF;
	}
	if( REGEX_MATCH(id, CONS_WID3("node", "condition", "leaf")) ) {
		return ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF;
	}

	if( REGEX_MATCH(id, CONS_WID3("path", "timed", "condition")) ) {
		return ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE;
	}
	if( REGEX_MATCH(id, CONS_WID3("node", "timed", "condition")) ) {
		return ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE;
	}

	if( REGEX_MATCH(id, CONS_WID4(
			"path", "timed", "condition", "(leaf|end|last|tail)")) ) {
		return ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF;
	}
	if( REGEX_MATCH(id, CONS_WID4(
			"node", "timed", "condition", "(leaf|end|last|tail)")) ) {
		return ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF;
	}

	if( id.find("statemachine") == 0 ) return ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE;
	if( id.find("machine") == 0 ) return ENUM_TRACE_POINT::TRACE_MACHINE_NATURE;
	if( id.find("state"  ) == 0 ) return ENUM_TRACE_POINT::TRACE_STATE_NATURE;


	if( id.find("transition") == 0 ) return ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE;
	if( id.find("routine"   ) == 0 ) return ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE;

	if( id.find("runnable"  ) == 0 ) return ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE;

	if( REGEX_MATCH(id, ENUM_TRACE_POINT::ATTRIBUTE_EXECUTION_INFORMATION_ID) ) {
		return ENUM_TRACE_POINT::TRACE_EXECUTION_INFORMATION_NATURE;
	}

	if( id.find("trace") == 0 ) return ENUM_TRACE_POINT::TRACE_META_TRACE_NATURE;
	if( id.find("debug") == 0 ) return ENUM_TRACE_POINT::TRACE_META_DEBUG_NATURE;

	if( REGEX_MATCH(id, CONS_WID2("step", "header")) ) {
		return ENUM_TRACE_POINT::TRACE_STEP_HEADER_NATURE;
	}
	if( REGEX_MATCH(id, CONS_WID2("step", "begin" )) ) {
		return ENUM_TRACE_POINT::TRACE_STEP_BEGIN_NATURE;
	}
	if( REGEX_MATCH(id, CONS_WID2("step", "end"   )) ) {
		return ENUM_TRACE_POINT::TRACE_STEP_END_NATURE;
	}

	if( REGEX_MATCH(id, CONS_WID2("init", "header")) ) {
		return ENUM_TRACE_POINT::TRACE_INIT_HEADER_NATURE;
	}
	if( REGEX_MATCH(id, CONS_WID2("init", "begin" )) ) {
		return ENUM_TRACE_POINT::TRACE_INIT_BEGIN_NATURE;
	}
	if( REGEX_MATCH(id, CONS_WID2("init", "end"   )) ) {
		return ENUM_TRACE_POINT::TRACE_INIT_END_NATURE;
	}

	if( id.find("comment"  ) == 0 ) return ENUM_TRACE_POINT::TRACE_COMMENT_NATURE;
	if( id.find("separator") == 0 ) return ENUM_TRACE_POINT::TRACE_SEPARATOR_NATURE;
	if( id.find("newline"  ) == 0 ) return ENUM_TRACE_POINT::TRACE_NEWLINE_NATURE;

//	if( not id.empty() )             return ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE;

	return ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE;
}


static AVM_OPCODE  to_op(const std::string & id)
{
	if( id.find("time"      ) == 0 ) return AVM_OPCODE_TIMED_GUARD;

	if( id.find("formula"   ) == 0 ) return AVM_OPCODE_GUARD;
	if( id.find("guard"     ) == 0 ) return AVM_OPCODE_GUARD;

	if( REGEX_MATCH(id,"check.sat") ) return AVM_OPCODE_CHECK_SAT;

	if( id.find("assign"    ) == 0 ) return AVM_OPCODE_ASSIGN;
	if( id.find("newfresh"  ) == 0 ) return AVM_OPCODE_ASSIGN_NEWFRESH;

	if( REGEX_MATCH(id, CONS_WID2("input", "env")) ) return AVM_OPCODE_INPUT_ENV;
	if( REGEX_MATCH(id, CONS_WID2("input", "buffer")) ) return AVM_OPCODE_INPUT_BUFFER;
	if( REGEX_MATCH(id, CONS_WID2("input", "broadcast")) ) return AVM_OPCODE_INPUT_BROADCAST;
	if( REGEX_MATCH(id, CONS_WID2("input", "rdv")) ) return AVM_OPCODE_INPUT_RDV;
	if( REGEX_MATCH(id, CONS_WID3("input", "multi", "rdv")) ) return AVM_OPCODE_INPUT_MULTI_RDV;

	if( id.find("input"     ) == 0 ) return AVM_OPCODE_INPUT;

	if( REGEX_MATCH(id, CONS_WID2("output", "env")) ) return AVM_OPCODE_OUTPUT_ENV;
	if( REGEX_MATCH(id, CONS_WID2("output", "buffer")) ) return AVM_OPCODE_OUTPUT_BUFFER;
	if( REGEX_MATCH(id, CONS_WID2("output", "broadcast")) ) return AVM_OPCODE_OUTPUT_BROADCAST;
	if( REGEX_MATCH(id, CONS_WID2("output", "rdv")) ) return AVM_OPCODE_OUTPUT_RDV;
	if( REGEX_MATCH(id, CONS_WID3("output", "multi", "rdv")) ) return AVM_OPCODE_OUTPUT_MULTI_RDV;

	if( id.find("output"    ) == 0 ) return AVM_OPCODE_OUTPUT;

	return AVM_OPCODE_NULL;
}


bool TraceFactory::configure(
		TraceSequence & aTraceElement, const ExecutionData * anED)
{
	const WObject * thePOINT = Query::getRegexWSequence(
			mParameterWObject, OR_WID2("point", "POINT"));
	if( (thePOINT != WObject::_NULL_) && thePOINT->hasOwnedElement() )
	{
//		if( configure(thePOINT, mDeclaredPoint, anED) )
//		{
//			//!! NOTHING
//		}
		mED = anED;

		WObject::const_iterator itWfO = thePOINT->owned_begin();
		WObject::const_iterator endWfO = thePOINT->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( configure(mDeclaredPoint, *itWfO) )
				{
					mDeclaredPointID.append( (*itWfO)->getNameID() );

					if( mDeclaredPoint.size() != mDeclaredPointID.size() )
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "TracePoint Declaration Error !!!"
								<< SEND_EXIT;
					}
				}
			}
		}
	}

	const WObject * theTRACE = Query::getRegexWSequence(
			mParameterWObject, OR_WID2("trace", "TRACE"));
	if( (theTRACE != WObject::_NULL_) && theTRACE->hasOwnedElement() )
	{
		if( configure(theTRACE, aTraceElement, anED) )
		{
			//!! NOTHING
		}
	}

	return( true );
}


bool TraceFactory::configure(
		AvmCode & aTraceExpression, const ExecutionData * anED)
{
	const WObject * thePOINT = Query::getRegexWSequence(
			mParameterWObject, OR_WID2("point", "POINT"));
	if( (thePOINT != WObject::_NULL_) && thePOINT->hasOwnedElement() )
	{
		mED = anED;

		WObject::const_iterator itWfO = thePOINT->owned_begin();
		WObject::const_iterator endWfO = thePOINT->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( configure(mDeclaredPoint, *itWfO) )
				{
					mDeclaredPointID.append( (*itWfO)->getNameID() );

					if( mDeclaredPoint.size() != mDeclaredPointID.size() )
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "TracePoint Declaration Error !!!"
								<< SEND_EXIT;
					}
				}
			}
		}
	}

	const WObject * theTRACE = Query::getRegexWSequence(
			mParameterWObject, OR_WID2("trace", "TRACE"));
	if( (theTRACE != WObject::_NULL_) && theTRACE->hasOwnedElement() )
	{
		if( configure(theTRACE, aTraceExpression.getOperands(), anED) )
		{
			//!! NOTHING
		}
	}

	return( true );
}

bool TraceFactory::collectIO(AvmCode & aTraceExpression, AvmCode & aTraceIO)
{
	for( const auto & itOperand : aTraceExpression.getOperands() )
	{
		if( itOperand.is< TracePoint >() )
		{
			const TracePoint & itTracePoint = itOperand.to< TracePoint >();
			if( itTracePoint.isCom() )
			{
				aTraceIO.append(itOperand);
			}
			else if( itTracePoint.isTransition()
					&& itTracePoint.object->is< AvmTransition >() )
			{
				BFList comStatement;
				StatementFactory::collectCommunication(
						itTracePoint.object->to< AvmTransition >().getCode(),
						comStatement);
				for( const auto & itStatement : comStatement )
				{
					const AvmCode & statement = itStatement.to< AvmCode >();
					AVM_OPCODE opNature = statement.getAvmOpCode();
					bfTP = aTracePoint = new TracePoint(
							ENUM_TRACE_POINT::TRACE_COM_NATURE, opNature);
					aTracePoint->object = statement.first().to_ptr< InstanceOfPort >();
					aTraceIO.append(bfTP);
				}
			}
		}
	}

	return true;
}

bool TraceFactory::configure(const WObject * aTraceSequence,
		BFCollection & tracePoints, const ExecutionData * anED)
{
	if( aTraceSequence == WObject::_NULL_ )
	{
		return( false );
	}
	else if( aTraceSequence->hasnoOwnedElement() )
	{
		return( true );
	}

	mED = anED;

	WObject::const_iterator itWfO = aTraceSequence->owned_begin();
	WObject::const_iterator endWfO = aTraceSequence->owned_end();
	for( ; itWfO != endWfO ; ++itWfO )
	{
		if( (*itWfO)->isWProperty() )
		{
			if( configure(tracePoints, *itWfO ) )
			{
				//!! NOTHING
			}
		}
	}

	return( true );
}


bool TraceFactory::configure(const WObject * aTraceSequence,
		TraceSequence & aTraceElement, const ExecutionData * anED)
{
	if( aTraceSequence == nullptr )
	{
		return( false );
	}
	else if( aTraceSequence->hasnoOwnedElement() )
	{
		return( true );
	}

	mED = anED;

	WObject::const_iterator itWfO = aTraceSequence->owned_begin();
	WObject::const_iterator endWfO = aTraceSequence->owned_end();

	if( (*itWfO)->isWProperty() )
	{
		if( (*itWfO)->getNameID() == "combinator" )
		{
			aTraceElement.combinator = OperatorManager::toOperator(
					(*itWfO)->toStringValue(),
					OperatorManager::OPERATOR_OR );

			++itWfO;
		}
	}

	for( ; itWfO != endWfO ; ++itWfO )
	{
		if( (*itWfO)->isWProperty() )
		{
			if( configure(aTraceElement.points, *itWfO ) )
			{
				//!! NOTHING
			}
		}
	}

	return( true );
}


bool TraceFactory::configure(const WObject * aTraceSequence,
		AvmCode * aTraceExpression, const ExecutionData * anED)
{
	if( aTraceSequence == nullptr )
	{
		return( false );
	}
	else if( aTraceSequence->hasnoOwnedElement() )
	{
		return( true );
	}

	mED = anED;

	WObject::const_iterator itWfO = aTraceSequence->owned_begin();
	WObject::const_iterator endWfO = aTraceSequence->owned_end();

	if( (*itWfO)->isWProperty() )
	{
		if( (*itWfO)->getNameID() == "combinator" )
		{
//			aTraceExpression.setOperator( OperatorManager::toOperator(
//					wfProperty->toStringValue(), OperatorManager::OPERATOR_OR) );

			AvmCode * subFTP = new AvmCode( OperatorManager::toOperator(
					(*itWfO)->toStringValue(),OperatorManager::OPERATOR_OR) );
			aTraceExpression->append( BF(subFTP) );
			aTraceExpression = subFTP;

			++itWfO;
		}
	}

	for( ; itWfO != endWfO ; ++itWfO )
	{
		if( (*itWfO)->isWProperty() )
		{
			if( (*itWfO)->getNameID() == "combinator" )
			{
				AvmCode * subFTP = new AvmCode(OperatorManager::toOperator(
						(*itWfO)->toStringValue(),
						OperatorManager::OPERATOR_OR) );
				aTraceExpression->append( BF(subFTP) );
				aTraceExpression = subFTP;
			}

			else if( configure(aTraceExpression->getOperands(), *itWfO) )
			{
				//!! NOTHING
			}
		}
	}

	return( true );
}


bool TraceFactory::configure(
		BFCollection & tracePoints, const WObject * wfProperty)
{
	ENUM_TRACE_POINT::TRACE_NATURE nature = to_nature( wfProperty->getNameID() );

	AVM_OPCODE opNature = to_op( wfProperty->getNameID() );


	if( (nature == ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE)
		&& (nature == ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE)
		&& (nature == ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE)
		&& (nature == ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE)

		&& (nature == ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF)
		&& (nature == ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF)
		&& (nature == ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF)
		&& (nature == ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF) )
	{
		bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_SELECT);

		if( not configureNodePathCondition(tracePoints, wfProperty->getValue()) )
		{
			AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
			wfProperty->warningLocation(AVM_OS_WARN)
					<< "Failed to configure <Node Path Condition> with value: "
					<< wfProperty->toStringValue() << std::endl;
		}
	}

	else if( nature == ENUM_TRACE_POINT::TRACE_EXECUTION_INFORMATION_NATURE )
	{
		bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_INFORMAL);

		if( not configureNodeInformation(tracePoints, wfProperty->getValue()) )
		{
			AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
			wfProperty->warningLocation(AVM_OS_WARN)
					<< "Failed to configure <Node Exec Information> with value: "
					<< wfProperty->toStringValue() << std::endl;
		}
	}

	else if( nature == ENUM_TRACE_POINT::TRACE_META_TRACE_NATURE )
	{
		bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_TRACE);

		if( not configureNodeInformation(tracePoints, wfProperty->getValue()) )
		{
			AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
			wfProperty->warningLocation(AVM_OS_WARN)
					<< "Failed to configure <Node Exec Trace> with value: "
					<< wfProperty->toStringValue() << std::endl;
		}
	}

	else if( nature == ENUM_TRACE_POINT::TRACE_META_TRACE_NATURE )
	{
		bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_DEBUG);

		if( not configureNodeInformation(tracePoints, wfProperty->getValue()) )
		{
			AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
			wfProperty->warningLocation(AVM_OS_WARN)
					<< "Failed to configure <Node Exec Debug> with value: "
					<< wfProperty->toStringValue() << std::endl;
		}
	}

	else if( wfProperty->hasBuiltinArrayValue() )
	{
		if( configureArray(tracePoints, wfProperty,
				wfProperty->getBuiltinArrayValue(), nature, opNature) )
		{
			//!! NOTHING
		}
	}

	else if( wfProperty->hasAvmCodeValue() )
	{
		if( (nature == ENUM_TRACE_POINT::TRACE_FORMULA_NATURE)
			|| (nature == ENUM_TRACE_POINT::TRACE_CONDITION_NATURE)
			|| (nature == ENUM_TRACE_POINT::TRACE_DECISION_NATURE) )
		{
			bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_CHECK_SAT);

			if( not configureFormula(tracePoints, wfProperty->getValue()) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Formula > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}
		}
		else if( configureExpression(tracePoints, wfProperty,
				wfProperty->getAvmCodeValue().raw_reference(), nature, opNature) )
		{
			//!! NOTHING
		}
	}

	else
	{
		if( nature != ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE )
		{
			if( configure(tracePoints, wfProperty,
					nature, wfProperty->toStringValue()) )
			{
				//!! NOTHING
			}
		}
		else if( opNature != AVM_OPCODE_NULL )
		{
			if( configure(tracePoints, wfProperty,
					opNature, wfProperty->toStringValue()) )
			{
				//!! NOTHING
			}
		}
	}

	return( true );
}


bool TraceFactory::configure(
		BFCollection & tracePoints, const WObject * wfProperty,
		ENUM_TRACE_POINT::TRACE_NATURE nature, const std::string & object)
{
	switch( nature )
	{
		case ENUM_TRACE_POINT::TRACE_COM_NATURE:
		case ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE:
		case ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE:
		case ENUM_TRACE_POINT::TRACE_PORT_NATURE:
		case ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_NULL);

			if( not configurePort(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Port > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_TIME_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_ASSIGN);

			if( not configureTime(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Time > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_ASSIGN);

			if( not configureVariable(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Variable > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_BUFFER_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_NULL);

			if( not configureBuffer(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Buffer > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_FORMULA_NATURE:
		case ENUM_TRACE_POINT::TRACE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_DECISION_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_CHECK_SAT);

			if( not configureFormula(tracePoints, wfProperty->getValue()) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Formula > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE:

		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF:
		{
			bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_SELECT);

			if( not configureNodePathCondition(tracePoints, wfProperty->getValue()) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Node Path Condition > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_MACHINE_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_RUN);

			if( not configureMachine(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Machine > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_NULL);

			if( not configureStatemachine(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Statemachine > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_STATE_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature,
					AVM_OPCODE_NULL /*AVM_OPCODE_ENABLE_SET*/);

			if( not configureState(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < State > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}


		case ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE:
		{
			bfTP = aTracePoint =
					new TracePoint(nature, AVM_OPCODE_INVOKE_TRANSITION);

			if( not configureTransition(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Transition > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature);
//					new TracePoint(nature, AVM_OPCODE_INVOKE_ROUTINE);

			if( not configureRoutine(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Routine > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature);

			if( not configureRunnable(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Runnable > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE:
		{
			bfTP = aTracePoint = new TracePoint(nature, AVM_OPCODE_NULL);

			if( not configureComposite(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Composite > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		default:
		{
			break;
		}
	}

	if( (mED != nullptr) && (aTracePoint != nullptr) )
	{
		aTracePoint->updateRID( *mED );
	}

	return( true );
}


bool TraceFactory::configure(
		BFCollection & tracePoints, const WObject * wfProperty,
		AVM_OPCODE opNature, const std::string & object)
{
	switch( opNature )
	{
		case AVM_OPCODE_INPUT:
		case AVM_OPCODE_INPUT_ENV:
		case AVM_OPCODE_OUTPUT:
		case AVM_OPCODE_OUTPUT_ENV:
		{
			bfTP = aTracePoint = new TracePoint(
					ENUM_TRACE_POINT::TRACE_COM_NATURE, opNature);

			if( not configurePort(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Port > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		case AVM_OPCODE_TIMED_GUARD:
		{
			break;
		}

		case AVM_OPCODE_ASSIGN:
		case AVM_OPCODE_ASSIGN_NEWFRESH:
		{
			bfTP = aTracePoint = new TracePoint(
					ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE, opNature);

			if( not configureVariable(tracePoints, object) )
			{
				AVM_OS_WARN << EOL << EMPHASIS("Configure warning ...", '*', 80);
				wfProperty->warningLocation(AVM_OS_WARN)
						<< "Failed to configure < Variable > with value: "
						<< wfProperty->toStringValue() << std::endl;
			}

			break;
		}

		default:
		{
			break;
		}
	}

	if( (mED != nullptr) && (aTracePoint != nullptr) )
	{
		aTracePoint->updateRID( *mED );
	}

	return( true );
}


bool TraceFactory::configureArray(BFCollection & tracePoints,
		const WObject * wfProperty, BuiltinArray * anArray,
		ENUM_TRACE_POINT::TRACE_NATURE nature, AVM_OPCODE opNature)
{
	BFVector tpArray;

	for( std::size_t offset = 0 ; offset < anArray->size() ; ++offset )
	{
		if( nature != ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE )
		{
			if( configure(tpArray, wfProperty, nature,
					wfProperty->toStringValue(anArray, offset)) )
			{
				//!! NOTHING
			}
		}
		else if( opNature != AVM_OPCODE_NULL )
		{
			if( configure(tpArray, wfProperty, opNature,
					wfProperty->toStringValue(anArray, offset)) )
			{
				//!! NOTHING
			}
		}
	}

	if( tpArray.singleton() )
	{
		tracePoints.append( tpArray[0] );
	}
	else if( tpArray.populated() )
	{
		bfTP = aTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE, AVM_OPCODE_AND);
		aTracePoint->tpid = ++TP_ID;
		aTracePoint->value = BF( new ArrayBF(tpArray) );

		tracePoints.append( bfTP );
	}

	return( true );
}


bool TraceFactory::configureExpression(BFCollection & tracePoints,
		const WObject * wfProperty, const AvmCode & aCode,
		ENUM_TRACE_POINT::TRACE_NATURE nature, AVM_OPCODE opNature)
{
	BFVector tpArray;

	for( const auto & itOperand : aCode.getOperands() )
	{
		if( itOperand.is< AvmCode >() )
		{
			if( configureExpression(tpArray, wfProperty,
					itOperand.to< AvmCode >(), nature, opNature) )
			{
				//!! NOTHING
			}
		}
		else if( nature != ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE )
		{
			if( configure(tpArray, wfProperty, nature,
					wfProperty->toStringValue(itOperand)) )
			{
				//!! NOTHING
			}
		}
		else if( opNature != AVM_OPCODE_NULL )
		{
			if( configure(tpArray, wfProperty,
					opNature, wfProperty->toStringValue(itOperand)) )
			{
				//!! NOTHING
			}
		}
	}

	if( tpArray.singleton() )
	{
		tracePoints.append( tpArray[0] );
	}
	else if( tpArray.populated() )
	{
		bfTP = aTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE,
				aCode.getAvmOpCode());
		aTracePoint->tpid = ++TP_ID;
		aTracePoint->value = BF( new ArrayBF(tpArray) );

		tracePoints.append( bfTP );
	}

	return( true );
}



bool TraceFactory::configureComposite(
		BFCollection & tracePoints, const std::string & object)
{
	for( std::size_t offset = 0 ; offset < mDeclaredPoint.size() ; ++offset )
	{
		if( mDeclaredPointID[offset] == object )
		{
			tracePoints.append( mDeclaredPoint[offset] );

			// if break: append first else: any Point with this ID
//			break;
		}
	}

	return( true );
}



bool TraceFactory::configurePort(
		BFCollection & tracePoints, const std::string & object)
{
	otherTracePoint.clear();

	if( aTracePoint->configurePort(mConfiguration, object, otherTracePoint) )
	{
		aTracePoint->tpid = ++TP_ID;

		listOfPortTracePoint.append( aTracePoint );
		listOfPortTracePoint.append( otherTracePoint );

		tracePoints.append( bfTP );

		while( otherTracePoint.nonempty() )
		{
			otherTracePoint.front()->tpid = ++TP_ID;

			tracePoints.append( BF(otherTracePoint.front()) );
			otherTracePoint.pop_front();
		}
	}
	else
	{
		return( false );
	}

	return( true );
}


bool TraceFactory::configureTime(
		BFCollection & tracePoints, const std::string & object)
{
	if( NamedElement::fqnStartsWith(object, "time" ) ||
		NamedElement::fqnStartsWith(object, "$time") ||
		NamedElement::fqnStartsWith(object, "#time") )
	{
		aTracePoint->tpid = ++TP_ID;
		aTracePoint->op = AVM_OPCODE_TIMED_GUARD;
		aTracePoint->object = mVarTime;

		tracePoints.append( bfTP );
	}
	else if( aTracePoint->configureVariable(
			mConfiguration, object, otherTracePoint) )
	{
		aTracePoint->tpid = ++TP_ID;
		aTracePoint->op = AVM_OPCODE_TIMED_GUARD;
		mVarTime = aTracePoint->object->to_ptr< InstanceOfData >();

		listOfVariableTracePoint.append( aTracePoint );
		listOfVariableTracePoint.append( otherTracePoint );

		tracePoints.append( bfTP );

		while( otherTracePoint.nonempty() )
		{
			otherTracePoint.front()->tpid = ++TP_ID;
			otherTracePoint.front()->op = AVM_OPCODE_TIMED_GUARD;

			tracePoints.append( BF(otherTracePoint.front()) );
			otherTracePoint.pop_front();
		}
	}
	else
	{
		return( false );
	}

	return( true );
}


bool TraceFactory::configureVariable(
		BFCollection & tracePoints, const std::string & object)
{
	if( NamedElement::fqnStartsWith(object, "time" ) ||
		NamedElement::fqnStartsWith(object, "$time") ||
		NamedElement::fqnStartsWith(object, "#time") )
	{
		aTracePoint->tpid = ++TP_ID;
		aTracePoint->nature = ENUM_TRACE_POINT::TRACE_TIME_NATURE;
		aTracePoint->op     = AVM_OPCODE_TIMED_GUARD;
		aTracePoint->object = mVarTime;

		tracePoints.append( bfTP );
	}
	else if( aTracePoint->configureVariable(
			mConfiguration, object, otherTracePoint) )
	{
		aTracePoint->tpid = ++TP_ID;

		listOfVariableTracePoint.append( aTracePoint );
		listOfVariableTracePoint.append( otherTracePoint );

		tracePoints.append( bfTP );

		while( otherTracePoint.nonempty() )
		{
			otherTracePoint.front()->tpid = ++TP_ID;

			tracePoints.append( BF(otherTracePoint.front()) );
			otherTracePoint.pop_front();
		}
	}
	else
	{
		return( false );
	}

	return( true );
}


bool TraceFactory::configureBuffer(
		BFCollection & tracePoints, const std::string & object)
{
	if( aTracePoint->configureBuffer(mConfiguration, object) )
	{
		aTracePoint->tpid = ++TP_ID;
		tracePoints.append( bfTP );

		listOfBufferTracePoint.append( aTracePoint );
	}
	else
	{
		return( false );
	}

	return( true );
}


bool TraceFactory::configureFormula(
		BFCollection & tracePoints, const BF & object)
{
	aTracePoint->tpid = ++TP_ID;

//	aTracePoint->value = ENV.getBuilder().compileExpression(
//			mConfiguration.getExecutableSystem()
//			.getSystemInstance().getExecutable(), object);

	ENV.getBuilder().resetErrorWarning();

	aTracePoint->value = ENV.getBuilder().
			compileExpression(mLocalExecutableForm, object);

	if( not ENV.getBuilder().hasError() )
	{
		tracePoints.append( bfTP );
	}

	return( true );
}


#define LEAF_NODE_REGEX_PATTERN     "\\S?(leaf|end|last|tail)\\S?"

#define LEAF_NODE_DEFAULT_PATTERN   ":leaf:"

bool TraceFactory::configureNodePathCondition(
		BFCollection & tracePoints, const BF & object)
{
	if( REGEX_MATCH( object.toBuiltinString() , LEAF_NODE_REGEX_PATTERN ) )
	{
		switch( aTracePoint->nature )
		{
			case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE:
			{
				aTracePoint->nature =
						ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF;
				break;
			}
			case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE:
			{
				aTracePoint->nature =
						ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF;
				break;
			}
			case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE:
			{
				aTracePoint->nature =
						ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF;
				break;
			}
			case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE:
			{
				aTracePoint->nature =
						ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF;
				break;
			}
			default:
			{
				break;
			}
		}

		aTracePoint->any_object = true;
	}

	else if( object.toBuiltinString() == "[*]" )
	{
		aTracePoint->any_object = true;
	}
	else
	{
		aTracePoint->value = object;
	}

	aTracePoint->tpid = ++TP_ID;
	tracePoints.append( bfTP );

	return( true );
}


bool TraceFactory::configureNodeInformation(
		BFCollection & tracePoints, const BF & object)
{
	if( object.toBuiltinString() == "[*]" )
	{
		aTracePoint->any_object = true;
	}
	else
	{
		aTracePoint->value = object;
	}

	aTracePoint->tpid = ++TP_ID;
	tracePoints.append( bfTP );

	return( true );
}


bool TraceFactory::configureMachine(
		BFCollection & tracePoints, const std::string & object)
{
	if( aTracePoint->configureMachine(mConfiguration, object) )
	{
		aTracePoint->tpid = ++TP_ID;
		tracePoints.append( bfTP );
	}
	else
	{
		return( false );
	}

	return( true );
}


bool TraceFactory::configureState(
		BFCollection & tracePoints, const std::string & object)
{
	if( aTracePoint->configureMachine(mConfiguration, object) )
	{
		aTracePoint->tpid = ++TP_ID;
		tracePoints.append( bfTP );
	}
	else
	{
		return( false );
	}

	return( true );
}

bool TraceFactory::configureStatemachine(
		BFCollection & tracePoints, const std::string & object)
{
	if( aTracePoint->configureMachine(mConfiguration, object) )
	{
		aTracePoint->tpid = ++TP_ID;
		tracePoints.append( bfTP );
	}
	else
	{
		return( false );
	}

	return( true );
}


bool TraceFactory::configureTransition(
		BFCollection & tracePoints, const std::string & object)
{
	if( aTracePoint->configureTransition(mConfiguration, object) )
	{
		aTracePoint->tpid = ++TP_ID;
		tracePoints.append( bfTP );
	}
	else
	{
		return( false );
	}

	return( true );
}


bool TraceFactory::configureRoutine(
		BFCollection & tracePoints, const std::string & object)
{
	if( aTracePoint->configureRoutine(mConfiguration, object) )
	{
		aTracePoint->tpid = ++TP_ID;
		tracePoints.append( bfTP );
	}
	else
	{
		return( false );
	}

	return( true );
}


bool TraceFactory::configureRunnable(
		BFCollection & tracePoints, const std::string & object)
{
	if( aTracePoint->configureRunnable(mConfiguration, object) )
	{
		aTracePoint->tpid = ++TP_ID;
		tracePoints.append( bfTP );
	}
	else
	{
		return( false );
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// BASIC PARSER API
////////////////////////////////////////////////////////////////////////////////

/*
 * Exemple de trace basique
1
TSI_target?1
120
RSD_ENABLED_source!1
0
PSD_ENABLED_source!1
423385
RSD_CMD_source!1
0
PSD_STATE1_target?0
3025646
DEP_AUTH1_source!1
1059822
TSI1_target?0
*/

bool TraceFactory::parseBasicTrace(TraceSequence & aTraceElement,
		std::ifstream & inFile, const BF & aVarTime)
{

	BasicTraceParser aParser( mConfiguration );

	return( aParser.parseBasicTrace(aTraceElement, inFile, aVarTime) );
}

bool TraceFactory::parseBasicXliaTrace(TraceSequence & aTraceElement,
		std::ifstream & inFile, const BF & aVarTime)
{

	BasicTraceParser aParser( mConfiguration );

	return( aParser.parseBasicXliaTrace(aTraceElement, inFile, aVarTime) );
}

////////////////////////////////////////////////////////////////////////////////
// OTHER API
////////////////////////////////////////////////////////////////////////////////

bool TraceFactory::appendTransitionPoint(const Configuration & aConfiguration,
		TraceSequence & aTraceElement, const std::string & aTransitionUfid)
{
	ExecutableQuery XQuery( aConfiguration );

	const BF & foundTransition =
			XQuery.getTransitionByQualifiedNameID(aTransitionUfid);

	if( foundTransition.valid() )
	{
		BF newTransitionPoint( new TracePoint(
				ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE,
				AVM_OPCODE_INVOKE_TRANSITION, nullptr,
				foundTransition.to_ptr< AvmTransition >()) );

		aTraceElement.points.append( newTransitionPoint );

		return( true );
	}

	return( false );
}



////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void TraceFactory::toStream(OutStream & os, ListOfTracePoint & listofTracePoint) const
{
	for( const auto & itTracePoint : listofTracePoint )
	{
		itTracePoint->toStream(os);
	}
}



} /* namespace sep */

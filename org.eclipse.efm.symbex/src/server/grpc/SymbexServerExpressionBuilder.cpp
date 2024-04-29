/*******************************************************************************
 * Copyright (c) 2020 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 mai 2020
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )

#include "SymbexServerExpressionBuilder.h"

#include<fml/builtin/Boolean.h>
#include<fml/builtin/Character.h>
#include<fml/builtin/Identifier.h>
#include<fml/builtin/QualifiedIdentifier.h>
#include<fml/builtin/String.h>

#include<fml/numeric/Float.h>
#include<fml/numeric/Integer.h>
#include<fml/numeric/Rational.h>

#include<fml/executable/AvmTransition.h>
#include<fml/executable/BaseInstanceForm.h>
#include<fml/executable/ExecutableQuery.h>
#include<fml/executable/InstanceOfBuffer.h>
#include<fml/executable/InstanceOfConnector.h>
#include<fml/executable/InstanceOfData.h>
#include<fml/executable/InstanceOfMachine.h>
#include<fml/executable/InstanceOfPort.h>

#include<fml/expression/AvmCode.h>
#include<fml/expression/ExpressionConstructor.h>

#include<fml/operator/OperatorManager.h>

#include<fml/runtime/ExecutionConfiguration.h>


namespace sep
{


::sep::grpc::OperatorKind
SymbexServerExpressionBuilder::to_grpc_op(AVM_OPCODE opcode)
{
	switch( opcode )
	{
		case AVM_OPCODE_PLUS:
		{
			return ::sep::grpc::OperatorKind::ADD;
		}

		case AVM_OPCODE_UMINUS:
		{
			return ::sep::grpc::OperatorKind::UMINUS;
		}

		case AVM_OPCODE_MINUS:
		{
			return ::sep::grpc::OperatorKind::MINUS;
		}

		case AVM_OPCODE_MULT:
		{
			return ::sep::grpc::OperatorKind::MULT;
		}

		case AVM_OPCODE_DIV:
		{
			return ::sep::grpc::OperatorKind::DIV;
		}

		case AVM_OPCODE_EQ:
		{
			return ::sep::grpc::OperatorKind::EQ;
		}
		case AVM_OPCODE_NEQ:
		{
			return ::sep::grpc::OperatorKind::NEQ;
		}
		case AVM_OPCODE_LT:
		{
			return ::sep::grpc::OperatorKind::LT;
		}
		case AVM_OPCODE_LTE:
		{
			return ::sep::grpc::OperatorKind::LTE;
		}
		case AVM_OPCODE_GT:
		{
			return ::sep::grpc::OperatorKind::GT;
		}
		case AVM_OPCODE_GTE:
		{
			return ::sep::grpc::OperatorKind::GTE;
		}
		case AVM_OPCODE_NOT:
		{
			return ::sep::grpc::OperatorKind::NOT;
		}
		case AVM_OPCODE_AND:
		{
			return ::sep::grpc::OperatorKind::AND;
		}
		case AVM_OPCODE_OR:
		{
			return ::sep::grpc::OperatorKind::OR;
		}


		case AVM_OPCODE_ASSIGN:
		case AVM_OPCODE_ASSIGN_AFTER:
		case AVM_OPCODE_ASSIGN_OP_AFTER:
		case AVM_OPCODE_ASSIGN_REF:
		case AVM_OPCODE_ASSIGN_MACRO:
		case AVM_OPCODE_ASSIGN_RESET:
		{
			return ::sep::grpc::OperatorKind::ASSIGN;
		}

		case AVM_OPCODE_ASSIGN_NEWFRESH:
		{
			return ::sep::grpc::OperatorKind::NEWFRESH;
		}

		case AVM_OPCODE_INPUT:
		{
			return ::sep::grpc::OperatorKind::INPUT;
		}
		case AVM_OPCODE_INPUT_ENV:
		{
			return ::sep::grpc::OperatorKind::INPUT_ENV;
		}
		case AVM_OPCODE_INPUT_RDV:
		case AVM_OPCODE_INPUT_MULTI_RDV:
		{
			return ::sep::grpc::OperatorKind::INPUT_RDV;
		}
		case AVM_OPCODE_INPUT_FROM:
		case AVM_OPCODE_INPUT_SAVE:
		case AVM_OPCODE_INPUT_VAR:
		case AVM_OPCODE_INPUT_FLOW:
		case AVM_OPCODE_INPUT_BUFFER:
		case AVM_OPCODE_INPUT_BROADCAST:
		case AVM_OPCODE_INPUT_DELEGATE:
		{
			return ::sep::grpc::OperatorKind::INPUT;
		}

		case AVM_OPCODE_OUTPUT:
		{
			return ::sep::grpc::OperatorKind::OUTPUT;
		}
		case AVM_OPCODE_OUTPUT_ENV:
		{
			return ::sep::grpc::OperatorKind::OUTPUT_ENV;
		}

		case AVM_OPCODE_OUTPUT_RDV:
		case AVM_OPCODE_OUTPUT_MULTI_RDV:
		{
			return ::sep::grpc::OperatorKind::OUTPUT_RDV;
		}
		case AVM_OPCODE_OUTPUT_TO:
		case AVM_OPCODE_OUTPUT_VAR:
		case AVM_OPCODE_OUTPUT_FLOW:
		case AVM_OPCODE_OUTPUT_BUFFER:
		case AVM_OPCODE_OUTPUT_BROADCAST:
		case AVM_OPCODE_OUTPUT_DELEGATE:
		{
			return ::sep::grpc::OperatorKind::OUTPUT;
		}


		case AVM_OPCODE_IENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_INVOKE:
		{
			return ::sep::grpc::OperatorKind::ENABLE;
		}

		case AVM_OPCODE_IDISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_CHILD:
		case AVM_OPCODE_DISABLE_SELF:
		case AVM_OPCODE_DISABLE_SELVES:
		{
			return ::sep::grpc::OperatorKind::DISABLE;
		}

		case AVM_OPCODE_IABORT_INVOKE:
		case AVM_OPCODE_ABORT_INVOKE:
		case AVM_OPCODE_ABORT_CHILD:
		case AVM_OPCODE_ABORT_SELF:
		case AVM_OPCODE_ABORT_SELVES:
		{
			return ::sep::grpc::OperatorKind::ABORT;
		}

		case AVM_OPCODE_INIT:
		{
			return ::sep::grpc::OperatorKind::INIT;
		}
		case AVM_OPCODE_FINAL:
		{
			return ::sep::grpc::OperatorKind::FINAL;
		}

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		{
			return ::sep::grpc::OperatorKind::START;
		}
		case AVM_OPCODE_STOP:
		{
			return ::sep::grpc::OperatorKind::STOP;
		}

		case AVM_OPCODE_RUN:
		{
			return ::sep::grpc::OperatorKind::RUN;
		}

		case AVM_OPCODE_RTC:
		{
			return ::sep::grpc::OperatorKind::RTC;
		}

		case AVM_OPCODE_SCHEDULE_INVOKE:
		{
			return ::sep::grpc::OperatorKind::SCHEDULE;
		}
		case AVM_OPCODE_DEFER_INVOKE:
		{
			return ::sep::grpc::OperatorKind::DEFER;
		}

		case AVM_OPCODE_INVOKE_TRANSITION:
		{
			return ::sep::grpc::OperatorKind::INVOKE_TRANSITION;
		}
		case AVM_OPCODE_INVOKE_ROUTINE:
		{
			return ::sep::grpc::OperatorKind::INVOKE_ROUTINE;
		}


		case AVM_OPCODE_SEQUENCE:
		case AVM_OPCODE_SEQUENCE_SIDE:
		case AVM_OPCODE_SEQUENCE_WEAK:
		{
			return ::sep::grpc::OperatorKind::SEQUENCE;
		}
		case AVM_OPCODE_PARALLEL:
		{
			return ::sep::grpc::OperatorKind::PARALLEL;
		}
		case AVM_OPCODE_INTERLEAVING:
		{
			return ::sep::grpc::OperatorKind::INTERLEAVING;
		}
		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		{
			return ::sep::grpc::OperatorKind::SYNCHRONOUS;
		}
		case AVM_OPCODE_PRIOR_GT:
		{
			return ::sep::grpc::OperatorKind::PRIOR_GT;
		}


		default:
		{
			AVM_OS_ERROR_ALERT
					<< "Unexpected AVM_OPCODE for GRPC<execution>\n"
					<< opcode
					<< std::endl;

			return ::sep::grpc::OperatorKind::UNKNOWN_OP;
		}
	}

}

static bool machine_id_to_grpc(::sep::grpc::Expression & grpc_expression,
		 const InstanceOfMachine & machine, const std::string & machine_id)
{
	::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
	symbol->set_id( machine_id );

	if( machine.getSpecifier().isFamilyComponentState() )
	{
		symbol->set_kind(::sep::grpc::STATE);
	}
	else if( machine.getSpecifier().isComponentStatemachine() )
	{
		symbol->set_kind(::sep::grpc::STATEMACHINE);
	}
	else if( machine.getSpecifier().isComponentSystem() )
	{
		symbol->set_kind(::sep::grpc::SYSTEM);
	}
	else
	{
		symbol->set_kind(::sep::grpc::MACHINE);
	}

	return true;
}

bool SymbexServerExpressionBuilder::to_grpc(
		::sep::grpc::Expression & grpc_expression,
		 avm_type_specifier_kind_t type_specifier_kind, const BF & expr)
{
	switch( expr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = expr.to< AvmCode >();

			::sep::grpc::OperatorKind operatorKind = to_grpc_op(aCode.getAvmOpCode());

			::sep::grpc::Operation * operation = grpc_expression.mutable_operation();
			operation->set_operatorkind(operatorKind);

			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not SymbexServerExpressionBuilder::to_grpc(
						(* (operation->add_operand())),
						type_specifier_kind, itOperand) )
				{
					return false;
				}
			}

			return true;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			const InstanceOfData & variable = expr.to< InstanceOfData >();

			::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
			symbol->set_id( variable.getLocationID() );

			if( variable.getModifier().hasNatureVariable() )
			{
				symbol->set_kind( ::sep::grpc::VARIABLE );
			}
			else if( variable.getModifier().hasNatureParameter() )
			{
				symbol->set_kind( ::sep::grpc::PARAMETER );
			}
			else
			{
				symbol->set_kind( ::sep::grpc::UNKNOWN_SYMBOL );
			}

			return true;
		}


		case FORM_BUILTIN_BOOLEAN_KIND:  // true <=> 1 ; false <=> 0
		{
			grpc_expression.set_raw_bool( expr.to< Boolean >().getValue() );

			return true;
		}

		case FORM_BUILTIN_INTEGER_KIND:
		{
			switch( type_specifier_kind )
			{
				case TYPE_POS_FLOAT_SPECIFIER:
				case TYPE_UFLOAT_SPECIFIER:
				case TYPE_FLOAT_SPECIFIER:
				case TYPE_POS_REAL_SPECIFIER:
				case TYPE_UREAL_SPECIFIER:
				case TYPE_REAL_SPECIFIER:
				{
					grpc_expression.set_raw_float( expr.to< Integer >().toFloat() );
					break;
				}
				default:
				{
					grpc_expression.set_raw_integer( expr.to< Integer >().toFloat() );
					break;
				}
			}

			return true;
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			if( expr.to< Rational >().isInteger() )
			{
				grpc_expression.set_raw_integer( expr.to< Rational >().toInteger() );
			}
			else
			{
				grpc_expression.set_raw_float( expr.to< Rational >().toFloat() );
			}

			return true;
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			switch( type_specifier_kind )
			{
				case TYPE_POS_INTEGER_SPECIFIER:
				case TYPE_UINTEGER_SPECIFIER:
				case TYPE_INTEGER_SPECIFIER:
				{
					if( expr.to< Float >().isInteger() )
					{
						grpc_expression.set_raw_integer( expr.to< Float >().toInteger() );
					}
					else
					{
						grpc_expression.set_raw_float( expr.to< Float >().toFloat() );
					}
					break;
				}
				default:
				{
					grpc_expression.set_raw_float( expr.to< Float >().toFloat() );
					break;
				}
			}


			return true;
		}


		case FORM_RUNTIME_ID_KIND:
		{
			std::string symbol_id = expr.bfRID().getFullyQualifiedNameID();

			std::string::size_type pos = symbol_id.rfind(':');
			if( pos != std::string::npos )
			{
				symbol_id = symbol_id.substr(pos + 1);
			}

			::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
			symbol->set_kind( ::sep::grpc::RUNTIME_ID );
			symbol->set_id( symbol_id );


			return true;
		}


		case FORM_BUILTIN_CHARACTER_KIND:
		{
			grpc_expression.set_raw_string( expr.to< Character >().str() );

			return true;
		}

		case FORM_BUILTIN_STRING_KIND:
		{
			grpc_expression.set_raw_string( expr.to< String >().str() );

			return true;
		}

		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			grpc_expression.set_raw_string( expr.to< QualifiedIdentifier >().str() );

			return true;
		}

		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			grpc_expression.set_raw_string( expr.to< Identifier >().str() );

			return true;
		}

		case FORM_OPERATOR_KIND:
		{
			grpc_expression.set_raw_string( expr.to< Operator >().str() );

			return true;
		}


		case FORM_INSTANCE_PORT_KIND:
		{
			::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
			symbol->set_kind( ::sep::grpc::PORT );
			symbol->set_id( expr.to< BaseInstanceForm >().getLocationID() );

			return true;
		}

		case FORM_INSTANCE_BUFFER_KIND:
		{
			::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
			symbol->set_kind( ::sep::grpc::BUFFER );
			symbol->set_id( expr.to< BaseInstanceForm >().getLocationID() );

			return true;
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
			const InstanceOfMachine & machine = expr.to< InstanceOfMachine >();

			return machine_id_to_grpc(grpc_expression, machine, machine.getLocationID());
		}

		case FORM_INSTANCE_CONNECTOR_KIND:
		{
			::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
			symbol->set_id( expr.to< BaseInstanceForm >().getLocationID() );

			switch( expr.to< InstanceOfPort >().getComPointNature() )
			{
				case IComPoint::IO_PORT_NATURE :
				{
					symbol->set_kind( ::sep::grpc::PORT );
					break;
				}

				case IComPoint::IO_CHANNEL_NATURE :
				{
					symbol->set_kind( ::sep::grpc::CHANNEL );
					break;
				}

				case IComPoint::IO_MESSAGE_NATURE :
				{
					symbol->set_kind( ::sep::grpc::MESSAGE );
					break;
				}

				case IComPoint::IO_SIGNAL_NATURE    :
				{
					symbol->set_kind( ::sep::grpc::SIGNAL );
					break;
				}

				case IComPoint::IO_UNDEFINED_NATURE :
				default:
				{
					symbol->set_kind( ::sep::grpc::PORT );
					break;
				}
			}

			return true;

		}

		case FORM_AVMTRANSITION_KIND:
		{
			::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
			symbol->set_kind( ::sep::grpc::TRANSITION );
			symbol->set_id( expr.to< AvmTransition >().getLocationID() );

			return true;

		}

		case FORM_EXECUTION_CONFIGURATION_KIND:
		{
			const ExecutionConfiguration & anExecConf =
					expr.to< ExecutionConfiguration >();

			if( anExecConf.isOperator() )
			{
				::sep::grpc::OperatorKind operatorKind =
						to_grpc_op(anExecConf.getOperator().getAvmOpCode());

				::sep::grpc::Operation * operation = grpc_expression.mutable_operation();
				operation->set_operatorkind(operatorKind);

				const RuntimeID & aRID = anExecConf.getRuntimeID();
				machine_id_to_grpc(*(operation->add_operand()),
						*(aRID.getInstance()), aRID.getFullyQualifiedNameID());

			}
			else if( anExecConf.isTransition() )
			{
				::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
				symbol->set_kind( ::sep::grpc::TRANSITION );
				symbol->set_id( anExecConf.toTransition().getLocationID() );
			}
			else if( anExecConf.isWeakProgram() )
			{
				::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
				symbol->set_kind( ::sep::grpc::PROGRAM );
				symbol->set_id( anExecConf.toProgram().getLocationID() );
			}
			else if( anExecConf.isAvmCode() )
			{
				to_grpc(grpc_expression, type_specifier_kind, anExecConf.getAvmCode());
			}
			else
			{
				::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
				symbol->set_kind( ::sep::grpc::UNKNOWN_SYMBOL );
				symbol->set_id( anExecConf.str() );
			}

			return true;
		}

		case FORM_ARRAY_BOOLEAN_KIND:
		case FORM_ARRAY_CHARACTER_KIND:
		case FORM_ARRAY_INTEGER_KIND:
		case FORM_ARRAY_RATIONAL_KIND:
		case FORM_ARRAY_FLOAT_KIND:
		case FORM_ARRAY_STRING_KIND:
		{
			::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
			symbol->set_kind( ::sep::grpc::ARRAY );
			symbol->set_id( expr.str() );

			return true;
		}

		case FORM_ARRAY_IDENTIFIER_KIND:
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:

		case FORM_ARRAY_BF_KIND:
		{
			::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
			symbol->set_kind( ::sep::grpc::ARRAY );
			symbol->set_id( expr.str() );

			return true;
		}

		case FORM_CONTAINER_VECTOR_KIND:

		case FORM_CONTAINER_REVERSE_VECTOR_KIND:
		case FORM_CONTAINER_LIST_KIND:
		case FORM_CONTAINER_SET_KIND:
		case FORM_CONTAINER_BAG_KIND:
		case FORM_CONTAINER_FIFO_KIND:
		case FORM_CONTAINER_LIFO_KIND:
		{
			::sep::grpc::Symbol * symbol = grpc_expression.mutable_symbol();
			symbol->set_kind( ::sep::grpc::COLLECTION );
			symbol->set_id( expr.str() );

			return true;
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "SymbexServerExpressionBuilder::to_grpc:> "
							"Unexpected KIND of expression << "
					<< expr.str() << " >> !!!"
					<< SEND_EXIT;

			return false;
		}
	}
}


BF SymbexServerExpressionBuilder::from_grpc(const ExecutableQuery & XQuery,
		const ExecutionContext & anEC, const::sep::grpc::Expression & expr)
{
	switch( expr.expression_alt_case() )
	{
		case ::sep::grpc::Expression::kSymbol:
		{
			const ::sep::grpc::Symbol & symbol = expr.symbol();

			switch( symbol.kind() )
			{
				case ::sep::grpc::VARIABLE:
				{
					return XQuery.getVariableByQualifiedNameID( symbol.id() );
				}
				case ::sep::grpc::PARAMETER:
				{
					return anEC.getExecutionData().getParametersRuntimeForm()
							.getParameters().getByQualifiedNameID( symbol.id() );
				}

				case ::sep::grpc::PORT:
				{
					return XQuery.getPortByQualifiedNameID( symbol.id() );
				}
				case ::sep::grpc::SIGNAL:
				{
					return XQuery.getPortByQualifiedNameID( symbol.id() );
				}
				case ::sep::grpc::MESSAGE:
				{
					return XQuery.getPortByQualifiedNameID( symbol.id() );
				}
				case ::sep::grpc::BUFFER:
				{
					return XQuery.getBufferByQualifiedNameID( symbol.id() );
				}
				case ::sep::grpc::CONNECTOR:
				{
					return XQuery.getVariableByQualifiedNameID( symbol.id() );
				}
				case ::sep::grpc::CHANNEL:
				{
					return XQuery.getPortByQualifiedNameID( symbol.id() );
				}
				case ::sep::grpc::MACHINE:
				{
					return XQuery.getMachineByQualifiedNameID(
							Specifier::DESIGN_INSTANCE_KIND, symbol.id() );
				}
				case ::sep::grpc::SYSTEM:
				{
					return XQuery.getMachineByQualifiedNameID(
							Specifier::DESIGN_INSTANCE_KIND, symbol.id() );
				}
				case ::sep::grpc::STATEMACHINE:
				{
					return XQuery.getMachineByQualifiedNameID(
							Specifier::DESIGN_INSTANCE_KIND, symbol.id() );
				}
				case ::sep::grpc::STATE:
				{
					return XQuery.getMachineByQualifiedNameID(
							Specifier::DESIGN_INSTANCE_KIND, symbol.id() );
				}
				case ::sep::grpc::TRANSITION:
				{
					return XQuery.getTransitionByQualifiedNameID( symbol.id() );
				}
				case ::sep::grpc::OPERATOR:
				case ::sep::grpc::ARRAY:
				case ::sep::grpc::LIST:
				case ::sep::grpc::COLLECTION:
				default:
				{
					return anEC.getExecutionData().getParametersRuntimeForm()
							.getParameters().getByQualifiedNameID( symbol.id() );
				}
			}
		}
		case ::sep::grpc::Expression::kOperation:
			return SymbexServerExpressionBuilder::
					from_grpc(XQuery, anEC, expr.operation());

		case ::sep::grpc::Expression::kRawBool:
			return ExpressionConstructor::newBoolean(expr.raw_bool());

		case ::sep::grpc::Expression::kRawInteger:
			return ExpressionConstructor::newInteger(expr.raw_integer());

		case ::sep::grpc::Expression::kRawFloat:
			return ExpressionConstructor::newFloat(expr.raw_float());

		case ::sep::grpc::Expression::kRawString:
			return ExpressionConstructor::newString(expr.raw_string());

		case ::sep::grpc::Expression::EXPRESSION_ALT_NOT_SET: {
			break;
		}
	}

	return BF::REF_NULL;
}


BF SymbexServerExpressionBuilder::from_grpc(const ExecutableQuery & XQuery,
		const ExecutionContext & anEC, const ::sep::grpc::Operation & operation)
{
	AvmCode::OperandCollectionT operands;

	for( const auto & grpc_arg : operation.operand() )
	{
		BF arg = SymbexServerExpressionBuilder::from_grpc(XQuery, anEC, grpc_arg);

		if( arg.valid() )
		{
			operands.append( arg );
		}
		else
		{
			return BF::REF_NULL;
		}
	}

	switch( operation.operatorkind() )
	{
		case ::sep::grpc::OperatorKind::ADD:
			return ExpressionConstructor::addExpr(operands);

		case ::sep::grpc::OperatorKind::MINUS:
			return ExpressionConstructor::minusExpr(operands);

		case ::sep::grpc::OperatorKind::UMINUS:
			return ExpressionConstructor::uminusExpr(operands.first());

		case ::sep::grpc::OperatorKind::MULT:
			return ExpressionConstructor::multExpr(operands);

		case ::sep::grpc::OperatorKind::DIV:
			return ExpressionConstructor::divExpr(
					operands.first(), operands.second());


		case ::sep::grpc::OperatorKind::OR:
			return ExpressionConstructor::orExpr(operands);

		case ::sep::grpc::OperatorKind::AND:
			return ExpressionConstructor::andExpr(operands);

		case ::sep::grpc::OperatorKind::NOT:
			return ExpressionConstructor::notExpr(operands.first());


		case ::sep::grpc::OperatorKind::EQ:
			return ExpressionConstructor::eqExpr(
					operands.first(), operands.second());

		case ::sep::grpc::OperatorKind::NEQ:
			return ExpressionConstructor::neqExpr(
					operands.first(), operands.second());

		case ::sep::grpc::OperatorKind::GT:
			return ExpressionConstructor::gtExpr(
					operands.first(), operands.second());

		case ::sep::grpc::OperatorKind::GTE:
			return ExpressionConstructor::gteExpr(
					operands.first(), operands.second());

		case ::sep::grpc::OperatorKind::LT:
			return ExpressionConstructor::ltExpr(
					operands.first(), operands.second());

		case ::sep::grpc::OperatorKind::LTE:
			return ExpressionConstructor::lteExpr(
					operands.first(), operands.second());

		case ::sep::grpc::OperatorKind::NEWFRESH:
			return ExpressionConstructor::newCode(
					OperatorManager::OPERATOR_ASSIGN_NEWFRESH, operands.first());

		case ::sep::grpc::OperatorKind::NOP:
		default:
			return ExpressionConstructor::newCode(OperatorManager::OPERATOR_NOP);
	}

	return BF::REF_NULL;
}



} /* namespace sep */

#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */

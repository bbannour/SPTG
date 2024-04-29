/*******************************************************************************
 * Copyright (c) 2020 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 avr. 2020
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/
#if defined(_EXPERIMENTAL_SERVER_GRPC_FEATURE_)

#ifdef __AVM_MINGW__

#include <grpcpp/grpcpp.h>
#include <grpcpp/health_check_service_interface.h>
#include <grpcpp/ext/proto_server_reflection_plugin.h>

#else //#ifdef __AVM_LINUX__

#include <grpc++/grpc++.h>
#include <grpc++/health_check_service_interface.h>
#include <grpc++/ext/proto_server_reflection_plugin.h>

#endif
#include <server/grpc/SymbexServer.h>
#include <server/grpc/SymbexServerWorkflowUtils.h>
#include <server/grpc/SymbexServerHelper.h>
#include <server/grpc/SymbexServerExpressionBuilder.h>
#include <sew/SymbexEngine.h>

#include <fml/runtime/RuntimeForm.h>

namespace sep
{
	namespace grpc
	{

		// Symbex Query Variable Value
		::grpc::Status SymbexServiceImpl::queryValueofVariable(
			::grpc::ServerContext *context,
			const QueryValueForVariableRequest *request,
			QueryValueForVariableReply *response)
		{
			::grpc::Status checkStatus = checkPrecondition();
			if (not checkStatus.ok())
				return checkStatus;

			// EVAL COMMAND CODE
			std::uint32_t execution_context_id = request->execution_context_id();

			ExecutionContext *foundEC = SymbexServerHelper::searchContext(
				mSymbexEngine->getConfiguration().getExecutionTrace(),
				execution_context_id);

			if (foundEC == nullptr)
			{
				return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
									  "NOT_FOUND: The Execution Context with ID< " + std::to_string(execution_context_id) + " > doesn't exist !");
			}

			response->set_execution_context_id(execution_context_id);

			std::size_t var_index = AVM_NUMERIC_MAX_SIZE_T;
			//special case : empty variable id ==> return all variable values
			if (request->variable_id_size() == 0)
			{
				//for all runtime of the TableOFRuntime
				for (const auto &itRF : foundEC->getExecutionData().getTableOfRuntime())
				{
					//for all variable du executable form
					for (const auto &itVar : itRF->refExecutable().getAllVariables())
					{
						VariableValuePair *variable_value = response->add_variable_value();
						Expression *grpc_expr = variable_value->mutable_value();
						//retrive the id
						InstanceOfData *varInstance = itVar.to_ptr<InstanceOfData>();
						std::string var_id;
						var_id = (*varInstance).getFullyQualifiedNameID();
						variable_value->set_variable_id(var_id);
						BF value = itRF->getDataTable()->get(varInstance);
						if ((varInstance != nullptr) && value.valid())
							if (var_index < AVM_NUMERIC_MAX_SIZE_T)
							{
								if (value.is<BuiltinVector>())
								{
									if (var_index < value.to<BuiltinVector>().size())
									{
										value = value.to<BuiltinVector>().get(var_index);
									}
									else
									{
										return ::grpc::Status(::grpc::StatusCode::INVALID_ARGUMENT,
															  "Out of range access in a BuiltinVector < size: " + std::to_string(value.to<BuiltinVector>().size()) + " value: " + value.str() + " > for the variabe_id< " + var_id + " > access with index< " + std::to_string(var_index) + " > !");
									}
								}
								else
								{
									return ::grpc::Status(::grpc::StatusCode::ABORTED,
														  "Expected a BuiltinVector value< " + value.str() + " > for the variabe_id< " + var_id + " > access with index< " + std::to_string(var_index) + " > !");
								}
							}
						//transform as a grpc expression
						if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
																	   varInstance->getTypeSpecifierKind(), value))
						{
							return ::grpc::Status(::grpc::StatusCode::ABORTED,
												  "Failed to encode in grpc::Expression the value < " + value.str() + " > for the variabe_id< " + var_id + " > !");
						}
					}
				}
			}
			else
			{
				for (std::string var_id : request->variable_id())
				{
					VariableValuePair *variable_value = response->add_variable_value();
					variable_value->set_variable_id(var_id);
					var_index = AVM_NUMERIC_MAX_SIZE_T;

					//removal of  '[]'?
					std::string index;
					std::string::size_type pos_1 = var_id.rfind('[');
					if (pos_1 != std::string::npos)
					{
						std::string::size_type pos_2 = var_id.rfind(']');
						var_index = std::stoi(var_id.substr(pos_1 + 1, pos_2 - pos_1 - 1));
						var_id = var_id.substr(0, pos_1);
					}

					Expression *grpc_expr = variable_value->mutable_value();
					InstanceOfData *varInstance = nullptr;
					//retrieve tha data value
					BF value = foundEC->getExecutionData()
								   .getDataByQualifiedNameID(var_id, varInstance);
					if ((varInstance != nullptr) && value.valid())
					{
						if (var_index < AVM_NUMERIC_MAX_SIZE_T)
						{
							if (value.is<BuiltinVector>())
							{
								if (var_index < value.to<BuiltinVector>().size())
								{
									value = value.to<BuiltinVector>().get(var_index);
								}
								else
								{
									return ::grpc::Status(::grpc::StatusCode::INVALID_ARGUMENT,
														  "Out of range access in a BuiltinVector < size: " + std::to_string(value.to<BuiltinVector>().size()) + " value: " + value.str() + " > for the variabe_id< " + var_id + " > access with index< " + std::to_string(var_index) + " > !");
								}
							}
							else
							{
								return ::grpc::Status(::grpc::StatusCode::ABORTED,
													  "Expected a BuiltinVector value< " + value.str() + " > for the variabe_id< " + var_id + " > access with index< " + std::to_string(var_index) + " > !");
							}
						}
						//transform as a grpc expression
						if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
																	   varInstance->getTypeSpecifierKind(), value))
						{
							return ::grpc::Status(::grpc::StatusCode::ABORTED,
												  "Failed to encode in grpc::Expression the value < " + value.str() + " > for the variabe_id< " + var_id + " > !");
						}

						AVM_OS_DEBUG << variable_value->DebugString() << std::endl;
					}
					else
					{
						return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
											  "NOT_FOUND: The value for the variabe_id< " + var_id + " > doesn't exist !");
					}
				}
			}
			return ::grpc::Status::OK;
		}

		// Symbex Query Trace for Node Condition
		::grpc::Status SymbexServiceImpl::queryNodeCondition(
			::grpc::ServerContext *context,
			const QueryValueForVariableRequest *request,
			QueryValueForVariableReply *response)
		{
			::grpc::Status checkStatus = checkPrecondition();
			if (not checkStatus.ok())
				return checkStatus;

			// EVAL COMMAND CODE
			std::uint32_t execution_context_id = request->execution_context_id();

			AVM_OS_DEBUG << "\n\nServer.queryNodeCondition {" << std::endl
						 << request->DebugString()
						 << "\texecution_context_id : " << execution_context_id << std::endl
						 << "\tvariable {" << std::endl;
			for (const auto &var_id : request->variable_id())
			{
				AVM_OS_DEBUG << "\t\tvariable_id: " << var_id << std::endl;
			}
			AVM_OS_DEBUG << "\t}" << std::endl
						 << "}" << std::endl;

			ExecutionContext *foundEC = SymbexServerHelper::searchContext(
				mSymbexEngine->getConfiguration().getExecutionTrace(),
				execution_context_id);

			if (foundEC == nullptr)
			{
				return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
									  "NOT_FOUND: The Execution Context with ID< " + std::to_string(execution_context_id) + " > doesn't exist !");
			}

			response->set_execution_context_id(execution_context_id);

			VariableValuePair *variable_value = response->add_variable_value();

			variable_value->set_variable_id("$node_condition");

			Expression *grpc_expr = variable_value->mutable_value();

			if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
														   TYPE_BOOLEAN_SPECIFIER,
														   foundEC->getExecutionData().getNodeCondition()))
			{
				return ::grpc::Status(::grpc::StatusCode::ABORTED,
									  "Failed to encode in grpc::Expression the value < " + foundEC->getExecutionData().getNodeCondition().str() + " > for the $node_condition !");
			}
			AVM_OS_DEBUG << variable_value->DebugString() << std::endl;

			variable_value = response->add_variable_value();

			variable_value->set_variable_id("$node_time_condition");

			grpc_expr = variable_value->mutable_value();

			if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
														   TYPE_BOOLEAN_SPECIFIER,
														   foundEC->getExecutionData().getNodeTimedCondition()))
			{
				return ::grpc::Status(::grpc::StatusCode::ABORTED,
									  "Failed to encode in grpc::Expression the value < " + foundEC->getExecutionData().getNodeTimedCondition().str() + " > for the $node_time_condition !");
			}
			AVM_OS_DEBUG << variable_value->DebugString() << std::endl;

			return ::grpc::Status::OK;
		}

		// Symbex Query Trace for Path Condition
		::grpc::Status SymbexServiceImpl::queryPathCondition(
			::grpc::ServerContext *context,
			const QueryValueForVariableRequest *request,
			QueryValueForVariableReply *response)
		{
			// CHECK PRECONDITION FOR << modelEval >> command
			::grpc::Status checkStatus = checkPrecondition();
			if (not checkStatus.ok())
				return checkStatus;

			// EVAL COMMAND CODE
			std::uint32_t execution_context_id = request->execution_context_id();

			AVM_OS_DEBUG << "\n\nServer.queryPathCondition {" << std::endl
						 << request->DebugString()
						 << "\texecution_context_id : " << execution_context_id << std::endl
						 << "\tvariable {" << std::endl;
			for (const auto &var_id : request->variable_id())
			{
				AVM_OS_DEBUG << "\t\tvariable_id: " << var_id << std::endl;
			}
			AVM_OS_DEBUG << "\t}" << std::endl
						 << "}" << std::endl;

			ExecutionContext *foundEC = SymbexServerHelper::searchContext(
				mSymbexEngine->getConfiguration().getExecutionTrace(),
				execution_context_id);

			if (foundEC == nullptr)
			{
				return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
									  "NOT_FOUND: The Execution Context with ID< " + std::to_string(execution_context_id) + " > doesn't exist !");
			}

			response->set_execution_context_id(execution_context_id);

			VariableValuePair *variable_value = response->add_variable_value();

			variable_value->set_variable_id("$path_condition");

			Expression *grpc_expr = variable_value->mutable_value();

			if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
														   TYPE_BOOLEAN_SPECIFIER,
														   foundEC->getExecutionData().getPathCondition()))
			{
				return ::grpc::Status(::grpc::StatusCode::ABORTED,
									  "Failed to encode in grpc::Expression the value < " + foundEC->getExecutionData().getPathCondition().str() + " > for the $path_condition !");
			}
			AVM_OS_DEBUG << variable_value->DebugString() << std::endl;

			variable_value = response->add_variable_value();

			variable_value->set_variable_id("$path_time_condition");

			grpc_expr = variable_value->mutable_value();

			if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
														   TYPE_BOOLEAN_SPECIFIER,
														   foundEC->getExecutionData().getPathTimedCondition()))
			{
				return ::grpc::Status(::grpc::StatusCode::ABORTED,
									  "Failed to encode in grpc::Expression the value < " + foundEC->getExecutionData().getPathTimedCondition().str() + " > for the $path_time_condition !");
			}
			AVM_OS_DEBUG << variable_value->DebugString() << std::endl;

			return ::grpc::Status::OK;
		}

		// Symbex Query Trace for IO élement (input / output / newfresh)
		::grpc::Status SymbexServiceImpl::queryTraceIO(
			::grpc::ServerContext *context,
			const QueryValueForVariableRequest *request,
			QueryValueForVariableReply *response)
		{
			// CHECK PRECONDITION FOR << modelEval >> command
			::grpc::Status checkStatus = checkPrecondition();
			if (not checkStatus.ok())
				return checkStatus;

			// EVAL COMMAND CODE
			std::uint32_t execution_context_id = request->execution_context_id();

			AVM_OS_DEBUG << "\n\nServer.queryTraceIO {" << std::endl
						 << request->DebugString()
						 << "\texecution_context_id : " << execution_context_id << std::endl
						 << "\tvariable {" << std::endl;
			for (const auto &var_id : request->variable_id())
			{
				AVM_OS_DEBUG << "\t\tvariable_id: " << var_id << std::endl;
			}
			AVM_OS_DEBUG << "\t}" << std::endl
						 << "}" << std::endl;

			ExecutionContext *foundEC = SymbexServerHelper::searchContext(
				mSymbexEngine->getConfiguration().getExecutionTrace(),
				execution_context_id);

			if (foundEC == nullptr)
			{
				return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
									  "NOT_FOUND: The Execution Context with ID< " + std::to_string(execution_context_id) + " > doesn't exist !");
			}

			response->set_execution_context_id(execution_context_id);

			VariableValuePair *variable_value = response->add_variable_value();

			variable_value->set_variable_id("$io_trace");

			Expression *grpc_expr = variable_value->mutable_value();

			if (foundEC->getExecutionData().hasIOElementTrace())
			{
				if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
															   TYPE_BOOLEAN_SPECIFIER,
															   foundEC->getExecutionData().getIOElementTrace()))
				{
					return ::grpc::Status(::grpc::StatusCode::ABORTED,
										  "Failed to encode in grpc::Expression the value < " + foundEC->getExecutionData().getIOElementTrace().str() + " > for the $io_trace !");
				}
			}
			else
			{
//				grpc_expr->set_raw_string("$io_trace");
			}
			AVM_OS_DEBUG << variable_value->DebugString() << std::endl;

			return ::grpc::Status::OK;
		}

		// Symbex Query Trace for Executable element (machine / statemachine / state / transition)
		::grpc::Status SymbexServiceImpl::queryTraceExecutable(
			::grpc::ServerContext *context,
			const QueryValueForVariableRequest *request,
			QueryValueForVariableReply *response)
		{
			// CHECK PRECONDITION FOR << modelEval >> command
			::grpc::Status checkStatus = checkPrecondition();
			if (not checkStatus.ok())
				return checkStatus;

			// EVAL COMMAND CODE
			std::uint32_t execution_context_id = request->execution_context_id();

			AVM_OS_DEBUG << "\n\nServer.queryTraceExecutable {" << std::endl
						 << request->DebugString()
						 << "\texecution_context_id : " << execution_context_id << std::endl
						 << "\tvariable {" << std::endl;
			for (const auto &var_id : request->variable_id())
			{
				AVM_OS_DEBUG << "\t\tvariable_id: " << var_id << std::endl;
			}
			AVM_OS_DEBUG << "\t}" << std::endl
						 << "}" << std::endl;

			ExecutionContext *foundEC = SymbexServerHelper::searchContext(
				mSymbexEngine->getConfiguration().getExecutionTrace(),
				execution_context_id);

			if (foundEC == nullptr)
			{
				return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
									  "NOT_FOUND: The Execution Context with ID< " + std::to_string(execution_context_id) + " > doesn't exist !");
			}

			response->set_execution_context_id(execution_context_id);

			VariableValuePair *variable_value = response->add_variable_value();

			variable_value->set_variable_id("$runnable_trace");

			Expression *grpc_expr = variable_value->mutable_value();

			if (foundEC->getExecutionData().hasRunnableElementTrace())
			{
				if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
															   TYPE_NULL_SPECIFIER,
															   foundEC->getExecutionData().getRunnableElementTrace()))
				{
					return ::grpc::Status(::grpc::StatusCode::ABORTED,
										  "Failed to encode in grpc::Expression the value < " + foundEC->getExecutionData().getRunnableElementTrace().str() + " > for the $runnable_trace !");
				}
			}
			else
			{
				grpc_expr->set_raw_string("$runnable_trace");
			}
			AVM_OS_DEBUG << variable_value->DebugString() << std::endl;

			return ::grpc::Status::OK;
		}

		::grpc::Status SymbexServiceImpl::queryEC(::grpc::ServerContext *context,
												  const ECQuery *request, GRPCExecutionContext *response)
		{
			// CHECK PRECONDITION FOR << queryEC >> command
			::grpc::Status checkStatus = checkPrecondition();
			if (not checkStatus.ok())
				return checkStatus;

			//Retrieve the context id 
			std::uint32_t execution_context_id = request->execution_context_id();
			ExecutionContext *foundEC = SymbexServerHelper::searchContext(
				mSymbexEngine->getConfiguration().getExecutionTrace(),
				execution_context_id);
			if (foundEC == nullptr)
			{
				return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
									  "NOT_FOUND: The Execution Context with ID< " + std::to_string(execution_context_id) + " > doesn't exist !");
			}
			response->set_execution_context_id(execution_context_id);

			//add variables values of all variables
//			std::size_t var_index = AVM_NUMERIC_MAX_SIZE_T;
			for (const auto &itRF : foundEC->getExecutionData().getTableOfRuntime())
			{
				//for all variable du executable form
				for (const auto &itVar : itRF->refExecutable().getAllVariables())
				{
					VariableValuePair *variable_value = response->add_variable_value();
					Expression *grpc_expr = variable_value->mutable_value();
					//retrive the id
					InstanceOfData *varInstance = itVar.to_ptr<InstanceOfData>();
					std::string var_id;
					var_id = (*varInstance).getFullyQualifiedNameID();
					variable_value->set_variable_id(var_id);
					BF value = itRF->getDataTable()->get(varInstance);
					//transform as a grpc expression
					if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
																   varInstance->getTypeSpecifierKind(), value))
					{
						return ::grpc::Status(::grpc::StatusCode::ABORTED,
											  "Failed to encode in grpc::Expression the value < " + value.str() + " > for the variabe_id< " + var_id + " > !");
					}
				}
			}
			//add children to the response
			ListOfExecutionContext childECs = foundEC->getChildContexts();
			for (const auto &childEC : childECs)
			{
				response->add_children(childEC->getIdNumber());
			}
			//TODO add runtime status tree 
			response->set_allocated_runtime_status(SymbexServerHelper::runtimeStatusTree(foundEC));
			//foundEC->getExecutionData().getRuntimeFormStateTable()

			if (foundEC->getExecutionData().hasRunnableElementTrace())
			{
//				response->set_trace_executable(foundEC->getExecutionData().getRunnableElementTrace().str());
				Expression *grpc_expr = response->mutable_trace_executable();
				if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
															   TYPE_NULL_SPECIFIER,
															   foundEC->getExecutionData().getRunnableElementTrace()))
				{
					return ::grpc::Status(::grpc::StatusCode::ABORTED,
										  "Failed to encode in grpc::Expression the value < " + foundEC->getExecutionData().getRunnableElementTrace().str() + " > for the $runnable_trace !");
				}
			}


			//TODO add IO Trace
			if (foundEC->getExecutionData().hasIOElementTrace())
			{
//				response->set_trace_io(foundEC->getExecutionData().getIOElementTrace().str());
				Expression *grpc_expr = response->mutable_trace_io();
				if (not SymbexServerExpressionBuilder::to_grpc(*grpc_expr,
															   TYPE_BOOLEAN_SPECIFIER,
															   foundEC->getExecutionData().getIOElementTrace()))
				{
					return ::grpc::Status(::grpc::StatusCode::ABORTED,
										  "Failed to encode in grpc::Expression the value < " + foundEC->getExecutionData().getIOElementTrace().str() + " > for the $io_trace !");
				}
			}
			response->set_is_eval(foundEC->isEvaluated());
			return ::grpc::Status::OK;
		}

	} /* namespace grpc */
} /* namespace sep */

#endif // _EXPERIMENTAL_SERVER_GRPC_FEATURE_

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

#include "SymbexServer.h"

#include <iostream>
#include <memory>
#include <string>

#ifdef __AVM_MINGW__

#include <grpcpp/grpcpp.h>
#include <grpcpp/health_check_service_interface.h>
#include <grpcpp/ext/proto_server_reflection_plugin.h>

#else //#ifdef __AVM_LINUX__

#include <grpc++/grpc++.h>
#include <grpc++/health_check_service_interface.h>
#include <grpc++/ext/proto_server_reflection_plugin.h>

#endif

#include <computer/ExecutionEnvironment.h>

#include <famcore/api/MainProcessorUnit.h>
#include <famcore/debug/IDebugProcessorHelper.h>

#include <fml/expression/BuiltinContainer.h>
#include <fml/runtime/ExecutionContext.h>

#include <main/AvmLauncher.h>

#include <printer/OutStream.h>

#include <sew/SymbexDispatcher.h>
#include <sew/SymbexControllerUnitManager.h>
#include <sew/SymbexEngine.h>
#include <sew/Workflow.h>
#include <sew/WorkflowParameter.h>

#include <server/grpc/SymbexServerExpressionBuilder.h>
#include <server/grpc/SymbexServerHelper.h>
#include <server/grpc/SymbexServerWorkflowUtils.h>

#include <util/avm_vfs.h>

//#include <chrono>
//#include <thread>

namespace sep
{
	namespace grpc
	{

		/**
 * CONSTRUCTOR
 * Default
 */
		SymbexServiceImpl::SymbexServiceImpl()
			: mSymbexServer(nullptr),
			  mWorkflowParameter(AvmLauncher::SYMBEX_BUILD_ID),
			  mWorkflow(nullptr),
			  mSymbexEngine(nullptr),
			  exec_cmd_flag(0)
		{
			//!! NOTHING
		}

		/**
 * UTILS
 */
		::grpc::Status SymbexServiceImpl::resetServer()
		{
			ExecutionContextHeader::ID_NUMBER = 0;

			//	return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
			//			"Fail to reset the server");

			return ::grpc::Status::OK;
		}

		::grpc::Status SymbexServiceImpl::checkPrecondition(){
			if (exec_cmd_flag < EXECUTED_SYMBEX_EVAL_INIT_FLAG)
			{
				::grpc::Status resetStatus = resetServer();
				if (not resetStatus.ok())
				{
					return resetStatus;
				}

				return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
									  "Use symbexEvalInit before !");
			}
			return ::grpc::Status::OK;
		}

		// Diversity Initialization
		::grpc::Status SymbexServiceImpl::initialization(
			::grpc::ServerContext *context,
			const InitializationRequest *request,
			InitializationReply *response)
		{
			// CHECK PRECONDITION FOR << initialization >> command
			if (exec_cmd_flag > EXECUTED_INITIALIZATION_FLAG)
			{
				::grpc::Status resetStatus = resetServer();
				if (not resetStatus.ok())
				{
					return resetStatus;
				}
			}
			else if (exec_cmd_flag == EXECUTED_INITIALIZATION_FLAG)
			{
				//!! NOTHING TO DO
			}

			// SET POST_CONDITION
			exec_cmd_flag = EXECUTED_INITIALIZATION_FLAG;

			AVM_OS_DEBUG << "\n\nServer.initialization { " << std::endl
						 << request->DebugString()
						 << "\tsession_id = " << request->session_id() << std::endl
						 << "}" << std::endl;

			// EVAL COMMAND CODE
			response->set_message("Symbex Server is Ready ;-)");

			return ::grpc::Status::OK;
		}

		// Symbex Evaluation of a Transition (by a string FQN_ID) on a Context
		::grpc::Status SymbexServiceImpl::runPostProcessor(
			::grpc::ServerContext *context,
			const PostProcessingRequest *request,
			PostProcessingReply *response)
		{
			// CHECK PRECONDITION FOR << modelEval >> command
			if (exec_cmd_flag < EXECUTED_MODEL_PARSE_FLAG)
			{
				::grpc::Status resetStatus = resetServer();
				if (not resetStatus.ok())
				{
					return resetStatus;
				}

				return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
									  "rpc symbexEvalStep:> Use symbexEvalInit before !");
			}
			else if (exec_cmd_flag == EXECUTED_SYMBEX_EVAL_INIT_FLAG)
			{
				//!! NOTHING TO DO
			}

			// EVAL COMMAND CODE
			AVM_OS_DEBUG << "\n\nServer.runPostProcessor {" << std::endl
						 << request->DebugString()
						 << "\tenable_execution_graph : " << request->enable_execution_graph() << std::endl
						 << "}" << std::endl;

			mSymbexEngine->runPostProcessor();

			return ::grpc::Status::OK;
		}

		////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////
		// FOR TEST : HELLO WORD

		//::grpc::Status SymbexServiceImpl::sayHello(::grpc::ServerContext * context,
		//		const HelloRequest * request, HelloReply * response)
		//{
		//	using namespace std::chrono_literals;
		//	AVM_OS_DEBUG << "SayHello waiter" << std::endl;
		//	auto start = std::chrono::high_resolution_clock::now();
		//	std::this_thread::sleep_for(2s);
		//	auto end = std::chrono::high_resolution_clock::now();
		//	std::chrono::duration<double, std::milli> elapsed = end-start;
		//	AVM_OS_DEBUG << "Waited " << elapsed.count() << " ms" << std::endl;;
		//
		//	std::string prefix("BONJOUR ");
		//	response->set_message(prefix + request->name());
		//
		//	return ::grpc::Status::OK;
		//}
		//
		//::grpc::Status SymbexServiceImpl::sayHelloAgain(::grpc::ServerContext * context,
		//		const HelloRequest * request, HelloReply * response)
		//{
		//	std::string prefix("Hello again ");
		//	response->set_message(prefix + request->name());
		//	return ::grpc::Status::OK;
		//}
		//
		//::grpc::Status SymbexServiceImpl::stopServer(::grpc::ServerContext * context,
		//		const ::google::protobuf::Empty * request, HelloReply * response)
		//{
		//	response->set_message("StopServer : Bye !");
		//
		//	// Shutdown();
		//
		//	return ::grpc::Status::OK;
		//}

		void SymbexServer::start()
		{
			//std::string server_address("0.0.0.0:" + _AVM_EXEC_SERVER_PORT_NUMBER_);
			//	std::string server_address("localhost:" + _AVM_EXEC_SERVER_PORT_NUMBER_);
			std::string server_address(_AVM_EXEC_SERVER_HOST_ADDRESS_ + ":" + _AVM_EXEC_SERVER_PORT_NUMBER_);
			SymbexServiceImpl service;

			::grpc::EnableDefaultHealthCheckService(true);
			::grpc::reflection::InitProtoReflectionServerBuilderPlugin();
			::grpc::ServerBuilder builder;
			// Listen on the given address without any authentication mechanism.
			builder.AddListeningPort(server_address, ::grpc::InsecureServerCredentials());
			// Register "service" as the instance through which we'll communicate with
			// clients. In this case it corresponds to an *synchronous* service.
			builder.RegisterService(&service);
			// Finally assemble the server.
			std::unique_ptr<::grpc::Server> server(builder.BuildAndStart());

			setServer(server.get());

			AVM_OS_DEBUG << "Symbex Server listening on " << server_address << std::endl;

			if (not VFS::WorkflowPath.empty())
			{
				AVM_OS_DEBUG << " ** With default Symbex Workflow :> " << VFS::WorkflowPath << std::endl;
			}

			// Wait for the server to shutdown. Note that some other thread must be
			// responsible for shutting down the server for this call to ever return.
			server->Wait();
		}

		void SymbexServer::shutdown()
		{
			mServer->Shutdown();
			// Always shutdown the completion queue after the server.
			// cq_->Shutdown();
			AVM_OS_DEBUG << "Server exiting ... " << std::endl;
		}

		void SymbexServer::runServer()
		{
			SymbexServer symbexServer;

			symbexServer.start();
		}

		// Symbex Evaluation of a Transition (by a string FQN_ID) on a Context
		::grpc::Status SymbexServiceImpl::queryChildContext(::grpc::ServerContext *context,
															const ECQuery *request,
															ECReply *response)
		{
			// CHECK PRECONDITION
			if (exec_cmd_flag < EXECUTED_SYMBEX_EVAL_INIT_FLAG)
			{
				::grpc::Status resetStatus = resetServer();
				if (not resetStatus.ok())
				{
					return resetStatus;
				}

				return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
									  "rpc queryChildContext:> Use symbexEvalInit before !");
			}
			//get the ec
			std::uint32_t execution_context_id = request->execution_context_id();
			ExecutionContext *foundEC = SymbexServerHelper::searchContext(
				mSymbexEngine->getConfiguration().getExecutionTrace(),
				execution_context_id);
			if (foundEC == nullptr)
			{
				return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
									  "NOT_FOUND: The Execution Context with ID< " + std::to_string(execution_context_id) + " > doesn't exist !");
			}
			//add children to the response
			ListOfExecutionContext childECs = foundEC->getChildContexts();
			for (const auto &childEC : childECs)
			{
				response->add_execution_context_id(childEC->getIdNumber());
			}
			return ::grpc::Status::OK;
		}

		::grpc::Status SymbexServiceImpl::queryRuntimesStatus(::grpc::ServerContext *context,
															  const ECQuery *request,
															  RuntimesStatusReply *response)
		{
			// CHECK PRECONDITION
			if (exec_cmd_flag < EXECUTED_SYMBEX_EVAL_INIT_FLAG)
			{
				::grpc::Status resetStatus = resetServer();
				if (not resetStatus.ok())
				{
					return resetStatus;
				}

				return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
									  "rpc queryRuntimesStatus:> Use symbexEvalInit before !");
			}
			//get the request ExecutionContext
			std::uint32_t execution_context_id = request->execution_context_id();
			ExecutionContext *foundEC = SymbexServerHelper::searchContext(
				mSymbexEngine->getConfiguration().getExecutionTrace(),
				execution_context_id);
			if (foundEC == nullptr)
			{
				return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
									  "NOT_FOUND: The Execution Context with ID< " + std::to_string(execution_context_id) + " > doesn't exist !");
			}
			//retrieve the table of runtime flag size
			std::size_t nb_of_runtime = foundEC->getExecutionData().getRuntimeFormStateTable()->size();
			std::size_t runtime_it;
			std::string runtimeID;
			PROCESS_EVAL_STATE runtimeState;
			for (runtime_it = 0; runtime_it < nb_of_runtime; runtime_it++)
			{
				//for all runtime
				//add its qualified name and flag to the response
				SingleRuntimeStatus *runtime_status = response->add_runtime_status();
				runtimeID = foundEC->getExecutionData().getRuntime(runtime_it).getFullyQualifiedNameID();				
				runtime_status->set_runtime_id(runtimeID);
				runtimeState = foundEC->getExecutionData().getRuntimeFormState(runtime_it);
				runtime_status->set_runtime_state(SymbexServerHelper::to_grpcProcesState(runtimeState));
			}
			return ::grpc::Status::OK;
		}
	} /* namespace grpc */
} /* namespace sep */

#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */

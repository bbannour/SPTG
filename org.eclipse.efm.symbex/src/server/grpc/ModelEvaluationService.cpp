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
#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )


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
#include <sew/SymbexEngine.h>

namespace sep
{
namespace grpc
{


// Model evaluation using workflow file
::grpc::Status SymbexServiceImpl::modelEval(::grpc::ServerContext * context,
		const ModelDefinitionRequest * request, ModelEvalReply * response)
{
	/*// CHECK PRECONDITION FOR << modelEval >> command
	if( exec_cmd_flag < EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		::grpc::Status resetStatus = resetServer();
		if( not resetStatus.ok() )
		{
			return resetStatus;
		}

		return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
				"rpc modelEval:> FAILED !!!");
	}
	else if( exec_cmd_flag == EXECUTED_INITIALIZATION_FLAG )
	{
		//!! NOTHING TO DO
	}*/

	// EVAL COMMAND CODE
	VFS::WorkflowPath = request->workflow_file_path();

	AVM_OS_DEBUG << "\n\nServer.modelEval { " << std::endl
			<< request->DebugString()
			<< "\tworkflow_file_path = " << VFS::WorkflowPath << std::endl
			<< "}" << std::endl;

	response->set_execution_context_count(-42);

	if( not VFS::WorkflowPath.empty() )
	{
		VFS::WorkflowPath = VFS::native_path(
				VFS::WorkflowPath, VFS::LaunchPath);

		if( VFS::checkReadingFile( VFS::WorkflowPath ) )
		{
			/*
			 * INITIALIZATION
			 * Loading  Workflow Parameter
			 */
			if( not mWorkflowParameter.loadConfiguration(VFS::WorkflowPath) )
			{
				response->set_execution_context_count(-1);

				return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
						"rpc modelEval:> Failed to load workflow configuration");
			}

			/*
			 * RUNNING
			 * parameter
			 */
			try
			{
//				SignalHandler::setSIGINT_handler();

				if( mWorkflow.configure(mWorkflowParameter) )
				{
					mWorkflow.startComputing();

					mSymbexEngine = mWorkflow.getMainSymbexEngine();

					mSymbexDispatcher = &( mSymbexEngine->getSymbexDispatcher() );
					
					mSupervisor = &( mSymbexEngine->getControllerUnitManager().getMainProcessor() );

					response->set_execution_context_count(ExecutionContextHeader::ID_NUMBER);
					response->set_execution_context_root_id(mSymbexEngine->getConfiguration().getMainExecutionContext().getIdNumber()+1);//TODO: investigate why +1 is required to have actual root of computed ec tree  

					response->set_step_count(mSymbexDispatcher->getSymbexStepCount());

					response->set_eval_count(mSymbexDispatcher->getEvalNumber());


					response->set_max_execution_context_height(mSupervisor->mMaxReachHeight);

					response->set_max_execution_context_width(mSupervisor->mMaxReachWidth);

//					response->set_redundancy_count(mSupervisor->);
					response->set_exit_execution_context_count(mSupervisor->mStatementExitCount);

					response->set_eval_limit_reached(
							mSupervisor->mSymbexEvalCountLimit <=
									mSymbexDispatcher->getEvalNumber());

					// SET POST_CONDITION
					exec_cmd_flag = EXECUTED_MODEL_EVAL_FLAG;

					return ::grpc::Status::OK;
				}
			}
			catch ( const std::exception & e )
			{
				AVM_OS_WARN << std::endl << EMPHASIS(
						"AvmLauncher::start< std::exception >", e.what(), '*', 80);

				return ::grpc::Status(::grpc::StatusCode::UNKNOWN,
						"rpc modelEval:> Symbex eception : " + std::string(e.what()));
			}
			catch ( ... )
			{
				AVM_OS_WARN << std::endl << EMPHASIS(
						"AvmLauncher::start< unknown::exception > !!!", '*', 80);

				return ::grpc::Status(::grpc::StatusCode::UNKNOWN,
						"rpc modelEval:> Symbex unknown eception !!!");
			}
		}
		else
		{
			AVM_OS_CERR << _SEW_
					<< "< error > Unreadable or non-existent file !"
					<< std::endl
					<< _SEW_ << "< info  > Launch path : "
					<< VFS::LaunchPath << std::endl;

			avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );

			return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
					"rpc modelEval:> Unreadable or non-existent file !!!");
		}
	}

	return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
			"rpc modelEval:> Unexpected empty file path !!!");
}


} /* namespace grpc */
} /* namespace sep */


#endif // _EXPERIMENTAL_SERVER_GRPC_FEATURE_ 

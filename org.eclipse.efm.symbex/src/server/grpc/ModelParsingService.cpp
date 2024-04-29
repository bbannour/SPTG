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

// Model Parsing
::grpc::Status SymbexServiceImpl::modelParse(
		::grpc::ServerContext * context,
		const ModelDefinitionRequest * request,
		ModelParseReply * response)
{    
	if( exec_cmd_flag > EXECUTED_INITIALIZATION_FLAG ){
		::grpc::Status resetStatus = resetServer();
		if (not resetStatus.ok()){
			return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
				"rpc modelParse:> FAILED !!!");
		}
	}

	if( not SymbexServerWorkflowUtils::prepareWorkspaceFolder() )
	{
		return ::grpc::Status(::grpc::StatusCode::RESOURCE_EXHAUSTED,
				"rpc modelParse:> Fail to prepare workspace folder "
				+ VFS::WorkspaceRootPath);
	}

	// EVAL COMMAND CODE
	const std::string & specFileLocation = request->model_file_path();
	if( VFS::checkReadingFile(specFileLocation) )
	{
		if( mWorkflowParameter.loadConfiguration(VFS::WorkflowPath) )
		{
			try
			{
				if( mWorkflow.configure(mWorkflowParameter) )
				{				
					mSymbexEngine = mWorkflow.getMainSymbexEngine();

					mSymbexEngine->getConfiguration()
							.setSpecificationFileLocation(specFileLocation);

					response->set_error_count(mSymbexEngine->mErrorCount);
					response->set_warning_count(mSymbexEngine->mWarningCount);

					// SET POST_CONDITION
					exec_cmd_flag = EXECUTED_MODEL_PARSE_FLAG;

					return ::grpc::Status::OK;
				}
				else
				{
					return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
							"rpc modelParse:> Fail to configure Workflow !!!");
				}
			}
			catch ( const std::exception & e )
			{
				AVM_OS_WARN << std::endl << EMPHASIS(
						"AvmLauncher::start< std::exception >", e.what(), '*', 80);

				return ::grpc::Status(::grpc::StatusCode::UNKNOWN,
						"rpc modelParse:> Symbex eception : " + std::string(e.what()));
			}
			catch ( ... )
			{
				AVM_OS_WARN << std::endl << EMPHASIS(
						"AvmLauncher::start< unknown::exception > !!!", '*', 80);

				return ::grpc::Status(::grpc::StatusCode::UNKNOWN,
						"rpc modelParse:> Symbex unknown eception !!!");
			}
		}
		else
		{
			response->set_error_count(-1);

			return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
					"rpc modelParse:> Fail to load Workflow configuration !!!");
		}
	}
	else
	{
		return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
				"rpc modelParse:> Unreadable or non-existent file !!!");
	}
}



::grpc::Status SymbexServiceImpl::modelParseFile(
		::grpc::ServerContext * context,
		const ModelDefinitionRequest * request,
		ModelParseReply * response)
{
	// CHECK PRECONDITION FOR << modelEval >> command
	if( exec_cmd_flag > EXECUTED_INITIALIZATION_FLAG )
	{
		::grpc::Status resetStatus = resetServer();
		if( not resetStatus.ok() )
		{
			return resetStatus;
		}
	}

	if( not SymbexServerWorkflowUtils::prepareWorkspaceFolder() )
	{
		return ::grpc::Status(::grpc::StatusCode::RESOURCE_EXHAUSTED,
				"rpc modelParseFIle:> Fail to prepare workspace folder "
				+ VFS::WorkspaceRootPath);
	}

	// EVAL COMMAND CODE
	const std::string & modelFileLocation = request->model_file_path();

	std::string workflowRawText =
			SymbexServerWorkflowUtils::getSEW(request, modelFileLocation);

	AVM_OS_DEBUG << "\n\nServer.modelParseFile { " << std::endl
			<< request->DebugString()
			<< "\tmodel_file_path = " << modelFileLocation << std::endl
			<< "\tSEW_file_path   = " << VFS::WorkflowPath << std::endl
			<< "}" << std::endl;

	if( VFS::checkReadingFile(modelFileLocation) )
	{
		if( mWorkflowParameter.loadConfiguration(VFS::WorkflowPath) )
		{
			try
			{
				if( mWorkflow.configure(mWorkflowParameter) )
				{
					mSymbexEngine = mWorkflow.getMainSymbexEngine();

					mSymbexEngine->getConfiguration()
							.setSpecificationFileLocation(modelFileLocation);

					response->set_error_count(mSymbexEngine->mErrorCount);
					response->set_warning_count(mSymbexEngine->mWarningCount);

					// SET POST_CONDITION
					exec_cmd_flag = EXECUTED_MODEL_PARSE_FLAG;

					return ::grpc::Status::OK;
				}
				else
				{
					return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
							"rpc modelParse:> Fail to configure Workflow !!!");
				}
			}
			catch ( const std::exception & e )
			{
				return ::grpc::Status(::grpc::StatusCode::UNKNOWN,
						"rpc modelParseFile:> Symbex eception : " + std::string(e.what()));
			}
			catch ( ... )
			{
				return ::grpc::Status(::grpc::StatusCode::UNKNOWN,
						"rpc modelParseFile:> Symbex unknown eception !!!");
			}
		}
		else
		{
			response->set_error_count(-1);
			return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
					"rpc modelParseFile:> Fail to load Workflow configuration !!!");
		}
	}
	else
	{
		return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
				"rpc modelParseFile:> Unreadable or non-existent file !!!");
	}
}


::grpc::Status SymbexServiceImpl::modelParseText(
		::grpc::ServerContext * context,
		const ModelDefinitionRequest * request,
		ModelParseReply * response)
{
	// CHECK PRECONDITION FOR << modelEval >> command
	if( exec_cmd_flag > EXECUTED_INITIALIZATION_FLAG )
	{
		::grpc::Status resetStatus = resetServer();
		if( not resetStatus.ok() )
		{
			return resetStatus;
		}
	}
	else if( exec_cmd_flag == EXECUTED_INITIALIZATION_FLAG )
	{
		//!! NOTHING TO DO
	}

	if( not SymbexServerWorkflowUtils::prepareWorkspaceFolder() )
	{
		return ::grpc::Status(::grpc::StatusCode::RESOURCE_EXHAUSTED,
				"rpc modelParseText:> Fail to prepare workspace folder "
				+ VFS::WorkspaceRootPath);
	}

	// EVAL COMMAND CODE
	const std::string & modelRawText = request->model_raw_text();

	std::string modelFileLocation =
			SymbexServerWorkflowUtils::saveRawTextModel(modelRawText);
	std::string workflowRawText =
			SymbexServerWorkflowUtils::getSEW(request, modelFileLocation);

	if( modelFileLocation.empty() )
	{
		return ::grpc::Status(::grpc::StatusCode::RESOURCE_EXHAUSTED,
				"rpc modelParseText:> Fail to save raw text model in folder "
				+ VFS::WorkspaceRootPath);
	}

	if( mWorkflowParameter.loadConfiguration(VFS::WorkflowPath) )
	{
		try
		{
			if( mWorkflow.configure(mWorkflowParameter) )
			{
				mSymbexEngine = mWorkflow.getMainSymbexEngine();

				mSymbexEngine->getConfiguration()
						.setSpecificationFileLocation(modelFileLocation);

				response->set_error_count(mSymbexEngine->mErrorCount);
				response->set_warning_count(mSymbexEngine->mWarningCount);

				// SET POST_CONDITION
				exec_cmd_flag = EXECUTED_MODEL_PARSE_FLAG;

				return ::grpc::Status::OK;
			}
			else
			{
				return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
						"rpc modelParse:> Fail to configure Workflow !!!");
			}
		}
		catch ( const std::exception & e )
		{
			return ::grpc::Status(::grpc::StatusCode::UNKNOWN,
					"rpc modelParseText:> Symbex eception : " + std::string(e.what()));
		}
		catch ( ... )
		{
			return ::grpc::Status(::grpc::StatusCode::UNKNOWN,
					"rpc modelParseText:> Symbex unknown eception !!!");
		}
	}
	else
	{
		response->set_error_count(-1);

		return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
				"rpc modelParseText:> Fail to load Workflow configuration !!!");
	}
}

} /* namespace grpc */
} /* namespace sep */


#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */

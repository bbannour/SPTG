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

#ifndef SERVER_GRPC_SYMBEXSERVER_H_
#define SERVER_GRPC_SYMBEXSERVER_H_

#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )

#include "SymbexServices.grpc.pb.h"

#ifdef __AVM_MINGW__
#include <grpcpp/server.h>
#else //#ifdef __AVM_LINUX__
#include <grpc++/server.h>
#endif


#include <sew/Workflow.h>
#include <sew/WorkflowParameter.h>

namespace sep
{

class EvaluationEnvironment;
class ExecutionContext;
class MainProcessorUnit;
class SymbexDispatcher;
class SymbexEngine;


namespace grpc
{

class SymbexServer
{

protected:
	/*
	 * ATTRIBUTES
	 */
	::grpc::Server * mServer;

public:
	/*
	 * GETTER
	 * mServer
	 */
	inline void setServer(::grpc::Server * server)
	{
		mServer = server;
	}


	/*
	 * RUN / SHUTDOWN
	 * SERVER
	 */
	void start();

	void shutdown();

	static void runServer();
};


// Logic and data behind the server's behavior.
class SymbexServiceImpl final : public Symbex::Service
{

protected:
	/*
	 * ATTRIBUTES
	 */
	SymbexServer * mSymbexServer;

	WorkflowParameter mWorkflowParameter;
	Workflow mWorkflow;

	SymbexEngine * mSymbexEngine;

	SymbexDispatcher * mSymbexDispatcher;

	MainProcessorUnit * mSupervisor;

	EvaluationEnvironment * ENV;


	enum EXECUTED_COMMAND_FLAG {

		EXECUTED_NONE_FLAG               = 0x000,

		EXECUTED_INITIALIZATION_FLAG     = 0x001,

		EXECUTED_MODEL_PARSE_FLAG        = 0x002,

		EXECUTED_MODEL_EVAL_FLAG         = 0x004,

		EXECUTED_SYMBEX_EVAL_INIT_FLAG   = 0x008,
	};

	typedef std::uint8_t executed_command_flag_t;

	executed_command_flag_t  exec_cmd_flag;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexServiceImpl();


	/*
	 * GETTER
	 * mServer
	 */
	inline void setServer(SymbexServer * server)
	{
		mSymbexServer = server;
	}


	/**
	 * UTILS
	 */
	::grpc::Status resetServer();

	::grpc::Status checkPrecondition();


	/**
	 * GRPC
	 * SERVICES
	 */
	// Initialization
	::grpc::Status initialization(::grpc::ServerContext * context,
			const InitializationRequest * request,
			InitializationReply * response) override;

	// Model Evaluation
	::grpc::Status modelEval(::grpc::ServerContext * context,
			const ModelDefinitionRequest * request,
			ModelEvalReply * response) override;

	// Model Parsing
	::grpc::Status modelParse(::grpc::ServerContext * context,
			const ModelDefinitionRequest * request,
			ModelParseReply * response) override;

	::grpc::Status modelParseFile(::grpc::ServerContext * context,
			const ModelDefinitionRequest * request,
			ModelParseReply * response) override;

	::grpc::Status modelParseText(::grpc::ServerContext * context,
			const ModelDefinitionRequest * request,
			ModelParseReply * response) override;

	  // Symbex Initialization
	::grpc::Status symbexEvalInit(::grpc::ServerContext * context,
			const SymbexEvalInitRequest * request,
			SymbexEvalInitReply * response) override;

	// Symbex Evaluation
	::grpc::Status symbexEvalStep(::grpc::ServerContext * context,
			const SymbexEvalStepRequest * request,
			SymbexEvalStepReply * response) override;

	// Symbex Evaluation from Context
	::grpc::Status symbexEvalContext(::grpc::ServerContext * context,
			const SymbexEvalContextRequest * request,
			SymbexEvalContextReply * response) override;

	::grpc::Status symbexEvalMachine(::grpc::ServerContext * context,
			const SymbexEvalRunnableRequest * request,
			SymbexEvalRunnableReply * response) override;

	::grpc::Status symbexEvalBasicMachine(::grpc::ServerContext * context,
			const SymbexEvalRunnableRequest * request,
			SymbexEvalRunnableBasicReply * response) override;

	// The request message for Evaluation of a State (by a string FQN_ID)
	::grpc::Status symbexEvalState(::grpc::ServerContext * context,
			const SymbexEvalRunnableRequest * request,
			SymbexEvalRunnableReply * response) override;

	// Symbex Evaluation of a Transition (by a string FQN_ID) on a Context
	::grpc::Status symbexEvalTransition(::grpc::ServerContext * context,
			const SymbexEvalRunnableRequest * request,
			SymbexEvalRunnableReply * response) override;


	// Symbex Query Variable Value
	::grpc::Status queryValueofVariable(::grpc::ServerContext * context,
			const QueryValueForVariableRequest * request,
			QueryValueForVariableReply * response) override;

	// Symbex Query Trace for Condition
	::grpc::Status queryNodeCondition(::grpc::ServerContext * context,
			const QueryValueForVariableRequest * request,
			QueryValueForVariableReply * response) override;

	::grpc::Status queryPathCondition(::grpc::ServerContext * context,
			const QueryValueForVariableRequest * request,
			QueryValueForVariableReply * response) override;

	// Symbex Query Trace for IO élement (input / output / newfresh)
	::grpc::Status queryTraceIO(::grpc::ServerContext * context,
			const QueryValueForVariableRequest * request,
			QueryValueForVariableReply * response) override;

	// Symbex Query Trace for Executable element (machine / statemachine / state / transition)
	::grpc::Status queryTraceExecutable(::grpc::ServerContext * context,
			const QueryValueForVariableRequest * request,
			QueryValueForVariableReply * response) override;


	// Symbex Evaluation of a Transition (by a string FQN_ID) on a Context
	::grpc::Status runPostProcessor(::grpc::ServerContext * context,
			const PostProcessingRequest * request,
			PostProcessingReply * response) override;


	::grpc::Status queryChildContext(::grpc::ServerContext * context,
			const ECQuery * request,
			ECReply * response) override;


	::grpc::Status queryRuntimesStatus(::grpc::ServerContext * context,
			const ECQuery * request,
			RuntimesStatusReply * response) override;


	::grpc::Status queryEC(::grpc::ServerContext * context,
			const ECQuery * request,GRPCExecutionContext* response) override;
//	// For test purpose
//	::grpc::Status sayHello(::grpc::ServerContext * context,
//			const HelloRequest * request, HelloReply * response) override;
//
//	::grpc::Status sayHelloAgain(::grpc::ServerContext * context,
//			const HelloRequest * request, HelloReply * response) override;
//
//	::grpc::Status stopServer(::grpc::ServerContext * context,
//			const ::google::protobuf::Empty * request, HelloReply * response) override;

};


} /* namespace grpc */

} /* namespace sep */


#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */

#endif /* SERVER_GRPC_SYMBEXSERVER_H_ */

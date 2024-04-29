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
#include <server/grpc/SymbexServerHelper.h>
#include <server/grpc/SymbexServerExpressionBuilder.h>


#include <sew/SymbexEngine.h>
#include <computer/ExecutionEnvironment.h>

namespace sep
{
namespace grpc
{


// Symbex Initialization
::grpc::Status SymbexServiceImpl::symbexEvalInit(::grpc::ServerContext * context,
		const SymbexEvalInitRequest * request, SymbexEvalInitReply * response)
{
	// CHECK PRECONDITION FOR << modelEval >> command
	if( exec_cmd_flag < EXECUTED_MODEL_PARSE_FLAG )
	{
		::grpc::Status resetStatus = resetServer();
		if( not resetStatus.ok() )
		{
			return resetStatus;
		}

		return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
				"rpc symbexEvalInit:> Use modelParse File or Text before !");
	}
	else if( exec_cmd_flag == EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		//!! NOTHING TO DO
	}

	// EVAL COMMAND CODE
	AVM_OS_DEBUG << "\n\nServer.symbexEvalInit {" << std::endl
			<< request->DebugString()
			<< "\tvariable_value {" << std::endl;

	if( not request->variable_value().empty() )
	{
		AVM_OS_DEBUG << "\t\tSymbexServerHelper::setVariableValue(...) " << std::endl;
	}
	AVM_OS_DEBUG << "\t}" << std::endl << "}" << std::endl;

	mSymbexEngine->initComputing();

	mSymbexDispatcher = &( mSymbexEngine->getSymbexDispatcher() );

	mSupervisor = &( mSymbexEngine->
			getControllerUnitManager().getMainProcessor() );

	const ListOfExecutionContext & resultContexts =
			mSymbexDispatcher->getLastResultContexts();

	if( resultContexts.nonempty()  )
	{
		const ExecutionContext * outEC = resultContexts.first();
		if( outEC->hasChildContext() )
		{
			response->set_execution_context_id(
					outEC->firstChildContext()->getIdNumber() );
		}

		::sep::grpc::Expression * grpc_path_condition =
				response->mutable_path_condition();

		if( not SymbexServerExpressionBuilder::to_grpc(*grpc_path_condition,
				TYPE_UNDEFINED_SPECIFIER, outEC->getPathCondition()) )
		{
			return ::grpc::Status(::grpc::StatusCode::ABORTED,
					"Failed to encode in grpc::Expression the PATH_CONDITION < "
					+ outEC->getPathCondition().str() + " > !");
		}

		::sep::grpc::Expression * grpc_other_condition =
				response->mutable_other_condition();

		if( not SymbexServerExpressionBuilder::to_grpc(*grpc_other_condition,
				TYPE_UNDEFINED_SPECIFIER, outEC->getPathTimedCondition()) )
		{
			return ::grpc::Status(::grpc::StatusCode::ABORTED,
					"Failed to encode in grpc::Expression the TIMED PATH_CONDITION < "
					+ outEC->getPathTimedCondition().str() + " > !");
		}
	}

//mSupervisor->getExecutionQueue().toStream(AVM_OS_DEBUG);

	// SET POST_CONDITION
	exec_cmd_flag = EXECUTED_SYMBEX_EVAL_INIT_FLAG;

	return ::grpc::Status::OK;
}


// Symbex Evaluation Step
::grpc::Status SymbexServiceImpl::symbexEvalStep(
		::grpc::ServerContext * context,
		const SymbexEvalStepRequest * request,
		SymbexEvalStepReply * response)
{
	// CHECK PRECONDITION FOR << modelEval >> command
	if( exec_cmd_flag < EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		::grpc::Status resetStatus = resetServer();
		if( not resetStatus.ok() )
		{
			return resetStatus;
		}

		return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
				"rpc symbexEvalStep:> Use symbexEvalInit before !");
	}
	else if( exec_cmd_flag == EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		//!! NOTHING TO DO
	}


	// EVAL COMMAND CODE
	std::uint32_t step_count = request->step_count();


	AVM_OS_DEBUG << "\n\nServer.symbexEvalStep {" << std::endl
			<< request->DebugString()
			<< "\tstep_count  : " << step_count  << std::endl
			<< "\tvariable_value {" << std::endl;

	if( not request->variable_value().empty() )
	{
		AVM_OS_DEBUG << "\t\tSymbexServerHelper::setVariableValue(...) " << std::endl;
	}
	AVM_OS_DEBUG << "\t}" << std::endl << "}" << std::endl;

	std::uint32_t prev_step_count = mSymbexDispatcher->getSymbexStepCount();

	std::uint32_t prev_eval_count = mSymbexDispatcher->getEvalNumber();

	for( ; step_count > 0 ; --step_count )
	{
		mSymbexDispatcher->runStep();
	}

	response->set_step_count(
			mSymbexDispatcher->getSymbexStepCount() - prev_step_count);
	response->set_eval_count(
			mSymbexDispatcher->getEvalNumber() - prev_eval_count);

	ListOfExecutionContext leaveEC;
	mSupervisor->computeLeafEC(
		mSymbexEngine->getConfiguration().getExecutionTrace(), leaveEC);

	const auto & not_yet_eval_ec_id =
			response->mutable_not_yet_eval_execution_context_id();
	for( const auto leafEC : leaveEC )
	{
		if( leafEC->getEvalNumber() < 1 )
		{
			not_yet_eval_ec_id->Add(leafEC->getIdNumber());
		}
	}

mSupervisor->getExecutionQueue().toStream(AVM_OS_DEBUG);

	return ::grpc::Status::OK;
}


// Symbex Evaluation from Context
::grpc::Status SymbexServiceImpl::symbexEvalContext(
		::grpc::ServerContext * context,
		const SymbexEvalContextRequest * request,
		SymbexEvalContextReply * response)
{
	// CHECK PRECONDITION FOR << modelEval >> command
	if( exec_cmd_flag < EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		::grpc::Status resetStatus = resetServer();
		if( not resetStatus.ok() )
		{
			return resetStatus;
		}

		return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
				"rpc symbexEvalContext:> Use symbexEvalInit before !");
	}
	else if( exec_cmd_flag == EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		//!! NOTHING TO DO
	}


	// EVAL COMMAND CODE
	std::uint32_t execution_context_id = request->execution_context_id();
	std::uint32_t step_count = request->step_count();

	AVM_OS_DEBUG << "\n\nServer.symbexEvalContext {" << std::endl
			<< request->DebugString()
			<< "\texecution_context_id : " << execution_context_id  << std::endl
			<< "\tstep_count           : " << step_count  << std::endl
			<< "\tvariable_value {" << std::endl;

	if( not request->variable_value().empty() )
	{
		AVM_OS_DEBUG << "\t\tSymbexServerHelper::setVariableValue(...) " << std::endl;
	}
	AVM_OS_DEBUG << "\t}" << std::endl << "}" << std::endl;

	ExecutionContext * foundEC = SymbexServerHelper::searchContext(
			mSymbexEngine->getConfiguration().getExecutionTrace(),
			execution_context_id);

	if( foundEC == nullptr )
	{
		return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
				"NOT_FOUND: The Execution Context with ID< "
				+ std::to_string(execution_context_id)
				+ " > doesn't exist !");
	}

	ExecutionContext * inputEC = foundEC;
	if( foundEC->hasChildContext() || (not request->variable_value().empty()) )
	{
		inputEC = foundEC->cloneData(foundEC, true);
		foundEC->appendChildContext( inputEC );

		inputEC->getwExecutionData().resetVariantBeforeEvaluation();
	}

	// Set variabe <- value in the inputEC
	if( not request->variable_value().empty() )
	{
		ExecutableQuery XQuery( mSymbexEngine->getConfiguration() );

		ExecutionEnvironment ENV(mSymbexEngine->getPrimitiveProcessor(), inputEC);

		if( not SymbexServerHelper::setVariableValue(XQuery, ENV, *inputEC, request->variable_value()) )
		{
			return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
					"FAILED_PRECONDITION: Failed to set variable <- value ");
		}
	}

	// Add condition
	if( request->has_condition() )
	{
		ExecutableQuery XQuery( mSymbexEngine->getConfiguration() );

		ExecutionEnvironment ENV(mSymbexEngine->getPrimitiveProcessor(), inputEC);

		if( not SymbexServerHelper::addCondtion(XQuery, ENV, *inputEC, request->condition()) )
		{
			return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
					"FAILED_PRECONDITION: Failed to add condition in Path Condition");
		}
	}

	// Set inputEC as singleton in the Waiting Queue
	ListOfExecutionContext readyContexts;
	ListOfExecutionContext waitingContexts;
	mSupervisor->getExecutionQueue().resetQueues(readyContexts, waitingContexts);

	mSupervisor->getExecutionQueue().appendAnteWaiting( inputEC );
	mSupervisor->getExecutionQueue().pushAnteWaiting();


	std::uint32_t prev_step_count = mSymbexDispatcher->getSymbexStepCount();

	std::uint32_t prev_eval_count = mSymbexDispatcher->getEvalNumber();

	for( ; step_count > 0 ; --step_count )
	{
		mSymbexDispatcher->runStep();
	}

	response->set_step_count(
			mSymbexDispatcher->getSymbexStepCount() - prev_step_count);
	response->set_eval_count(
			mSymbexDispatcher->getEvalNumber() - prev_eval_count);

	ListOfExecutionContext listOfRootEC( inputEC );
	ListOfExecutionContext leaveEC;
	mSupervisor->computeLeafEC(listOfRootEC, leaveEC);

	const auto & child_execution_context_id =
			response->mutable_child_execution_context_id();
	for( const auto leafEC : leaveEC )
	{
		if( leafEC->getEvalNumber() < 1 )
		{
			child_execution_context_id->Add(leafEC->getIdNumber());
		}
	}

mSupervisor->getExecutionQueue().toStream(AVM_OS_DEBUG);

	return ::grpc::Status::OK;

}





::grpc::Status SymbexServiceImpl::symbexEvalMachine(
		::grpc::ServerContext * context,
		const SymbexEvalRunnableRequest * request,
		SymbexEvalRunnableReply * response)
{
	// CHECK PRECONDITION FOR << modelEval >> command
	if( exec_cmd_flag < EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		::grpc::Status resetStatus = resetServer();
		if( not resetStatus.ok() )
		{
			return resetStatus;
		}

		return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
				"rpc symbexEvalMachine:> Use symbexEvalInit before !");
	}
	else if( exec_cmd_flag == EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		//!! NOTHING TO DO
	}


	// EVAL COMMAND CODE
	std::uint32_t execution_context_id      = request->execution_context_id();
	const std::string & runnable_element_id = request->runnable_element_id();


	AVM_OS_DEBUG << "\n\nServer.symbexEvalMachine {" << std::endl
			<< request->DebugString()
			<< "\texecution_context_id : " << execution_context_id << std::endl
			<< "\trunnable_element_id  : " << runnable_element_id  << std::endl
			<< "\tvariable_value {" << std::endl;

	if( not request->variable_value().empty() )
	{
		AVM_OS_DEBUG << "\t\tSymbexServerHelper::setVariableValue(...) " << std::endl;
	}
	AVM_OS_DEBUG << "\t}" << std::endl << "}" << std::endl;


	ExecutionContext * foundEC = SymbexServerHelper::searchContext(
			mSymbexEngine->getConfiguration().getExecutionTrace(),
			execution_context_id);

	if( foundEC == nullptr )
	{
		return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
				"NOT_FOUND: The Execution Context with ID< "
					+ std::to_string(execution_context_id)
					+ " > doesn't exist !");
	}

	ExecutionContext * inputEC = foundEC;
	if( foundEC->hasChildContext() || (not request->variable_value().empty()) )
	{
		inputEC = foundEC->cloneData(foundEC, true);
		foundEC->appendChildContext( inputEC );

		inputEC->getwExecutionData().resetVariantBeforeEvaluation();
	}

	ExecutableQuery XQuery( mSymbexEngine->getConfiguration() );
	const sep::Symbol & foundMachineSymbol = XQuery.getMachineByID(
			Specifier::DESIGN_INSTANCE_KIND, runnable_element_id);

	if( foundMachineSymbol.invalid() )
	{
AVM_OS_DEBUG << "  --> NOT FOUND runnable_element_id: " << runnable_element_id << " ??????????" << std::endl << std::endl;

		return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
				"NOT_FOUND: The machine with ID " + runnable_element_id );
	}
//AVM_OS_DEBUG << "  --> FOUND runnable_element_id: " << foundMachineSymbol.getFullyQualifiedNameID() << " !!!!!!!!!!" << std::endl;

	ExecutionData & inputED = inputEC->getwExecutionData();

	const RuntimeID & machineRID =
			inputED.getRuntimeID( foundMachineSymbol.machine() );

AVM_OS_DEBUG << "  --> FOUND & Schedule machineRID: " << machineRID.getFullyQualifiedNameID() << " !!!!!!!!!!" << std::endl;


	// Set variabe <- value in the inputEC
	if( not request->variable_value().empty() )
	{
		ExecutionEnvironment ENV(mSymbexEngine->getPrimitiveProcessor(), inputEC);

		if( not SymbexServerHelper::setVariableValue(XQuery, ENV, *inputEC, request->variable_value()) )
		{
			return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
					"FAILED_PRECONDITION: Failed to set variable <- value ");
		}
	}

	// Set inputEC as singleton in the Waiting Queue
	ListOfExecutionContext readyContexts;
	ListOfExecutionContext waitingContexts;
	mSupervisor->getExecutionQueue().resetQueues(readyContexts, waitingContexts);

	inputED.makeWritable();

	inputED.setRID(machineRID.getPRID());
	inputED.mwsetRuntimeFormOnScheduleAndIdle(machineRID.getPRID());

	inputED.setRID(machineRID);
	inputED.mwsetRuntimeFormOnScheduleAndIdle(machineRID);

	mSupervisor->getExecutionQueue().appendAnteWaiting( inputEC );
	mSupervisor->getExecutionQueue().pushAnteWaiting();

//AVM_OS_DEBUG << "  --> onScheduleCode: " << inputEC->getwExecutionData().getSystemRuntime().getOnSchedule() << " !!!!!!!!!!" << std::endl;

	mSymbexDispatcher->runStep();


	const ListOfExecutionContext & resultContexts =
			mSymbexDispatcher->getLastResultContexts();

	const auto & out_ec_id = response->mutable_execution_context_id();
	for( const auto & resultEC : resultContexts )
	{
		for( const auto & outEC : resultEC->getChildContexts() )
		{
			out_ec_id->Add(outEC->getIdNumber());
		}
	}

	ListOfExecutionContext leaveEC;
	mSupervisor->computeLeafEC(
		mSymbexEngine->getConfiguration().getExecutionTrace(), leaveEC);

	const auto & not_yet_eval_ec_id =
			response->mutable_not_yet_eval_execution_context_id();
	for( const auto leafEC : leaveEC )
	{
		if( leafEC->getEvalNumber() < 1 )
		{
			not_yet_eval_ec_id->Add(leafEC->getIdNumber());
		}
	}

mSupervisor->getExecutionQueue().toStream(AVM_OS_DEBUG);

	return ::grpc::Status::OK;
}






::grpc::Status SymbexServiceImpl::symbexEvalBasicMachine(
		::grpc::ServerContext * context,
		const SymbexEvalRunnableRequest * request,
		SymbexEvalRunnableBasicReply * response)
{
	// CHECK PRECONDITION FOR << modelEval >> command
	if( exec_cmd_flag < EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		::grpc::Status resetStatus = resetServer();
		if( not resetStatus.ok() )
		{
			return resetStatus;
		}

		return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
				"rpc symbexEvalMachine:> Use symbexEvalInit before !");
	}
	else if( exec_cmd_flag == EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		//!! NOTHING TO DO
	}


	// EVAL COMMAND CODE
	std::uint32_t execution_context_id      = request->execution_context_id();
	const std::string & runnable_element_id = request->runnable_element_id();

AVM_OS_DEBUG << std::endl
	<< "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$" << std::endl
	<< "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$" << std::endl;

	AVM_OS_DEBUG << "\n\nServer.symbexEvalBasicMachine {" << std::endl
			<< request->DebugString()
			<< "\texecution_context_id : " << execution_context_id << std::endl
			<< "\trunnable_element_id  : " << runnable_element_id  << std::endl
			<< "\tvariable_value {" << std::endl;

	if( not request->variable_value().empty() )
	{
		AVM_OS_DEBUG << "\t\tSymbexServerHelper::setVariableValue(...) " << std::endl;
	}
	AVM_OS_DEBUG << "\t}" << std::endl << "}" << std::endl;


	ExecutionContext * foundEC = SymbexServerHelper::searchContext(
			mSymbexEngine->getConfiguration().getExecutionTrace(),
			execution_context_id);

	if( foundEC == nullptr )
	{
		return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
				"NOT_FOUND: The Execution Context with ID< "
					+ std::to_string(execution_context_id)
					+ " > doesn't exist !");
	}

	ExecutionContext * inputEC = foundEC;
	if( foundEC->hasChildContext() || (not request->variable_value().empty()) )
	{
		inputEC = foundEC->cloneData(foundEC, true);
		foundEC->appendChildContext( inputEC );

		inputEC->getwExecutionData().resetVariantBeforeEvaluation();
	}

	ExecutableQuery XQuery( mSymbexEngine->getConfiguration() );
	const sep::Symbol & foundMachineSymbol = XQuery.getMachineByID(
			Specifier::DESIGN_INSTANCE_KIND, runnable_element_id);

	if( foundMachineSymbol.invalid() )
	{
AVM_OS_DEBUG << "  --> NOT FOUND runnable_element_id: " << runnable_element_id << " ??????????" << std::endl << std::endl;

		return ::grpc::Status(::grpc::StatusCode::NOT_FOUND,
				"NOT_FOUND: The machine with ID " + runnable_element_id );
	}
//AVM_OS_DEBUG << "  --> FOUND runnable_element_id: " << foundMachineSymbol.getFullyQualifiedNameID() << " !!!!!!!!!!" << std::endl;

	ExecutionData & inputED = inputEC->getwExecutionData();

	const RuntimeID & machineRID =
			inputED.getRuntimeID( foundMachineSymbol.machine() );

AVM_OS_DEBUG << "  --> FOUND & Schedule machineRID: " << machineRID.getFullyQualifiedNameID() << " !!!!!!!!!!" << std::endl;


	// Set variabe <- value in the inputEC
	if( not request->variable_value().empty() )
	{
		ExecutionEnvironment ENV(mSymbexEngine->getPrimitiveProcessor(), inputEC);

		if( not SymbexServerHelper::setVariableValue(XQuery, ENV, *inputEC, request->variable_value()) )
		{
			return ::grpc::Status(::grpc::StatusCode::FAILED_PRECONDITION,
					"FAILED_PRECONDITION: Failed to set variable <- value ");
		}
	}

	// Set inputEC as singleton in the Waiting Queue
	ListOfExecutionContext readyContexts;
	ListOfExecutionContext waitingContexts;
	mSupervisor->getExecutionQueue().resetQueues(readyContexts, waitingContexts);

	inputED.makeWritable();

	inputED.setRID(machineRID.getPRID());
	inputED.mwsetRuntimeFormOnScheduleAndIdle(machineRID.getPRID());

	inputED.setRID(machineRID);
	inputED.mwsetRuntimeFormOnScheduleAndIdle(machineRID);

	mSupervisor->getExecutionQueue().appendAnteWaiting( inputEC );
	mSupervisor->getExecutionQueue().pushAnteWaiting();

//AVM_OS_DEBUG << "  --> onScheduleCode: " << inputEC->getwExecutionData().getSystemRuntime().getOnSchedule() << " !!!!!!!!!!" << std::endl;

	mSymbexDispatcher->runStep();


	const ListOfExecutionContext & resultContexts =
			mSymbexDispatcher->getLastResultContexts();

	if( resultContexts.singleton()  )
	{
		const ExecutionContext * firstEC = resultContexts.first();
		if( firstEC->singleChildContext() )
		{
			const ExecutionContext * outEC = firstEC->firstChildContext();

			response->set_execution_context_id( outEC->getIdNumber() );

			response->set_is_satisfiable(true);

			::sep::grpc::Expression * grpc_path_condition =
					response->mutable_path_condition();

			if( not SymbexServerExpressionBuilder::to_grpc(*grpc_path_condition,
					TYPE_UNDEFINED_SPECIFIER, outEC->getPathCondition()) )
			{
				return ::grpc::Status(::grpc::StatusCode::ABORTED,
						"Failed to encode in grpc::Expression the PATH_CONDITION < "
						+ outEC->getPathCondition().str() + " > !");
			}

			::sep::grpc::Expression * grpc_other_condition =
					response->mutable_other_condition();

			if( not SymbexServerExpressionBuilder::to_grpc(*grpc_other_condition,
					TYPE_UNDEFINED_SPECIFIER, outEC->getPathTimedCondition()) )
			{
				return ::grpc::Status(::grpc::StatusCode::ABORTED,
						"Failed to encode in grpc::Expression the TIMED PATH_CONDITION < "
						+ outEC->getPathTimedCondition().str() + " > !");
			}

			if( not SymbexServerHelper::setCreatedSymbols(
					*inputEC, *outEC, response) )
			{
				return ::grpc::Status(::grpc::StatusCode::ABORTED,
						"Failed to encode new  grpc::TypedSymbol !");
			}
		}
		else if( firstEC->noChildContext() )
		{
			//!! DEADLOCK

			response->set_is_satisfiable(false);

			response->mutable_path_condition()->set_raw_bool(false);

			response->mutable_other_condition()->set_raw_bool(false);
		}
		else
		{
			return ::grpc::Status(::grpc::StatusCode::ABORTED,
					"Unexped more than one execution context as evaluation result "
					"( resust " + std::to_string(firstEC->getChildContexts().size())
					+ " execution contexts ) !");
		}
	}
	else if( resultContexts.empty()  )
	{
		//!! DEADLOCK

		response->set_is_satisfiable(false);

		response->set_is_satisfiable(false);

		response->mutable_path_condition()->set_raw_bool(false);

		response->mutable_other_condition()->set_raw_bool(false);
	}


	ListOfExecutionContext leaveEC;
	mSupervisor->computeLeafEC(
		mSymbexEngine->getConfiguration().getExecutionTrace(), leaveEC);

	const auto & not_yet_eval_ec_id =
			response->mutable_not_yet_eval_execution_context_id();
	for( const auto leafEC : leaveEC )
	{
		if( leafEC->getEvalNumber() < 1 )
		{
			not_yet_eval_ec_id->Add(leafEC->getIdNumber());
		}
	}

//mSupervisor->getExecutionQueue().toStream(AVM_OS_DEBUG);

	return ::grpc::Status::OK;
}







// The request message for Evaluation of a State (by a string FQN_ID)
::grpc::Status SymbexServiceImpl::symbexEvalState(
		::grpc::ServerContext * context,
		const SymbexEvalRunnableRequest * request,
		SymbexEvalRunnableReply * response)
{
	// CHECK PRECONDITION FOR << modelEval >> command
	if( exec_cmd_flag < EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		::grpc::Status resetStatus = resetServer();
		if( not resetStatus.ok() )
		{
			return resetStatus;
		}
	}
	else if( exec_cmd_flag == EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		//!! NOTHING TO DO
	}


	// EVAL COMMAND CODE
	std::uint32_t execution_context_id      = request->execution_context_id();
	const std::string & runnable_element_id = request->runnable_element_id();


	AVM_OS_DEBUG << "\n\nServer.symbexEvalState {" << std::endl
			<< request->DebugString()
			<< "\texecution_context_id : " << execution_context_id << std::endl
			<< "\trunnable_element_id  : " << runnable_element_id  << std::endl
			<< "\tvariable_value {" << std::endl;

	if( not request->variable_value().empty() )
	{
		AVM_OS_DEBUG << "\t\tSymbexServerHelper::setVariableValue(...) " << std::endl;
	}
	AVM_OS_DEBUG << "\t}" << std::endl << "}" << std::endl;


	return ::grpc::Status::OK;
}

// Symbex Evaluation of a Transition (by a string FQN_ID) on a Context
::grpc::Status SymbexServiceImpl::symbexEvalTransition(
		::grpc::ServerContext * context,
		const SymbexEvalRunnableRequest * request,
		SymbexEvalRunnableReply * response)
{
	// CHECK PRECONDITION FOR << modelEval >> command
	if( exec_cmd_flag < EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		::grpc::Status resetStatus = resetServer();
		if( not resetStatus.ok() )
		{
			return resetStatus;
		}
	}
	else if( exec_cmd_flag == EXECUTED_SYMBEX_EVAL_INIT_FLAG )
	{
		//!! NOTHING TO DO
	}


	// EVAL COMMAND CODE
	std::uint32_t execution_context_id      = request->execution_context_id();
	const std::string & runnable_element_id = request->runnable_element_id();


	AVM_OS_DEBUG << "\n\nServer.symbexEvalTransition {" << std::endl
			<< request->DebugString()
			<< "\texecution_context_id : " << execution_context_id << std::endl
			<< "\trunnable_element_id  : " << runnable_element_id  << std::endl
			<< "\tvariable_value {" << std::endl;

	if( not request->variable_value().empty() )
	{
		AVM_OS_DEBUG << "\t\tSymbexServerHelper::setVariableValue(...) " << std::endl;
	}
	AVM_OS_DEBUG << "\t}" << std::endl << "}" << std::endl;

	return ::grpc::Status::OK;
}

} /* namespace grpc */
} /* namespace sep */


#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */

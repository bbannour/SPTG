/*******************************************************************************
 * Copyright (c) 2020 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 mai 2020
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef SERVER_GRPC_SYMBEXSERVERHELPER_H_
#define SERVER_GRPC_SYMBEXSERVERHELPER_H_

#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )

#include "SymbexServices.pb.h"
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/RuntimeForm.h>
#include <famcore/debug/IDebugProcessorHelper.h>
#include <server/grpc/SymbexServices.pb.h>

namespace sep
{

class BaseEnvironment;
class BaseTypeSpecifier;
class ExecutionContext;
class ExecutionEnvironment;
class ExecutableQuery;

namespace grpc
{
	class SymbexEvalRunnableBasicReply;
}

class SymbexServerHelper
{

public:

	static ExecutionContext * searchContext(
		const ListOfExecutionContext & relativeRootEC, std::uint32_t ctxID);

	static grpc::RuntimeStatusTree* runtimeStatusTree(const ExecutionContext* ec);
	static void runtimeStatusTree_aux(grpc::RuntimeStatusTree*,const ExecutionContext* ec,const RuntimeForm& runtimeForm);


	static bool setVariableValue(ExecutableQuery & XQuery,
			BaseEnvironment & ENV, ExecutionContext & inputEC,
			const ::google::protobuf::RepeatedPtrField<
					::sep::grpc::VariableValuePair > & variable_value);

	static bool addCondtion(ExecutableQuery & XQuery,
			ExecutionEnvironment & ENV, ExecutionContext & inputEC,
			const ::sep::grpc::Expression & condition);

	static ::sep::grpc::DataType to_grpcDataType(
			const BaseTypeSpecifier & typeSpecifier);

	static ::sep::grpc::PROCESS_STATE to_grpcProcesState(const PROCESS_EVAL_STATE & pes);

	static bool setCreatedSymbols(
			const ExecutionContext & inputEC, const ExecutionContext & outputEC,
			::sep::grpc::SymbexEvalRunnableBasicReply * response);

};

} /* namespace sep */

#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */

#endif /* SERVER_GRPC_SYMBEXSERVERHELPER_H_ */

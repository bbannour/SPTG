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

#ifndef SERVER_GRPC_SYMBEXSERVEREXPRESSIONBUILDER_H_
#define SERVER_GRPC_SYMBEXSERVEREXPRESSIONBUILDER_H_

#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )

#include "SymbexServices.pb.h"

#include <fml/lib/ITypeSpecifier.h>
#include <fml/operator/OperatorLib.h>

namespace sep
{

class BF;
class ExecutableQuery;
class ExecutionContext;


class SymbexServerExpressionBuilder
{

public:

	static ::sep::grpc::OperatorKind to_grpc_op(AVM_OPCODE opcode);

	static bool to_grpc(::sep::grpc::Expression & grpc_expression,
			avm_type_specifier_kind_t type_specifier_kind, const BF & expr);

	static BF from_grpc(const ExecutableQuery & XQuery,
			const ExecutionContext & anEC, const ::sep::grpc::Expression & expr);

	static BF from_grpc(const ExecutableQuery & XQuery,
			const ExecutionContext & anEC, const ::sep::grpc::Operation & operation);

};

} /* namespace sep */

#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */

#endif /* SERVER_GRPC_SYMBEXSERVEREXPRESSIONBUILDER_H_ */

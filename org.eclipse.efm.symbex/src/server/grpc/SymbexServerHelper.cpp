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

#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )

#include "SymbexServerHelper.h"

#include <builder/Builder.h>

#include <common/BF.h>

#include <computer/BaseEnvironment.h>
#include <computer/ExecutionEnvironment.h>
#include <computer/PathConditionProcessor.h>

#include <fml/executable/ExecutableQuery.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>

#include <server/grpc/SymbexServerExpressionBuilder.h>


namespace sep
{

ExecutionContext * SymbexServerHelper::searchContext(
		const ListOfExecutionContext & relativeRootEC, std::uint32_t ctxID)
{
	ExecutionContext * foundEC = nullptr;

	for( const auto initEC : relativeRootEC )
	{
		AVM_OS_DEBUG << "Initial EC : " << initEC->getIdNumber();

		foundEC = const_cast< ExecutionContext * >(
				IDebugProcessorHelper::searchContext(initEC, ctxID) );
		if( foundEC != nullptr )
		{
AVM_OS_DEBUG << "  --> FOUND ec_id: " << ctxID << " !!!!!!!!!!" << std::endl;
			break;
		}
		else
		{
AVM_OS_DEBUG << "  --> NOT FOUND ec_id: " << ctxID << " ??????????" << std::endl << std::endl;
		}
	}

	return foundEC;
}

grpc::RuntimeStatusTree* SymbexServerHelper::runtimeStatusTree(const ExecutionContext* ec){
	grpc::RuntimeStatusTree* result = new grpc::RuntimeStatusTree();
	SymbexServerHelper::runtimeStatusTree_aux(result,ec, ec->getExecutionData().getSystemRuntime());
	return result;
}

void SymbexServerHelper::runtimeStatusTree_aux(grpc::RuntimeStatusTree* result, const ExecutionContext* ec,const RuntimeForm& rtf){
	grpc::SingleRuntimeStatus* status = result->mutable_runtime_status() ;
	std::string runtimeID = rtf.getFullyQualifiedNameID();				
	status->set_runtime_id(runtimeID);
	PROCESS_EVAL_STATE runtimeState = ec->getExecutionData().getRuntimeFormState(rtf.getRID());
	status->set_runtime_state(SymbexServerHelper::to_grpcProcesState(runtimeState));
	//TODO add the children status
	if (rtf.hasChild()){
		TableOfRuntimeID::const_iterator itChildRID;
		for(itChildRID = rtf.beginChild(); itChildRID != rtf.endChild() ; itChildRID++ ){
			const RuntimeForm& child_rtf =ec->getExecutionData().getRuntime(*itChildRID);
			grpc::RuntimeStatusTree* child_status= result->add_children_status();
			SymbexServerHelper::runtimeStatusTree_aux( child_status,ec,child_rtf);
		}
	}
}

bool SymbexServerHelper::setVariableValue( ExecutableQuery & XQuery,
		BaseEnvironment & ENV, ExecutionContext & inputEC,
		const ::google::protobuf::RepeatedPtrField<
				::sep::grpc::VariableValuePair > & variable_value)
{
	AVM_OS_DEBUG << "\tvariable_value {" << std::endl;
	for( const auto & pair : variable_value )
	{
		const std::string & variable_id = pair.variable_id();

		BF variable = XQuery.getVariableByQualifiedNameID(variable_id);
		if( variable.invalid() )
		{
			return false;
		}

		BF value = SymbexServerExpressionBuilder::from_grpc(XQuery, inputEC, pair.value() );
		if( value.invalid() )
		{
			AVM_OS_DEBUG << "\t\tFAIL to convert gRPC Expression to Symbex Expression !" << std::endl;
			return false;
		}

		AVM_OS_DEBUG << "\t\tvariable: " << variable_id << std::endl
				<< "\t\tvalue   : " << value.str() << std::endl;

		const InstanceOfData & instanceVar = variable.to< InstanceOfData >();
		if( instanceVar.getModifier().hasNatureMacro() && value.is< AvmCode >())
		{
			value = ENV.getBuilder().compileExpression(value);
		}

		if( not ENV.setRvalue(inputEC.getwExecutionData(), instanceVar, value) )
		{
			AVM_OS_DEBUG << "\t\tFAIL to setRvalue !" << std::endl;

			return false;
		}
	}
	AVM_OS_DEBUG << "\t}" << std::endl << std::endl;

	return true;
}


bool SymbexServerHelper::addCondtion(
		ExecutableQuery & XQuery, ExecutionEnvironment & ENV,
		ExecutionContext & inputEC, const ::sep::grpc::Expression & condition)
{
	BF symbexCondition =
			SymbexServerExpressionBuilder::from_grpc(XQuery, inputEC, condition );
	if( symbexCondition.invalid() )
	{
		AVM_OS_DEBUG << "\t\tFAIL to convert gRPC Expression< condition > "
				"to Symbex Expression< condition > !" << std::endl;
		return false;
	}

	if( ! PathConditionProcessor::appendPathCondition(ENV,
			inputEC.getwExecutionData(), symbexCondition) )
	{
		AVM_OS_DEBUG << "\t\tFAIL to append Condition in Path Condition !" << std::endl;
		return false;
	}

	return true;
}


::sep::grpc::PROCESS_STATE SymbexServerHelper::to_grpcProcesState(const sep::PROCESS_EVAL_STATE & pes){
	return 	::sep::grpc::PROCESS_STATE(pes);
}

::sep::grpc::DataType SymbexServerHelper::to_grpcDataType(
		const BaseTypeSpecifier & typeSpecifier)
{
	switch( typeSpecifier.getTypeSpecifierKind() )
	{
		case TYPE_BOOLEAN_SPECIFIER:
			return ::sep::grpc::DataType::BOOLEAN;

		case TYPE_CHARACTER_SPECIFIER:
		case TYPE_STRING_SPECIFIER:
			return ::sep::grpc::DataType::STRING;

		case TYPE_INTEGER_SPECIFIER:
		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_POS_INTEGER_SPECIFIER:
			return ::sep::grpc::DataType::INTEGER;

		case TYPE_RATIONAL_SPECIFIER:
		case TYPE_URATIONAL_SPECIFIER:
		case TYPE_POS_RATIONAL_SPECIFIER:
			return ::sep::grpc::DataType::RATIONAL;

		case TYPE_FLOAT_SPECIFIER:
		case TYPE_UFLOAT_SPECIFIER:
		case TYPE_POS_FLOAT_SPECIFIER:
			return ::sep::grpc::DataType::FLOAT;

		case TYPE_REAL_SPECIFIER:
		case TYPE_UREAL_SPECIFIER:
		case TYPE_POS_REAL_SPECIFIER:
			return ::sep::grpc::DataType::FLOAT;

		case TYPE_INTERVAL_SPECIFIER:
			return to_grpcDataType(
					typeSpecifier.to< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier());


		case TYPE_CLOCK_SPECIFIER:
		case TYPE_TIME_SPECIFIER:
		case TYPE_CONTINUOUS_TIME_SPECIFIER:
		case TYPE_DENSE_TIME_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:
			return to_grpcDataType(
					typeSpecifier.to< ContainerTypeSpecifier >().getContentsTypeSpecifier());


		case TYPE_MACHINE_SPECIFIER:
		case TYPE_PORT_SPECIFIER:
		case TYPE_BUFFER_SPECIFIER:
		case TYPE_MESSAGE_SPECIFIER:
		case TYPE_OPERATOR_SPECIFIER:
		case TYPE_AVMCODE_SPECIFIER:

		case TYPE_ENUM_SPECIFIER:

		case TYPE_ARRAY_SPECIFIER:
		case TYPE_CLASS_SPECIFIER:

		case TYPE_UNIVERSAL_SPECIFIER:

		default:
			return ::sep::grpc::DataType::ANY;
	}
}

bool SymbexServerHelper::setCreatedSymbols(
		const ExecutionContext & inputEC, const ExecutionContext & outputEC,
		::sep::grpc::SymbexEvalRunnableBasicReply * response)
{
	std::size_t oldParameterSize = inputEC.getExecutionData()
			.getParametersRuntimeForm().getParameters().size();
	std::size_t offset = 0;
	for( const auto & symbol :
			outputEC.getExecutionData().getParametersRuntimeForm().getParameters() )
	{
		if( offset++ >= oldParameterSize )
		{
			const InstanceOfData & parameter = symbol.to< InstanceOfData >();

			std::string symbol_id = parameter.getFullyQualifiedNameID();

			std::string::size_type pos = symbol_id.rfind(':');
			if( pos != std::string::npos )
			{
				symbol_id = symbol_id.substr(pos + 1);
			}

			::sep::grpc::TypedSymbol * typedSymbol = response->add_created_symbols();

			typedSymbol->set_symbol_id( symbol_id );

			typedSymbol->set_type( to_grpcDataType(parameter.getTypeSpecifier()) );

AVM_OS_DEBUG << typedSymbol->DebugString() << std::endl;
		}
	}

	return true;

}


} /* namespace sep */

#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */

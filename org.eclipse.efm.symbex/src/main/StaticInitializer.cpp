/*******************************************************************************
 * Copyright (c) 2019 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 mai 2019
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "StaticInitializer.h"

#include <base/ClassKindInfo.h>
#include <base/InstanceCounter.h>

#include <builder/Builder.h>

#include <collection/Bitset.h>

#include <common/AvmObject.h>
#include <common/Element.h>
#include <common/BF.h>
#include <common/RunnableElement.h>

#include <computer/BaseEnvironment.h>
#include <computer/EvaluationEnvironment.h>
#include <computer/EnvironmentFactory.h>
#include <computer/ExecutionEnvironment.h>
#include <computer/instruction/InstructionEnvironment.h>
#include <computer/primitive/AvmCommunicationRdvPrimitive.h>

#include  <famcore/api/AbstractProcessorUnit.h>

#include  <famcore/api/ExtenderProcessorUnit.h>
#include  <famcore/FormulaCoverageFilter.h>

#include <fml/common/BehavioralElement.h>
#include <fml/common/PropertyElement.h>
#include <fml/common/ObjectElement.h>

#include <fml/builtin/Boolean.h>
#include <fml/builtin/BuiltinForm.h>
#include <fml/builtin/Character.h>
#include <fml/builtin/Identifier.h>
#include <fml/builtin/QualifiedIdentifier.h>
#include <fml/builtin/String.h>

#include <fml/buffer/BaseBufferQueue.h>
#include <fml/buffer/BroadcastBuffer.h>
#include <fml/buffer/FifoBuffer.h>
#include <fml/buffer/LifoBuffer.h>
#include <fml/buffer/MultiFifoBuffer.h>
#include <fml/buffer/MultiLifoBuffer.h>
#include <fml/buffer/RamBuffer.h>
#include <fml/buffer/SetBuffer.h>

#include <fml/executable/AvmLambda.h>
#include <fml/executable/AvmProgram.h>
#include <fml/executable/AvmTransition.h>
#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/BaseAvmProgram.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfConnector.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/Router.h>
#include <fml/executable/RoutingData.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>
#include <fml/expression/BuiltinQueue.h>
#include <fml/expression/BuiltinContainer.h>
#include <fml/expression/ExpressionFactory.h>

#include <fml/lib/AvmLang.h>

#include <fml/numeric/Number.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Buffer.h>
#include <fml/infrastructure/Channel.h>
#include <fml/infrastructure/ComPoint.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/ComRoute.h>
#include <fml/infrastructure/Connector.h>
#include <fml/infrastructure/DataType.h>
#include <fml/infrastructure/Function.h>
//#include <infrastructure/Instance.h>
#include <fml/infrastructure/InteractionPart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/ModelOfComputationPart.h>
#include <fml/infrastructure/Package.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/PropertyPart.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/System.h>
#include <fml/infrastructure/Transition.h>
#include <fml/infrastructure/Variable.h>

#include <fml/numeric/Float.h>
#include <fml/numeric/Integer.h>
#include <fml/numeric/Number.h>
#include <fml/numeric/Rational.h>

#include <fml/operator/Operator.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/ExecutionInformation.h>
#include <fml/runtime/ExecutionLocation.h>
#include <fml/runtime/ExecutionSynchronizationPoint.h>
#include <fml/runtime/LocalRuntime.h>
#include <fml/runtime/Message.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>
#include <fml/runtime/RuntimeLib.h>

#include <fml/symbol/Symbol.h>
#include <fml/symbol/TableOfSymbol.h>

#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/BaseSymbolTypeSpecifier.h>
#include <fml/type/ClassTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>
#include <fml/type/TableOfTypeSpecifier.h>
#include <fml/type/TypeAliasSpecifier.h>
#include <fml/type/TypeManager.h>
#include <fml/type/TypeSpecifier.h>
#include <fml/type/UnionTypeSpecifier.h>

#include <fml/workflow/UniFormIdentifier.h>
#include <fml/workflow/WObject.h>

#include <printer/OutStream.h>

#include <solver/api/SolverFactory.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// INITIALIZATION / DESTRUCTION  INVARIANT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


#define INIT_CLASS_KIND_INFO( T )  \
	do { \
		ClassKindInfoInitializer::classKindInfo< T >().mNAME = #T; \
	} while( false )


/**
 * CONSTRUCTOR
 * Default
 * Ensures equality between ENUM_CLASS_KIND literal
 * and ClassKindInfo::mKIND of base classes !
 * Due to dependencies, implementation in main/StaticInitializer
 */
ClassKindInfoInitializer::ClassKindInfoInitializer()
{
	if( (0 == NIFTY_COUNTER++) && (ClassKindInfo::TYPE_UNDEFINED_INFO == nullptr) )
	{
		// STATIC INITIALIZATION DEPENDANCY
		CKI_TABLE = new std::vector< ClassKindInfo * >();

		ClassKindInfo::TYPE_UNDEFINED_INFO =
				new ClassKindInfo(TYPE_UNDEFINED_ID, "#undefined", "#undefined");

		////////////////////////////////////////////////////////////////////////
		//PREDEFINED CLASS KIND w.r.t. ENUM_CLASS_KIND ORDER
		////////////////////////////////////////////////////////////////////////

		// BUILTIN
		INIT_CLASS_KIND_INFO( Boolean   );

		INIT_CLASS_KIND_INFO( Character );

		INIT_CLASS_KIND_INFO( Integer   );

		INIT_CLASS_KIND_INFO( Rational  );

		INIT_CLASS_KIND_INFO( Float     );

		INIT_CLASS_KIND_INFO( String    );

		INIT_CLASS_KIND_INFO( Identifier          );
		INIT_CLASS_KIND_INFO( QualifiedIdentifier );

		// OPERATOR
		INIT_CLASS_KIND_INFO( Operator );

		// EXPRESSION , STATEMENT
		INIT_CLASS_KIND_INFO( AvmCode  );

		// EXECUTABLE OBJECT INSTANCE
		INIT_CLASS_KIND_INFO( InstanceOfBuffer    );
		INIT_CLASS_KIND_INFO( InstanceOfConnector );
		INIT_CLASS_KIND_INFO( InstanceOfData      );
		INIT_CLASS_KIND_INFO( InstanceOfMachine   );
		INIT_CLASS_KIND_INFO( InstanceOfPort      );

		// EXECUTABLE OBJECT
		INIT_CLASS_KIND_INFO( AvmLambda           );
		INIT_CLASS_KIND_INFO( AvmProgram          );
		INIT_CLASS_KIND_INFO( AvmTransition       );

		INIT_CLASS_KIND_INFO( ExecutableForm      );
		INIT_CLASS_KIND_INFO( ExecutableSystem    );

		// RUNTIME OBJECT
		INIT_CLASS_KIND_INFO( RuntimeID           );
		INIT_CLASS_KIND_INFO( RuntimeForm         );

		// EXECUTION OBJECT
		INIT_CLASS_KIND_INFO( ExecutionConfiguration );

		INIT_CLASS_KIND_INFO( ExecutionData       );
		INIT_CLASS_KIND_INFO( ExecutionContext    );

		// WORKFLOW CONFIGURATION
		INIT_CLASS_KIND_INFO( WObject );

		// LIA or FSP
		INIT_CLASS_KIND_INFO( UniFormIdentifier );

		// XLIA or XFSP
		INIT_CLASS_KIND_INFO( Buffer     );
		INIT_CLASS_KIND_INFO( Channel    );
		INIT_CLASS_KIND_INFO( ComPoint   );
		INIT_CLASS_KIND_INFO( ComRoute   );
		INIT_CLASS_KIND_INFO( Connector  );
		INIT_CLASS_KIND_INFO( Machine    );
//		INIT_CLASS_KIND_INFO( Instance   );
		INIT_CLASS_KIND_INFO( Package    );
		INIT_CLASS_KIND_INFO( Port       );
		INIT_CLASS_KIND_INFO( Routine    );
		INIT_CLASS_KIND_INFO( System     );
		INIT_CLASS_KIND_INFO( Transition );
		INIT_CLASS_KIND_INFO( Variable   );

		// DATA TYPE
		INIT_CLASS_KIND_INFO( DataType   );

		// FUNCTION
		INIT_CLASS_KIND_INFO( Function   );

		// TYPE SPECIFIER
		INIT_CLASS_KIND_INFO( BaseTypeSpecifier );

		// ARRAY
		INIT_CLASS_KIND_INFO( ArrayBoolean    );
		INIT_CLASS_KIND_INFO( ArrayCharacter  );
		INIT_CLASS_KIND_INFO( ArrayInteger    );
		INIT_CLASS_KIND_INFO( ArrayRational   );
		INIT_CLASS_KIND_INFO( ArrayFloat      );
		INIT_CLASS_KIND_INFO( ArrayString     );

		INIT_CLASS_KIND_INFO( ArrayIdentifier );
		INIT_CLASS_KIND_INFO( ArrayQualifiedIdentifier );

		INIT_CLASS_KIND_INFO( ArrayBF );

		// CONTAINER
		INIT_CLASS_KIND_INFO( BuiltinVector   );
		INIT_CLASS_KIND_INFO( BuiltinReverseVector );
		INIT_CLASS_KIND_INFO( BuiltinList     );
		INIT_CLASS_KIND_INFO( BuiltinSet      );
		INIT_CLASS_KIND_INFO( BuiltinBag      );
		INIT_CLASS_KIND_INFO( BuiltinFifo     );
		INIT_CLASS_KIND_INFO( BuiltinLifo     );

		// BUFFER
		INIT_CLASS_KIND_INFO( FifoBuffer      );
		INIT_CLASS_KIND_INFO( LifoBuffer      );
		INIT_CLASS_KIND_INFO( MultiFifoBuffer );
		INIT_CLASS_KIND_INFO( MultiLifoBuffer );
		INIT_CLASS_KIND_INFO( MultisetBuffer  );
		INIT_CLASS_KIND_INFO( SetBuffer       );
		INIT_CLASS_KIND_INFO( BroadcastBuffer );
		INIT_CLASS_KIND_INFO( RamBuffer       );

		// COM
		INIT_CLASS_KIND_INFO( Message         );
		INIT_CLASS_KIND_INFO( Router          );
		INIT_CLASS_KIND_INFO( RoutingData     );

		// OTHER
		INIT_CLASS_KIND_INFO( FormulaData     );

		// EXECUTION TRACE
		INIT_CLASS_KIND_INFO( TracePoint      );
		INIT_CLASS_KIND_INFO( TraceSequence   );

		// Uncomment for debug trace
//		toStreamTable("ClassKindInfoInitializer< constructor >");
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

#define CHECK_CLASS_KIND_INFO( T , K )  \
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( CLASS_KIND_T( T ) == ((class_kind_t) K) )  \
		<< ClassKindInfoImpl< T >::info() << " =/= ENUM_CLASS_KIND::"  << #K   \
		<< "< kind: " << ((std::size_t) K) << " > !!!"  << SEND_EXIT;

/**
 * Loader
 * Checking equality between ENUM_CLASS_KIND literal
 * and ClassKindInfo::mKIND of base classes !
 * Mandatory, call by load()
 */
void ClassKindInfoInitializer::checkingAssertions()
{
//	std::cout << "checkClassKindInfo_w_r_t_EnumClassKind :>" << std::endl;

	// BUILTIN
	CHECK_CLASS_KIND_INFO( Boolean    , FORM_BUILTIN_BOOLEAN_KIND    );

	CHECK_CLASS_KIND_INFO( Character  , FORM_BUILTIN_CHARACTER_KIND  );

	CHECK_CLASS_KIND_INFO( Integer    , FORM_BUILTIN_INTEGER_KIND    );
	CHECK_CLASS_KIND_INFO( Rational   , FORM_BUILTIN_RATIONAL_KIND   );
	CHECK_CLASS_KIND_INFO( Float      , FORM_BUILTIN_FLOAT_KIND      );

	CHECK_CLASS_KIND_INFO( String     , FORM_BUILTIN_STRING_KIND     );
	CHECK_CLASS_KIND_INFO( Identifier , FORM_BUILTIN_IDENTIFIER_KIND );
	CHECK_CLASS_KIND_INFO( QualifiedIdentifier, FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND );

	// OPERATOR
	CHECK_CLASS_KIND_INFO( Operator , FORM_OPERATOR_KIND );

	// EXPRESSION , STATEMENT
	CHECK_CLASS_KIND_INFO( AvmCode  , FORM_AVMCODE_KIND  );

	// EXECUTABLE OBJECT INSTANCE
	CHECK_CLASS_KIND_INFO( InstanceOfBuffer    , FORM_INSTANCE_BUFFER_KIND    );
	CHECK_CLASS_KIND_INFO( InstanceOfConnector , FORM_INSTANCE_CONNECTOR_KIND );
	CHECK_CLASS_KIND_INFO( InstanceOfData      , FORM_INSTANCE_DATA_KIND      );
	CHECK_CLASS_KIND_INFO( InstanceOfMachine   , FORM_INSTANCE_MACHINE_KIND   );
	CHECK_CLASS_KIND_INFO( InstanceOfPort      , FORM_INSTANCE_PORT_KIND      );

	// EXECUTABLE OBJECT
	CHECK_CLASS_KIND_INFO( AvmLambda           , FORM_AVMLAMBDA_KIND          );
	CHECK_CLASS_KIND_INFO( AvmProgram          , FORM_AVMPROGRAM_KIND         );
	CHECK_CLASS_KIND_INFO( AvmTransition       , FORM_AVMTRANSITION_KIND      );
	CHECK_CLASS_KIND_INFO( ExecutableForm      , FORM_EXECUTABLE_MACHINE_KIND );
	CHECK_CLASS_KIND_INFO( ExecutableSystem    , FORM_EXECUTABLE_SYSTEM_KIND  );

	// RUNTIME OBJECT
	CHECK_CLASS_KIND_INFO( RuntimeID           , FORM_RUNTIME_ID_KIND );
	CHECK_CLASS_KIND_INFO( RuntimeForm         , FORM_RUNTIME_KIND    );

	// EXECUTION OBJECT
	CHECK_CLASS_KIND_INFO( ExecutionConfiguration ,
											FORM_EXECUTION_CONFIGURATION_KIND );
	CHECK_CLASS_KIND_INFO( ExecutionData       , FORM_EXECUTION_DATA_KIND     );
	CHECK_CLASS_KIND_INFO( ExecutionContext    , FORM_EXECUTION_CONTEXT_KIND  );

	// WORKFLOW CONFIGURATION
	CHECK_CLASS_KIND_INFO( WObject   , FORM_WOBJECT_KIND     );

	// LIA or FSP
	CHECK_CLASS_KIND_INFO( UniFormIdentifier , FORM_UFI_KIND );

	// XLIA or XFSP
	CHECK_CLASS_KIND_INFO( Buffer       , FORM_XFSP_BUFFER_KIND     );
	CHECK_CLASS_KIND_INFO( Channel      , FORM_XFSP_CHANNEL_KIND    );
	CHECK_CLASS_KIND_INFO( ComPoint     , FORM_XFSP_COM_POINT_KIND  );
	CHECK_CLASS_KIND_INFO( ComRoute     , FORM_XFSP_COM_ROUTE_KIND  );
	CHECK_CLASS_KIND_INFO( Connector    , FORM_XFSP_CONNECTOR_KIND  );
	CHECK_CLASS_KIND_INFO( Machine      , FORM_XFSP_MACHINE_KIND    );
//	CHECK_CLASS_KIND_INFO( Instance     , FORM_XFSP_INSTANCE_KIND   );
	CHECK_CLASS_KIND_INFO( Package      , FORM_XFSP_PACKAGE_KIND    );
	CHECK_CLASS_KIND_INFO( Port         , FORM_XFSP_PORT_KIND       );
	CHECK_CLASS_KIND_INFO( Routine      , FORM_XFSP_ROUTINE_KIND    );
	CHECK_CLASS_KIND_INFO( System       , FORM_XFSP_SYSTEM_KIND     );
	CHECK_CLASS_KIND_INFO( Transition   , FORM_XFSP_TRANSITION_KIND );
	CHECK_CLASS_KIND_INFO( Variable     , FORM_XFSP_VARIABLE_KIND   );

	// DATA TYPE
	CHECK_CLASS_KIND_INFO( DataType     , FORM_XFSP_DATATYPE_KIND   );

	// FUNCTION
	CHECK_CLASS_KIND_INFO( Function     , FORM_XFSP_FUNCTION_KIND   );

	// TYPE SPECIFIER
	CHECK_CLASS_KIND_INFO( BaseTypeSpecifier, FORM_TYPE_SPECIFIER_KIND   );

	// ARRAY
	CHECK_CLASS_KIND_INFO( ArrayBoolean     , FORM_ARRAY_BOOLEAN_KIND    );
	CHECK_CLASS_KIND_INFO( ArrayCharacter   , FORM_ARRAY_CHARACTER_KIND  );
	CHECK_CLASS_KIND_INFO( ArrayInteger     , FORM_ARRAY_INTEGER_KIND    );
	CHECK_CLASS_KIND_INFO( ArrayRational    , FORM_ARRAY_RATIONAL_KIND   );
	CHECK_CLASS_KIND_INFO( ArrayFloat       , FORM_ARRAY_FLOAT_KIND      );
	CHECK_CLASS_KIND_INFO( ArrayString      , FORM_ARRAY_STRING_KIND     );
	CHECK_CLASS_KIND_INFO( ArrayIdentifier  , FORM_ARRAY_IDENTIFIER_KIND );
	CHECK_CLASS_KIND_INFO( ArrayQualifiedIdentifier ,
								    FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND );
	CHECK_CLASS_KIND_INFO( ArrayBF          , FORM_ARRAY_BF_KIND         );

	// CONTAINER
	CHECK_CLASS_KIND_INFO( BuiltinVector , FORM_CONTAINER_VECTOR_KIND    );
	CHECK_CLASS_KIND_INFO( BuiltinReverseVector ,
									FORM_CONTAINER_REVERSE_VECTOR_KIND   );
	CHECK_CLASS_KIND_INFO( BuiltinList   , FORM_CONTAINER_LIST_KIND      );
	CHECK_CLASS_KIND_INFO( BuiltinSet    , FORM_CONTAINER_SET_KIND       );
	CHECK_CLASS_KIND_INFO( BuiltinBag    , FORM_CONTAINER_BAG_KIND       );
	CHECK_CLASS_KIND_INFO( BuiltinFifo   , FORM_CONTAINER_FIFO_KIND      );
	CHECK_CLASS_KIND_INFO( BuiltinLifo   , FORM_CONTAINER_LIFO_KIND      );

	// BUFFER
	CHECK_CLASS_KIND_INFO( FifoBuffer      , FORM_BUFFER_FIFO_KIND       );
	CHECK_CLASS_KIND_INFO( LifoBuffer      , FORM_BUFFER_LIFO_KIND       );
	CHECK_CLASS_KIND_INFO( MultiFifoBuffer , FORM_BUFFER_MULTI_FIFO_KIND );
	CHECK_CLASS_KIND_INFO( MultiLifoBuffer , FORM_BUFFER_MULTI_LIFO_KIND );

	CHECK_CLASS_KIND_INFO( MultisetBuffer  , FORM_BUFFER_MULTISET_KIND   );
	CHECK_CLASS_KIND_INFO( SetBuffer       , FORM_BUFFER_SET_KIND        );

	CHECK_CLASS_KIND_INFO( BroadcastBuffer , FORM_BUFFER_BROADCAST_KIND  );
	CHECK_CLASS_KIND_INFO( RamBuffer       , FORM_BUFFER_RAM_KIND        );

	// COM
	CHECK_CLASS_KIND_INFO( Message         , FORM_MESSAGE_KIND           );
	CHECK_CLASS_KIND_INFO( Router          , FORM_ROUTER_KIND            );
	CHECK_CLASS_KIND_INFO( RoutingData     , FORM_ROUTING_DATA_KIND      );

	// OTHER
	CHECK_CLASS_KIND_INFO( FormulaData , FORM_EXEC_FILTER_FORMULA_DATA_KIND );

	// EXECUTION TRACE
	CHECK_CLASS_KIND_INFO( TracePoint      , FORM_TRACE_POINT_KIND       );
	CHECK_CLASS_KIND_INFO( TraceSequence   , FORM_TRACE_SEQUENCE_KIND    );

	//	std::cout << "end" << std::endl;
}



//ClassKindInfoInitializer::dispose:>
// typeinfo<   0 , #undefined::#undefined >
// typeinfo<   1 , Boolean::N3sep7BooleanE >
// typeinfo<   2 , Character::N3sep9CharacterE >
// typeinfo<   3 , Integer::N3sep7IntegerE >
// typeinfo<   4 , Rational::N3sep8RationalE >
// typeinfo<   5 , Float::N3sep5FloatE >
// typeinfo<   6 , String::N3sep6StringE >
// typeinfo<   7 , Identifier::N3sep10IdentifierE >
// typeinfo<   8 , QualifiedIdentifier::N3sep19QualifiedIdentifierE >
// typeinfo<   9 , Operator::N3sep8OperatorE >
// typeinfo<  10 , AvmCode::N3sep7AvmCodeE >
// typeinfo<  11 , InstanceOfBuffer::N3sep16InstanceOfBufferE >
// typeinfo<  12 , InstanceOfConnector::N3sep19InstanceOfConnectorE >
// typeinfo<  13 , InstanceOfData::N3sep14InstanceOfDataE >
// typeinfo<  14 , InstanceOfMachine::N3sep17InstanceOfMachineE >
// typeinfo<  15 , InstanceOfPort::N3sep14InstanceOfPortE >
// typeinfo<  16 , AvmLambda::N3sep9AvmLambdaE >
// typeinfo<  17 , AvmProgram::N3sep10AvmProgramE >
// typeinfo<  18 , AvmTransition::N3sep13AvmTransitionE >
// typeinfo<  19 , ExecutableForm::N3sep14ExecutableFormE >
// typeinfo<  20 , ExecutableSystem::N3sep16ExecutableSystemE >
// typeinfo<  21 , RuntimeID::N3sep9RuntimeIDE >
// typeinfo<  22 , RuntimeForm::N3sep11RuntimeFormE >
// typeinfo<  23 , ExecutionConfiguration::N3sep22ExecutionConfigurationE >
// typeinfo<  24 , ExecutionData::N3sep13ExecutionDataE >
// typeinfo<  25 , ExecutionContext::N3sep16ExecutionContextE >
// typeinfo<  26 , WObject::N3sep7WObjectE >
// typeinfo<  27 , UniFormIdentifier::N3sep17UniFormIdentifierE >
// typeinfo<  28 , Buffer::N3sep6BufferE >
// typeinfo<  29 , Channel::N3sep7ChannelE >
// typeinfo<  30 , ComPoint::N3sep8ComPointE >
// typeinfo<  31 , ComRoute::N3sep8ComRouteE >
// typeinfo<  32 , Connector::N3sep9ConnectorE >
// typeinfo<  33 , Machine::N3sep7MachineE >
// typeinfo<  34 , Package::N3sep7PackageE >
// typeinfo<  35 , Port::N3sep4PortE >
// typeinfo<  36 , Routine::N3sep7RoutineE >
// typeinfo<  37 , System::N3sep6SystemE >
// typeinfo<  38 , Transition::N3sep10TransitionE >
// typeinfo<  39 , Variable::N3sep8VariableE >
// typeinfo<  40 , DataType::N3sep8DataTypeE >
// typeinfo<  41 , Function::N3sep8FunctionE >
// typeinfo<  42 , BaseTypeSpecifier::N3sep17BaseTypeSpecifierE >
// typeinfo<  43 , ArrayBoolean::N3sep12ArrayBooleanE >
// typeinfo<  44 , ArrayCharacter::N3sep14ArrayCharacterE >
// typeinfo<  45 , ArrayInteger::N3sep12ArrayIntegerE >
// typeinfo<  46 , ArrayRational::N3sep13ArrayRationalE >
// typeinfo<  47 , ArrayFloat::N3sep10ArrayFloatE >
// typeinfo<  48 , ArrayString::N3sep11ArrayStringE >
// typeinfo<  49 , ArrayIdentifier::N3sep15ArrayIdentifierE >
// typeinfo<  50 , ArrayQualifiedIdentifier::N3sep24ArrayQualifiedIdentifierE >
// typeinfo<  51 , ArrayBF::N3sep7ArrayBFE >
// typeinfo<  52 , BuiltinVector::N3sep13BuiltinVectorE >
// typeinfo<  53 , BuiltinReverseVector::N3sep20BuiltinReverseVectorE >
// typeinfo<  54 , BuiltinList::N3sep11BuiltinListE >
// typeinfo<  55 , BuiltinSet::N3sep10BuiltinSetE >
// typeinfo<  56 , BuiltinBag::N3sep10BuiltinBagE >
// typeinfo<  57 , BuiltinFifo::N3sep11BuiltinFifoE >
// typeinfo<  58 , BuiltinLifo::N3sep11BuiltinLifoE >
// typeinfo<  59 , FifoBuffer::N3sep10FifoBufferE >
// typeinfo<  60 , LifoBuffer::N3sep10LifoBufferE >
// typeinfo<  61 , MultiFifoBuffer::N3sep15MultiFifoBufferE >
// typeinfo<  62 , MultiLifoBuffer::N3sep15MultiLifoBufferE >
// typeinfo<  63 , MultisetBuffer::N3sep14MultisetBufferE >
// typeinfo<  64 , SetBuffer::N3sep9SetBufferE >
// typeinfo<  65 , BroadcastBuffer::N3sep15BroadcastBufferE >
// typeinfo<  66 , RamBuffer::N3sep9RamBufferE >
// typeinfo<  67 , Message::N3sep7MessageE >
// typeinfo<  68 , Router::N3sep6RouterE >
// typeinfo<  69 , RoutingData::N3sep11RoutingDataE >
// typeinfo<  70 , FormulaData::N3sep11FormulaDataE >
// typeinfo<  71 , TracePoint::N3sep10TracePointE >
// typeinfo<  72 , TraceSequence::N3sep13TraceSequenceE >
// typeinfo<  73 , N3sep17ExecutionLocationE::N3sep17ExecutionLocationE >
// typeinfo<  74 , N3sep12LocalRuntimeE::N3sep12LocalRuntimeE >
// typeinfo<  75 , N3sep12PropertyPartE::N3sep12PropertyPartE >
// typeinfo<  76 , N3sep21ParametersRuntimeFormE::N3sep21ParametersRuntimeFormE >
// typeinfo<  77 , N3sep15GenericInfoDataE::N3sep15GenericInfoDataE >
// typeinfo<  78 , N3sep20ExecutionInformationE::N3sep20ExecutionInformationE >
// typeinfo<  79 , N3sep22ExecutionContextHeaderE::N3sep22ExecutionContextHeaderE >
// typeinfo<  80 , N3sep14BehavioralPartE::N3sep14BehavioralPartE >
// typeinfo<  81 , N3sep13CompositePartE::N3sep13CompositePartE >
// typeinfo<  82 , N3sep17EnumTypeSpecifierE::N3sep17EnumTypeSpecifierE >
// typeinfo<  83 , N3sep21IntervalTypeSpecifierE::N3sep21IntervalTypeSpecifierE >
// typeinfo<  84 , N3sep19ChoiceTypeSpecifierE::N3sep19ChoiceTypeSpecifierE >
// typeinfo<  85 , N3sep18ClassTypeSpecifierE::N3sep18ClassTypeSpecifierE >
// typeinfo<  86 , N3sep22ContainerTypeSpecifierE::N3sep22ContainerTypeSpecifierE >
// typeinfo<  87 , N3sep18TypeAliasSpecifierE::N3sep18TypeAliasSpecifierE >
// typeinfo<  88 , N3sep18UnionTypeSpecifierE::N3sep18UnionTypeSpecifierE >
// typeinfo<  89 , N3sep27SymbexControllerUnitManagerE::N3sep27SymbexControllerUnitManagerE >
// typeinfo<  90 , N3sep13ConfigurationE::N3sep13ConfigurationE >
// typeinfo<  91 , N3sep29SecurityAnalysisProcessorInfoE::N3sep29SecurityAnalysisProcessorInfoE >
// typeinfo<  92 , N3sep25FormulaCoverageFilterInfoE::N3sep25FormulaCoverageFilterInfoE >
// typeinfo<  93 , N3sep22HitOrJumpObjectiveInfoE::N3sep22HitOrJumpObjectiveInfoE >
// typeinfo<  94 , N3sep24OfflineTestProcessorInfoE::N3sep24OfflineTestProcessorInfoE >
// typeinfo<  95 , N3sep21InstanceSpecifierPartE::N3sep21InstanceSpecifierPartE >
// typeinfo<  96 , N3sep15InteractionPartE::N3sep15InteractionPartE >
// typeinfo<  97 , N3sep22ModelOfComputationPartE::N3sep22ModelOfComputationPartE >
// typeinfo<  98 , N3sep16AvmTracePropertyE::N3sep16AvmTracePropertyE >
// typeinfo<  99 , N3sep23AvmCoverageAbstractViewE::N3sep23AvmCoverageAbstractViewE >
// typeinfo< 100 , N3sep21AbstractProcessorUnitE::N3sep21AbstractProcessorUnitE >
// typeinfo< 101 , N3sep23CompositeControllerUnitE::N3sep23CompositeControllerUnitE >
// typeinfo< 102 , N3sep15RunnableElementE::N3sep15RunnableElementE >
//CKI_TABLE.size: 103
//CKI_NEW_ID    : 103
//NIFTY_COUNTER : 312
//end



/**
 * Global report counter usage function
 * reportInstanceCounterUsage(...)
 */

#define AVM_INSTANCE_SHOW_COUNTER(ClassName)  \
	InstanceCounter< ClassName >::showCounters(os, #ClassName)

#define AVM_INSTANCE_REPORT_COUNTER(ClassName)  \
	InstanceCounter< ClassName >::reportCounters(os, #ClassName)


#define AVM_SHOW_INSTANCE_COUNT_T(ClassName, counter)  \
	if( counter > 0 ) do {  \
		int colSize = 32 - std::strlen(#ClassName);  \
		os << TAB << #ClassName << std::setw((colSize > 0) ? colSize : 1);  \
		os << " :> " << std::setw(6) << counter << EOL_FLUSH;  \
	} while( 0 )



void reportInstanceCounterUsage(
		OutStream & os, const std::string & aMsg, bool forced)
{
//!![MIGRATION]
AVM_IF_DEBUG_LEVEL_FLAG_OR( MEDIUM , REFERENCE_COUNTING , forced )

	os << AVM_TAB_INDENT;

	os << std::endl << "\t" << "***** FORM COUNTER in << " << aMsg
	<< " >> *****" << std::endl;

	AVM_INSTANCE_SHOW_COUNTER(AvmObject);
	AVM_INSTANCE_SHOW_COUNTER(Element  );

	AVM_INSTANCE_SHOW_COUNTER(BF);

	AVM_INSTANCE_SHOW_COUNTER(Symbol       );
	AVM_INSTANCE_SHOW_COUNTER(TypeSpecifier);

	AVM_INSTANCE_SHOW_COUNTER(TableOfSymbol       );
	AVM_INSTANCE_SHOW_COUNTER(TableOfTypeSpecifier);

	AVM_SHOW_INSTANCE_COUNT_T(BF_FROM_ASP, BF::INSTANCE_COUNTER_ASP);

	AVM_INSTANCE_REPORT_COUNTER(AvmCode);
	AVM_INSTANCE_REPORT_COUNTER(BFCode );

	AVM_INSTANCE_REPORT_COUNTER(LocalRuntime );
	AVM_INSTANCE_REPORT_COUNTER(RuntimeForm  );
	AVM_INSTANCE_REPORT_COUNTER(_RuntimeID_  );
	AVM_INSTANCE_REPORT_COUNTER(RuntimeID    );

	AVM_INSTANCE_REPORT_COUNTER(ExecutionContext    );
	AVM_INSTANCE_REPORT_COUNTER(ExecutionData       );
	AVM_INSTANCE_REPORT_COUNTER(ExecutionInformation);
	AVM_INSTANCE_REPORT_COUNTER(GenericInfoData     );

	AVM_INSTANCE_REPORT_COUNTER(WObject);
AVM_ENDIF_DEBUG_LEVEL_FLAG_OR( MEDIUM , REFERENCE_COUNTING )


AVM_IF_DEBUG_LEVEL_FLAG_AND( HIGH , REFERENCE_COUNTING ,
		(AvmObject::INSTANCE_ALIVE > 0) )

	AVM_INSTANCE_REPORT_COUNTER(RunnableElement);

	AVM_INSTANCE_REPORT_COUNTER(AbstractProcessorUnit);

	AVM_INSTANCE_REPORT_COUNTER(Bitset);

	AVM_INSTANCE_REPORT_COUNTER(BuiltinForm);
	AVM_INSTANCE_REPORT_COUNTER(Number     );
	AVM_INSTANCE_REPORT_COUNTER(Identifier );
	AVM_INSTANCE_REPORT_COUNTER(QualifiedIdentifier);

	AVM_INSTANCE_REPORT_COUNTER(ArrayBF        );
	AVM_INSTANCE_REPORT_COUNTER(ArrayBoolean   );
	AVM_INSTANCE_REPORT_COUNTER(ArrayCharacter );
	AVM_INSTANCE_REPORT_COUNTER(ArrayInteger   );
	AVM_INSTANCE_REPORT_COUNTER(ArrayRational  );
	AVM_INSTANCE_REPORT_COUNTER(ArrayFloat     );
	AVM_INSTANCE_REPORT_COUNTER(ArrayString    );
	AVM_INSTANCE_REPORT_COUNTER(ArrayIdentifier);
	AVM_INSTANCE_REPORT_COUNTER(ArrayQualifiedIdentifier);

	AVM_INSTANCE_REPORT_COUNTER(BuiltinContainer );
	AVM_INSTANCE_REPORT_COUNTER(BuiltinList      );
	AVM_INSTANCE_REPORT_COUNTER(BuiltinVector    );
	AVM_INSTANCE_REPORT_COUNTER(BuiltinQueue     );
	AVM_INSTANCE_REPORT_COUNTER(BuiltinFifo      );
	AVM_INSTANCE_REPORT_COUNTER(BuiltinLifo      );
	AVM_INSTANCE_REPORT_COUNTER(BuiltinSet       );
	AVM_INSTANCE_REPORT_COUNTER(BuiltinBag       );

	AVM_INSTANCE_REPORT_COUNTER(UniFormIdentifier);

	AVM_INSTANCE_REPORT_COUNTER(ObjectElement    );
	AVM_INSTANCE_REPORT_COUNTER(PropertyElement  );

	AVM_INSTANCE_REPORT_COUNTER(WObject   );

	AVM_INSTANCE_REPORT_COUNTER(DataType  );
	AVM_INSTANCE_REPORT_COUNTER(Buffer    );
	AVM_INSTANCE_REPORT_COUNTER(Channel   );
	AVM_INSTANCE_REPORT_COUNTER(ComPoint  );
	AVM_INSTANCE_REPORT_COUNTER(ComRoute  );
	AVM_INSTANCE_REPORT_COUNTER(Connector);
	AVM_INSTANCE_REPORT_COUNTER(Machine   );
	AVM_INSTANCE_REPORT_COUNTER(Package   );
	AVM_INSTANCE_REPORT_COUNTER(Port      );
	AVM_INSTANCE_REPORT_COUNTER(Routine   );
	AVM_INSTANCE_REPORT_COUNTER(System    );
	AVM_INSTANCE_REPORT_COUNTER(Transition);
	AVM_INSTANCE_REPORT_COUNTER(Variable  );

	AVM_INSTANCE_REPORT_COUNTER(BehavioralPart );
	AVM_INSTANCE_REPORT_COUNTER(CompositePart  );
	AVM_INSTANCE_REPORT_COUNTER(InteractionPart);
	AVM_INSTANCE_REPORT_COUNTER(ModelOfComputationPart);
	AVM_INSTANCE_REPORT_COUNTER(PropertyPart   );

	AVM_INSTANCE_REPORT_COUNTER(AvmLambda       );
	AVM_INSTANCE_REPORT_COUNTER(AvmProgram      );
	AVM_INSTANCE_REPORT_COUNTER(ExecutableForm  );
	AVM_INSTANCE_REPORT_COUNTER(ExecutableSystem);
	AVM_INSTANCE_REPORT_COUNTER(RoutingData     );

	AVM_INSTANCE_REPORT_COUNTER(BaseEnvironment        );
	AVM_INSTANCE_REPORT_COUNTER(EvaluationEnvironment  );
	AVM_INSTANCE_REPORT_COUNTER(ExecutionEnvironment   );
	AVM_INSTANCE_REPORT_COUNTER(InstructionEnvironment );

	AVM_INSTANCE_REPORT_COUNTER(ExecutionContextHeader );
	AVM_INSTANCE_REPORT_COUNTER(ExecutionContext       );
	AVM_INSTANCE_REPORT_COUNTER(ExecutionData          );
	AVM_INSTANCE_REPORT_COUNTER(ExecutionConfiguration );
	AVM_INSTANCE_REPORT_COUNTER(ExecutionInformation   );
	AVM_INSTANCE_REPORT_COUNTER(GenericInfoData        );

	AVM_INSTANCE_REPORT_COUNTER(ExecutionLocation      );
	AVM_INSTANCE_REPORT_COUNTER(ExecutionSynchronizationPoint);
	AVM_INSTANCE_REPORT_COUNTER(RdvConfigurationData   );

	AVM_INSTANCE_REPORT_COUNTER(TableOfData            );
	AVM_INSTANCE_REPORT_COUNTER(TableOfInstanceOfData  );
	AVM_INSTANCE_REPORT_COUNTER(TableOfAvmProgram      );
	AVM_INSTANCE_REPORT_COUNTER(StackOfLocalRuntime    );
	AVM_INSTANCE_REPORT_COUNTER(TableOfRuntimeFormState);
	AVM_INSTANCE_REPORT_COUNTER(TableOfRuntimeID       );

	AVM_INSTANCE_REPORT_COUNTER(InstanceOfData   );
	AVM_INSTANCE_REPORT_COUNTER(InstanceOfMachine);
	AVM_INSTANCE_REPORT_COUNTER(InstanceOfPort   );
	AVM_INSTANCE_REPORT_COUNTER(InstanceOfBuffer );
	AVM_INSTANCE_REPORT_COUNTER(InstanceOfConnector);
	AVM_INSTANCE_REPORT_COUNTER(BaseInstanceForm );

	AVM_INSTANCE_REPORT_COUNTER(LocalRuntime     );
	AVM_INSTANCE_REPORT_COUNTER(RuntimeForm      );

	AVM_INSTANCE_REPORT_COUNTER(Message          );
	AVM_INSTANCE_REPORT_COUNTER(BaseBufferForm   );
	AVM_INSTANCE_REPORT_COUNTER(Router           );

	AVM_INSTANCE_REPORT_COUNTER(Operator         );

	AVM_INSTANCE_REPORT_COUNTER(BaseTypeSpecifier);

	AVM_INSTANCE_REPORT_COUNTER(TracePoint       );
	AVM_INSTANCE_REPORT_COUNTER(TraceSequence    );
	AVM_INSTANCE_REPORT_COUNTER(TraceFilter      );

	os << END_INDENT;

AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( HIGH , REFERENCE_COUNTING )
}


////////////////////////////////////////////////////////////////////////////////
// LOADER / DISPOSER  API
////////////////////////////////////////////////////////////////////////////////

bool StaticInitializer::mLoadedFlag = false;

void StaticInitializer::load()
{
	if( not mLoadedFlag )
	{
		OutStream::load();

		ClassKindInfoInitializer::load();

		XLIA_SYNTAX::load();

		ExpressionFactory::load();

		TypeManager::load();


		EnvironmentFactory::load();

		Builder::load();

		ExecutableLib::load();

		RuntimeLib::load();

AVM_IF_DEBUG_FLAG( REFERENCE_COUNTING )
	reportInstanceCounterUsage(AVM_OS_LOG, "StaticInitializer::load");
AVM_ENDIF_DEBUG_FLAG( REFERENCE_COUNTING )

		mLoadedFlag = true;
	}
}


void StaticInitializer::dispose()
{
	if( mLoadedFlag )
	{
		EnvironmentFactory::dispose();

		SolverFactory::dispose();

		RuntimeLib::dispose();

		ExecutableLib::dispose();

		Builder::dispose();


		TypeManager::dispose();

		ExpressionFactory::dispose();

		XLIA_SYNTAX::dispose();

AVM_IF_DEBUG_FLAG( REFERENCE_COUNTING )
	reportInstanceCounterUsage(AVM_OS_COUT, "StaticInitializer::dispose");
AVM_ENDIF_DEBUG_FLAG( REFERENCE_COUNTING )

		ClassKindInfoInitializer::dispose();

		OutStream::dispose();
	}
}


} /* namespace sep */

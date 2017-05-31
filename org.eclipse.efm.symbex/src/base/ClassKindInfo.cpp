/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 déc. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ClassKindInfo.h"

#include <common/NamedElement.h>

#include <printer/OutStream.h>

#include <fam/coverage/FormulaCoverageFilter.h>

#include <fml/common/BehavioralElement.h>
#include <fml/common/PropertyElement.h>
#include <fml/common/ObjectElement.h>

#include <fml/builtin/Boolean.h>
#include <fml/builtin/BuiltinForm.h>
#include <fml/builtin/Character.h>
#include <fml/builtin/Identifier.h>
#include <fml/builtin/String.h>

#include <fml/buffer/BaseBufferQueue.h>
#include <fml/buffer/BroadcastBuffer.h>
#include <fml/buffer/FifoBuffer.h>
#include <fml/buffer/LifoBuffer.h>
#include <fml/buffer/MultiFifoBuffer.h>
#include <fml/buffer/MultiLifoBuffer.h>
#include <fml/buffer/MultisetBuffer.h>
#include <fml/buffer/RamBuffer.h>
#include <fml/buffer/SetBuffer.h>

#include <fml/executable/AvmLambda.h>
#include <fml/executable/AvmProgram.h>
#include <fml/executable/AvmTransition.h>
#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/BaseAvmProgram.h>
#include <fml/executable/ComRouteData.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfConnect.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/Router.h>
#include <fml/executable/RoutingData.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/BuiltinQueue.h>
#include <fml/expression/BuiltinContainer.h>
#include <fml/expression/ExpressionFactory.h>

#include <fml/infrastructure/Buffer.h>
#include <fml/infrastructure/Channel.h>
#include <fml/infrastructure/ComPoint.h>
#include <fml/infrastructure/ComRoute.h>
#include <fml/infrastructure/Connector.h>
#include <fml/infrastructure/DataType.h>
//#include <infrastructure/Instance.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Package.h>
#include <fml/infrastructure/Port.h>
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
#include <fml/runtime/Message.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/BaseSymbolTypeSpecifier.h>
#include <fml/type/ClassTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>
#include <fml/type/TypeAliasSpecifier.h>
#include <fml/type/UnionTypeSpecifier.h>

#include <fml/workflow/UniFormIdentifier.h>
#include <fml/workflow/WObject.h>


namespace sep
{


ClassKindInfo * ClassKindInfo::TYPE_UNDEFINED_INFO;

class_kind_t ClassKindInfoInitializer::TYPE_NEW_ID = 0;

std::vector< ClassKindInfo * > * ClassKindInfoInitializer::CKI_TABLE;



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// INITIALIZATION / DESTRUCTION  INVARIANT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


#define INIT_CLASS_KIND_INFO( T )  \
	do { \
		ClassKindInfoInitializer::classKindInfo< T >().mNAME = #T; \
	} while( false )

static avm_uint16_t NIFTY_COUNTER = 0;

ClassKindInfoInitializer::ClassKindInfoInitializer()
{
	if( (0 == NIFTY_COUNTER++) && (0 == TYPE_NEW_ID) )
	{
		// STATIC INITIALIZATION DEPENDANCY
		CKI_TABLE = new std::vector< ClassKindInfo * >();

		ClassKindInfo::TYPE_UNDEFINED_INFO =
				new ClassKindInfo(TYPE_UNDEFINED_ID, "#undefined");

		// TYPE_NEW_ID == 0 for ClassKindInfo::TYPE_UNDEFINED_INFO
		TYPE_NEW_ID = 1;


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
		INIT_CLASS_KIND_INFO( InstanceOfBuffer  );
		INIT_CLASS_KIND_INFO( InstanceOfConnect );
		INIT_CLASS_KIND_INFO( InstanceOfData    );
		INIT_CLASS_KIND_INFO( InstanceOfMachine );
		INIT_CLASS_KIND_INFO( InstanceOfPort    );

		// EXECUTABLE OBJECT
		INIT_CLASS_KIND_INFO( AvmLambda         );
		INIT_CLASS_KIND_INFO( AvmProgram        );
		INIT_CLASS_KIND_INFO( AvmTransition     );

		INIT_CLASS_KIND_INFO( ExecutableForm    );
		INIT_CLASS_KIND_INFO( ExecutableSystem  );

		// RUNTIME OBJECT
		INIT_CLASS_KIND_INFO( RuntimeID         );
		INIT_CLASS_KIND_INFO( RuntimeForm       );

		// EXECUTION OBJECT
		INIT_CLASS_KIND_INFO( ExecutionConfiguration );

		INIT_CLASS_KIND_INFO( ExecutionData     );
		INIT_CLASS_KIND_INFO( ExecutionContext  );

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
		INIT_CLASS_KIND_INFO( BuiltinVector );
		INIT_CLASS_KIND_INFO( BuiltinReverseVector );
		INIT_CLASS_KIND_INFO( BuiltinList   );
		INIT_CLASS_KIND_INFO( BuiltinSet    );
		INIT_CLASS_KIND_INFO( BuiltinBag    );
		INIT_CLASS_KIND_INFO( BuiltinFifo   );
		INIT_CLASS_KIND_INFO( BuiltinLifo   );

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
		INIT_CLASS_KIND_INFO( Message      );
		INIT_CLASS_KIND_INFO( ComRouteData );
		INIT_CLASS_KIND_INFO( Router       );
		INIT_CLASS_KIND_INFO( RoutingData  );

		// OTHER
		INIT_CLASS_KIND_INFO( FormulaData  );

		// EXECUTION TRACE
		INIT_CLASS_KIND_INFO( TracePoint    );
		INIT_CLASS_KIND_INFO( TraceSequence );

AVM_IF_DEBUG_LEVEL_FLAG( ULTRA , COMPILING )
	toStreamTable(AVM_OS_COUT,
			"ClassKindInfoInitializer::ClassKindInfoInitializer");
AVM_ENDIF_DEBUG_LEVEL_FLAG( ULTRA , COMPILING )
	}
}


ClassKindInfoInitializer::~ClassKindInfoInitializer()
{
	if( 0 == --NIFTY_COUNTER )
	{
//		toStreamTable(std::cout, ~ClassKindInfoInitializer);
//
//		ClassKindInfoInitializer::CKI_TABLE->clear();

		delete( CKI_TABLE );
		delete( ClassKindInfo::TYPE_UNDEFINED_INFO );
	}
}




/**
 * CONSTRUCTOR
 * Default
 */
ClassKindInfo::ClassKindInfo(class_kind_t aClassKind, const char * tname)
: mKIND( aClassKind ),
mTNAME( tname ),
mNAME( tname )
{
	ClassKindInfoInitializer::CKI_TABLE->push_back( this );
}


std::string ClassKindInfo::info() const
{
	return( OSS() << "typeinfo< " << std::setw(3) << ((avm_size_t) mKIND)
			<< " , " << mNAME << FQN_ID_ROOT_SEPARATOR << mTNAME << " >" );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


void ClassKindInfoInitializer::toStreamTable(
		OutStream & os, const std::string & msg)
{
	os << TAB << msg << ":>" << std::endl;
	std::vector< ClassKindInfo * >::const_iterator it = CKI_TABLE->begin();
	std::vector< ClassKindInfo * >::const_iterator endIt = CKI_TABLE->end();
	for( ; it != endIt ; ++it )
	{
		os << TAB2 << (*it)->info() << EOL;
	}

	os << TAB << "CKI_TABLE.size: " << CKI_TABLE->size() << EOL;
	os << TAB << "CKI_NEW_ID    : " << ((avm_size_t) TYPE_NEW_ID) << EOL;
	os << TAB << "NIFTY_COUNTER : " << NIFTY_COUNTER << EOL;

	os << TAB << "end" << EOL_FLUSH;
}




#define CHECK_CLASS_KIND_INFO( T , K )  \
	do {  \
		if( CLASS_KIND_T( T ) != ((class_kind_t) K) )  \
		{  \
			std::cout << "FATAL_ERROR :> " << #T << " : "  \
					<< ((avm_size_t) CLASS_KIND_T( T )) << " =/= "  \
					<< ((avm_size_t) K) << " : " << #K << "!!!" << std::endl;  \
		}  \
	} while( false )


static void checkClassKindInfo_w_r_t_EnumClassKind()
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
	CHECK_CLASS_KIND_INFO( InstanceOfBuffer  , FORM_INSTANCE_BUFFER_KIND   );
	CHECK_CLASS_KIND_INFO( InstanceOfConnect , FORM_INSTANCE_CONNECTOR_KIND  );
	CHECK_CLASS_KIND_INFO( InstanceOfData    , FORM_INSTANCE_DATA_KIND     );
	CHECK_CLASS_KIND_INFO( InstanceOfMachine , FORM_INSTANCE_MACHINE_KIND  );
	CHECK_CLASS_KIND_INFO( InstanceOfPort    , FORM_INSTANCE_PORT_KIND     );

	// EXECUTABLE OBJECT
	CHECK_CLASS_KIND_INFO( AvmLambda        , FORM_AVMLAMBDA_KIND          );
	CHECK_CLASS_KIND_INFO( AvmProgram       , FORM_AVMPROGRAM_KIND         );
	CHECK_CLASS_KIND_INFO( AvmTransition    , FORM_AVMTRANSITION_KIND      );
	CHECK_CLASS_KIND_INFO( ExecutableForm   , FORM_EXECUTABLE_MACHINE_KIND );
	CHECK_CLASS_KIND_INFO( ExecutableSystem , FORM_EXECUTABLE_SYSTEM_KIND  );

	// RUNTIME OBJECT
	CHECK_CLASS_KIND_INFO( RuntimeID   , FORM_RUNTIME_ID_KIND );
	CHECK_CLASS_KIND_INFO( RuntimeForm , FORM_RUNTIME_KIND    );

	// EXECUTION OBJECT
	CHECK_CLASS_KIND_INFO( ExecutionConfiguration , FORM_EXECUTION_CONFIGURATION_KIND );
	CHECK_CLASS_KIND_INFO( ExecutionData          , FORM_EXECUTION_DATA_KIND );
	CHECK_CLASS_KIND_INFO( ExecutionContext       , FORM_EXECUTION_CONTEXT_KIND );

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

	// ARRAY
	CHECK_CLASS_KIND_INFO( ArrayBoolean    , FORM_ARRAY_BOOLEAN_KIND    );
	CHECK_CLASS_KIND_INFO( ArrayCharacter  , FORM_ARRAY_CHARACTER_KIND  );
	CHECK_CLASS_KIND_INFO( ArrayInteger    , FORM_ARRAY_INTEGER_KIND    );
	CHECK_CLASS_KIND_INFO( ArrayRational   , FORM_ARRAY_RATIONAL_KIND   );
	CHECK_CLASS_KIND_INFO( ArrayFloat      , FORM_ARRAY_FLOAT_KIND      );
	CHECK_CLASS_KIND_INFO( ArrayString     , FORM_ARRAY_STRING_KIND     );
	CHECK_CLASS_KIND_INFO( ArrayIdentifier , FORM_ARRAY_IDENTIFIER_KIND );
	CHECK_CLASS_KIND_INFO( ArrayQualifiedIdentifier ,
								   FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND );
	CHECK_CLASS_KIND_INFO( ArrayBF         , FORM_ARRAY_BF_KIND         );

	// CONTAINER
	CHECK_CLASS_KIND_INFO( BuiltinVector , FORM_CONTAINER_VECTOR_KIND );
	CHECK_CLASS_KIND_INFO( BuiltinReverseVector ,
										FORM_CONTAINER_REVERSE_VECTOR_KIND );
	CHECK_CLASS_KIND_INFO( BuiltinList   , FORM_CONTAINER_LIST_KIND );
	CHECK_CLASS_KIND_INFO( BuiltinSet    , FORM_CONTAINER_SET_KIND );
	CHECK_CLASS_KIND_INFO( BuiltinBag    , FORM_CONTAINER_BAG_KIND );
	CHECK_CLASS_KIND_INFO( BuiltinFifo   , FORM_CONTAINER_FIFO_KIND );
	CHECK_CLASS_KIND_INFO( BuiltinLifo   , FORM_CONTAINER_LIFO_KIND );

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
	CHECK_CLASS_KIND_INFO( Message      , FORM_MESSAGE_KIND        );
	CHECK_CLASS_KIND_INFO( ComRouteData , FORM_COM_ROUTE_DATA_KIND );
	CHECK_CLASS_KIND_INFO( Router       , FORM_ROUTER_KIND         );
	CHECK_CLASS_KIND_INFO( RoutingData  , FORM_ROUTING_DATA_KIND   );

	// OTHER
	CHECK_CLASS_KIND_INFO( FormulaData  , FORM_EXEC_FILTER_FORMULA_DATA_KIND );

	// EXECUTION TRACE
	CHECK_CLASS_KIND_INFO( TracePoint   , FORM_TRACE_POINT_KIND        );
	CHECK_CLASS_KIND_INFO( TraceSequence, FORM_TRACE_SEQUENCE_KIND      );

	//	std::cout << "end" << std::endl;
}

////////////////////////////////////////////////////////////////////////////////
// LOADER / DISPOSER  API
////////////////////////////////////////////////////////////////////////////////

void ClassKindInfoInitializer::load()
{
	checkClassKindInfo_w_r_t_EnumClassKind();

AVM_IF_DEBUG_LEVEL_FLAG( ULTRA , COMPILING )
	toStreamTable(AVM_OS_COUT, "ClassKindInfoInitializer::load");
AVM_ENDIF_DEBUG_LEVEL_FLAG( ULTRA , COMPILING )
}


void ClassKindInfoInitializer::dispose()
{
AVM_IF_DEBUG_LEVEL_FLAG( ULTRA , COMPILING )
	toStreamTable(AVM_OS_COUT, "ClassKindInfoInitializer::dispose");
AVM_ENDIF_DEBUG_LEVEL_FLAG( ULTRA , COMPILING )
}




/**
 * CLASS KIND CHECKER
 * CAST
 */
template<> bool ClassKindImpl::is< Machine >() const
{
	return( is_exactly< Machine >() ||
			is< System          >() ||
			is< Package         >() );
}

template<> bool ClassKindImpl::isnot< Machine >() const
{
	return( isnot_exactly< Machine >() &&
			isnot< System          >() &&
			isnot< Package         >() );
}


template<> bool ClassKindImpl::is< BehavioralElement >() const
{
	return( is< PropertyElement >() ||
			is< Machine         >() ||
//			is< Instance        >() ||
			is< Transition      >() ||
			is< Routine         >() );
}

template<> bool ClassKindImpl::isnot< BehavioralElement >() const
{
	return( isnot< PropertyElement >() &&
			isnot< Machine         >() &&
//			isnot< Instance        >() &&
			isnot< Transition      >() &&
			isnot< Routine         >() );
}


template<> bool ClassKindImpl::is< PropertyElement >() const
{
	return( is< Variable >() ||
			is< Port     >() ||
			is< Buffer   >() ||
			is< Channel  >() );
}

template<> bool ClassKindImpl::isnot< PropertyElement >() const
{
	return( isnot< Variable >() &&
			isnot< Port     >() &&
			isnot< Buffer   >() &&
			isnot< Channel  >() );
}


template<> bool ClassKindImpl::is< ObjectElement >() const
{
	return( is< PropertyElement   >() ||
			is< BehavioralElement >() ||
			is< DataType          >() ||
			is< Connector         >() ||
			is< ComRoute          >() ||
			is< BaseCompiledForm  >() ||
			is< WObject           >() );
}

template<> bool ClassKindImpl::isnot< ObjectElement >() const
{
	return( isnot< PropertyElement   >() &&
			isnot< BehavioralElement >() &&
			isnot< DataType          >() &&
			isnot< Connector         >() &&
			isnot< ComRoute          >() &&
			isnot< BaseCompiledForm  >() &&
			isnot< WObject           >() );
}


template<> bool ClassKindImpl::is< Number >() const
{
	return( is< Integer  >() ||
			is< Rational >() ||
			is< Float    >() );
}

template<> bool ClassKindImpl::isnot< Number >() const
{
	return( isnot< Integer  >() &&
			isnot< Rational >() &&
			isnot< Float    >() );
}


template<> bool ClassKindImpl::is< BuiltinQueue >() const
{
	return( is< BuiltinFifo >() ||
			is< BuiltinLifo >() );
}

template<> bool ClassKindImpl::isnot< BuiltinQueue >() const
{
	return( isnot< BuiltinFifo >() &&
			isnot< BuiltinLifo >() );
}


template<> bool ClassKindImpl::is< BuiltinList >() const
{
	return( is_exactly< BuiltinList >() ||
			is< BuiltinQueue        >() ||
			is< BuiltinSet          >() ||
			is< BuiltinBag          >() );
}

template<> bool ClassKindImpl::isnot< BuiltinList >() const
{
	return( isnot_exactly< BuiltinList >() ||
			isnot< BuiltinQueue        >() ||
			isnot< BuiltinSet          >() ||
			isnot< BuiltinBag          >() );
}


template<> bool ClassKindImpl::is< BuiltinVector >() const
{
	return( is_exactly< BuiltinVector >() ||
			is< BuiltinReverseVector  >() );
}

template<> bool ClassKindImpl::isnot< BuiltinVector >() const
{
	return( isnot_exactly< BuiltinVector >() &&
			isnot< BuiltinReverseVector  >() );
}


template<> bool ClassKindImpl::is< BuiltinArray >() const
{
	return( is< ArrayBoolean             >() ||
			is< ArrayCharacter           >() ||
			is< ArrayInteger             >() ||
			is< ArrayFloat               >() ||
			is< ArrayString              >() ||
			is< ArrayIdentifier          >() ||
			is< ArrayQualifiedIdentifier >() ||
			is< ArrayBF                  >() );
}

template<> bool ClassKindImpl::isnot< BuiltinArray >() const
{
	return( isnot< ArrayBoolean             >() &&
			isnot< ArrayCharacter           >() &&
			isnot< ArrayInteger             >() &&
			isnot< ArrayFloat               >() &&
			isnot< ArrayString              >() &&
			isnot< ArrayIdentifier          >() &&
			isnot< ArrayQualifiedIdentifier >() &&
			isnot< ArrayBF                  >() );
}


template<> bool ClassKindImpl::is_strictly< BuiltinArray >() const
{
	return( is< ArrayBoolean             >() ||
			is< ArrayCharacter           >() ||
			is< ArrayInteger             >() ||
			is< ArrayFloat               >() ||
			is< ArrayString              >() ||
			is< ArrayIdentifier          >() ||
			is< ArrayQualifiedIdentifier >() );
}

template<> bool ClassKindImpl::isnot_strictly< BuiltinArray >() const
{
	return( is< ArrayBF >() );
}


template<> bool ClassKindImpl::is< BuiltinContainer >() const
{
	return( is< BuiltinVector        >() ||
			is< BuiltinList          >() ||
			is< BuiltinQueue         >() ||
			is< BuiltinReverseVector >() );
}

template<> bool ClassKindImpl::isnot< BuiltinContainer >() const
{
	return( isnot< BuiltinVector        >() &&
			isnot< BuiltinList          >() &&
			isnot< BuiltinQueue         >() &&
			isnot< BuiltinReverseVector >() );
}


template<> bool ClassKindImpl::is< BuiltinCollection >() const
{
	return( is< BuiltinArray     >() ||
			is< BuiltinContainer >() );
}

template<> bool ClassKindImpl::isnot< BuiltinCollection >() const
{
	return( isnot< BuiltinArray     >() &&
			isnot< BuiltinContainer >() );
}


template<> bool ClassKindImpl::is< BuiltinForm >() const
{
	return( is< Boolean           >() ||
			is< Character         >() ||
			is< Number            >() ||
			is< String            >() ||
			is< BuiltinCollection >() );
}

template<> bool ClassKindImpl::isnot< BuiltinForm >() const
{
	return( isnot< Boolean           >() &&
			isnot< Character         >() &&
			isnot< Number            >() &&
			isnot< String            >() &&
			isnot< BuiltinCollection >() );
}


template<> bool ClassKindImpl::is< BaseInstanceForm >() const
{
	return( is< InstanceOfData    >() ||
			is< InstanceOfPort    >() ||
			is< InstanceOfMachine >() ||
			is< InstanceOfBuffer  >() ||
			is< InstanceOfConnect >() );
}

template<> bool ClassKindImpl::isnot< BaseInstanceForm >() const
{
	return( isnot< InstanceOfData    >() &&
			isnot< InstanceOfPort    >() &&
			isnot< InstanceOfMachine >() &&
			isnot< InstanceOfBuffer  >() &&
			isnot< InstanceOfConnect >() );
}


template<> bool ClassKindImpl::is< AvmProgram >() const
{
	return( is_exactly< AvmProgram >() ||
			is< AvmTransition      >() ||
			is< ExecutableForm     >() );
}

template<> bool ClassKindImpl::isnot< AvmProgram >() const
{
	return( isnot_exactly< AvmProgram >() &&
			isnot< AvmTransition      >() &&
			isnot< ExecutableForm     >() );
}


template<> bool ClassKindImpl::is< BaseAvmProgram >() const
{
	return( is_exactly< BaseAvmProgram >() ||
			is< AvmProgram             >() ||
			is< AvmLambda              >() );
}

template<> bool ClassKindImpl::isnot< BaseAvmProgram >() const
{
	return( isnot_exactly< BaseAvmProgram >() &&
			isnot< AvmProgram             >() &&
			isnot< AvmLambda              >() );
}


template<> bool ClassKindImpl::is< BaseSymbolTypeSpecifier >() const
{
	return( is< ClassTypeSpecifier >() ||
			is< EnumTypeSpecifier  >() ||
			is< UnionTypeSpecifier >() );
}

template<> bool ClassKindImpl::isnot< BaseSymbolTypeSpecifier >() const
{
	return( isnot< ClassTypeSpecifier >() &&
			isnot< EnumTypeSpecifier  >() &&
			isnot< UnionTypeSpecifier >() );
}


template<> bool ClassKindImpl::is< BaseTypeSpecifier >() const
{
	return( is_exactly< BaseTypeSpecifier >() ||
			is< BaseSymbolTypeSpecifier   >() ||
			is< ContainerTypeSpecifier    >() ||
			is< IntervalTypeSpecifier     >() ||
			is< TypeAliasSpecifier        >() );
}

template<> bool ClassKindImpl::isnot< BaseTypeSpecifier >() const
{
	return( isnot_exactly< BaseTypeSpecifier >() &&
			isnot< BaseSymbolTypeSpecifier   >() &&
			isnot< ContainerTypeSpecifier    >() &&
			isnot< IntervalTypeSpecifier     >() &&
			isnot< TypeAliasSpecifier        >() );
}


template<> bool ClassKindImpl::is< BaseCompiledForm >() const
{
	return( is< BaseInstanceForm  >() ||
			is< BaseAvmProgram    >() ||
			is< ExecutableSystem  >() ||
			is< ComRouteData      >() ||
			is< BaseTypeSpecifier >() );
}

template<> bool ClassKindImpl::isnot< BaseCompiledForm >() const
{
	return( isnot< BaseInstanceForm  >() &&
			isnot< BaseAvmProgram    >() &&
			isnot< ExecutableSystem  >() &&
			isnot< ComRouteData      >() &&
			isnot< BaseTypeSpecifier >() );
}


template<> bool ClassKindImpl::is< RamBuffer >() const
{
	return( is_exactly< RamBuffer >() ||
			is< BroadcastBuffer   >() );
}

template<> bool ClassKindImpl::isnot< RamBuffer >() const
{
	return( isnot_exactly< RamBuffer >() &&
			isnot< BroadcastBuffer   >() );
}


template<> bool ClassKindImpl::is< BaseBufferQueue >() const
{
	return( is< FifoBuffer      >() ||
			is< LifoBuffer      >() ||
			is< MultiFifoBuffer >() ||
			is< MultiLifoBuffer >() ||
			is< SetBuffer       >() ||
			is< MultisetBuffer  >() );
}

template<> bool ClassKindImpl::isnot< BaseBufferQueue >() const
{
	return( isnot< FifoBuffer      >() &&
			isnot< LifoBuffer      >() &&
			isnot< MultiFifoBuffer >() &&
			isnot< MultiLifoBuffer >() &&
			isnot< SetBuffer       >() &&
			isnot< MultisetBuffer  >() );
}


template<> bool ClassKindImpl::is< BaseBufferForm >() const
{
	return( is< BaseBufferQueue >() ||
			is< RamBuffer       >() );
}

template<> bool ClassKindImpl::isnot< BaseBufferForm >() const
{
	return( isnot< BaseBufferQueue >() &&
			isnot< RamBuffer       >() );
}


} /* namespace sep */

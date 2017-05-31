/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#include "avm_util.h"

#include <collection/Bitset.h>

#include <common/AvmObject.h>
#include <common/Element.h>
#include <common/BF.h>
#include <common/RunnableElement.h>
#include <computer/BaseEnvironment.h>
#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionEnvironment.h>
#include <computer/instruction/InstructionEnvironment.h>
#include <computer/primitive/AvmCommunicationRdvPrimitive.h>

#include <fml/buffer/BaseBufferQueue.h>

#include <fml/builtin/BuiltinForm.h>
#include <fml/builtin/Identifier.h>
#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/common/ObjectElement.h>
#include <fml/common/PropertyElement.h>

#include <fml/executable/AvmLambda.h>
#include <fml/executable/AvmProgram.h>
#include <fml/executable/ComRouteData.h>
#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfConnect.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/Router.h>
#include <fml/executable/RoutingData.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>
#include <fml/expression/BuiltinQueue.h>
#include <fml/expression/BuiltinContainer.h>

#include <fml/numeric/Number.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Buffer.h>
#include <fml/infrastructure/Channel.h>
#include <fml/infrastructure/ComPoint.h>
#include <fml/infrastructure/ComRoute.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/Connector.h>
#include <fml/infrastructure/DataType.h>
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

#include <fml/operator/Operator.h>

#include <fml/symbol/Symbol.h>
#include <fml/symbol/TableOfSymbol.h>

#include <fml/type/TableOfTypeSpecifier.h>
#include <fml/type/TypeSpecifier.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/ExecutionInformation.h>
#include <fml/runtime/ExecutionLocation.h>
#include <fml/runtime/ExecutionSynchronizationPoint.h>
#include <fml/runtime/LocalRuntime.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>
#include <fml/runtime/TableOfData.h>
#include <fml/runtime/TableOfRuntimeFormState.h>

#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <fml/type/BaseTypeSpecifier.h>

#include <fml/workflow/UniFormIdentifier.h>
#include <fml/workflow/WObject.h>

#include <fam/api/AbstractProcessorUnit.h>
#include <fml/runtime/LocalRuntime.h>
#include <fml/runtime/Message.h>

#include <parser/ParserManager.h>


namespace sep {


/**
 *******************************************************************************
 * AVM EXIT CODE
 *******************************************************************************
 */
AVM_EXIT_CODE_KIND  _AVM_EXIT_CODE_ = AVM_EXIT_GOOD_CODE;


void avm_set_exit_code(AVM_EXIT_CODE_KIND exit_code)
{
	if( _AVM_EXIT_CODE_ == AVM_EXIT_GOOD_CODE )
	{
		_AVM_EXIT_CODE_ = exit_code;
	}
	else if( _AVM_EXIT_CODE_ != exit_code )
	{
AVM_IF_DEBUG_ENABLED

	AVM_OS_WARN << _DBG_ << "Previous exit code: " << std::endl
			<< exit_msg( _AVM_EXIT_CODE_ ) << std::endl;

AVM_ENDIF_DEBUG_ENABLED

		_AVM_EXIT_CODE_ = exit_code;
	}
}


std::string avm_strExitCode(AVM_EXIT_CODE_KIND exit_code)
{

#define CASE_RETURN( code , str )  case AVM_EXIT_##code##_CODE: return( str );

	switch( exit_code )
	{
		CASE_RETURN( GOOD , "good" )

		CASE_RETURN( FAILED , "failed" )


		CASE_RETURN( OUT_OF_MEMORY , "out-of-memory" )

		CASE_RETURN( FATAL_ERROR , "fatal error" )


		CASE_RETURN( CONFIGURE_ERROR , "error in configuration process" )

		CASE_RETURN( PARSING_ERROR , "error in parsing process" )

		CASE_RETURN( PARSING_EXCEPTION , "exception in parsing process" )

		CASE_RETURN( COMPILING_ERROR , "error in compiling process" )


		CASE_RETURN( EXECUTION_ERROR , "error in execution process" )

		CASE_RETURN( RUNTIME_ERROR , "runtime error" )


		CASE_RETURN( INITIALIZING_ERROR , "processor: initialization error" )

		CASE_RETURN( PRE_PROCESSING_ERROR , "processor: pre-processing error" )

		CASE_RETURN( PROCESSING_ERROR , "processor: processing error" )

		CASE_RETURN( POST_PROCESSING_ERROR , "processor: post_processing error" )

		CASE_RETURN( FINALIZING_ERROR , "processor: finalization error" )


		//CONTROLLER UNIT VERDICT
		CASE_RETURN( SYMBEX_CONTROLLER_MIN , "symbex controller: minimal code" )


		CASE_RETURN( COVERAGE_GOAL_ACHIEVED    , "coverage: GOAL ACHIEVED"   )
		CASE_RETURN( COVERAGE_GOAL_UNACHIEVED  , "coverage: GOAL UNACHIEVED" )

		CASE_RETURN( COVERAGE_GOAL_ALMOST_ACHIEVED,	"coverage: ALMOST ACHIEVED")

		CASE_RETURN( COVERAGE_GOAL_UNREACHABLE , "coverage: GOAL UNREACHABLE" )


		CASE_RETURN( VERDICT_PASS              , "verdict: PASS"        )
		CASE_RETURN( VERDICT_STRONG_PASS       , "verdict: STRONG PASS" )
		CASE_RETURN( VERDICT_WEAK_PASS         , "verdict: WEAK PASS"   )

		CASE_RETURN( VERDICT_INCONCLUIVE       , "verdict: INCONCLUIVE"       )
		CASE_RETURN( VERDICT_INCONCLUIVE_INPUT , "verdict: INCONCLUIVE_INPUT" )
		CASE_RETURN( VERDICT_INCONCLUIVE_R     , "verdict: INCONCLUIVE_R"     )

		CASE_RETURN( VERDICT_NONE              , "verdict: NONE"        )
		CASE_RETURN( VERDICT_FAIL              , "verdict: FAIL"        )
		CASE_RETURN( VERDICT_ERROR             , "verdict: ERROR"       )
		CASE_RETURN( VERDICT_ABORT             , "verdict: ABORT"       )

		CASE_RETURN( VERDICT_UNDEFINED         , "verdict: UNDEFINED"   )


		CASE_RETURN( UNKNOWN , "unknown exit code" )

		default: return "undefined exit code";
	}
}


OutStream & operator<<(OutStream & OS, const AvmEXIT_SIGNAL & exitSignal)
{
	return( OS << EMPHASIS( OSS() << "@exit< "
			<< avm_strExitCode( exitSignal.code ) << " > bye !",
			( ((exitSignal.code == AVM_EXIT_GOOD_CODE)
					|| (exitSignal.code > AVM_EXIT_SYMBEX_CONTROLLER_MIN_CODE))
				? '*' : '?' ),
			( ((exitSignal.code == AVM_EXIT_GOOD_CODE)
					|| (exitSignal.code > AVM_EXIT_SYMBEX_CONTROLLER_MIN_CODE))
				? 42 : 80 ) ) );

//	return( OS << "@exit< " << avm_strExitCode( exitSignal.code )
//			<< " > bye !" << std::endl );
}


/**
 ***************************************************************************
 * AVM EVAL MODE
 ***************************************************************************
 */
AVM_EXEC_MODE_KIND  _AVM_EXEC_MODE_ = AVM_EXEC_STANDALONE_MODE;

void avm_setExecModeKind(std::string strModeKind)
{
	StringTools::toupper(strModeKind);

	if( strModeKind.empty() )                AVM_EXEC_MODE_SET( STANDALONE  )

	else if( strModeKind == "STANDALONE"  )  AVM_EXEC_MODE_SET( STANDALONE  )

	else if( strModeKind == "SERVER"      )  AVM_EXEC_MODE_SET( SERVER      )

	else if( strModeKind == "INTERACTIVE" )  AVM_EXEC_MODE_SET( INTERACTIVE )

	else AVM_EXEC_MODE_SET( STANDALONE )
}



AVM_EXEC_VERBOSITY_LEVEL  _AVM_EXEC_VERBOSITY_ = AVM_EXEC_VERBOSITY_MAXIMUM;

void avm_setExecVerbosityLevel(std::string strVerbosityLevel)
{
	StringTools::toupper(strVerbosityLevel);

	if( strVerbosityLevel.empty() )           AVM_EXEC_VERBOSITY_SET( MAXIMUM )

	else if( strVerbosityLevel == "SILENT"  ) AVM_EXEC_VERBOSITY_SET( SILENT  )

	else if( strVerbosityLevel == "MINIMUM" ) AVM_EXEC_VERBOSITY_SET( MINIMUM )

	else if( strVerbosityLevel == "MEDIUM"  ) AVM_EXEC_VERBOSITY_SET( MEDIUM  )

	else if( strVerbosityLevel == "MAXIMUM" ) AVM_EXEC_VERBOSITY_SET( MAXIMUM )

	else AVM_EXEC_VERBOSITY_SET( MAXIMUM )
}

std::string avm_strExecVerbosityLevel()
{
	switch( _AVM_EXEC_VERBOSITY_ )
	{
		case AVM_EXEC_VERBOSITY_SILENT : return( "SILENT"  );
		case AVM_EXEC_VERBOSITY_MINIMUM: return( "MINIMUM" );
		case AVM_EXEC_VERBOSITY_MEDIUM : return( "MEDIUM"  );
		case AVM_EXEC_VERBOSITY_MAXIMUM: return( "MAXIMUM" );

		default: return( "VERBOSITY< UNKNOWN >" );
	}
}



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



/**
 * avm_report
 */
void avm_report(OutStream & os, const std::string & aMsg, bool forced)
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

//	AVM_INSTANCE_REPORT_COUNTER(ginac_and       );
//	AVM_INSTANCE_REPORT_COUNTER(ginac_or        );
//	AVM_INSTANCE_REPORT_COUNTER(ginac_not       );
//	AVM_INSTANCE_REPORT_COUNTER(ginac_relational);


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
	AVM_INSTANCE_REPORT_COUNTER(Connector );
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
	AVM_INSTANCE_REPORT_COUNTER(ComRouteData    );
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
	AVM_INSTANCE_REPORT_COUNTER(InstanceOfConnect);
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


}

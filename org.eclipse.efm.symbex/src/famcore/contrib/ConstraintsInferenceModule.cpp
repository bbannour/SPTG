/******************************************************************************
 * ConstraintsInferenceModule.cpp
 *
 *  Created on: 29 sept. 2017
 *  Author: IB252693
 *
 *  Imen Boudhiba (CEA LIST) imen.boudhiba@cea.fr
 *
 ******************************************************************************/


#include <collection/BFContainer.h>
#include <fml/expression/AvmCode.h>
#include <fml/expression/AvmCodeFactory.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <collection/Collection.h>
#include  <famcore/contrib/ConstraintsInferenceModule.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <printer/OutStream.h>

#include <sew/Configuration.h>
#include <fml/trace/TraceFactory.h>
#include <fml/expression/ExpressionFactory.h>

#include <regex>

namespace sep
{

/*
Functions_Contracts_Inference {
	table [
		variable  = "globalProgramTrace"
	] // end property
}
*/
#define KW_SLACH      "\\"
#define KW_THIS       "$this#call"
#define KW_PREV       "$prev#call"
#define KW_RESULT     "$result"


#define   ID( var )   (var)[0]

#define  PRE( var )   (var)[1]

#define CALL( var )   (var)[2]

#define POST( var )   (var)[3]

#define  INV( var )   (var)[4]


#define TYPE_POINTER_PREFIX            "ptr_"

#define TYPE_POINTER_REGEX_PATTERN     std::regex("ptr_(\\w+)")

#define TYPE_POINTER_REGEX_REPLACE     "$1 *"


/**
 * CONFIGURE allows to take into account user's parameters:
 * at the moment, it takes as input ... à compléter
 */
bool ConstraintsInferenceModule::configureImpl()
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( hasParameterWObject() )
							<< "Unexpected a <null> ConstraintsInferenceModule WObject !!!"
							<< SEND_EXIT;

	const WObject * theTABLE = Query::getWSequence(getParameterWObject(), "table");
	if( theTABLE == WObject::_NULL_ )
	{
		// TODO ERROR
		return false;
	}

	mFunctionCalls = Query::getRegexWPropertyString(theTABLE, "variable", "AllCallsStack");
	mFunctionSigs = Query::getRegexWPropertyString(theTABLE, "signature", "AllSignatures");

	//get xLIA/c mapping types
	const WObject * theTYPE_MAPPING =
				Query::getWSequence(getParameterWObject(), "type_c_mapping");

	if( theTYPE_MAPPING != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = theTYPE_MAPPING->owned_begin();
		WObject::const_iterator endWfO = theTYPE_MAPPING->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( (*itWfO)->getValue().is< String >() )
				{
					mAllxLIAtypes.add_unique((*itWfO)->getNameID());
					mAllCtypes.add_unique((*itWfO)->getValue().to< String >().getValue());
				}
			}
		}
	}


	return true;
}

/**
 * REPORT TRACE
 */
void ConstraintsInferenceModule::reportDefault(OutStream & out) const
{
	reportHeader(out, "FUNCTIONS CONTRACTS INFERENCE ");
	out << TAB << "==> DONE" << std::endl;
}


/**
 * postProcessing
 */
bool ConstraintsInferenceModule::postprocess()
{
	AVM_OS_TRACE << "PostProcess method "<< std::endl;


	ListOfExecutionContext listOfLeafEC;

	computeLeafEC( getConfiguration().getExecutionTrace() , listOfLeafEC );

	beginStream();

//	OutStream & out1File = getStream("file#1");
	OutStream & out2File = getStream("file#2");

	ExecutionContext * itEC = nullptr;

	for( ExecutionContext * ec : listOfLeafEC )
	{
		mCurrentPathECs.clear();
		for( itEC = ec ; itEC != nullptr ; itEC = itEC->getPrevious() )
		{
			mCurrentPathECs.push_front( itEC );
		}

		//OutStream & out1File = ( hasStream() ) ? currentStream() : AVM_OS_TRACE;//getStream("file#1");
		postprocessLeaf( *ec, //out1File,
				out2File );
	}

	closeStream();

	return true;
}


bool ConstraintsInferenceModule::postprocessLeaf(
		ExecutionContext & leafEC, //OutStream & out1File,
		OutStream & out2File)
{
	// Resetting global variables
	mAllDependancyVariables.clear();
	mAllReturnVariables.clear();


	// Collecter la path condition de la feuille
	const BF & pathCondition = leafEC.getExecutionData().getPathCondition();
//	out2File << "postprocessLeaf on  " << leafEC.str() << std::endl
//			<< "PC: " << PC
//			<< std::endl;

	//collecter séquence d'appels de fonctions de la feuille: val
	BF stackVal = leafEC.getExecutionData().getDataByNameID( mFunctionCalls.getValue() );
	AVM_OS_TRACE << "Global function calls stack:> " << stackVal << std::endl;

	//collecter ensemble des variables des appels de fonctions
	BuiltinVector & callStack = stackVal.to< BuiltinVector >();

	//out2File << "before normalize" << std::endl;

	normalizeCallStack(callStack);

	collectDependancyProgramVariables(
			pathCondition, callStack, mAllDependancyVariables);

	collectReturnVariables(callStack, mAllReturnVariables);


	//out2File << "after normalize" << std::endl;

	StringOutStream acslstream( AVM_TAB1_INDENT );
	ToACSL(acslstream, callStack, pathCondition, leafEC);

	std::string acslRelational = acslstream.str();

	// ACSL POST-TREATMENT for removing #
	//StringTools::replaceAll( acslRelational, "#params.", "_params_");
	StringTools::replaceAll( acslRelational, "#params.", "_");
	StringTools::replaceAll( acslRelational, "->", "==>");
	StringTools::replaceAll( acslRelational, "true", "\\true");
//	std::string acslRelational = acslConstraint.str();
//	std::size_t idx = 0;
//	while ((idx = acslRelational.find("#params.", idx)) != -1)
//	{
//		acslRelational.replace(idx++, 8, "_");
//	}

	//collecter signatures de fonctions de la feuille: val
		BF sigsVal = leafEC.getExecutionData().getDataByNameID( mFunctionSigs.getValue() );
		AVM_OS_TRACE << "Global function signatures:> " << sigsVal << std::endl;

		//collecter ensemble des variables des appels de fonctions
		BuiltinVector & sigsStack = sigsVal.to< BuiltinVector >();


	//lib and declaration

		out2File << "#include \"stdint.h\""<< std::endl;

		out2File << "extern uint32_t *FLASH_BASE;"<< std::endl;

	//normalize signatureStack
		normalizeSigsStack(sigsStack);

	// Writing n-1 function signatures
		for( std::size_t i = 0 ; i < mAllCalledFunNames.size()-1 ; ++i  )
		{
			for( std::size_t idx = 0 ; idx < sigsStack.size() ; ++idx  )
			{
				ArrayBF & currentSig = sigsStack.at(idx).to< ArrayBF >();

				if( currentSig.first().is< String >() )
				{
					String name = currentSig.first().to< String >().getValue();
					if( name.compare(mAllCalledFunNames.at(i)) == 0 )
					{
						if( currentSig.second().is< String >() )
						{
							out2File << currentSig.second().to< String >().getValue() << ";" << std::endl;
						}
					}
				}
			}
		}
	// Writing relational pproperty in final file
	out2File << acslRelational << std::endl;

	//writing last signature
//	ArrayBF & lastSig = sigsStack.last().to< ArrayBF >();
//
//	if( lastSig.second().is< String >() )
//	{
//		out2File << lastSig.second().to< String >().getValue() << ";" << std::endl;
//	}



	for( std::size_t idx = 0 ; idx < sigsStack.size() ; ++idx  )
	{
		ArrayBF & currentSig = sigsStack.at(idx).to< ArrayBF >();

		if( currentSig.first().is< String >() )
		{
			String name = currentSig.first().to< String >().getValue();
			if( name.compare(mAllCalledFunNames.last())==0 )
			{
				if( currentSig.second().is< String >() )
				{
					out2File << currentSig.second().to< String >().getValue() << ";" << std::endl;
				}
			}
		}
	}

	return true;
}

void ConstraintsInferenceModule::normalizeSigsStack(BuiltinVector & sigsStack)
{
//	AVM_OS_TRACE << "mAllxLIAtypes: " << mAllxLIAtypes << std::endl;
//	AVM_OS_TRACE << "mAllCtypes: " << mAllCtypes << std::endl;
	for( auto & itSig : sigsStack )
	{
		ArrayBF & currentSig = itSig.to< ArrayBF >();

		if( currentSig.second().is< String >() )
		{
			String & sig = currentSig.second().to< String >();

			for( std::size_t idx = 0 ; idx < mAllxLIAtypes.size() ; ++idx)
			{
				const std::string xLIA_Type = mAllxLIAtypes.at(idx);
				const std::string C_Type = mAllCtypes.at(idx);

//				StringTools::replaceAll(sig.getValue(), xLIA_Type, C_Type);
				sig.setValue( std::regex_replace(sig.getValue(),
						std::regex("\\b" + xLIA_Type + "\\b"), C_Type) );
			}

			sig.setValue( std::regex_replace(sig.getValue(),
					TYPE_POINTER_REGEX_PATTERN, TYPE_POINTER_REGEX_REPLACE) );
		}
	}
}

void ConstraintsInferenceModule::normalizeCallStack(BuiltinVector & callStack)
{
	//bool isnotFirst = false;

	const ArrayBF * previousCall = nullptr;

	std::string callID = "";
	std::string thisID = "";
	std::string prevID = "";

	for( auto & itCall : callStack )
	{
		ArrayBF & currentCallTrace = itCall.to< ArrayBF >();

		if( ID( currentCallTrace ).is< String >() )
		{
			thisID = ID( currentCallTrace ).to< String >().getValue();
		}
		else
		{
			thisID = "$this<undefined>";
		}
		callID = "\\callresult(" + thisID + ")";

		if( (previousCall != nullptr)
			&& ID( *previousCall ).is< String >() )
		{
			prevID = ID( *previousCall ).to< String >().getValue();
		}
		else
		{
			prevID = "$previous<undefined>";
		}

		if( PRE( currentCallTrace ).is< String >() )
		{
			String & condition = PRE( currentCallTrace ).to< String >();

			StringTools::replaceAll( condition.getValue(), KW_THIS, thisID);
			StringTools::replaceAll( condition.getValue(), KW_PREV, prevID);
			StringTools::replaceAll( condition.getValue(), KW_RESULT, callID);
			StringTools::replaceAll( condition.getValue(), "\\\\", "\\");
		}

		if( POST( currentCallTrace ).is< String >() )
		{
			String & condition = POST( currentCallTrace ).to< String >();

			StringTools::replaceAll( condition.getValue(), KW_THIS, thisID);
			StringTools::replaceAll( condition.getValue(), KW_PREV, prevID);
			StringTools::replaceAll( condition.getValue(), KW_RESULT, callID);
			StringTools::replaceAll( condition.getValue(), "\\\\", "\\");
		}

		previousCall = (& currentCallTrace);

//		if( CALL( currentCallTrace ).is< BuiltinVector >() )
//		{
//			const BuiltinVector & currentCall =
//					CALL( currentCallTrace ).to< BuiltinVector >();
//
//			if( currentCall.nonempty() )
//			{
//				for( std::size_t idx = 1 ; idx < currentCall.size()-1 ; ++idx )
//				{
//					normalizeArgumentCall(callStack, currentCall.at(idx).str());
//				}
//			}
//		}
	}
}

void ConstraintsInferenceModule::normalizeExpression(std::string & expression)
{
	for( const auto & varName : mAllReturnVariables)
	{
		StringTools::replaceAll( expression,
				varName, "\\callresult(" + varName + ")" );
	}
}

void ConstraintsInferenceModule::normalizeArgumentCall(const BuiltinVector & callStack,
		std::string & callArg)
{
	VectorOfString allReturnVars;
	collectReturnVariables(callStack, allReturnVars);
	for( const auto & otherCallId : allReturnVars )
	{
//		if( callArg.compare(otherCallId) == 0)
//		{
			StringTools::replaceAll( callArg,
					otherCallId, "\\callresult(" +
					otherCallId + ")" );
//		}
	}



//	for( const auto & otherCall : callStack )
//	{
//		std::string other
//		if( callArg.compare(ID(otherCall).to< String >().getValue()) == 0)
//		{
//			StringTools::replaceAll( callArg,
//					ID(otherCall).to< String >().getValue(), "\\callresult(" +
//					ID(otherCall).to< String >().getValue() + ")" );
//		}
//	}
}


void ConstraintsInferenceModule::collectAllProgsVars(
		const BuiltinVector & callStack, BFVector & AllVars)
{
	for( const auto & itArray : callStack )
	{
		// Chaque appel de programme est supposé etre de type: ArrayBF
		if( itArray.is< ArrayBF >() )
		{
			const ArrayBF & currentCallTrace = itArray.to< ArrayBF >();
			if( currentCallTrace.populated() )
			{
				if( CALL( currentCallTrace ).is< BuiltinVector >() )
				{//currentCallTrace.third()
					const BuiltinVector & currentCall =
							CALL( currentCallTrace ).to< BuiltinVector >();

					for( std::size_t idx = 1 ; idx < currentCall.size() ; ++idx )
					{
						const BF & term = currentCall.get( idx );
						BFVector variables;
						ExpressionFactory::collectVariable(term, variables);

						AllVars.append(variables);
					}
				}
			}
		}
	}
}



void ConstraintsInferenceModule::inOutCallsFormula(
		const BuiltinVector & Programs, BF & inOutCallsConstraints)
{
	inOutCallsConstraints = ExpressionConstructor::newBoolean(true);
	for( const auto & itArray : Programs )
	{
		// Chaque appel de programme est supposÃ© etre de type: ArrayBF
		if( itArray.is< ArrayBF >() )
		{
			const ArrayBF & currentProg = itArray.to< ArrayBF >();
			if( currentProg.nonempty() )
			{
				BFVector params;
				for( std::size_t idx = 1 ; idx < currentProg.size()-1 ; ++idx )
				{
					const BF term = currentProg.get( idx );//.at(1);
					params.append(term);
				}
				inOutCallsConstraints = ExpressionConstructor::andExpr(
						inOutCallsConstraints,
						ExpressionConstructor::newCode(
								OperatorManager::OPERATOR_EQ,
								currentProg.get(currentProg.size()-1 ),
								ExpressionConstructor::newCode(
										OperatorManager::OPERATOR_INVOKE_FUNCTION,
										ExpressionConstructor::newIdentifier(
												currentProg.get(0).str()),
										params)));
			}
		}

	}

}



// returns all vars in PC on which depend function calls

void ConstraintsInferenceModule::collectDependancyProgramVariables(
		const BF & PC, const BuiltinVector & callStack, BFVector & AllDepVars)
{
	BFVector AllVars;
	collectAllProgsVars(callStack, AllVars);

	AllDepVars.append(AllVars);
	BF callsConstraints = ExpressionConstructor::newBoolean(true);

	BFVector listOfClause;

	ExpressionFactory::collectsClause(PC, listOfClause);

	for( std::size_t idx = 0 ; idx < AllDepVars.size() ; ++idx )
	{
		for( std::size_t idx1 = 0 ; idx1 < listOfClause.size() ; ++idx1 )
		{
			// pour Chaque clause du PC determiner les variables reliées aux appels
			BFVector listOfClauseVars;

			ExpressionFactory::collectVariable(
					listOfClause.at(idx1), listOfClauseVars);

			if( listOfClauseVars.contains(AllDepVars.at(idx)) )
			{
				AllDepVars.add_unique(listOfClauseVars);

				//break;
			}
		}
	}
}


void ConstraintsInferenceModule::collectReturnVariables(
		const BuiltinVector & callStack, VectorOfString & allReturnVars)
{
	for( const auto & itCall : callStack )
	{
		if( (itCall).is< ArrayBF >() )
		{
			const ArrayBF & currentCallTrace = itCall.to< ArrayBF >();

			if( currentCallTrace.populated() )
			{
				if( ID( currentCallTrace ).is< String >() )
				{
					allReturnVars.append(
							ID( currentCallTrace ).to< String >().getValue() );
				}
			}
		}
	}
}


void ConstraintsInferenceModule::ToACSL( OutStream & out2File,
		const BuiltinVector & callStack, const BF & pathCondition,
		const ExecutionContext & leafEC )
{
	// HEADER PART
	//toAcsl_header( out2File, leafEC );
	out2File << std::endl;

	// RELATIONAL PART
	out2File << "/*@relational" << std::endl;

	// FORALL PART
	out2File << "\\forall " << std::endl;
	toAcsl_variableDeclaration(out2File, callStack, pathCondition);
	out2File << std::endl;

	// CALLSET PART
	toAcsl_callset(out2File, callStack);

	// PATH-CONDITION PROJECTION PART
	//toAcsl_pathCondition(out2File, pathCondition, callStack);

	// PRE-POST IMPLIES PART
	toAcsl_preImpliesPost(out2File, callStack);


	out2File << ";" << EOL << "*/" << std::endl;
}

void ConstraintsInferenceModule::toAcsl_header(OutStream & out2File,
		const ExecutionContext & leafEC)
{
	out2File << "Inferred ACSL Spec for the scenario Init --> "
			<< "state" << leafEC.getIdNumber()
			<< " is: > "
			<< std::endl;
//			<< "/*@ predicate Pred{L1, L2}(uint8_t * x, uint8_t * y, integer length)"
//				" = \\forall integer k; 0<=k<length ==> \\at(x[k], L1) == \\at(y[k], L2);"
//			<< "*/" << std::endl;
}


void ConstraintsInferenceModule::toAcsl_variableDeclaration( OutStream & out2File,
		const BuiltinVector & callStack, const BF & pathCondition)
{
	VectorOfString AllcallsRelVarsIdentifier;
	VectorOfString AllcallsRelVarsType;

	std::string type_c;
	std::string type_xlia;

	std::string var_name;

	VectorOfString doNotDeclareVariables( mAllReturnVariables );


//	const WObject * theTYPE_MAPPING =
//			Query::getWSequence(getParameterWObject(), "type_c_mapping");

	AVM_OS_TRACE << "collectDependancyProgramVariables "
			<< mAllDependancyVariables << std::endl;


	for( const auto & itVar : mAllDependancyVariables)
	{
		var_name = itVar.to< InstanceOfData >().getNameID();
AVM_OS_DEBUG << "DependancyProgramVariable: " << var_name << std::endl;

		type_xlia = itVar.to< InstanceOfData >().getTypeSpecifier().strT();
		type_c = type_xlia;

		int position = mAllxLIAtypes.find(type_xlia);
		if( position >= 0 ){
			type_c = mAllCtypes.at(position);
		}
		else if( StringTools::startsWith(type_xlia, TYPE_POINTER_PREFIX) ) {
			type_c = type_xlia.substr(std::strlen(TYPE_POINTER_PREFIX)) + " *";
		}

		//type_c = Query::getWPropertyString(theTYPE_MAPPING, type_xlia, type_xlia);

AVM_OS_DEBUG << "contains: " << AllcallsRelVarsIdentifier.contains(var_name) << std::endl;
		if( not doNotDeclareVariables.contains(var_name) )
		{
			AllcallsRelVarsIdentifier.append(var_name);
			AllcallsRelVarsType.append(type_c);

			doNotDeclareVariables.append(var_name);
		}
	}

	if( AllcallsRelVarsIdentifier.nonempty() )
	{
		std::size_t lastPosition = AllcallsRelVarsIdentifier.size() - 1;
		for( std::size_t idx = 0 ; idx < lastPosition ; ++idx )
		{
			out2File << TAB << AllcallsRelVarsType[idx] <<  " "
					<< AllcallsRelVarsIdentifier[idx] << "," <<  EOL;
		}
		out2File << TAB << AllcallsRelVarsType[lastPosition] << " "
				<< AllcallsRelVarsIdentifier[lastPosition]	<< ";\n";

	}
//	AVM_OS_TRACE << "AllcallsRelVarsType " << AllcallsRelVarsType << std::endl;
//	AVM_OS_TRACE << "AllcallsRelVarsIdentifier " << AllcallsRelVarsIdentifier << std::endl;
}


void ConstraintsInferenceModule::toAcsl_callset(OutStream & out2File,
		const BuiltinVector & callStack)
{

	std::size_t callIndex = 0;

	out2File << TAB << "\\callset(" << std::endl;

	if( callStack.empty())
	{
		AVM_OS_DEBUG << " callstack empty !!" << std::endl;
	}


	for( const auto & itCall : callStack )
	{
//		out2File << std::endl << itCall << std::endl;

		if( (itCall).is< ArrayBF >() )
		{
			const ArrayBF & currentCallTrace = itCall.to< ArrayBF >();

			if( currentCallTrace.nonempty())//populated()
			{
				AVM_OS_DEBUG << "on passe bien ici...currentCallTrace.nonempty()" << std::endl;
				if( CALL( currentCallTrace ).is< BuiltinVector >() )
				{
					const BuiltinVector & currentCall =
							CALL( currentCallTrace ).to< BuiltinVector >();

					if( currentCall.nonempty() )
					{
						AVM_OS_DEBUG << "on passe bien ici...currentCall.nonempty() " << std::endl;
						std::string funcName = currentCall.get( 0).str().substr(1, currentCall.get( 0).size());
						out2File  << TAB2 << "\x5C" << "call"<<
								//"{L" << callIndex
								//<< ", L" << callIndex+1 << "}"<<
								"(" << funcName
								<< ", ";
						mAllCalledFunNames.add_unique(funcName);
						AVM_OS_DEBUG << "on passe bien ici...add_unique(funcName) " << std::endl;
						for( std::size_t idx = 1 ; idx < currentCall.size()-1 ; ++idx )
						{
							std::string argument = currentCall.at(idx).str();
							normalizeArgumentCall(callStack, argument);
							//out2File << currentCall.get( idx ).str() << ", ";
							out2File << argument << ", ";
						}
						AVM_OS_DEBUG << "on passe bien ici...add arguments " << std::endl;
						out2File << currentCall.get( currentCall.size()-1 ).str();

						if (callIndex == callStack.size()-1)
						{
							out2File << ")" << EOL
									<< TAB << ")" << EOL;
						}
						else
						{
							out2File << ")," << EOL;
						}
						AVM_OS_DEBUG << "on passe bien ici...write callset " << std::endl;
					}
				}
			}
		}
		// LOOP INCREMENTATION
		++ callIndex;
	}
}


void ConstraintsInferenceModule::toAcsl_pathCondition(OutStream & out2File,
		const BF & pathCondition, const BuiltinVector & callStack)
{
	BFVector listOfClause;
	ExpressionFactory::collectsClause(pathCondition, listOfClause);
	BF callsConstraints = ExpressionConstructor::newBoolean(true);

	for( const auto & itClause : listOfClause )
	{
		BFVector listOfClauseVars;

		ExpressionFactory::collectVariable(itClause, listOfClauseVars);

		for( const auto & itDepVar : mAllDependancyVariables )
		{
			if ( listOfClauseVars.contains( itDepVar) )
			{
				callsConstraints =
						ExpressionConstructor::andExpr(
								callsConstraints, itClause);
				break;
			}
		}
	}

	std::string strConstraint = callsConstraints.str();

	normalizeExpression( strConstraint );

	out2File << TAB << "==>" << EOL
			<< TAB << strConstraint << EOL;

	for( const auto & itArray : callStack )
	{
		if( itArray.is< ArrayBF >() )
		{
			const ArrayBF & currentCallTrace = itArray.to< ArrayBF >();

			// Check if INVARIANT String field is present
			if( (currentCallTrace.size() >= 4)
				&& INV( currentCallTrace ).is< String >() )
			{
				const String & invariantStr = INV( currentCallTrace ).to< String >();
				if( not invariantStr.getValue().empty() )
				{
					out2File << TAB << "&& " << invariantStr.getValue() << EOL;
				}
			}
		}
	}
}

BF ConstraintsInferenceModule::toAcsl_clean( const BF & constraint,
		const BFVector & variables)
{
	BFVector listOfClause;
	ExpressionFactory::collectsClause(constraint, listOfClause);
	BF callsConstraints = ExpressionConstructor::newBoolean(true);

	for( const auto & itClause : listOfClause )
	{
		BFVector listOfClauseVars;

		ExpressionFactory::collectVariable(itClause, listOfClauseVars);

		for( const auto & itDepVar : variables )
		{
			if ( listOfClauseVars.contains( itDepVar) )
			{
				callsConstraints =
						ExpressionConstructor::andExpr(
								callsConstraints, itClause);
				break;
			}
		}
	}

	return( callsConstraints );
}


BF ConstraintsInferenceModule::builtHypothesis( const ArrayBF & currentCallTrace,
				const BF & pathCondition)
{
	AVM_OS_TRACE << "PC for hypothesis " << pathCondition.str() << std::endl;
	BF hypothesisConstraint = ExpressionConstructor::newBoolean(true);
//	if( currentCallTrace.populated() )
//	{
		if( CALL( currentCallTrace ).is< BuiltinVector >() )
		{
			const BuiltinVector & currentCall =
					CALL( currentCallTrace ).to< BuiltinVector >();
			if( currentCall.nonempty() )
			{
				//collect the call arguments
				BFVector Ins;
				for( std::size_t idx = 1 ; idx < currentCall.size()-1 ; ++idx )
				{
					const BF & term = currentCall.get( idx );
					BFVector variables;
					ExpressionFactory::collectVariable(term, variables);
					Ins.append(variables);
				}
				hypothesisConstraint = ExpressionConstructor::andExpr(
						hypothesisConstraint, toAcsl_clean(pathCondition, Ins));

				AVM_OS_TRACE << "cleaned PC for hypothesis " << hypothesisConstraint.str() << std::endl;

				//replace with \callresult
				std::string hypothesisConstraintStr = hypothesisConstraint.str();
				normalizeExpression(hypothesisConstraintStr);
				hypothesisConstraint = ExpressionConstructor::newIdentifier(hypothesisConstraintStr);

				if( PRE( currentCallTrace ).is< String >() )
				{
					const String & preConditionStr =
							PRE( currentCallTrace ).to< String >();
					if( not (preConditionStr.getValue().empty()) )
					{
						hypothesisConstraint = ExpressionConstructor::andExpr(
								hypothesisConstraint,
								ExpressionConstructor::newIdentifier(preConditionStr.getValue()));
					}

				}
				AVM_OS_TRACE << "hypothesis " << hypothesisConstraint << std::endl;
			}
		}
//	}
	return(hypothesisConstraint);
}


BF ConstraintsInferenceModule::builtRequirement( const ArrayBF & currentCallTrace,
				const BF & pathCondition)
{
	AVM_OS_TRACE << "PC for requirement " << pathCondition.str() << std::endl;
	BF requirementConstraint = ExpressionConstructor::newBoolean(true);
//	if( currentCallTrace.populated() )
//	{
		if( CALL( currentCallTrace ).is< BuiltinVector >() )
		{
			const BuiltinVector & currentCall =
					CALL( currentCallTrace ).to< BuiltinVector >();
			if( currentCall.nonempty() )
			{
				BFVector outVar;
				outVar.append(currentCall.get( currentCall.size()-1));
				requirementConstraint = ExpressionConstructor::andExpr(
						requirementConstraint,
						toAcsl_clean(pathCondition, outVar));
				AVM_OS_TRACE << "cleaned PC for requirement " <<
						requirementConstraint.str() << std::endl;

				//replace with \callresult
				std::string hypothesisConstraintStr = requirementConstraint.str();
				normalizeExpression(hypothesisConstraintStr);
				requirementConstraint = ExpressionConstructor::newIdentifier(hypothesisConstraintStr);

				if( POST( currentCallTrace ).is< String >() )
				{
					const String & postConditionStr =
							POST( currentCallTrace ).to< String >();
					if( not (postConditionStr.getValue().empty()) )
					{
						requirementConstraint = ExpressionConstructor::andExpr(
								requirementConstraint,
								ExpressionConstructor::newIdentifier(postConditionStr.getValue()));
					}

				}
			}
			AVM_OS_TRACE << "requirement " << requirementConstraint << std::endl;
		}
	//}
	return(requirementConstraint);
}

static avm_integer_t integerValueOf(const ExecutionContext & anEC, std::string varNameID)
{
	BF value = anEC.getExecutionData().getDataByNameID( varNameID );
	AVM_OS_TRACE << "Value of " << varNameID << " :> " << value.str() << std::endl;
	if( value.is< Integer >() )
	{
		return value.to< Integer >().toInteger();
	}
	else
	{
		return -1;
	}
}


void ConstraintsInferenceModule::toAcsl_preImpliesPost(
		OutStream & out2File, const BuiltinVector & callStack)
{

	avm_integer_t currentIndex = -1;
	mCallIndex = -1;
	BFVector hypotheses;
	BFVector requirements;

	const BF & PCleaf = mCurrentPathECs.back()->getPathCondition();
	for( const auto & itEC : mCurrentPathECs )
	{
		AVM_OS_TRACE << "Value of mCallIndex :> " << mCallIndex << std::endl;
		currentIndex = integerValueOf(*itEC, "callIndex");
		if(  mCallIndex < currentIndex )//mCallIndex == (currentIndex + 1) )
		{
			mCallIndex++;

			const ArrayBF & currentCallTrace = callStack.at(mCallIndex).to< ArrayBF >();
			BF hypothesis = builtHypothesis(currentCallTrace, itEC->getPathCondition());
			hypotheses.append(hypothesis);
			requirements.append(builtRequirement(currentCallTrace, PCleaf));
		}
	}

	AVM_OS_TRACE << "Compute hypotheses implies requirements " << std::endl;

	if( requirements.nonempty())
	{
		AVM_OS_TRACE << "we have requirements " << std::endl;
		BF impliesConstraint = requirements.back();

		for ( int offset = hypotheses.size()-1;  offset > 0 ; --offset)
		{
			impliesConstraint = ExpressionConstructor::newCode(
					OperatorManager::OPERATOR_IMP_T,
					//ExpressionConstructor::impliesExpr(//to be replaced with implies
					ExpressionConstructor::andExpr(
							requirements[offset-1],
							hypotheses[offset]),
							impliesConstraint);
		}

		impliesConstraint = ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_IMP_T,
				//ExpressionConstructor::orExpr(//to be replaced with implies
				hypotheses[0], impliesConstraint);

		out2File << TAB << "==>" << EOL
							<< TAB << impliesConstraint.str() << EOL << TAB2;
	}
}


} // namespace sep

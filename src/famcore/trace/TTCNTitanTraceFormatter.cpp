/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TTCNTitanTraceFormatter.h"

#include "TraceManager.h"

#include <common/SerializerFeature.h>

#include  <famcore/trace/AvmTraceGenerator.h>

#include <fml/common/ModifierElement.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/expression/ExpressionTypeChecker.h>

#include <fml/symbol/TableOfSymbol.h>

#include <fml/runtime/ExecutionData.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <fml/type/ClassTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>
#include <fml/type/TypeAliasSpecifier.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>

#include <boost/format.hpp>


namespace sep
{


/**
 * CONSTANTS
 * DEFAULT PROFILE
 */
const std::string & TTCNTitanTraceFormatter::DEFAULT_ENVIRONMENT_CHANNEL = "cEnv";


const std::string & TTCNTitanTraceFormatter::DEFAULT_TESTCASES_STARTING_WRAPPER
		= "\t\tf_start();";

const std::string & TTCNTitanTraceFormatter::DEFAULT_TESTCASES_ENDING_WRAPPER
		= "\t\tf_end();";


const std::string & TTCNTitanTraceFormatter::DEFAULT_TESTCASES_STARTING_ENDING_IMPL =
//		%1% --> <system name id>
		"\tfunction f_start() runs on runsOn_%1% { }\n"
		"\tfunction f_end() runs on runsOn_%1% { }";


//	%1% --> <port name id>
//	%2% --> <container/lifeline/component name id>
//	%3% --> <system name id>
//	%4% --> <environment channel id>
//	%5% --> <message type name id>
//	%6% --> <port type name id>
//	%7% --> <port instance name id>
//	%8% --> <port parameters template message>

const std::string & TTCNTitanTraceFormatter::DEFAULT_TESTCASES_SENDING_WRAPPER
		= "\t\t%7%_send( %8% );";

const std::string & TTCNTitanTraceFormatter::DEFAULT_TESTCASES_RECEIVING_WRAPPER
		= "\t\t%7%_receive( %8% );";


const std::string & TTCNTitanTraceFormatter::DEFAULT_TESTCASES_SENDING_IMPL =
		"\tfunction %1%_send( template %5% pdu ) runs on runsOn_%3% {\n"
		"\t%7%.send( %5% );\n"
		"\t}";

const std::string & TTCNTitanTraceFormatter::DEFAULT_TESTCASES_RECEIVING_IMPL =
		"\tfunction %1%_receive( template %5% pdu ) runs on runsOn_%3% {\n"
		"\t\t%7%.receive( %5% );\n"
		"\t}";


const std::string & TTCNTitanTraceFormatter::DEFAULT_ADAPTATION_UTILS_IMPL =
		"\t// A testcase could just call the function below, "
				"when it needs to wait for a timeout.\n"
		"\t// In case the user wants he can activated "
				"altsteps in 'f_start()' to catch events \n"
		"\t// during this time period"

		"\tfunction f_waitForTimeout(float p_duration) {\n"
		"\t\ttimer t;\n"
		"\t\tt.start(p_duration);\n"
		"\t\tt.timeout;\n"
		"\t}";


/*
prototype process::trace_generator as &avm::processor.TRACE_GENERATOR is
 section REPORT
  ...
endsection REPORT

 section PROPERTY
  // 'OMEGA' | 'CVC4' | 'Z3' | 'YICES'
  @solver = 'Z3';

  // 'BASIC' | 'TTCN' | 'TTCN#SDL' | 'TTCN#XLIA'
  @format = 'BASIC';
 endsection PROPERTY

 section TRACE
  ...
 endsection FORMAT
endprototype
*/

////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool TTCNTitanTraceFormatter::configureImpl(const WObject * wfParameterObject)
{
	if( not TTCNBaseTraceFormatter::configureImpl(wfParameterObject) )
	{
		return false;
	}

	const WObject * thePROPERTY = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{
		std::string format =
				Query::getWPropertyString(thePROPERTY, "format", "TTCN#SDL");

//		mUseMessageTemplateWithParameters = Query::getRegexWPropertyBoolean(
//			thePROPERTY, CONS_WID3("template", "with", "parameters"), true);
//
//		mUseMessageFunctionWithParameters = Query::getRegexWPropertyBoolean(
//			thePROPERTY, CONS_WID3("function", "with", "parameters"), true);

		std::string message =
				Query::getWPropertyString(thePROPERTY, "message", "FUNCTION");
		if( message == "FUNCTION" )
		{
			mUseMessageFunctionWithParameters = true;
		}
		else // TEMPLATE
		{
			mUseMessageTemplateWithParameters =
				Query::getWPropertyBoolean(thePROPERTY, "parameterized", true);
		}
	}
	else
	{
		return false;
	}

	const WObject * theFORMAT = Query::getWSequenceOrElse(
			wfParameterObject, "interface", "format");

	if( theFORMAT != WObject::_NULL_ )
	{
		mControlModuleName = Query::getRegexWPropertyString(theFORMAT,
				CONS_WID3("control", "module", "name"),
				"TTCN_ControlPart");

		mDeclarationsModuleName = Query::getRegexWPropertyString(theFORMAT,
				CONS_WID3("declarations", "module", "name"),
				"TTCN_Declarations");

		mTemplatesModuleName = Query::getRegexWPropertyString(theFORMAT,
				CONS_WID3("templates", "module", "name"),
				"TTCN_Templates");

		mTestcasesModuleName = Query::getRegexWPropertyString(theFORMAT,
				CONS_WID3("testcases", "module", "name"),
				"TTCN_TestsAndControl");
	}

	const WObject * theWRAPPER =
			Query::getWSequence(wfParameterObject, "wrapper");

	std::size_t error = 0;

	if( theWRAPPER != WObject::_NULL_ )
	{
		error += configureFormatter(
				theWRAPPER, mTestcasesStartingWrapper,
				CONS_WID2("testcases", "starting"), true ) ? 0 : 1;

		error += configureFormatter(
				theWRAPPER, mTestcasesEndingWrapper,
				CONS_WID2("testcases", "ending"), true ) ? 0 : 1;


		error += configureFormatter(
				theWRAPPER, mTestcasesSendingWrapper,
				CONS_WID2("testcases", "sending"), true ) ? 0 : 1;

		error += configureFormatter(
				theWRAPPER, mTestcasesReceivingWrapper,
				CONS_WID2("testcases", "receiving"), true ) ? 0 : 1;
	}


	const WObject * theIMPLEMENTATION = Query::getWSequence(
			wfParameterObject, "implementation");
	if( theIMPLEMENTATION != WObject::_NULL_ )
	{
		error += configureFormatter(
				theIMPLEMENTATION, mAdaptationStartingEndingImpl,
				CONS_WID2("adaptation#starting", "ending"), true ) ? 0 : 1;


		error += configureFormatter(
				theIMPLEMENTATION, mAdaptationSendingImpl,
				CONS_WID2("adaptation", "sending"), true ) ? 0 : 1;

		error += configureFormatter(
				theIMPLEMENTATION, mAdaptationReceivingImpl,
				CONS_WID2("adaptation", "receiving"), true ) ? 0 : 1;

		error += configureFormatter(
				theIMPLEMENTATION, mAdaptationUtilsImpl,
				CONS_WID2("adaptation", "utils"), true ) ? 0 : 1;
	}

	// Default typename mapping
	mapofTreatedTypeName[ "string" ] = "charstring";

	return( error == 0 );
}


////////////////////////////////////////////////////////////////////////////////
// FORMAT API
////////////////////////////////////////////////////////////////////////////////

void TTCNTitanTraceFormatter::format(TraceManager & aTraceManager)
{
	formatTraceManager(aTraceManager);

	// Generation des fichiers TTCN_
	//
	std::string TTCN_folder = mTraceGenerator.getLastFolder().location;
	std::ios_base::openmode theOpenMode = std::ios_base::out;

	StringOutStream ossScenarioFileURL;
	std::string filename;

	filename = mDeclarationsModuleName;
	if( filename.empty() )
	{
		filename = "TTCN_Declarations";
	}
	ossScenarioFileURL << TTCN_folder << "/" << filename << ".ttcn3";
	std::ofstream declStream(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( declStream.is_open() )
	{
		declStream << outModuleDeclaration.str() << std::endl << std::endl;
		declStream.close();
	}

	filename = mTemplatesModuleName;
	if( filename.empty() )
	{
		filename = "TTCN_Templates";
	}
	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/" << filename << ".ttcn3";
	std::ofstream templStream(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( templStream.is_open() )
	{
		templStream << outModuleTemplate.str() << std::endl << std::endl;
		templStream.close();
	}

	filename = mAdaptationModuleName;
	if( filename.empty() )
	{
		filename = "TTCN_Adaptation";
	}
	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/" << filename << ".ttcn3";
	std::ofstream adaptStream(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( adaptStream.is_open() )
	{
		adaptStream << outModuleAdaptation.str() << std::endl << std::endl;
		adaptStream.close();
	}

	filename = mTestcasesModuleName;
	if( filename.empty() )
	{
		filename = "TTCN_TestsAndControl";
	}
	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/" << filename << ".ttcn3";
	std::ofstream testStream(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( testStream.is_open() )
	{
		testStream << outModuleTestsAndControl.str() << std::endl << std::endl;
		testStream.close();
	}

	filename = mControlModuleName;
	if( filename.empty() )
	{
		filename = "TTCN_ControlPart";
	}
	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/" << filename << ".ttcn3";
	std::ofstream ctrlStream(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( ctrlStream.is_open() )
	{
		ctrlStream << outModuleControlPart.str() << std::endl << std::endl;
		ctrlStream.close();
	}

	// Affichage des resultats dans le fichier ttcn/trace
	//
	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/TTCN_global.ttcn3";
	OutStream outGlobalTTCN;
	if ( outGlobalTTCN.open(ossScenarioFileURL.str(), theOpenMode) )
	{
		outGlobalTTCN << AVM_SPC1_INDENT
			<< "/*" << std::endl
			<< EMPHASIS("outModuleDeclaration", '*', 79, true)
			<< " */" << std::endl
			<< outModuleDeclaration.str() << std::endl << std::endl

			<< "/*" << std::endl
			<< EMPHASIS("outModuleTemplate", '*', 79, true)
			<< " */" << std::endl
			<< outModuleTemplate.str() << std::endl << std::endl

			<< "/*" << std::endl
			<< EMPHASIS("outModuleAdaptation", '*', 79, true)
			<< " */" << std::endl
			<< outModuleAdaptation.str() << std::endl << std::endl

			<< "/*" << std::endl
			<< EMPHASIS("outModuleTestsAndControl", '*', 79, true)
			<< " */" << std::endl
			<< outModuleTestsAndControl.str() << std::endl << std::endl

			<< "/*" << std::endl
			<< EMPHASIS("outModuleControlPart", '*', 79, true)
			<< " */" << std::endl
			<< outModuleControlPart.str() << std::endl << std::endl
			<< END_INDENT;
	}

	mTraceGenerator.beginStream();
	while( mTraceGenerator.hasStream() )
	{
		OutStream & out = mTraceGenerator.currentStream();

AVM_IF_DEBUG_FLAG( PROCESSOR )
	aTraceManager.toStream( out );
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )

		out << AVM_SPC1_INDENT
			<< "/*" << std::endl
			<< EMPHASIS("outModuleDeclaration", '*', 79, true)
			<< " */" << std::endl
			<< outModuleDeclaration.str() << std::endl << std::endl

			<< "/*" << std::endl
			<< EMPHASIS("outModuleTemplate", '*', 79, true)
			<< " */" << std::endl
			<< outModuleTemplate.str() << std::endl << std::endl

			<< "/*" << std::endl
			<< EMPHASIS("outModuleAdaptation", '*', 79, true)
			<< " */" << std::endl
			<< outModuleAdaptation.str() << std::endl << std::endl

			<< "/*" << std::endl
			<< EMPHASIS("outModuleTestsAndControl", '*', 79, true)
			<< " */" << std::endl
			<< outModuleTestsAndControl.str() << std::endl << std::endl

			<< "/*" << std::endl
			<< EMPHASIS("outModuleControlPart", '*', 79, true)
			<< " */" << std::endl
			<< outModuleControlPart.str() << std::endl << std::endl
			<< END_INDENT;
	}

	mTraceGenerator.closeStream();
}

void TTCNTitanTraceFormatter::formatTraceManager(
		const TraceManager & aTraceManager)
{
	// Nom du system
	mSystemNameID = mTraceGenerator.
			getConfiguration().getExecutableSystem().getNameID();

	// module TTCN_Declarations
	// module TTCN_Templates
	// module TTCN_Adaptation
	// module TTCN_TestsAndControl
	// module TTCN_ControlPart
	//
	formatModuleDeclarationsHeader(outModuleDeclaration);
	formatModuleTemplatesHeader(outModuleTemplate);
	formatModuleAdaptationHeader(outModuleAdaptation);
	formatModuleTestsAndControlHeader(outModuleTestsAndControl);
	formatModuleControlPartHeader(outModuleControlPart);

	std::string testCaseName;

	for( const auto & itTraceElement : aTraceManager )
	{
		mCurrentTraceSequence = itTraceElement;

		testCaseName = formatTestcaseName( *mCurrentTraceSequence );

		formatModuleTestsAndControlTestcaseHeader(
				outModuleTestsAndControl, testCaseName);

		formatTraceSequence( *mCurrentTraceSequence );

		formatModuleTestsAndControlTestcaseEnd(outModuleTestsAndControl);

		formatModuleControlPartBody(outModuleControlPart, testCaseName);
	}

	formatDeclarationChannels();
	formatModuleDeclarationsEnd(outModuleDeclaration);

	formatModuleTemplatesEnd(outModuleTemplate);
	formatModuleAdaptationEnd(outModuleAdaptation);
	formatModuleTestsAndControlEnd(outModuleTestsAndControl);
	formatModuleControlPartEnd(outModuleControlPart);
}


void TTCNTitanTraceFormatter::formatTracePointImpl(const TracePoint & aTracePoint)
{
	if( aTracePoint.object->is< InstanceOfPort >()
		&& aTracePoint.isOpEnv() )
	{
		// Assume only one type or template function declaration per object
		bool isFirstTime4Object = setofTracePointObjectName.insert(
				aTracePoint.object->getNameID() ).second;

		if( isFirstTime4Object )
		{
			formatDeclaration( aTracePoint );
		}

		if( mUseMessageFunctionWithParameters )
		{
			formatTestcaseWithTemplateFunctionWithParameters
			(ossTemplateList, aTracePoint, isFirstTime4Object);
		}
		else if( mUseMessageTemplateWithParameters )
		{
			formatTestcaseWithTemplateWithParameters(
					ossTemplateList, aTracePoint, isFirstTime4Object);
		}
		else
		{
			formatTestcaseWithTemplateWithoutParameters(
					ossTemplateList, aTracePoint, isFirstTime4Object);
		}
	}
}


void TTCNTitanTraceFormatter::formatModuleDeclarationsHeader(OutStream & out)
{
	out << "module " << mDeclarationsModuleName << " {" << std::endl;
}

void TTCNTitanTraceFormatter::formatModuleDeclarationsEnd(OutStream & out)
{
	out << TAB << "// Used Type definitions" << std::endl
		<< outDeclarationTypedefBuffer.str();

	out << TAB << "// Communicating Message-Record declarations" << std::endl
		<< outDeclarationMessageRecordBuffer.str();

	/*!! TODO code à supprimer après validation nouveau code pour les channels
	out << TAB << "// Ports declaration" << std::endl
		<< TAB << "type port port_cEnv message {" << std::endl
		<< portsDeclaration.str()
		<< TAB << "}" << std::endl << std::endl;
	*/

	out << TAB << "// Channels & ports declaration" << std::endl
		<< outChannelDefinitionBuffer.str();

	// fin du module TTCN_Declarations
	out << "}" << std::endl;
}


void TTCNTitanTraceFormatter::formatModuleTemplatesHeader(OutStream & out)
{
	out << "module " << mTemplatesModuleName << " {" << std::endl
		<< TAB << "import from " << mDeclarationsModuleName << " all;"
		<< std::endl << std::endl;
}

void TTCNTitanTraceFormatter::formatModuleTemplatesEnd(OutStream & out)
{
	out << ossTemplateList.str()
		<< "}" << std::endl;
}



void TTCNTitanTraceFormatter::formatModuleAdaptationHeader(OutStream & out)
{
	out << "module " << mAdaptationModuleName << " {" << std::endl
		<< TAB << "import from " << mDeclarationsModuleName << " all;"
		<< std::endl << std::endl;
}

void TTCNTitanTraceFormatter::formatModuleAdaptationEnd(OutStream & out)
{
	out << TAB << "// Components declaration" << std::endl
		<< TAB << "type component runsOn_" << mSystemNameID << " {" << std::endl
		<< TAB2 << "// Port instance declaration" << std::endl
		<< outPortInstanceDeclarationBuffer.str()
		<< channelsDeclaration.str()
		<< TAB << "}"
		<< std::endl << std::endl
		<< TAB << "type component " << mSystemNameID << " {" << std::endl
		<< channelsDeclaration.str()
		<< TAB << "}"
		<< std::endl << std::endl
		<< TAB << "// Implementation of port-instance mapping to system"
		<< std::endl
		<< TAB << "function f_mapPortsToSystem() runs on runsOn_"
		<< mSystemNameID << " {" << std::endl
		<< outPortInstanceMappingToSystemBuffer.str()
		<< TAB << "}"
		<< std::endl << std::endl
		<< TAB << "// Implementation of port-instance unmapping from system"
		<< std::endl
		<< TAB << "function f_unmapPortsToSystem() runs on runsOn_"
		<< mSystemNameID << " {" << std::endl
		<< outPortInstanceUnmappingToSystemBuffer.str()
		<< TAB << "}"
		<< std::endl << std::endl;


	boost::format utilsFormatter( mAdaptationUtilsImpl);
	utilsFormatter.exceptions( boost::io::no_error_bits );
	out << TAB << "// Implementation of utility functions"
		<< std::endl
		<< utilsFormatter
		% mSystemNameID
		<< std::endl << std::endl;

	// Starting / Ending Testcases wrapper Implementation

	boost::format startingEndingFormatter( mAdaptationStartingEndingImpl);
	startingEndingFormatter.exceptions( boost::io::no_error_bits );
	out << TAB << "// Implementation of testcases Starting / Ending wrappers"
		<< std::endl
		<< startingEndingFormatter
		% mSystemNameID
		<< std::endl << std::endl;

	out << TAB << "// Implementation of testcases Sending / Receiving wrappers"
		<< std::endl
		<< ossAdaptationList.str()
		<< std::endl;

	out << "}" << std::endl;
}



void TTCNTitanTraceFormatter::formatModuleTestsAndControlHeader(OutStream & out)
{
	out << "module " << mTestcasesModuleName << " {" << std::endl << std::endl
		<< TAB << "import from " << mAdaptationModuleName   << " all;" << std::endl
//		<< TAB << "import from " << mDeclarationsModuleName << " all;" << std::endl
		<< TAB << "import from " << mTemplatesModuleName    << " all;" << std::endl
		<< std::endl;
}

void TTCNTitanTraceFormatter::formatModuleTestsAndControlEnd(OutStream & out)
{
	out << "}" << std::endl;
}

void TTCNTitanTraceFormatter::formatModuleTestsAndControlTestcaseHeader(
		OutStream & out, const std::string & testcaseName)
{
	formatTestcaseCoverageInfo( out );

//	boost::format startingFormatter( mTestcasesStartingWrapper);
//	startingFormatter.exceptions( boost::io::no_error_bits );

	out << TAB << "testcase " << testcaseName << "() "
		<< "runs on runsOn_" << mSystemNameID
		<< " system " << mSystemNameID << " {"
		<< std::endl
		<< mTestcasesStartingWrapper
		<< std::endl;

	// Mapping of Channels
	SetOfChannelIterator it = setofCommunicationgChannel.begin();
	for( ; it != setofCommunicationgChannel.end() ; ++it)
	{
		out << TAB2 << "map(self:" << (*it)->getNameID()
			<< ", system:" << (*it)->getNameID() << ");"
			<< std::endl;
	}
	ossTestcaseList.str("");
}

void TTCNTitanTraceFormatter::formatModuleTestsAndControlTestcaseEnd(
		OutStream & out)
{
	boost::format endingFormatter( mTestcasesEndingWrapper);
	endingFormatter.exceptions( boost::io::no_error_bits );

	out << ossTestcaseList.str()
		<< endingFormatter
		<< std::endl
		<< TAB << "}" << std::endl << std::endl;
}

void TTCNTitanTraceFormatter::formatModuleControlPartHeader(OutStream & out)
{
	out << "module " << mControlModuleName << " {" << std::endl << std::endl
		<< TAB << "import from " << mTestcasesModuleName << " all;" << std::endl
		<< std::endl
		<< TAB << "control {" << std::endl;
}

void TTCNTitanTraceFormatter::formatModuleControlPartEnd(OutStream & out)
{
	out << TAB << "}" << std::endl
		<< "}" << std::endl;
}

void TTCNTitanTraceFormatter::formatModuleControlPartBody(
		OutStream & out, const std::string & testcaseName)
{
	out << TAB2 << "execute( " << testcaseName << "() );" << std::endl;
}



void TTCNTitanTraceFormatter::formatTestcase(
		StringOutStream & outTemplateMessageParameterName,
		StringOutStream & outTemplateParameters, const TracePoint & aTracePoint)
{
	const InstanceOfPort & aPort = aTracePoint.object->to< InstanceOfPort >();

	// TEST CASES
	StringOutStream ossActionName;

	ossActionName << ( aPort.hasRoutingChannel() ?
				aPort.getRoutingChannel()->getNameID() :
				DEFAULT_ENVIRONMENT_CHANNEL )
			<< ( (aTracePoint.op == AVM_OPCODE_INPUT_ENV) ?
					"_send_" : "_receive_" ) << aPort.getNameID();
//
//	ossTestcaseList << TAB2 << ossActionName.str()
//			<< "(" << templateName.str() << ");" << std::endl;


	std::string strMessageTypeName  = messageTypeName( aPort );
	std::string strPortTypeName     = portTypeName( aPort );
	std::string strPortInstanceName = portInstanceName( aPort );

	if( setofAdaptationPortFunction.insert(ossActionName.str()).second )
	{
		boost::format adaptationFormatter(
				(aTracePoint.op == AVM_OPCODE_INPUT_ENV) ?
					mAdaptationSendingImpl : mAdaptationReceivingImpl);
		adaptationFormatter.exceptions( boost::io::no_error_bits );

		ossAdaptationList << adaptationFormatter
				% aPort.getNameID()
				% mCurrentTracePoint->RID.getLifeline(aPort).getNameID()
				% mSystemNameID
				% ( aPort.hasRoutingChannel() ?
					aPort.getRoutingChannel()->getNameID() :
					DEFAULT_ENVIRONMENT_CHANNEL )
				% strMessageTypeName
				% strPortTypeName
				% strPortInstanceName
				% outTemplateMessageParameterName.str()
				<< std::endl;
	}

//	%1% --> <port name id>
//	%2% --> <container/lifeline/component name id>
//	%3% --> <system name id>
//	%4% --> <environment channel>
//	%5% --> <message type name id>
//	%6% --> <port type name id>
//	%7% --> <port instance name id>
//	%8% --> <port parameters template message>

	boost::format wrapperFormatter(
			(aTracePoint.op == AVM_OPCODE_INPUT_ENV) ?
				mTestcasesSendingWrapper : mTestcasesReceivingWrapper);
	wrapperFormatter.exceptions( boost::io::no_error_bits );

	if( outTemplateParameters.nonempty() )
	{
		outTemplateMessageParameterName << "( " << outTemplateParameters.str() << " )";
	}
	ossTestcaseList << wrapperFormatter
			% aPort.getNameID()
			% mCurrentTracePoint->RID.getLifeline(aPort).getNameID()
			% mSystemNameID
			% ( aPort.hasRoutingChannel() ?
				aPort.getRoutingChannel()->getNameID() :
				DEFAULT_ENVIRONMENT_CHANNEL )
			% strMessageTypeName
			% strPortTypeName
			% strPortInstanceName
			% outTemplateMessageParameterName.str()
			<< std::endl;
}


} /* namespace sep */

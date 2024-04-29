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
 *  Alain Faivre (CEA LIST) alain.faivre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TTCNTraceFormatter.h"

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

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/ClassTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>
#include <fml/type/TypeAliasSpecifier.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>


namespace sep
{


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

bool TTCNTraceFormatter::configureImpl(const WObject * wfParameterObject)
{
	if( not TTCNBaseTraceFormatter::configureImpl(wfParameterObject) )
	{
		return false;
	}

	const WObject * thePROPERTY = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("property", "PROPERTY"));

	if( thePROPERTY == WObject::_NULL_ )
	{
		return false;
	}

	std::string format =
			Query::getWPropertyString(thePROPERTY, "format", "TTCN.SDL");

	isSDLFlag = ( format.find("SDL") != std::string::npos );

	// Default typename mapping
	mapofTreatedTypeName[ "string" ] = "charstring";

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// FORMAT API
////////////////////////////////////////////////////////////////////////////////

void TTCNTraceFormatter::format(TraceManager & aTraceManager)
{
	formatTraceManager(aTraceManager);

	// Generation des fichiers TTCN_
	//
	std::string TTCN_folder = mTraceGenerator.getLastFolder().location;
	std::ios_base::openmode theOpenMode = std::ios_base::out;
	StringOutStream ossScenarioFileURL;

	ossScenarioFileURL << TTCN_folder << "/TTCN_Declarations.ttcn3";
	std::ofstream fileStream1(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( fileStream1.is_open() )
	{
		fileStream1 << outModuleDeclaration.str() << std::endl << std::endl;
		fileStream1.close();
	}

	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/TTCN_Templates.ttcn3";
	std::ofstream fileStream2(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( fileStream2.is_open() )
	{
		fileStream2 << outModuleTemplate.str() << std::endl << std::endl;
		fileStream2.close();
	}

	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/TTCN_TestsAndControl.ttcn3";
	std::ofstream fileStream3(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( fileStream3.is_open() )
	{
		fileStream3 << outModuleTestsAndControl.str()
				<< std::endl << std::endl;
		fileStream3.close();
	}

	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/TTCN_ControlPart.ttcn3";
	std::ofstream fileStream4(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( fileStream4.is_open() )
	{
		fileStream4 << outModuleControlPart.str() << std::endl << std::endl;
		fileStream4.close();
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

void TTCNTraceFormatter::formatTraceManager(const TraceManager & aTraceManager)
{
	// Nom du system
	mSystemNameID = mTraceGenerator.
			getConfiguration().getExecutableSystem().getNameID();

	// module TTCN_Declarations
	// module TTCN_Templates
	// module TTCN_TestsAndControl
	// module TTCN_ControlPart
	//
	formatModuleDeclarationsHeader(outModuleDeclaration);
	formatModuleTemplatesHeader(outModuleTemplate);
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
	formatModuleTestsAndControlEnd(outModuleTestsAndControl);
	formatModuleControlPartEnd(outModuleControlPart);
}


void TTCNTraceFormatter::formatTracePointImpl(const TracePoint & aTracePoint)
{
	formatDeclaration( aTracePoint );

	format_TTCN_Templates( aTracePoint );
}


void TTCNTraceFormatter::formatModuleDeclarationsHeader(OutStream & out)
{
	out << "module TTCN_Declarations {" << std::endl;
}

void TTCNTraceFormatter::formatModuleDeclarationsEnd(OutStream & out)
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

	out << TAB << "// TSI and MTC component declaration" << std::endl
		<< TAB << "type component runsOn_" << mSystemNameID << " {" << std::endl;

	/*!! TODO code à supprimer après validation nouveau code pour les channels
	out << TAB2 << "port port_cEnv cEnv;" << std::endl;
	*/
	out << channelsDeclaration.str()

		<< TAB << "}" << std::endl
		<< TAB << "type component " << mSystemNameID << " {" << std::endl;

	/*!! TODO code à supprimer après validation nouveau code pour les channels
	out << TAB2 << "port port_cEnv cEnv;" << std::endl;
	*/
	out << channelsDeclaration.str()

		<< TAB << "}" << std::endl

		<< "}" << std::endl; // fin du module TTCN_Declarations
}


void TTCNTraceFormatter::formatModuleTemplatesHeader(OutStream & out)
{
	out << "module TTCN_Templates {" << std::endl
		<< TAB << "import from TTCN_Declarations all;" << std::endl << std::endl;
}

void TTCNTraceFormatter::formatModuleTemplatesEnd(OutStream & out)
{
	out << templateList.str()
		<< "}" << std::endl;
}

void TTCNTraceFormatter::formatModuleTestsAndControlHeader(OutStream & out)
{
	out << "module TTCN_TestsAndControl {" << std::endl << std::endl
		<< TAB << "import from TTCN_Declarations all;" << std::endl
		<< TAB << "import from TTCN_Templates all;" << std::endl << std::endl;

	out << TAB << "altstep RTDS_fail() runs on "
		<< mSystemNameID << " {" << std::endl;
	SetOfChannelIterator it = setofCommunicationgChannel.begin();
	for( ; it != setofCommunicationgChannel.end() ; ++it )
	{
		out << TAB2 << "[]" << (*it)->getNameID()
			<< ".receive { setverdict(fail); };"
			<< std::endl;
	}
	out << TAB << "}" << std::endl << std::endl;
}

void TTCNTraceFormatter::formatModuleTestsAndControlEnd(OutStream & out)
{
	out << "}" << std::endl;
}

void TTCNTraceFormatter::formatModuleTestsAndControlTestcaseHeader(
		OutStream & out, const std::string & testcaseName)
{
	formatTestcaseCoverageInfo( out );

	out << TAB << "testcase " << testcaseName << "() "
		<< "runs on runsOn_" << mSystemNameID
		<< " system " << mSystemNameID << " {" << std::endl
		<< TAB2 << "activate(RTDS_fail());" << std::endl;

	// Mapping of Channels
	SetOfChannelIterator it = setofCommunicationgChannel.begin();
	for( ; it != setofCommunicationgChannel.end() ; ++it )
	{
		out << TAB2 << "map(self:" << (*it)->getNameID()
			<< ", system:" << (*it)->getNameID() << ");"
			<< std::endl;
	}
	ossTestcaseList.str("");
}

void TTCNTraceFormatter::formatModuleTestsAndControlTestcaseEnd(OutStream & out)
{
	out << ossTestcaseList.str()
		<< TAB2 << "setverdict(pass);" << std::endl
		<< TAB << "}" << std::endl << std::endl;
}

void TTCNTraceFormatter::formatModuleControlPartHeader(OutStream & out)
{
	out << "module TTCN_ControlPart {" << std::endl << std::endl
		<< TAB << "import from TTCN_TestsAndControl all;" << std::endl << std::endl

		<< TAB << "control {" << std::endl;
}

void TTCNTraceFormatter::formatModuleControlPartEnd(OutStream & out)
{
	out << TAB << "}" << std::endl
		<< "}" << std::endl;
}

void TTCNTraceFormatter::formatModuleControlPartBody(
		OutStream & out, const std::string & testcaseName)
{
	out << TAB2 << "execute( " << testcaseName << "() );" << std::endl;
}


void TTCNTraceFormatter::format_TTCN_Templates(const TracePoint & aTracePoint)
{
	if( aTracePoint.object->is< InstanceOfPort >()
		&& aTracePoint.isOpEnv() )
	{
		const InstanceOfPort & aPort = aTracePoint.object->to< InstanceOfPort >();

		StringOutStream templateName;
		templateName << aPort.getNameID()
				<< "_trace" << mCurrentTraceSequence->tid
				<< "_tpid_" << aTracePoint.tpid;

		ArrayOfBF::const_iterator it = aPort.getParameters().begin();
		ArrayOfBF::const_iterator endIt = aPort.getParameters().end();
		if( isSDLFlag )
		{
			// ATTENTION : dans ce cas on ne  prend pas en compte le dernier paramètre
			// qui correspond au PID de l'émetteur
			//
			endIt = endIt - 1;
		}

		if( aPort.hasParameter() && it != endIt )
		{
			// signal avec au moins un paramètre à afficher
			//
			templateList << TAB << "template " << aPort.getNameID() << " ";
			templateList << templateName.str() << " := {";

			templateList << INCR_INDENT;
			for( std::size_t offset = 0 ; it != endIt ; ++it , ++offset )
			{
				templateList << ( (offset == 0) ? "" : "," ) << std::endl;

				// paramètre anonyme
				if( (*it).is< BaseTypeSpecifier >() )
				{
					// le nom
					templateList << TAB << "unamed";
					// la valeur
					templateList << " := " << aTracePoint.val(offset).str();
				}
				// paramètre nommé
				else if( (*it).is< InstanceOfData >() )
				{
					InstanceOfData * aParam = (*it).to_ptr< InstanceOfData >();

					format_TTCN_Templates(
							aTracePoint.val(offset),
							aParam->getTypeSpecifier(),
							aParam->getNameID(), offset);
				}
				// #bind expression parameter
				else
				{
					// Cf Arnault si cas erreur ???
				}
			}
			templateList << std::endl << DECR_INDENT_TAB << "}"
				<< std::endl << std::endl;
		}
		else
		{
			// signal sans paramètre à afficher
			//
			templateList << TAB << "template " << aPort.getNameID()
					<< " " << templateName.str() << " := ?;"
					<< std::endl << std::endl;
		}

		StringOutStream outTemplateParameters;

		formatTestcase(templateName, outTemplateParameters, aTracePoint);

	}
}

void TTCNTraceFormatter::format_TTCN_Templates(
		const BF & value, const BaseTypeSpecifier & aTS,
		const std::string & aParamName, std::size_t anOffset)
{
	// Affichage de "nom := "
	if( (aParamName[0] == '$') || (aParamName[0] == '#') )
	{
		std::string newParamName = aParamName.substr(1);
		templateList << TAB << "param" << newParamName << " := " ;
	}
	else
	{
		templateList << TAB << aParamName << " := " ;
	}

	if( aTS.hasTypeContainer() )
	{
		const ContainerTypeSpecifier & containerTS =
				aTS.to< ContainerTypeSpecifier >();
//		std::size_t sizeT = containerTS.size();

		switch( containerTS.getTypeSpecifierKind() )
		{
			case TYPE_VECTOR_SPECIFIER:
			case TYPE_REVERSE_VECTOR_SPECIFIER:
			case TYPE_LIST_SPECIFIER:
			case TYPE_SET_SPECIFIER:
			case TYPE_FIFO_SPECIFIER:
			case TYPE_LIFO_SPECIFIER:
			case TYPE_MULTI_FIFO_SPECIFIER:
			case TYPE_MULTI_LIFO_SPECIFIER:
			default:
			{
				templateList << value.str();
//				if( not aTS.isTypedSimple() )
//				{
//					format_TTCN_Templates(aTracePoint,
//							containerTS.getTypeSpecifier(), aParamName);
//				}
				break;
			}
		}
	}

	else if( aTS.isTypedClass() )
	{
		const ClassTypeSpecifier & structTS = aTS.to< ClassTypeSpecifier >();
		std::size_t sizeT = structTS.size();

		Symbol aField;

		templateList << "{" << EOL_INCR_INDENT;

		for( std::size_t idx = 0 ; idx < sizeT ; ++idx )
		{
			templateList << ( (idx == 0) ? "" : "," ) << std::endl;

			aField = structTS.getSymbolData(idx);

			format_TTCN_Templates(
					value.to< ArrayBF >().at( idx ),
					aField.getTypeSpecifier(), aField.getNameID(), idx);
		}

		templateList << std::endl << DECR_INDENT_TAB << "}";
	}

	else if( aTS.isTypedEnum() )
	{
		const EnumTypeSpecifier & enumTS = aTS.to< EnumTypeSpecifier >();

		// Affichage de la valeur numérique
		if( value.invalid() )
		{
			templateList << "nullptr";
		}
		else if( value.is< ArrayBF >() )
		{
			templateList << "ARRAY<?>";
		}
		else if( value.is< InstanceOfData >() )
		{
			const InstanceOfData & aSymbol = value.to< InstanceOfData >();

			if( not enumTS.hasSymbolData(aSymbol) )
			{
				AVM_OS_ERROR_ALERT << "TTCNTraceFormatter::format_TTCN_Templates"
						<< " :> Unexpected symbol\n<< " << str_header( aSymbol )
						<< " >>\nfor the enum type << "
						<< enumTS.getFullyQualifiedNameID() << " >> !!!"
						<< SEND_ALERT;
			}

			templateList << aSymbol.getNameID();
		}
		else
		{
			const Symbol & aSymbol = enumTS.getSymbolDataByValue(value);
			if( aSymbol.valid() )
			{
				templateList << aSymbol.getNameID();
			}
			else
			{
				AVM_OS_ERROR_ALERT
						<< "TTCNTraceFormatter::format_TTCN_Templates"
							" :>\nUnexpected symbol value << "
						<< value.str() << " >> for the enum type << "
						<< enumTS.getFullyQualifiedNameID()
						<< " >> for the parameter << param"
						<< aParamName << " >> !!!"
						<< SEND_ALERT;

				templateList << enumTS.getNameID()
						<< "[ " << value.str() << " ]";
			}
		}
	}

	else if( value.is< Character >() )
	{
		// On remplace 'x' par "x"
		templateList << value.to< Character >().strChar('"');
	}
	else //if( aTS.isTypedSimple() )
	{
		// Affichage de la valeur numérique
		if( value.invalid() )
		{
			templateList << "nullptr";
		}
		else if( value.is< ArrayBF >() )
		{
			templateList << value.to< ArrayBF >().at( anOffset ).str();
		}
		else
		{
			templateList << value.str();
		}
	}
}


void TTCNTraceFormatter::formatTestcase(StringOutStream & outTemplateName,
		StringOutStream & outTemplateParameters, const TracePoint & aTracePoint)
{
	const InstanceOfPort & aPort = aTracePoint.object->to< InstanceOfPort >();

	if( aTracePoint.op	== AVM_OPCODE_INPUT_ENV )
	{
		if( aPort.hasRoutingChannel() )
		{
			ossTestcaseList << TAB2
					<< aPort.getRoutingChannel()->getNameID()
					<< ".send(" << outTemplateName.str() << ");" << std::endl;
		}
		else
		{
			ossTestcaseList << TAB2 << "cEnv.send("
					<< outTemplateName.str() << ");" << std::endl;
		}
	}
	else
	{
		if( aPort.hasRoutingChannel() )
		{
			ossTestcaseList << TAB2
					<< aPort.getRoutingChannel()->getNameID()
					<< ".receive(" << outTemplateName.str() << ");"
					<< std::endl;
		}
		else
		{
			ossTestcaseList << TAB2 << "cEnv.receive("
					<< outTemplateName.str() << ");" << std::endl;
		}
	}
}

} /* namespace sep */

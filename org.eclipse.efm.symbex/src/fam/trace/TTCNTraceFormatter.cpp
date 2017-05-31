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

#include <fam/trace/AvmTraceGenerator.h>

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

bool TTCNTraceFormatter::configureImpl(WObject * wfParameterObject)
{
	WObject * thePROPERTY = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("property", "PROPERTY"));

	if( thePROPERTY == WObject::_NULL_ )
	{
		return false;
	}

	std::string format =
			Query::getWPropertyString(thePROPERTY, "format", "TTCN.SDL");

	isSDLFlag = ( format.find("SDL") != std::string::npos );

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// FORMAT API
////////////////////////////////////////////////////////////////////////////////

void TTCNTraceFormatter::format(TraceManager & aTraceManager)
{
	format_impl(aTraceManager);

	// Generation des fichiers TTCN_
	//
	std::string TTCN_folder = mTraceGenerator.getLastFolder().location;
	std::ios_base::openmode theOpenMode = std::ios_base::out;
	std::ostringstream ossScenarioFileURL;

	ossScenarioFileURL << TTCN_folder << "/TTCN_Declarations.ttcn3";
	std::ofstream fileStream1(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( fileStream1.is_open() )
	{
		fileStream1 << module_TTCN_Declarations.str() << std::endl << std::endl;
		fileStream1.close();
	}

	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/TTCN_Templates.ttcn3";
	std::ofstream fileStream2(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( fileStream2.is_open() )
	{
		fileStream2 << module_TTCN_Templates.str() << std::endl << std::endl;
		fileStream2.close();
	}

	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/TTCN_TestsAndControl.ttcn3";
	std::ofstream fileStream3(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( fileStream3.is_open() )
	{
		fileStream3 << module_TTCN_TestsAndControl.str()
				<< std::endl << std::endl;
		fileStream3.close();
	}

	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/TTCN_ControlPart.ttcn3";
	std::ofstream fileStream4(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( fileStream4.is_open() )
	{
		fileStream4 << module_TTCN_ControlPart.str() << std::endl << std::endl;
		fileStream4.close();
	}

	// Affichage des resultats dans le fichier ttcn/trace
	//
	ossScenarioFileURL.str("");
	ossScenarioFileURL << TTCN_folder << "/TTCN_global.ttcn3";
	std::ofstream fileStream5(ossScenarioFileURL.str().c_str(), theOpenMode);
	if ( fileStream5.is_open() )
	{
		fileStream5 << "****************************************************" << std::endl;
		fileStream5 << "          module_TTCN_Declarations                  " << std::endl;
		fileStream5 << "****************************************************" << std::endl;
		fileStream5 << module_TTCN_Declarations.str() << std::endl << std::endl;
		fileStream5 << "****************************************************" << std::endl;
		fileStream5 << "          module_TTCN_Templates                     " << std::endl;
		fileStream5 << "****************************************************" << std::endl;
		fileStream5 << module_TTCN_Templates.str() << std::endl << std::endl;
		fileStream5 << "****************************************************" << std::endl;
		fileStream5 << "          module_TTCN_TestsAndControl               " << std::endl;
		fileStream5 << "****************************************************" << std::endl;
		fileStream5 << module_TTCN_TestsAndControl.str() << std::endl << std::endl;
		fileStream5 << "****************************************************" << std::endl;
		fileStream5 << "          module_TTCN_ControlPart                   " << std::endl;
		fileStream5 << "****************************************************" << std::endl;
		fileStream5 << module_TTCN_ControlPart.str() << std::endl << std::endl;
		fileStream5.close();
	}

	mTraceGenerator.beginStream();
	while( mTraceGenerator.hasStream() )
	{
		OutStream & os = mTraceGenerator.currentStream();

AVM_IF_DEBUG_FLAG( PROCESSOR )
	aTraceManager.toStream( os );
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )

		os << "****************************************************" << std::endl;
		os << "          module_TTCN_Declarations                  " << std::endl;
		os << "****************************************************" << std::endl;
		os << module_TTCN_Declarations.str() << std::endl << std::endl;
		os << "****************************************************" << std::endl;
		os << "          module_TTCN_Templates                     " << std::endl;
		os << "****************************************************" << std::endl;
		os << module_TTCN_Templates.str() << std::endl << std::endl;
		os << "****************************************************" << std::endl;
		os << "          module_TTCN_TestsAndControl               " << std::endl;
		os << "****************************************************" << std::endl;
		os << module_TTCN_TestsAndControl.str() << std::endl << std::endl;
		os << "****************************************************" << std::endl;
		os << "          module_TTCN_ControlPart                   " << std::endl;
		os << "****************************************************" << std::endl;
		os << module_TTCN_ControlPart.str() << std::endl << std::endl;
	}

	mTraceGenerator.closeStream();
}

void TTCNTraceFormatter::format_impl(TraceManager & aTraceManager)
{
	// Nom du system
	systemName = mTraceGenerator.
			getConfiguration().getExecutableSystem().getNameID();

	// module TTCN_Declarations
	//
	formatHeader_TTCN_Declarations(module_TTCN_Declarations);

	TraceManager::const_iterator it = aTraceManager.begin();
	TraceManager::const_iterator endIt = aTraceManager.end();
	for( ; it != endIt ; ++it )
	{
		aTraceElement = (*it);

		format_TTCN_Declarations(aTraceElement);
	}

	format_TTCN_DeclarationsChannels();


	formatEnd_TTCN_Declarations(module_TTCN_Declarations);

	// module TTCN_Templates
	// module TTCN_TestsAndControl
	// module TTCN_ControlPart
	//
	formatHeader_TTCN_Templates(module_TTCN_Templates);
	formatHeader_TTCN_TestsAndControl(module_TTCN_TestsAndControl);
	formatHeader_TTCN_ControlPart(module_TTCN_ControlPart);

	traceNumber = 1;
	linkNumber = 0;
	it = aTraceManager.begin();
	endIt = aTraceManager.end();
	for( ; it != endIt ; ++it )
	{
		formatHeader_TTCN_TestsAndControl_testcase(module_TTCN_TestsAndControl);

		aTraceElement = (*it);

		format_TTCN_Templates(aTraceElement);

		formatEnd_TTCN_TestsAndControl_testcase(module_TTCN_TestsAndControl);

		format_TTCN_ControlPart_execute(module_TTCN_ControlPart);

		traceNumber ++;
		linkNumber = 0;
	}

	formatEnd_TTCN_Templates(module_TTCN_Templates);
	formatEnd_TTCN_TestsAndControl(module_TTCN_TestsAndControl);
	formatEnd_TTCN_ControlPart(module_TTCN_ControlPart);
}

void TTCNTraceFormatter::formatHeader_TTCN_Declarations(std::ostream & os)
{
	os << "module TTCN_Declarations {" << std::endl;
}

void TTCNTraceFormatter::formatEnd_TTCN_Declarations(std::ostream & os)
{
	if( not newTypesDeclaration.str().empty() )
	{
		os << "\t// New types declarations" << std::endl;
		os << newTypesDeclaration.str();
	}

	os << "\t// Records declaration" << std::endl;
	os << recordsDeclaration.str();

	/*!! TODO code à supprimer après validation nouveau code pour les channels
	os << "\t// Ports declaration" << std::endl;
	os << "\ttype port port_cEnv message {" << std::endl;
	os << portsDeclaration.str();
	os << "\t}" << std::endl << std::endl;
	*/
	os << "\t// Channels & ports declaration" << std::endl;
	os << channelsDefinition.str();

	os << "\t// TSI and MTC component declaration" << std::endl;
	os << "\ttype component runsOn_" << systemName << " {" << std::endl;

	/*!! TODO code à supprimer après validation nouveau code pour les channels
	os << "\t\tport port_cEnv cEnv;" << std::endl;
	*/
	os << channelsDeclaration.str();

	os << "\t}" << std::endl;
	os << "\ttype component " << systemName << " {" << std::endl;

	/*!! TODO code à supprimer après validation nouveau code pour les channels
	os << "\t\tport port_cEnv cEnv;" << std::endl;
	*/
	os << channelsDeclaration.str();

	os << "\t}" << std::endl;

	// fin du module TTCN_Declarations
	os << "}" << std::endl;
}

void TTCNTraceFormatter::format_TTCN_Declarations(TraceSequence * aTraceElt)
{
	BFList::const_iterator it = aTraceElt->points.begin();
	BFList::const_iterator endIt = aTraceElt->points.end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).is< TracePoint >() )
		{
			if( (*it).to_ptr< TracePoint >()->isVirtual() )
			{
				//!! NOTHING
			}
			else
			{
				format_TTCN_Declarations((*it).to_ptr< TracePoint >());
			}
		}

		else if( (*it).is< TraceSequence >() )
		{
			format_TTCN_Declarations((*it).to_ptr< TraceSequence >());
		}
	}
}

void TTCNTraceFormatter::format_TTCN_Declarations(TracePoint * aTracePoint)
{
	std::string paramName;
	std::string paramType;

// !!! Modif AFA - 23/05/2016 !!!
//	if( not listOfTreatedSignal.contains( aTracePoint->object ) )
//	{
	if( not listOfTreatedSignalName.contains(
			aTracePoint->object->getNameID() ) )
	{

//		listOfTreatedSignal.append( aTracePoint->object );
		listOfTreatedSignalName.append( aTracePoint->object->getNameID() );

		if( aTracePoint->object->is< InstanceOfPort >() )
		{
			InstanceOfPort * aSignal =
					aTracePoint->object->to< InstanceOfPort >();

			// Records declaration
			//
			ArrayOfBF::const_iterator it = aSignal->getParameters().begin();
			ArrayOfBF::const_iterator endIt = aSignal->getParameters().end();
			if( isSDLFlag )
			{
				// ATTENTION : dans ce cas on ne  prend pas en compte le dernier paramètre
				// qui correspond au PID de l'émetteur
				//
				endIt = endIt - 1;
			}

			if( aSignal->hasParameter() && it != endIt )
			{
				// signal avec au moins un paramètre à afficher
				//
				recordsDeclaration << "\ttype record "
						<< aTracePoint->object->getNameID() << " {";

				std::string::size_type posOfDiese;

				bool firstParameter = true;
				for( ; it != endIt ; ++it )
				{
					recordsDeclaration << ( firstParameter ? "" : ",")
							<< std::endl;

					firstParameter = false;

					// paramètre anonyme
					if( (*it).is< BaseTypeSpecifier >() )
					{
						format_TTCN_Declarations(aTracePoint,
								(*it).to_ptr< BaseTypeSpecifier >(), "unamed");

						recordsDeclaration << "\t\t";
						// le type
						if( (*it).to_ptr< BaseTypeSpecifier >()->isTypedReal() )
						{
							recordsDeclaration << "float";
						}
						else
						{
							recordsDeclaration
								<< (*it).to_ptr< BaseTypeSpecifier >()->strT();
						}
						// le nom
						recordsDeclaration << " " << "unamed";
					}
					// paramètre nommé
					else if( (*it).is< InstanceOfData >() )
					{
						InstanceOfData * aParam = (*it).to_ptr< InstanceOfData >();

						format_TTCN_Declarations(aTracePoint,
								aParam->getTypeSpecifier(),
								aParam->getTypeSpecifier()->strT());

						recordsDeclaration << "\t\t";
						// le type
						if( aParam->getTypeSpecifier()->isTypedString() )
						{
							paramType = "charstring";
						}
						else if( aParam->getTypeSpecifier()->isTypedCharacter() )
						{
							paramType = "charstring";
						}
						else if( aParam->getTypeSpecifier()->isTypedReal())
						{
							paramType = "float";
						}
						else
						{
							paramType = aParam->getTypeSpecifier()->strT();
						}

						recordsDeclaration <<
								( aParam->getTypeSpecifier()->
										hasTypePrimitive() ? "" : "TTCN_" )
								<< paramType;
						// le nom
						posOfDiese = aParam->getNameID().find_first_of('#');
						if( (aParam->getNameID()[0] == '$')
							|| (aParam->getNameID()[0] == '#') )
						{
							paramName = aParam->getNameID().substr(1);
							recordsDeclaration << " " << "param" << paramName;
						}
						else
						{
							recordsDeclaration << " " << aParam->getNameID();
						}
					}
					// #bind expression parameter
					else
					{
					}
				}
				recordsDeclaration << std::endl;
				recordsDeclaration << "\t}" << std::endl << std::endl;
			}
			else
			{
				// signal sans paramètre à afficher
				//
				recordsDeclaration << "\ttype enumerated "
						<< aTracePoint->object->getNameID()
						<< " { e_" << aTracePoint->object->getNameID() << " }"
						<< std::endl << std::endl;
			}


/*
			// Ports declaration
			//
			switch( aTracePoint->op )
			{
				case AVM_OPCODE_INPUT_ENV:
				{
					inoutSignalName = "out " + aTracePoint->object->getNameID();
					break;
				}

				case AVM_OPCODE_OUTPUT_ENV:
				{
					inoutSignalName = "in " + aTracePoint->object->getNameID();
					break;
				}

				default:
				{
					// Messsage erreur ???
					break;
				}
			}
*/

		}
	}


	if( aTracePoint->object->is< InstanceOfPort >() )
	{
		InstanceOfPort * aSignal = aTracePoint->object->to< InstanceOfPort >();
		// Liste des channels associés aux signaux
		if( aSignal->hasRoutingChannel() )
		{
			std::string channelName = aSignal->getRoutingChannel()->getNameID();
			if( not ListOfChannelName.contains( channelName ) )
			{
				ListOfChannelName.append( channelName );
			}
		}
		else
		{
//!![TRACE ] to delete
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_COUT << "Messsage erreur ??? : Signal non connecté : "
//			<< str_header( aSignal ) << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		}
	}
}

void TTCNTraceFormatter::format_TTCN_Declarations(TracePoint * aTracePoint,
		BaseTypeSpecifier * aTS, std::string typeName)
{
	if( listOfTreatedType.contains( aTS ) )
	{
		return;
	}

	listOfTreatedType.append( aTS );

	if( aTS->hasTypeContainer() )
	{
		ContainerTypeSpecifier * containerT = aTS->as< ContainerTypeSpecifier >();
		avm_size_t sizeT = containerT->size();

		switch( containerT->getTypeSpecifierKind() )
		{
			case TYPE_VECTOR_SPECIFIER:
			case TYPE_REVERSE_VECTOR_SPECIFIER:
			case TYPE_LIST_SPECIFIER:
			case TYPE_SET_SPECIFIER:
			case TYPE_MULTISET_SPECIFIER:
			case TYPE_FIFO_SPECIFIER:
			case TYPE_LIFO_SPECIFIER:
			case TYPE_MULTI_FIFO_SPECIFIER:
			case TYPE_MULTI_LIFO_SPECIFIER:
			default:
			{
				format_TTCN_Declarations(aTracePoint,
						containerT->getContentsTypeSpecifier(), typeName);

				newTypesDeclaration << "\ttype "
					<< ( containerT->getContentsTypeSpecifier().
							hasTypePrimitive() ? "" : "TTCN_" )
					<< containerT->getContentsTypeSpecifier().strT() << " "
					<< "TTCN_" << typeName << "[" << sizeT << "];"
					<< std::endl << std::endl;

				break;
			}
		}
	}

	else if( aTS->isTypedClass() )
	{
		ClassTypeSpecifier * classType = aTS->as< ClassTypeSpecifier >();
		avm_size_t sizeT = classType->size();

		Symbol aField;

		for( avm_size_t idx = 0 ; idx < sizeT ; ++idx )
		{
			aField = classType->getSymbolData(idx);

			format_TTCN_Declarations(aTracePoint, aField.getTypeSpecifier(),
					aField.getTypeSpecifier()->strT());
//					aField.getTypeSpecifier()->getNameID());
		}

		// Type Structure/Record declaration
		newTypesDeclaration << "\ttype record " << "TTCN_" << typeName << " {"
				<< std::endl;
		for( avm_size_t idx = 0 ; idx < sizeT ; ++idx )
		{
			aField = classType->getSymbolData(idx);

			newTypesDeclaration << "\t\t"
				<< ( aField.getTypeSpecifier()->hasTypePrimitive() ? "" : "TTCN_" )
				<< ( aField.getTypeSpecifier()->isTypedReal() ?
						"float" : aField.getTypeSpecifier()->strT() )
				<< " " << aField.getNameID() << ((idx < (sizeT - 1)) ? "," : "")
				<< std::endl;
		}
		newTypesDeclaration << "\t}" << std::endl << std::endl;
	}

	else if( aTS->isTypedEnum() )
	{
		EnumTypeSpecifier * enumType = aTS->as< EnumTypeSpecifier >();

		// Type enum declaration
		newTypesDeclaration << "\ttype enumerated " << "TTCN_" << typeName
				<< " {" << std::endl;
		newTypesDeclaration << "\t\t";

		avm_size_t sizeT = enumType->getSymbolData().size();
		for( avm_size_t idx = 0 ; idx < sizeT ; ++idx )
		{
			newTypesDeclaration << enumType->getSymbolData(idx).getNameID()
					<< ((idx < (sizeT - 1)) ? ", " : "\n");
		}
		newTypesDeclaration << "\t}" << std::endl << std::endl;
	}

	else if( aTS->isTypedInterval() )
	{
		IntervalTypeSpecifier * intervalTS = aTS->as< IntervalTypeSpecifier >();

		newTypesDeclaration << "\ttype "
			<< ( intervalTS->getSupportTypeSpecifier().
					hasTypePrimitive() ? "" : "TTCN_" )
			<< ( intervalTS->getSupportTypeSpecifier().isTypedReal() ?
					"float" : intervalTS->getSupportTypeSpecifier().strT() )
			<< " TTCN_" << typeName
			<< " ("   << intervalTS->getInfimum().str()
			<< " .. " << intervalTS->getSupremum().str()
			<< ");"    << std::endl << std::endl;
	}

	else if( aTS->isTypedString() )
	{
		if( aTS->size() < AVM_NUMERIC_MAX_SIZE_T )
		{
			newTypesDeclaration << "\ttype charstring TTCN_" << typeName
					<< " length( " << aTS->getMinimumSize()
					<< " .. " << aTS->getMaximumSize() << " );"
					<< std::endl << std::endl;
		}
	}

	else if( aTS->isTypedAlias() )
	{
		if( aTS->hasConstraint() )
		{
//			format_TTCN_Declarations(aTracePoint,
//				aTS->as< TypeAliasSpecifier >()->targetTypeSpecifier(), typeName);

			BaseTypeSpecifier * targetTS =
					aTS->as< TypeAliasSpecifier >()->targetTypeSpecifier();

			newTypesDeclaration << "\ttype "
//				<< ( aTS->hasTypedPrimitive() ? "" : "TTCN_")
				<< targetTS->strT() << " " << "TTCN_" << typeName << "{ "
				<< aTS->getConstraint().as_ptr< AvmProgram >()->getCode().str()
				<< " };" << std::endl << std::endl;
		}
		else
		{
			format_TTCN_Declarations(aTracePoint,
				aTS->as< TypeAliasSpecifier >()->targetTypeSpecifier(), typeName);
		}
	}

	else if( aTS->weaklyTypedInteger() && (aTS->getBitSize() > 0) )
	{
		newTypesDeclaration << "\ttype integer" // << aTS->getNameID()
			<< " TTCN_" << typeName
			<< " ("   << aTS->minIntegerValue()
			<< " .. " << aTS->maxIntegerValue()
			<< ");"    << std::endl << std::endl;
	}
	else if( /*aTS->isTypedSimple() &&*/ aTS->hasConstraint() )
	{
		//!! TODO
		newTypesDeclaration << "\ttype "
			<< /*( aTS->hasTypedPrimitive() ? "" : "TTCN_") <<*/ typeName << " "
			<< "TTCN_" << aTS->strT() << "{ "
			<< aTS->getConstraint().as_ptr< AvmProgram >()->getCode().str()
			<< " };" << std::endl << std::endl;
	}
}


void TTCNTraceFormatter::format_TTCN_DeclarationsChannels()
{
	const ExecutableSystem & anExecutableSystem =
			mTraceGenerator.getConfiguration().getExecutableSystem();

	TableOfSymbol::const_iterator itChannel;
	TableOfSymbol::const_iterator endChannel;

	TableOfSymbol::const_iterator itPort;
	TableOfSymbol::const_iterator endPort;

	TableOfExecutableForm::const_raw_iterator itExec =
			anExecutableSystem.getExecutables().begin();
	TableOfExecutableForm::const_raw_iterator endExec =
			anExecutableSystem.getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		itChannel = (itExec)->getChannel().begin();
		endChannel = (itExec)->getChannel().end();
		for( ; itChannel != endChannel ; ++itChannel )
		{
			channelsDefinition << "\ttype port port_"
					<< (*itChannel).getNameID() << " message {" << std::endl;

			channelsDeclaration << "\t\tport port_" << (*itChannel).getNameID()
					<< " " << (*itChannel).getNameID() << ";" << std::endl;

			itPort = (*itChannel).channel().getContents().begin();
			endPort = (*itChannel).channel().getContents().end();
			for( ; itPort != endPort ; ++itPort )
			{
// !!! Modif AFA - 23/05/2016 !!!
//				if( listOfTreatedSignal.contains( (*itPort).rawPort() ) )
				if( listOfTreatedSignalName.contains(
						(*itPort).rawPort()->getNameID() ) )

				{
					channelsDefinition << "\t\t"
						<< ( (*itPort).port().getModifier().isDirectionInput()
								? "out " : "in " )
						<< (*itPort).getNameID() << ";" << std::endl;
				}
			}
			channelsDefinition << "\t}" << std::endl;
		}
	}
}


void TTCNTraceFormatter::formatHeader_TTCN_Templates(std::ostream & os)
{
	os << "module TTCN_Templates {" << std::endl;
	os << "\timport from TTCN_Declarations all;" << std::endl << std::endl;
}

void TTCNTraceFormatter::formatEnd_TTCN_Templates(std::ostream & os)
{
	os << templateList.str();
	os << "}" << std::endl;
}

void TTCNTraceFormatter::formatHeader_TTCN_TestsAndControl(std::ostream & os)
{
	int unsigned i;

	os << "module TTCN_TestsAndControl {" << std::endl << std::endl;
	os << "\timport from TTCN_Declarations all;" << std::endl;
	os << "\timport from TTCN_Templates all;" << std::endl << std::endl;

	os << "\taltstep RTDS_fail() runs on " << systemName << " {" << std::endl;
	for(i = 0 ; i < ListOfChannelName.size() ; i++)
	{
		os << "\t\t[]" << ListOfChannelName.get(i)
				<< ".receive { setverdict(fail); };" << std::endl;
	}
	os << "\t}" << std::endl << std::endl;
}

void TTCNTraceFormatter::formatEnd_TTCN_TestsAndControl(std::ostream & os)
{
	os << "}" << std::endl;
}

void TTCNTraceFormatter::formatHeader_TTCN_TestsAndControl_testcase(std::ostream & os)
{
	int unsigned i;

	os << "\ttestcase TC_trace" << traceNumber << "() "
		<< "runs on runsOn_" << systemName
		<< " system " << systemName << " {" << std::endl
		<< "\t\tactivate(RTDS_fail());" << std::endl;
	for(i = 0 ; i < ListOfChannelName.size() ; i++)
	{
		os << "\t\tmap(self:" << ListOfChannelName.get(i)
				<< ",system:" << ListOfChannelName.get(i) << ");" << std::endl;
	}
	ossTestcaseList.str("");
}

void TTCNTraceFormatter::formatEnd_TTCN_TestsAndControl_testcase(std::ostream & os)
{
	os << ossTestcaseList.str();
	os << "\t\tsetverdict(pass)" << std::endl;
	os << "\t}" << std::endl << std::endl;
}

void TTCNTraceFormatter::formatHeader_TTCN_ControlPart(std::ostream & os)
{
	os << "module TTCN_ControlPart {" << std::endl << std::endl;
	os << "\timport from TTCN_TestsAndControl all;" << std::endl << std::endl;

	os << "\tcontrol {" << std::endl;
}

void TTCNTraceFormatter::formatEnd_TTCN_ControlPart(std::ostream & os)
{
	os << "\t}" << std::endl;
	os << "}" << std::endl;
}

void TTCNTraceFormatter::format_TTCN_ControlPart_execute(std::ostream & os)
{
	os << "\t\texecute(TC_trace" << traceNumber << "());" << std::endl;
}

void TTCNTraceFormatter::format_TTCN_Templates(TraceSequence * aTraceElt)
{
	BFList::const_iterator it = aTraceElt->points.begin();
	BFList::const_iterator endIt = aTraceElt->points.end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).is< TracePoint >() )
		{
			if( (*it).to_ptr< TracePoint >()->isVirtual() )
			{
				//!! NOTHING
			}
			else
			{
				format_TTCN_Templates((*it).to_ptr< TracePoint >());
			}
		}

		else if( (*it).is< TraceSequence >() )
		{
			format_TTCN_Templates((*it).to_ptr< TraceSequence >());
		}
	}
}

void TTCNTraceFormatter::format_TTCN_Templates(TracePoint * aTracePoint)
{
	std::string template_TAB = "\t\t";
	std::string template_incrTab = "\t";

	if( aTracePoint->object->is< InstanceOfPort >() &&
		( ( aTracePoint->op	== AVM_OPCODE_INPUT_ENV ) ||
		  ( aTracePoint->op	== AVM_OPCODE_OUTPUT_ENV ) ) )
	{
		InstanceOfPort * aSignal = aTracePoint->object->to< InstanceOfPort >();

		std::ostringstream templateName;
		templateName << aSignal->getNameID()
				<< "_trace" << traceNumber
				<< "_LINK_" << linkNumber;

		ArrayOfBF::const_iterator it = aSignal->getParameters().begin();
		ArrayOfBF::const_iterator endIt = aSignal->getParameters().end();
		if( isSDLFlag )
		{
			// ATTENTION : dans ce cas on ne  prend pas en compte le dernier paramètre
			// qui correspond au PID de l'émetteur
			//
			endIt = endIt - 1;
		}

		if( aSignal->hasParameter() && it != endIt )
		{
			// signal avec au moins un paramètre à afficher
			//
			templateList << "\ttemplate " << aSignal->getNameID() << " ";
			templateList << templateName.str() << " := {" << std::endl;

			avm_size_t sizeT = aSignal->getParameters().size() - 1;

			for( avm_size_t offset = 0 ; it != endIt ; ++it , ++offset )
			{
				// paramètre anonyme
				if( (*it).is< BaseTypeSpecifier >() )
				{
					// le nom
					templateList << "\t\t" << "unamed";
					// la valeur
					templateList << " := " << aTracePoint->val(offset).str();
				}
				// paramètre nommé
				else if( (*it).is< InstanceOfData >() )
				{
					InstanceOfData * aParam = (*it).to_ptr< InstanceOfData >();

					format_TTCN_Templates(aTracePoint->val(offset),
							aParam->getTypeSpecifier(), aParam->getNameID(),
							offset, template_TAB, template_incrTab);
				}
				// #bind expression parameter
				else
				{
					// Cf Arnault si cas erreur ???
				}

				templateList << ((offset+1 >= sizeT) ? "" : ",") << std::endl;
			}
			templateList << "\t}" << std::endl << std::endl;
		}
		else
		{
			// signal sans paramètre à afficher
			//
			templateList << "\ttemplate " << aSignal->getNameID()
					<< " " << templateName.str() << " := ?;"
					<< std::endl << std::endl;
		}

		if( aTracePoint->op	== AVM_OPCODE_INPUT_ENV )
		{
			if( aSignal->hasRoutingChannel() )
			{
				ossTestcaseList << "\t\t"
						<< aSignal->getRoutingChannel()->getNameID()
						<< ".send(" << templateName.str() << ")" << std::endl;
			}
			else
			{
				ossTestcaseList << "\t\tcEnv.send("
						<< templateName.str() << ")" << std::endl;
			}
		}
		else
		{
			if( aSignal->hasRoutingChannel() )
			{
				ossTestcaseList << "\t\t"
						<< aSignal->getRoutingChannel()->getNameID()
						<< ".receive(" << templateName.str() << ")"
						<< std::endl;
			}
			else
			{
				ossTestcaseList << "\t\tcEnv.receive("
						<< templateName.str() << ")" << std::endl;
			}
		}

		linkNumber ++;
	}
}

void TTCNTraceFormatter::format_TTCN_Templates(
		const BF & value, BaseTypeSpecifier * aTS,
		std::string aParamName, avm_size_t anOffset,
		const std::string & TAB, const std::string & CHAR)
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

	if( aTS->hasTypeContainer() )
	{
		ContainerTypeSpecifier * containerT = aTS->as< ContainerTypeSpecifier >();
//		avm_size_t sizeT = containerT->size();

		switch( containerT->getTypeSpecifierKind() )
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
//				if( not aTS->isTypedSimple() )
//				{
//					format_TTCN_Templates(aTracePoint,
//							containerT->getTypeSpecifier(), aParamName);
//				}
				break;
			}
		}
	}

	else if( aTS->isTypedClass() )
	{
		ClassTypeSpecifier * classType = aTS->as< ClassTypeSpecifier >();
		avm_size_t sizeT = classType->size();

		Symbol aField;

		templateList << "{" << std::endl;

		for( avm_size_t idx = 0 ; idx < sizeT ; ++idx )
		{
			aField = classType->getSymbolData(idx);

			format_TTCN_Templates(
					value.to_ptr< ArrayBF >()->at( idx ),
					aField.getTypeSpecifier(), aField.getNameID(),
					idx, TAB + CHAR, CHAR);

			templateList << ((idx+1 >= sizeT) ? "" : ",") << std::endl;
		}

		templateList << TAB << "}" << std::endl;
	}

	else if( aTS->isTypedEnum() )
	{
		EnumTypeSpecifier * enumT = aTS->as< EnumTypeSpecifier >();

		// Affichage de la valeur numérique
		if( value.invalid() )
		{
			templateList << "NULL";
		}
		else if( value.is< ArrayBF >() )
		{
			templateList << "ARRAY<?>";
		}
		else if( value.is< InstanceOfData >() )
		{
			InstanceOfData * aSymbol = value.to_ptr< InstanceOfData >();

			if( not enumT->hasSymbolData(aSymbol) )
			{
				AVM_OS_ERROR_ALERT << "TTCNTraceFormatter::format_TTCN_Templates"
						<< " :> Unexpected symbol\n<< " << str_header( aSymbol )
						<< " >>\nfor the enum type << "
						<< enumT->getFullyQualifiedNameID() << " >> !!!"
						<< SEND_ALERT;
			}

			templateList << aSymbol->getNameID();
		}
		else
		{
			const Symbol & aSymbol = enumT->getSymbolDataByValue(value);
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
						<< enumT->getFullyQualifiedNameID()
						<< " >> for the parameter << param"
						<< aParamName << " >> !!!"
						<< SEND_ALERT;

				templateList << enumT->getNameID()
						<< "[ " << value.str() << " ]";
			}
		}
	}

	else if( value.is< Character >() )
	{
		// On remplace 'x' par "x"
		templateList << value.to_ptr< Character >()->strChar('"');
	}
	else //if( aTS->isTypedSimple() )
	{
		// Affichage de la valeur numérique
		if( value.invalid() )
		{
			templateList << "NULL";
		}
		else if( value.is< ArrayBF >() )
		{
			templateList << value.to_ptr< ArrayBF >()->at( anOffset ).str();
		}
		else
		{
			templateList << value.str();
		}
	}
}


} /* namespace sep */

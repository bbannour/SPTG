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

#include "TTCNBaseTraceFormatter.h"

#include "TraceManager.h"

#include <collection/BFContainer.h>

#include  <famcore/trace/AvmTraceGenerator.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionInformation.h>

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
const std::string & TTCNBaseTraceFormatter::DATA_TYPE_NAME_FORMAT
//		%1% --> <data type name id>
//		%2% --> <container/lifeline/component name id>
//		%3% --> <system name id>
		= "TTCN_%1%";


const std::string & TTCNBaseTraceFormatter::PORT_TYPE_NAME_FORMAT
//		%1% --> <port name id>
//		%2% --> <container/lifeline/component name id>
//		%3% --> <system name id>
		= "port_%1%_t";

const std::string & TTCNBaseTraceFormatter::PORT_INSTANCE_NAME_FORMAT
//		%1% --> <port name id>
//		%2% --> <container/lifeline/component name id>
//		%3% --> <system name id>
		= "port_%1%_instance";


const std::string & TTCNBaseTraceFormatter::MESSAGE_TYPE_NAME_FORMAT
//		%1% --> <port name id>
//		%2% --> <container/lifeline/component name id>
//		%3% --> <system name id>
		= "msg_%1%_t";


const std::string & TTCNBaseTraceFormatter::TEMPLATE_VALUE_NAME_FORMAT
//		%1% --> <port name id>
//		%2% --> <container/lifeline/component name id>
//		%3% --> <system name id>
//		%4% --> <trace sequence id number>
//		%5% --> <trace point id number>
		= "msg_%1%_trace%4%_tpid%5%";


const std::string & TTCNBaseTraceFormatter::TEMPLATE_FUNCTION_NAME_FORMAT
//		%1% --> <port name id>
//		%2% --> <container/lifeline/component name id>
//		%3% --> <system name id>
		= "msg_%1%_funct";

const std::string & TTCNBaseTraceFormatter::TEMPLATE_PARAMETRIZED_NAME_FORMAT
//		%1% --> <port name id>
//		%2% --> <container/lifeline/component name id>
//		%3% --> <system name id>
		= "msg_%1%_templ";


const std::string & TTCNBaseTraceFormatter::TESTCASE_NAME_FORMAT
//		%1% --> <system name id>
//		%2% --> <trace sequence id number>
		= "TC_trace_%2%";


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool TTCNBaseTraceFormatter::configureImpl(const WObject * wfParameterObject)
{
	const WObject * theFORMAT = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("format", "FORMAT") );

	std::size_t error = 0;

	if( theFORMAT != WObject::_NULL_ )
	{
		error += configureFormatter(theFORMAT, mDataTypeNameFormat,
				CONS_WID3("data", "type" , "name"), true ) ? 0 : 1;
		
		error += configureFormatter(theFORMAT, mPortTypeNameFormat,
				CONS_WID3("port", "type" , "name"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mPortInstanceNameFormat,
				CONS_WID3("port", "instance" , "name"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mMessageTypeNameFormat,
				CONS_WID3("message", "type" , "name"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mTemplateValueNameFormat,
				CONS_WID3("template", "value" , "name"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mTemplateFunctionNameFormat,
				CONS_WID3("template", "function" , "name"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mTemplateParametrizedNameFormat,
				CONS_WID3("template", "parametrized" , "name"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mTestcaseNameFormat,
				CONS_WID2("testcase", "name"), true ) ? 0 : 1;

	}

	return( error == 0 );
}

bool TTCNBaseTraceFormatter::configureFormatter(const WObject * FORMAT,
		std::string & formatPattern, const std::string & id, bool isRegex)
{
	formatPattern =  isRegex
			? Query::getRegexWPropertyString(FORMAT, id, formatPattern)
			: Query::getWPropertyString(FORMAT, id, formatPattern);

	StringTools::replaceAllEscapeSequences(formatPattern);

	try
	{
		boost::format formatter(formatPattern);
	}
	catch(const boost::io::bad_format_string & bfs)
	{
		Query::reportErrorAttribute(FORMAT, id, bfs.what());

		return( false );
	}

	return( true );
}


/**
 * FORMAT API
 */
void TTCNBaseTraceFormatter::formatTraceSequence(const TraceSequence & aTraceSequence)
{
	setofExecutionContext4CoverageInfo.clear();
	mCoverageInfoTraceabilitySequence.clear();

	for( const auto & itPoint : aTraceSequence.points )
	{
		if( itPoint.is< TracePoint >() )
		{
			mCurrentTracePoint = itPoint.to_ptr< TracePoint >();

			if( itPoint.to< TracePoint >().isVirtual() )
			{
				//!! NOTHING
			}
			else
			{
				formatTracePoint( itPoint.to< TracePoint >() );
			}
		}
		else if( itPoint.is< TraceSequence >() )
		{
			formatTraceSequence( itPoint.to< TraceSequence >() );
		}
	}
}

void TTCNBaseTraceFormatter::formatTracePoint(const TracePoint & aTracePoint)
{
	collectTraceCoverageInfo( aTracePoint );

	formatTracePointImpl( aTracePoint );
}


void TTCNBaseTraceFormatter::collectTraceCoverageInfo(
		const TracePoint & aTracePoint)
{
	if( aTracePoint.EC.getFlags().hasCoverageElementTrace()
		&& aTracePoint.EC.hasInfo()
		&& setofExecutionContext4CoverageInfo.insert( &aTracePoint.EC ).second )
	{
		mCoverageInfoTraceabilitySequence.append( aTracePoint.EC.getInfos() );
	}
}


void TTCNBaseTraceFormatter::formatTestcaseCoverageInfo(OutStream & out)
{
	if( mCoverageInfoTraceabilitySequence.nonempty() )
	{

		out << TAB << "/* Coverage elements" << std::endl;

		for( const auto & info : mCoverageInfoTraceabilitySequence )
		{
			out << TAB << " * "
				<< info.to< GenericInfoData >().strData()
				<< std::endl;
		}

		out << TAB << " */" << std::endl;
	}
}


/**
 * COMMON UTILS
 */
std::string TTCNBaseTraceFormatter::ttcnTypename(const BaseTypeSpecifier & aTS)
{
	if( aTS.isTypedString() )
	{
		return( "charstring" );
	}
	else if( aTS.isTypedCharacter() )
	{
		return( "charstring" );
	}
	else if( aTS.isTypedReal() || aTS.isTypedRational() )
	{
		return( "float" );
	}
	else if( aTS.hasTypePrimitive() )
	{
		return( aTS.strT() );
	}
	else
	{
		std::map< std::string , std::string >::iterator itFind =
				mapofTreatedTypeName.find( aTS.strT() );

		if( itFind != mapofTreatedTypeName.end() )
		{
			return( (*itFind).second );
		}
		else
		{
			return( mapofTreatedTypeName[aTS.strT()] = dataTypeName(aTS) );
		}
	}
}


//	%1% --> <data type name id>
//	%2% --> <container/lifeline/component name id>
//	%3% --> <system name id>
OutStream & TTCNBaseTraceFormatter::dataTypeName(
		OutStream & out, const std::string & aTypename) const
{
	boost::format formatter( mDataTypeNameFormat );
	formatter.exceptions( boost::io::no_error_bits );

	return out << formatter
			% aTypename
			% mSystemNameID
			% mSystemNameID;
}

OutStream & TTCNBaseTraceFormatter::dataTypeName(
		OutStream & out, const BaseTypeSpecifier & aTS) const
{
	boost::format formatter( mDataTypeNameFormat );
	formatter.exceptions( boost::io::no_error_bits );

	return out << formatter
			% aTS.strT()
			% mSystemNameID
			% mSystemNameID;
}


//	%1% --> <port name id>
//	%2% --> <container/lifeline/component name id>
//	%3% --> <system name id>
OutStream & TTCNBaseTraceFormatter::portTypeName(
		OutStream & out, const InstanceOfPort & aPort) const
{
	boost::format formatter( mPortTypeNameFormat );
	formatter.exceptions( boost::io::no_error_bits );

	return out << formatter
			% aPort.getNameID()
			% mCurrentTracePoint->RID.getLifeline(aPort).getNameID()
			% mSystemNameID;
}

//	%1% --> <port name id>
//	%2% --> <container/lifeline/component name id>
//	%3% --> <system name id>
OutStream & TTCNBaseTraceFormatter::portInstanceName(
		OutStream & out, const InstanceOfPort & aPort) const
{
	boost::format formatter( mPortInstanceNameFormat );
	formatter.exceptions( boost::io::no_error_bits );

	return out << formatter
			% aPort.getNameID()
			% mCurrentTracePoint->RID.getLifeline(aPort).getNameID()
			% mSystemNameID;
}

//	%1% --> <port name id>
//	%2% --> <container/lifeline/component name id>
//	%3% --> <system name id>
OutStream & TTCNBaseTraceFormatter::messageTypeName(
		OutStream & out, const InstanceOfPort & aPort) const
{
	boost::format formatter( mMessageTypeNameFormat );
	formatter.exceptions( boost::io::no_error_bits );

	return out << formatter
			% aPort.getNameID()
			% mCurrentTracePoint->RID.getLifeline(aPort).getNameID()
			% mSystemNameID;
}


//	%1% --> <port name id>
//	%2% --> <container/lifeline/component name id>
//	%3% --> <system name id>
//	%4% --> <trace sequence id number>
//	%5% --> <trace point id number>
inline OutStream & TTCNBaseTraceFormatter::formatTemplateValueName(
		OutStream & out, const TracePoint & aTracePoint) const
{
	boost::format formatter( mTemplateFunctionNameFormat );
	formatter.exceptions( boost::io::no_error_bits );

	return out << formatter
			% aTracePoint.object->getNameID()
			% aTracePoint.RID.getLifeline().getNameID()
			% mSystemNameID
			% mCurrentTraceSequence->tid
			% aTracePoint.tpid;
}


//	%1% --> <port name id>
//	%2% --> <container/lifeline/component name id>
//	%3% --> <system name id>
inline OutStream & TTCNBaseTraceFormatter::formatTemplateFunctionName(
		OutStream & out, const TracePoint & aTracePoint) const
{
	boost::format formatter( mTemplateFunctionNameFormat );
	formatter.exceptions( boost::io::no_error_bits );

	return out << formatter
			% aTracePoint.object->getNameID()
			% aTracePoint.RID.getLifeline().getNameID()
			% mSystemNameID;
}

//	%1% --> <port name id>
//	%2% --> <container/lifeline/component name id>
//	%3% --> <system name id>
inline OutStream & TTCNBaseTraceFormatter::formatTemplateParametrizedName(
		OutStream & out, const TracePoint & aTracePoint) const
{
	boost::format formatter( mTemplateParametrizedNameFormat );
	formatter.exceptions( boost::io::no_error_bits );

	return out << formatter
			% aTracePoint.object->getNameID()
			% aTracePoint.RID.getLifeline().getNameID()
			% mSystemNameID;
}


//	%1% --> <system name id>
//	%2% --> <trace sequence id number>
OutStream & TTCNBaseTraceFormatter::formatTestcaseName(
		OutStream & out, const TraceSequence & aTraceSequence) const
{
	boost::format formatter( mTestcaseNameFormat );
	formatter.exceptions( boost::io::no_error_bits );

	return out << formatter
			% mSystemNameID
			% aTraceSequence.tid;
}


/**
 * USED TYPE DEFINITION
 */
void TTCNBaseTraceFormatter::formatDeclarationTypedef(
		OutStream & out, const TracePoint & aTracePoint,
		const BaseTypeSpecifier & aTS, const std::string & typeName)
{
	if( (not setofTreatedType.insert( &aTS ).second)
		|| (not setofTreatedTypeName.insert( typeName ).second) )
	{
		return;
	}

	switch( aTS.getTypeSpecifierKind() )
	{
		case TYPE_ARRAY_SPECIFIER:
		case TYPE_VECTOR_SPECIFIER:
		case TYPE_REVERSE_VECTOR_SPECIFIER:
		case TYPE_LIST_SPECIFIER:
		case TYPE_SET_SPECIFIER:
		case TYPE_MULTISET_SPECIFIER:
		case TYPE_FIFO_SPECIFIER:
		case TYPE_LIFO_SPECIFIER:
		case TYPE_MULTI_FIFO_SPECIFIER:
		case TYPE_MULTI_LIFO_SPECIFIER:
		{
			const ContainerTypeSpecifier & containerTS =
					aTS.to< ContainerTypeSpecifier >();

			StringOutStream outTypeName( out );
			dataTypeName( outTypeName, containerTS.getContentsTypeSpecifier() )
					<< "_" << containerTS.strSpecifierKing();

			mapofTreatedTypeName[ typeName ] = outTypeName.str();

			formatDeclarationTypedef(out, aTracePoint,
					containerTS.getContentsTypeSpecifier());

			out << TAB << "type "
				<< ( containerTS.hasTypeSetOrMultiset() ? "set" : "record" );
			if( containerTS.isBound() )
			{
				out << " length(" << (aTS.isTypedArray() ? "" : "0 .. ")
					<< containerTS.size() << ")";
			}
			out << " of "
				<< ttcnTypename( containerTS.getContentsTypeSpecifier() )
				<< " " << outTypeName.str() << std::endl << std::endl;

			break;
		}

		case TYPE_CLASS_SPECIFIER:
		case TYPE_UNION_SPECIFIER:
		{
			const ClassTypeSpecifier & strucTS = aTS.to< ClassTypeSpecifier >();
			std::size_t sizeT = strucTS.size();

			Symbol aField;

			for( std::size_t idx = 0 ; idx < sizeT ; ++idx )
			{
				aField = strucTS.getSymbolData(idx);

				formatDeclarationTypedef(out,
						aTracePoint, aField.getTypeSpecifier());
			}

			// Type Structure/Record/Union declaration
			out << TAB << "type " << (aTS.isTypedUnion() ? "union " : "record ");
			dataTypeName( out , typeName ) << " {";
			for( std::size_t idx = 0 ; idx < sizeT ; ++idx )
			{
				aField = strucTS.getSymbolData(idx);

				out << ( (idx == 0) ? "" : "," ) << std::endl
					<< TAB2 << ttcnTypename( aField.getTypeSpecifier() )
					<< " " << aField.getNameID();
			}
			out << std::endl << TAB << "}" << std::endl << std::endl;

			break;
		}

		case TYPE_ENUM_SPECIFIER:
		{
			const EnumTypeSpecifier & enumTS = aTS.to< EnumTypeSpecifier >();

			// Type enum declaration
			out << TAB << "type enumerated ";
			dataTypeName( out , typeName ) << " {";

			std::size_t sizeT = enumTS.getSymbolData().size();
			for( std::size_t idx = 0 ; idx < sizeT ; ++idx )
			{
				out << ( (idx == 0) ? "" : "," ) << std::endl
					<< TAB2 << enumTS.getSymbolData(idx).getNameID();

				if( enumTS.getSymbolData(idx).hasValue() )
				{
					out << "("
						<<  enumTS.getSymbolData(idx).getValue().str()
						<< ")";
				}
			}
			out << std::endl << TAB << "}" << std::endl << std::endl;

			break;
		}

		case TYPE_INTERVAL_SPECIFIER:
		{
			const IntervalTypeSpecifier & intervalTS =
					aTS.to< IntervalTypeSpecifier >();

			out << TAB << "type "
				<< ttcnTypename( intervalTS.getSupportTypeSpecifier() );
			dataTypeName( out , typeName )
				<< " ("   << intervalTS.getInfimum().str()
				<< " .. " << intervalTS.getSupremum().str()
				<< ");"    << std::endl << std::endl;

			break;
		}

		case TYPE_STRING_SPECIFIER:
		{
			if( aTS.isBound() )
			{
				out << TAB << "type charstring ";
				dataTypeName( out , typeName )
					<< " length( " << aTS.getMinimumSize()
					<< " .. " << aTS.getMaximumSize() << " );"
					<< std::endl << std::endl;
			}

			break;
		}

		case TYPE_ALIAS_SPECIFIER:
		{
			if( aTS.hasConstraint() )
			{
//				formatDeclaration(aTracePoint,
//					aTS.to< TypeAliasSpecifier >().targetTypeSpecifier(),
//					typeName);

				const BaseTypeSpecifier & targetTS =
					aTS.to< TypeAliasSpecifier >().targetTypeSpecifier();

				out << TAB << "type " << ttcnTypename( targetTS ) << " ";
				dataTypeName( out , typeName ) << "{ "
					<< aTS.getConstraint().as_ptr<AvmProgram>()->getAvmCode().str()
					<< " };" << std::endl << std::endl;
			}
			else
			{
				formatDeclarationTypedef(out, aTracePoint,
					aTS.to< TypeAliasSpecifier >().targetTypeSpecifier(),
					typeName);
			}

			break;
		}

		default:
		{
			if( aTS.weaklyTypedInteger() && (aTS.getBitSize() > 0) )
			{
				out << TAB << "type integer "; // << aTS.getNameID()
				dataTypeName( out , typeName )
					<< " ("   << aTS.minIntegerValue()
					<< " .. " << aTS.maxIntegerValue()
					<< ");"    << std::endl << std::endl;
			}
			else if( /*aTS.isTypedSimple() &&*/ aTS.hasConstraint() )
			{
				//!! TODO
				out << TAB << "type " << typeName;
				dataTypeName(out, aTS) << "{ "
					<< aTS.getConstraint().as_ptr<AvmProgram>()->getCode().str()
					<< " };" << std::endl << std::endl;
			}

			break;
		}
	}
}


/**
 * COMMUNICATING CHANNEL DECLARATIONS
 */
void TTCNBaseTraceFormatter::formatDeclarationChannels()
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
			outChannelDefinitionBuffer
				<< TAB << "type port port_" << (*itChannel).getNameID()
				<< " message {" << std::endl;

			outChannelDefinitionBuffer << TAB2
					<< "port port_" << (*itChannel).getNameID()
					<< " " << (*itChannel).getNameID() << ";" << std::endl;

			itPort = (*itChannel).channel().getContents().begin();
			endPort = (*itChannel).channel().getContents().end();
			for( ; itPort != endPort ; ++itPort )
			{
				if( setofTracePointObjectName.contains(
						(*itPort).rawPort()->getNameID() ) )
				{
					outChannelDefinitionBuffer << TAB2
						<< ( (*itPort).asPort().getModifier().isDirectionInput()
								? "out" : "in" )
						<< " " << (*itPort).getNameID() << ";" << std::endl;
				}
			}
			outChannelDefinitionBuffer << TAB << "}" << std::endl;
		}
	}
}


void TTCNBaseTraceFormatter::collectDeclarationCommunicatingChannel(
		const TracePoint & aTracePoint)
{
	if( aTracePoint.object->is< InstanceOfPort >() )
	{
		const InstanceOfPort & aPort = aTracePoint.object->to< InstanceOfPort >();

		// Liste des channels associés aux signaux
		if( aPort.hasRoutingChannel() )
		{
			setofCommunicationgChannel.insert( aPort.getRoutingChannel() );
		}
		else
		{
//!![TRACE ] to delete
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_COUT << "Messsage erreur ??? : Signal non connecté : "
//			<< str_header( aPort ) << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		}
	}
}


/**
 * COMMUNICATING MESSAGE-RECORD DECLARATIONS
 */

void TTCNBaseTraceFormatter::formatDeclaration(const TracePoint & aTracePoint)
{
	formatDeclarationCommunicatingMessage(outDeclarationMessageRecordBuffer,
			outDeclarationTypedefBuffer, aTracePoint);

	collectDeclarationCommunicatingChannel( aTracePoint );
}

void TTCNBaseTraceFormatter::formatDeclarationCommunicatingMessage(
		OutStream & out, OutStream & outTypedefBuffer,
		const TracePoint & aTracePoint)
{
	if( aTracePoint.object->is< InstanceOfPort >() )
	{
		const InstanceOfPort & aPort = aTracePoint.object->to< InstanceOfPort >();

		// Records declaration
		//
		ArrayOfBF::const_iterator it = aPort.getParameters().begin();
		ArrayOfBF::const_iterator endIt = aPort.getParameters().end();

		if( aPort.hasParameter() && it != endIt )
		{
			// signal avec au moins un paramètre à afficher
			//
			messageTypeName( out << TAB << "type record " , aPort ) << " {";

			for( std::size_t offset = 0 ; it != endIt ; ++it , ++offset )
			{
				out << ( (offset == 0) ? "" : "," ) << std::endl;

				// paramètre anonyme
				if( (*it).is< BaseTypeSpecifier >() )
				{
					formatDeclarationTypedef(outTypedefBuffer, aTracePoint,
							(*it).to< BaseTypeSpecifier >());

					out << TAB2
						<< ttcnTypename((*it).to< BaseTypeSpecifier >())
						<< " p" << mTemplatesPortMessageAnonymParameterPrefix
						<< offset << "_unamed";
				}
				// paramètre nommé
				else if( (*it).is< InstanceOfData >() )
				{
					const InstanceOfData & aParam =
							(*it).to< InstanceOfData >();

					formatDeclarationTypedef(outTypedefBuffer,
							aTracePoint, aParam.getTypeSpecifier());

					out << TAB2 << ttcnTypename( aParam.getTypeSpecifier() )
							<< " ";
					// le nom
					if( (aParam.getNameID()[0] == '$')
						|| (aParam.getNameID()[0] == '#') )
					{
						out << mTemplatesPortMessageAnonymParameterPrefix
							<< aParam.getNameID().substr(1);
					}
					else
					{
						out << aParam.getNameID();
					}
				}
				// #bind expression parameter
				else
				{
				}
			}
			out << std::endl << TAB << "}" << std::endl;
		}
		else
		{
			// signal sans paramètre à afficher
			//
			messageTypeName( out << TAB << "type enumerated " , aPort)
				<< " { enum_" << aPort.getNameID() << " }"
				<< std::endl << std::endl;
		}

		// Message-based Port Declaration
		out << TAB << "type port ";
		portTypeName( out , aPort ) << " message {"
			<< std::endl
			<< TAB2 << ( aPort.getModifier().isDirectionInout() ? "inout" :
				(aPort.getModifier().isDirectionInput() ? "out" : "in") );
		messageTypeName( out << " " , aPort ) << ";"
			<< std::endl
			<< TAB << "}" << std::endl << std::endl;

		// Port-Instance Declaration
		outPortInstanceDeclarationBuffer << TAB2 << "port ";
		portTypeName( outPortInstanceDeclarationBuffer , aPort ) << " ";
		portInstanceName( outPortInstanceDeclarationBuffer , aPort )
			<< ";" << std::endl;

		// Implementation of port-instance mapping to system
		outPortInstanceMappingToSystemBuffer << TAB2 << "map( self:";
		portInstanceName( outPortInstanceMappingToSystemBuffer , aPort )
			<< " , system:";
		portInstanceName( outPortInstanceMappingToSystemBuffer , aPort )
			<< " );" << std::endl;

		// Implementation of port-instance unmapping from system
		outPortInstanceUnmappingToSystemBuffer << TAB2 << "unmap( self:";
		portInstanceName( outPortInstanceUnmappingToSystemBuffer , aPort )
			<< " , system:";
		portInstanceName( outPortInstanceUnmappingToSystemBuffer , aPort )
			<< " );" << std::endl;

/*
		// Ports declaration
		//
		switch( aTracePoint.op )
		{
			case AVM_OPCODE_INPUT_ENV:
			{
				inoutSignalName = "out " + aTracePoint.object->getNameID();
				break;
			}

			case AVM_OPCODE_OUTPUT_ENV:
			{
				inoutSignalName = "in " + aTracePoint.object->getNameID();
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


void TTCNBaseTraceFormatter::formatDeclarationConstant(OutStream & out,
		const TracePoint & aTracePoint, const InstanceOfData & paramConstant)
{
	if( paramConstant.hasValue() )
	{
		formatDeclarationTypedef(out,
				aTracePoint, paramConstant.getTypeSpecifier());

		out << TAB << "const "
			<< ttcnTypename( paramConstant.getTypeSpecifier() )
			<< paramConstant.getNameID() << " := "
			<< paramConstant.getValue().str() << std::endl;
	}
}


/**
 * MESSAGE TEMPLATE WITHOUT PARAMETERS
 */
void TTCNBaseTraceFormatter::formatTemplateWithoutParameters(
		OutStream & out, const TracePoint & aTracePoint)
{
	const InstanceOfPort & aPort = aTracePoint.object->to< InstanceOfPort >();

	ArrayOfBF::const_iterator it = aPort.getParameters().begin();
	ArrayOfBF::const_iterator endIt = aPort.getParameters().end();

	if( aPort.hasParameter() && it != endIt )
	{
		// signal avec au moins un paramètre à afficher
		//
		messageTypeName( out << TAB << "template " , aPort ) << " ";
		formatTemplateValueName( out, aTracePoint )
			<< " := {";

		out << INCR_INDENT;
		for( std::size_t offset = 0 ; it != endIt ; ++it , ++offset )
		{
			out << ( (offset == 0) ? "" : "," ) << std::endl;

			// paramètre anonyme
			if( (*it).is< BaseTypeSpecifier >() )
			{
				formatTemplateWithoutParameters(out, aTracePoint.val(offset),
					(*it).to< BaseTypeSpecifier >(),
					(OSS() << "$" << offset << "_unamed").str(), offset);
			}
			// paramètre nommé
			else if( (*it).is< InstanceOfData >() )
			{
				const InstanceOfData & aParam =
						(*it).to< InstanceOfData >();

				formatTemplateWithoutParameters(out, aTracePoint.val(offset),
					aParam.getTypeSpecifier(), aParam.getNameID(), offset);
			}
			// #bind expression parameter
			else
			{
				// Cf Arnault si cas erreur ???
			}
		}
		out << DECR_INDENT << std::endl
				<< TAB << "}" << std::endl << std::endl;
	}
	else
	{
		// signal sans paramètre à afficher
		//
		messageTypeName( out << TAB << "template " , aPort ) << " ";
		formatTemplateValueName( out, aTracePoint )
			<< " := ?;"	<< std::endl << std::endl;
	}
}


void TTCNBaseTraceFormatter::formatTemplateWithoutParameters(
		OutStream & out, const BF & value, const BaseTypeSpecifier & aTS,
		const std::string & aParamName, std::size_t anOffset)
{
	// Affichage de "nom := "
	if( (aParamName[0] == '$') || (aParamName[0] == '#') )
	{
		out << TAB << mTemplatesPortMessageAnonymParameterPrefix
			<< aParamName.substr(1) << " := " ;
	}
	else
	{
		out << TAB << aParamName << " := " ;
	}

	if( value.invalid() )
	{
		out << "nullptr";
	}
	else if( aTS.hasTypeContainer() )
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
				out << value.str();
//				if( not aTS.isTypedSimple() )
//				{
//					format_TTCN_Templates(aTracePoint,
//							containerTS.getTypeSpecifier(), aParamName);
//				}
				break;
			}
		}
	}

	else if( aTS.isTypedStructure() )
	{
		const ClassTypeSpecifier & structTS = aTS.to< ClassTypeSpecifier >();
		std::size_t sizeT = structTS.size();

		Symbol aField;

		out << "{" << INCR_INDENT;

		for( std::size_t idx = 0 ; idx < sizeT ; ++idx )
		{
			aField = structTS.getSymbolData(idx);

			out << ( (idx == 0) ? "" : "," ) << std::endl;

			formatTemplateWithoutParameters(
					out, value.to< ArrayBF >().at( idx ),
					aField.getTypeSpecifier(), aField.getNameID(), idx);
		}

		out << std::endl << DECR_INDENT_TAB << "}";
	}

	else if( aTS.isTypedEnum() )
	{
		const EnumTypeSpecifier & enumTS = aTS.to< EnumTypeSpecifier >();

		// Affichage de la valeur numérique
		if( value.is< InstanceOfData >() )
		{
			const InstanceOfData & aSymbol = value.to< InstanceOfData >();

			if( enumTS.hasSymbolData(aSymbol) )
			{
				out << aSymbol.getNameID();
			}
			else
			{
				AVM_OS_ERROR_ALERT
						<< "TTCNTitanTraceFormatter::format_TTCN_Templates"
						<< " :> Unexpected symbol\n<< " << str_header( aSymbol )
						<< " >>\nfor the enum type << "
						<< enumTS.getFullyQualifiedNameID() << " >> !!!"
						<< SEND_ALERT;
			}
		}
		else
		{
			const Symbol & aSymbol = enumTS.getSymbolDataByValue(value);
			if( aSymbol.valid() )
			{
				out << aSymbol.getNameID();
			}
			else
			{
				AVM_OS_ERROR_ALERT
						<< "TTCNTitanTraceFormatter::format_TTCN_Templates"
							" :>\nUnexpected symbol value << "
						<< value.str() << " >> for the enum type << "
						<< enumTS.getFullyQualifiedNameID()
						<< " >> for the parameter << param"
						<< aParamName << " >> !!!"
						<< SEND_ALERT;

				out << enumTS.getNameID()
						<< "[ " << value.str() << " ]";
			}
		}
	}

	else if( value.is< Character >() )
	{
		// On remplace 'x' par "x"
		out << value.to< Character >().strChar('"');
	}
	else //if( aTS.isTypedSimple() )
	{
		// Affichage de la valeur numérique
		if( value.is< ArrayBF >() )
		{
			out << value.to< ArrayBF >().at( anOffset ).str();
		}
		else
		{
			out << value.str();
		}
	}
}


void TTCNBaseTraceFormatter::formatTestcaseWithTemplateWithoutParameters(
		OutStream & out, const TracePoint & aTracePoint, bool isFirstTime4Object)
{
	formatTemplateWithoutParameters(out, aTracePoint);

	// TEST CASES
	StringOutStream outTemplateName( out );
	formatTemplateValueName(outTemplateName, aTracePoint);

	StringOutStream outTemplateParameters( out );

	formatTestcase(outTemplateName, outTemplateParameters, aTracePoint);

}


/**
 * MESSAGE TEMPLATE WITH PARAMETERS
 */
void TTCNBaseTraceFormatter::formatTestcaseWithTemplateWithParameters(
		OutStream & out, const TracePoint & aTracePoint, bool isFirstTime4Object)
{
	const InstanceOfPort & aPort =
			aTracePoint.object->to< InstanceOfPort >();

	// Records declaration
	//
	ArrayOfBF::const_iterator it = aPort.getParameters().begin();
	ArrayOfBF::const_iterator endIt = aPort.getParameters().end();

	StringOutStream outTemplateParametersValue( out );

	if( aPort.hasParameter() && it != endIt )
	{
		// message avec au moins un paramètre à afficher
		//
		// Unique declaration/definition format
		if( isFirstTime4Object )
		{
			formatTemplateParametrizedName( out << TAB << "template ", aTracePoint )
					<< "(";
		}

		StringOutStream outTemplateBody( AVM_TAB1_INDENT , out );

		for( std::size_t offset = 0 ; it != endIt ; ++it , ++offset )
		{
			// Unique declaration/definition format
			if( isFirstTime4Object )
			{
				out << ( (offset == 0) ? "" : ", ");
			}

			// paramètre anonyme
			if( (*it).is< BaseTypeSpecifier >() )
			{
				// Unique declaration/definition format
				if( isFirstTime4Object )
				{
					const BaseTypeSpecifier & aTypeSpecifier =
							(*it).to< BaseTypeSpecifier >();

					formatDeclarationTypedef(outDeclarationTypedefBuffer,
							aTracePoint, aTypeSpecifier);

					out << ttcnTypename( aTypeSpecifier )
						<< " " << mTemplatesPortMessageArgumentParameterPrefix
						<< offset << "_unamed";

					outTemplateBody << TAB2
						<< mTemplatesPortMessageAnonymParameterPrefix
						<< offset << "_unamed := "
						<< mTemplatesPortMessageArgumentParameterPrefix
						<< offset << "_unamed;" << std::endl;
				}

				// Value format
				formatTemplatesParametersValue(outTemplateParametersValue,
						(*it).to< BaseTypeSpecifier >(),
						aTracePoint.val(offset), offset);
			}
			// paramètre nommé
			else if( (*it).is< InstanceOfData >() )
			{
				const InstanceOfData & aParam =
						(*it).to< InstanceOfData >();

				// Unique declaration/definition format
				if( isFirstTime4Object )
				{
					formatDeclarationTypedef(outDeclarationTypedefBuffer,
							aTracePoint, aParam.getTypeSpecifier());

					out << ttcnTypename( aParam.getTypeSpecifier() ) << " ";
					// le nom
					if( (aParam.getNameID()[0] == '$')
						|| (aParam.getNameID()[0] == '#') )
					{
						out << mTemplatesPortMessageArgumentParameterPrefix
							<< aParam.getNameID().substr(1);

						outTemplateBody << TAB2
							<< mTemplatesPortMessageAnonymParameterPrefix
							<< aParam.getNameID().substr(1) << " := "
							<< mTemplatesPortMessageArgumentParameterPrefix
							<< aParam.getNameID().substr(1) << ";" << std::endl;
					}
					else
					{
						out << mTemplatesPortMessageArgumentParameterPrefix
							<< "_" << aParam.getNameID();

						outTemplateBody << TAB2
							<< aParam.getNameID() << " := "
							<< mTemplatesPortMessageArgumentParameterPrefix
							<< "_" << aParam.getNameID() << ";" << std::endl;
					}
				}

				// Value format
				formatTemplatesParametersValue(outTemplateParametersValue,
						aParam.getTypeSpecifier(),
						aTracePoint.val(offset), offset);
			}
			// #bind expression parameter
			else
			{
			}
		}

		// Unique declaration/definition format
		if( isFirstTime4Object )
		{
			out << ") := {" << std::endl
				<< outTemplateBody.str()
				<< TAB << "}" << std::endl << std::endl;
		}
	}
	else if( isFirstTime4Object )
	{
		// message sans paramètre à afficher
		//
		messageTypeName( out << TAB << "template " , aPort ) << " ";
		formatTemplateParametrizedName( out, aTracePoint )
			<< " := ?;"	<< std::endl << std::endl;
	}

	// TEST CASES format
	StringOutStream outTemplateName( out );
	formatTemplateParametrizedName(outTemplateName, aTracePoint);

	formatTestcase(outTemplateName, outTemplateParametersValue, aTracePoint);
}


/**
 * MESSAGE FUNCTION WITH PARAMETERS
 */
void TTCNBaseTraceFormatter::formatTestcaseWithTemplateFunctionWithParameters(
		OutStream & out, const TracePoint & aTracePoint, bool isFirstTime4Object)
{
	const InstanceOfPort & aPort = aTracePoint.object->to< InstanceOfPort >();

	StringOutStream outTemplateParametersValue;

	// Records declaration
	//
	ArrayOfBF::const_iterator it = aPort.getParameters().begin();
	ArrayOfBF::const_iterator endIt = aPort.getParameters().end();

	if( aPort.hasParameter() && it != endIt )
	{
		// message avec au moins un paramètre à afficher
		//
		StringOutStream outFunctionBody( AVM_TAB1_INDENT );

		// Unique declaration/definition format
		if( isFirstTime4Object )
		{
			formatTemplateFunctionName( out << TAB << "function ", aTracePoint )
					<< "(";
		}

		for( std::size_t offset = 0 ; it != endIt ; ++it , ++offset )
		{
			outTemplateParametersValue << ( (offset == 0) ? "" : " , " );

			if( isFirstTime4Object )
			{
				out << ( (offset == 0) ? "" : ", ");

				outFunctionBody << ( (offset == 0) ? "" : " , ");
			}

			// paramètre anonyme
			if( (*it).is< BaseTypeSpecifier >() )
			{
				const BaseTypeSpecifier & aTypeSpecifier =
						(*it).to< BaseTypeSpecifier >();

				// Unique declaration/definition format
				if( isFirstTime4Object )
				{
					formatDeclarationTypedef(outDeclarationTypedefBuffer,
						aTracePoint, aTypeSpecifier);

					out << ttcnTypename( aTypeSpecifier )
						<< " " << mTemplatesPortMessageArgumentParameterPrefix
						<< offset << "_unamed";

					outFunctionBody
						<< mTemplatesPortMessageArgumentParameterPrefix
						<< offset << "_unamed";
				}

				// Value format
				formatTemplatesParametersValue(outTemplateParametersValue,
						aTypeSpecifier, aTracePoint.val(offset), offset);
			}
			// paramètre nommé
			else if( (*it).is< InstanceOfData >() )
			{
				const InstanceOfData & aParam = (*it).to< InstanceOfData >();

				// Unique declaration/definition format
				if( isFirstTime4Object )
				{
					formatDeclarationTypedef(outDeclarationTypedefBuffer,
							aTracePoint, aParam.getTypeSpecifier());

					out << ttcnTypename( aParam.getTypeSpecifier() ) << " ";
					// le nom
					if( (aParam.getNameID()[0] == '$')
						|| (aParam.getNameID()[0] == '#') )
					{
						out << mTemplatesPortMessageArgumentParameterPrefix
							<< aParam.getNameID().substr(1);

						outFunctionBody
							<< mTemplatesPortMessageArgumentParameterPrefix
							<< aParam.getNameID().substr(1);
					}
					else
					{
						out << mTemplatesPortMessageArgumentParameterPrefix
							<< "_" << aParam.getNameID();

						outFunctionBody
							<< mTemplatesPortMessageArgumentParameterPrefix
							<< "_" << aParam.getNameID();
					}
				}

				// Value format
				formatTemplatesParametersValue(outTemplateParametersValue,
						aParam.getTypeSpecifier(),
						aTracePoint.val(offset), offset);
			}
			// #bind expression parameter
			else
			{
			}
		}

		// Unique declaration/definition format
		if( isFirstTime4Object )
		{
			messageTypeName( out << ") return template ",  aPort )
				<< " {" << std::endl

				<< TAB2 << "return { " << outFunctionBody.str() << " };" << std::endl

				<< TAB << "}" << std::endl << std::endl;
		}
	}
	else if( isFirstTime4Object )
	{
		// message sans paramètre à afficher
		//
		messageTypeName( out << TAB << "template " , aPort ) << " ";
		formatTemplateFunctionName( out, aTracePoint )
			<< " := ?;"	<< std::endl << std::endl;
	}

	// TEST CASES format
	StringOutStream outTemplateName( out );
	formatTemplateFunctionName(outTemplateName, aTracePoint);

	formatTestcase(outTemplateName, outTemplateParametersValue, aTracePoint);
}


/**
 * MESSAGE TEMPLATE / FUNCTION PARAMETERS VALUE
 */
void TTCNBaseTraceFormatter::formatTemplatesParametersValue(
		OutStream & out, const BaseTypeSpecifier & aTS,
		const BF & value, std::size_t anOffset)
{
	switch( aTS.getTypeSpecifierKind() )
	{
		case TYPE_ARRAY_SPECIFIER:
		case TYPE_VECTOR_SPECIFIER:
		case TYPE_REVERSE_VECTOR_SPECIFIER:
		case TYPE_LIST_SPECIFIER:
		case TYPE_SET_SPECIFIER:
		case TYPE_MULTISET_SPECIFIER:
		case TYPE_FIFO_SPECIFIER:
		case TYPE_LIFO_SPECIFIER:
		case TYPE_MULTI_FIFO_SPECIFIER:
		case TYPE_MULTI_LIFO_SPECIFIER:
		{
			out << value.str();

			break;
		}

		case TYPE_CLASS_SPECIFIER:
		case TYPE_UNION_SPECIFIER:
		{
			const ClassTypeSpecifier & structTS = aTS.to< ClassTypeSpecifier >();
			std::size_t sizeT = structTS.size();

			const ArrayBF & arrayValue = value.to< ArrayBF >();

			out << "{ ";
			for( std::size_t idx = 0 ; idx < sizeT ; ++idx )
			{
				formatTemplatesParametersValue(
						out << ( (idx == 0) ? "" : " , " ),
						structTS.getSymbolData(idx).getTypeSpecifier(),
						arrayValue[idx], idx);
			}
			out << TAB << " }" ;

			break;
		}

		case TYPE_ENUM_SPECIFIER:
		{
			const EnumTypeSpecifier & enumTS = aTS.to< EnumTypeSpecifier >();

			if( value.is< InstanceOfData >() )
			{
				const InstanceOfData & aSymbol = value.to< InstanceOfData >();

				if( enumTS.hasSymbolData(aSymbol) )
				{
					out << aSymbol.getNameID();
				}
				else
				{
					AVM_OS_ERROR_ALERT
							<< "TTCNTitanTraceFormatter::format_TTCN_Templates"
							<< " :> Unexpected symbol\n<< " << str_header( aSymbol )
							<< " >>\nfor the enum type << "
							<< enumTS.getFullyQualifiedNameID() << " >> !!!"
							<< SEND_ALERT;
				}
			}
			else
			{
				const Symbol & aSymbol = enumTS.getSymbolDataByValue(value);
				if( aSymbol.valid() )
				{
					out << aSymbol.getNameID();
				}
				else
				{
					AVM_OS_ERROR_ALERT
							<< "TTCNTitanTraceFormatter::format_TTCN_Templates"
								" :>\nUnexpected symbol value << "
							<< value.str() << " >> for the enum type << "
							<< enumTS.getFullyQualifiedNameID() << " >> !!!"
							<< SEND_ALERT;

					out << enumTS.getNameID()
							<< "[ " << value.str() << " ]";
				}
			}

			break;
		}

		case TYPE_CHARACTER_SPECIFIER:
		{
			// On remplace 'x' par "x"
			out << value.to< Character >().strChar('"');

			break;
		}

		case TYPE_STRING_SPECIFIER:
		{
			out << value.to< String >().str();

			break;
		}

		case TYPE_ALIAS_SPECIFIER:
		{
			formatTemplatesParametersValue(out,
					aTS.to< TypeAliasSpecifier >().targetTypeSpecifier(),
					value, anOffset);

			break;
		}

		default:
		{
			// Affichage de la valeur numérique
			if( value.is< ArrayBF >() )
			{
				out << value.to< ArrayBF >().at( anOffset ).str();
			}
			else
			{
				out << value.str();
			}

			break;
		}
	}
}

} /* namespace sep */

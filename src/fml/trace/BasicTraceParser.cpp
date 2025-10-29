/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 févr. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BasicTraceParser.h"

#include <fstream>

#include <fml/expression/ExpressionConstructor.h>

#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/infrastructure/PropertyPart.h>

#include <fml/symbol/Symbol.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <sew/Configuration.h>


namespace sep
{

////////////////////////////////////////////////////////////////////////////////
// OTHER API
////////////////////////////////////////////////////////////////////////////////

/*
 * Exemple de trace basique
1
TSI_target?1
120
RSD_ENABLED_source!1
0
PSD_ENABLED_source!1
423385
RSD_CMD_source!1
0
PSD_STATE1_target?0
3025646
DEP_AUTH1_source!1
1059822
TSI1_target?0

BASIC#XLIA:
	INPUT  env_connection_signal(  )
	OUTPUT env_enter_pin_message(  )
	INPUT  env_user_pin( 3782 )
	OUTPUT env_asked_withdrawal_message(  )
	INPUT  env_asked_withdrawal( 5001 )
	OUTPUT env_operation_not_possible( 2 , 5000 )
*/

bool BasicTraceParser::parseBasicXliaTrace(TraceSequence & aTraceElement,
		std::ifstream & inFile, const BF & aVarTime)
{
	bool isOK = true;

		//for debug purposes
	bool isOKLine = true;
	std::size_t traceLine = 0;

	bfVarTime = aVarTime;

	std::string inLine;

	while( inFile.good() )
	{
		traceLine ++;

		std::getline(inFile, inLine);

		StringTools::trim( inLine );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_CLOG << "PARSER : the trace line is >>" << inLine << "<<"
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

		if( (inLine == "\\n") || inLine.empty() )
		{
			// !!NOTHING: SKIP NEWLINE
			isOKLine = true;
		}
		else if((inLine[0]) == '#')
		{
			// COMMENT
			isOKLine = true;
		}
		else if( inLine.starts_with("delta" )
				|| inLine.starts_with("$delta")
				|| inLine.starts_with("delay")
				|| inLine.starts_with("$delay")
				|| inLine.starts_with(PropertyPart::VAR_ID_DELTA_TIME) )
		{
			isOKLine = parseBasicXliaTraceDuration(aTraceElement, inLine, aVarTime);
		}
		else if( REGEX_STARTS(inLine, "(input|output|INPUT|OUTPUT)") )
		{
			isOKLine = parseBasicXliaTraceSignal(aTraceElement, inLine, traceLine);
		}

		else if((inLine[0]) == '{')
		{
			isOKLine = parseBasicTraceStructure(aTraceElement, inLine);
		}

		isOK = isOKLine && isOK;

		if(not isOKLine)
		{
			AVM_OS_WARN << "Error found on the trace line "
					<< traceLine << ": " << inLine << std::endl;
		}

	}

	return( isOK );
}

bool BasicTraceParser::parseBasicXliaTraceDuration(TraceSequence & aTraceElement,
		const std::string & inLine, const BF & aVarTime)
{

	std::string::size_type pos = inLine.find('=');
	std::string delta = inLine.substr(pos+1);
	StringTools::ltrim( delta );

	if( (pos = delta.find_first_of("/.")) != std::string::npos )
	{
		bfTP = new TracePoint(
				ENUM_TRACE_POINT::TRACE_TIME_NATURE,
				AVM_OPCODE_TIMED_GUARD, nullptr,
				aVarTime.to_ptr< InstanceOfData >(),
				ExpressionConstructor::newRational(delta) );

		aTraceElement.points.append( bfTP );

		return( true );
	}
	else
	{
		avm_integer_t duration;
		if( from_string(delta, duration, std::dec) )
		{
			bfTP = new TracePoint(
					ENUM_TRACE_POINT::TRACE_TIME_NATURE,
					AVM_OPCODE_TIMED_GUARD, nullptr,
					aVarTime.to_ptr< InstanceOfData >(),
					ExpressionConstructor::newInteger(duration) );

			aTraceElement.points.append( bfTP );

			return( true );
		}
	}

	return( false );
}


bool BasicTraceParser::parseBasicXliaTraceSignal(TraceSequence & aTraceElement,
		const std::string & inLine, std::size_t traceLine)
{
	bfTP = aTracePoint = new TracePoint(ENUM_TRACE_POINT::TRACE_COM_NATURE);

	Modifier::DIRECTION_KIND ioDirection = Modifier::DIRECTION_INOUT_KIND;

	//std::string::size_type pos = inLine.find('?');
	std::string message;

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "PARSER : the message trace is >>" << inLine << "<<"
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

	if(  REGEX_STARTS(inLine, "(input|INPUT)") )
	{
		ioDirection = Modifier::DIRECTION_INPUT_KIND;
		message = inLine.substr(6);
	}
	else if(  REGEX_STARTS(inLine, "(output|OUTPUT)") )
	{
		ioDirection = Modifier::DIRECTION_OUTPUT_KIND;
		message = inLine.substr(7);
	}

	message = StringTools::trim(message);

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "PARSER : the message is >>" << message << "<<" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

	std::string::size_type pos = message.find('(');

	ExecutableQuery XQuery( mConfiguration );

	std::string msgPort = message.substr(0,
			(pos != std::string::npos) ? pos : message.length());

	ListOfSymbol listofPort;
	std::size_t foundCount = XQuery.getPortByQualifiedNameID(
			msgPort, listofPort, ioDirection, false );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "PARSER : the port is >>" << msgPort << "<<" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

	if( foundCount == 1 )
	{
		InstanceOfPort * port = listofPort.first().rawPort();
		aTracePoint->object = port;

		if( ioDirection == Modifier::DIRECTION_INPUT_KIND )
		{
			if( port->hasInputRoutingData() &&
				port->getInputRoutingData().isProtocolENV() )
			{
				aTracePoint->op = AVM_OPCODE_INPUT_ENV;
			}
			else
			{
				aTracePoint->op = AVM_OPCODE_INPUT;
			}
		}
		else if( ioDirection == Modifier::DIRECTION_OUTPUT_KIND )
		{
			if( port->hasOutputRoutingData() &&
				port->getOutputRoutingData().isProtocolENV() )
			{
				aTracePoint->op = AVM_OPCODE_OUTPUT_ENV;
			}
			else
			{
				aTracePoint->op = AVM_OPCODE_OUTPUT;
			}
		}

		if( pos != std::string::npos )
		{
			if( parseBasicTraceSignalParameters(aTracePoint, port,
					message.substr(pos + 1, message.size()-pos-2)) )
			{
				aTraceElement.points.append( bfTP );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "PARSER : and its parameters are >>"
			<< message.substr(pos + 1, message.size()-pos-2) << "<<"
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
			}
		}
		else
		{
			aTraceElement.points.append( bfTP );
		}

		return( true );
	}
	else
	{
		if( foundCount > 1 )
		{
			AVM_OS_WARN << "Error< line: " << traceLine
						<< " >: Found < " << foundCount
						<< " > ports named < " << msgPort << " > " << std::endl;
			for( const auto & foundPort : listofPort )
			{
				AVM_OS_WARN << '\t' << foundPort.getFullyQualifiedNameID()
							<< std::endl;
			}
		}
		else
		{
			AVM_OS_WARN << "Error< line: " << traceLine
						<< " > : Unfound port < "
						<< msgPort << " > " << std::endl;
		}

		aTracePoint->value = ExpressionConstructor::newString(inLine);

		aTraceElement.points.append( bfTP );
	}

	return( false );
}



bool BasicTraceParser::parseBasicTrace(TraceSequence & aTraceElement,
		std::ifstream & inFile, const BF & aVarTime)
{
	bool isOK = true;

		//for debug purposes
	bool isOKLine = true;
	std::size_t traceLine = 0;

	bfVarTime = aVarTime;

	std::string inLine;

	while( inFile.good() )
	{
		traceLine ++;

		std::getline(inFile, inLine);

		StringTools::ltrim( inLine );

		if( (inLine == "\\n") || inLine.empty() )
		{
			// !!NOTHING: SKIP NEWLINE
			isOKLine = true;
		}
		else if((inLine[0]) == '#')
		{
			// COMMENT
			isOKLine = true;
		}
		else if( std::isdigit(inLine[0]) )
		{
			isOKLine = parseBasicTraceDuration(aTraceElement, inLine, aVarTime);
		}
		else if( std::isalpha(inLine[0]) )
		{
			isOKLine = parseBasicTraceSignal(aTraceElement, inLine, traceLine);
		}

		else if((inLine[0]) == '{')
		{
			isOKLine = parseBasicTraceStructure(aTraceElement, inLine);
		}

		isOK = isOKLine && isOK;

		if(not isOKLine)
		{
			AVM_OS_WARN << "Error found on the trace line "
					<< traceLine << ": " << inLine << std::endl << std::endl;
		}

	}

	return( isOK );
}



bool BasicTraceParser::parseBasicTraceDuration(TraceSequence & aTraceElement,
		const std::string & inLine, const BF & aVarTime)
{
	avm_integer_t duration;
	if( from_string(inLine, duration, std::dec) )
	{
		bfTP = new TracePoint(
				ENUM_TRACE_POINT::TRACE_TIME_NATURE,
				AVM_OPCODE_TIMED_GUARD, nullptr,
				aVarTime.to_ptr< InstanceOfData >(),
				ExpressionConstructor::newInteger(duration) );

		aTraceElement.points.append( bfTP );

		return( true );
	}

	return( false );
}

bool BasicTraceParser::parseBasicTraceSignal(TraceSequence & aTraceElement,
		const std::string & inLine, std::size_t traceLine)
{
	bfTP = aTracePoint = new TracePoint(ENUM_TRACE_POINT::TRACE_COM_NATURE);

	Modifier::DIRECTION_KIND io_dir;

	std::string::size_type pos = inLine.find('?');
	if( pos != std::string::npos )
	{
		io_dir = Modifier::DIRECTION_INPUT_KIND;
		aTracePoint->op = AVM_OPCODE_INPUT;
	}
	else if( (pos = inLine.find('!')) != std::string::npos )
	{
		io_dir = Modifier::DIRECTION_OUTPUT_KIND;
		aTracePoint->op = AVM_OPCODE_OUTPUT;
	}

	if( pos != std::string::npos )
	{
		ExecutableQuery XQuery( mConfiguration );

		std::string msgPort = inLine.substr(0, pos);

		ListOfSymbol listofPort;
		std::size_t foundCount = XQuery.getPortByQualifiedNameID(
				msgPort, listofPort, io_dir, false );

		if( foundCount == 1 )
		{
			InstanceOfPort* port = listofPort.first().rawPort();
			aTracePoint->object = port;

			if( parseBasicTraceSignalParameters(
					aTracePoint, port,  inLine.substr(pos + 1)))
			{
				aTraceElement.points.append( bfTP );

				return( true );
			}
		}
		else if( foundCount > 1 )
		{
			AVM_OS_WARN << "Error< line: " << traceLine
						<< " >: Found < " << foundCount
						<< " > ports named < " << msgPort << " > " << std::endl;
			for( const auto & foundPort : listofPort )
			{
				AVM_OS_WARN << '\t' << foundPort.getFullyQualifiedNameID()
							<< std::endl;
			}
		}
		else
		{
			AVM_OS_WARN << "Error< line: " << traceLine
						<< " > : Unfound port < "
						<< msgPort << " > " << std::endl;
		}
	}

	aTracePoint->value = ExpressionConstructor::newString(inLine);

	aTraceElement.points.append( bfTP );

	return( false );
}

/*
 * This method takes an inputs:
 * a trace point, a port and a string expression
 *
 */
bool BasicTraceParser::parseBasicTraceSignalParameters(
		TracePoint * aTracePoint, const InstanceOfPort* port,
		const std::string & anExpr)
{
	std::string::size_type pos;
	std::size_t nbParams = port->getParameterCount();
	std::size_t count = 0;
	//this variables is used to count the number of parameters given in the trace
	std::string currentExpr = anExpr;

	//TODO: do the verification on the number of parameters while parsing
	// e.g. create an array with the parameter values
	while ((pos = currentExpr.find(',') )!= std::string::npos)
	{
		currentExpr = currentExpr.substr(pos+1);
		count++;
	}

	StringTools::trim(currentExpr);
	if( currentExpr.compare("") != 0 )
	{
		count++;
	}

	if( count != port->getParameterCount() )
	{
		// if the number of parameters given in the trace does
		// not match  the declaration in the file specification
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "PARSER WARNING : the number of parameters expected "
			"is " << nbParams << " while the actual number of parameters "
			"given in the trace is " << count << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		return false;
	}

	if (nbParams != 0)
	{
		aTracePoint->newArrayValue(nbParams);
		std::string  param;
		currentExpr = anExpr;
		int i = 0;
		bool correct = true;
		//the correct number of parameters has already been ascertained
		while (((pos = currentExpr.find(',')) != std::string::npos) && correct)
		{
			// retrieving parameter from the string
			param = currentExpr.substr(0, pos);
			BF paramBF = parseBasicTraceSignalParameter(
					(port->getParameterType(i)), param);

			if(paramBF == nullptr)
			{
				return false;
			}
			else
			{
				aTracePoint->val(i, paramBF);
				i++;
				currentExpr = currentExpr.substr(pos+1);
			}
		}
		param = StringTools::trim(currentExpr);
		BF paramBF = parseBasicTraceSignalParameter(port->getParameterType(i), param);
		//BF paramBF = ExpressionConstructor::newExpr(* port->getParameterType(i), param);
		if(paramBF == nullptr)
		{
			return false;
		}
		else
		{
			aTracePoint->val(i, paramBF);
		}
		return true;
	}
	else
	{
		return true;
	}
	return true;
}

/*
 * anExpr is the string representing the parameter to be parsed
 * aTypeSpecifier is the type of the parameter
 * returns a BF representing the parameter
 */
BF BasicTraceParser::parseBasicTraceSignalParameter(
		const ITypeSpecifier & aTypeSpecifier, const std::string & anExpr)
{
	std::string param = anExpr;
	StringTools::trim(param);

	const BaseTypeSpecifier & targetTypeSpecifier =
			aTypeSpecifier.thisTypeSpecifier().referedTypeSpecifier();

	BF paramBF;

//AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
//	AVM_OS_LOG << "PARSER: parameter type: ";
//    targetTypeSpecifier.toStream(AVM_OS_LOG);
//	AVM_OS_LOG << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

	// Removing encompassing quotes in strings before building
	if( targetTypeSpecifier.isTypedString()
		&& (not param.empty()) && (param[0] == '"') )
	{
		param = param.substr(1, param.size() - 2);

		paramBF = ExpressionConstructor::newString(param);

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "PARSER: reading a string: " << param << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	}

	else if( targetTypeSpecifier.isTypedCharacter() && (not param.empty()) )
	{
		if( param.size() == 1 )
		{
			paramBF = ExpressionConstructor::newChar(param[0]);
		}
		else if( param[0] == '\'' )
		{
			paramBF = ExpressionConstructor::newChar(param[1]);
		}
		else // ERROR !!!
		{
			paramBF = ExpressionConstructor::newChar(param[0]);
		}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "PARSER: reading a string: " << param << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	}
	// machines as parameters contain run and pid information,
	// we must remove them (no configuration yet)
	else if( targetTypeSpecifier.isTypedMachine() )
	{
		if( param.starts_with("run::") )
		{
			std::string::size_type parampos = param.find(':', 5);
			if( parampos != std::string::npos )
			{
				param = param.substr(parampos+1);
			}

			paramBF = ExpressionConstructor::newExprRuntime(mConfiguration, param);
		}
		else
		{
			paramBF = ExpressionConstructor::newExprMachine(mConfiguration, param);
		}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "PARSER: reading a machine: " << param << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	}

	else
	{
		paramBF = ExpressionConstructor::newExpr(
				mConfiguration, targetTypeSpecifier, param);
	}

	if( paramBF.invalid() )
	{
		AVM_OS_WARN << "PARSER: failed to build BF from parameter: "
				<< param << std::endl;
	}
	else
	{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "PARSER: parameter value read: " << paramBF << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	}

	return paramBF;
}


bool BasicTraceParser::parseBasicTraceStructure(
		TraceSequence & aTraceElement, const std::string & inLine)
{
	return( false );
}


} /* namespace sep */

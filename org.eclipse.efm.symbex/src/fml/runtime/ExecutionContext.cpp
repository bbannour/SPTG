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

#include <fml/runtime/ExecutionContext.h>


#include <fml/expression/StatementConstructor.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{


/**
 * ID_NUMBER
 */
avm_uint32_t ExecutionContextHeader::ID_NUMBER = 0;


/**
 * TRACE CONSTANT
 */
avm_size_t ExecutionContext::EC_CHILD_TRACE_DEFAULT_SIZE = 42;

avm_size_t ExecutionContext::EXECUTION_CONTEXT_CHILD_TRACE_MAX =
		EC_CHILD_TRACE_DEFAULT_SIZE;


/*
 * DEFAULT NULL REFERENCE
 */
ExecutionContext ExecutionContext::_NULL_;

/**
 * LCA -LCRA
 */
const ExecutionContext * ExecutionContext::LCA(
		const ExecutionContext * anEC) const
{
	const ExecutionContext * containerOfThis = this;
	const ExecutionContext * containerOfEC = anEC;

	while( containerOfThis->getHeight() < containerOfEC->getHeight() )
	{
		containerOfEC = containerOfEC->getContainer();
	}
	while( containerOfEC->getHeight() < containerOfThis->getHeight() )
	{
		containerOfThis = containerOfThis->getContainer();
	}

	while( containerOfThis != containerOfEC )
	{
		containerOfThis = containerOfThis->getContainer();
		containerOfEC = containerOfEC->getContainer();
	}

	return( containerOfThis );
}


/**
 * Serialization
 */
void ExecutionContext::toDebug(OutStream & out) const
{
	out << TAB << "EC:" << "<"
		<< "Id:" << getIdNumber()   << ";"
		<< "Ev:" << getEvalNumber() << ";"
		<<  "H:" << getHeight()     << ";"
		<<  "W:" << getWidth()    //<< ";"
//		<<  "Q:" << ((avm_uint32_t) getWeight())
		<< ">{"  << INCR_INDENT;

	if( hasExecutionData() )
	{
		out << " SC: " << refExecutionData().strStateConfToFscn() << EOL;
	}

	if( hasRunnableElementTrace() )
	{
		out << TAB << "EXE   : ";  getRunnableElementTrace().toStream(out);
	}

	if( hasIOElementTrace() )
	{
		out << TAB << "TRACE : "; getIOElementTrace().toStream(out);
	}

	// FLAGS
	if( hasFlags() )
	{
		out << TAB << "/*FLAGS{ " << getFlags().str() << " }*/" << EOL;
	}

	// INFORMATION
	if( hasInformation())
	{
		if( getInformation()->hasInfo() )
		{
			out << TAB << "INFO{" << EOL_INCR_INDENT;
			getInformation()->toFscnInfo(out);
			out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
		}

		if( getInformation()->hasSpecificInfo() )
		{
			out << TAB << "/*INFORMATION{" << EOL_INCR_INDENT;
			getInformation()->toFscn(out);
			out << DECR_INDENT_TAB << "}*/" << EOL_FLUSH;
		}
	}
	// END INFORMATION


	if( hasNodeCondition() && getNodeCondition().isNotEqualTrue() )
	{
		out << DEFAULT_WRAP_DATA << TAB << "NC:"
			<< str_indent( getNodeCondition() ) << END_WRAP_EOL;
	}

	if( hasNodeTimedCondition() &&
			getNodeTimedCondition().isNotEqualTrue() )
	{
		out << DEFAULT_WRAP_DATA << TAB << "NtC:"
			<< str_indent( getNodeTimedCondition() ) << END_WRAP_EOL;
	}

	if( hasExecutionData() )
	{
		ScopeIncrIndent asii(out);

		refExecutionData().toFscn(out, hasPrevious() ?
				getPrevious()->getExecutionData() : NULL);
	}

	out << DECR_INDENT_TAB << "}" << EOL;
}


void ExecutionContext::toDebugFet(OutStream & out) const
{
	out << TAB << "ec( "
		<< "Id:" << getIdNumber()     << " , "
		<< "Pr:" << getPrevIdNumber() << " , "
		<< "Ev:" << getEvalNumber()   << " , "
		<< "H:"  << getHeight()       << " , "
		<< "W:"  << getWidth()        << " , "
		<< "Q:"  << getStrWeight()
		<< " )" ;

	AVM_DEBUG_REF_COUNTER(out);
	out << " {" << EOL_INCR_INDENT;

	if( hasNodeCondition() &&
		getNodeCondition().isNotEqualTrue() )
	{
		out << DEFAULT_WRAP_DATA << TAB << "fired#condition ="
			<< str_indent( getNodeCondition() )
			<< ";" << END_WRAP_EOL;
	}

	if( hasNodeTimedCondition() &&
		getNodeTimedCondition().isNotEqualTrue() )
	{
		out << DEFAULT_WRAP_DATA << TAB << "fired#timed#condition ="
			<< str_indent( getNodeTimedCondition() ) << ";" << END_WRAP_EOL;
	}

	if( hasRunnableElementTrace() )
	{
		out << TAB << "fired =" << str_indent( getRunnableElementTrace() )
			<< ";" << EOL_FLUSH;
	}

	if( hasIOElementTrace() )
	{
		out << TAB << "trace =" << str_indent( getIOElementTrace() )
			<< ";" << EOL_FLUSH;
	}


	if( hasInformation() )
	{
		getInformation()->toStream(out);
	}

	if( hasExecutionData() )
	{
		refExecutionData().toStream(out);
	}


	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}



void ExecutionContext::toStream(OutStream & out) const
{
	out << TAB << getFlags().toString(" ") << "ec( "
		<< "Id:" << getIdNumber()     << " , "
		<< "Pr:" << getPrevIdNumber() << " , "
		<< "Ev:" << getEvalNumber()   << " , "
		<<  "H:" << getHeight()       << " , "
		<<  "W:" << getWidth()        << " , "
		<<  "Q:" << getStrWeight()
		<< " )" ;

	AVM_DEBUG_REF_COUNTER(out);
	out << " {" << EOL_INCR_INDENT;

	if( hasNodeCondition() && getNodeCondition().isNotEqualTrue() )
	{
		out << DEFAULT_WRAP_DATA << TAB << "nodecondition ="
			<< str_indent( getNodeCondition() ) << ";" << END_WRAP_EOL;
	}

	if( hasNodeTimedCondition() && getNodeTimedCondition().isNotEqualTrue() )
	{
		out << DEFAULT_WRAP_DATA << TAB << "nodetimedcondition ="
			<< str_indent( getNodeTimedCondition() ) << ";" << END_WRAP_EOL;
	}

	if( hasRunnableElementTrace() )
	{
		out << TAB << "fired =" << str_indent( getRunnableElementTrace() )
			<< ";" << EOL_FLUSH;
	}

	if( hasIOElementTrace() )
	{
		out << TAB << "trace =" << str_indent( getIOElementTrace() )
			<< ";" << EOL_FLUSH;
	}


	if( hasInformation() )
	{
		getInformation()->toStream(out);
	}

	if( hasExecutionData() )
	{
		refExecutionData().toStream(out);
	}

	out << DECR_INDENT;


	if( hasChildContext() )
	{
		out << EOL_TAB << "ec:" << EOL_INCR_INDENT;
		for( child_iterator it = begin() ; it != end() ; ++it )
		{
			(*it)->toStream(out);
		}
		out << DECR_INDENT;
	}

	out << TAB << "}" << EOL_FLUSH;
}


void ExecutionContext::toFscn(OutStream & out,
		const ExecutionData * aPreviousExecData) const
{
	out << TAB << "EC:" << "<"
		<< "Id:" << getIdNumber()   << ";"
		<< "Ev:" << getEvalNumber() << ";"
		<<  "H:" << getHeight()     << ";"
		<<  "W:" << getWidth()    //<< ";"
//		<<  "Q:" << ((avm_uint32_t) getWeight())
		<<  ">{" ;

	if( hasExecutionData() )
	{
		out << " SC: " << refExecutionData().strStateConfToFscn() << EOL;

		avm_size_t indexAlias = 0;
		bool isAlias = false;
		if( (getPrevious() != NULL) )
		{
			// Recherche des nouveaux PID
			if(refExecutionData().getTableOfRuntime().size()
				> getPrevious()->refExecutionData().getTableOfRuntime().size())
			{
				indexAlias = getPrevious()
						->refExecutionData().getTableOfRuntime().size();
				isAlias = true;
			}
		}
		else
		{
			isAlias = true;
		}

		if( isAlias )
		{
			out << TAB2 << "ALIAS{" << EOL;

			for( avm_size_t i = indexAlias ;
					i < refExecutionData().getTableOfRuntime().size() ; ++i)
			{
				const RuntimeID & currentRID =
					refExecutionData().getTableOfRuntime().at(i)->getRID();

				out << TAB3 << ":ppid#" << currentRID.getPRid()
					<< ":" << "pid#" << currentRID.getRid();

				if( currentRID.getInstance()->
						getSpecifier().isDesignPrototypeStatic() )
				{
					out << " = "
						<< currentRID.getInstance()->getAstFullyQualifiedNameID()
						<< ";" << EOL;
				}
				else if( currentRID.getInstance()->
						getSpecifier().isDesignInstance() )
				{
					out << " = "
						<< currentRID.getInstance()->getAstFullyQualifiedNameID()
						<< ";";

					out << " // model is "
						<< currentRID.getExecutable()->getAstFullyQualifiedNameID()
						<< ";" << EOL;
				}
				else
				{
					out << " = " << currentRID.getFullyQualifiedNameID() << ";"
						<< " // model is "
						<< currentRID.getExecutable()->getAstFullyQualifiedNameID()
						<< ";" << EOL;
				}


				if( currentRID.getInstance()->hasExecutable() )
				{
					const TableOfSymbol & rfBuffers =
							currentRID.getExecutable()->getBuffer();
					if(rfBuffers.nonempty()){
						out << TAB4 << "BUFFER NUMBER = " << rfBuffers.size()
								<< ";" << EOL;

						out << TAB4 << "/*BUFFER{" << EOL;

						TableOfSymbol::const_iterator itBuffer = rfBuffers.begin();
						TableOfSymbol::const_iterator endBuffer = rfBuffers.end();
						for( ; itBuffer != endBuffer ; ++itBuffer )
						{
							out << TAB5 << ":ppid#" << currentRID.getPRid()
									<< ":" << "pid#" << currentRID.getRid()
									<< ":" << (*itBuffer).getNameID() << " = ";
							out << ( ((*itBuffer).hasAstElement()) ?
									(*itBuffer).getAstFullyQualifiedNameID()
									: (*itBuffer).getFullyQualifiedNameID() )
									<< ";" << EOL;
						}

						out << TAB4 << "}*/" << EOL;
					}

					if( currentRID.getExecutable()->hasData() )
					{
						out << TAB4 << "DATA{" << EOL;

						TableOfInstanceOfData::const_raw_iterator itData =
								currentRID.getExecutable()->getBasicData().begin();
						TableOfInstanceOfData::const_raw_iterator endData =
								currentRID.getExecutable()->getBasicData().end();
						for( ; (itData != endData) ; ++itData )
						{
							out << TAB5 << ":ppid#" << currentRID.getPRid()
								<< ":pid#" << currentRID.getRid() << ":"
								<< (itData)->getNameID() << " = "
								<< ( ( (itData)->hasAstElement() )
										? (itData)->getAstFullyQualifiedNameID()
										: (itData)->getFullyQualifiedNameID() )
								<< ";" << EOL;
						}

						out << TAB4 << "}" << EOL;
					}

					if( currentRID.getExecutable()->hasPort() )
					{
						out << TAB4 << "INTERFACE{" << EOL;

						TableOfSymbol & rfInterface =
								currentRID.getExecutable()->getPort();
						TableOfSymbol::iterator itPort = rfInterface.begin();
						for(  ; itPort != rfInterface.end() ; ++itPort )
						{
							out << TAB5 << ":ppid#" << currentRID.getPRid()
								<< ":pid#" << currentRID.getRid() << ":"
								<<  (*itPort).getNameID() << " = "
								<<  (*itPort).getAstFullyQualifiedNameID()
								<< ";" << EOL;
						}

						out << TAB4 << "}" << EOL;
					}
				}
			}
			out << TAB2 << "}" << EOL;
		}
	}

	if( hasRunnableElementTrace() )
	{
		out << DEFAULT_WRAP_DATA << TAB2 << "EXE:"
			<< str_indent( getRunnableElementTrace() ) << END_WRAP_EOL;
	}

	if( hasIOElementTrace() )
	{
		out << DEFAULT_WRAP_DATA << TAB2 << "TRACE:"
			<< str_indent( getIOElementTrace() ) << END_WRAP_EOL;
	}

	// FLAGS
	if( hasFlags() )
	{
		out << TAB2 << "/*FLAGS{ " << getFlags().str() << " }*/" << EOL;
	}

	// INFORMATION
	if( hasInformation() )
	{
		if( getInformation()->hasInfo() )
		{
			out << TAB2 << "INFO{" << EOL_INCR2_INDENT;
			getInformation()->toFscnInfo(out);
			out << DECR2_INDENT_TAB2 << "}" << EOL_FLUSH;
		}

		if( getInformation()->hasSpecificInfo() )
		{
			out << TAB2 << "/*INFORMATION{" << EOL_INCR2_INDENT;
			getInformation()->toFscn(out);
			out << DECR2_INDENT_TAB2 << "}*/" << EOL_FLUSH;
		}
	}
	// END INFORMATION


	if( hasNodeCondition() && getNodeCondition().isNotEqualTrue() )
	{
		out << DEFAULT_WRAP_DATA << TAB2 << "NC:"
			<< str_indent( getNodeCondition() ) << END_WRAP_EOL;
	}

	if( hasNodeTimedCondition() &&
			getNodeTimedCondition().isNotEqualTrue() )
	{
		out << DEFAULT_WRAP_DATA << TAB2 << "NtC:"
			<< str_indent( getNodeTimedCondition() ) << END_WRAP_EOL;
	}

	if( hasExecutionData() )
	{
		ScopeIncrIndent asii(out);

		refExecutionData().toFscn(out, aPreviousExecData);
	}


	if( hasChildContext() )
	{
		out << INCR_INDENT;

		for( child_iterator it = begin() ; it != end() ; ++it )
		{
			(*it)->toFscn(out, getExecutionData());
		}

		out << DECR_INDENT;
	}

	out << TAB << "}" << EOL;
}


/**
 * ExecutionContext::str_min
 *
 */
std::string ExecutionContext::str_min() const
{
	return( OSS() << str_position() << " "
			<< refExecutionData().strStateConf() );
}


/**
 * ExecutionContext::str_Positions
 *
 */
std::string ExecutionContext::str_position() const
{
	std::ostringstream oss;

	oss << "Id:" /*<< std::setw(4)*/ << getIdNumber();

	oss << " PE:";
	if( hasContainer() )
	{
		//oss /*<< std::setw(4)*/ << getContainer()->getIdNumber();
		oss /*<< std::setw(4)*/ << getContainer()->getEvalNumber();
	}
	else
	{
		oss << "ROOT";
	}

	oss << " H:" /*<< std::setw(4)*/ << getHeight();
	oss << " W:" /*<< std::setw(4)*/ << getWidth();
	oss << " Q:" /*<< std::setw(2)*/ << getStrWeight();

	return( oss.str() );
}


/**
 * traceMinimum
 *
 */
void ExecutionContext::traceMinimum(OutStream & out) const
{
	out << TAB << "ctx:" << getIdNumber();

	if( getWeight() != 0 )
	{
		out << " Q:" << getStrWeight();
	}
	out << " " << refExecutionData().strStateConf() << EOL;
}

void ExecutionContext::traceDefault(OutStream & out) const
{
	out << TAB << "ctx:" << getIdNumber();
	if( getWeight() != 0 )
	{
		out << " Q:" << getStrWeight();
	}

	out << " " << refExecutionData().strStateConf() << "|=> fired ";

	if( hasRunnableElementTrace() )
	{
		out << getRunnableElementTrace().str();
	}
	else
	{
		out << "nothing in " << refExecutionData().getSystemRID().str();
	}

	out << EOL;
}

void ExecutionContext::debugDefault(OutStream & out) const
{
	out << TAB << "ctx:" << getIdNumber();
	if( getWeight() != 0 )
	{
		out << " Q:" << getStrWeight();
	}
	out << " " << refExecutionData().strStateConf() << EOL;

	if( hasRunnableElementTrace() )
	{
		getRunnableElementTrace().toStream(out << TAB << "EXE   : ");
	}
	if( hasIOElementTrace() )
	{
		getIOElementTrace().toStream(out << TAB << "TRACE : ");
	}
}


void ExecutionContext::traceMinimum(OutStream & out,
		ListOfExecutionContext & listofEC, const std::string & header)
{
	out << TAB << header << " {" << EOL_INCR_INDENT;
	ListOfExecutionContext::const_iterator itEC = listofEC.begin();
	ListOfExecutionContext::const_iterator endEC = listofEC.end();
	for( ; itEC != endEC ; ++itEC )
	{
		(*itEC)->traceMinimum(out);
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}

void ExecutionContext::traceMinimum(OutStream & out,
		VectorOfExecutionContext & listofEC, const std::string & header)
{
	out << TAB << header << " {" << EOL_INCR_INDENT;
	VectorOfExecutionContext::const_iterator itEC = listofEC.begin();
	VectorOfExecutionContext::const_iterator endEC = listofEC.end();
	for( ; itEC != endEC ; ++itEC )
	{
		(*itEC)->traceMinimum(out);
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}


void ExecutionContext::traceDefault(OutStream & out,
		ListOfExecutionContext & listofEC, const std::string & header)
{
	out << TAB << header << " {" << EOL_INCR_INDENT;
	ListOfExecutionContext::const_iterator itEC = listofEC.begin();
	ListOfExecutionContext::const_iterator endEC = listofEC.end();
	for( ; itEC != endEC ; ++itEC )
	{
		(*itEC)->traceDefault(out);
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}

void ExecutionContext::traceDefault(OutStream & out,
		VectorOfExecutionContext & listofEC, const std::string & header)
{
	out << TAB << header << " {" << EOL_INCR_INDENT;
	VectorOfExecutionContext::const_iterator itEC = listofEC.begin();
	VectorOfExecutionContext::const_iterator endEC = listofEC.end();
	for( ; itEC != endEC ; ++itEC )
	{
		(*itEC)->traceDefault(out);
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}


void ExecutionContext::debugDefault(OutStream & out,
		ListOfExecutionContext & listofEC, const std::string & header)
{
	out << TAB << header << " {" << EOL_INCR_INDENT;
	ListOfExecutionContext::const_iterator itEC = listofEC.begin();
	ListOfExecutionContext::const_iterator endEC = listofEC.end();
	for( ; itEC != endEC ; ++itEC )
	{
		(*itEC)->debugDefault(out);
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}

void ExecutionContext::debugDefault(OutStream & out,
		VectorOfExecutionContext & listofEC, const std::string & header)
{
	out << TAB << header << " {" << EOL_INCR_INDENT;
	VectorOfExecutionContext::const_iterator itEC = listofEC.begin();
	VectorOfExecutionContext::const_iterator endEC = listofEC.end();
	for( ; itEC != endEC ; ++itEC )
	{
		(*itEC)->debugDefault(out);
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}


/**
 * OK
 */
void ExecutionContext::writeTraceAfterExec(OutStream & out) const
{
	avm_size_t count = 1;
	child_iterator it = begin();
	child_iterator endIt = end();
	for( ; (it != endIt) && (count < EXECUTION_CONTEXT_CHILD_TRACE_MAX);
			++it , ++count )
	{
		out << TAB << "==>E[?] " << (*it)->str_min() << "|=> fired ";

		if( (*it)->hasRunnableElementTrace() )
		{
			out << (*it)->getRunnableElementTrace().str();
		}
		else
		{
			out << "machine#main " << refExecutionData().getSystemRID().str();
		}

		out << EOL;
	}

	if( it != endIt )
	{
		out << TAB << "==>E[?] " << mChildContexts.last()->str_min()
			<< "|=> fired ";

		if( mChildContexts.last()->hasRunnableElementTrace() )
		{
			out << mChildContexts.last()->getRunnableElementTrace().str();
		}
		else
		{
			out << "machine#main " << refExecutionData().getSystemRID().str();
		}

		out << EOL;
	}

	if( count == EXECUTION_CONTEXT_CHILD_TRACE_MAX )
	{
		out << REPEAT("--------", 10) << EOL
			<< "<< PRINT " << EXECUTION_CONTEXT_CHILD_TRACE_MAX << " OF "
			<< size() << " EXECUTION CONTEXT RESULT >> " << EOL;

		if( EXECUTION_CONTEXT_CHILD_TRACE_MAX == EC_CHILD_TRACE_DEFAULT_SIZE )
		{
			out << REPEAT("--------", 10) << EOL
				<< "==> You could fix that limit using the integer attribute"
				" << @ec_size = <integer>; >> in the section TRACE " << EOL;
		}
	}

	out << REPEAT("--------", 10) << EOL_FLUSH;
}


void ExecutionContext::traceDefaultPostEval(OutStream & out) const
{
	avm_size_t count = 1;

	child_iterator it = begin();
	child_iterator endIt = end();
	for( ; (it != endIt) &&
			(count < ExecutionContext::EXECUTION_CONTEXT_CHILD_TRACE_MAX);
			++it , ++count )
	{
		out << TAB << "==> ctx:" << (*it)->getIdNumber();
		if( (*it)->getWeight() != 0 )
		{
			out << " Q:" << (*it)->getStrWeight();
		}
		out << " " << (*it)->refExecutionData().strStateConf();

		out << EOL_TAB << "|=> fired ";

		if( (*it)->hasRunnableElementTrace() )
		{
			out << (*it)->getRunnableElementTrace().str();
		}
		else
		{
			out << "nothing in " << refExecutionData().getSystemRID().str();
		}

		out << EOL;
	}

	if( it != endIt )
	{
		out << TAB << "==> ctx:" << mChildContexts.last()->getIdNumber();
		if( mChildContexts.last()->getWeight() != 0 )
		{
			out << " Q:" << mChildContexts.last()->getStrWeight();
		}
		out << " " << mChildContexts.last()->refExecutionData().strStateConf();

		out << EOL_TAB << "|=> fired ";

		if( mChildContexts.last()->hasRunnableElementTrace() )
		{
			out << mChildContexts.last()->getRunnableElementTrace().str();
		}
		else
		{
			out << "nothing in " << refExecutionData().getSystemRID().str();
		}

		out << EOL;
	}

	if( count == EXECUTION_CONTEXT_CHILD_TRACE_MAX )
	{
		out << REPEAT("--------", 10) << EOL
			<< "<< PRINT " << EXECUTION_CONTEXT_CHILD_TRACE_MAX << " OF "
			<< size() << " EXECUTION CONTEXT RESULT >> " << EOL;

		if( EXECUTION_CONTEXT_CHILD_TRACE_MAX == EC_CHILD_TRACE_DEFAULT_SIZE )
		{
			out << REPEAT("--------", 10) << EOL
				<< "==> You could fix that limit using the integer attribute"
				" << @ec_size = <integer>; >> in the section TRACE " << EOL;
		}
	}

	out << REPEAT("--------", 10) << EOL_FLUSH;
}


/**
 * OK
 */
void ExecutionContext::writeTraceBeforeExec(OutStream & out) const
{
AVM_VERBOSITY_SWITCH_SILENT

	out << TAB << "step[" << std::setw(4) << getEvalNumber() << "]  "
		<< "context[" << std::setw(6) << getIdNumber()
		<< " / " << std::setw(6) << ExecutionContextHeader::ID_NUMBER
		<< "]    " << std::flush;

AVM_VERBOSITY_SWITCH_CASE_MINIMUM

	out << TAB << "step[" << std::setw(4) << getEvalNumber() << "]  "
		<< "context[" << std::setw(6) << getIdNumber()
		<< " / " << std::setw(6) << ExecutionContextHeader::ID_NUMBER
		<< "]    " << std::flush;

AVM_VERBOSITY_SWITCH_CASE_MEDIUM

	out << TAB << "E[" << std::setw(4) << getEvalNumber() << "] "
		<< str_min() << EOL_FLUSH;

AVM_VERBOSITY_SWITCH_CASE_MAXIMUM

	out << TAB << "E[" << std::setw(4) << getEvalNumber() << "] "
		<< str_min() << EOL_FLUSH;

AVM_VERBOSITY_SWITCH_END
}


/**
 * OK
 */
void ExecutionContext::writeTraceForDeadlock(OutStream & out,
		avm_uint32_t nDeadlockCounter) const
{
	out << TAB << " ==> DEADLOCK : " << nDeadlockCounter << "<=="
		<< TAB << " << NO FIREABLE TRANSITIONS FOUND >>" << EOL
		<< TAB << REPEAT("-------", 6) << EOL_FLUSH;
}

/**
 * OK
 */
void ExecutionContext::writeTraceForRedundancy(OutStream & out,
		ExecutionContext * aRedundantExecContext,
		avm_uint32_t nRedundancyCounter) const
{
	out << TAB << " ==> REDUNDANCE : " << nRedundancyCounter << " <=="
		<< std::endl
		<< TAB << " E[" << std::setw(4)
		<< aRedundantExecContext->getEvalNumber()
		<< "] " << aRedundantExecContext->str_min()
		<< std::endl
		<< TAB << REPEAT("-------", 6) << EOL_FLUSH;
}



}

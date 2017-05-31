/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 17 déc. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "OutStream.h"

#include <util/avm_assert.h>
#include <util/avm_vfs.h>

#include <sew/Workflow.h>

#include <fml/workflow/WObject.h>


namespace sep
{


/**
 * CONSOLE PROMPT
 */
const std::string & CONSOLE_DEBUG_PROMPT  = "[DBG] ";

const std::string & CONSOLE_SEW_PROMPT    = "[SEW] ";

const std::string & CONSOLE_CONFIG_PROMPT = "[CFG] ";

const std::string & CONSOLE_SYMBEX_PROMPT = "[SBX] ";


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// OutStream
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * LOAD
 * DISPOSE
 */
void OutStream::load()
{
	_avm_os_log_ = AVM_OS_COUT.OS;

	_avm_os_trace_ = AVM_OS_COUT.OS;

	_avm_os_tdd_ = AVM_OS_COUT.OS;
}

void OutStream::dispose()
{
	// AVM TRACE LOG << ofstream >>
	if( _avm_os_log_ != NULL )
	{
		_avm_os_log_->flush();

		if( (_avm_os_log_ != AVM_OS_COUT.OS) &&
				(_avm_os_log_ != _avm_os_null_) )
		{
//			_avm_os_log->close();
			delete _avm_os_log_;
		}
	}
	_avm_os_log_ = NULL;


	// AVM TRACE DEBUG << ofstream >>
	if( _avm_os_trace_ != NULL )
	{
		_avm_os_trace_->flush();

		if( (_avm_os_trace_ != AVM_OS_COUT.OS) &&
				(_avm_os_trace_ != _avm_os_null_) )
		{
//			_avm_os_trace->close();
			delete _avm_os_trace_;
		}
	}
	_avm_os_trace_ = NULL;


	// AVM TEST DRIVEN DEVELOPMENT << ofstream >>
	if( _avm_os_tdd_ != NULL )
	{
		_avm_os_tdd_->flush();

		if( (_avm_os_tdd_ != AVM_OS_COUT.OS) &&
				(_avm_os_tdd_ != _avm_os_null_) )
		{
//			_avm_os_tdd_->close();
			delete _avm_os_tdd_;
		}
	}
	_avm_os_tdd_ = NULL;


	// AVM NULL << ofstream >>
	if( _avm_os_null_ != NULL )
	{
		delete _avm_os_null_;
	}
}


/**
 * CONFIGURE
 */
/*
// GLOBAL PROPERTY
section PROPERTY
	output#tab = " ";

	fscn#tab = " ";

	line#wrap#width = 80;
	line#wrap#separator = "\n\t";
endsection
*/
bool OutStream::configure(Workflow * aWorkflow)
{
	WObject * seqFORMAT = Query::getWSequenceOrElse(
			aWorkflow->getParameterWObject(), "format", "PROPERTY");

	// GLOBAL INDENT CHAR
	std::string strTab = Query::getRegexWPropertyString(seqFORMAT,
			CONS_WID2("output", "tab"), AVM_OUTPUT_INDENT.CHAR);

	AVM_FSCN_INDENT.CHAR =
			Query::getRegexWPropertyString(
					seqFORMAT, CONS_WID2("fscn", "tab"),
					(strTab != AVM_OUTPUT_INDENT.CHAR) ?
							strTab : AVM_FSCN_INDENT.CHAR);

	AVM_OUTPUT_INDENT.CHAR = strTab;

	/*
	 * DEFAULT_WRAP_DATA
	 */
	if( DEFAULT_WRAP_DATA.configure( seqFORMAT ) )
	{
		//!!NOTHING
	}

	// AVM TRACE LOG << ofstream >>
	if( aWorkflow->hasDeveloperDebugLogFile() )
	{
		_avm_os_log_ = new std::ofstream(
				aWorkflow->getDeveloperDebugLogFileLocation().c_str() );
		if( (_avm_os_log_ == NULL) || _avm_os_log_->fail() )
		{
			_avm_os_log_ = _avm_os_null_;

			AVM_OS_FATAL_ERROR_EXIT
					<< "Failed to open AVM_OS_LOG << "
					<< aWorkflow->getDeveloperDebugLogFileLocation()
					<< " >> file in write mode !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
	else
	{
		_avm_os_log_ = _avm_os_null_;
	}

	AVM_OS_LOG.OS = _avm_os_log_;


	// AVM TRACE DEBUG << ofstream >>
	if( aWorkflow->hasDeveloperDebugTraceFile() )
	{
		_avm_os_trace_ = new std::ofstream(
				aWorkflow->getDeveloperDebugTraceFileLocation().c_str() );
		if( (_avm_os_trace_ == NULL) || _avm_os_trace_->fail() )
		{
			_avm_os_trace_ = _avm_os_null_;

			AVM_OS_FATAL_ERROR_EXIT
					<< "Failed to open AVM_OS_TRACE << "
					<< aWorkflow->getDeveloperDebugTraceFileLocation()
					<< " >> file in write mode !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
	else
	{
		_avm_os_trace_ = _avm_os_null_;
	}

	AVM_OS_TRACE.OS = _avm_os_trace_;


	// AVM TEST DRIVEN DEVELOPMENT << ofstream >>
	if( aWorkflow->hasTddReport() )
	{
		_avm_os_tdd_ = new std::ofstream(
				aWorkflow->getTddReportLocation().c_str() );
		if( (_avm_os_tdd_ == NULL) || _avm_os_tdd_->fail() )
		{
			_avm_os_tdd_ = _avm_os_null_;

			AVM_OS_FATAL_ERROR_EXIT
					<< "Failed to open AVM_OS_TDD << "
					<< aWorkflow->getTddReportLocation()
					<< " >> file in write mode !!!"
					<< SEND_EXIT;

			return( false );
		}
	}
	else
	{
		_avm_os_tdd_ = _avm_os_null_;
	}

	AVM_OS_TDD.OS = _avm_os_tdd_;

	// For ASSERT
	AVM_OS_THROW_EXCEPTION.OS.INDENT = AVM_OUTPUT_INDENT;

	AVM_OS_THROW_ALERT.OS.INDENT = AVM_OUTPUT_INDENT;

	return( true );
}


/**
 * REPEAT
 * COLUMN
 * EMPHASIS
 */
OutStream & OutStream::operator<<(const AvmEMPHASIS & emphasis)
{
	if( emphasis.enableTab ) { ( *OS ) << INDENT.TABS; }
	repeat(emphasis.emph, emphasis.count) << INDENT.EOL;

	std::size_t count = emphasis.count + ( (emphasis.count > 2) ? -2 : 0 );
	// for 2 spaces char --> ' ' emphasis.text ' '

	std::size_t after = 0;
	std::size_t before = 0;

	// emphasis.header
	if( not emphasis.header.empty() )
	{
		if( count > emphasis.header.size() )
		{
			after = (count - emphasis.header.size()) / 2;
			before = count - after - emphasis.header.size();

			if( emphasis.enableTab ) { ( *OS ) << INDENT.TABS; }
			repeat(emphasis.emph, before) << ' ' << emphasis.header << ' ';
			repeat(emphasis.emph, after)  << INDENT.EOL;
		}
		else
		{
			if( emphasis.enableTab ) { ( *OS ) << INDENT.TABS; }
			( *OS ) << emphasis.emph << emphasis.emph
					<< ' ' << emphasis.header << INDENT.EOL;
		}
	}

	// emphasis.body
	if( not emphasis.body.empty() )
	{
		if( count > emphasis.body.size() )
		{
			std::size_t body_after = (count - emphasis.body.size()) / 2;

			std::size_t space = 1;
			bool rightSpace = false;
			if( (after > 0) && (after < body_after) )
			{
				space += body_after - after;

				rightSpace = ( ((emphasis.body.size() + before + after) % 2)
						!= (count % 2) );
			}
			else
			{
				after = body_after;

				before = count - body_after - emphasis.body.size();
			}

			AvmREPEAT< char > center = REPEAT(' ', space);

			if( emphasis.enableTab ) { ( *OS ) << INDENT.TABS; }
			repeat(emphasis.emph, before) << center
					<< emphasis.body << center;
			if( rightSpace ) { ( *OS ) << ' '; }
			repeat(emphasis.emph, after) << INDENT.EOL;
		}
		else
		{
			if( emphasis.enableTab ) { ( *OS ) << INDENT.TABS; }
			( *OS ) << emphasis.emph << emphasis.emph
					<< ' ' << emphasis.body << INDENT.EOL;
		}
	}

	if( emphasis.enableTab ) { ( *OS ) << INDENT.TABS; }
	repeat(emphasis.emph, emphasis.count) << INDENT.EOL << std::flush;

	return( *this );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// GLOBAL PRE-DEFINED STREAM
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * UTIL VARIABLE
 * AVM_OS_NULL
 */
std::ostream * _avm_os_null_ = new std::ostream(NULL);

NullOutStream AVM_OS_NULL;


/**
 * AVM COUT & CERR & DEBUG
 */
// !!! Due to Initialization order !!!
//OutStream AVM_OS_COUT( std::cout , AVM_SPC_INDENT );
OutStream AVM_OS_COUT( std::cout , ""   , " "  , "\n" );

OutStream AVM_OS_CERR(
		((_AVM_EXEC_MODE_ == AVM_EXEC_SERVER_MODE) ? std::cout : std::cerr),
//		AVM_SPC_INDENT );
		""   , " "  , "\n" );

OutStream AVM_OS_DEBUG( std::cout , ""   , "\t"  , "\n" );

/**
 * AVM LOG & TRACE FILE LOCATION
 */
std::string AVM_LOG_FILE_LOCATION;

std::string AVM_TRACE_FILE_LOCATION;


/**
 * UTIL VARIABLE
 * AVM_OS_LOG
 */
std::ostream * _avm_os_log_ = NULL;

//OutStream AVM_OS_LOG( std::cout , AVM_SPC_INDENT );
OutStream AVM_OS_LOG( std::cout , ""   , " "  , "\n" );


/**
 * UTIL VARIABLE
 * AVM_OS_TRACE
 */
std::ostream * _avm_os_trace_ = NULL;

//OutStream AVM_OS_TRACE( std::cout , AVM_SPC_INDENT );
OutStream AVM_OS_TRACE( std::cout , ""   , " "  , "\n" );


/**
 * UTIL VARIABLE
 * AVM_OS_WARN
 */
WarnOutstreamT AVM_OS_WARN(AVM_OS_CERR, AVM_OS_TRACE);

/**
 * UTIL VARIABLE
 * AVM_OS_INFO
 */
InfoOutstreamT AVM_OS_INFO(AVM_OS_COUT, AVM_OS_TRACE);

/**
 * UTIL VARIABLE
 * AVM_OS_CLOG
 */
InfoOutstreamT AVM_OS_CLOG(AVM_OS_COUT, AVM_OS_LOG);


/**
 * UTIL VARIABLE
 * AVM_OS_TDD
 * for Test Driven Development
 */
std::ostream * _avm_os_tdd_ = NULL;

//OutStream AVM_OS_TDD( std::cout , AVM_TAB_INDENT );
OutStream AVM_OS_TDD( std::cout , ""   , "\t" , "\n" );


} /* namespace sep */

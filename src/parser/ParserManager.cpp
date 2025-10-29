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

#include "ParserManager.h"

#include <exception>
#include <fstream>

#include <fml/infrastructure/System.h>
#include <fml/workflow/WObject.h>

#include <parser/Antlr4ErrorFactory.h>
#include <parser/ParserUtil.h>

#include <parser/fml/FMLLexer.h>
#include <parser/fml/FMLParser.h>

//!!! DEPRECATED ANTLR3 C Parser code
//#include <parser/model/fmlLexer.h>
//#include <parser/model/fmlParser.h>

#include <parser/sew/SEWLexer.h>
#include <parser/sew/SEWParser.h>

#include <printer/OutStream.h>

#include <util/avm_vfs.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
ParserManager::ParserManager(const std::string & fileLocation)
: mFileLocation( fileLocation ),
mFilename( VFS::filename( fileLocation ) ),

mErrorCount( 0 ),
mWarningCount( 0 ),
mExceptionMessage( )
{
	//!! NOTHING
}


/**
 * ParserManager::start
 *
 */
System * ParserManager::parseFML(WObjectManager & aWObjectManager)
{
	System * theParseSpec = nullptr;

	mErrorCount = 0;

	if( mFileLocation.empty() )
	{
		AVM_OS_WARN << _SEW_
			<< "< error > Unexpected an empty specification file location !"
			<< std::endl;

		return( nullptr );
	}

	std::ifstream anInputStream( mFileLocation );

	if( anInputStream.fail() )
	{
		AVM_OS_WARN << _SEW_
				<< "< error > Cannot open file '"
				<< mFileLocation << "'." << std::endl;

		avm_set_exit_code( AVM_EXIT_PARSING_ERROR_CODE );

		return( nullptr );
	}

	try
	{
		if( (mFileLocation.rfind(".xfml") != std::string::npos) ||
			(mFileLocation.rfind(".fml" ) != std::string::npos) ||
			(mFileLocation.rfind(".xlia") != std::string::npos) ||
			(mFileLocation.rfind(".xfsp") != std::string::npos) ||
			(mFileLocation.rfind(".lia" ) != std::string::npos) )
		{
			theParseSpec = parseFML(aWObjectManager, anInputStream);
		}

		if( theParseSpec == nullptr )
		{
			AVM_OS_WARN << _SEW_
					<< "< error > NO PARSING RESULT !" << std::endl;

			avm_set_exit_code( AVM_EXIT_PARSING_ERROR_CODE );

			return( nullptr );
		}
	}
	catch( std::exception & e )
	{
		AVM_OS_WARN << _SEW_ << e.what() << std::endl;

		avm_set_exit_code( AVM_EXIT_PARSING_ERROR_CODE );

		return( nullptr );
	}

	return( theParseSpec );
}


/**
 * ParserManager::parseXLIA
 * ANTLR4
 *
 */
System * ParserManager::parseFML(
		WObjectManager & aWObjectManager, std::istream & anInputStream)
{
	///!!! The Return Variable Value *!*
	System * theParseSpec = nullptr;

	Ref<SymbexErrorStrategy> fmlErrorStrategy( new SymbexErrorStrategy() );

	SymbexErrorListener fmlErrorListener;

	mErrorCount = 0;
	ParserUtil::XLIA_SYNTAX_ERROR_COUNT = 0;

	try
	{
		antlr4::ANTLRInputStream input( anInputStream );

		FMLLexer lexer( & input );

		antlr4::CommonTokenStream tokens( & lexer );

		FMLParser  parser( & tokens );

		parser.setErrorHandler(fmlErrorStrategy);

		parser.removeErrorListeners();
		parser.addErrorListener(& fmlErrorListener);

//		lexer.setFilename( mFilename );
		parser.setFilename( mFilename );

//		lexer.resetErrors();
		parser.resetErrors();

		theParseSpec = parser.formalML( & aWObjectManager )->spec;

		mErrorCount = //lexer.numberOfErrors() +
				parser.numberOfErrors() + ParserUtil::XLIA_SYNTAX_ERROR_COUNT;

		AVM_OS_VERBOSITY_MINIMUM( AVM_OS_CLOG ) << _SEW_
				<< "Done ==> " << mErrorCount << " syntax error"
				<< ((mErrorCount > 1)? "s" : "") << " found."
				<< std::endl;

		if( mErrorCount > 0 )
		{
			avm_set_exit_code( AVM_EXIT_PARSING_ERROR_CODE );
		}
	}
	catch( antlr4::RuntimeException & e )
	{
		mExceptionMessage = e.what();

		if( mErrorCount == 0 )
		{
			++mErrorCount;
		}

		avm_set_exit_code( AVM_EXIT_PARSING_EXCEPTION_CODE );
	}

	return( theParseSpec );
}



/**
 * Symbolic Execution Workflow
 * ANTLR4 Parser
 */
WObject * ParserManager::parseSEW(
		WObjectManager & aWObjectManager, std::istream & anInputStream)
{
	///!!! The Return Variable Value *!*
	WObject * theParseParam = WObject::_NULL_;

	Ref<SymbexErrorStrategy> sewErrorStrategy( new SymbexErrorStrategy() );

	SymbexErrorListener sewErrorListener;

	mErrorCount = 0;

	try
	{
		antlr4::ANTLRInputStream input( anInputStream );

		SEWLexer lexer( & input );

		antlr4::CommonTokenStream tokens( & lexer );

//!@?DEBUG:
//tokens.fill();
//for (auto token : tokens.getTokens()) {
//	AVM_OS_LOG << ((antlr4::CommonToken *)token)->toString( & lexer ) << std::endl;
//}

		SEWParser  parser( & tokens );

		parser.setErrorHandler(sewErrorStrategy);

		parser.removeErrorListeners();
		parser.addErrorListener(& sewErrorListener);

		lexer.setFilename( mFilename );
		parser.setFilename( mFilename );

		lexer.resetErrors();
		parser.resetErrors();

//		AVM_OS_VERBOSITY_MINIMUM( AVM_OS_CLOG ) << _SEW_
//				<< "Parsing: " << mFilename << " ..." << std::endl;

		theParseParam = parser.form_grammar( & aWObjectManager )->wfObject;

		mErrorCount = lexer.numberOfErrors() + parser.numberOfErrors();

//		AVM_OS_VERBOSITY_MINIMUM( AVM_OS_CLOG ) << _SEW_
//				<< "Done ==> " << mErrorCount << " syntax error"
//				<< ((mErrorCount > 1)? "s" : "") << " found."
//				<< std::endl;

		if( mErrorCount > 0 )
		{
			avm_set_exit_code( AVM_EXIT_PARSING_ERROR_CODE );
		}
	}
	catch( antlr4::RuntimeException & e )
	{
		mExceptionMessage = e.what();

		if( mErrorCount == 0 )
		{
			++mErrorCount;
		}

		avm_set_exit_code( AVM_EXIT_PARSING_EXCEPTION_CODE );
	}

	return( theParseParam );
}


}

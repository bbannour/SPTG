/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 14 mars 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeMetaStatementCompiler.h"

namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE NOP COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeNothingCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( aCode );
}

BF AvmcodeNothingCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( aCode );
}


BFCode AvmcodeNothingCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( aCode );
}

BFCode AvmcodeNothingCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( aCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE INFORMAL EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeInformalExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileAvmcode(aCTX, aCode) );
}


BFCode AvmcodeInformalExpressionCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileAvmcode(aCTX, aCode) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE TRACE EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeTraceExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileAvmcode(aCTX, aCode) );
}


BFCode AvmcodeTraceExpressionCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileAvmcode(aCTX, aCode) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE DEBUG EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeDebugExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileAvmcode(aCTX, aCode) );
}


BFCode AvmcodeDebugExpressionCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileAvmcode(aCTX, aCode) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE COMMENT EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeCommentExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode = aCode;

	return( newCode );
}


BFCode AvmcodeCommentExpressionCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode = aCode;

	return( newCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE META EVAL STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeMetaEvalStatementCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileAvmcode(aCTX, aCode) );
}


BFCode AvmcodeMetaEvalStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileAvmcode(aCTX, aCode) );
}




////////////////////////////////////////////////////////////////////////////////
// AVMCODE META RUN STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeMetaRunStatementCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileAvmcode(aCTX, aCode) );
}


BFCode AvmcodeMetaRunStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileAvmcode(aCTX, aCode) );
}





} /* namespace sep */

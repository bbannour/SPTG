/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 mars 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "CompilerOfProgram.h"

#include <builder/primitive/AvmcodeCompiler.h>
#include <builder/compiler/Compiler.h>
#include <builder/compiler/CompilerOfVariable.h>

#include <fml/common/SpecifierElement.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/ExecutableForm.h>



namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
CompilerOfProgram::CompilerOfProgram(Compiler & aCompiler)
: BaseCompiler(aCompiler),
mDataCompiler( aCompiler.mDataCompiler )
{
	//!! NOTHING
}


/**
 *******************************************************************************
 * IMPLEMENT FORM PROGRAM
 *******************************************************************************
 *
 * form
 * 	section HEADER
 * 		@ufi = <% UFI %> ;
 * 		@name = <% String %> ;
 * 		@type = <% <PROGRAM> %> ;
 * 		@design = FORM ;
 * 	endsection HEADER
 *
 * 	section PARAM
 * 		( @const = <% Boolean %> ; )?
 * 	endsection PARAM
 *
 * 	section DATA
 * 		( data_typedef )* 		// MODEL of a DATA_TYPE i.e definition of new DATA_TYPE
 * 		( const_decl )* 		// INSTANCE of DATA_TYPE CONSTANT DEFINITION
 * 		( var_decl )* 			// INSTANCE of DATA_TYPE VARIABLE DECLARATION
 * 	endsection DATA
 *
 * 	section MOE
 * 		( @run{ <% <AvmCode> %> } )?
 * 	endsection MOE
 * endform
 *
 ***************************************************************************
 */



/**
 *******************************************************************************
 * PRECOMPILATION
 *******************************************************************************
 */
void CompilerOfProgram::precompileProgram(
		ExecutableForm * aContainer, ObjectElement * aProgram)
{
//	AVM_OS_TRACE << TAB << "<||||| begin precompiling simple Program:> "
//			<< aProgram->getFullyQualifiedNameID() << std::endl;

	// CREATE NEW EXECUTABLE
	AvmProgram * anAvmProgram = new AvmProgram(
			Specifier::SCOPE_PROGRAM_KIND, aContainer, aProgram, 0);

	getSymbolTable().addProgram( aContainer->saveProgram( anAvmProgram ) );

	TableOfInstanceOfData tableOfVariable;

	/*
	 * Allocation of program PARAM variable
	 */
//	if( aMachine->hasDeclarationParam() )
//	{
//		avm_offset_t paramOffset = tableOfVariable.size();
//
//		mDataCompiler.precompileData(anExec, aProgram->getDeclarationParam(),
//				tableOfVariable);
//
//		anAvmProgram->setParamOffsetCount( paramOffset , tableOfVariable.size() );
//	}
//
//	if( aMachine->hasDeclaration() )
//	{
//		PropertyPart * aDeclaration = aProgram->getDeclaration();
//
//		/*
//		 * Allocation of program DATA variable
//		 */
//		mDataCompiler.precompileData(anExec, aDeclaration, tableOfVariable);
//	}


	//////////////////////////////////////////////////////////////////////////////////////////////
	// Update data table
	//////////////////////////////////////////////////////////////////////////////////////////////
	anAvmProgram->setData(tableOfVariable);

//	AVM_OS_TRACE << TAB << ">||||| end precompiling simple Program:> "
//			<< aProgram->getFullyQualifiedNameID() << std::endl;
}




/**
 *******************************************************************************
 * COMPILATION
 *******************************************************************************
 */

/**
 * compile
 * transition
 */
void CompilerOfProgram::compileProgram(AvmProgram * anAvmProgram)
{
	const ObjectElement * aCompiledProgram = anAvmProgram->getAstElement();

//	AVM_OS_TRACE << TAB << "<| compiling<program>: "
//			<< Query::getUfi(aProgram) << std::endl;


	// COMPILATION OF DATA
	mDataCompiler.compileData(anAvmProgram);


	/*
	 * onRun
	 */
	if( aCompiledProgram->is< Routine >() )
	{
		anAvmProgram->setCode( mAvmcodeCompiler.compileStatement(anAvmProgram,
				aCompiledProgram->as< Routine >()->getCode()) );
	}
	if( aCompiledProgram->is< Transition >() )
	{
		anAvmProgram->setCode( mAvmcodeCompiler.compileStatement(anAvmProgram,
				aCompiledProgram->as< Transition >()->getStatement()) );
	}

//	AVM_OS_TRACE << TAB << ">| compiling<program>: "
//			<< Query::getUfi(aProgram) << std::endl << std::endl;
}



}



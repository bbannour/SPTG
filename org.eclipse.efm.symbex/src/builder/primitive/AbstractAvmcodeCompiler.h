/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 avr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef ABSTRACTAVMCODECOMPILER_H_
#define ABSTRACTAVMCODECOMPILER_H_

#include <common/AvmObject.h>

#include <builder/compiler/BaseCompilerTable.h>

#include <builder/primitive/AvmcodeCompiler.h>
#include <builder/primitive/CompilationEnvironment.h>

#include <fml/expression/AvmCode.h>

#include <fml/type/BaseTypeSpecifier.h>


namespace sep
{

class ArrayBF;
class AvmBytecode;

class BaseAvmProgram;
class Element;

class ExecutableForm;

class SymbolTable;


class AbstractAvmcodeCompiler  :  public AvmObject
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AbstractAvmcodeCompiler(AvmcodeCompiler & aCodeCompiler)
	: AvmObject( ),
	AVMCODE_COMPILER( aCodeCompiler )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AbstractAvmcodeCompiler()
	{
		//!! NOTHING
	}


	/*
	 * GETTER
	 * theCompilerTable
	 */
	inline BaseCompilerTable & getCompilerTable()
	{
		return( AVMCODE_COMPILER.getCompilerTable() );
	}


	/*
	 * GETTER
	 * theSymbolTable
	 */
	inline SymbolTable & getSymbolTable()
	{
		return( AVMCODE_COMPILER.getSymbolTable() );
	}


	////////////////////////////////////////////////////////////////////////////
	// SPECIFIC ARGUMENT COMPILATION
	////////////////////////////////////////////////////////////////////////////

	BF compileArgLvalue(COMPILE_CONTEXT * aCTX, const BF & arg);

	BF compileArgRvalue(COMPILE_CONTEXT * aCTX,
			const TypeSpecifier & aType, const BF & arg)
	{
		return( compileArgRvalue(aCTX->clone(aType), arg,
				(aType != TypeManager::UNIVERSAL)) );
	}

	BF compileArgRvalue(COMPILE_CONTEXT * aCTX, const BF & arg,
			bool needTypeChecking = false);

	inline BF compileArgStatement(COMPILE_CONTEXT * aCTX, const BF & arg)
	{
		return( AVMCODE_COMPILER.decode_compileStatement(aCTX, arg) );
	}


	////////////////////////////////////////////////////////////////////////////
	// EXPRESSION COMPILATION STEP
	////////////////////////////////////////////////////////////////////////////

	BFCode compileExpressionCode(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode);

	inline virtual BF compileExpression(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode)
	{
		return( compileExpressionCode(aCTX, aCode) );
	}


	BFCode optimizeExpressionCode(COMPILE_CONTEXT * aCTX, const BFCode & aCode,
			avm_arg_operand_t anOperand = AVM_ARG_EXPRESSION_KIND);

	inline virtual BF optimizeExpression(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode)
	{
		return( optimizeExpressionCode(aCTX, aCode) );
	}


	inline void optimizeArgExpression(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode, avm_offset_t offset)
	{
		if( aCode->at(offset).is< AvmCode >() )
		{
			aCode->safe_set( offset,
					AVMCODE_COMPILER.optimizeExpression(
							aCTX, aCode->at(offset).bfCode()) );
		}
	}

	inline void optimizeArgStatement(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode, avm_offset_t offset)
	{
		if( aCode->at(offset).is< AvmCode >() )
		{
			aCode->safe_set( offset,
					AVMCODE_COMPILER.optimizeStatement(
							aCTX, aCode->at(offset).bfCode()) );
		}
	}


	inline void optimizeArgExpression(COMPILE_CONTEXT * aCTX,
			BFCodeList & listOfCodes)
	{
		BFCodeList::iterator itCode = listOfCodes.begin();
		BFCodeList::iterator endCode = listOfCodes.end();
		for( ; itCode != endCode ; ++itCode )
		{
			(*itCode) = AVMCODE_COMPILER.optimizeExpression(aCTX, (*itCode));
		}
	}

	inline void optimizeArgStatement(COMPILE_CONTEXT * aCTX,
			BFCodeList & listOfCodes)
	{
		BFCodeList::iterator itCode = listOfCodes.begin();
		BFCodeList::iterator endCode = listOfCodes.end();
		for( ; itCode != endCode ; ++itCode )
		{
			(*itCode) = AVMCODE_COMPILER.optimizeStatement(aCTX, (*itCode));
		}
	}


	////////////////////////////////////////////////////////////////////////////
	// STATEMENT COMPILATION STEP
	////////////////////////////////////////////////////////////////////////////

	virtual BFCode compileStatementCode(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode);

	inline virtual BFCode optimizeStatementCode(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode)
	{
		return( optimizeExpressionCode(aCTX, aCode, AVM_ARG_STATEMENT_KIND) );
	}



	inline virtual BFCode compileStatement(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode)
	{
		return( compileStatementCode(aCTX, aCode) );
	}

	inline virtual BFCode optimizeStatement(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode)
	{
		return( aCode );
//		return( optimizeStatementCode(aCTX, aCode) );
	}




	////////////////////////////////////////////////////////////////////////////
	// AVMCODE COMPILATION STEP
	////////////////////////////////////////////////////////////////////////////

	virtual BFCode compileAvmcode(COMPILE_CONTEXT * aCTX, const BFCode & aCode);


	////////////////////////////////////////////////////////////////////////////
	// AVM OPCODE COMPILATION
	////////////////////////////////////////////////////////////////////////////

	static bool mustBeEvaluatedArgument(const BF & arg);

	static bool mustBeEvaluatedArgumentArray(ArrayBF * arrayArg);


	avm_arg_operand_t operandOf(const BF & arg);

	avm_arg_processor_t processorOf(BaseTypeSpecifier * aType);

	avm_arg_operand_t operandOf(BaseTypeSpecifier * aType);


	void setArgcodeLValue(COMPILE_CONTEXT * aCTX, AvmBytecode & argCode,
			const BF & arg, bool needTypeChecking = true);

	void setArgcodeLValueRef(COMPILE_CONTEXT * aCTX, AvmBytecode & argCode,
			const BF & arg, bool needTypeChecking = true);

	void setArgcodeLValueMacro(COMPILE_CONTEXT * aCTX, AvmBytecode & argCode,
			const BF & arg, bool needTypeChecking = true);


	void setArgcodeRValue(COMPILE_CONTEXT * aCTX, AvmBytecode & argCode,
			BF & arg, bool needTypeChecking = true);

	AvmBytecode argcodeOfExpression(COMPILE_CONTEXT * aCTX, AvmCode * aCode);


	void setArgcodeRValueArray(COMPILE_CONTEXT * aCTX, AvmBytecode & argCode,
			BF & arg, bool needTypeChecking = true);

	void setArgcodeRValueArray(COMPILE_CONTEXT * aCTX, AvmBytecode & argCode,
			ArrayBF * arg, bool needTypeChecking = true);

	inline void setArgcodeParamValue(COMPILE_CONTEXT * aCTX,
			AvmBytecode & argCode, BF & arg,
			bool needTypeChecking = true)
	{
		setArgcodeRValue(aCTX, argCode, arg, needTypeChecking);
		argCode.context = AVM_ARG_PARAMETER_CTX;
	}


	void setArgcodeContainerWValue(COMPILE_CONTEXT * aCTX,
			AvmBytecode & argCode, const BF & arg);

	void setArgcodeContainerRValue(COMPILE_CONTEXT * aCTX,
			AvmBytecode & argCode, const BF & arg);

	void setArgcodeStatement(COMPILE_CONTEXT * aCTX, AvmBytecode & argCode,
			const BF & arg, bool needTypeChecking = true);

	ExecutableForm * getExecutableMachine(COMPILE_CONTEXT * aCTX, const BF & arg);

	void checkArgType(COMPILE_CONTEXT * aCTX,
			BaseTypeSpecifier * aType, const BF & arg);


protected:
	/**
	 * ATTRIBUTES
	 */
	AvmcodeCompiler & AVMCODE_COMPILER;


};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Macro for smart avmcode compiler declaration.
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

#define AVMCODE_BASECOMPILER_CLASS_HEADER(classname, supername)                \
class classname :  public supername                                            \
{                                                                              \
public:                                                                        \
	classname(AvmcodeCompiler & aCompiler)                                     \
	: supername( aCompiler )                                                   \
	{ /*!! NOTHING !!*/ }                                                      \
	virtual ~classname()                                                       \
	{ /*!! NOTHING !!*/ }



/**
 * Macro for smart avmcode compiler declaration.
 */

#define AVMCODE_COMPILER_CLASS_HEADER(classname, supername)                    \
AVMCODE_BASECOMPILER_CLASS_HEADER(Avmcode##classname##Compiler, supername)     \
	virtual BF compileExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode);\
	virtual BFCode compileStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode);

#define AVMCODE_COMPILER_CLASS(classname, supername)                           \
		AVMCODE_COMPILER_CLASS_HEADER(classname, supername)                    \
};



#define AVMCODE_COMPILER_EXPRESSION_CLASS_HEADER(name, classname, supername)   \
AVMCODE_BASECOMPILER_CLASS_HEADER(Avmcode##classname##Compiler, supername)     \
	virtual BF compileExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode);\
	BFCode compileStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode)      \
	{ \
		AVM_OS_FATAL_ERROR_EXIT << "Unexpected << " << name       \
				<< " >> EXPRESSION as statement compilation !!!"  \
				<< SEND_EXIT;  \
		return( aCode ); \
	}

#define AVMCODE_COMPILER_EXPRESSION_CLASS(name, classname, supername)          \
		AVMCODE_COMPILER_EXPRESSION_CLASS_HEADER(name, classname, supername)   \
};


#define AVMCODE_COMPILER_STATEMENT_CLASS_HEADER(name, classname, supername)    \
AVMCODE_BASECOMPILER_CLASS_HEADER(Avmcode##classname##Compiler, supername)     \
	BF compileExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode)         \
	{ \
		AVM_OS_FATAL_ERROR_EXIT << "Unexpected << " << name    \
				<< " STATEMENT as expression compilation !!!"  \
				<< SEND_EXIT; \
		return( aCode ); \
	} \
	virtual BFCode compileStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode);

#define AVMCODE_COMPILER_STATEMENT_CLASS(name, classname, supername)           \
		AVMCODE_COMPILER_STATEMENT_CLASS_HEADER(name, classname, supername)    \
};



#define AVMCODE_COMPILER_OPTIMIZER_CLASS_HEADER(classname, supername)          \
AVMCODE_BASECOMPILER_CLASS_HEADER(Avmcode##classname##Compiler, supername)     \
	virtual BF compileExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode);\
	virtual BF optimizeExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode); \
	virtual BFCode compileStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode); \
	virtual BFCode optimizeStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode);


#define AVMCODE_COMPILER_OPTIMIZER_CLASS(classname, supername)                 \
	AVMCODE_COMPILER_OPTIMIZER_CLASS_HEADER(classname, supername)              \
};



#define AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS_HEADER(name, classname, supername) \
AVMCODE_BASECOMPILER_CLASS_HEADER(Avmcode##classname##Compiler, supername)     \
	virtual BF compileExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode);\
	virtual BF optimizeExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode); \
	BFCode compileStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode)      \
	{ \
		AVM_OS_FATAL_ERROR_EXIT << "Unexpected << " << name       \
				<< " >> EXPRESSION as statement compilation !!!"  \
				<< SEND_EXIT; \
		return( aCode ); \
	} \
	BFCode optimizeStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode)     \
	{ \
		AVM_OS_FATAL_ERROR_EXIT << "Unexpected << " << name        \
				<< " >> EXPRESSION as statement optimization !!!"  \
				<< SEND_EXIT; \
		return( aCode ); \
	}

#define AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS(name, classname, supername) \
		AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS_HEADER(name, classname, supername) \
};


#define AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS_HEADER(name, classname, supername) \
AVMCODE_BASECOMPILER_CLASS_HEADER(Avmcode##classname##Compiler, supername)     \
	BF compileExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode)         \
	{ \
		AVM_OS_FATAL_ERROR_EXIT << "Unexpected << " << name       \
				<< " >> STATEMENT as expression compilation !!!"  \
				<< SEND_EXIT; \
		return( aCode ); \
	} \
	BF optimizeExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode)        \
	{ \
		AVM_OS_FATAL_ERROR_EXIT << "Unexpected << " << name        \
				<< " >> STATEMENT as expression optimization !!!"  \
				<< SEND_EXIT; \
		return( aCode ); \
	} \
	virtual BFCode compileStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode); \
	virtual BFCode optimizeStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode);

#define AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(name, classname, supername) \
		AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS_HEADER(name, classname, supername) \
};




#define AVMCODE_COMPILER_NO_OPTIMIZER_CLASS_HEADER(name, classname, supername) \
AVMCODE_BASECOMPILER_CLASS_HEADER(Avmcode##classname##Compiler, supername)     \
	BF compileExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode);        \
	BF optimizeExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode)        \
	{ \
		AVM_OS_FATAL_ERROR_EXIT << "Unexpected invoke of " << name  \
				<< " >> STATEMENT as expression optimization !!!"   \
				<< SEND_EXIT; \
		return( aCode ); \
	} \
	virtual BFCode compileStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode); \
	virtual BFCode optimizeStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode) \
	{ \
		AVM_OS_FATAL_ERROR_EXIT << "Unexpected invoke of " << name  \
				<< " >> EXPRESSION as statement optimization !!!"   \
				<< SEND_EXIT; \
		return( aCode ); \
	} \

#define AVMCODE_COMPILER_NO_OPTIMIZER_CLASS(name, classname, supername)        \
		AVMCODE_COMPILER_NO_OPTIMIZER_CLASS_HEADER(name, classname, supername) \
};





/**
 * Macro for smart avmcode compiler declaration.
 *
#define AVMCODE_COMPILER_EXPRESSION_CLASS_HEADER(classname, supername)         \
AVMCODE_BASECOMPILER_CLASS_HEADER(Avmcode##classname##Compiler, supername)     \
	virtual BF compileExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode);


#define AVMCODE_COMPILER_EXPRESSION_CLASS(classname, supername)                \
AVMCODE_COMPILER_EXPRESSION_CLASS_HEADER(classname, supername)                 \
};
*/

/**
 * Macro for smart avmcode compiler declaration.
 *
#define AVMCODE_COMPILER_STATEMENT_CLASS_HEADER(classname, supername)          \
AVMCODE_BASECOMPILER_CLASS_HEADER(Avmcode##classname##Compiler, supername)     \
	virtual BFCode compileStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode);


#define AVMCODE_COMPILER_STATEMENT_CLASS(classname, supername)                 \
AVMCODE_COMPILER_STATEMENT_CLASS_HEADER(classname, supername)                  \
};
*/


}

#endif /* ABSTRACTAVMCODECOMPILER_H_ */

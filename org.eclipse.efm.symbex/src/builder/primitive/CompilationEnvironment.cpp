/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 14 févr. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "CompilationEnvironment.h"

#include <fml/executable/ExecutableLib.h>


namespace sep
{


/**
 * STATIC
 * ATTRIBUTES
 */
bool COMPILE_CONTEXT::DEFAUL_TYPE_CHECKING_MASK = true;

bool COMPILE_CONTEXT::INLINE_DISABLE_MASK = false;

bool COMPILE_CONTEXT::INLINE_ENABLE_MASK = false;

bool COMPILE_CONTEXT::INLINE_PROCEDURE_MASK = true;


/**
 * Runtime Executable Context
 */
ExecutableForm * COMPILE_CONTEXT::getRuntimeExecutableCxt(
		const InstanceOfData & aConsVarInstance)
{
	if( mRuntimeCtx != nullptr )
	{
		if( ExecutableLib::MACHINE_THIS == aConsVarInstance )
		{
			return( mRuntimeCtx );
		}
		else if( ExecutableLib::MACHINE_SELF == aConsVarInstance )
		{
			return( mRuntimeCtx );
		}
		else if( ExecutableLib::MACHINE_PARENT == aConsVarInstance )
		{
			return( mRuntimeCtx->getExecutableContainer() );
		}
		else if( ExecutableLib::MACHINE_COMMUNICATOR == aConsVarInstance )
		{
			return( mRuntimeCtx->getExcutableCommunicator() );
		}

		else if( ExecutableLib::MACHINE_SYSTEM == aConsVarInstance )
		{
			return( mRuntimeCtx->getExcutableSystem() );
		}

//		else if( ExecutableLib::MACHINE_COMPONENT_SELF == aConsVarInstance )
//		{
//			return( mRuntimeCtx );
//		}
//		else if( ExecutableLib::MACHINE_COMPONENT_PARENT == aConsVarInstance )
//		{
//			return( mRuntimeCtx );
//		}
//		else if( ExecutableLib::MACHINE_COMPONENT_COMMUNICATOR
//				== aConsVarInstance )
//		{
//			return( mRuntimeCtx );
//		}
//
//		else if( ExecutableLib::MACHINE_ENVIRONMENT == aConsVarInstance )
//		{
//			return( nullptr );
//		}
	}

	return( nullptr );
}

/**
 * report debug Context
 */
OutStream & COMPILE_CONTEXT::debugContext(OutStream & os)
{
	os << TAB << "Context:> "
			<< mCompileCtx->getFullyQualifiedNameID() << std::endl;

	if( isSpecificRuntimeCtx() )
	{
		os << TAB << "Runtime:> "
				<< mRuntimeCtx->getFullyQualifiedNameID() << std::endl;
	}

	if( mVariableCtx != nullptr )
	{
		os << TAB << "DataVar:> "
				<< mVariableCtx->getFullyQualifiedNameID() << std::endl;
	}

	return( os );
}


/**
 * report error Context & Location
 */
OutStream & COMPILE_CONTEXT::errorContext(OutStream & os)
{
AVM_IF_DEBUG_FLAG( COMPILING )
	os << "ctx:> " << mCompileCtx->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	BaseAvmProgram * errorCtx =
			( mCompileCtx == mRuntimeCtx )? mCompileCtx : mRuntimeCtx;
	errorCtx->getAstElement().errorLocation(os,
			errorCtx->hasContainer() ?
					&( errorCtx->getContainer()->getAstElement() ) : nullptr);

	return( os );
}

PairOutStream & COMPILE_CONTEXT::errorContext(PairOutStream & os)
{
AVM_IF_DEBUG_FLAG( COMPILING )
	os << "ctx:> " << mCompileCtx->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	BaseAvmProgram * errorCtx =
			( mCompileCtx == mRuntimeCtx )? mCompileCtx : mRuntimeCtx;
	errorCtx->getAstElement().errorLocation(os,
			errorCtx->hasContainer() ?
					&( errorCtx->getContainer()->getAstElement() ) : nullptr);

	return( os );
}

TripleOutStream & COMPILE_CONTEXT::errorContext(TripleOutStream & os)
{
AVM_IF_DEBUG_FLAG( COMPILING )
	os << "ctx:> " << mCompileCtx->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	BaseAvmProgram * errorCtx =
			( mCompileCtx == mRuntimeCtx )? mCompileCtx : mRuntimeCtx;
	errorCtx->getAstElement().errorLocation(os,
			errorCtx->hasContainer() ?
					&( errorCtx->getContainer()->getAstElement() ) : nullptr);

	return( os );
}


/**
 * report warning Context & Location
 */
OutStream & COMPILE_CONTEXT::warningContext(OutStream & os)
{
AVM_IF_DEBUG_FLAG( COMPILING )
	os << "ctx:> " << mCompileCtx->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	BaseAvmProgram * warningCtx =
			( mCompileCtx == mRuntimeCtx )? mCompileCtx : mRuntimeCtx;
	warningCtx->getAstElement().warningLocation(os,
			warningCtx->hasContainer() ?
					&( warningCtx->getContainer()->getAstElement() ) : nullptr);

	return( os );
}

PairOutStream & COMPILE_CONTEXT::warningContext(PairOutStream & os)
{
AVM_IF_DEBUG_FLAG( COMPILING )
	os << "ctx:> " << mCompileCtx->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	BaseAvmProgram * warningCtx =
			( mCompileCtx == mRuntimeCtx )? mCompileCtx : mRuntimeCtx;
	warningCtx->getAstElement().warningLocation(os,
			warningCtx->hasContainer() ?
					&( warningCtx->getContainer()->getAstElement() ) : nullptr);

	return( os );
}

TripleOutStream & COMPILE_CONTEXT::warningContext(TripleOutStream & os)
{
AVM_IF_DEBUG_FLAG( COMPILING )
	os << "ctx:> " << mCompileCtx->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	BaseAvmProgram * warningCtx =
			( mCompileCtx == mRuntimeCtx )? mCompileCtx : mRuntimeCtx;
	warningCtx->getAstElement().warningLocation(os,
			warningCtx->hasContainer() ?
					&( warningCtx->getContainer()->getAstElement() ) : nullptr);

	return( os );
}


/**
 * Serialization
 */
void COMPILE_CONTEXT::strHeader(OutStream & os) const
{
	os << TAB << ( hasModifier() ? getModifier().toString() : "" )
			<< "COMPILER< ctx: " << mCompileCtx->getFullyQualifiedNameID();
	if( mCompileCtx != mRuntimeCtx )
	{
		os << " , run: " << mRuntimeCtx->getFullyQualifiedNameID();
	}
	if( (mType != nullptr) && (mType != TypeManager::UNIVERSAL) )
	{
		os << " , type " << ( mNeedTypeChecking ? "?:" : ":" )
				<< str_header( mType );
	}
	os << " >";
}


void COMPILE_CONTEXT::toStream(OutStream & os) const
{
	os << TAB << ( hasModifier() ? getModifier().toString() : "" )
			<< "compiler {" << EOL
			<< TAB2 << "context = " << str_header( mCompileCtx ) << EOL
			<< TAB2 << "runtime = " << str_header( mRuntimeCtx ) << EOL;

	if( mType != nullptr )
	{
		os << TAB2 << ( mNeedTypeChecking ? "check_" : "" )
				<< "type = " << str_header( mType ) << EOL;
	}

	os << TAB << "}" << EOL;
}



///////////////////////////////////////////////////////////////////////////
// CACHE MANAGER
///////////////////////////////////////////////////////////////////////////

List< COMPILE_CONTEXT * > CompilationEnvironment::COMPILE_CONTEXT_CACHE;


void CompilationEnvironment::initCache()
{
	for( std::size_t i = 0 ; i < COMPILE_CONTEXT_INITIAL_COUNT ; ++i )
	{
		COMPILE_CONTEXT_CACHE.append(
				new COMPILE_CONTEXT(nullptr, nullptr, nullptr, nullptr) );
	}
}

void CompilationEnvironment::finalizeCache()
{
	std::size_t finalCacheSize = 0;

	while( COMPILE_CONTEXT_CACHE.nonempty() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPILING , MEMORY_MANAGEMENT )
		AVM_OS_TRACE << "COMPILE_CONTEXT::finalize:> @"
				<< std::addressof( COMPILE_CONTEXT_CACHE.last() ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPILING , MEMORY_MANAGEMENT )

		++finalCacheSize;
		delete( COMPILE_CONTEXT_CACHE.pop_last() );
	}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPILING , MEMORY_MANAGEMENT )
	AVM_OS_TRACE << "COMPILE_CONTEXT::finalize#cache:> count = "
			<< finalCacheSize << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPILING , MEMORY_MANAGEMENT )
}



COMPILE_CONTEXT * CompilationEnvironment::newCTX(COMPILE_CONTEXT * PREV,
		BaseAvmProgram * aCompileCtx, ExecutableForm * aRuntimeCtx,
		InstanceOfData * aVariableCtx, const BaseTypeSpecifier * aType,
		bool needTypeChecking, const Modifier & aModifier)
{
	COMPILE_CONTEXT * newCTX = nullptr;

	if( COMPILE_CONTEXT_CACHE.nonempty() )
	{
		COMPILE_CONTEXT_CACHE.pop_last_to( newCTX );

		newCTX->PREV = PREV;

		// Used for safe memory management !!!
		if( PREV != nullptr )
		{
			newCTX->NEXT = PREV->NEXT;
			PREV->NEXT   = newCTX;
		}
		else
		{
			newCTX->NEXT = nullptr;
		}

		newCTX->mCompileCtx  = aCompileCtx;
		newCTX->mRuntimeCtx  = aRuntimeCtx;
		newCTX->mVariableCtx = aVariableCtx;

		newCTX->mType = aType;
		newCTX->mNeedTypeChecking = needTypeChecking;

		newCTX->setModifier( aModifier );
	}
	else
	{
		newCTX = new COMPILE_CONTEXT(PREV,
				aCompileCtx, aRuntimeCtx, aVariableCtx, aType, aModifier);

		AVM_OS_ASSERT_OUT_OF_MEMORY_EXIT( newCTX )
				<< "CompilationEnvironment::newCTX !!!"
				<< SEND_EXIT;
	}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPILING , MEMORY_MANAGEMENT )
	AVM_OS_TRACE << "COMPILE_CONTEXT::new:> @" << std::addressof( newCTX )
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPILING , MEMORY_MANAGEMENT )

	return( newCTX );
}


void CompilationEnvironment::freeCTX(COMPILE_CONTEXT * & CTX)
{
	if( CTX->NEXT == nullptr )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPILING , MEMORY_MANAGEMENT )
		AVM_OS_TRACE << "COMPILE_CONTEXT::free:> @"
				<< std::addressof( CTX ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPILING , MEMORY_MANAGEMENT )
		COMPILE_CONTEXT_CACHE.append( CTX );

		CTX = nullptr;
	}
	else
	{
		for( COMPILE_CONTEXT * nextCTX = CTX ; CTX != nullptr ; CTX = nextCTX )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPILING , MEMORY_MANAGEMENT )
			AVM_OS_TRACE << "COMPILE_CONTEXT::free:> @"
					<< std::addressof( CTX ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPILING , MEMORY_MANAGEMENT )

			nextCTX = CTX->NEXT;
//			CTX->NEXT = nullptr;
			COMPILE_CONTEXT_CACHE.append( CTX );
		}
	}
}



} /* namespace sep */

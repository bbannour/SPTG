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

	if( mVariableCtx != NULL )
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
	errorCtx->getAstElement()->errorLocation(os,
			errorCtx->hasContainer() ?
					errorCtx->getContainer()->getAstElement() : NULL);

	return( os );
}

PairOutStream & COMPILE_CONTEXT::errorContext(PairOutStream & os)
{
AVM_IF_DEBUG_FLAG( COMPILING )
	os << "ctx:> " << mCompileCtx->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	BaseAvmProgram * errorCtx =
			( mCompileCtx == mRuntimeCtx )? mCompileCtx : mRuntimeCtx;
	errorCtx->getAstElement()->errorLocation(os,
			errorCtx->hasContainer() ?
					errorCtx->getContainer()->getAstElement() : NULL);

	return( os );
}

TripleOutStream & COMPILE_CONTEXT::errorContext(TripleOutStream & os)
{
AVM_IF_DEBUG_FLAG( COMPILING )
	os << "ctx:> " << mCompileCtx->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	BaseAvmProgram * errorCtx =
			( mCompileCtx == mRuntimeCtx )? mCompileCtx : mRuntimeCtx;
	errorCtx->getAstElement()->errorLocation(os,
			errorCtx->hasContainer() ?
					errorCtx->getContainer()->getAstElement() : NULL);

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
	warningCtx->getAstElement()->warningLocation(os,
			warningCtx->hasContainer() ?
					warningCtx->getContainer()->getAstElement() : NULL);

	return( os );
}

PairOutStream & COMPILE_CONTEXT::warningContext(PairOutStream & os)
{
AVM_IF_DEBUG_FLAG( COMPILING )
	os << "ctx:> " << mCompileCtx->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	BaseAvmProgram * warningCtx =
			( mCompileCtx == mRuntimeCtx )? mCompileCtx : mRuntimeCtx;
	warningCtx->getAstElement()->warningLocation(os,
			warningCtx->hasContainer() ?
					warningCtx->getContainer()->getAstElement() : NULL);

	return( os );
}

TripleOutStream & COMPILE_CONTEXT::warningContext(TripleOutStream & os)
{
AVM_IF_DEBUG_FLAG( COMPILING )
	os << "ctx:> " << mCompileCtx->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	BaseAvmProgram * warningCtx =
			( mCompileCtx == mRuntimeCtx )? mCompileCtx : mRuntimeCtx;
	warningCtx->getAstElement()->warningLocation(os,
			warningCtx->hasContainer() ?
					warningCtx->getContainer()->getAstElement() : NULL);

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
	if( (mType != NULL) && (mType != TypeManager::UNIVERSAL) )
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

	if( mType != NULL )
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
	for( avm_size_t i = 0 ; i < COMPILE_CONTEXT_INITIAL_COUNT ; ++i )
	{
		COMPILE_CONTEXT_CACHE.append(
				new COMPILE_CONTEXT(NULL, NULL, NULL, NULL) );
	}
}

void CompilationEnvironment::finalizeCache()
{
	avm_size_t finalCacheSize = 0;

	while( COMPILE_CONTEXT_CACHE.nonempty() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
		AVM_OS_TRACE << "COMPILE_CONTEXT::finalize:> @"
				<< avm_address_t( COMPILE_CONTEXT_CACHE.last() ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )

		++finalCacheSize;
		delete( COMPILE_CONTEXT_CACHE.pop_last() );
	}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << "COMPILE_CONTEXT::finalize#cache:> count = "
			<< finalCacheSize << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
}



COMPILE_CONTEXT * CompilationEnvironment::newCTX(COMPILE_CONTEXT * PREV,
		BaseAvmProgram * aCompileCtx, ExecutableForm * aRuntimeCtx,
		InstanceOfData * aVariableCtx, BaseTypeSpecifier * aType,
		bool needTypeChecking, const Modifier & aModifier)
{
	COMPILE_CONTEXT * newCTX = NULL;

	if( COMPILE_CONTEXT_CACHE.nonempty() )
	{
		COMPILE_CONTEXT_CACHE.pop_last_to( newCTX );

		newCTX->PREV = PREV;

		// Used for safe memory management !!!
		if( PREV != NULL )
		{
			newCTX->NEXT = PREV->NEXT;
			PREV->NEXT   = newCTX;
		}
		else
		{
			newCTX->NEXT = NULL;
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

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << "COMPILE_CONTEXT::new:> @" << avm_address_t( newCTX )
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )

	return( newCTX );
}


void CompilationEnvironment::freeCTX(COMPILE_CONTEXT * & CTX)
{
	if( CTX->NEXT == NULL )
	{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
		AVM_OS_TRACE << "COMPILE_CONTEXT::free:> @"
				<< avm_address_t( CTX ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
		COMPILE_CONTEXT_CACHE.append( CTX );

		CTX = NULL;
	}
	else
	{
		for( COMPILE_CONTEXT * nextCTX = CTX ; CTX != NULL ; CTX = nextCTX )
		{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
			AVM_OS_TRACE << "COMPILE_CONTEXT::free:> @"
					<< avm_address_t( CTX ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )

			nextCTX = CTX->NEXT;
//			CTX->NEXT = NULL;
			COMPILE_CONTEXT_CACHE.append( CTX );
		}
	}
}



} /* namespace sep */

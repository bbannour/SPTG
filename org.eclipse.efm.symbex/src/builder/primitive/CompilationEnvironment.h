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

#ifndef COMPILATIONENVIRONMENT_H_
#define COMPILATIONENVIRONMENT_H_

#include <common/BF.h>

#include <fml/expression/AvmCode.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/BaseAvmProgram.h>
#include <fml/executable/ExecutableForm.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/TypeManager.h>

#include <fml/infrastructure/Machine.h>

#include <collection/List.h>


#define COMPILE_CONTEXT_INITIAL_COUNT     16


namespace sep
{

class BaseAvmProgram;
class ExecutableForm;
class InstanceOfData;

class COMPILE_CONTEXT;


class CompilationEnvironment
{
public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	CompilationEnvironment(COMPILE_CONTEXT * aCTX,
			BaseAvmProgram * aCompileCtx, ExecutableForm * aRuntimeCtx)
	: mCTX( newCTX(aCTX, aCompileCtx, aRuntimeCtx) )
	{
		//!! NOTHING
	}

//	CompilationEnvironment(COMPILE_CONTEXT * aCTX, BaseAvmProgram * aCompileCtx)
//	: mCTX( newCTX(aCTX, aCompileCtx, aCompileCtx->getExecutable()) )
//	{
//		//!! NOTHING
//	}

	CompilationEnvironment(COMPILE_CONTEXT * aCTX, ExecutableForm * aCompileCtx)
	: mCTX( newCTX(aCTX, aCompileCtx, aCompileCtx) )
	{
		//!! NOTHING
	}


	CompilationEnvironment(AvmProgram & aCompileCtx,
			InstanceOfData * aVariableCtx = nullptr)
	: mCTX( newCTX(nullptr, (& aCompileCtx),
			aCompileCtx.getExecutable(), aVariableCtx) )
	{
		//!! NOTHING
	}

	CompilationEnvironment(AvmProgram * aCompileCtx,
			InstanceOfData * aVariableCtx = nullptr)
	: mCTX( newCTX(nullptr, aCompileCtx,
			aCompileCtx->getExecutable(), aVariableCtx) )
	{
		//!! NOTHING
	}


	CompilationEnvironment(ExecutableForm & aCompileCtx)
	: mCTX( newCTX(nullptr, & aCompileCtx, & aCompileCtx) )
	{
		//!! NOTHING
	}

	CompilationEnvironment(ExecutableForm * aCompileCtx)
	: mCTX( newCTX(nullptr, aCompileCtx, aCompileCtx) )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~CompilationEnvironment()
	{
		freeCTX( mCTX );
	}



public:
	/*ATTRIBUTES*/

	COMPILE_CONTEXT * mCTX;


	///////////////////////////////////////////////////////////////////////////
	// CACHE MANAGER
	///////////////////////////////////////////////////////////////////////////
	static List< COMPILE_CONTEXT * >  COMPILE_CONTEXT_CACHE;

	static void initCache();

	static void finalizeCache();


	static COMPILE_CONTEXT * newCTX(COMPILE_CONTEXT * PREV,
			BaseAvmProgram * aCompileCtx, ExecutableForm * aRuntimeCtx,
			InstanceOfData * aVariableCtx = nullptr,
			const BaseTypeSpecifier * aType = TypeManager::UNIVERSAL,
			bool needTypeChecking = true,
			const Modifier & aModifier = Modifier::PROPERTY_UNDEFINED_MODIFIER);


	static void freeCTX(COMPILE_CONTEXT * & CTX);

};



struct COMPILE_CONTEXT  :  public ModifierImpl
{

public:
	/**
	 * STATIC
	 * ATTRIBUTES
	 */
	static bool DEFAUL_TYPE_CHECKING_MASK;

	static bool INLINE_DISABLE_MASK;

	static bool INLINE_ENABLE_MASK;

	static bool INLINE_PROCEDURE_MASK;

	/**
	 * ATTRIBUTES
	 */
	COMPILE_CONTEXT * PREV;
	COMPILE_CONTEXT * NEXT;

	BaseAvmProgram * mCompileCtx;
	ExecutableForm * mRuntimeCtx;

	InstanceOfData * mVariableCtx;

	const BaseTypeSpecifier * mType;

	bool mNeedTypeChecking;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	COMPILE_CONTEXT(COMPILE_CONTEXT * aCTX, BaseAvmProgram * aCompileCtx,
			ExecutableForm * aRuntimeCtx, InstanceOfData * aVariableCtx,
			const BaseTypeSpecifier * aType = TypeManager::UNIVERSAL,
			const Modifier & aModifier = Modifier::PROPERTY_UNDEFINED_MODIFIER)
	: ModifierImpl( aModifier ),
	PREV( aCTX ), NEXT( nullptr ),

	mCompileCtx ( aCompileCtx  ),
	mRuntimeCtx ( aRuntimeCtx  ),
	mVariableCtx( aVariableCtx ),

	mType( aType ),
	mNeedTypeChecking( true )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~COMPILE_CONTEXT()
	{
		//!! NOTHING
	}


	inline COMPILE_CONTEXT * newCTX(BaseAvmProgram * aCompileCtx,
			ExecutableForm * aRuntimeCtx,
			InstanceOfData * aVariableCtx = nullptr)
	{
		return( CompilationEnvironment::newCTX(this,
				aCompileCtx, aRuntimeCtx, aVariableCtx,
				mType, mNeedTypeChecking, getModifier()) );
	}

	inline COMPILE_CONTEXT * newCTX(BaseAvmProgram * aCompileCtx)
	{
		return( CompilationEnvironment::newCTX(this,
				aCompileCtx, aCompileCtx->getExecutable(), mVariableCtx,
				mType, mNeedTypeChecking, getModifier()) );
	}

	inline COMPILE_CONTEXT * newCompileCTX(BaseAvmProgram * aCompileCtx)
	{
		return( CompilationEnvironment::newCTX(this,
				aCompileCtx, mRuntimeCtx, mVariableCtx,
				mType, mNeedTypeChecking, getModifier()) );
	}


	inline COMPILE_CONTEXT * newCTX(ExecutableForm * aRuntimeCtx)
	{
		return( CompilationEnvironment::newCTX(this,
				mCompileCtx, aRuntimeCtx, mVariableCtx,
				mType, mNeedTypeChecking, getModifier()) );
	}


	inline COMPILE_CONTEXT * newCTX(ExecutableForm * aRuntimeCtx,
			const Modifier & aModifier)
	{
		return( CompilationEnvironment::newCTX(this,
				mCompileCtx, aRuntimeCtx, mVariableCtx,
				mType, mNeedTypeChecking, aModifier) );
	}

	inline COMPILE_CONTEXT * newCTX(const Modifier & aModifier)
	{
		return( CompilationEnvironment::newCTX(this,
				mCompileCtx, mRuntimeCtx, mVariableCtx,
				mType, mNeedTypeChecking, aModifier) );
	}


	inline COMPILE_CONTEXT * clone()
	{
		return( CompilationEnvironment::newCTX(this,
				mCompileCtx, mRuntimeCtx, mVariableCtx,
				mType, mNeedTypeChecking, getModifier()) );
	}

	inline COMPILE_CONTEXT * clone(const TypeSpecifier & aType)
	{
		return( CompilationEnvironment::newCTX(this, mCompileCtx, mRuntimeCtx,
				mVariableCtx, aType, mNeedTypeChecking, getModifier()) );
	}

	inline COMPILE_CONTEXT * clone(const BaseTypeSpecifier & aType)
	{
		return( CompilationEnvironment::newCTX(this,
				mCompileCtx, mRuntimeCtx, mVariableCtx,
				(& aType), mNeedTypeChecking, getModifier()) );
	}


	/**
	 * mType
	 */
	inline bool hasType() const
	{
		return( (mType != nullptr) && (mType != TypeManager::UNIVERSAL) );
	}


	inline avm_type_specifier_kind_t getTypeFamily() const
	{
		return( ( mType != nullptr ) ?
				mType->getTypeSpecifierKind() : TYPE_UNDEFINED_SPECIFIER );
	}


	inline bool typeMustBeMachineFamily() const
	{
		return( (mType == nullptr)
				|| mType->hasTypeSpecifierKind(TYPE_MACHINE_SPECIFIER,
						TYPE_UNIVERSAL_SPECIFIER, TYPE_UNDEFINED_SPECIFIER) );
	}

	inline bool typeMustBePortFamily() const
	{
		return( (mType == nullptr)
				|| mType->hasTypeSpecifierKind(TYPE_PORT_SPECIFIER,
						TYPE_SIGNAL_SPECIFIER,TYPE_MESSAGE_SPECIFIER)
				|| mType->hasTypeSpecifierKind(TYPE_UNIVERSAL_SPECIFIER,
						TYPE_UNDEFINED_SPECIFIER) );
	}

	inline bool typeMustBeChannelFamily() const
	{
		return( (mType == nullptr)
				|| mType->hasTypeSpecifierKind(TYPE_CHANNEL_SPECIFIER,
						TYPE_UNIVERSAL_SPECIFIER, TYPE_UNDEFINED_SPECIFIER) );
	}

	inline bool typeMustBeBufferFamily() const
	{
		return( (mType == nullptr)
				|| mType->hasTypeSpecifierKind(TYPE_BUFFER_SPECIFIER,
						TYPE_UNIVERSAL_SPECIFIER, TYPE_UNDEFINED_SPECIFIER) );
	}

	inline bool typeMustBeConnectorFamily() const
	{
		return( (mType == nullptr)
				|| mType->hasTypeSpecifierKind(TYPE_CONNECTOR_SPECIFIER,
						TYPE_UNIVERSAL_SPECIFIER, TYPE_UNDEFINED_SPECIFIER) );
	}


	inline bool typeCouldBeOherFamily() const
	{
		if( mType != nullptr )
		{
			switch( mType->getTypeSpecifierKind() )
			{
				case TYPE_MACHINE_SPECIFIER:
				case TYPE_PORT_SPECIFIER:
				case TYPE_SIGNAL_SPECIFIER:
				case TYPE_MESSAGE_SPECIFIER:
				case TYPE_CHANNEL_SPECIFIER:
				case TYPE_BUFFER_SPECIFIER:
				case TYPE_CONNECTOR_SPECIFIER:
					return( false );

				default:
					return( true );
			}
		}

		return( true );
	}

	inline bool typeCouldBeTypeSpecifierFamily() const
	{
		return( typeCouldBeOherFamily() );
	}

	inline bool typeCouldBeTransitionFamily() const
	{
		return( typeCouldBeOherFamily() );
	}

	inline bool typeCouldBeGenericProgramFamily() const
	{
		return( typeCouldBeOherFamily() );
	}



	/**
	 * mNeedTypeChecking
	 */
	inline bool isStrongNeedTypeChecking(bool localTypeCheckingMask = true ) const
	{
		return( localTypeCheckingMask
				&& DEFAUL_TYPE_CHECKING_MASK
				&& mNeedTypeChecking );
	}

	inline bool isWeakNeedTypeChecking(bool localTypeCheckingMask = true ) const
	{
		return( DEFAUL_TYPE_CHECKING_MASK
				&& (localTypeCheckingMask
					|| mNeedTypeChecking) );
	}

	inline bool isNeedTypeChecking(bool localTypeCheckingMask = true ) const
	{
		return( isStrongNeedTypeChecking(localTypeCheckingMask) );
	}


	/**
	 * mCompileCtx
	 */
	inline bool isCompileTransitionCtx()
	{
		return( mCompileCtx->is< AvmTransition >() );
	}

	inline bool isInlineEnable(ExecutableForm * anExecutable)
	{
		return( INLINE_ENABLE_MASK
				&& isCompileTransitionCtx()
				&& anExecutable->isInlinableEnable() );
	}


	inline bool isInlineProcedure(ExecutableForm * anExecutable)
	{
		return( INLINE_PROCEDURE_MASK
				&& isCompileTransitionCtx()
				&& anExecutable->isInlinableProcedure() );
	}

	/**
	 * mCompileCtx
	 */
	inline bool isSpecificRuntimeCtx()
	{
		return( (mRuntimeCtx != mCompileCtx)
				&& (mRuntimeCtx != mCompileCtx->getContainer()) );
	}


	/**
	 * Runtime Executable Context
	 */
	ExecutableForm * getRuntimeExecutableCxt(
			const InstanceOfData & aConsVarInstance);

	/**
	 * report debug Context
	 */
	OutStream & debugContext(OutStream & os);

	/**
	 * report error Context & Location
	 */
	OutStream & errorContext(OutStream & os);
	PairOutStream & errorContext(PairOutStream & os);
	TripleOutStream & errorContext(TripleOutStream & os);

	OutStream & warningContext(OutStream & os);
	PairOutStream & warningContext(PairOutStream & os);
	TripleOutStream & warningContext(TripleOutStream & os);

	/**
	 * Serialization
	 */
	virtual void strHeader(OutStream & os) const;

	virtual void toStream(OutStream & os) const;

};



} /* namespace sep */
#endif /* COMPILATIONENVIRONMENT_H_ */

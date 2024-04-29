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
#ifndef EXECUTABLESYSTEM_H_
#define EXECUTABLESYSTEM_H_

#include <fml/executable/BaseCompiledForm.h>

#include <collection/Typedef.h>

#include <fml/common/SpecifierElement.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/infrastructure/System.h>

#include <fml/symbol/Symbol.h>

#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>

#include <vector>



namespace sep
{


class AvmCode;

class ObjectElement;

class System;


class ExecutableSystem :
		public BaseCompiledForm ,
		AVM_INJECT_STATIC_NULL_REFERENCE( ExecutableSystem ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutableSystem )

{

	AVM_DECLARE_CLONABLE_CLASS( ExecutableSystem )

protected:
	/*
	 * ATTRIBUTES
	 */
	std::vector< ExecutableForm > mExecutableForms;

	TableOfExecutableForm mExecutables;

	ExecutableForm    mParametersExecutable;
	InstanceOfMachine mParametersInstance;

	Symbol mSystemInstance;

	ExecutableForm mDefaultProcessExecutableForm;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutableSystem(const System & astSystem)
	: BaseCompiledForm( CLASS_KIND_T( ExecutableSystem ) , nullptr, astSystem ),

	mExecutableForms( ),

	mExecutables( ),

	mParametersExecutable( *this, nullptr, astSystem, 0 ),
	mParametersInstance( nullptr, astSystem, mParametersExecutable, nullptr, 0 ),

	mSystemInstance( ),
	mDefaultProcessExecutableForm( (* this) , 0  )
	{
		mExecutableForms.reserve( 16 + astSystem.getExecutableMachineCount() );

		mParametersExecutable.incrPossibleStaticInstanciationCount(1);
		mParametersExecutable.setAllNameID("exec::#PARAMETERS#" , "#PARAMETERS#");

		mParametersInstance.setAllNameID("inst::#PARAMETERS#" , "#PARAMETERS#");

		updateFullyQualifiedNameID();
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutableSystem(const ExecutableSystem & anExecutable)
	: BaseCompiledForm( anExecutable ),

	mExecutableForms( anExecutable.mExecutableForms ),

	mExecutables( anExecutable.mExecutables ),

	mParametersExecutable( anExecutable.mParametersExecutable ),
	mParametersInstance( anExecutable.mParametersInstance ),

	mSystemInstance( anExecutable.mSystemInstance ),
	mDefaultProcessExecutableForm( anExecutable.mDefaultProcessExecutableForm )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutableSystem()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static ExecutableSystem & nullref()
	{
		static ExecutableSystem _NULL_( System::nullref() );
		_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );
//		_NULL_.setSpecifier( Specifier::OBJECT_NULL_SPECIFIER );

		return( _NULL_ );
	}


	/**
	 * SETTER
	 * updateFullyQualifiedNameID()
	 */
	virtual void updateFullyQualifiedNameID() override;


	/**
	 * GETTER  API
	 * Specifier
	 */
	const Specifier & getSpecifier() const
	{
		return( rawSystemInstance()->refExecutable().getSpecifier() );
	}


	/**
	 * GETTER
	 * Compiled ObjectElement as Compiled System
	 */
	inline const System & getAstSystem() const
	{
		return( safeAstElement().as< System >() );
	}

	/**
	 * FACTORY - GETTER
	 * mExecutableSystems
	 */
	template<typename... _Args>
	ExecutableForm & newExecutableForm( _Args && ... __args )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mExecutableForms.size() <
				getAstSystem().getExecutableMachineCount() )
				<< "Out Of Memory for Table of Executable !!!";

		return mExecutableForms.emplace_back( (* this), __args ... ) ;
	}

	inline std::vector< ExecutableForm > & getExecutableForms()
	{
		return( mExecutableForms );
	}


	/**
	 * GETTER
	 * TableOfExecutableForm
	 */
	inline const TableOfExecutableForm & getExecutables() const
	{
		return( mExecutables );
	}


	inline virtual std::size_t size() const override
	{
		return( mExecutables.size() );
	}


	/**
	 * GETTER - SETTER
	 * mExecutableForm
	 */
//	inline ExecutableForm & newExecutable(ExecutableForm * aContainer,
//			const ObjectElement * aCompiled, std::size_t aDataSize = 0)
//	{
//		mExecutables.push_front(
//				ExecutableForm(aContainer, aCompiled, aDataSize) );
//
//		ExecutableForm & newExec = mExecutables.front();
//
//		newExec.setOffset( size() - 1 );
//
//		return( newExec );
//	}

	inline const BF & saveExecutable(ExecutableForm * anExecutableForm)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anExecutableForm )
				<< "ExecutableForm !!!"
				<< SEND_EXIT;

		anExecutableForm->setOffset( mExecutables.size() );

		return( mExecutables.save( anExecutableForm ) );
	}


	/**
	 * GETTER - SETTER
	 * mParametersInstance
	 */
	inline const InstanceOfMachine * rawParametersInstance() const
	{
		return( & mParametersInstance );
	}

	inline InstanceOfMachine * rawParametersInstance()
	{
		return( & mParametersInstance );
	}


	/**
	 * GETTER - SETTER
	 * mSystemInstance
	 */
	inline InstanceOfMachine * rawSystemInstance() const
	{
		return( mSystemInstance.rawMachine() );
	}

	inline const Symbol & getSystemInstance() const
	{
		return( mSystemInstance );
	}

	inline bool hasSystemInstance() const
	{
		return( mSystemInstance.valid() );
	}

	inline const Symbol & setSystemInstance(InstanceOfMachine * anInstance)
	{
		mSystemInstance.renew( anInstance );

		return( mSystemInstance );
	}


	/**
	 * mDefaultProcessExecutableForm
	 */
	inline ExecutableForm & defaultExecutableForm()
	{
		return( mDefaultProcessExecutableForm );
	}

	/**
	 * NEW TMP EXECUTABLE
	 */
	inline void initProcessExecutableForm(
			ExecutableForm & anExecutableForm, std::size_t aDataSize = 0) const
	{
		anExecutableForm.init(
				rawSystemInstance()->getExecutable(), aDataSize);
	}


	/**
	 * GETTER - SETTER
	 * Machine Count
	 */
	inline std::size_t getMachineCount() const
	{
		return( rawSystemInstance()->refExecutable().getrecMachineCount() +1 );
	}


	/**
	 * Serialization
	 */
	virtual void strHeader(OutStream & os) const override;

	// Due to [-Woverloaded-virtual=]
	using BaseCompiledForm::strHeader;

	virtual void toStream(OutStream & os) const override;

};


}

#endif /*EXECUTABLESYSTEM_H_*/

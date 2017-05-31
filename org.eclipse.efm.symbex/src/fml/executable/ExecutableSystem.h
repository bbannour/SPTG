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

#include <common/AvmPointer.h>

#include <fml/executable/BaseCompiledForm.h>

#include <collection/Typedef.h>

#include <fml/common/SpecifierElement.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/symbol/Symbol.h>

#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>



namespace sep
{


class AvmCode;

class ObjectElement;

class System;


class ExecutableSystem :
		public BaseCompiledForm ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutableSystem )

{

	AVM_DECLARE_CLONABLE_CLASS( ExecutableSystem )


protected:
	/*
	 * ATTRIBUTES
	 */
	TableOfExecutableForm mExecutables;

	ExecutableForm    mNullExecutable;
	Symbol            mNullInstance;

	ExecutableForm    mParametersExecutable;
	InstanceOfMachine mParametersInstance;

	Symbol mSystemInstance;

	ExecutableForm * mDefaultProcessExecutableForm;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutableSystem(System & astSystem)
	: BaseCompiledForm( CLASS_KIND_T( ExecutableSystem ) , NULL, &astSystem ),
	mExecutables( ),

	mNullExecutable( *this , 0 ),
	mNullInstance( new InstanceOfMachine(
			&mNullExecutable, NULL, &mNullExecutable, NULL, 0,
			Specifier::DESIGN_INSTANCE_STATIC_SPECIFIER) ),

	mParametersExecutable( *this, NULL, &astSystem, 0 ),
	mParametersInstance( NULL, &astSystem, &mParametersExecutable, NULL, 0 ),

	mSystemInstance( ),
	mDefaultProcessExecutableForm( NULL )
	{
		mNullInstance.machine().setInstanceModel(mNullInstance.rawMachine());

		ExecutableLib::MACHINE_NULL.setExecutable( &mNullExecutable );

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
	mExecutables( anExecutable.mExecutables ),

	mNullExecutable( anExecutable.mNullExecutable ),
	mNullInstance( anExecutable.mNullInstance ),

	mParametersExecutable( anExecutable.mParametersExecutable ),
	mParametersInstance( anExecutable.mParametersInstance ),

	mSystemInstance( anExecutable.mSystemInstance ),
	mDefaultProcessExecutableForm(
		(anExecutable.mDefaultProcessExecutableForm == NULL) ? NULL :
			new ExecutableForm( *(anExecutable.mDefaultProcessExecutableForm) ) )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutableSystem()
	{
		if( mDefaultProcessExecutableForm != NULL )
		{
			delete( mDefaultProcessExecutableForm );
		}
	}


	/**
	 * SETTER
	 * updateFullyQualifiedNameID()
	 */
	virtual void updateFullyQualifiedNameID();


	/**
	 * GETTER  API
	 * Specifier
	 */
	const Specifier & getSpecifier() const
	{
		return( rawSystemInstance()->getExecutable()->getSpecifier() );
	}


	/**
	 * GETTER
	 * TableOfExecutableForm
	 */
	inline const TableOfExecutableForm & getExecutables() const
	{
		return( mExecutables );
	}


	inline avm_size_t size() const
	{
		return( mExecutables.size() );
	}


	/**
	 * GETTER - SETTER
	 * mExecutableForm
	 */
//	inline ExecutableForm & newExecutable(ExecutableForm * aContainer,
//			const ObjectElement * aCompiled, avm_size_t aDataSize = 0)
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
	inline ExecutableForm * defaultExecutableForm()
	{
		if( mDefaultProcessExecutableForm != NULL )
		{
			mDefaultProcessExecutableForm = new ExecutableForm( *this , 0 );
		}
		return( mDefaultProcessExecutableForm );
	}

	/**
	 * NEW TMP EXECUTABLE
	 */
	inline void initProcessExecutableForm(
			ExecutableForm & anExecutableForm, avm_size_t aDataSize = 0) const
	{
		anExecutableForm.init(
				rawSystemInstance()->getExecutable(), aDataSize);
	}


	/**
	 * GETTER - SETTER
	 * Machine Count
	 */
	inline avm_size_t getMachineCount() const
	{
		return( rawSystemInstance()->getExecutable()->getrecMachineCount() +1 );
	}


	/**
	 * Serialization
	 */
	void strHeader(OutStream & os) const;

	virtual void toStream(OutStream & os) const;

};


}

#endif /*EXECUTABLESYSTEM_H_*/

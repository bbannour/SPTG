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

#include "Compiler.h"

#include <builder/analysis/CommunicationDependency.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/builtin/Identifier.h>
#include <fml/expression/StatementTypeChecker.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementFactory.h>
#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/AvmTransition.h>
#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/RoutingData.h>

#include <fml/operator/OperatorManager.h>

#include <fml/type/TypeManager.h>

#include <fml/infrastructure/DataType.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/System.h>
#include <fml/infrastructure/Transition.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/PropertyPart.h>

#include <fml/workflow/UniFormIdentifier.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
Compiler::Compiler(Configuration & aConfiguration,
		AvmcodeCompiler & anAvmcodeCompiler)
: BaseMachineCompiler( aConfiguration, anAvmcodeCompiler ),
mDataCompiler( *this ),
mProgramCompiler( *this ),
mTransitionCompiler( *this ),
mComCompiler( *this )
{
	//!! NOTHING
}


/**
 * CONFIGURE
 */
bool Compiler::configure()
{
	if( not mAvmcodeCompiler.configure() )
	{
		AVM_OS_ERROR_ALERT << "Compiler::configure:> "
					"the Avmcode compiler configuration failed !!!"
				<< SEND_ALERT;

		return( false );
	}

	return( true );
}


/*
 ******************************************************************************
 * START
 ******************************************************************************
 */

bool Compiler::start(System & aSystem)
{
	ExecutableSystem * aExecutableSystem = new ExecutableSystem( aSystem );
	mConfiguration.setExecutableSystem( aExecutableSystem );

	precompileSystem(aSystem);


AVM_IF_DEBUG_FLAG( COMPILING )
	mConfiguration.serializeDebugExecutable( "precompiling" );
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	mComCompiler.updateMessageID();

	compileExecutableSystem();

AVM_IF_DEBUG_FLAG( COMPILING )
	mConfiguration.serializeDebugExecutable( "compiling" );
AVM_ENDIF_DEBUG_FLAG( COMPILING )


	postcompileExecutableSystem();

AVM_IF_DEBUG_FLAG( COMPILING )
mConfiguration.serializeDebugExecutable( "postcompiling" );
AVM_ENDIF_DEBUG_FLAG( COMPILING )


	return( hasZeroError() );
}

/**
 *******************************************************************************
 * PRECOMPILATION
 *******************************************************************************
 */

/**
 * precompile
 * declaration
 */
void Compiler::precompilePropertyPart(ExecutableForm * anExecutable,
		PropertyPart & theDeclaration, TableOfInstanceOfData & tableOfVariable)
{
	// User Variable-Parameters
	PropertyPart::const_variable_iterator itVar =
			theDeclaration.var_parameter_begin();
	PropertyPart::const_owned_iterator endVar =
			theDeclaration.var_parameter_end();
	for( ; itVar != endVar ; ++itVar )
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( (*itVar) )
				<< "data or type for compiling !!!"
				<< SEND_EXIT;

		// Allocation for variable
		mDataCompiler.precompileData(anExecutable,
				(*itVar).to_ptr< Variable >(), tableOfVariable);
	}

	// User Variable-Returns
	itVar = theDeclaration.var_return_begin();
	endVar = theDeclaration.var_return_end();
	for( ; itVar != endVar ; ++itVar )
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( (*itVar) )
				<< "data or type for compiling !!!"
				<< SEND_EXIT;

		// Allocation for variable
		mDataCompiler.precompileData(anExecutable,
				(*itVar).to_ptr< Variable >(), tableOfVariable);
	}

	// Other OwnedElements
	PropertyPart::const_owned_iterator itWfO = theDeclaration.owned_begin();
	PropertyPart::const_owned_iterator endWfO = theDeclaration.owned_end();
	for( ; itWfO != endWfO ; ++itWfO )
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( (*itWfO) )
				<< "data or type for compiling !!!"
				<< SEND_EXIT;

		// Allocation for variable
		if( (*itWfO).is< Variable >() )
		{
			Variable * aVariable = (*itWfO).to_ptr< Variable >();

			if( aVariable->getModifier().noNatureParameter() )
			{
				mDataCompiler.precompileData(anExecutable,
						aVariable, tableOfVariable);
			}
		}

		// Allocation for buffer
		else if( (*itWfO).is< Buffer >() )
		{
			mComCompiler.precompileBuffer(
					anExecutable, (*itWfO).to_ptr< Buffer >());
		}

		// Allocation for port
		else if( (*itWfO).is< Port >() )
		{
//			mComCompiler.precompilePort(anExecutable,
//					(*it).to_ptr< Port >(), tableOfVariable);
		}

		else if( (*itWfO).is< Channel >() )
		{
//			mComCompiler.precompileChannel(
//					anExecutable, (*it).to_ptr< Channel >());
		}

		else if( (*itWfO).is< Machine >() )
		{
//			precompileInstanceStatic(
//					anExecutable, (*it).to_ptr< Machine >());
		}

		// Allocation for typedef
		else  if( (*itWfO).is< DataType >() )
		{
			precompileTypeSpecifier(anExecutable, (*itWfO));
		}
	}

	// Allocation for ports / signals
	mComCompiler.precompileComPoint(
			anExecutable, theDeclaration, tableOfVariable);

	// Allocation for channels
	mComCompiler.precompileChannel(anExecutable,
			theDeclaration, tableOfVariable);
}


void Compiler::precompileDataType(AvmProgram * aProgram,
		PropertyPart & theDeclaration, TableOfInstanceOfData & tableOfVariable)
{
	PropertyPart::const_owned_iterator it = theDeclaration.owned_begin();
	PropertyPart::const_owned_iterator endIt = theDeclaration.owned_end();
	for( ; it != endIt ; ++it )
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( (*it) )
				<< "data or type for compiling !!!"
				<< SEND_EXIT;

		// Allocation for variable
		if( (*it).is< Variable >() )
		{
			mDataCompiler.precompileData(aProgram,
					(*it).to_ptr< Variable >(), tableOfVariable);
		}

		// Allocation for typedef
		else
		{
			precompileTypeSpecifier(aProgram, (*it));
		}
	}
}


/**
 * precompile
 * specification
 */
void Compiler::precompileExecutableCompositePart(
		ExecutableForm * aContainer, Machine * anExecutableSpec)
{
	CompositePart * aCompositePart = anExecutableSpec->getCompositePart();

	if( aCompositePart == NULL )
	{
		//!! NOTHING
		return;
	}

	/*
	 * precompiling procedure
	 */
	if( aCompositePart->hasProcedure() )
	{
		CompositePart::const_procedure_iterator it =
				aCompositePart->procedure_begin();
		CompositePart::const_procedure_iterator endIt =
				aCompositePart->procedure_end();
		for( ; it != endIt ; ++it )
		{
			precompileExecutable(aContainer, (it));
		}
	}

	/*
	 * precompiling executable - instance static
	 */
	if( aCompositePart->hasMachine() )
	{
		// precompiling sub-executable
		anExecutableSpec->expandGroupStatemachine();

		CompositePart::const_machine_iterator it =
				aCompositePart->machine_begin();
		CompositePart::const_machine_iterator endIt =
				aCompositePart->machine_end();
		for( ; it != endIt ; ++it )
		{
			precompileExecutable(aContainer, (it));
		}
	}

	/*
	 * precompiling instance dynamic
	 */
	if( aCompositePart->hasInstanceDynamic() )
	{
		CompositePart::const_machine_iterator it =
				aCompositePart->instance_dynamic_begin();
		CompositePart::const_machine_iterator endIt =
				aCompositePart->instance_dynamic_end();
		for( ; it != endIt ; ++it )
		{
//			if( (it)->getSpecifier().isDesignInstanceDynamic() )
			{
				precompileExecutableInstanceDynamique(aContainer, (it));
			}
		}
	}
}


void Compiler::precompileExecutable(
		ExecutableForm * aContainer, Machine * anExecutableSpec)
{
	if( anExecutableSpec->getSpecifier().hasGroupMask() )
	{
		precompileExecutableGroup(aContainer, anExecutableSpec);
	}
	else if( anExecutableSpec->getSpecifier().isDesignModel())
	{
		precompileExecutableModel(aContainer, anExecutableSpec);
	}
	else if( anExecutableSpec->getSpecifier().isDesignPrototypeStatic() )
	{
		precompileExecutablePrototype(aContainer, anExecutableSpec);
	}
	else if( anExecutableSpec->getSpecifier().isDesignInstanceStatic() )
	{
		precompileExecutableInstanceStatic(aContainer, anExecutableSpec);
	}
	else if( anExecutableSpec->getSpecifier().isDesignInstanceDynamic() )
	{
		precompileExecutableInstanceDynamique(aContainer, anExecutableSpec);
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected in precompiling stage the executable: "
				<< std::endl << str_header( anExecutableSpec ) << std::endl
				<< "==> with specifier: "
				<< anExecutableSpec->getSpecifier().str() << " !!!"
				<< SEND_EXIT;
	}
}


ExecutableForm * Compiler::precompileExecutableModel(
		ExecutableForm * aContainer, Machine * anExecutableSpec)
{
//AVM_OS_CERR << TAB << "<** begin precompiling executable model:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;

	// CREATE NEW EXECUTABLE
	ExecutableForm * anExec = new ExecutableForm(
			mConfiguration.getExecutableSystem(),
			aContainer, anExecutableSpec);

	setInheritedSpecifier(aContainer, anExec);

	// APPEND NEW EXECUTABLE IN THE SYSTEM
//	//?? For retrocompatibity serialization order
//	getSymbolTable().addMachineExecutable(
//			mExecutableSystem->saveExecutable( anExec ) );

	avm_size_t maximalInstanceCount = anExecutableSpec->hasInstanceSpecifier()
		? anExecutableSpec->getInstanceSpecifier()->getMaximalInstanceCount()
		: AVM_NUMERIC_MAX_SIZE_T;

	//??? Sera fait dans precompileExecutableInstanceXXX(...) ?
//	anExec->incrPossibleStaticInstanciationCount( createdInstanceCount );

	if( anExecutableSpec->getSpecifier().isFamilyComponentComposite() )
	{
		Specifier aSpecifier( anExecutableSpec->getSpecifier() );

		InstanceOfMachine * aModelInstance = new InstanceOfMachine(
				aContainer, anExecutableSpec, anExec, NULL,
				aContainer->getInstanceModel().size(),
				aSpecifier.setDesignModel() );

		//??? Sera fait dans precompileExecutableInstanceXXX(...) ?
		aModelInstance->setInstanceCount(
				/*createdInstanceCount*/0, maximalInstanceCount);

		aContainer->saveInstanceModel( aModelInstance );
	}

	/*
	 * Allocation of declaration contents :>
	 * constant, variable, typedef, buffer, port
	 */
	TableOfInstanceOfData tableOfVariable;

	if( anExecutableSpec->hasProperty() )
	{
		avm_offset_t parametersCount = anExecutableSpec->
				getPropertyPart().getVariableParametersCount();

		anExec->setParamOffsetCount( 0 , parametersCount );

		anExec->setReturnOffsetCount( parametersCount, anExecutableSpec->
				getPropertyPart().getVariableReturnsCount() );

		precompilePropertyPart(anExec,
				anExecutableSpec->getPropertyPart(), tableOfVariable);
	}

	/*
	 * Update data table
	 */
	anExec->setData(tableOfVariable);


	/*
	 * precompiling executable composite part
	 */
	if( anExecutableSpec->hasMachine() || anExecutableSpec->hasPortSignal() )
	{
		Specifier aSpecifier( anExecutableSpec->getSpecifier() );

		// Set the instance THIS at first position (index = 0)
		InstanceOfMachine * aNewInstance =
				InstanceOfMachine::newInstanceModelThis(
						anExec, anExecutableSpec, anExec, NULL,
						anExec->getInstanceModel().size(),
						aSpecifier.setDesignModel() );

		anExec->saveInstanceModel(aNewInstance);

		aNewInstance = InstanceOfMachine::newThis(anExec,
				aNewInstance, anExec->getInstanceStatic().size() );
//		aNewInstance->setAutoStart( anExecutableSpec->hasInitialInstance() );

		anExec->saveInstanceStatic(aNewInstance);
	}

	precompileExecutableCompositePart(anExec, anExecutableSpec);


	/*
	 * precompiling transition
	 */
	if( anExecutableSpec->hasOutgoingTransition() )
	{
		BehavioralPart::const_transition_iterator it = anExecutableSpec->
				getBehavior()->outgoing_transition_begin();
		BehavioralPart::const_transition_iterator endIt = anExecutableSpec->
				getBehavior()->outgoing_transition_end();
		for( ; it != endIt ; ++it )
		{
			mTransitionCompiler.precompileTransition( anExec, (it) );
		}
	}

	// APPEND NEW EXECUTABLE IN THE SYSTEM
	//?? For retrocompatibity serialization order
	getSymbolTable().addMachineExecutable( mConfiguration.
			getExecutableSystem().saveExecutable( anExec ) );

//AVM_OS_TRACE << TAB << ">** end precompiling executable MODEL:>"
//	<< std::endl << str_header( anExecutableSpec ) << std::endl;

	return( anExec );
}


void Compiler::precompileExecutablePrototype(
		ExecutableForm * aContainer, Machine * anExecutableSpec)
{
//AVM_OS_TRACE << TAB << "<++ begin precompiling executable #instance model:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;

		ExecutableForm * anExec =
				precompileExecutableModel(aContainer, anExecutableSpec);

		avm_size_t initialInstanceCount = 1;
		avm_size_t maximalInstanceCount = AVM_NUMERIC_MAX_SIZE_T;
		if( anExecutableSpec->hasInstanceSpecifier() )
		{
			initialInstanceCount = anExecutableSpec->
					getInstanceSpecifier()->getInitialInstanceCount();

			maximalInstanceCount = anExecutableSpec->
					getInstanceSpecifier()->getMaximalInstanceCount();
		}

		// Instances for << MODEL >> & INSTANCE
		InstanceOfMachine * aModelInstance = NULL;
		if( anExecutableSpec->getSpecifier().isFamilyComponentComposite() )
		{
			aModelInstance = aContainer->getInstanceModel().
					getByAstElement( anExec->getAstElement() ).rawMachine();
			if( aModelInstance == NULL )
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unfound model instance of #prototype executable !!!"
						<< std::endl << str_header( anExec->getAstElement() )
						<< SEND_EXIT;
			}
			else
			{
				aModelInstance->incrInstanciationCount( initialInstanceCount );

				anExec->incrPossibleStaticInstanciationCount( initialInstanceCount );
			}
		}

		if( initialInstanceCount > 0 )
		{
			Specifier aSpecifier( anExecutableSpec->getSpecifier() );

			InstanceOfMachine * aNewInstance = new InstanceOfMachine(
					aContainer, anExecutableSpec, anExec, aModelInstance,
					aContainer->getInstanceStatic().size(),
					aSpecifier.setDesignPrototypeStatic() );

			aNewInstance->setInstanceCount(
					initialInstanceCount, maximalInstanceCount);

			aNewInstance->setAutoStart( true );

			setInheritedSpecifier(aContainer, aNewInstance);

			anExec->setPrototypeInstance( aNewInstance );

			const Symbol & bfInstance =
					aContainer->saveInstanceStatic(aNewInstance);
			getSymbolTable().addInstanceStatic(bfInstance);

			aSpecifier.setDesignInstanceStatic();

			avm_size_t offset = 1;
			for( ; offset < initialInstanceCount ; ++offset )
			{
				aNewInstance = new InstanceOfMachine(
						aContainer, anExecutableSpec, anExec, aModelInstance,
						aContainer->getInstanceStatic().size(), aSpecifier);
				aNewInstance->setInstanceCount(1, maximalInstanceCount);

				aNewInstance->updateUfid(offset);

				aNewInstance->setAutoStart( true );

				setInheritedSpecifier(aContainer, aNewInstance);

				getSymbolTable().addInstanceStatic(
						aContainer->saveInstanceStatic(aNewInstance));
			}
		}
		else
		{
//!![TRACE]: to delete
//AVM_OS_DEBUG << "precompileExecutablePrototype Initial Instanciation Count: 0"
//		<< std::endl << str_header( anExec ) << std::endl;
		}

//AVM_OS_TRACE << TAB << ">++ end precompiling executable #instance model:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;
}


void Compiler::precompileExecutableInstanceStatic(
		ExecutableForm * aContainer, Machine * anExecutableSpec)
{
//AVM_OS_TRACE << TAB << "<-- begin precompiling executable #static instance:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;

		ExecutableForm * anExec =
				getSymbolTable().searchExecutableModel(anExecutableSpec);

		if( anExec != NULL )
		{
			avm_size_t initialInstanceCount = anExecutableSpec->
					getInstanceSpecifier()->getInitialInstanceCount();
			avm_size_t maximalInstanceCount = anExecutableSpec->
					getInstanceSpecifier()->getMaximalInstanceCount();

			anExec->incrPossibleStaticInstanciationCount( initialInstanceCount );

			// Instances for << MODEL >> & INSTANCE
			InstanceOfMachine * aModelInstance = aContainer->getInstanceModel().
					getByAstElement( anExec->getAstElement() ).rawMachine();
			if( aModelInstance == NULL )
			{
				Specifier aSpecifier(
						anExec->getAstMachine()->getSpecifier() );

				aModelInstance = new InstanceOfMachine( aContainer,
						anExec->getAstMachine(), anExec, NULL,
						aContainer->getInstanceModel().size(),
						aSpecifier.setDesignModel() );

				aModelInstance->setInstanceCount(
						initialInstanceCount, maximalInstanceCount);

				aContainer->saveInstanceModel( aModelInstance );
			}
			else
			{
				aModelInstance->incrInstanciationCount( initialInstanceCount );
			}

			InstanceOfMachine * aNewInstance = NULL;
			avm_size_t offset = 0;
			for( ; offset < initialInstanceCount ; ++offset )
			{
				aNewInstance = new InstanceOfMachine(
						aContainer, anExecutableSpec, anExec, aModelInstance,
						aContainer->getInstanceStatic().size() );

				aNewInstance->setInstanceCount(
						initialInstanceCount, maximalInstanceCount);

				if( offset > 0 )
				{
					aNewInstance->updateUfid(offset);
				}

				aNewInstance->setAutoStart( anExecutableSpec->isAutoStart() );
//				aNewInstance->setAutoStart( true );

				setInheritedSpecifier(aContainer, aNewInstance);

				getSymbolTable().addInstanceStatic(
						aContainer->saveInstanceStatic(aNewInstance));
			}
		}

		// ERROR REPORTING
		else if( getSymbolTable().hasError() )
		{
			incrErrorCount();
			anExecutableSpec->errorLocation(AVM_OS_WARN)
					<< getSymbolTable().getErrorMessage()
					<< std::endl << std::endl;
		}

		else
		{


			incrErrorCount();
			anExecutableSpec->errorLocation(AVM_OS_WARN)
					<< "Unfound the model << " << anExecutableSpec->strType()
					<< " >> of the executable instance << "
					<< str_header( anExecutableSpec ) << " >>"
					<< std::endl << std::endl;
		}

//AVM_OS_TRACE << TAB << ">-- end precompiling executable #dynamic instance:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;
}


void Compiler::precompileExecutableInstanceDynamique(
		ExecutableForm * aContainer, Machine * anExecutableSpec)
{
//AVM_OS_WARN << TAB << "<-- begin precompiling executable #dynamic instance:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;

		ExecutableForm * anExec =
				getSymbolTable().searchExecutableModel(anExecutableSpec);

		avm_size_t initialInstanceCount = anExecutableSpec->
				getInstanceSpecifier()->getInitialInstanceCount();
		avm_size_t maximalInstanceCount = anExecutableSpec->
				getInstanceSpecifier()->getMaximalInstanceCount();

		if( anExec != NULL )
		{
			// Instances for << MODEL >> & INSTANCE
			CompilationEnvironment cENV(anExec);

			InstanceOfMachine * aModelInstance =
					getSymbolTable().searchInstanceModel(
							cENV.mCTX, anExec->getAstElement()).rawMachine();
			if( aModelInstance == NULL )
			{
				aModelInstance = aContainer->getInstanceModel().
						getByAstElement( anExec->getAstElement() ).rawMachine();
			}
			if( aModelInstance == NULL )
			{
				Specifier aSpecifier(
						anExec->getAstMachine()->getSpecifier() );

				aModelInstance = new InstanceOfMachine( aContainer,
						anExec->getAstMachine(), anExec, NULL,
						aContainer->getInstanceModel().size(),
						aSpecifier.setDesignModel() );

				aModelInstance->setInstanceCount(
						initialInstanceCount, maximalInstanceCount);

				aContainer->saveInstanceModel( aModelInstance );

				anExec->incrPossibleDynamicInstanciationCount(
						initialInstanceCount );
			}
			else
			{
				aModelInstance->incrPossibleDynamicInstanciationCount(
						initialInstanceCount );
			}

			InstanceOfMachine * aNewInstance = new InstanceOfMachine(
					aContainer, anExecutableSpec, anExec, aModelInstance,
					aContainer->getInstanceStatic().size() );

			aNewInstance->setInstanceCount(
					initialInstanceCount, maximalInstanceCount);

			aNewInstance->setAutoStart( true );

			setInheritedSpecifier(aContainer, aNewInstance);

			aContainer->saveInstanceDynamic(aNewInstance);
		}

		// ERROR REPORTING
		else if( getSymbolTable().hasError() )
		{
			incrErrorCount();
			anExecutableSpec->errorLocation(AVM_OS_WARN)
					<< getSymbolTable().getErrorMessage()
					<< std::endl << std::endl;
		}

		else
		{
			incrWarningCount();
			anExecutableSpec->warningLocation(AVM_OS_LOG)
					<< "Unfound the executable model << "
					<< anExecutableSpec->strType()
					<< " >> of the #dynamic instance !!!"
					<< std::endl << str_header( anExecutableSpec )
					<< std::endl << std::endl;

			InstanceOfMachine * aNewInstance = new InstanceOfMachine(
					aContainer, anExecutableSpec, anExec, NULL,
					aContainer->getInstanceStatic().size() );

			aNewInstance->setInstanceCount(
					initialInstanceCount, maximalInstanceCount);

			aNewInstance->setAutoStart( false );

			setInheritedSpecifier(aContainer, aNewInstance);

			aContainer->saveInstanceDynamic(aNewInstance);
		}

//AVM_OS_WARN << TAB << ">-- end precompiling executable #dynamic instance:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;
}


void Compiler::precompileExecutableGroup(
		ExecutableForm * aContainer, Machine * anExecutableSpec)
{
//	Machine * containerSM = anExecutableSpec->getContainerMachine();
//
//	if( anExecutableSpec->getSpecifier().isGroupEvery())
//	{
//		containerSM->appendOutgoingTransitionToEveryState(anExecutableSpec);
//	}
//	else if( anExecutableSpec->getSpecifier().isGroupSome())
//	{
//		containerSM->appendOutgoingTransitionToSomeState(anExecutableSpec);
//	}
//	else if( anExecutableSpec->getSpecifier().isGroupExcept() )
//	{
//		containerSM->appendOutgoingTransitionToExceptState(anExecutableSpec);
//	}
}





/**
 * precompile
 * specification
 */
void Compiler::precompileSystem(System & aSystem)
{
//AVM_OS_TRACE << TAB << "< begin precompiling specification:> "
//		<< aSystem.getFullyQualifiedNameID() << std::endl;

	/*
	 * For the system executable
	 */
	ExecutableForm * systemExec = new ExecutableForm(
			mConfiguration.getExecutableSystem(), NULL, (& aSystem));

	// APPEND NEW EXECUTABLE IN THE SYSTEM
//	//?? For retrocompatibity serialization order
//	getSymbolTable().addMachineExecutable(
//			mExecutableSystem->saveExecutable( systemExec ) );

	// Structural decompositon
	systemExec->setMainComponent( true );


	Specifier aSpecifier( aSystem.getSpecifier() );

	InstanceOfMachine * aNewInstance = new InstanceOfMachine(NULL, (& aSystem),
			systemExec, NULL, 0, aSpecifier.setDesignPrototypeStatic() );

	aNewInstance->setAutoStart( true );
//	aSystem.getInstanceSpecifier()->hasInitialInstance() );

	aNewInstance->setInstanceCount(1, 1);

	systemExec->setPrototypeInstance( aNewInstance );
	systemExec->incrPossibleStaticInstanciationCount(1);

	getSymbolTable().addInstanceStatic( mConfiguration.
			getExecutableSystem().setSystemInstance(aNewInstance) );


	// Set the instance THIS in first position (index = 0)
	// for << MODEL >> & INSTANCE
	aNewInstance = InstanceOfMachine::newInstanceModelThis(
			systemExec, (& aSystem), systemExec, NULL,
			systemExec->getInstanceModel().size(),
			aSpecifier.setDesignModel() );

	aNewInstance->setInstanceCount(0, 1);

	systemExec->saveInstanceModel( aNewInstance );

	aNewInstance = InstanceOfMachine::newThis(systemExec,
			aNewInstance, systemExec->getInstanceStatic().size() );

	systemExec->saveInstanceStatic(aNewInstance);

	/*
	 * Allocation of declaration contents :>
	 * constant, variable, typedef, buffer, port
	 */
	if( aSystem.hasProperty() )
	{
		TableOfInstanceOfData tableOfVariable;

		precompilePropertyPart(systemExec,
				aSystem.getPropertyPart(), tableOfVariable);

		/*
		 * Update data table
		 */
		systemExec->setData(tableOfVariable);
	}


	/*
	 * precompiling executable composite part
	 */
	precompileExecutableCompositePart(systemExec, (& aSystem));

//AVM_OS_TRACE << TAB << "> end precompiling specification:> "
//		<< aSystem.getFullyQualifiedNameID() << std::endl << std::endl;

	// APPEND NEW EXECUTABLE IN THE SYSTEM
	//?? For retrocompatibity serialization order
	getSymbolTable().addMachineExecutable( mConfiguration.
			getExecutableSystem().saveExecutable( systemExec ) );
}


/**
 * setInheritedSpecifier from container to owned elements
 */
void Compiler::setInheritedSpecifier(
		ExecutableForm * aContainer, ExecutableForm * anExecutable)
{
	if( aContainer->getSpecifier().hasFeatureInputEnabled() )
	{
		anExecutable->getwSpecifier().setFeatureInputEnabled();

		const_cast< Machine * >(anExecutable->getAstMachine() )
				->getwSpecifier().setFeatureInputEnabled();

	}
}

void Compiler::setInheritedSpecifier(
		ExecutableForm * aContainer, InstanceOfMachine * aMachine)
{
	if( aContainer->getSpecifier().hasFeatureInputEnabled() )
	{
		aMachine->getwSpecifier().setFeatureInputEnabled();
	}
}




/**
 *******************************************************************************
 * COMPILATION OF EXECUTABLE
 *******************************************************************************
 */

void Compiler::compileExecutableSystem()
{
	TableOfExecutableForm::const_raw_iterator itProc;
	TableOfExecutableForm::const_raw_iterator endProc;

	TableOfExecutableForm::const_raw_iterator itExec =
			mConfiguration.getExecutableSystem().getExecutables().begin();
	TableOfExecutableForm::const_raw_iterator endIt =
			mConfiguration.getExecutableSystem().getExecutables().end();
	for( ; itExec != endIt ; ++itExec )
	{
		compileExecutable( (itExec) );

		if( (itExec)->hasExecutable() )
		{
			itProc = (itExec)->getExecutables().begin();
			endProc = (itExec)->getExecutables().end();
			for( ; itProc != endProc ; ++itProc )
			{
				compileProcedure( itProc );
			}
		}
	}
}


void Compiler::compileExecutable(ExecutableForm * anExecutable)
{
	if( anExecutable->isCompiledFlag() )
	{
		return;
	}
	else
	{
		anExecutable->setCompiledFlag();
	}

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<executable>: "
			<< anExecutable->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	// Compile data & all machine MOE program
	compileBaseMachine(anExecutable);

	// Compile data & all instance MOE program
	compileAllInstances( anExecutable );

	if( anExecutable->getAstElement()->is< System >() )
	{
		compileSystem( anExecutable );
	}

	else if( anExecutable->getAstElement()->is_exactly< Machine >() )
	{
		if( anExecutable->getSpecifier().isFamilyComponentStatemachine() )
		{
			compileStatemachine( anExecutable );
		}

		else
		{
			compileMachine( anExecutable );
		}
	}

	else
	{
		AVM_OS_EXIT( FAILED )
				<< "Unexpected executable form for compiling :\n"
				<< anExecutable->toString()
				<< SEND_EXIT;
	}

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| compiling<executable>: "
			<< anExecutable->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
}


/**
 *******************************************************************************
 * COMPILATION OF INSTANCE MACHINE PARAM
 *******************************************************************************
 */
void Compiler::compileAllInstances(ExecutableForm * anExecutableForm)
{
	if( anExecutableForm->hasInstanceStatic() )
	{
		// Compilation of InstanceOfMachine Parameters / Behaviors
		TableOfSymbol::const_iterator itMachine =
				anExecutableForm->instance_static_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm->instance_static_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			compileInstance(anExecutableForm, (*itMachine).rawMachine());

			if( not (*itMachine).hasExecutable() )
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected a #static instance "
								"without executable model !!!"
						<< std::endl << str_header( (*itMachine) )
						<< SEND_EXIT;
			}
		}
	}

	if( anExecutableForm->hasInstanceDynamic() )
	{
		// Compilation of InstanceOfMachine Parameters / Behaviors
		TableOfSymbol::const_iterator itMachine =
				anExecutableForm->instance_dynamic_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm->instance_dynamic_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			compileInstance(anExecutableForm, (*itMachine).rawMachine());

			if( not (*itMachine).hasExecutable() )
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected a #dynamic instance "
								"without executable model !!!"
						<< std::endl << str_header( (*itMachine) )
						<< SEND_EXIT;
			}
		}
	}
}

void Compiler::compileInstance(
		ExecutableForm * theExecutableContainer, InstanceOfMachine * anInstance)
{
	const Machine * anExecutableSpec = anInstance->getAstMachine();

//AVM_OS_WARN << TAB << "<-- begin compiling executable instance:>" << std::endl
//			<< to_stream( anInstance )// << std::endl
//			<< to_stream( anExecutableSpec ) << std::endl;

	ExecutableForm * anExec = anInstance->getExecutable();

	if( anExec == NULL )
	{
		anExec = getSymbolTable().searchExecutableModel(anExecutableSpec);

		if( anExec != NULL )
		{
			anInstance->setExecutable( anExec );

			anInstance->setAutoStart( true );

			// Instances for << MODEL >> & INSTANCE
			CompilationEnvironment cENV(anExec);

			InstanceOfMachine * aModelInstance =
					getSymbolTable().searchInstanceModel(
							cENV.mCTX, anExec->getAstElement()).rawMachine();
			if( aModelInstance == NULL )
			{
				aModelInstance = theExecutableContainer->getInstanceModel().
						getByAstElement( anExec->getAstElement() ).rawMachine();
			}
			if( aModelInstance != NULL )
			{
				anInstance->setInstanceModel( aModelInstance );
			}

			if( anInstance->getSpecifier().hasDesignInstanceDynamic() )
			{
				if( aModelInstance != NULL )
				{
					aModelInstance->incrPossibleDynamicInstanciationCount( 1 );
				}
				else
				{
					anExec->incrPossibleDynamicInstanciationCount( 1 );
				}
			}
			else
			{
				anExec->incrPossibleStaticInstanciationCount( 1 );
			}
		}

		// ERROR REPORTING
		else if( getSymbolTable().hasError() )
		{
			incrErrorCount();
			anExecutableSpec->errorLocation(AVM_OS_WARN)
					<< getSymbolTable().getErrorMessage()
					<< std::endl << std::endl;
		}

		else
		{
			incrErrorCount();
			anExecutableSpec->errorLocation(AVM_OS_WARN)
					<< "Unfound the model << "
					<< anExecutableSpec->strType()
					<< " >> of the statemachine instance << "
					<< str_header( anExecutableSpec ) << " >>"
					<< std::endl << std::endl;
		}
	}

	if( anExec != NULL )
	{
		compileExecutable( anExec );

		if( anExec->hasParamReturn() )
		{
			compileInstanceParameters(theExecutableContainer, anInstance);
		}
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a instance without executable model !!!"
				<< std::endl << str_header( anInstance )
				<< SEND_EXIT;

		return;
	}

	BehavioralPart * theBehavior = anExecutableSpec->getBehavior();

	if( theBehavior != NULL )
	{
		/*
		 * onCreate
		 */
		if( theBehavior->hasOnCreate()
			&& StatementTypeChecker::doSomething(theBehavior->getOnCreate()) )
		{
			CompilationEnvironment cENV(NULL, anExec, theExecutableContainer);

			BFCode onCreate = theBehavior->getOnCreate();
			if( anExec->hasOnCreate()
				&& anInstance->getSpecifier().hasDesignInstanceNotModel() )
			{
				onCreate = StatementConstructor::newCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						anExec->getOnCreate(), onCreate );
			}

			anInstance->setOnCreate(
					mAvmcodeCompiler.compileStatement(cENV.mCTX, onCreate) );
		}

		/*
		 * onStart
		 */
		if( theBehavior->hasOnStart()
			&& StatementTypeChecker::doSomething(theBehavior->getOnStart()) )
		{
			CompilationEnvironment cENV(NULL, anExec, theExecutableContainer);

			BFCode onStart = theBehavior->getOnStart();
			if( anExec->hasOnStart() )
			{
				onStart = StatementConstructor::newCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						anExec->getOnStart(), onStart );
			}

			if( anExec->hasOnInit() )
			{
				onStart = StatementConstructor::newCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						onStart, anExec->getOnInit() );
			}

			anInstance->setOnStart(
					mAvmcodeCompiler.compileStatement(cENV.mCTX, onStart) );
		}
	}

//AVM_OS_WARN << TAB << ">-- end compiling executable instance:>" << std::endl
//			<< to_stream( anInstance )// << std::endl
//			<< str_header( anExecutableSpec ) << std::endl;
}


void Compiler::compileInstanceParameters(
		ExecutableForm * theExecutableContainer, InstanceOfMachine * anInstance)
{
	ExecutableForm * anExecutableForm = anInstance->getExecutable();

	const Machine * aMachine = anInstance->getAstMachine();

	if( (anExecutableForm != NULL) && anExecutableForm->hasParamReturn() )
	{
		APTableOfData aParamTable( new TableOfData(
				anExecutableForm->getParamReturnCount() ) );
		anInstance->setParamReturnTable( aParamTable );

		anInstance->setReturnOffset( anExecutableForm->getParamCount() );

		bool hasInitialInstance =
				aMachine->getInstanceSpecifier()->hasInitialInstance();


		if( anExecutableForm->hasParam() )
		{
			if( aMachine->hasVariableParameter() )
			{
				BF paramValue;

				TableOfVariable::const_raw_iterator it =
						aMachine->getVariableParameters().begin();
				TableOfVariable::const_raw_iterator itEnd =
						aMachine->getVariableParameters().end();
				for( avm_offset_t offset = 0 ; it != itEnd ; ++it , ++offset )
				{
					if( (*it).invalid() )
					{
						if( hasInitialInstance )
						{
							incrWarningCount();
							aMachine->errorLocation(AVM_OS_WARN)
									<< "Compile param warning << "
									<< str_header(
										anExecutableForm->rawParamData(offset) )
									<< " >> for the statemachine instance << "
									<< str_header( aMachine ) << " >> "
									<< "Unexpected non-instanciated parameters !"
									<< std::endl << std::endl;
							//!! Generation of symbolic parameter
							//!! Generation of symbolic parameter
						}
					}
					else if( (it)->hasValue() )
					{
						paramValue = mAvmcodeCompiler.decode_compileExpression(
								theExecutableContainer, (it)->getValue() );
						if( paramValue.valid() )
						{
							aParamTable->set(offset, paramValue);
						}
						else
						{
							incrErrorCount();
							aMachine->errorLocation(AVM_OS_WARN)
									<< "Compile param error << "
									<< str_header( *it )
									<< " >> for the statemachine instance << "
									<< str_header( aMachine ) << " >>"
									<< std::endl << std::endl;
						}
					}
					else if( hasInitialInstance )
					{
						incrWarningCount();
						aMachine->warningLocation(AVM_OS_WARN)
								<< "Compile param warning << "
								<< str_header( *it )
								<< " >> for the statemachine instance << "
								<< str_header( aMachine ) << " >> "
								<< "Unexpected non-instanciated parameters !"
								<< std::endl << std::endl;
						//!! Generation of symbolic parameter
						//!! Generation of symbolic parameter
					}
				}
			}
		}

		if( anExecutableForm->hasReturn() )
		{
			if( aMachine->hasVariableReturn() )
			{
				BF returnValue;

				TableOfVariable::const_raw_iterator it =
						aMachine->getVariableReturns().begin();
				TableOfVariable::const_raw_iterator itEnd =
						aMachine->getVariableReturns().end();
				for( avm_offset_t offset = 0 ; it != itEnd ; ++it , ++offset )
				{
					if( (*it).invalid() )
					{
						incrWarningCount();
						aMachine->errorLocation(AVM_OS_WARN)
								<< "Compile return warning << "
								<< str_header(
									anExecutableForm->rawReturnData(offset) )
								<< " >> for the statemachine instance << "
								<< str_header( aMachine ) << " >> "
								<< "Unexpected non-instanciated parameters !"
								<< std::endl << std::endl;
						//!! Generation of symbolic parameter
						//!! Generation of symbolic parameter
					}
					else if( (it)->hasValue() )
					{
						returnValue = mAvmcodeCompiler.decode_compileExpression(
								theExecutableContainer, (it)->getValue() );
						if( returnValue.valid() )
						{
							aParamTable->set(anExecutableForm->getReturnOffset()
									+ offset, returnValue);
						}
						else
						{
							incrErrorCount();
							aMachine->errorLocation(AVM_OS_WARN)
									<< "Compile return error << "
									<< str_header( *it )
									<< " >> for the statemachine instance << "
									<< str_header( aMachine ) << " >>"
									<< std::endl << std::endl;
						}
					}
				}
			}
		}
	}
}


/**
 *******************************************************************************
 * COMPILATION OF AVMPROGRAM
 *******************************************************************************
 */

void Compiler::compileAvmPrograms()
{
	AvmProgram * aProgram;
	avm_size_t offset;

	TableOfExecutableForm::const_raw_iterator itExec =
			mConfiguration.getExecutableSystem().getExecutables().begin();
	TableOfExecutableForm::const_raw_iterator endExec =
			mConfiguration.getExecutableSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		for( offset = 0 ; offset < (itExec)->getProgram().size() ; ++offset )
		{
			aProgram = (itExec)->getProgram().rawAt(offset);

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<program>: "
			<< aProgram->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

			mProgramCompiler.compileProgram( aProgram );

AVM_IF_DEBUG_FLAG( COMPILING )
//	(*itProg)->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| compiling<program>: "
			<< aProgram->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
		}
	}
}


/**
 * compile
 * Executable
 */
void Compiler::compileBaseMachine(ExecutableForm * anExecutableForm)
{
	const Machine * aMachine = anExecutableForm->getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<machine>: "
//		<< str_header( aMachine ) << std::endl;


	// COMPILATION OF PORT
	mComCompiler.compilePort(anExecutableForm);

	// COMPILATION OF DATA
	mDataCompiler.compileData(anExecutableForm);


	if( not aMachine->hasBehavior() )
	{
		return;
	}

	BehavioralPart * theBehavior = aMachine->getBehavior();

	/*
	 * onCreate
	 */
	if( theBehavior->hasOnCreate() &&
			StatementTypeChecker::doSomething(theBehavior->getOnCreate()) )
	{
		anExecutableForm->setOnCreate(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnCreate()) );
	}

	/*
	 * onInit
	 */
	if( theBehavior->hasOnInit() &&
			StatementTypeChecker::doSomething(theBehavior->getOnInit()) )
	{
		anExecutableForm->setOnInit(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnInit()) );
	}

	/*
	 * onFinal
	 */
	if( theBehavior->hasOnFinal() &&
			StatementTypeChecker::doSomething(theBehavior->getOnFinal()) )
	{
		anExecutableForm->setOnFinal(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnFinal()) );
	}


	/*
	 * onReturn
	 */
	if( theBehavior->hasOnReturn() &&
			StatementTypeChecker::doSomething(theBehavior->getOnReturn()) )
	{
		anExecutableForm->setOnReturn(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						mAvmcodeCompiler.compileStatement(
								anExecutableForm, theBehavior->getOnReturn()),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_FINAL) ) );
	}


	/*
	 * onStart
	 */
	if( theBehavior->hasOnStart() &&
			StatementTypeChecker::doSomething(theBehavior->getOnStart()) )
	{
		anExecutableForm->setOnStart(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnStart()) );
	}

	/*
	 * onStop
	 */
	if( theBehavior->hasOnStop() &&
			StatementTypeChecker::doSomething(theBehavior->getOnStop()) )
	{
		anExecutableForm->setOnStop(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnStop()) );
	}


	/*
	 * onIEnable
	 */
	if( theBehavior->hasOnIEnable() &&
			StatementTypeChecker::doSomething(theBehavior->getOnIEnable()) )
	{
		anExecutableForm->setOnIEnable(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnIEnable()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm->setOnIEnable(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				StatementConstructor::newComment( "begin<ienable> " +
						anExecutableForm->getFullyQualifiedNameID() ),

				anExecutableForm->getOnIEnable(),

				StatementConstructor::newComment( "end<ienable> " +
						anExecutableForm->getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	}

	/*
	 * onEnable
	 */
	if( theBehavior->hasOnEnable() &&
			StatementTypeChecker::doSomething(theBehavior->getOnEnable()) )
	{
		anExecutableForm->setOnEnable(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnEnable()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm->setOnEnable(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				StatementConstructor::newComment( "begin<enable> " +
						anExecutableForm->getFullyQualifiedNameID() ),

				anExecutableForm->getOnEnable(),

				StatementConstructor::newComment( "end<enable> " +
						anExecutableForm->getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	}

	// EXPAND IENABLE / ENABLE
	if( anExecutableForm->hasOnIEnable() )
	{
		if( anExecutableForm->hasOnEnable() )
		{
			if( not AvmCodeFactory::contains(anExecutableForm,
					anExecutableForm->getOnEnable(), AVM_OPCODE_IENABLE_INVOKE) )
			{
				anExecutableForm->setOnEnable(
						StatementConstructor::newCodeFlat(
								OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

								anExecutableForm->getOnIEnable(),

								anExecutableForm->getOnEnable() ) );
			}
			else
			{
				// EXPAND IENABLE
			}
		}
		else
		{
//			(*it)->setOnEnable( BFCode(OperatorManager::OPERATOR_IENABLE) );

			//Optimization
			anExecutableForm->setOnEnable( anExecutableForm->getOnIEnable() );
		}
	}



	/*
	 * onIDisable
	 */
	if( theBehavior->hasOnIDisable() &&
			StatementTypeChecker::doSomething(theBehavior->getOnIDisable()) )
	{
		anExecutableForm->setOnIDisable(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnIDisable()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm->setOnIDisable(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
				StatementConstructor::newComment( "begin<idisable> " +
						anExecutableForm->getFullyQualifiedNameID() ),

				anExecutableForm->getOnIDisable(),

				StatementConstructor::newComment( "end<idisable> " +
						anExecutableForm->getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	}

	/*
	 * onDisable
	 */
	if( theBehavior->hasOnDisable() &&
			StatementTypeChecker::doSomething(theBehavior->getOnDisable()) )
	{
		anExecutableForm->setOnDisable(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnDisable()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm->setOnDisable(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
				StatementConstructor::newComment( "begin<disable> " +
						anExecutableForm->getFullyQualifiedNameID() ),

				anExecutableForm->getOnDisable(),

				StatementConstructor::newComment( "end<disable> " +
						anExecutableForm->getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

		anExecutableForm->setOnDisable( StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				anExecutableForm->getOnDisable(),

				StatementConstructor::newCode(
						OperatorManager::OPERATOR_DISABLE_SELF) ) );
	}

	// EXPAND IDISABLE / DISABLE
	if( anExecutableForm->hasOnIDisable() )
	{
		if( anExecutableForm->hasOnDisable() )
		{
			if( not AvmCodeFactory::contains(anExecutableForm,
				anExecutableForm->getOnDisable(), AVM_OPCODE_IDISABLE_INVOKE) )
			{
				anExecutableForm->setOnDisable(
						StatementConstructor::newCodeFlat(
								OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

								anExecutableForm->getOnIDisable(),

								anExecutableForm->getOnDisable() ) );
			}
			else
			{
				// EXPAND IDISABLE
			}
		}
		else
		{
//			(*it)->setOnDisable( BFCode(OperatorManager::OPERATOR_IDISABLE) );

			//Optimization
			anExecutableForm->setOnDisable( StatementConstructor::newCodeFlat(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

					anExecutableForm->getOnIDisable(),

					StatementConstructor::newCode(
							OperatorManager::OPERATOR_DISABLE_SELF) ) );
		}

		anExecutableForm->setOnIDisable( StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				anExecutableForm->getOnIDisable(),

				StatementConstructor::newCode(
						OperatorManager::OPERATOR_DISABLE_SELF) ) );
	}


	/*
	 * onIAbort
	 */
	if( theBehavior->hasOnIAbort() &&
			StatementTypeChecker::doSomething(theBehavior->getOnIAbort()) )
	{
		anExecutableForm->setOnIAbort(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnIAbort()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm->setOnIAbort(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
				StatementConstructor::newComment( "begin<iabort> " +
						anExecutableForm->getFullyQualifiedNameID() ),

				anExecutableForm->getOnIAbort(),

				StatementConstructor::newComment( "end<iabort> " +
						anExecutableForm->getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	}

	/*
	 * onAbort
	 */
	if( theBehavior->hasOnAbort() &&
			StatementTypeChecker::doSomething(theBehavior->getOnAbort()) )
	{
		anExecutableForm->setOnAbort(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnAbort()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm->setOnAbort(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
				StatementConstructor::newComment( "begin<abort> " +
						anExecutableForm->getFullyQualifiedNameID() ),

				anExecutableForm->getOnAbort(),

				StatementConstructor::newComment( "end<abort> " +
						anExecutableForm->getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

		anExecutableForm->setOnAbort( StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				anExecutableForm->getOnAbort(),

				StatementConstructor::newCode(
						OperatorManager::OPERATOR_ABORT_SELF) ) );
	}

	// EXPAND IABORT / ABORT
	if( anExecutableForm->hasOnIAbort() )
	{
		if( anExecutableForm->hasOnAbort() )
		{
			if( not AvmCodeFactory::contains(anExecutableForm,
				anExecutableForm->getOnAbort(), AVM_OPCODE_IABORT_INVOKE) )
			{
				anExecutableForm->setOnAbort(
						StatementConstructor::newCodeFlat(
								OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

								anExecutableForm->getOnIAbort(),

								anExecutableForm->getOnAbort() ) );
			}
			else
			{
				// EXPAND IABORT
			}
		}
		else
		{
//			(*it)->setOnAbort( BFCode(OperatorManager::OPERATOR_IABORT) );

			//Optimization
			anExecutableForm->setOnAbort( StatementConstructor::newCodeFlat(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

					anExecutableForm->getOnIAbort(),

					StatementConstructor::newCode(
							OperatorManager::OPERATOR_ABORT_SELF) ) );
		}

		anExecutableForm->setOnIAbort( StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				anExecutableForm->getOnIAbort(),

				StatementConstructor::newCode(
						OperatorManager::OPERATOR_ABORT_SELF) ) );
	}


	/*
	 * onIRun
	 */
	if( theBehavior->hasOnIRun() &&
			StatementTypeChecker::doSomething(theBehavior->getOnIRun()) )
	{
		anExecutableForm->setOnIRun(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnIRun()) );
	}

	/*
	 * onRun
	 */
	if( theBehavior->hasOnRun() &&
			StatementTypeChecker::doSomething(theBehavior->getOnRun()) )
	{
		anExecutableForm->setOnRun(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnRun()) );
	}

	/*
	 * onRtc
	 */
	if( theBehavior->hasOnRtc() &&
			StatementTypeChecker::doSomething(theBehavior->getOnRtc()) )
	{
		anExecutableForm->setOnRtc(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnRtc()) );
	}


	/*
	 * onSchedule
	 */
	if( theBehavior->hasOnSchedule() )
	{
		if( StatementTypeChecker::isEmptySchedule(theBehavior->getOnSchedule()) )
		{
			//!! NOTHING
		}
		else
		{
			anExecutableForm->setOnSchedule(
					compileSchedulerRoutine(
							anExecutableForm,
							theBehavior->getOnSchedule() ) );
		}
	}

	/*
	 * onConcurrency
	 */
	if( theBehavior->hasOnConcurrency() )
	{
		if( StatementTypeChecker::isEmptySchedule(theBehavior->getOnConcurrency()) )
		{
			anExecutableForm->setOnConcurrency( theBehavior->getOnConcurrency() );
		}
		else
		{
			anExecutableForm->setOnConcurrency(
					mAvmcodeCompiler.compileStatement(
							anExecutableForm, theBehavior->getOnConcurrency()) );
		}
	}
	else if( StatementTypeChecker::isSchedule(theBehavior->getOnSchedule()) )
	{
		anExecutableForm->setOnConcurrency(
				theBehavior->getOnSchedule().getOperator() );
	}


	/*
	 * onSynchronize
	 */
	if( theBehavior->hasOnSynchronize() )
	{
		anExecutableForm->setOnSynchronize(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnSynchronize()) );
	}


	/*
	 * other user Routines
	 */
	BehavioralPart::const_routine_iterator it = theBehavior->routine_begin();
	BehavioralPart::const_routine_iterator endIt = theBehavior->routine_end();
	for( ; it != endIt ; ++it )
	{
		anExecutableForm->saveProgram(
				mAvmcodeCompiler.compileRoutine(this, anExecutableForm, it) );
	}


//AVM_OS_TRACE << TAB << ">| compiling<machine>: "
//		<< str_header( aMachine ) << std::endl << std::endl;
}


/**
 * compile
 * executable procedure
 */
void Compiler::compileProcedure(ExecutableForm * anExecutableForm)
{
	// Compile data & all machine MOE program
	compileBaseMachine(anExecutableForm);

	const Machine * aProcedure = anExecutableForm->getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aProcedure ) << std::endl;

	// PUSH MOC
	WObject * moc_transition = NULL;//aProcedure::getTransitionMoc();
	if( moc_transition != NULL )
	{
		mTransitionCompiler.pushMoc(moc_transition);
	}


	// Compile all specific statemachine
	if( aProcedure->getSpecifier().isStateBasic() )
	{
		compileStatemachineBasic(anExecutableForm);
	}

	else if( aProcedure->getSpecifier().isMocStateTransitionStructure() )
	{
		compileExecutableMocStateTransitionStructure(anExecutableForm);
	}
	else if( aProcedure->getSpecifier().isMocCompositeStructure() )
	{
		compileExecutableMocCompositeStructure(anExecutableForm);
	}

	else
	{
		// MOC Attribute for mutable Schedule
		anExecutableForm->setMutableSchedule(
				anExecutableForm->hasOnSchedule() );

		/*
		 * Compiling communication
		 */
		bool hasSynchronizeMachine = false;
		bool hasUpdateBuffer = false;

		mComCompiler.compileCommunication(anExecutableForm,
				hasUpdateBuffer, hasSynchronizeMachine);

		if( anExecutableForm->hasOnRun() )
		{
			//!! NOTHING
		}
		else if( anExecutableForm->hasOnRtc() )
		{
			anExecutableForm->setOnRun(StatementConstructor::newCode(
					OperatorManager::OPERATOR_RTC));
		}

		else if( anExecutableForm->hasOnSchedule() )
		{
			anExecutableForm->setOnRun( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SCHEDULE_INVOKE));
		}
	}

	// POP MOC
	if( moc_transition != NULL )
	{
		mTransitionCompiler.popMoc();
	}

//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aProcedure ) << std::endl;
}


/**
 * compile
 * executable machine
 */
void Compiler::compileMachine(ExecutableForm * anExecutableForm)
{
//AVM_OS_TRACE << TAB << "<| compiling<machine>: "
//		<< str_header( aMachine ) << std::endl;

	// COMPILE PROGRAM
	if( anExecutableForm->hasProgram() )
	{
		AvmProgram * aProgram;

		avm_size_t offset = 0;
		for( ; offset < anExecutableForm->getProgram().size() ; ++offset )
		{
			aProgram = anExecutableForm->getProgram().rawAt(offset);

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<program>: "
			<< aProgram->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

			mProgramCompiler.compileProgram( aProgram );

AVM_IF_DEBUG_FLAG( COMPILING )
//	(*itProg)->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| compiling<program>: "
			<< aProgram->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
		}
	}


	const Machine * aMachine = anExecutableForm->getAstMachine();

	// Compile all specific machine
	if( aMachine->getSpecifier().isMocStateTransitionStructure() )
	{
		compileExecutableMocStateTransitionStructure(anExecutableForm);
	}
	else if( aMachine->getSpecifier().isMocCompositeStructure() )
	{
		compileExecutableMocCompositeStructure(anExecutableForm);
	}
	else
	{
		// MOC Attribute for mutable Schedule
		anExecutableForm->setMutableSchedule(
				anExecutableForm->hasOnSchedule() );

		/*
		 * Compiling communication
		 */
		bool hasSynchronizeMachine = false;
		bool hasUpdateBuffer = false;

		mComCompiler.compileCommunication(anExecutableForm,
				hasUpdateBuffer, hasSynchronizeMachine);

		if( anExecutableForm->hasOnRun() )
		{
			//!! NOTHING
		}
		else if( anExecutableForm->hasOnRtc() )
		{
			anExecutableForm->setOnRun(StatementConstructor::newCode(
					OperatorManager::OPERATOR_RTC));
		}

		else if( anExecutableForm->hasOnSchedule() )
		{
			anExecutableForm->setOnRun( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SCHEDULE_INVOKE));
		}
	}

//AVM_OS_TRACE << TAB << ">| compiling<machine>: "
//		<< str_header( aMachine ) << std::endl << std::endl;
}


/**
 * compile
 * specification
 */
void Compiler::compileSystem(ExecutableForm * anExecutableForm)
{
	const System * aSystem = anExecutableForm->getAstSystem();

//AVM_OS_TRACE << TAB << "<| compiling<system>: "
//		<< aSystem->getFullyQualifiedNameID() << std::endl;

	// Compile all specific machine
	if( aSystem->getSpecifier().isMocStateTransitionStructure() )
	{
		compileExecutableMocStateTransitionStructure(anExecutableForm);
	}
	else //if( aSystem->getSpecifier().isMocCompositeStructure()
		//|| (not aSystem->hasRunnableBehavior()) )
	{
		compileExecutableMocCompositeStructure(anExecutableForm);
	}

	if( not anExecutableForm->hasOnInit() )
	{
		anExecutableForm->setOnInit( StatementConstructor::nopCode() );
	}

	if( anExecutableForm->hasOnIRun() )
	{
		if( anExecutableForm->hasOnRun() )
		{
			anExecutableForm->setOnRun(
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE_SIDE,
							anExecutableForm->getOnIRun(),
							anExecutableForm->getOnRun()) );
		}
		else
		{
			anExecutableForm->setOnRun( anExecutableForm->getOnIRun() );
		}
	}
	else if( (not anExecutableForm->hasOnSchedule())
			&& (not anExecutableForm->hasOnRun())  )
	{
		anExecutableForm->setOnRun( StatementConstructor::nopCode() );
	}


//AVM_OS_TRACE << TAB << ">| compiling<system>: "
//		<< aSystem->getFullyQualifiedNameID() << std::endl << std::endl;
}




/**
 * compile
 * statemachine
 */
void Compiler::compileStatemachine(ExecutableForm * anExecutableForm)
{
	const Machine * aStatemachine = anExecutableForm->getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;

	// PUSH MOC
	WObject * moc_transition = NULL;//aStatemachine::getTransitionMoc();
	if( moc_transition != NULL )
	{
		mTransitionCompiler.pushMoc(moc_transition);
	}

	// Compile all specific statemachine
	if( aStatemachine->getSpecifier().hasFamilyPseudostateEnding() )
	{
		compilePseudostateEnding(anExecutableForm);
	}
	else if( aStatemachine->getSpecifier().hasPseudostateMocHISTORY() )
	{
		compileStatemachineHistory(anExecutableForm);
	}
	else  if( aStatemachine->getSpecifier().isPseudostate() )
	{
		compileStatemachinePseudo(anExecutableForm);
	}

	else if( aStatemachine->getSpecifier().isStateBasic() )
	{
		compileStatemachineBasic(anExecutableForm);
	}

	else if( aStatemachine->getSpecifier().isMocStateTransitionStructure() )
	{
		compileExecutableMocStateTransitionStructure(anExecutableForm);
	}
	else if( aStatemachine->getSpecifier().isMocCompositeStructure() )
	{
		compileExecutableMocCompositeStructure(anExecutableForm);
	}
	else if( aStatemachine->getSpecifier().isComponentProcedure() )
	{
		compileExecutableMocCompositeStructure(anExecutableForm);
	}

	else
	{
		incrErrorCount();
		aStatemachine->errorLocation(AVM_OS_WARN)
				<< "Unexpected statemachine type << "
				<< str_header( aStatemachine ) << " >>"
				<< std::endl << std::endl;
	}


	// COMPILE TRANSITION
	if( anExecutableForm->hasTransition() )
	{
		AvmTransition * aTransition;

		avm_size_t offset = 0;
		for( ; offset < anExecutableForm->getTransition().size() ; ++offset )
		{
			aTransition = anExecutableForm->getTransition().rawAt(offset);

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<transition>: "
			<< aTransition->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

			mTransitionCompiler.compileTransition( aTransition );

AVM_IF_DEBUG_FLAG( COMPILING )
//	(*itProg)->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| compiling<transition>: "
			<< aTransition->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
		}

		if( anExecutableForm->getSpecifier().hasFeatureInputEnabled() )
		{
			computeInputEnabledCom( anExecutableForm );
		}
	}


	// COMPILE PROGRAM
	if( anExecutableForm->hasProgram() )
	{
		AvmProgram * aProgram;

		avm_size_t offset = 0;
		for( ; offset < anExecutableForm->getProgram().size() ; ++offset )
		{
			aProgram = anExecutableForm->getProgram().rawAt(offset);

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<program>: "
			<< aProgram->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

			mProgramCompiler.compileProgram( aProgram );

AVM_IF_DEBUG_FLAG( COMPILING )
//	(*itProg)->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| compiling<program>: "
			<< aProgram->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
		}

		if( anExecutableForm->getSpecifier().hasFeatureInputEnabled() )
		{
			computeInputEnabledCom( anExecutableForm );
		}
	}


	// POP MOC
	if( moc_transition != NULL )
	{
		mTransitionCompiler.popMoc();
	}

//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;
}


void Compiler::compileExecutableMocCompositeStructure(
		ExecutableForm * anExecutableForm)
{
	const Machine * anExecutableSpec = anExecutableForm->getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling executable< moc: and >: "
//		<< str_header( anExecutableSpec ) << std::endl;

	bool hasInstanceStatic = anExecutableSpec->hasMachine();
	bool hasSynchronizeMachine = false;
	bool hasUpdateBuffer = false;


	// MOC Attribute for mutable Schedule
	anExecutableForm->setMutableSchedule( false );

	/**
	 * compile all routines which defined the executable's behavior
	 */
	compileAllBehavioralRoutines( anExecutableForm );

	/*
	 * Compiling communication
	 */
	mComCompiler.compileCommunication(anExecutableForm,
			hasUpdateBuffer, hasSynchronizeMachine);


	/*
	 * OnRun
	 * whith high priority order
	 *
	 * StrongAbort Transition
	 * OnIRun
	 * ( Simple Transition or submachine ) depend on MOC
	 * WeakAbort Transition
	 * NormalTerminaison Transition
	 */

	BFCode onRunProgram;

	// Update Buffer
	if( hasInstanceStatic )
	{
		if( hasSynchronizeMachine ) 	// only if has RDV protocol
		{
			anExecutableForm->setRdvCommunication( hasSynchronizeMachine );

			setRdvScheduling( anExecutableForm );
		}

		if( anExecutableForm->hasOnRun() )
		{
			onRunProgram = anExecutableForm->getOnRun();

			anExecutableForm->setOnRun( BFCode::REF_NULL );

			if( not AvmCodeFactory::contains(anExecutableForm,
					onRunProgram, AVM_OPCODE_SCHEDULE_INVOKE) )
			{
				if( (not anExecutableForm->hasOnRtc()) &&
						AvmCodeFactory::contains(anExecutableForm,
								onRunProgram, AVM_OPCODE_RTC) )
				{
					anExecutableForm->setOnRtc(
							StatementConstructor::newCode(
								OperatorManager::OPERATOR_SCHEDULE_INVOKE) );
				}
				else if( anExecutableForm->hasOnSchedule()
						|| anExecutableForm->isMutableSchedule() )
				{
					onRunProgram = StatementConstructor::newCodeFlat(
							OperatorManager::OPERATOR_SEQUENCE, onRunProgram,
							StatementConstructor::newCode(
								OperatorManager::OPERATOR_SCHEDULE_INVOKE) );
				}
			}
		}
		else if( anExecutableForm->hasOnSchedule()
				|| anExecutableForm->isMutableSchedule() )
		{
			onRunProgram = StatementConstructor::newCode(
					OperatorManager::OPERATOR_SCHEDULE_INVOKE);
		}

		if( hasUpdateBuffer )  // only if has BROADCAST protocol
		{
			onRunProgram = StatementConstructor::newCode(
					OperatorManager::OPERATOR_UPDATE_BUFFER, onRunProgram);
		}
	}

	if( anExecutableSpec->hasOutgoingTransition() )
	{
		// Compile Statemachine Transition
		mTransitionCompiler.compileStatemachineTransition(
				anExecutableForm, onRunProgram );
	}
	else if( onRunProgram.valid() )
	{
		anExecutableForm->setOnRun( onRunProgram );
	}
	else if( anExecutableForm->hasOnIRun() )
	{
		anExecutableForm->setOnRun( StatementConstructor::nopCode() );
	}


//AVM_OS_TRACE << TAB << ">| compiling executable< moc: and >: "
//		<< str_header( anExecutableSpec ) << std::endl;
}


void Compiler::compileExecutableMocStateTransitionStructure(
		ExecutableForm * anExecutableForm)
{
	const Machine * anExecutableSpec = anExecutableForm->getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling executable< moc: and >: "
//		<< str_header( anExecutableSpec ) << std::endl;

	bool hasSynchronizeMachine = false;
	bool hasUpdateBuffer = false;

//	/*
//	 * Compiling program
//	 */
//
//	TableOfAvmProgram::iterator it = anExecutableForm->getProgram().begin();
//	for( ; it != anExecutableForm->getProgram().end() ; ++it )
//	{
//		compileProgram(anExecutableForm, (*it));
//	}


	// MOC Attribute for mutable Schedule
	anExecutableForm->setMutableSchedule( true );

	if( anExecutableSpec->hasMachine() )
	{
		/*
		 * ON_INIT
		 * ON_ENABLE
		 */
		// non determinism: simulation of enabling for
		// each [ start ] state or [ initial ] state ...
		BFCode onInitCode( OperatorManager::OPERATOR_NONDETERMINISM );

		BFCode onEnableCode( OperatorManager::OPERATOR_NONDETERMINISM );

		BFCode onScheduleCode( OperatorManager::OPERATOR_NONDETERMINISM );

		bool hasnotOwnedPseudostateHistory = (not anExecutableSpec->
				getOwnedElementsSpecifier().hasPseudostateMocHISTORY());

		bool hasnotOwnedPseudostateInitialOrStateStart =
				(not anExecutableSpec->
						getOwnedElementsSpecifier().hasMocINITIAL_START());

		TableOfSymbol::const_iterator itMachine =
				anExecutableForm->instance_static_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm->instance_static_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			const Specifier & itSpecifier =
					(*itMachine).getExecutable()->getSpecifier();

			if( itSpecifier.isPseudostateInitialOrStateStart() )
			{
				onInitCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_INIT, (*itMachine) ) );

				if( hasnotOwnedPseudostateHistory )
				{
					onEnableCode->append( StatementConstructor::newCode(
							OperatorManager::OPERATOR_ENABLE_INVOKE,
							(*itMachine) ) );
				}

				onScheduleCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_RUN, (*itMachine)) );
			}
			else if( itSpecifier.hasPseudostateHistory() )
			{
				onEnableCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_ENABLE_INVOKE,
						(*itMachine) ) );
			}
			else if( hasnotOwnedPseudostateInitialOrStateStart )
			{
				onInitCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_INIT, (*itMachine) ) );

				if( hasnotOwnedPseudostateHistory )
				{
					onEnableCode->append( StatementConstructor::newCode(
							OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
							StatementConstructor::newCode(
									OperatorManager::OPERATOR_ENABLE_SET,
									(*itMachine) ),
							StatementConstructor::newCode(
									OperatorManager::OPERATOR_ENABLE_INVOKE,
									(*itMachine) ) ) );
				}

				onScheduleCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_RUN, (*itMachine) ) );
			}
		}

		// ON INIT
		if( onInitCode->nonempty() )
		{
			anExecutableForm->setOnInit( StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					anExecutableForm->getOnInit(),
					(onInitCode->singleton() ?
							onInitCode->first().bfCode() : onInitCode) ) );
		}

		// ON ENABLE
		if( onEnableCode->nonempty() )
		{
			anExecutableForm->setOnEnable( StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					anExecutableForm->getOnEnable(),
					(onEnableCode->singleton() ?
							onEnableCode->first().bfCode() : onEnableCode) ) );
		}

		/**
		 * ON SCHEDULE
		 */
		if( anExecutableForm->hasOnSchedule() )
		{
			incrErrorCount();
			anExecutableSpec->errorLocation(AVM_OS_WARN)
					<< "Unexpected a State-Transition-System << "
					<< str_header( anExecutableSpec )
					<< " >> with user schedule code: "
					<< anExecutableForm->getOnSchedule() << std::endl;
		}
		else if( onScheduleCode->nonempty() )
		{
			anExecutableForm->setOnSchedule( StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					anExecutableForm->getOnSchedule(),
					(onScheduleCode->singleton() ?
						onScheduleCode->first().bfCode() : onScheduleCode) ) );
		}
		else if( anExecutableForm->hasOneInstanceStatic() )
		{
			anExecutableForm->setOnSchedule( StatementConstructor::newCode(
					OperatorManager::OPERATOR_RUN,
					anExecutableForm->firstInstanceStatic() ) );
		}

		/*
		 * ON_DISABLE
		 */
		if( anExecutableForm->hasOnDisable() )
		{
			anExecutableForm->setOnDisable(
					StatementConstructor::newCodeFlat(
							OperatorManager::OPERATOR_SEQUENCE,
							StatementConstructor::newCode(
									OperatorManager::OPERATOR_DISABLE_CHILD),
							anExecutableForm->getOnDisable() ) );
		}
		else
		{
			anExecutableForm->setOnDisable( StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_DISABLE_CHILD),
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_DISABLE_SELF) ) );
		}
	}

	/*
	 * Compiling communication
	 */
	mComCompiler.compileCommunication(anExecutableForm,
			hasUpdateBuffer, hasSynchronizeMachine);


	/*
	 * OnRun
	 * whith high priority order
	 *
	 * StrongAbort Transition
	 * OnIRun
	 * ( Simple Transition or submachine ) depend on MOC
	 * WeakAbort Transition
	 * NormalTerminaison Transition
	 */

	BFCode onRunProgram;

	// Update Buffer
	if( anExecutableSpec->hasMachine() )
	{
		if( hasSynchronizeMachine ) 	// only if has RDV protocol
		{
			anExecutableForm->setRdvCommunication( hasSynchronizeMachine );

			setRdvScheduling( anExecutableForm );
		}

		if( anExecutableForm->hasOnRun() )
		{
			onRunProgram = anExecutableForm->getOnRun();

			if( AvmCodeFactory::contains(anExecutableForm,
					onRunProgram, AVM_OPCODE_SCHEDULE_INVOKE) )
			{
				//!!NOTHING
			}
			else if( (not anExecutableForm->hasOnRtc())
					&& AvmCodeFactory::contains(anExecutableForm,
							onRunProgram, AVM_OPCODE_RTC) )
			{
				anExecutableForm->setOnRtc(
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_SCHEDULE_INVOKE) );
			}
			else
			{
				onRunProgram = StatementConstructor::newCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE, onRunProgram,
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_SCHEDULE_INVOKE) );
			}

			anExecutableForm->setOnRun( BFCode::REF_NULL );
		}
		else
		{
			onRunProgram = StatementConstructor::newCode(
					OperatorManager::OPERATOR_SCHEDULE_INVOKE);
		}

		if( hasUpdateBuffer )  // only if has BROADCAST protocol
		{
			onRunProgram = StatementConstructor::newCode(
					OperatorManager::OPERATOR_UPDATE_BUFFER, onRunProgram);
		}
	}

	if( anExecutableSpec->hasOutgoingTransition() )
	{
		// Compile Statemachine Transition
		mTransitionCompiler.compileStatemachineTransition(
				anExecutableForm, onRunProgram);
	}
	else if( onRunProgram.valid() )
	{
		anExecutableForm->setOnRun( onRunProgram );
	}
	else if( anExecutableForm->hasOnIRun() )
	{
		anExecutableForm->setOnRun( StatementConstructor::nopCode() );
	}


//AVM_OS_TRACE << TAB << ">| compiling executable< moc: and >: "
//		<< str_header( anExecutableSpec ) << std::endl;
}


void Compiler::compilePseudostateEnding(ExecutableForm * anExecutableForm)
{
	const Machine * aStatemachine = anExecutableForm->getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;

	// MOC Attribute for mutable Schedule
	anExecutableForm->setMutableSchedule( false );

	/*
	 * ON ENABLE
	 */
	BFCode onTerminalCode;

	if( aStatemachine->getSpecifier().isPseudostateTerminal() )
	{
		onTerminalCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_DESTROY, ExecutableLib::MACHINE_PARENT);
	}
	else //if( aStatemachine->getSpecifier().isPseudostateReturn() )
	{
		onTerminalCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_FINAL);
	}

	anExecutableForm->setOnEnable( StatementConstructor::xnewCodeFlat(
			OperatorManager::OPERATOR_SEQUENCE,
			anExecutableForm->getOnEnable(), onTerminalCode) );

	if( aStatemachine->hasOutgoingTransition() )
	{
		incrErrorCount();
		aStatemachine->errorLocation(AVM_OS_WARN)
				<< "Unexpected state< terminal > << "
				<< str_header( aStatemachine )
				<< " >> with outgoing transitions"
				<< std::endl << std::endl;
	}

//aStatemachine->toStream(AVM_OS_TRACE << TAB);
//anExecutableForm->toStream(AVM_OS_TRACE << TAB);
//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;
}


void Compiler::compileStatemachineHistory(ExecutableForm * anExecutableForm)
{
	const Machine * aStatemachine = anExecutableForm->getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;

	// MOC Attribute for mutable Schedule
	anExecutableForm->setMutableSchedule( false );

	if( aStatemachine->hasOutgoingTransition() )
	{
		// Compile Statemachine Transition
		mTransitionCompiler.compileStatemachineTransition(
				anExecutableForm , anExecutableForm->getOnRun());
	}

	BFCode onEnableCode = StatementConstructor::newCode(
			OperatorManager::OPERATOR_RUN);

	BFCode onHistoryCode = StatementConstructor::newCode(
			aStatemachine->getSpecifier().isPseudostateDeepHistory() ?
					OperatorManager::OPERATOR_DEEP_HISTORY_INVOKE :
					OperatorManager::OPERATOR_SHALLOW_HISTORY_INVOKE,
			ExecutableLib::MACHINE_PARENT);

	if( anExecutableForm->hasOnRun() )
	{
		anExecutableForm->setOnRun( StatementConstructor::xnewCodeFlat(
				OperatorManager::OPERATOR_PRIOR_GT,
				anExecutableForm->getOnRun(), onHistoryCode) );
	}
	else if( anExecutableForm->hasOnIRun() )
	{
		anExecutableForm->setOnRun( onHistoryCode );
	}
	else
	{
		onEnableCode = onHistoryCode;
	}


	/*
	 * ON INIT
	 * ON ENABLE
	 */
	// this is aStatemachine->getSpecifier().isPseudostate()
	// ON INIT
	anExecutableForm->setOnInit( StatementConstructor::xnewCodeFlat(
			OperatorManager::OPERATOR_SEQUENCE,
			anExecutableForm->getOnInit(), onEnableCode) );

	// ON ENABLE
	anExecutableForm->setOnEnable( StatementConstructor::xnewCodeFlat(
			OperatorManager::OPERATOR_SEQUENCE,
			anExecutableForm->getOnEnable(), onEnableCode) );

//aStatemachine->toStream(AVM_OS_TRACE << TAB);
//anExecutableForm->toStream(AVM_OS_TRACE << TAB);
//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;
}


void Compiler::compileStatemachinePseudo(ExecutableForm * anExecutableForm)
{
	const Machine * aStatemachine = anExecutableForm->getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;

	// MOC Attribute for mutable Schedule
	anExecutableForm->setMutableSchedule( false );

	/*
	 * ON INIT
	 * ON ENABLE
	 */
	BFCode onEnableCode  = StatementConstructor::newCode(
			OperatorManager::OPERATOR_RUN);

	// ON INIT
	if( aStatemachine->getSpecifier().isPseudostateInitial()
		&& anExecutableForm->hasOnEnable() )
	{
		anExecutableForm->setOnInit(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						anExecutableForm->getOnInit(),
						anExecutableForm->getOnEnable(), onEnableCode) );
	}
	else
	{
		anExecutableForm->setOnInit( StatementConstructor::xnewCodeFlat(
				OperatorManager::OPERATOR_SEQUENCE,
				anExecutableForm->getOnInit(), onEnableCode) );
	}

	anExecutableForm->setOnEnable(
			StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					anExecutableForm->getOnEnable(), onEnableCode) );



	/*
	 * Schedule State Transition
	 */
	if( aStatemachine->getSpecifier().isPseudostateFork() )
	{
		if( aStatemachine->hasOutgoingTransition() &&
			aStatemachine->getBehavior()->
					getOutgoingTransitions().populated() )
		{
			// Schedule State< fork > Transition
			mTransitionCompiler.compileStateForkOutputTransition(
					anExecutableForm, anExecutableForm->getOnRun());
		}
		else
		{
			incrErrorCount();
			aStatemachine->errorLocation(AVM_OS_WARN)
					<< "Unexpected pseudostate< fork > << "
					<< str_header( aStatemachine )
					<< " >> with less than 2 outgoing transitions"
					<< std::endl << std::endl;
		}
	}

	else if( aStatemachine->getSpecifier().isPseudostateJoin() )
	{
		if( aStatemachine->hasIncomingTransition()
			&& aStatemachine->getBehavior()->
					getIncomingTransitions().populated() )
		{
			// SYnchronize incoming Transition
			mTransitionCompiler.compileStateJoinInputTransition(
					anExecutableForm );
		}
		else
		{
			incrErrorCount();
			aStatemachine->errorLocation(AVM_OS_WARN)
					<< "Unexpected pseudostate< join > << "
					<< str_header( aStatemachine )
					<< " >> with less than 2 incoming transitions"
					<< std::endl << std::endl;
		}


		if( aStatemachine->hasOutgoingTransition() )
		{
			// Compile Statemachine Transition
			mTransitionCompiler.compileStatemachineTransition(
					anExecutableForm , anExecutableForm->getOnRun());
		}
		else
		{
			incrErrorCount();
			aStatemachine->errorLocation(AVM_OS_WARN)
					<< "Unexpected pseudostate< join > << "
					<< str_header( aStatemachine )
					<< " >> without outgoing transitions"
					<< std::endl << std::endl;
		}
	}


	else if( aStatemachine->hasOutgoingTransition() )
	{
		// Compile Statemachine Transition
		mTransitionCompiler.compileStatemachineTransition(
				anExecutableForm , anExecutableForm->getOnRun() );
	}


	if( not anExecutableForm->hasOnRun() )
	{
		if( not aStatemachine->getSpecifier().hasFamilyPseudostateENDING() )
		{
			incrWarningCount();
			aStatemachine->warningLocation(AVM_OS_WARN)
					<< "No eval code for << " << str_header( aStatemachine )
					<< " >> which is not TERMINAL or RETURN moc!" << std::endl;
		}
		else if( aStatemachine->getSpecifier().isPseudostateInitial() )
		{
			incrErrorCount();
			aStatemachine->errorLocation(AVM_OS_WARN)
					<< "No eval code for << " << str_header( aStatemachine )
					<< " >> which is an INITIAL state!!!" << std::endl;

			anExecutableForm->setOnRun( StatementConstructor::nopCode() );
		}
		AVM_OS_WARN << std::endl;

		if( anExecutableForm->hasOnIRun() )
		{
			anExecutableForm->setOnRun( StatementConstructor::nopCode() );
		}
	}

//aStatemachine->toStream(AVM_OS_TRACE << TAB);
//anExecutableForm->toStream(AVM_OS_TRACE << TAB);
//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;
}


void Compiler::compileStatemachineBasic(ExecutableForm * anExecutableForm)
{
	const Machine * aStatemachine = anExecutableForm->getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;

	// MOC Attribute for mutable Schedule
	anExecutableForm->setMutableSchedule( false );


	// ON INIT
	if( aStatemachine->getSpecifier().isStateStart()
		&& anExecutableForm->hasOnEnable() )
	{
		anExecutableForm->setOnInit(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						anExecutableForm->getOnInit(),
						anExecutableForm->getOnEnable()) );
	}


	/*
	 * Schedule State Transition
	 */
	if( aStatemachine->getSpecifier().isStateFinal() )
	{
		anExecutableForm->setOnEnable(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						anExecutableForm->getOnEnable(),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_FINAL)) );

		if( aStatemachine->hasOutgoingTransition() )
		{
			incrErrorCount();
			aStatemachine->errorLocation(AVM_OS_WARN)
					<< "Unexpected state< final > << "
					<< str_header( aStatemachine )
					<< " >> with outgoing transitions"
					<< std::endl << std::endl;
		}
	}


	else if( aStatemachine->hasOutgoingTransition() )
	{
		// Compile Statemachine Transition
		mTransitionCompiler.compileStatemachineTransition(
				anExecutableForm , anExecutableForm->getOnRun() );
	}

	if( aStatemachine->getSpecifier().isStateSync() )
	{
		Variable * aVar = new Variable(
				const_cast< Machine * >( aStatemachine ),
				Modifier::PROPERTY_PUBLIC_VOLATILE_MODIFIER,
				TypeManager::INTEGER,
				aStatemachine->getNameID() + "#syncVar" );

		const_cast< Machine * >( aStatemachine )->
				getPropertyPart().saveOwnedVariable( aVar );

		InstanceOfData * syncInstance = new InstanceOfData(
				IPointerDataNature::POINTER_STANDARD_NATURE,
				anExecutableForm, aVar, TypeManager::INTEGER,
				anExecutableForm->getDataSize(),
				Modifier::PROPERTY_PUBLIC_VOLATILE_MODIFIER);
//!![MIGRATION]:MODIFIER
//				Modifier::PROPERTY_VOLATILE_FEATURE);
		syncInstance->setValue( ExpressionConstant::INTEGER_ZERO );

		const BF & syncVar = anExecutableForm->saveData(syncInstance);


		BFCode incrSyncVar = StatementConstructor::newCode(
				OperatorManager::OPERATOR_ASSIGN, syncVar,
				StatementConstructor::newCode(
						OperatorManager::OPERATOR_PLUS, syncVar,
						ExpressionConstant::INTEGER_ONE) );

		anExecutableForm->setOnEnable(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
						anExecutableForm->getOnEnable(), incrSyncVar) );


		BFCode decrSyncVar = StatementConstructor::newCode(
				OperatorManager::OPERATOR_ASSIGN, syncVar,
				StatementConstructor::newCode(
						OperatorManager::OPERATOR_PLUS, syncVar,
						ExpressionConstant::INTEGER_MINUS_ONE) );

		anExecutableForm->setOnDisable(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
						anExecutableForm->getOnDisable(), decrSyncVar) );


		BFCode guardSyncVar = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD,
				StatementConstructor::newCode(
						OperatorManager::OPERATOR_GT, syncVar,
						ExpressionConstant::INTEGER_ZERO) );

		anExecutableForm->setOnRun(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						guardSyncVar, anExecutableForm->getOnRun()) );
	}


	if( anExecutableForm->hasOnIRun()
		&& (not anExecutableForm->hasOnRun()) )
	{
		anExecutableForm->setOnRun( StatementConstructor::nopCode() );
	}

	if( (not anExecutableForm->hasOnRun())
		&& (not aStatemachine->getSpecifier().isStateFinal()) )
	{
		incrWarningCount();
		aStatemachine->warningLocation(AVM_OS_WARN)
				<< "No eval code for << " << str_header( aStatemachine )
				<< " >> which is not FINAL!"
				<< std::endl << std::endl;
	}

//aStatemachine->toStream(AVM_OS_TRACE << TAB);
//anExecutableForm->toStream(AVM_OS_TRACE << TAB);
//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;
}


/**
 * compile
 * statemachine input_enabled
 */

void Compiler::removeSubmachineInputEnabledCode(
		ExecutableForm * anExecutableForm)
{
	if( anExecutableForm->hasInstanceStatic() )
	{
		TableOfSymbol::const_iterator itMachine =
				anExecutableForm->instance_static_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm->instance_static_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (*itMachine).machine().
					getSpecifier().isDesignPrototypeStatic()
				&& (*itMachine).getExecutable()->hasOnRun() )
			{
				if( (*itMachine).getExecutable()->
						getOnRun()->isOpCode( AVM_OPCODE_INPUT_ENABLED ) )
				{
					BFCode newCode = (*itMachine).getExecutable()->
							getOnRun()->first().bfCode();
					(*itMachine).getExecutable()->setOnRun( newCode );
				}

				removeSubmachineInputEnabledCode(
						(*itMachine).getExecutable() );
			}
		}
	}
}


void Compiler::computeInputEnabledCom(ExecutableForm * anExecutableForm)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT(
			anExecutableForm->getSpecifier().hasFeatureInputEnabled() )
			<< "Unexpected a non INPUT_ENABLED Executable !!!"
			<< SEND_EXIT;

	// input enabled running code
	CommunicationDependency::computeInputEnabledCom(
			anExecutableForm, anExecutableForm->getOnRun() );

	if( anExecutableForm->getSpecifier().isState() )
	{
		computeInputEnabledBuffer( anExecutableForm );

		if( anExecutableForm->getInputEnabledBuffer().populated() )
		{
			incrErrorCount();
			anExecutableForm->getAstMachine()->errorLocation(AVM_OS_WARN)
					<< "InputEnabled:> NO SUPPORT for multiple buffer "
							"at runtime for << "
					<< str_header( anExecutableForm->getAstMachine() )
					<< " >> !" << std::endl;

			AVM_OS_FATAL_ERROR_EXIT << "Expect the Future !!!" << SEND_EXIT;
		}
		else if( anExecutableForm->getInputEnabledBuffer().empty() )
		{
			incrErrorCount();
			anExecutableForm->getAstMachine()->errorLocation(AVM_OS_WARN)
					<< "InputEnabled:> Unfound runtime buffer for << "
					<< str_header( anExecutableForm->getAstMachine() )
					<< " >> !" << std::endl;
		}

		if( anExecutableForm->hasContainer() &&
			anExecutableForm->getExecutableContainer()->hasTransition() )
		{
			//!! NOTHING
		}
		else
		{
			anExecutableForm->setOnRun( StatementConstructor::newCode(
					OperatorManager::OPERATOR_INPUT_ENABLED,
					anExecutableForm->getOnRun() ));

			removeSubmachineInputEnabledCode( anExecutableForm );
		}
	}
}


void Compiler::computeInputEnabledBuffer(ExecutableForm * anExecutableForm)
{
	for( ExecutableForm * tmpExec = anExecutableForm ; tmpExec != NULL ;
			tmpExec = tmpExec->getExecutableContainer() )
	{
		if( tmpExec->hasBuffer() )
		{
			const TableOfSymbol & bufferTable = tmpExec->getBuffer();
			for( avm_size_t offset = 0 ; offset < bufferTable.size() ; ++offset )
			{
				anExecutableForm->addInputEnabledBuffer(
						bufferTable[ offset ].rawBuffer());
			}
			return;
		}

		if( tmpExec->hasRouter4This() )
		{
			return;
		}

		if( tmpExec->hasRouter4Instance() )
		{
			return;
		}

		if( tmpExec->hasRouter4Model() )
		{
			return;
		}
	}
}


/**
 * compile statemachine
 * initialization
 * enabling
 * scheduling
 */
void Compiler::compileAllBehavioralRoutines(ExecutableForm * theExecutable)
{
	const Machine * aMachine = theExecutable->getAstMachine();

	if( aMachine->hasMachine() )
	{
		//compiling initialization
		compileBehaviorInitialization(theExecutable);

		//compiling scheduler
		compileBehaviorScheduling(theExecutable);

		//enabling
		compileBehaviorEnabling(theExecutable);

		//disabling
		compileBehaviorDisabling(theExecutable);

		//aborting
		compileBehaviorAborting(theExecutable);
	}
}



void Compiler::compileBehaviorInitialization(ExecutableForm * theExecutable)
{
	BFCodeList listOfCode;

	ListOfInstanceOfMachine usedInstance;
	if( theExecutable->hasOnInit() )
	{
		StatementFactory::collectActivityMachine(
				theExecutable, AVM_OPCODE_INIT, AVM_OPCODE_START,
				theExecutable->getOnInit(), usedInstance);
	}

	TableOfSymbol::const_iterator itMachine =
			theExecutable->instance_static_begin();
	TableOfSymbol::const_iterator endMachine =
			theExecutable->instance_static_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( (*itMachine).getExecutable()->isSchedulable()
			&& (*itMachine).machine().isAutoStart()
			&& (not usedInstance.contains( (*itMachine).rawMachine() )) )
		{
			listOfCode.append( StatementConstructor::newCode(
					OperatorManager::OPERATOR_INIT, (*itMachine)) );
		}
	}

	/**
	 * Optimisization
	 */
	BFCode onInitCode;
	if( listOfCode.populated() )
	{
		onInitCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_STRONG_SYNCHRONOUS, listOfCode);
	}
	else if( listOfCode.nonempty() )
	{
		onInitCode = listOfCode.first();
	}
	else if( not theExecutable->hasOnInit() )
	{
//		incrWarningCount();
		theExecutable->getAstElement()->warningLocation(AVM_OS_LOG)
					<< "Unfound InstanceStatic for onInit code compilation "
							"of composite machine << "
					<< theExecutable->getAstElement()->getFullyQualifiedNameID()
					<< " >>" << std::endl << std::endl;
	}

	if( onInitCode.valid() )
	{
		theExecutable->setOnInit(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						theExecutable->getOnInit(), onInitCode) );
	}

	// onSTART
	theExecutable->setOnStart(
			StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					theExecutable->getOnStart(),
					theExecutable->getOnInit()) );
}


void Compiler::compileBehaviorEnabling(ExecutableForm * theExecutable)
{
	BFCodeList listOfCode;

	ListOfInstanceOfMachine usedInstance;
	if( theExecutable->hasOnEnable() )
	{
		StatementFactory::collectActivityMachine(
				theExecutable, AVM_OPCODE_ENABLE_INVOKE,
				theExecutable->getOnEnable(), usedInstance);
	}

	TableOfSymbol::const_iterator itMachine =
			theExecutable->instance_static_begin();
	TableOfSymbol::const_iterator endMachine =
			theExecutable->instance_static_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( ( (*itMachine).getExecutable()->hasOnInit()
				|| (*itMachine).getExecutable()->hasOnRun()
				|| (*itMachine).getExecutable()->hasOnEnable() )
			&& (*itMachine).machine().isAutoStart()
			&& (not usedInstance.contains( (*itMachine).rawMachine() )) )
		{
			listOfCode.append( StatementConstructor::newCode(
					OperatorManager::OPERATOR_ENABLE_INVOKE, (*itMachine)) );
		}
	}

	/**
	 * Optimisization
	 */
	BFCode onEnableCode;
	if( listOfCode.populated() )
	{
		onEnableCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_STRONG_SYNCHRONOUS, listOfCode);
	}
	else if( listOfCode.nonempty() )
	{
		onEnableCode = listOfCode.first();
	}
	else if( not theExecutable->hasOnInit() )
	{
//		incrWarningCount();
		theExecutable->getAstElement()->warningLocation(AVM_OS_LOG)
					<< "Unfound InstanceStatic for onEnable code compilation "
							"of composite machine << "
					<< theExecutable->getAstElement()->getFullyQualifiedNameID()
					<< " >>" << std::endl << std::endl;
	}

	if( onEnableCode.valid() )
	{
		theExecutable->setOnEnable(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						theExecutable->getOnEnable(), onEnableCode) );
	}
}


void Compiler::compileBehaviorDisabling(ExecutableForm * theExecutable)
{
	BFCodeList listOfCode;

	ListOfInstanceOfMachine usedInstance;
	if( theExecutable->hasOnDisable() )
	{
		StatementFactory::collectActivityMachine(
				theExecutable, AVM_OPCODE_DISABLE_INVOKE,
				theExecutable->getOnDisable(), usedInstance);
	}

	TableOfSymbol::const_iterator itMachine =
			theExecutable->instance_static_begin();
	TableOfSymbol::const_iterator endMachine =
			theExecutable->instance_static_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( (*itMachine).machine().isAutoStart()
			&& (not usedInstance.contains( (*itMachine).rawMachine() )) )
		{
			listOfCode.append( StatementConstructor::newCode(
					OperatorManager::OPERATOR_DISABLE_INVOKE, (*itMachine)) );
		}
	}

	/**
	 * Optimisization
	 */
	BFCode onDisableCode;
	if( listOfCode.populated() )
	{
		onDisableCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_STRONG_SYNCHRONOUS, listOfCode);
	}
	else if( listOfCode.nonempty() )
	{
		onDisableCode = listOfCode.first();
	}

	if( onDisableCode.valid() )
	{
		theExecutable->setOnDisable(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						onDisableCode, theExecutable->getOnDisable()) );
	}
}


void Compiler::compileBehaviorAborting(ExecutableForm * theExecutable)
{
	BFCodeList listOfCode;

	ListOfInstanceOfMachine usedInstance;
	if( theExecutable->hasOnAbort() )
	{
		StatementFactory::collectActivityMachine(
				theExecutable, AVM_OPCODE_ABORT_INVOKE,
				theExecutable->getOnAbort(), usedInstance);
	}

	TableOfSymbol::const_iterator itMachine =
			theExecutable->instance_static_begin();
	TableOfSymbol::const_iterator endMachine =
			theExecutable->instance_static_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( (*itMachine).machine().isAutoStart()
			&& (not usedInstance.contains( (*itMachine).rawMachine() )) )
		{
			listOfCode.append( StatementConstructor::newCode(
					OperatorManager::OPERATOR_ABORT_INVOKE, (*itMachine)) );
		}
	}

	/**
	 * Optimisization
	 */
	BFCode onAbortCode;
	if( listOfCode.populated() )
	{
		onAbortCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_STRONG_SYNCHRONOUS, listOfCode);
	}
	else if( listOfCode.nonempty() )
	{
		onAbortCode = listOfCode.first();
	}

	if( onAbortCode.valid() )
	{
		theExecutable->setOnAbort(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						onAbortCode, theExecutable->getOnAbort()) );
	}
}


void Compiler::compileBehaviorScheduling(ExecutableForm * theExecutable)
{
	ListOfInstanceOfMachine usedInstance;
	Operator * defaultConcurrencyOp = NULL;
	BFCode userScheduler;

	// INIT STEP
	// Collect unscheduled submachines
	// get default concurrency policy
	if( theExecutable->hasOnRun() )
	{
		StatementFactory::collectRunMachine(
				theExecutable, theExecutable->getOnRun(), usedInstance);
	}

	if( theExecutable->hasOnSchedule() )
	{
		userScheduler = theExecutable->getOnSchedule();

		if( userScheduler->empty() )
		{
			defaultConcurrencyOp = userScheduler->getOperator();
			theExecutable->setOnSchedule( userScheduler = BFCode::REF_NULL );
		}
		else
		{
			if( OperatorManager::isSchedule( userScheduler->getOperator() ) )
			{
				defaultConcurrencyOp = userScheduler->getOperator();
			}

			StatementFactory::collectRunMachine(
					theExecutable, userScheduler, usedInstance);
		}
	}

	if( theExecutable->hasOnConcurrency() )
	{
		defaultConcurrencyOp = theExecutable->getOnConcurrencyOperator();
	}
	else
	{
		if( defaultConcurrencyOp == NULL )
		{
			defaultConcurrencyOp = OperatorManager::OPERATOR_INTERLEAVING;
		}

		theExecutable->setOnConcurrency(
				StatementConstructor::newCode(defaultConcurrencyOp) );
	}

	// STEP case for singleton submachine
	if( usedInstance.empty()
		&& theExecutable->hasOneInstanceStatic()
		&& theExecutable->hasOneInstanceModel() )
	{
		BFCode runMachineCode(OperatorManager::OPERATOR_RUN,
				theExecutable->getInstanceStatic().last());

		if( userScheduler.valid() )
		{
			if( userScheduler->isOperator( defaultConcurrencyOp ) )
			{
				userScheduler->append( runMachineCode );
			}
			else
			{
				userScheduler = StatementConstructor::newCode(
						defaultConcurrencyOp, userScheduler, runMachineCode );
			}

			theExecutable->setOnSchedule( userScheduler );
		}
		else
		{
			theExecutable->setOnSchedule( runMachineCode );
		}
	}

	// STEP case for many submachines
	else if( usedInstance.size() < (theExecutable->sizeInstanceStatic()
			+ theExecutable->sizeInstanceModel()) )
	{
		BFCode aScheduleCode;

		if( userScheduler.valid() )
		{
			aScheduleCode = compileSchedulerRoutine(
					theExecutable, usedInstance, userScheduler);

			if( aScheduleCode->isnotOperator( defaultConcurrencyOp ) )
			{
				aScheduleCode = StatementConstructor::newCode(
						defaultConcurrencyOp, aScheduleCode );
			}
		}
		else
		{
			userScheduler = aScheduleCode =
					StatementConstructor::newCode( defaultConcurrencyOp );
		}

		TableOfSymbol::const_iterator itInstance =
				theExecutable->instance_static_begin();
		TableOfSymbol::const_iterator endInstance =
				theExecutable->instance_static_end();
		for( ; itInstance != endInstance ; ++itInstance )
		{
			if( (*itInstance).getExecutable()->isSchedulable()
				&& (not usedInstance.contains((*itInstance).rawMachine())) )
			{
				aScheduleCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_RUN, (*itInstance)) );
			}
		}

		itInstance = theExecutable->instance_model_begin();
		endInstance = theExecutable->instance_model_end();
		for( ; itInstance != endInstance ; ++itInstance )
		{
			if( (*itInstance).machine().hasPossibleDynamicInstanciation()
				&& (*itInstance).getExecutable()->isSchedulable()
				&& (not usedInstance.contains((*itInstance).rawMachine())) )
			{
				aScheduleCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_RUN, (*itInstance)) );
			}
		}

		if( aScheduleCode->singleton() )
		{
			aScheduleCode->pop_last_to( userScheduler );

			if( userScheduler.valid() )
			{
				theExecutable->setOnSchedule( userScheduler );
			}
		}
		else
		{
			theExecutable->setOnSchedule( aScheduleCode );
		}
	}
	else if( userScheduler.valid() )
	{
		theExecutable->setOnSchedule( compileSchedulerRoutine(
				theExecutable, usedInstance, userScheduler) );
	}
}


void Compiler::setRdvScheduling(ExecutableForm * theExecutable)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( theExecutable->hasRdvCommunication() )
			<< "Unexpected Executable without RDV comunication !!!"
			<< SEND_EXIT;


	BFCode & aScheduleCode = theExecutable->getOnSchedule();
	switch( aScheduleCode.getAvmOpCode() )
	{
		case AVM_OPCODE_ASYNCHRONOUS:
		{
			aScheduleCode.setOperator(
					OperatorManager::OPERATOR_RDV_ASYNCHRONOUS );
			break;
		}

		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		{
			aScheduleCode.setOperator(
					OperatorManager::OPERATOR_RDV_STRONG_SYNCHRONOUS );
			break;
		}

		case AVM_OPCODE_WEAK_SYNCHRONOUS:
		{
			aScheduleCode.setOperator(
					OperatorManager::OPERATOR_RDV_WEAK_SYNCHRONOUS );
			break;
		}

		case AVM_OPCODE_INTERLEAVING:
		{
			aScheduleCode.setOperator(
					OperatorManager::OPERATOR_RDV_INTERLEAVING );
			break;
		}

		case AVM_OPCODE_PARALLEL:
		{
			aScheduleCode.setOperator(
					OperatorManager::OPERATOR_RDV_PARALLEL );
			break;
		}

		default:
		{
			theExecutable->setOnSchedule(StatementConstructor::newCode(
					OperatorManager::OPERATOR_SYNCHRONIZE, aScheduleCode));
			break;
		}
	}
}


}

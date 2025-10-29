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

#include <fml/builtin/Identifier.h>
#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/StatementTypeChecker.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementFactory.h>

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
mVariableCompiler( *this ),
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
void Compiler::precompilePropertyPart(
		ExecutableForm & anExecutable, const PropertyPart & aPropertyPart,
		TableOfInstanceOfData & tableOfVariable)
{
	// User Variable-Parameters
	PropertyPart::const_variable_iterator itVar =
			aPropertyPart.var_parameter_begin();
	PropertyPart::const_owned_iterator endVar =
			aPropertyPart.var_parameter_end();
	for( ; itVar != endVar ; ++itVar )
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( (*itVar) )
				<< "data or type for compiling !!!"
				<< SEND_EXIT;

		// Allocation for variable
		mVariableCompiler.precompileVariable(anExecutable,
				(*itVar).to< Variable >(), tableOfVariable);
	}

	// User Variable-Returns
	itVar = aPropertyPart.var_return_begin();
	endVar = aPropertyPart.var_return_end();
	for( ; itVar != endVar ; ++itVar )
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( (*itVar) )
				<< "data or type for compiling !!!"
				<< SEND_EXIT;

		// Allocation for variable
		mVariableCompiler.precompileVariable(anExecutable,
				(*itVar).to< Variable >(), tableOfVariable);
	}

	// Other OwnedElements
	PropertyPart::const_owned_iterator itWfO = aPropertyPart.owned_begin();
	PropertyPart::const_owned_iterator endWfO = aPropertyPart.owned_end();
	for( ; itWfO != endWfO ; ++itWfO )
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( (*itWfO) )
				<< "data or type for compiling !!!"
				<< SEND_EXIT;

		// Allocation for variable
		if( (*itWfO).is< Variable >() )
		{
			const Variable & aVariable = (*itWfO).to< Variable >();

			if( aVariable.getModifier().noNatureParameter() )
			{
				mVariableCompiler.precompileVariable(anExecutable,
						aVariable, tableOfVariable);
			}
		}

		// Allocation for buffer
		else if( (*itWfO).is< Buffer >() )
		{
			mComCompiler.precompileBuffer(
					anExecutable, (*itWfO).to< Buffer >());
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
			anExecutable, aPropertyPart, tableOfVariable);

	// Allocation for channels
	mComCompiler.precompileChannel(anExecutable,
			aPropertyPart, tableOfVariable);
}


void Compiler::precompileDataType(
		AvmProgram & aProgram, const PropertyPart & aPropertyPart,
		TableOfInstanceOfData & tableOfVariable)
{
	PropertyPart::const_owned_iterator itProperty = aPropertyPart.owned_begin();
	PropertyPart::const_owned_iterator endProperty = aPropertyPart.owned_end();
	for( ; itProperty != endProperty ; ++itProperty )
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( (*itProperty) )
				<< "data or type for compiling !!!"
				<< SEND_EXIT;

		// Allocation for variable
		if( (*itProperty).is< Variable >() )
		{
			mVariableCompiler.precompileVariable(aProgram,
					(*itProperty).to< Variable >(), tableOfVariable);
		}

		// Allocation for typedef
		else
		{
			precompileTypeSpecifier(aProgram, (*itProperty));
		}
	}
}


/**
 * precompile
 * specification
 */
void Compiler::precompileExecutableCompositePart(
		ExecutableForm & aContainer, Machine & anExecutableSpec)
{
	const CompositePart * aCompositePart = anExecutableSpec.getCompositePart();

	if( aCompositePart == nullptr )
	{
		//!! NOTHING
		return;
	}

	/*
	 * precompiling procedure
	 */
	if( aCompositePart->hasProcedure() )
	{
		for( auto & itProcedure : aCompositePart->getProcedures() )
		{
			Machine & aProcedure = const_cast< Machine & >(
					itProcedure.to< Machine >() );

			precompileExecutable(aContainer, aProcedure);
		}
	}

	/*
	 * precompiling executable - instance static
	 */
	if( aCompositePart->hasMachine() )
	{
		// precompiling sub-executable
		anExecutableSpec.expandGroupStatemachine();

		for( auto & itMachine : aCompositePart->getMachines() )
		{
			Machine & aMachine = const_cast< Machine & >(
					itMachine.to< Machine >() );

			precompileExecutable(aContainer, aMachine);
		}
	}

	/*
	 * precompiling instance dynamic
	 */
	if( aCompositePart->hasInstanceDynamic() )
	{
		for( auto & itMachine : aCompositePart->getInstanceDynamics() )
		{
//			if( (it)->getSpecifier().isDesignInstanceDynamic() )
			{
				precompileExecutableInstanceDynamique(
						aContainer, itMachine.to< Machine >());
			}
		}
	}
}


void Compiler::precompileExecutable(
		ExecutableForm & aContainer, Machine & anExecutableSpec)
{
	if( anExecutableSpec.getSpecifier().hasGroupMask() )
	{
		precompileExecutableGroup(aContainer, anExecutableSpec);
	}
	else if( anExecutableSpec.getSpecifier().isDesignModel())
	{
		precompileExecutableModel(aContainer, anExecutableSpec);
	}
	else if( anExecutableSpec.getSpecifier().isDesignPrototypeStatic() )
	{
		precompileExecutablePrototype(aContainer, anExecutableSpec);
	}
	else if( anExecutableSpec.getSpecifier().isDesignInstanceStatic() )
	{
		precompileExecutableInstanceStatic(aContainer, anExecutableSpec);
	}
	else if( anExecutableSpec.getSpecifier().isDesignInstanceDynamic() )
	{
		precompileExecutableInstanceDynamique(aContainer, anExecutableSpec);
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected in precompiling stage the executable: "
				<< std::endl << str_header( anExecutableSpec ) << std::endl
				<< "==> with specifier: "
				<< anExecutableSpec.getSpecifier().str() << " !!!"
				<< SEND_EXIT;
	}
}


ExecutableForm * Compiler::precompileExecutableModel(
		ExecutableForm & aContainer, Machine & anExecutableSpec)
{
//AVM_OS_CERR << TAB << "<** begin precompiling executable model:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;

	// CREATE NEW EXECUTABLE
	ExecutableForm * anExec = new ExecutableForm(
			mConfiguration.getExecutableSystem(),
			(& aContainer), anExecutableSpec );

	setInheritedSpecifier(aContainer, *anExec);

//	// APPEND NEW EXECUTABLE IN THE SYSTEM
//	//?? For retrocompatibity serialization order
	getSymbolTable().addMachineExecutable(
			mConfiguration.getExecutableSystem().saveExecutable( anExec ) );

	std::size_t maximalInstanceCount = anExecutableSpec.hasInstanceSpecifier()
		? anExecutableSpec.getInstanceSpecifier()->getMaximalInstanceCount()
		: AVM_NUMERIC_MAX_SIZE_T;

	//??? Sera fait dans precompileExecutableInstanceXXX(...) ?
//	anExec->incrPossibleStaticInstanciationCount( createdInstanceCount );

	if( anExecutableSpec.getSpecifier().isFamilyComponentComposite() )
	{
		Specifier aSpecifier( anExecutableSpec.getSpecifier() );

		InstanceOfMachine * aModelInstance = new InstanceOfMachine(
				(& aContainer), anExecutableSpec, (* anExec), nullptr,
				aContainer.getInstanceModel().size(),
				aSpecifier.setDesignModel() );

		//??? Sera fait dans precompileExecutableInstanceXXX(...) ?
		aModelInstance->setInstanceCount(
				/*createdInstanceCount*/0, maximalInstanceCount);

		aContainer.saveInstanceModel( aModelInstance );
	}

	/*
	 * Allocation of declaration contents :>
	 * constant, variable, typedef, buffer, port
	 */
	if( anExecutableSpec.hasProperty() )
	{
		const PropertyPart & aPropertyPart = anExecutableSpec.getPropertyPart();

		avm_offset_t parametersCount = aPropertyPart.getVariableParametersCount();

		anExec->setParamOffsetCount( 0 , parametersCount );

		TableOfInstanceOfData tableOfVariable;

		anExec->setReturnOffsetCount( parametersCount,
				aPropertyPart.getVariableReturnsCount() );

		precompilePropertyPart( (* anExec), aPropertyPart, tableOfVariable);

		/*
		 * Update data table
		 */
		anExec->setVariables(tableOfVariable);

		// Set Time & Delta Variable link
		anExec->setDeltaTimeVariable();
	}

	/*
	 * precompiling executable composite part
	 */
	if( anExecutableSpec.hasMachine() || anExecutableSpec.hasPortSignal() )
	{
		Specifier aSpecifier( anExecutableSpec.getSpecifier() );

		// Set the instance THIS at first position (index = 0)
		InstanceOfMachine * aNewInstance =
				InstanceOfMachine::newInstanceModelThis(
						anExec, anExecutableSpec, (* anExec), nullptr,
						anExec->getInstanceModel().size(),
						aSpecifier.setDesignModel() );

		anExec->saveInstanceModel(aNewInstance);

		aNewInstance = InstanceOfMachine::newThis((* anExec),
				aNewInstance, anExec->getInstanceStatic().size() );
//		aNewInstance->setAutoStart( anExecutableSpec.hasInitialInstance() );

		anExec->saveInstanceStatic(aNewInstance);
	}

	precompileExecutableCompositePart((* anExec), anExecutableSpec);


	/*
	 * precompiling transition
	 */
	if( anExecutableSpec.hasOutgoingTransition() )
	{
		for( auto & itTransition :
				anExecutableSpec.getBehavior()->getOutgoingTransitions() )
		{
			Transition & aTransition = const_cast< Transition & >(
					itTransition.to< Transition >() );

			mTransitionCompiler.precompileTransition((* anExec), aTransition);
		}
	}

	// APPEND NEW EXECUTABLE IN THE SYSTEM
	//?? For retrocompatibity serialization order
//	getSymbolTable().addMachineExecutable(
//			mConfiguration.getExecutableSystem().saveExecutable( anExec ) );

//AVM_OS_TRACE << TAB << ">** end precompiling executable MODEL:>"
//	<< std::endl << str_header( anExecutableSpec ) << std::endl;

	return( anExec );
}


void Compiler::precompileExecutablePrototype(
		ExecutableForm & aContainer, Machine & anExecutableSpec)
{
//AVM_OS_TRACE << TAB << "<++ begin precompiling executable #instance model:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;

		ExecutableForm * anExec =
				precompileExecutableModel(aContainer, anExecutableSpec);

		std::size_t initialInstanceCount = 1;
		std::size_t maximalInstanceCount = AVM_NUMERIC_MAX_SIZE_T;
		if( anExecutableSpec.hasInstanceSpecifier() )
		{
			initialInstanceCount = anExecutableSpec.
					getInstanceSpecifier()->getInitialInstanceCount();

			maximalInstanceCount = anExecutableSpec.
					getInstanceSpecifier()->getMaximalInstanceCount();
		}

		// Instances for << MODEL >> & INSTANCE
		InstanceOfMachine * aModelInstance = nullptr;
		if( anExecutableSpec.getSpecifier().isFamilyComponentComposite() )
		{
			aModelInstance = aContainer.getInstanceModel().
					getByAstElement( anExec->safeAstElement() ).rawMachine();
			if( aModelInstance == nullptr )
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
			Specifier aSpecifier( anExecutableSpec.getSpecifier() );

			InstanceOfMachine * aNewInstance = new InstanceOfMachine(
					(& aContainer), anExecutableSpec, (* anExec), aModelInstance,
					aContainer.getInstanceStatic().size(),
					aSpecifier.setDesignPrototypeStatic() );

			aNewInstance->setInstanceCount(
					initialInstanceCount, maximalInstanceCount);

			aNewInstance->setAutoStart( true );

			setInheritedSpecifier(aContainer, (* aNewInstance));

			anExec->setPrototypeInstance( aNewInstance );

			const Symbol & bfInstance =
					aContainer.saveInstanceStatic(aNewInstance);
			getSymbolTable().addInstanceStatic(bfInstance);

			aSpecifier.setDesignInstanceStatic();

			std::size_t offset = 1;
			for( ; offset < initialInstanceCount ; ++offset )
			{
				aNewInstance = new InstanceOfMachine( (& aContainer),
						anExecutableSpec, (* anExec), aModelInstance,
						aContainer.getInstanceStatic().size(), aSpecifier);
				aNewInstance->setInstanceCount(1, maximalInstanceCount);

				aNewInstance->updateUfid(offset);

				aNewInstance->setAutoStart( true );

				setInheritedSpecifier(aContainer, (* aNewInstance));

				getSymbolTable().addInstanceStatic(
						aContainer.saveInstanceStatic(aNewInstance));
			}
		}
		else
		{
			//!! NOTHING
		}

//AVM_OS_TRACE << TAB << ">++ end precompiling executable #instance model:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;
}


void Compiler::precompileExecutableInstanceStatic(
		ExecutableForm & aContainer, const Machine & anExecutableSpec)
{
//AVM_OS_TRACE << TAB << "<-- begin precompiling executable #static instance:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;

		ExecutableForm * anExec =
				getSymbolTable().searchExecutableModel(& anExecutableSpec);

		if( anExec != nullptr )
		{
			std::size_t initialInstanceCount = anExecutableSpec.
					getInstanceSpecifier()->getInitialInstanceCount();
			std::size_t maximalInstanceCount = anExecutableSpec.
					getInstanceSpecifier()->getMaximalInstanceCount();

			anExec->incrPossibleStaticInstanciationCount( initialInstanceCount );

			// Instances for << MODEL >> & INSTANCE
			InstanceOfMachine * aModelInstance = aContainer.getInstanceModel().
					getByAstElement( anExec->safeAstElement() ).rawMachine();
			if( aModelInstance == nullptr )
			{
				Specifier aSpecifier(
						anExec->getAstMachine().getSpecifier() );

				aModelInstance = new InstanceOfMachine( (& aContainer),
						anExec->getAstMachine(), (* anExec), nullptr,
						aContainer.getInstanceModel().size(),
						aSpecifier.setDesignModel() );

				aModelInstance->setInstanceCount(
						initialInstanceCount, maximalInstanceCount);

				aContainer.saveInstanceModel( aModelInstance );
			}
			else
			{
				aModelInstance->incrInstanciationCount( initialInstanceCount );
			}

			InstanceOfMachine * aNewInstance = nullptr;
			std::size_t offset = 0;
			for( ; offset < initialInstanceCount ; ++offset )
			{
				aNewInstance = new InstanceOfMachine( (& aContainer),
						anExecutableSpec, (* anExec), aModelInstance,
						aContainer.getInstanceStatic().size() );

				aNewInstance->setInstanceCount(
						initialInstanceCount, maximalInstanceCount);

				if( offset > 0 )
				{
					aNewInstance->updateUfid(offset);
				}

				aNewInstance->setAutoStart( anExecutableSpec.isAutoStart() );
//				aNewInstance->setAutoStart( true );

				setInheritedSpecifier(aContainer, (* aNewInstance));

				getSymbolTable().addInstanceStatic(
						aContainer.saveInstanceStatic(aNewInstance));
			}
		}

		// ERROR REPORTING
		else if( getSymbolTable().hasError() )
		{
			incrErrorCount();
			anExecutableSpec.errorLocation(AVM_OS_WARN)
					<< getSymbolTable().getErrorMessage()
					<< std::endl << std::endl;
		}

		else
		{


			incrErrorCount();
			anExecutableSpec.errorLocation(AVM_OS_WARN)
					<< "Unfound the model << " << anExecutableSpec.strType()
					<< " >> of the executable instance << "
					<< str_header( anExecutableSpec ) << " >>"
					<< std::endl << std::endl;
		}

//AVM_OS_TRACE << TAB << ">-- end precompiling executable #dynamic instance:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;
}


void Compiler::precompileExecutableInstanceDynamique(
		ExecutableForm & aContainer, const Machine & anExecutableSpec)
{
//AVM_OS_WARN << TAB << "<-- begin precompiling executable #dynamic instance:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;

		ExecutableForm * anExec =
				getSymbolTable().searchExecutableModel(& anExecutableSpec);

		std::size_t initialInstanceCount = anExecutableSpec.
				getInstanceSpecifier()->getInitialInstanceCount();
		std::size_t maximalInstanceCount = anExecutableSpec.
				getInstanceSpecifier()->getMaximalInstanceCount();

		if( anExec != nullptr )
		{
			// Instances for << MODEL >> & INSTANCE
			CompilationEnvironment cENV(anExec);

			InstanceOfMachine * aModelInstance =
					getSymbolTable().searchInstanceModel(
							cENV.mCTX, anExec->safeAstElement()).rawMachine();
			if( aModelInstance == nullptr )
			{
				aModelInstance = aContainer.getInstanceModel().
						getByAstElement( anExec->getAstElement() ).rawMachine();
			}
			if( aModelInstance == nullptr )
			{
				Specifier aSpecifier(
						anExec->getAstMachine().getSpecifier() );

				aModelInstance = new InstanceOfMachine( (& aContainer),
						anExec->getAstMachine(), (* anExec), nullptr,
						aContainer.getInstanceModel().size(),
						aSpecifier.setDesignModel() );

				aModelInstance->setInstanceCount(
						initialInstanceCount, maximalInstanceCount);

				aContainer.saveInstanceModel( aModelInstance );

				anExec->incrPossibleDynamicInstanciationCount(
						initialInstanceCount );
			}
			else
			{
				aModelInstance->incrPossibleDynamicInstanciationCount(
						initialInstanceCount );
			}

			InstanceOfMachine * aNewInstance = new InstanceOfMachine(
					(& aContainer), anExecutableSpec, (* anExec),
					aModelInstance, aContainer.getInstanceStatic().size() );

			aNewInstance->setInstanceCount(
					initialInstanceCount, maximalInstanceCount);

			aNewInstance->setAutoStart( true );

			setInheritedSpecifier(aContainer, *aNewInstance);

			aContainer.saveInstanceDynamic(aNewInstance);
		}

		// ERROR REPORTING
		else if( getSymbolTable().hasError() )
		{
			incrErrorCount();
			anExecutableSpec.errorLocation(AVM_OS_WARN)
					<< getSymbolTable().getErrorMessage()
					<< std::endl << std::endl;
		}

		else
		{
			incrWarningCount();
			anExecutableSpec.warningLocation(AVM_OS_LOG)
					<< "Unfound the executable model << "
					<< anExecutableSpec.strType()
					<< " >> of the #dynamic instance !!!"
					<< std::endl << str_header( anExecutableSpec )
					<< std::endl << std::endl;

			InstanceOfMachine * aNewInstance = new InstanceOfMachine(
					(& aContainer), anExecutableSpec, (* anExec), nullptr,
					aContainer.getInstanceStatic().size() );

			aNewInstance->setInstanceCount(
					initialInstanceCount, maximalInstanceCount);

			aNewInstance->setAutoStart( false );

			setInheritedSpecifier(aContainer, (* aNewInstance));

			aContainer.saveInstanceDynamic(aNewInstance);
		}

//AVM_OS_WARN << TAB << ">-- end precompiling executable #dynamic instance:>"
//		<< std::endl << str_header( anExecutableSpec ) << std::endl;
}


void Compiler::precompileExecutableGroup(
		ExecutableForm & aContainer, const Machine & anExecutableSpec)
{
//	Machine * containerSM = anExecutableSpec.getContainerMachine();
//
//	if( anExecutableSpec.getSpecifier().isGroupEvery())
//	{
//		containerSM->appendOutgoingTransitionToEveryState(anExecutableSpec);
//	}
//	else if( anExecutableSpec.getSpecifier().isGroupSome())
//	{
//		containerSM->appendOutgoingTransitionToSomeState(anExecutableSpec);
//	}
//	else if( anExecutableSpec.getSpecifier().isGroupExcept() )
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
			mConfiguration.getExecutableSystem(), nullptr, aSystem);

//	// APPEND NEW EXECUTABLE IN THE SYSTEM
//	//?? For retrocompatibity serialization order
	getSymbolTable().addMachineExecutable(
			mConfiguration.getExecutableSystem().saveExecutable( systemExec ) );

	// Structural decompositon
	systemExec->setMainComponent( true );


	Specifier aSpecifier( aSystem.getSpecifier() );

	InstanceOfMachine * aNewInstance = new InstanceOfMachine(nullptr, aSystem,
			(* systemExec), nullptr, 0, aSpecifier.setDesignPrototypeStatic() );

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
			systemExec, aSystem, (* systemExec), nullptr,
			systemExec->getInstanceModel().size(),
			aSpecifier.setDesignModel() );

	aNewInstance->setInstanceCount(0, 1);

	systemExec->saveInstanceModel( aNewInstance );

	aNewInstance = InstanceOfMachine::newThis((* systemExec),
			aNewInstance, systemExec->getInstanceStatic().size() );

	systemExec->saveInstanceStatic(aNewInstance);

	/*
	 * Allocation of declaration contents :>
	 * constant, variable, typedef, buffer, port
	 */
	if( aSystem.hasProperty() )
	{
		TableOfInstanceOfData tableOfVariable;

		precompilePropertyPart( (* systemExec),
				aSystem.getPropertyPart(), tableOfVariable);

		/*
		 * Update data table
		 */
		systemExec->setVariables(tableOfVariable);

		// Set Time & Delta Variable link
		systemExec->setDeltaTimeVariable();
	}


	/*
	 * precompiling executable composite part
	 */
	precompileExecutableCompositePart((* systemExec), aSystem);

//AVM_OS_TRACE << TAB << "> end precompiling specification:> "
//		<< aSystem.getFullyQualifiedNameID() << std::endl << std::endl;

	// APPEND NEW EXECUTABLE IN THE SYSTEM
	//?? For retrocompatibity serialization order
//	getSymbolTable().addMachineExecutable(
//			mConfiguration.getExecutableSystem().saveExecutable( systemExec ) );
}


/**
 * setInheritedSpecifier from container to owned elements
 */
void Compiler::setInheritedSpecifier(
		ExecutableForm & aContainer, ExecutableForm & anExecutable)
{
	if( aContainer.getSpecifier().hasFeatureInputEnabled() )
	{
		anExecutable.getwSpecifier().setFeatureInputEnabled();

		const_cast< Machine & >( anExecutable.getAstMachine() ).
				getwSpecifier().setFeatureInputEnabled();

	}
}

void Compiler::setInheritedSpecifier(
		ExecutableForm & aContainer, InstanceOfMachine & aMachine)
{
	if( aContainer.getSpecifier().hasFeatureInputEnabled() )
	{
		aMachine.getwSpecifier().setFeatureInputEnabled();
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

	for( const auto & itExec :
			mConfiguration.getExecutableSystem().getExecutables() )
	{
		ExecutableForm & anExecutable = const_cast< ExecutableForm & >(
				itExec.to< ExecutableForm >() );

		compileExecutable( anExecutable );

		if( anExecutable.hasExecutable() )
		{
			for( const auto & itProc : anExecutable.getExecutables() )
			{
				ExecutableForm & aProcedure = const_cast< ExecutableForm & >(
						itProc.to< ExecutableForm >() );

				compileProcedure( aProcedure );
			}
		}
	}
}


void Compiler::compileExecutable(ExecutableForm & anExecutable)
{
	if( anExecutable.getLifecycle().isCompiled() ||
		anExecutable.getLifecycle().isCompiling() )
	{
		return;
	}
	else
	{
		anExecutable.getwLifecycle().setCompiling();
	}

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<executable>: "
			<< anExecutable.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	// Compile data & all machine MOE program
	compileBaseMachine(anExecutable);

	// Compile data & all instance MOE program
	compileAllInstances( anExecutable );

	if( anExecutable.safeAstElement().is< System >() )
	{
		compileSystem( anExecutable );
	}

	else if( anExecutable.getAstElement().is_exactly< Machine >() )
	{
		if( anExecutable.getSpecifier().isFamilyComponentStatemachine() )
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
				<< anExecutable.toString()
				<< SEND_EXIT;
	}

	anExecutable.getwLifecycle().setCompiled();

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| compiling<executable>: "
			<< anExecutable.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
}


/**
 *******************************************************************************
 * COMPILATION OF INSTANCE MACHINE PARAMETERS
 *******************************************************************************
 */
void Compiler::compileAllInstances(ExecutableForm & anExecutableForm)
{
	if( anExecutableForm.hasInstanceStatic() )
	{
		// Compilation of InstanceOfMachine Parameters / Behaviors
		TableOfSymbol::const_iterator itMachine =
				anExecutableForm.instance_static_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm.instance_static_end();
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

	if( anExecutableForm.hasInstanceDynamic() )
	{
		// Compilation of InstanceOfMachine Parameters / Behaviors
		TableOfSymbol::const_iterator itMachine =
				anExecutableForm.instance_dynamic_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm.instance_dynamic_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			compileInstance(anExecutableForm, (*itMachine).rawMachine());

			AVM_OS_ASSERT_FATAL_ERROR_EXIT( (*itMachine).hasExecutable() )
					<< "Unexpected a #dynamic instance "
							"without executable model !!!"
					<< std::endl << str_header( (*itMachine) )
					<< SEND_EXIT;
		}
	}
}

void Compiler::compileInstance(
		ExecutableForm & theExecutableContainer, InstanceOfMachine * anInstance)
{
	const Machine & anExecutableSpec = anInstance->getAstMachine();

//AVM_OS_WARN << TAB << "<-- begin compiling executable instance:>" << std::endl
//			<< to_stream( anInstance )// << std::endl
//			<< to_stream( anExecutableSpec ) << std::endl;

	ExecutableForm * anExec = anInstance->getExecutable();

// TODO compileInstance: searchExecutableModel
//	AVM_OS_ASSERT_FATAL_ERROR_EXIT( anExec != nullptr )
//			<< "Unexpected an instance without executable model !!!"
//			<< std::endl << str_header( anInstance )
//			<< SEND_EXIT;

	if( anExec == nullptr )
	{
		anExec = getSymbolTable().searchExecutableModel(& anExecutableSpec);

		if( anExec != nullptr )
		{
			anInstance->setExecutable( anExec );

			anInstance->setAutoStart( true );

			// Instances for << MODEL >> & INSTANCE
			CompilationEnvironment cENV(anExec);

			InstanceOfMachine * aModelInstance =
					getSymbolTable().searchInstanceModel(
							cENV.mCTX, anExec->safeAstElement()).rawMachine();
			if( aModelInstance == nullptr )
			{
				aModelInstance = theExecutableContainer.getInstanceModel().
						getByAstElement( anExec->getAstElement() ).rawMachine();
			}
			if( aModelInstance != nullptr )
			{
				anInstance->setInstanceModel( aModelInstance );
			}

			if( anInstance->getSpecifier().hasDesignInstanceDynamic() )
			{
				if( aModelInstance != nullptr )
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
			anExecutableSpec.errorLocation(AVM_OS_WARN)
					<< getSymbolTable().getErrorMessage()
					<< std::endl << std::endl;
		}

		else
		{
			incrErrorCount();
			anExecutableSpec.errorLocation(AVM_OS_WARN)
					<< "Unfound the model << "
					<< anExecutableSpec.strType()
					<< " >> of the statemachine instance << "
					<< str_header( anExecutableSpec ) << " >>"
					<< std::endl << std::endl;
		}
	}

	if( anExec != nullptr )
	{
		// Compile Executable model if it's not yet
		compileExecutable( * anExec );

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

	const BehavioralPart * theBehavior = anExecutableSpec.getBehavior();

	if( theBehavior != nullptr )
	{
		/*
		 * onCreate
		 */
		if( theBehavior->hasOnCreate()
			&& StatementTypeChecker::doSomething(* theBehavior->getOnCreate()) )
		{
			CompilationEnvironment cENV(nullptr, anExec, (& theExecutableContainer));

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
			&& StatementTypeChecker::doSomething(* theBehavior->getOnStart()) )
		{
			CompilationEnvironment cENV(nullptr, anExec, (& theExecutableContainer));

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
		ExecutableForm & theExecutableContainer, InstanceOfMachine * anInstance)
{
	ExecutableForm & anExecutableForm = anInstance->refExecutable();

	const Machine & aMachine = anInstance->getAstMachine();

	if( anExecutableForm.hasParamReturn() )
	{
		APTableOfData aParamTable( new TableOfData(
				anExecutableForm.getParamReturnCount() ) );
		anInstance->setParamReturnTable( aParamTable );

		anInstance->setReturnOffset( anExecutableForm.getParamCount() );

		bool hasInitialInstance =
				aMachine.getInstanceSpecifier()->hasInitialInstance();


		if( anExecutableForm.hasParam() )
		{
			if( aMachine.hasVariableParameter() )
			{
				BF paramValue;

				TableOfVariable::const_raw_iterator it =
						aMachine.getVariableParameters().begin();
				TableOfVariable::const_raw_iterator itEnd =
						aMachine.getVariableParameters().end();
				for( avm_offset_t offset = 0 ; it != itEnd ; ++it , ++offset )
				{
					if( (*it).invalid() )
					{
						if( hasInitialInstance )
						{
							incrWarningCount();
							aMachine.errorLocation(AVM_OS_WARN)
									<< "Compile param warning << "
									<< str_header(
										anExecutableForm.rawParamVariable(offset) )
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
							aMachine.errorLocation(AVM_OS_WARN)
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
						aMachine.warningLocation(AVM_OS_WARN)
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

		if( anExecutableForm.hasReturn() )
		{
			if( aMachine.hasVariableReturn() )
			{
				BF returnValue;

				TableOfVariable::const_raw_iterator it =
						aMachine.getVariableReturns().begin();
				TableOfVariable::const_raw_iterator itEnd =
						aMachine.getVariableReturns().end();
				for( avm_offset_t offset = 0 ; it != itEnd ; ++it , ++offset )
				{
					if( (*it).invalid() )
					{
						incrWarningCount();
						aMachine.errorLocation(AVM_OS_WARN)
								<< "Compile return warning << "
								<< str_header(
									anExecutableForm.rawReturnVariable(offset) )
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
							aParamTable->set(anExecutableForm.getReturnOffset()
									+ offset, returnValue);
						}
						else
						{
							incrErrorCount();
							aMachine.errorLocation(AVM_OS_WARN)
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
void Compiler::compilePrograms(ExecutableForm & anExecutable)
{
	for( auto & itProgram : anExecutable.getProgram() )
	{
AVM_IF_DEBUG_FLAG( COMPILING )
AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<program>: "
		<< itProgram.strHeader() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

		compileProgram( itProgram.to< AvmProgram >() );

AVM_IF_DEBUG_FLAG( COMPILING )
//	(*itProg)->toStream(AVM_OS_TRACE);
AVM_OS_TRACE << TAB_DECR_INDENT << ">| compiling<program>: "
		<< itProgram.strHeader() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
	}
}


/**
 * compile
 * executable program
 */
void Compiler::compileProgram(AvmProgram & aProgram)
{
	const ObjectElement & astProgram = aProgram.safeAstElement();

//	AVM_OS_TRACE << TAB << "<| compiling<program>: "
//			<< str_header(aProgram) << std::endl;

	// COMPILATION OF VARIABLE
	mVariableCompiler.compileVariable(aProgram);

	if( astProgram.is< Routine >() )
	{
		aProgram.setCode( mAvmcodeCompiler.compileStatement(aProgram,
				astProgram.as< Routine >().getCode()) );
	}
	else if( astProgram.is< Transition >() )
	{
		aProgram.setCode( mAvmcodeCompiler.compileStatement(aProgram,
				astProgram.as< Transition >().getStatement()) );
	}

//	AVM_OS_TRACE << TAB << ">| compiling<program>: "
//			<< str_header(aProgram) << std::endl << std::endl;
}


/**
 * compile
 * Executable
 */
void Compiler::compileBaseMachine(ExecutableForm & anExecutableForm)
{
	const Machine & aMachine = anExecutableForm.getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<machine>: "
//		<< str_header( aMachine ) << std::endl;


	// COMPILATION OF PORT
	mComCompiler.compilePort(anExecutableForm);

	// COMPILATION OF VARIABLE
	mVariableCompiler.compileVariable(anExecutableForm);


	if( not aMachine.hasBehavior() )
	{
		return;
	}

	BehavioralPart * theBehavior = aMachine.getBehavior();

	/*
	 * onCreate
	 */
	if( theBehavior->hasOnCreate()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnCreate()) )
	{
		anExecutableForm.setOnCreate(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnCreate()) );
	}

	/*
	 * onInit
	 */
	if( theBehavior->hasOnInit()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnInit()) )
	{
		anExecutableForm.setOnInit(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnInit()) );
	}

	/*
	 * onFinal
	 */
	if( theBehavior->hasOnFinal()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnFinal()) )
	{
		anExecutableForm.setOnFinal(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnFinal()) );
	}


	/*
	 * onReturn
	 */
	if( theBehavior->hasOnReturn()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnReturn()) )
	{
		anExecutableForm.setOnReturn(
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
	if( theBehavior->hasOnStart()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnStart()) )
	{
		anExecutableForm.setOnStart(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnStart()) );
	}

	/*
	 * onStop
	 */
	if( theBehavior->hasOnStop()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnStop()) )
	{
		anExecutableForm.setOnStop(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnStop()) );
	}


	/*
	 * onIEnable
	 */
	if( theBehavior->hasOnIEnable()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnIEnable()) )
	{
		anExecutableForm.setOnIEnable(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnIEnable()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm.setOnIEnable(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				StatementConstructor::newComment( "begin<ienable> " +
						anExecutableForm.getFullyQualifiedNameID() ),

				anExecutableForm.getOnIEnable(),

				StatementConstructor::newComment( "end<ienable> " +
						anExecutableForm.getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	}

	/*
	 * onEnable
	 */
	if( theBehavior->hasOnEnable()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnEnable()) )
	{
		anExecutableForm.setOnEnable(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnEnable()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm.setOnEnable(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				StatementConstructor::newComment( "begin<enable> " +
						anExecutableForm.getFullyQualifiedNameID() ),

				anExecutableForm.getOnEnable(),

				StatementConstructor::newComment( "end<enable> " +
						anExecutableForm.getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	}

	// EXPAND IENABLE / ENABLE
	if( anExecutableForm.hasOnIEnable() )
	{
		if( anExecutableForm.hasOnEnable() )
		{
			if( not AvmCodeFactory::contains(anExecutableForm,
					anExecutableForm.getOnEnable(), AVM_OPCODE_IENABLE_INVOKE) )
			{
				anExecutableForm.setOnEnable(
						StatementConstructor::newCodeFlat(
								OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

								anExecutableForm.getOnIEnable(),

								anExecutableForm.getOnEnable() ) );
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
			anExecutableForm.setOnEnable( anExecutableForm.getOnIEnable() );
		}
	}



	/*
	 * onIDisable
	 */
	if( theBehavior->hasOnIDisable()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnIDisable()) )
	{
		anExecutableForm.setOnIDisable(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnIDisable()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm.setOnIDisable(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
				StatementConstructor::newComment( "begin<idisable> " +
						anExecutableForm.getFullyQualifiedNameID() ),

				anExecutableForm.getOnIDisable(),

				StatementConstructor::newComment( "end<idisable> " +
						anExecutableForm.getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	}

	/*
	 * onDisable
	 */
	if( theBehavior->hasOnDisable()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnDisable()) )
	{
		anExecutableForm.setOnDisable(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnDisable()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm.setOnDisable(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
				StatementConstructor::newComment( "begin<disable> " +
						anExecutableForm.getFullyQualifiedNameID() ),

				anExecutableForm.getOnDisable(),

				StatementConstructor::newComment( "end<disable> " +
						anExecutableForm.getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

		anExecutableForm.setOnDisable( StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				anExecutableForm.getOnDisable(),

				StatementConstructor::newCode(
						OperatorManager::OPERATOR_DISABLE_SELF) ) );
	}

	// EXPAND IDISABLE / DISABLE
	if( anExecutableForm.hasOnIDisable() )
	{
		if( anExecutableForm.hasOnDisable() )
		{
			if( not AvmCodeFactory::contains(anExecutableForm,
				anExecutableForm.getOnDisable(), AVM_OPCODE_IDISABLE_INVOKE) )
			{
				anExecutableForm.setOnDisable(
						StatementConstructor::newCodeFlat(
								OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

								anExecutableForm.getOnIDisable(),

								anExecutableForm.getOnDisable() ) );
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
			anExecutableForm.setOnDisable( StatementConstructor::newCodeFlat(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

					anExecutableForm.getOnIDisable(),

					StatementConstructor::newCode(
							OperatorManager::OPERATOR_DISABLE_SELF) ) );
		}

		anExecutableForm.setOnIDisable( StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				anExecutableForm.getOnIDisable(),

				StatementConstructor::newCode(
						OperatorManager::OPERATOR_DISABLE_SELF) ) );
	}


	/*
	 * onIAbort
	 */
	if( theBehavior->hasOnIAbort()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnIAbort()) )
	{
		anExecutableForm.setOnIAbort(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnIAbort()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm.setOnIAbort(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
				StatementConstructor::newComment( "begin<iabort> " +
						anExecutableForm.getFullyQualifiedNameID() ),

				anExecutableForm.getOnIAbort(),

				StatementConstructor::newComment( "end<iabort> " +
						anExecutableForm.getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	}

	/*
	 * onAbort
	 */
	if( theBehavior->hasOnAbort()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnAbort()) )
	{
		anExecutableForm.setOnAbort(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnAbort()) );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		anExecutableForm.setOnAbort(StatementConstructor::newCodeFlatMiddle(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
				StatementConstructor::newComment( "begin<abort> " +
						anExecutableForm.getFullyQualifiedNameID() ),

				anExecutableForm.getOnAbort(),

				StatementConstructor::newComment( "end<abort> " +
						anExecutableForm.getFullyQualifiedNameID() ) ) );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

		anExecutableForm.setOnAbort( StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				anExecutableForm.getOnAbort(),

				StatementConstructor::newCode(
						OperatorManager::OPERATOR_ABORT_SELF) ) );
	}

	// EXPAND IABORT / ABORT
	if( anExecutableForm.hasOnIAbort() )
	{
		if( anExecutableForm.hasOnAbort() )
		{
			if( not AvmCodeFactory::contains(anExecutableForm,
				anExecutableForm.getOnAbort(), AVM_OPCODE_IABORT_INVOKE) )
			{
				anExecutableForm.setOnAbort(
						StatementConstructor::newCodeFlat(
								OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

								anExecutableForm.getOnIAbort(),

								anExecutableForm.getOnAbort() ) );
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
			anExecutableForm.setOnAbort( StatementConstructor::newCodeFlat(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

					anExecutableForm.getOnIAbort(),

					StatementConstructor::newCode(
							OperatorManager::OPERATOR_ABORT_SELF) ) );
		}

		anExecutableForm.setOnIAbort( StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

				anExecutableForm.getOnIAbort(),

				StatementConstructor::newCode(
						OperatorManager::OPERATOR_ABORT_SELF) ) );
	}


	/*
	 * onIRun
	 */
	if( theBehavior->hasOnIRun()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnIRun()) )
	{
		anExecutableForm.setOnIRun(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnIRun()) );
	}

	/*
	 * onRun
	 */
	if( theBehavior->hasOnRun()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnRun()) )
	{
		anExecutableForm.setOnRun(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnRun()) );
	}

	/*
	 * onRtc
	 */
	if( theBehavior->hasOnRtc()
		&& StatementTypeChecker::doSomething(* theBehavior->getOnRtc()) )
	{
		anExecutableForm.setOnRtc(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnRtc()) );
	}


	/*
	 * onSchedule
	 */
	if( theBehavior->hasOnSchedule() )
	{
		if( StatementTypeChecker::isEmptySchedule(* theBehavior->getOnSchedule()) )
		{
			//!! NOTHING
		}
		else
		{
			anExecutableForm.setOnSchedule(
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
		if( StatementTypeChecker::isEmptySchedule(* theBehavior->getOnConcurrency()) )
		{
			anExecutableForm.setOnConcurrency( theBehavior->getOnConcurrency() );
		}
		else
		{
			anExecutableForm.setOnConcurrency(
					mAvmcodeCompiler.compileStatement(
							anExecutableForm, theBehavior->getOnConcurrency()) );
		}
	}
	else if( StatementTypeChecker::isSchedule(theBehavior->getOnSchedule()) )
	{
		anExecutableForm.setOnConcurrency(
				theBehavior->getOnSchedule().getOperator() );
	}


	/*
	 * onSynchronize
	 */
	if( theBehavior->hasOnSynchronize() )
	{
		anExecutableForm.setOnSynchronize(
				mAvmcodeCompiler.compileStatement(
						anExecutableForm, theBehavior->getOnSynchronize()) );
	}


	/*
	 * other user Routines
	 */
	for( const auto & itRoutine : theBehavior->getRoutines() )
	{
		anExecutableForm.saveProgram(
				mAvmcodeCompiler.compileRoutine(*this,
						anExecutableForm, itRoutine.to< Routine >() ) );
	}


//AVM_OS_TRACE << TAB << ">| compiling<machine>: "
//		<< str_header( aMachine ) << std::endl << std::endl;
}


/**
 * compile
 * executable procedure
 */
void Compiler::compileProcedure(ExecutableForm & anExecutableForm)
{
	// Compile data & all machine MOE program
	compileBaseMachine(anExecutableForm);

	const Machine & aProcedure = anExecutableForm.getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aProcedure ) << std::endl;

	// PUSH MOC
	const WObject * moc_transition = nullptr;//aProcedure::getTransitionMoc();
	if( moc_transition != nullptr )
	{
		mTransitionCompiler.pushMoc(moc_transition);
	}


	// Compile all specific statemachine
	if( aProcedure.getSpecifier().isStateBasic() )
	{
		compileStatemachineBasic(anExecutableForm);
	}

	else if( aProcedure.getSpecifier().isMocStateTransitionStructure() )
	{
		compileExecutableMocStateTransitionStructure(anExecutableForm);
	}
	else if( aProcedure.getSpecifier().isMocCompositeStructure() )
	{
		compileExecutableMocCompositeStructure(anExecutableForm);
	}

	else
	{
		// MOC Attribute for mutable Schedule
		anExecutableForm.setMutableSchedule(
				anExecutableForm.hasOnSchedule() );

		/*
		 * Compiling communication
		 */
		bool hasSynchronizeMachine = false;
		bool hasUpdateBuffer = false;

		mComCompiler.compileCommunication(anExecutableForm,
				hasUpdateBuffer, hasSynchronizeMachine);

		if( anExecutableForm.hasOnRun() )
		{
			//!! NOTHING
		}
		else if( anExecutableForm.hasOnSchedule() )
		{
			anExecutableForm.setOnRun( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SCHEDULE_INVOKE));
		}
	}

	// POP MOC
	if( moc_transition != nullptr )
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
void Compiler::compileMachine(ExecutableForm & anExecutableForm)
{
//AVM_OS_TRACE << TAB << "<| compiling<machine>: "
//		<< str_header( aMachine ) << std::endl;

	// COMPILE PROGRAM
	if( anExecutableForm.hasProgram() )
	{
		compilePrograms( anExecutableForm );
	}

	const Machine & aMachineSpec = anExecutableForm.getAstMachine();

	// Compile all specific machine
	if( aMachineSpec.getSpecifier().isMocStateTransitionStructure() )
	{
		compileExecutableMocStateTransitionStructure(anExecutableForm);
	}
	else if( aMachineSpec.getSpecifier().isMocCompositeStructure() )
	{
		compileExecutableMocCompositeStructure(anExecutableForm);
	}
	else
	{
		// MOC Attribute for mutable Schedule
		anExecutableForm.setMutableSchedule(
				anExecutableForm.hasOnSchedule() );

		/*
		 * Compiling communication
		 */
		bool hasSynchronizeMachine = false;
		bool hasUpdateBuffer = false;

		mComCompiler.compileCommunication(anExecutableForm,
				hasUpdateBuffer, hasSynchronizeMachine);

		if( anExecutableForm.hasOnRun() )
		{
			//!! NOTHING
		}
		else if( anExecutableForm.hasOnSchedule() )
		{
			anExecutableForm.setOnRun( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SCHEDULE_INVOKE));
		}

		if( //aMachineSpec.getOwnedElementsSpecifier().hasStateMocFINAL()
			(not anExecutableForm.getSpecifier().isComponentProcedure())
			&& (not anExecutableForm.hasOnIRun())
			&& (not anExecutableForm.hasOnFinal()) )
		{
			const BFCode & onFinal = ( aMachineSpec.hasBehaviorPart()
					&& aMachineSpec.getBehavior()->hasOnFinal() ) ?
							anExecutableForm.getOnDisable() : BFCode::REF_NULL;

			anExecutableForm.setOnFinal(
					StatementConstructor::xnewCodeFlat(
							OperatorManager::OPERATOR_SEQUENCE, onFinal,
							StatementConstructor::newCode(
									OperatorManager::OPERATOR_PROCESS_STATE_SET,
									ExecutableLib::MACHINE_THIS,
									INCR_BF(OperatorManager::OPERATOR_FINAL)),
							StatementConstructor::newCode(
									OperatorManager::OPERATOR_FINAL,
									ExecutableLib::MACHINE_PARENT)) );
		}
	}

//AVM_OS_TRACE << TAB << ">| compiling<machine>: "
//		<< str_header( aMachine ) << std::endl << std::endl;
}


/**
 * compile
 * specification
 */
void Compiler::compileSystem(ExecutableForm & anExecutableForm)
{
	const System & aSystem = anExecutableForm.getAstSystem();

//AVM_OS_TRACE << TAB << "<| compiling<system>: "
//		<< aSystem.getFullyQualifiedNameID() << std::endl;

	// Compile all specific machine
	if( aSystem.getSpecifier().isMocStateTransitionStructure() )
	{
		compileExecutableMocStateTransitionStructure(anExecutableForm);
	}
	else //if( aSystem.getSpecifier().isMocCompositeStructure()
		//|| (not aSystem.hasRunnableBehavior()) )
	{
		compileExecutableMocCompositeStructure(anExecutableForm);
	}

	if( not anExecutableForm.hasOnInit() )
	{
		anExecutableForm.setOnInit( StatementConstructor::nopCode() );
	}

	if( anExecutableForm.hasOnIRun() )
	{
		if( anExecutableForm.hasOnRun() )
		{
			anExecutableForm.setOnRun(
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE_SIDE,
							anExecutableForm.getOnIRun(),
							anExecutableForm.getOnRun()) );
		}
		else
		{
			anExecutableForm.setOnRun( anExecutableForm.getOnIRun() );
		}
	}
	else
	{
		if( (not anExecutableForm.hasOnSchedule())
			&& (not anExecutableForm.hasOnRun()) )
		{
			anExecutableForm.setOnRun( StatementConstructor::nopCode() );
		}

		if( not anExecutableForm.hasOnFinal() )
		{
			anExecutableForm.setOnFinal(
//					StatementConstructor::newCode(
//							OperatorManager::OPERATOR_PROCESS_STATE_SET,
//							ExecutableLib::MACHINE_THIS,
//							INCR_BF(OperatorManager::OPERATOR_FINAL)));

					StatementConstructor::xnewCodeFlat(
							OperatorManager::OPERATOR_SEQUENCE,
							StatementConstructor::newCode(
									OperatorManager::OPERATOR_PROCESS_STATE_SET,
									ExecutableLib::MACHINE_THIS,
									INCR_BF(OperatorManager::OPERATOR_FINAL)),
							StatementConstructor::newCode(
									OperatorManager::OPERATOR_EXIT,
									ExpressionConstructor::newString("FINALIZE")) ));
		}
	}

//AVM_OS_TRACE << TAB << ">| compiling<system>: "
//		<< aSystem.getFullyQualifiedNameID() << std::endl << std::endl;
}




/**
 * compile
 * statemachine
 */
void Compiler::compileStatemachine(ExecutableForm & anExecutableForm)
{
	const Machine & aStatemachine = anExecutableForm.getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;

	// PUSH MOC
	const WObject * moc_transition = nullptr;//aStatemachine::getTransitionMoc();
	if( moc_transition != nullptr )
	{
		mTransitionCompiler.pushMoc(moc_transition);
	}

	// Compile all specific statemachine
	if( aStatemachine.getSpecifier().hasFamilyPseudostateEnding() )
	{
		compilePseudostateEnding(anExecutableForm);
	}
	else if( aStatemachine.getSpecifier().hasPseudostateMocHISTORY() )
	{
		compileStatemachineHistory(anExecutableForm);
	}
	else  if( aStatemachine.getSpecifier().isPseudostate() )
	{
		compileStatemachinePseudo(anExecutableForm);
	}

	else if( aStatemachine.getSpecifier().isStateBasic() )
	{
		compileStatemachineBasic(anExecutableForm);
	}

	else if( aStatemachine.getSpecifier().isMocStateTransitionStructure() )
	{
		compileExecutableMocStateTransitionStructure(anExecutableForm);
	}
	else if( aStatemachine.getSpecifier().isMocCompositeStructure() )
	{
		compileExecutableMocCompositeStructure(anExecutableForm);
	}
	else if( aStatemachine.getSpecifier().isComponentProcedure() )
	{
		compileExecutableMocCompositeStructure(anExecutableForm);
	}

	else
	{
		incrErrorCount();
		aStatemachine.errorLocation(AVM_OS_WARN)
				<< "Unexpected statemachine type << "
				<< str_header( aStatemachine ) << " >>"
				<< std::endl << std::endl;
	}


	// COMPILE TRANSITION
	if( anExecutableForm.hasTransition() )
	{
		std::size_t offset = 0;
		for( ; offset < anExecutableForm.getTransition().size() ; ++offset )
		{
			AvmTransition & aTransition =
					anExecutableForm.getTransition().refAt(offset);

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<transition>: "
			<< aTransition.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

			mTransitionCompiler.compileTransition( aTransition );

AVM_IF_DEBUG_FLAG( COMPILING )
//	(*itProg)->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| compiling<transition>: "
			<< aTransition.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( COMPILING )
		}

		if( anExecutableForm.getSpecifier().hasFeatureInputEnabled() )
		{
			computeInputEnabledCom( anExecutableForm );
		}
	}


	// COMPILE PROGRAM
	if( anExecutableForm.hasProgram() )
	{
		compilePrograms( anExecutableForm );

		if( anExecutableForm.getSpecifier().hasFeatureInputEnabled() )
		{
			computeInputEnabledCom( anExecutableForm );
		}
	}


	// POP MOC
	if( moc_transition != nullptr )
	{
		mTransitionCompiler.popMoc();
	}

//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;
}


void Compiler::compileExecutableMocCompositeStructure(
		ExecutableForm & anExecutableForm)
{
	const Machine & anExecutableSpec = anExecutableForm.getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling executable< moc: and >: "
//		<< str_header( anExecutableSpec ) << std::endl;

	bool hasInstanceStatic = anExecutableSpec.hasMachine();
	bool hasSynchronizeMachine = false;
	bool hasUpdateBuffer = false;


	// MOC Attribute for mutable Schedule
	anExecutableForm.setMutableSchedule( false );

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
			anExecutableForm.setRdvCommunication( hasSynchronizeMachine );

			setRdvScheduling( anExecutableForm );
		}

		if( anExecutableForm.hasOnRun() )
		{
			onRunProgram = anExecutableForm.getOnRun();

			anExecutableForm.setOnRun( BFCode::REF_NULL );

			if( not AvmCodeFactory::contains(anExecutableForm,
					onRunProgram, AVM_OPCODE_SCHEDULE_INVOKE) )
			{
//				if( (not anExecutableForm.hasOnRtc())
//					&& AvmCodeFactory::contains(anExecutableForm,
//								onRunProgram, AVM_OPCODE_RTC) )
//				{
//					anExecutableForm.setOnRtc(
//							StatementConstructor::newCode(
//								OperatorManager::OPERATOR_SCHEDULE_INVOKE) );
//				}
//				else
					if( anExecutableForm.hasOnSchedule()
						|| anExecutableForm.isMutableSchedule() )
				{
					onRunProgram = StatementConstructor::newCodeFlat(
							OperatorManager::OPERATOR_SEQUENCE, onRunProgram,
							StatementConstructor::newCode(
								OperatorManager::OPERATOR_SCHEDULE_INVOKE) );
				}
			}
		}
		else if( anExecutableForm.hasOnSchedule()
				|| anExecutableForm.isMutableSchedule() )
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

	if( anExecutableSpec.hasOutgoingTransition() )
	{
		// Compile Statemachine Transition
		mTransitionCompiler.compileStatemachineTransition(
				anExecutableForm, onRunProgram );
	}
	else if( onRunProgram.valid() )
	{
		anExecutableForm.setOnRun( onRunProgram );
	}
	else if( anExecutableForm.hasOnIRun() )
	{
		anExecutableForm.setOnRun( StatementConstructor::nopCode() );
	}

	if( (not anExecutableForm.getSpecifier().isComponentSystem())
		&& (not anExecutableForm.hasOnIRun())
		&& (not anExecutableForm.hasOnFinal()) )
	{
		const BFCode & onFinal = ( anExecutableSpec.hasBehaviorPart()
				&& anExecutableSpec.getBehavior()->hasOnFinal() ) ?
						anExecutableForm.getOnDisable() : BFCode::REF_NULL;

		anExecutableForm.setOnFinal(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE, onFinal,
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_PROCESS_STATE_SET,
								ExecutableLib::MACHINE_THIS,
								INCR_BF(OperatorManager::OPERATOR_FINAL)),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_FINAL,
								ExecutableLib::MACHINE_PARENT)) );
	}


//AVM_OS_TRACE << TAB << ">| compiling executable< moc: and >: "
//		<< str_header( anExecutableSpec ) << std::endl;
}


void Compiler::compileExecutableMocStateTransitionStructure(
		ExecutableForm & anExecutableForm)
{
	const Machine & anExecutableSpec = anExecutableForm.getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling executable< moc: and >: "
//		<< str_header( anExecutableSpec ) << std::endl;

	bool hasSynchronizeMachine = false;
	bool hasUpdateBuffer = false;

//	/*
//	 * Compiling program
//	 */
//	if( anExecutableForm.hasProgram() )
//	{
//		compilePrograms( anExecutableForm );
//	}


	// MOC Attribute for mutable Schedule
	anExecutableForm.setMutableSchedule( true );

	if( anExecutableSpec.hasMachine() )
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

		bool hasnotOwnedPseudostateHistory = (not anExecutableSpec.
				getOwnedElementsSpecifier().hasPseudostateMocHISTORY());

		bool hasOwnedPseudostateInitialOrStateStartOrMachineInit =
				(anExecutableSpec.getOwnedElementsSpecifier()
						.hasMocINITIAL_START()
				|| anExecutableSpec.hasOnInitMachine());

		TableOfSymbol::const_iterator itMachine =
				anExecutableForm.instance_static_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm.instance_static_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			const Specifier & itSpecifier =
					(*itMachine).getExecutable().getSpecifier();

			if( itSpecifier.isPseudostateInitialOrStateStart()
				|| (itSpecifier.isComponentExecutable()
					&& itSpecifier.hasMocINITIAL_START()) )
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
			else if( not hasOwnedPseudostateInitialOrStateStartOrMachineInit )
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
		if( onInitCode->hasOperand() )
		{
			anExecutableForm.setOnInit( StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					anExecutableForm.getOnInit(),
					(onInitCode->hasOneOperand() ?
							onInitCode->first().bfCode() : onInitCode) ) );
		}

		// ON ENABLE
		if( onEnableCode->hasOperand() )
		{
			anExecutableForm.setOnEnable( StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					anExecutableForm.getOnEnable(),
					(onEnableCode->hasOneOperand() ?
							onEnableCode->first().bfCode() : onEnableCode) ) );
		}

		/**
		 * ON SCHEDULE
		 */
		if( anExecutableForm.hasOnSchedule())
		{
			if( anExecutableForm.getSpecifier().isFamilyComponentStatemachine() )
			{
				incrErrorCount();
				anExecutableSpec.errorLocation(AVM_OS_WARN)
						<< "Unexpected a State-Transition-System << "
						<< str_header( anExecutableSpec )
						<< " >> with user schedule code: "
						<< anExecutableForm.getOnSchedule() << std::endl;
			}
		}
		else if( onScheduleCode->hasOperand() )
		{
			anExecutableForm.setOnSchedule( onScheduleCode->hasOneOperand() ?
						onScheduleCode->first().bfCode() : onScheduleCode);
		}
		else if( anExecutableForm.hasOneInstanceStatic() )
		{
			anExecutableForm.setOnSchedule( StatementConstructor::newCode(
					OperatorManager::OPERATOR_RUN,
					anExecutableForm.firstInstanceStatic() ) );
		}
		else if( anExecutableForm.hasOnInitMachine() )
		{
			anExecutableForm.setOnSchedule( StatementConstructor::newCode(
					OperatorManager::OPERATOR_RUN,
					anExecutableForm.getOnInit()->first() ) );
		}
		else if( anExecutableForm.hasOnInit() )
		{
			BFList schedulableMachine;

			StatementFactory::collectActivityMachine(AVM_OPCODE_INIT,
					anExecutableForm.getOnInit(), schedulableMachine);

			for( const auto & machine : schedulableMachine )
			{
				onScheduleCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_RUN, machine) );
			}

			if( onScheduleCode->hasOperand() )
			{
				anExecutableForm.setOnSchedule( onScheduleCode->hasOneOperand() ?
							onScheduleCode->first().bfCode() : onScheduleCode);
			}
		}

		/*
		 * ON_DISABLE
		 */
		if( anExecutableForm.hasOnDisable() )
		{
			anExecutableForm.setOnDisable(
					StatementConstructor::newCodeFlat(
							OperatorManager::OPERATOR_SEQUENCE,
							StatementConstructor::newCode(
									OperatorManager::OPERATOR_DISABLE_CHILD),
							anExecutableForm.getOnDisable() ) );
		}
		else
		{
			anExecutableForm.setOnDisable( StatementConstructor::newCode(
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
	if( anExecutableSpec.hasMachine() )
	{
		if( hasSynchronizeMachine ) 	// only if has RDV protocol
		{
			anExecutableForm.setRdvCommunication( hasSynchronizeMachine );

			setRdvScheduling( anExecutableForm );
		}

		if( anExecutableForm.hasOnRun() )
		{
			onRunProgram = anExecutableForm.getOnRun();

			if( AvmCodeFactory::contains(anExecutableForm,
					onRunProgram, AVM_OPCODE_SCHEDULE_INVOKE) )
			{
				//!!NOTHING
			}
//			else if( (not anExecutableForm.hasOnRtc())
//					&& AvmCodeFactory::contains(anExecutableForm,
//							onRunProgram, AVM_OPCODE_RTC) )
//			{
//				anExecutableForm.setOnRtc(
//						StatementConstructor::newCode(
//								OperatorManager::OPERATOR_SCHEDULE_INVOKE) );
//			}
//			else
			{
				onRunProgram = StatementConstructor::newCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE, onRunProgram,
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_SCHEDULE_INVOKE) );
			}

			anExecutableForm.setOnRun( BFCode::REF_NULL );
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

	if( anExecutableSpec.hasOutgoingTransition() )
	{
		// Compile Statemachine Transition
		mTransitionCompiler.compileStatemachineTransition(
				anExecutableForm, onRunProgram);
	}
	else if( onRunProgram.valid() )
	{
		anExecutableForm.setOnRun( onRunProgram );
	}
	else if( anExecutableForm.hasOnIRun() )
	{
		anExecutableForm.setOnRun( StatementConstructor::nopCode() );
	}

	if( anExecutableSpec.getOwnedElementsSpecifier().hasStateMocFINAL()
		&& (not anExecutableForm.getSpecifier().isComponentSystem())
		&& (not anExecutableForm.hasOnIRun())
		&& (not anExecutableForm.hasOnFinal()) )
	{
		const BFCode & onFinal = ( anExecutableSpec.hasBehaviorPart()
				&& anExecutableSpec.getBehavior()->hasOnFinal() ) ?
						anExecutableForm.getOnDisable() : BFCode::REF_NULL;

		anExecutableForm.setOnFinal(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE, onFinal,
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_PROCESS_STATE_SET,
								ExecutableLib::MACHINE_THIS,
								INCR_BF(OperatorManager::OPERATOR_FINAL)),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_FINAL,
								ExecutableLib::MACHINE_PARENT)) );
	}


//AVM_OS_TRACE << TAB << ">| compiling executable< moc: and >: "
//		<< str_header( anExecutableSpec ) << std::endl;
}


void Compiler::compilePseudostateEnding(ExecutableForm & anExecutableForm)
{
	const Machine & aStatemachine = anExecutableForm.getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;

	// MOC Attribute for mutable Schedule
	anExecutableForm.setMutableSchedule( false );

	/*
	 * ON ENABLE
	 */
	BFCode onTerminalCode;

	if( aStatemachine.getSpecifier().isPseudostateTerminal() )
	{
		onTerminalCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_DESTROY, ExecutableLib::MACHINE_PARENT);
	}
	else //if( aStatemachine.getSpecifier().isPseudostateReturn() )
	{
		onTerminalCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_FINAL);
	}

	anExecutableForm.setOnEnable( StatementConstructor::xnewCodeFlat(
			OperatorManager::OPERATOR_SEQUENCE,
			anExecutableForm.getOnEnable(), onTerminalCode) );

	if( aStatemachine.hasOutgoingTransition() )
	{
		incrErrorCount();
		aStatemachine.errorLocation(AVM_OS_WARN)
				<< "Unexpected state< terminal > << "
				<< str_header( aStatemachine )
				<< " >> with outgoing transitions"
				<< std::endl << std::endl;
	}

//aStatemachine.toStream(AVM_OS_TRACE << TAB);
//anExecutableForm.toStream(AVM_OS_TRACE << TAB);
//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;
}


void Compiler::compileStatemachineHistory(ExecutableForm & anExecutableForm)
{
	const Machine & aStatemachine = anExecutableForm.getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;

	// MOC Attribute for mutable Schedule
	anExecutableForm.setMutableSchedule( false );

	if( aStatemachine.hasOutgoingTransition() )
	{
		// Compile Statemachine Transition
		mTransitionCompiler.compileStatemachineTransition(
				anExecutableForm , anExecutableForm.getOnRun());
	}

	BFCode onEnableCode = StatementConstructor::newCode(
			OperatorManager::OPERATOR_RUN);

	BFCode onHistoryCode = StatementConstructor::newCode(
			aStatemachine.getSpecifier().isPseudostateDeepHistory() ?
					OperatorManager::OPERATOR_DEEP_HISTORY_INVOKE :
					OperatorManager::OPERATOR_SHALLOW_HISTORY_INVOKE,
			ExecutableLib::MACHINE_PARENT);

	if( anExecutableForm.hasOnRun() )
	{
		anExecutableForm.setOnRun( StatementConstructor::xnewCodeFlat(
				OperatorManager::OPERATOR_PRIOR_GT,
				anExecutableForm.getOnRun(), onHistoryCode) );
	}
	else if( anExecutableForm.hasOnIRun() )
	{
		anExecutableForm.setOnRun( onHistoryCode );
	}
	else
	{
		onEnableCode = onHistoryCode;
	}


	/*
	 * ON INIT
	 * ON ENABLE
	 */
	// this is aStatemachine.getSpecifier().isPseudostate()
	// ON INIT
	anExecutableForm.setOnInit( StatementConstructor::xnewCodeFlat(
			OperatorManager::OPERATOR_SEQUENCE,
			anExecutableForm.getOnInit(), onEnableCode) );

	// ON ENABLE
	anExecutableForm.setOnEnable( StatementConstructor::xnewCodeFlat(
			OperatorManager::OPERATOR_SEQUENCE,
			anExecutableForm.getOnEnable(), onEnableCode) );

//aStatemachine.toStream(AVM_OS_TRACE << TAB);
//anExecutableForm.toStream(AVM_OS_TRACE << TAB);
//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;
}


void Compiler::compileStatemachinePseudo(ExecutableForm & anExecutableForm)
{
	const Machine & aStatemachine = anExecutableForm.getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;

	// MOC Attribute for mutable Schedule
	anExecutableForm.setMutableSchedule( false );

	/*
	 * ON INIT
	 * ON ENABLE
	 */
	BFCode onEnableCode  = StatementConstructor::newCode(
			OperatorManager::OPERATOR_RUN);

	// ON INIT
	if( aStatemachine.getSpecifier().isPseudostateInitial()
		&& anExecutableForm.hasOnEnable() )
	{
		anExecutableForm.setOnInit(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						anExecutableForm.getOnInit(),
						anExecutableForm.getOnEnable(), onEnableCode) );
	}
	else
	{
		anExecutableForm.setOnInit( StatementConstructor::xnewCodeFlat(
				OperatorManager::OPERATOR_SEQUENCE,
				anExecutableForm.getOnInit(), onEnableCode) );
	}

	anExecutableForm.setOnEnable(
			StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					anExecutableForm.getOnEnable(), onEnableCode) );



	/*
	 * Schedule State Transition
	 */
	if( aStatemachine.getSpecifier().isPseudostateFork() )
	{
		if( aStatemachine.hasOutgoingTransition()
			&& aStatemachine.getBehavior()->
					getOutgoingTransitions().populated() )
		{
			// Schedule State< fork > Transition
			mTransitionCompiler.compileStateForkOutputTransition(
					anExecutableForm, anExecutableForm.getOnRun());
		}
		else
		{
			incrErrorCount();
			aStatemachine.errorLocation(AVM_OS_WARN)
					<< "Unexpected pseudostate< fork > << "
					<< str_header( aStatemachine )
					<< " >> with less than 2 outgoing transitions"
					<< std::endl << std::endl;
		}
	}

	else if( aStatemachine.getSpecifier().isPseudostateJoin() )
	{
		if( aStatemachine.hasIncomingTransition()
			&& aStatemachine.getBehavior()->
					getIncomingTransitions().populated() )
		{
			// SYnchronize incoming Transition
			mTransitionCompiler.compileStateJoinInputTransition(
					anExecutableForm );
		}
		else
		{
			incrErrorCount();
			aStatemachine.errorLocation(AVM_OS_WARN)
					<< "Unexpected pseudostate< join > << "
					<< str_header( aStatemachine )
					<< " >> with less than 2 incoming transitions"
					<< std::endl << std::endl;
		}


		if( aStatemachine.hasOutgoingTransition() )
		{
			// Compile Statemachine Transition
			mTransitionCompiler.compileStatemachineTransition(
					anExecutableForm , anExecutableForm.getOnRun());
		}
		else
		{
			incrErrorCount();
			aStatemachine.errorLocation(AVM_OS_WARN)
					<< "Unexpected pseudostate< join > << "
					<< str_header( aStatemachine )
					<< " >> without outgoing transitions"
					<< std::endl << std::endl;
		}
	}


	else if( aStatemachine.hasOutgoingTransition() )
	{
		// Compile Statemachine Transition
		mTransitionCompiler.compileStatemachineTransition(
				anExecutableForm , anExecutableForm.getOnRun() );
	}


	if( not anExecutableForm.hasOnRun() )
	{
		if( not aStatemachine.getSpecifier().hasFamilyPseudostateENDING() )
		{
			incrWarningCount();
			aStatemachine.warningLocation(AVM_OS_WARN)
					<< "No eval code for << " << str_header( aStatemachine )
					<< " >> which is not TERMINAL or RETURN moc!" << std::endl;
		}
		else if( aStatemachine.getSpecifier().isPseudostateInitial() )
		{
			incrErrorCount();
			aStatemachine.errorLocation(AVM_OS_WARN)
					<< "No eval code for << " << str_header( aStatemachine )
					<< " >> which is an INITIAL state!!!" << std::endl;

			anExecutableForm.setOnRun( StatementConstructor::nopCode() );
		}
		AVM_OS_WARN << std::endl;

		if( anExecutableForm.hasOnIRun() )
		{
			anExecutableForm.setOnRun( StatementConstructor::nopCode() );
		}
	}

//aStatemachine.toStream(AVM_OS_TRACE << TAB);
//anExecutableForm.toStream(AVM_OS_TRACE << TAB);
//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;
}


void Compiler::compileStatemachineBasic(ExecutableForm & anExecutableForm)
{
	const Machine & aStatemachine = anExecutableForm.getAstMachine();

//AVM_OS_TRACE << TAB << "<| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;

	// MOC Attribute for mutable Schedule
	anExecutableForm.setMutableSchedule( false );


	// ON INIT
	if( aStatemachine.getSpecifier().isStateStart()
		&& anExecutableForm.hasOnEnable() )
	{
		anExecutableForm.setOnInit(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						anExecutableForm.getOnInit(),
						anExecutableForm.getOnEnable()) );
	}


	/*
	 * Schedule State Transition
	 */
	if( aStatemachine.getSpecifier().isStateFinal() )
	{
		anExecutableForm.setOnEnable(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						anExecutableForm.getOnEnable(),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_FINAL,
								ExecutableLib::MACHINE_THIS)) );

		anExecutableForm.setOnFinal(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						anExecutableForm.getOnFinal(),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_PROCESS_STATE_SET,
								ExecutableLib::MACHINE_THIS,
								INCR_BF(OperatorManager::OPERATOR_FINAL)),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_FINAL,
								ExecutableLib::MACHINE_PARENT)) );

		if( aStatemachine.hasOutgoingTransition() )
		{
			incrErrorCount();
			aStatemachine.errorLocation(AVM_OS_WARN)
					<< "Unexpected state< final > << "
					<< str_header( aStatemachine )
					<< " >> with outgoing transitions"
					<< std::endl << std::endl;
		}
	}


	else if( aStatemachine.hasOutgoingTransition() )
	{
		// Compile Statemachine Transition
		mTransitionCompiler.compileStatemachineTransition(
				anExecutableForm , anExecutableForm.getOnRun() );
	}

	if( aStatemachine.getSpecifier().isStateSync() )
	{
		Variable * aVar = new Variable(
				const_cast< Machine * >( & aStatemachine ),
				Modifier::PROPERTY_PUBLIC_VOLATILE_MODIFIER,
				TypeManager::INTEGER,
				aStatemachine.getNameID() + "#syncVar" );

		const_cast< Machine * >( & aStatemachine )->
				getPropertyPart().saveOwnedVariable( aVar );

		InstanceOfData * syncInstance = new InstanceOfData(
				IPointerVariableNature::POINTER_STANDARD_NATURE,
				(& anExecutableForm), (* aVar), TypeManager::INTEGER,
				anExecutableForm.getVariablesSize(),
				Modifier::PROPERTY_PUBLIC_VOLATILE_MODIFIER);
//!![MIGRATION]:MODIFIER
//				Modifier::PROPERTY_VOLATILE_FEATURE);
		syncInstance->setValue( ExpressionConstant::INTEGER_ZERO );

		const BF & syncVar = anExecutableForm.saveVariable(syncInstance);


		BFCode incrSyncVar = StatementConstructor::newCode(
				OperatorManager::OPERATOR_ASSIGN, syncVar,
				StatementConstructor::newCode(
						OperatorManager::OPERATOR_PLUS, syncVar,
						ExpressionConstant::INTEGER_ONE) );

		anExecutableForm.setOnEnable(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
						anExecutableForm.getOnEnable(), incrSyncVar) );


		BFCode decrSyncVar = StatementConstructor::newCode(
				OperatorManager::OPERATOR_ASSIGN, syncVar,
				StatementConstructor::newCode(
						OperatorManager::OPERATOR_PLUS, syncVar,
						ExpressionConstant::INTEGER_MINUS_ONE) );

		anExecutableForm.setOnDisable(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
						anExecutableForm.getOnDisable(), decrSyncVar) );


		BFCode guardSyncVar = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD,
				StatementConstructor::newCode(
						OperatorManager::OPERATOR_GT, syncVar,
						ExpressionConstant::INTEGER_ZERO) );

		anExecutableForm.setOnRun(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						guardSyncVar, anExecutableForm.getOnRun()) );
	}


	if( anExecutableForm.hasOnIRun()
		&& (not anExecutableForm.hasOnRun()) )
	{
		anExecutableForm.setOnRun( StatementConstructor::nopCode() );
	}

	if( (not anExecutableForm.hasOnRun())
		&& (not aStatemachine.getSpecifier().isStateFinal()) )
	{
		incrWarningCount();
		aStatemachine.warningLocation(AVM_OS_WARN)
				<< "No eval code for << " << str_header( aStatemachine )
				<< " >> which is not FINAL!"
				<< std::endl << std::endl;
	}

//aStatemachine.toStream(AVM_OS_TRACE << TAB);
//anExecutableForm.toStream(AVM_OS_TRACE << TAB);
//AVM_OS_TRACE << TAB << ">| compiling<statemachine>: "
//		<< str_header( aStatemachine ) << std::endl;
}


/**
 * compile
 * statemachine input_enabled
 */

void Compiler::removeSubmachineInputEnabledCode(
		const ExecutableForm & anExecutableForm)
{
	if( anExecutableForm.hasInstanceStatic() )
	{
		TableOfSymbol::const_iterator itMachine =
				anExecutableForm.instance_static_begin();
		TableOfSymbol::const_iterator endMachine =
				anExecutableForm.instance_static_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (*itMachine).machine().
					getSpecifier().isDesignPrototypeStatic()
				&& (*itMachine).getExecutable().hasOnRun() )
			{
				if( (*itMachine).getExecutable().
						getOnRun()->isOpCode( AVM_OPCODE_INPUT_ENABLED ) )
				{
					BFCode newCode = (*itMachine).getExecutable().
							getOnRun()->first().bfCode();

					const_cast< ExecutableForm & >(
							(*itMachine).getExecutable() ).setOnRun( newCode );
				}

				removeSubmachineInputEnabledCode((*itMachine).getExecutable());
			}
		}
	}
}


void Compiler::computeInputEnabledCom(ExecutableForm & anExecutableForm)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT(
			anExecutableForm.getSpecifier().hasFeatureInputEnabled() )
			<< "Unexpected a non INPUT_ENABLED Executable !!!"
			<< SEND_EXIT;

	// input enabled running code
	CommunicationDependency::computeInputEnabledCom(
			anExecutableForm, *( anExecutableForm.getOnRun() ) );

	if( anExecutableForm.getSpecifier().isState()
		|| anExecutableForm.getSpecifier().isPseudostate() )
	{
		computeInputEnabledBuffer( anExecutableForm );

		if( anExecutableForm.getInputEnabledBuffer().populated() )
		{
			incrErrorCount();
			anExecutableForm.getAstMachine().errorLocation(AVM_OS_WARN)
					<< "InputEnabled:> NO SUPPORT for multiple buffer "
							"at runtime for << "
					<< str_header( anExecutableForm.getAstMachine() )
					<< " >> !" << std::endl;

			AVM_OS_FATAL_ERROR_EXIT << "Expect the Future !!!" << SEND_EXIT;
		}
		else if( anExecutableForm.getInputEnabledBuffer().empty() )
		{
			incrErrorCount();
			anExecutableForm.getAstMachine().errorLocation(AVM_OS_WARN)
					<< "InputEnabled:> Unfound runtime buffer for << "
					<< str_header( anExecutableForm.getAstMachine() )
					<< " >> !" << std::endl;
		}

		if( anExecutableForm.hasContainer()
			&& anExecutableForm.getExecutableContainer()->hasTransition() )
		{
			//!! NOTHING
		}
		else
		{
			anExecutableForm.setOnRun( StatementConstructor::newCode(
					OperatorManager::OPERATOR_INPUT_ENABLED,
					anExecutableForm.getOnRun() ));

			removeSubmachineInputEnabledCode( anExecutableForm );
		}
	}
	else
	{

	}
}


void Compiler::computeInputEnabledBuffer(ExecutableForm & anExecutableForm)
{
	for( ExecutableForm * tmpExec = (& anExecutableForm) ; tmpExec != nullptr ;
			tmpExec = tmpExec->getExecutableContainer() )
	{
		if( tmpExec->hasBuffer() )
		{
			const TableOfSymbol & bufferTable = tmpExec->getBuffer();
			for( std::size_t offset = 0 ; offset < bufferTable.size() ; ++offset )
			{
				anExecutableForm.addInputEnabledBuffer(
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
void Compiler::compileAllBehavioralRoutines(ExecutableForm & theExecutable)
{
	const Machine & aMachine = theExecutable.getAstMachine();

	if( aMachine.hasMachine() )
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



void Compiler::compileBehaviorInitialization(ExecutableForm & theExecutable)
{
	BFCodeList listOfCode;

	ListOfInstanceOfMachine usedInstance;
	if( theExecutable.hasOnInit() )
	{
		StatementFactory::collectActivityMachine(AVM_OPCODE_INIT,
				AVM_OPCODE_START, theExecutable.getOnInit(), usedInstance);
	}

	TableOfSymbol::const_iterator itMachine =
			theExecutable.instance_static_begin();
	TableOfSymbol::const_iterator endMachine =
			theExecutable.instance_static_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( (*itMachine).getExecutable().isSchedulable()
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
	else if( not theExecutable.hasOnInit() )
	{
//		incrWarningCount();
		theExecutable.safeAstElement().warningLocation(AVM_OS_LOG)
					<< "Unfound InstanceStatic for onInit code compilation "
							"of composite machine << "
					<< theExecutable.getAstElement().getFullyQualifiedNameID()
					<< " >>" << std::endl << std::endl;
	}

	if( onInitCode.valid() )
	{
		theExecutable.setOnInit(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						theExecutable.getOnInit(), onInitCode) );
	}

	// onSTART
	theExecutable.setOnStart(
			StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					theExecutable.getOnStart(),
					theExecutable.getOnInit()) );
}


void Compiler::compileBehaviorEnabling(ExecutableForm & theExecutable)
{
	BFCodeList listOfCode;

	ListOfInstanceOfMachine usedInstance;
	if( theExecutable.hasOnEnable() )
	{
		StatementFactory::collectActivityMachine(AVM_OPCODE_ENABLE_INVOKE,
				theExecutable.getOnEnable(), usedInstance);
	}

	TableOfSymbol::const_iterator itMachine =
			theExecutable.instance_static_begin();
	TableOfSymbol::const_iterator endMachine =
			theExecutable.instance_static_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( ( (*itMachine).getExecutable().hasOnInit()
				|| (*itMachine).getExecutable().hasOnRun()
				|| (*itMachine).getExecutable().hasOnEnable() )
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
	else if( not theExecutable.hasOnInit() )
	{
//		incrWarningCount();
		theExecutable.safeAstElement().warningLocation(AVM_OS_LOG)
					<< "Unfound InstanceStatic for onEnable code compilation "
							"of composite machine << "
					<< theExecutable.getAstElement().getFullyQualifiedNameID()
					<< " >>" << std::endl << std::endl;
	}

	if( onEnableCode.valid() )
	{
		theExecutable.setOnEnable(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						theExecutable.getOnEnable(), onEnableCode) );
	}
}


void Compiler::compileBehaviorDisabling(ExecutableForm & theExecutable)
{
	BFCodeList listOfCode;

	ListOfInstanceOfMachine usedInstance;
	if( theExecutable.hasOnDisable() )
	{
		StatementFactory::collectActivityMachine(AVM_OPCODE_DISABLE_INVOKE,
				theExecutable.getOnDisable(), usedInstance);
	}

	TableOfSymbol::const_iterator itMachine =
			theExecutable.instance_static_begin();
	TableOfSymbol::const_iterator endMachine =
			theExecutable.instance_static_end();
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
		theExecutable.setOnDisable(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						onDisableCode, theExecutable.getOnDisable()) );
	}
}


void Compiler::compileBehaviorAborting(ExecutableForm & theExecutable)
{
	BFCodeList listOfCode;

	ListOfInstanceOfMachine usedInstance;
	if( theExecutable.hasOnAbort() )
	{
		StatementFactory::collectActivityMachine(AVM_OPCODE_ABORT_INVOKE,
				theExecutable.getOnAbort(), usedInstance);
	}

	TableOfSymbol::const_iterator itMachine =
			theExecutable.instance_static_begin();
	TableOfSymbol::const_iterator endMachine =
			theExecutable.instance_static_end();
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
		theExecutable.setOnAbort(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						onAbortCode, theExecutable.getOnAbort()) );
	}
}


void Compiler::compileBehaviorScheduling(ExecutableForm & theExecutable)
{
	ListOfInstanceOfMachine usedInstance;
	const Operator * defaultConcurrencyOp = nullptr;
	BFCode userScheduler;

	// INIT STEP
	// Collect unscheduled submachines
	// get default concurrency policy
	if( theExecutable.hasOnRun() )
	{
		StatementFactory::collectRunMachine(
				theExecutable.getOnRun(), usedInstance);
	}

	if( theExecutable.hasOnSchedule() )
	{
		userScheduler = theExecutable.getOnSchedule();

		if( userScheduler->noOperand() )
		{
			defaultConcurrencyOp = userScheduler->getOperator();
			theExecutable.setOnSchedule( userScheduler = BFCode::REF_NULL );
		}
		else
		{
			if( OperatorManager::isSchedule( userScheduler->getOperator() ) )
			{
				defaultConcurrencyOp = userScheduler->getOperator();
			}

			StatementFactory::collectRunMachine(userScheduler, usedInstance);
		}
	}

	if( theExecutable.hasOnConcurrency() )
	{
		defaultConcurrencyOp = theExecutable.getOnConcurrencyOperator();
	}
	else
	{
		if( defaultConcurrencyOp == nullptr )
		{
			defaultConcurrencyOp = OperatorManager::OPERATOR_INTERLEAVING;
		}

		theExecutable.setOnConcurrency(
				StatementConstructor::newCode(defaultConcurrencyOp) );
	}

	// USER DEFINED SCHEDULE
	if( theExecutable.getSpecifier().hasFeatureUserDefinedSchedule() )
	{
		return;
	}

	// ELSE
	const Machine & astMachine = theExecutable.getAstMachine();

	// STEP case for owned behaviors
	if( astMachine.hasOwnedBehavior()
		&& (usedInstance.size() <
				astMachine.getBehaviorPart()->getOwnedBehaviors().size()) )
	{
		BFCode aScheduleCode;

		if( userScheduler.valid() )
		{
			aScheduleCode = compileSchedulerRoutine(
					theExecutable, usedInstance, userScheduler);

			if( not aScheduleCode->isOperator( defaultConcurrencyOp ) )
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

		for( const auto & itBehavior :
				astMachine.getBehaviorPart()->getOwnedBehaviors() )
		{
			const Symbol & foundBehaviorInstance =
				theExecutable.getByAstInstanceStatic(itBehavior.to< Machine >());

			if( foundBehaviorInstance.getExecutable().isSchedulable()
				&& (not usedInstance.contains(foundBehaviorInstance.rawMachine())) )
			{
				aScheduleCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_RUN, foundBehaviorInstance) );
			}
		}

		if( aScheduleCode->hasOneOperand() )
		{
			aScheduleCode->getOperands().pop_last_to( userScheduler );

			if( userScheduler.valid() )
			{
				theExecutable.setOnSchedule( userScheduler );
			}
		}
		else if( aScheduleCode->hasOperand() )
		{
			theExecutable.setOnSchedule( aScheduleCode );
		}
	}


	// STEP case for singleton submachine
	else if( usedInstance.empty()
		&& theExecutable.hasOneInstanceStatic()
		&& theExecutable.hasOneInstanceModel() )
	{
		BFCode runMachineCode(OperatorManager::OPERATOR_RUN,
				theExecutable.getInstanceStatic().last());

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

			theExecutable.setOnSchedule( userScheduler );
		}
		else
		{
			theExecutable.setOnSchedule( runMachineCode );
		}
	}

	// STEP case for many submachines
	else if( usedInstance.size() < (theExecutable.sizeInstanceStatic()
									+ theExecutable.sizeInstanceModel()) )
	{
		BFCode aScheduleCode;

		if( userScheduler.valid() )
		{
			aScheduleCode = compileSchedulerRoutine(
					theExecutable, usedInstance, userScheduler);

			if( not aScheduleCode->isOperator( defaultConcurrencyOp ) )
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
				theExecutable.instance_static_begin();
		TableOfSymbol::const_iterator endInstance =
				theExecutable.instance_static_end();
		for( ; itInstance != endInstance ; ++itInstance )
		{
			if( (*itInstance).getExecutable().isSchedulable()
				&& (not usedInstance.contains((*itInstance).rawMachine())) )
			{
				aScheduleCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_RUN, (*itInstance)) );
			}
		}

		itInstance = theExecutable.instance_model_begin();
		endInstance = theExecutable.instance_model_end();
		for( ; itInstance != endInstance ; ++itInstance )
		{
			if( (*itInstance).machine().hasPossibleDynamicInstanciation()
				&& (*itInstance).getExecutable().isSchedulable()
				&& (not usedInstance.contains((*itInstance).rawMachine())) )
			{
				aScheduleCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_RUN, (*itInstance)) );
			}
		}

		if( aScheduleCode->hasOneOperand() )
		{
			aScheduleCode->getOperands().pop_last_to( userScheduler );

			if( userScheduler.valid() )
			{
				theExecutable.setOnSchedule( userScheduler );
			}
		}
		else if( aScheduleCode->hasOperand() )
		{
			theExecutable.setOnSchedule( aScheduleCode );
		}
	}
	else if( userScheduler.valid() )
	{
		theExecutable.setOnSchedule( compileSchedulerRoutine(
				theExecutable, usedInstance, userScheduler) );
	}
}


void Compiler::setRdvScheduling(ExecutableForm & theExecutable)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( theExecutable.hasRdvCommunication() )
			<< "Unexpected Executable without RDV comunication !!!"
			<< SEND_EXIT;


	const BFCode & aScheduleCode = theExecutable.getOnSchedule();
	switch( aScheduleCode->getAvmOpCode() )
	{
		case AVM_OPCODE_ASYNCHRONOUS:
		{
			aScheduleCode->setOperator(
					OperatorManager::OPERATOR_RDV_ASYNCHRONOUS );
			break;
		}

		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		{
			aScheduleCode->setOperator(
					OperatorManager::OPERATOR_RDV_STRONG_SYNCHRONOUS );
			break;
		}

		case AVM_OPCODE_WEAK_SYNCHRONOUS:
		{
			aScheduleCode->setOperator(
					OperatorManager::OPERATOR_RDV_WEAK_SYNCHRONOUS );
			break;
		}

		case AVM_OPCODE_INTERLEAVING:
		{
			aScheduleCode->setOperator(
					OperatorManager::OPERATOR_RDV_INTERLEAVING );
			break;
		}

		case AVM_OPCODE_PARALLEL:
		{
			aScheduleCode->setOperator(
					OperatorManager::OPERATOR_RDV_PARALLEL );
			break;
		}

		default:
		{
			theExecutable.setOnSchedule(StatementConstructor::newCode(
					OperatorManager::OPERATOR_SYNCHRONIZE, aScheduleCode));
			break;
		}
	}
}


}

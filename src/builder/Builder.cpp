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

#include "Builder.h"

#include <builder/Loader.h>

#include <builder/primitive/CompilationEnvironment.h>
#include <builder/primitive/AvmcodeUfiCastExpressionCompiler.h>

#include <computer/ExecutionEnvironment.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfConnector.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/operator/Operator.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/LocalRuntime.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/TableOfRuntimeFormState.h>

#include <fml/infrastructure/System.h>
#include <fml/runtime/LocalRuntime.h>

#include <fml/workflow/UniFormIdentifier.h>

#include <sew/Configuration.h>
#include <sew/SymbexEngine.h>

#include <util/ExecutionTime.h>


namespace sep
{


/**
 * LOADER
 */
void Builder::load()
{
	CompilationEnvironment::initCache();
}


/**
 * DISPOSER
 */
void Builder::dispose()
{
	CompilationEnvironment::finalizeCache();
}



/**
 * CONFIGURE
 */
bool Builder::configure()
{
	if( not mCompiler.configure() )
	{
		AVM_OS_ERROR_ALERT
				<< "Builder::configure:> "
					"the XLIA compiler configuration failed !!!"
				<< SEND_ALERT;

		return( false );
	}

	return( true );
}


/**
 * START
 */
bool Builder::start()
{
	// COMPILATION
//CHRONO
//AVM_OS_DEBUG << std::endl << "Building:> start chrono !" << std::endl;
//ExecutionTime chrono( true );

	if( mConfiguration.hasSpecification() )
	{
		mCompiler.start( mConfiguration.getSpecification() );

		mCompiler.reportCompilation(AVM_OS_LOG);
		if( mCompiler.hasError() )
		{
			mCompiler.reportCompilation(AVM_OS_COUT);
			mCompiler.reportCompilation(AVM_OS_TRACE);

			return( false );
		}
		else if( mCompiler.hasErrorWarning() )
		{
			mCompiler.reportCompilation(AVM_OS_COUT);
		}
	}
	else if( AVM_ERROR_COUNT == 0 )
	{
		++AVM_ERROR_COUNT;
	}


	if( (AVM_ERROR_COUNT > 0) && (AVM_WARNING_COUNT > 0) )
	{
		AVM_OS_EXIT( FAILED )
				<< "Compilation : error"
				<< ( (AVM_ERROR_COUNT > 0) ? "s " : " " ) << AVM_ERROR_COUNT
				<< " : warning"
				<< ( (AVM_ERROR_COUNT > 0) ? "s " : " " ) << AVM_WARNING_COUNT
				<< SEND_EXIT;
	}


//	CHRONO
//chrono.finish_time();
//AVM_OS_DEBUG << std::endl << "chrono stop:> " << chrono.time_stat() << std::endl;


AVM_IF_DEBUG_FLAG( COMPILING )
	mConfiguration.serializeDebugExecutable( "compiled" );
AVM_ENDIF_DEBUG_FLAG(COMPILING )


	// LOADING INSTANCE FOR EXECUTION
//CHRONO
//AVM_OS_DEBUG << std::endl << "Loading:> start chrono !" << std::endl;
//chrono.start_time();

	/*
	 * Creating the first/initial execution data/context
	 */
	ExecutionData theInitialExecutionData = createInitialExecutionData();

	mConfiguration.setMainExecutionData( theInitialExecutionData );

//!@! SPTG
	ExecutionContextHeader::ID_NUMBER--;

	ExecutionContext * anInitialExecutionContext =
			new ExecutionContext(theInitialExecutionData, 0, 1);


	mConfiguration.appendInputContext( anInitialExecutionContext );

//CHRONO
//chrono.finish_time();
//AVM_OS_DEBUG << std::endl << "chrono stop:> " << chrono.time_stat() << std::endl;

	return( true );
}


/*
 * Initial Execution Context creation
 */
ExecutionData Builder::createInitialExecutionData()
{
	ExecutableSystem & anExecutableSystem =
			mConfiguration.getExecutableSystem();

	ExecutionData theInitialExecutionData(
			anExecutableSystem.getMachineCount() + 1 /* for PARAMETERS */ );

	theInitialExecutionData.setNodeCondition(
			ExpressionConstant::BOOLEAN_TRUE );
	theInitialExecutionData.setNodeTimedCondition(
			ExpressionConstant::BOOLEAN_TRUE );

	theInitialExecutionData.setPathCondition(
			ExpressionConstant::BOOLEAN_TRUE );
	theInitialExecutionData.setPathTimedCondition(
			ExpressionConstant::BOOLEAN_TRUE );

	/*
	 * Loading instance
	 */
	int thePid = 0;
	avm_offset_t theOffset = 0;

	Loader & theLoader = mSymbexEngine.getLoader();

	/*
	 * Loading parameters instance
	 */
	// ExecutionData::PARAM_MACHINE_RUNTIME_OFFSET === theOffset === 0
	RuntimeID parametersRID(RuntimeID::nullref(), thePid++,
			theOffset++, anExecutableSystem.rawParametersInstance());

	mConfiguration.appendRID( parametersRID );

	theInitialExecutionData.saveRuntimeForm(parametersRID.getOffset(),
			new ParametersRuntimeForm( parametersRID ) );

	theInitialExecutionData.setRuntimeFormState(
			parametersRID.getOffset(), PROCESS_UNDEFINED_STATE);

	/*
	 * Loading system instance
	 */
	// ExecutionData::SYSTEM_RUNTIME_OFFSET === theOffset === 1
	RuntimeForm * theSystemRuntime = theLoader.loadSystemInstance(
			theInitialExecutionData, RuntimeID::nullref(),
			anExecutableSystem.rawSystemInstance(), thePid, theOffset);

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , LOADING )
	theSystemRuntime->toStream( AVM_OS_TRACE );
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , LOADING )

	/**
	 * RUNNING onCREATE
	 */
	if( not theLoader.finalizeRunningOnCreate(ENV, theInitialExecutionData) )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "createInitialExecutionContext:> Failed to finalize "
						"loading by running << onCreate Primitive >> !!!"
				<< SEND_EXIT;
	}

	// WARNING Assume possible auto-destruction of <theSystemExecutable>
	// after running< system->onCreate() > due to makeWritable... process !
	const RuntimeID & theSystemRID = theInitialExecutionData.getSystemRID();

	const ExecutableForm & theSystemExecutable = theSystemRID.refExecutable();


//!![MIGRATION]:MONITOR --> onCreate Routine
//	theLoader.loadInitialMonitorData(theInitialExecutionData,
//			theSystemRID, anExecutableSystem.rawSystemInstance(), true);

AVM_IF_DEBUG_FLAG( LOADING )
	mConfiguration.serializeDebugExecutable( "loaded" );
AVM_ENDIF_DEBUG_FLAG( LOADING )

	/*
	 * Setting the main program
	 */
	theInitialExecutionData.setOnInit( theSystemExecutable.getOnInit() );

	theInitialExecutionData.setOnSchedule( theSystemExecutable.getOnRun() );

//	if( theInitialExecutionData.getOnSchedule()->nonempty()
//		&& theInitialExecutionData.getOnSchedule()
//				->isOpCode( AVM_OPCODE_SCHEDULE_INVOKE )
//		&& theSystemExecutable->isMocKindAnd() )
//	{
//		theInitialExecutionData.setOnSchedule(
//				theSystemExecutable->getOnSchedule() );
//	}

	theInitialExecutionData.setSystemRID();

	theInitialExecutionData.setRuntimeFormState(
			theSystemRID, PROCESS_RUNNING_STATE );

	return( theInitialExecutionData );
}




/**
 * BUILDER
 * Replace a qualified element by its runtime's counterpart
 */
BF Builder::searchSymbolInstance(TableOfSymbol & aliasTable,
		const ExecutionData & anED, UniFormIdentifier * anUFI)
{
	std::ostringstream osUFI;

	std::string aFullyQualifiedNameID = anUFI->str();

	{
		const BF & foundInstance =
				aliasTable.getByFQNameID( aFullyQualifiedNameID );
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}


	if( anED.hasLocalRuntimeStack() )
	{
		StackOfLocalRuntime::const_reverse_iterator it =
				anED.getLocalRuntimes()->rbegin();
		StackOfLocalRuntime::const_reverse_iterator itEnd =
				anED.getLocalRuntimes()->rend();
		for(  ; it != itEnd ; ++it )
		{
			const BF & anInstance = (*it).getProgram()->getAllVariables().
					getByFQNameID( aFullyQualifiedNameID );
			if( anInstance.valid() )
			{
				return( anInstance );
			}
		}
	}


	UniFormIdentifier::iterator it = anUFI->begin();
	UniFormIdentifier::iterator itEnd = anUFI->end();

	// recherche de la machine PRINCIPALE (ROOT)
	osUFI << "inst::" << (*it).str();

	const RuntimeID & theSystemRID = anED.getSystemRID();
	RuntimeID theMachineID = theSystemRID;

	for( ++it ; (it != itEnd) ; ++it )
	{
		if( theMachineID.getInstance()->fqnEquals( osUFI.str() ) )
		{
			break;
		}
		osUFI << "." << (*it).str();
	}

	if( it != itEnd )
	{
		VectorOfInstanceOfMachine aliasPath;

		RuntimeID rid = theMachineID;

		// comme c'est la spec RID
//		aliasPath.append( theMachineID.getInstance() );

		// recherche de la machine FEUILLE
		for( ; it != itEnd ; ++it)
		{
			osUFI << "." << (*it).str();
			rid = anED.getRuntime(rid).getChild( osUFI.str() );
			if( rid.valid() )
			{
				theMachineID = rid;
				aliasPath.append( theMachineID.getInstance() );
			}
			else
			{
				break;
			}
		}

		if( (it == itEnd) && (theMachineID == theSystemRID) )
		{
			--it;
		}

		if( it != itEnd )
		{
			const ExecutableForm & anExecutable = theMachineID.refExecutable();
			osUFI.str( "" );

			osUFI << "inst::"      // with std::strlen( "exec::" ) --> 6
					<< anExecutable.getFullyQualifiedNameID().substr( 6 );

			for( ; it != itEnd ; ++it)
			{
				osUFI << "." << (*it).str();
			}


			// The ORIGINAL INSTANCE
			BF anInstance = anExecutable.getAllVariables().getByFQNameID(
					osUFI.str() );

			if( anInstance.invalid() )
			{
				anInstance = anExecutable.getConstVariable().getByFQNameID(
						osUFI.str() );
			}
			if( anInstance.invalid() )
			{
				anInstance = anExecutable.getPort().getByFQNameID(
						osUFI.str() );
			}
			if( anInstance.invalid() )
			{
				anInstance = anExecutable.getBuffer().getByFQNameID(
						osUFI.str() );
			}
			if( anInstance.invalid() )
			{
				anInstance = anExecutable.getConnector().getByFQNameID(
						osUFI.str() );
			}

			if( anInstance.valid() )
			{

//				AVM_OS_TRACE << TAB << "Searching " << anUFI->str() << std::endl
//						<< TAB << "Found " << std::endl;
//				anInstance.toStream(AVM_OS_TRACE << TAB);
//				AVM_OS_TRACE << std::flush;

				if( aliasPath.nonempty() )
				{
					BaseInstanceForm * newInstance = nullptr;

					switch ( anInstance.classKind() )
					{
						case FORM_INSTANCE_DATA_KIND:
						{
							newInstance = new InstanceOfData(
									theSystemRID.getExecutable(),
									anInstance.to< InstanceOfData >(),
									aliasPath);
							newInstance->setCreatorContainerRID( theMachineID );
							newInstance->setRuntimeContainerRID( theMachineID );
							aliasTable.save( newInstance );

							break;
						}

						case FORM_INSTANCE_MACHINE_KIND:
						{
							newInstance = new InstanceOfMachine(
									theSystemRID.getExecutable(),
									anInstance.to< InstanceOfMachine >(),
									aliasPath);
							newInstance->setCreatorContainerRID( theMachineID );
							newInstance->setRuntimeContainerRID( theMachineID );

							return( aliasTable.save( newInstance ) );
						}

						case FORM_INSTANCE_PORT_KIND:
						{
							newInstance = new InstanceOfPort(
									theSystemRID.getExecutable(),
									anInstance.to< InstanceOfPort >(),
									aliasPath);
							newInstance->setCreatorContainerRID( theMachineID );
							newInstance->setRuntimeContainerRID( theMachineID );

							return( aliasTable.save( newInstance ) );
						}

						case FORM_INSTANCE_BUFFER_KIND:
						{
							newInstance = new InstanceOfBuffer(
									theSystemRID.getExecutable(),
									anInstance.to< InstanceOfBuffer >(),
									aliasPath);
							newInstance->setCreatorContainerRID( theMachineID );
							newInstance->setRuntimeContainerRID( theMachineID );

							return( aliasTable.save( newInstance ) );
						}

						case FORM_INSTANCE_CONNECTOR_KIND:
						{
							newInstance = new InstanceOfConnector(
									theSystemRID.getExecutable(),
									anInstance.to< InstanceOfConnector >(),
									aliasPath);
							newInstance->setCreatorContainerRID( theMachineID );
							newInstance->setRuntimeContainerRID( theMachineID );

							return( aliasTable.save( newInstance ) );
						}

						default :
						{
							return( BF::REF_NULL );
						}
					}
				}
			}

			return( anInstance );
		}

		else if( aliasPath.nonempty() )
		{
			return( BF(	sep::incrReferenceCount(aliasPath.last()) ) );
		}


		else
		{
			AVM_OS_EXIT( FAILED )
					<< "Unfound leaf machine : " << osUFI.str()
					<< " >> container of << " << aFullyQualifiedNameID
					<< " >> !!!"
					<< SEND_EXIT;
		}
	}

	return( BF::REF_NULL );
}


const BF & Builder::searchSymbolInstance(TableOfSymbol & aliasTable,
		const ExecutionData & anED, const ObjectElement & astElement)
{
	{
		const BF & foundInstance = aliasTable.getByAstElement(astElement);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	if( anED.hasLocalRuntimeStack() )
	{
		StackOfLocalRuntime::const_reverse_iterator it =
				anED.getLocalRuntimes()->rbegin();
		StackOfLocalRuntime::const_reverse_iterator itEnd =
				anED.getLocalRuntimes()->rend();
		for( ; it != itEnd ; ++it )
		{
			const BF & anInstance =
					(*it).getProgram()->getAllVariables().getByAstElement(astElement);
			if( anInstance.valid() )
			{
				return( anInstance );
			}
		}
	}

	{
		ExecutableQuery XQuery( mConfiguration );

		const BF & foundInstance = XQuery.getInstanceByAstElement(astElement);

		return( foundInstance );
	}
}


const BF & Builder::searchSymbolInstance(TableOfSymbol & aliasTable,
		const ExecutionData & anED, const BF & aBaseInstance)
{
	if( aliasTable.contains(aBaseInstance) )
	{
		return( aBaseInstance );
	}

	if( anED.hasLocalRuntimeStack() )
	{
		StackOfLocalRuntime::const_reverse_iterator it =
				anED.getLocalRuntimes()->rbegin();
		StackOfLocalRuntime::const_reverse_iterator itEnd =
				anED.getLocalRuntimes()->rend();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).getProgram()->containsVariable( aBaseInstance ) )
			{
				return( aBaseInstance );
			}
		}
	}

	const RuntimeID & theSystemRID = anED.getSystemRID();

	VectorOfInstanceOfMachine aliasPath;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	for( RuntimeID itRID ; itRF != endRF ; ++itRF)
	{
		itRID = (*itRF)->getRID();

		switch( aBaseInstance.classKind() )
		{
			case FORM_INSTANCE_DATA_KIND:
			{
				if( itRID.refExecutable().containsVariable(
						aBaseInstance.to_ptr< InstanceOfData >() ) )
				{
					aliasPath.append( itRID.getInstance() );

					InstanceOfData * newInstance = new InstanceOfData(
							theSystemRID.getExecutable(),
							aBaseInstance.to< InstanceOfData >(), aliasPath);
					newInstance->setCreatorContainerRID( itRID );
					newInstance->setRuntimeContainerRID( itRID );

					aliasTable.save( newInstance );
				}

				break;
			}

			case FORM_INSTANCE_MACHINE_KIND:
			{
				if( itRID.refExecutable().
						getInstanceStatic().contains(aBaseInstance) )
				{
					aliasPath.append( itRID.getInstance() );

					InstanceOfMachine * newInstance = new InstanceOfMachine(
							theSystemRID.getExecutable(),
							aBaseInstance.to< InstanceOfMachine >(),
							aliasPath );
					newInstance->setCreatorContainerRID( itRID );
					newInstance->setRuntimeContainerRID( itRID );

					aliasTable.save( newInstance );
				}
				break;
			}

			case FORM_INSTANCE_PORT_KIND:
			{
				if( itRID.refExecutable().getPort().contains(aBaseInstance) )
				{
					aliasPath.append( itRID.getInstance() );

					InstanceOfPort * newInstance = new InstanceOfPort(
							theSystemRID.getExecutable(),
							aBaseInstance.to< InstanceOfPort >(), aliasPath);
					newInstance->setCreatorContainerRID( itRID );
					newInstance->setRuntimeContainerRID( itRID );

					aliasTable.save( newInstance );
				}
				break;
			}

			case FORM_INSTANCE_BUFFER_KIND:
			{
				const InstanceOfBuffer & bufferInstance =
						aBaseInstance.to< InstanceOfBuffer >();

				if( itRID.refExecutable().getBuffer().contains(& bufferInstance) )
				{
					aliasPath.append( itRID.getInstance() );

					InstanceOfBuffer * newInstance = new InstanceOfBuffer(
							theSystemRID.getExecutable(),
							bufferInstance, aliasPath );
					newInstance->setCreatorContainerRID( itRID );
					newInstance->setRuntimeContainerRID( itRID );

					aliasTable.save( newInstance );
				}
				break;
			}

			case FORM_INSTANCE_CONNECTOR_KIND:
			{
				const InstanceOfConnector & connectInstance =
						aBaseInstance.to< InstanceOfConnector >();

				if( itRID.refExecutable().
						getConnector().contains(& connectInstance) )
				{
					aliasPath.append( itRID.getInstance() );

					InstanceOfConnector * newInstance = new InstanceOfConnector(
							theSystemRID.getExecutable(),
							connectInstance, aliasPath );
					newInstance->setCreatorContainerRID( itRID );
					newInstance->setRuntimeContainerRID( itRID );

					aliasTable.save( newInstance );
				}
				break;
			}

			default :
			{
				break;
			}
		}
	}

	return( aBaseInstance );
}



BF Builder::build(TableOfSymbol & aliasTable,
		const ExecutionData & anED, const AvmProgram & aProgram, const BF & aCode)
{
	if( aProgram.hasVariable() )
	{
		bool destroyLocalRuntimeStackFlag = false;

		ExecutionData cloneED( anED );

		if( not cloneED.hasLocalRuntimeStack() )
		{
			destroyLocalRuntimeStackFlag = true;
			cloneED.createLocalRuntimeStack();
		}
		cloneED.getLocalRuntimes()->push( LocalRuntime(aProgram) );

		BF buildCode = build(aliasTable, cloneED, aCode);

		cloneED.getLocalRuntimes()->pop();
		if( destroyLocalRuntimeStackFlag )
		{
			cloneED.destroyLocalRuntimeStack();
		}


		return( buildCode );
	}
	else
	{
		return( build(aliasTable, anED, aCode) );
	}
}


BF Builder::build(const ExecutionData & anED, const BF & aCode)
{
	TableOfSymbol aliasTable;

	BF buildCode = build(aliasTable, anED, aCode);

	aliasTable.clear();

	return( buildCode );
}


BF Builder::build(TableOfSymbol & aliasTable,
		const ExecutionData & anED, const BF & aCode)
{
	BF compileCode = compile(aliasTable, anED, aCode);
	if( compileCode.is< AvmCode >() )
	{
		compileCode = mAvmcodeCompiler.optimizeExpression(
				mConfiguration.getExecutableSystem()
				.rawSystemInstance()->refExecutable(), compileCode.bfCode() );
	}

	return( ExpressionConstructor::newExpr( compileCode ) );
}


BF Builder::compile(TableOfSymbol & aliasTable,
		const ExecutionData & anED, const BF & aCode)
{
	switch( aCode.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & anAvmCode = aCode.to< AvmCode >();

			const Operator * mainOperator = anAvmCode.getOperator();

			BFCode newCode( mainOperator );

			for( const auto & itOperand : anAvmCode.getOperands() )
			{
				switch( itOperand.classKind() )
				{
					case FORM_AVMCODE_KIND:
					{
						BF bf = compile(aliasTable, anED, itOperand);

						if( bf.is< AvmCode >() )
						{
							const AvmCode & bfAvmCode = bf.to< AvmCode >();
							if( bfAvmCode.isOpCode( mainOperator )
								&& mainOperator->isAssociative() )
							{
								newCode->append( bfAvmCode.getOperands() );
							}
							else
							{
								newCode->append( bf );
							}
						}
						else
						{
							newCode->append( bf );
						}

						break;
					}


					default:
					{
						newCode->append( compile(aliasTable, anED, itOperand) );

						break;
					}
				}

			}

			return( newCode );
		}


		case FORM_UFI_KIND:
		{
			BF anInstance = searchSymbolInstance(aliasTable,
					anED, aCode.to_ptr< UniFormIdentifier>());

			if( anInstance.invalid() )
			{
				CompilationEnvironment compilENV(
						anED.getSystemRID().getExecutable());

				anInstance = getAvmcodeCompiler().UFI_EXPRESSION_COMPILER
						->compileUfiExpression(compilENV.mCTX,
								aCode.to< UniFormIdentifier>());
			}

			if( anInstance.valid() )
			{
				if( anInstance.is< InstanceOfData >() )
				{
					InstanceOfData * aData =
							anInstance.to_ptr< InstanceOfData >();
					if( aData->getModifier().hasFeatureFinal()
						&& aData->hasValue() )
					{
						return( aData->getValue() );
					}
				}

				return( anInstance );
			}
			else
			{
				ExecutableQuery XQuery( mConfiguration );

				const BF & aProgram =
						XQuery.getExecutableOrProgram(aCode.str());
				if( aProgram.valid() )
				{
					return( aProgram );
				}
				else
				{
					AVM_OS_EXIT( FAILED )
							<< "Unfound UFI symbol : " << aCode.str()
							<< SEND_EXIT;

					return( aCode );
				}
			}

			break;
		}

		case FORM_XFSP_BUFFER_KIND:
		case FORM_XFSP_CHANNEL_KIND:
		case FORM_XFSP_CONNECTOR_KIND:
		case FORM_XFSP_MACHINE_KIND:
		case FORM_XFSP_PORT_KIND:
		case FORM_XFSP_ROUTINE_KIND:
		case FORM_XFSP_SYSTEM_KIND:
		case FORM_XFSP_TRANSITION_KIND:
		case FORM_XFSP_DATATYPE_KIND:
		case FORM_XFSP_VARIABLE_KIND:
		{
			const BF & anInstance = searchSymbolInstance(
					aliasTable, anED, aCode.to< ObjectElement >() );
			if( anInstance.valid() )
			{
				if( anInstance.is< InstanceOfData >() )
				{
					InstanceOfData * aData = anInstance.to_ptr< InstanceOfData >();
					if( aData->getModifier().hasFeatureFinal() && aData->hasValue() )
					{
						return( aData->getValue() );
					}
				}

				return( anInstance );
			}
			else
			{
				ExecutableQuery XQuery( mConfiguration );

				const BF & aProgram = XQuery.getExecutableOrProgram(
						aCode.to< ObjectElement >() );
				if( aProgram.valid() )
				{
					return( aProgram );
				}
				else
				{
					AVM_OS_EXIT( FAILED )
							<< "Unfound FORM symbol : " << aCode.str()
							<< SEND_EXIT;

					return( aCode );
				}
			}

			break;
		}

		case FORM_OPERATOR_KIND:
		{
			return( aCode );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			const BF & anInstance = searchSymbolInstance(aliasTable, anED, aCode);
			if( anInstance.valid() )
			{
				if( anInstance.is< InstanceOfData >() )
				{
					InstanceOfData * aData = anInstance.to_ptr< InstanceOfData >();
					if( aData->getModifier().hasFeatureFinal() && aData->hasValue() )
					{
						return( aData->getValue() );
					}
				}

				return( anInstance );
			}

			return( aCode );
		}

		case FORM_INSTANCE_BUFFER_KIND:
		case FORM_INSTANCE_CONNECTOR_KIND:
		case FORM_INSTANCE_MACHINE_KIND:
		case FORM_INSTANCE_PORT_KIND:
		{
			BF anInstance = searchSymbolInstance(aliasTable, anED, aCode);
			if( anInstance.valid() )
			{
				// AVM_OS_TRACE << " --> bOK" << std::endl;

				return( anInstance );
			}

			return( aCode );
		}

		case FORM_RUNTIME_ID_KIND:
		{
			return( aCode );
		}


		case FORM_BUILTIN_BOOLEAN_KIND:
		case FORM_BUILTIN_CHARACTER_KIND:
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:
		case FORM_BUILTIN_STRING_KIND:
		case FORM_BUILTIN_IDENTIFIER_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			return( aCode );
		}

		default:
		{
			AVM_OS_EXIT( FAILED )
					<< "Unexpected FORM KIND for compileAvmCode\n"
					<< aCode.toString()
					<< SEND_EXIT;

			return( aCode );
		}
	}

	return( BF::REF_NULL );

}


}

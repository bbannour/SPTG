/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 mai 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeUfiCastExpressionCompiler.h"

#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionTypeChecker.h>

#include <fml/lib/AvmOperationFactory.h>

#include <fml/symbol/TableOfSymbol.h>

#include <fml/operator/OperatorManager.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/BaseSymbolTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>

#include <fml/workflow/UniFormIdentifier.h>

#include <sew/Configuration.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE UFI EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeUfiExpressionCompiler::compileUfiExpression(
		COMPILE_CONTEXT * aCTX, const UniFormIdentifier & theUFI)
{
	BF bfInstance;

	if( theUFI.isAbsoluteFullFields() )
	{
		bfInstance = getSymbolTable().searchSymbolByUFI(aCTX, theUFI);
		if( bfInstance.valid() )
		{
			return( bfInstance );
		}

		else
		{
			std::string strUFI = theUFI.str();

			//StringTools::replace(strUFI, "spec::", "inst::");
			StringTools::eraseAll(strUFI, "&");

			bfInstance = getSymbolTable().searchSymbol(aCTX, strUFI);
			if( bfInstance.valid() )
			{
				return( bfInstance );
			}
		}
	}
	else if( theUFI.isFullOffset() )
	{
		bfInstance = getSymbolTable().searchSymbolByQualifiedNameID(
				aCTX, theUFI.str());
		if( bfInstance.valid() )
		{
			return( bfInstance );
		}
	}

	UniFormIdentifier::const_iterator it = theUFI.begin();
	UniFormIdentifier::const_iterator itEnd = theUFI.end();

	std::ostringstream ossUFI;

	const ObjectElement * theMainObjectElement = nullptr;

	// CHECKING FIRST ELEMENT
	if( (*it).is< ObjectElement >() )
	{
		theMainObjectElement = (*it).to_ptr< ObjectElement >();
	}
	else
	{
		if( theUFI.hasLocator() )
		{
			ossUFI << theUFI.toStringLocator()
					<< FQN_ID_ROOT_SEPARATOR << (*it).str();
		}
		ossUFI << (*it).str();

		if( AVMCODE_COMPILER.getConfiguration().
				getExecutableSystem().getSystemInstance().hasAstElement() )
		{
			theMainObjectElement = &( AVMCODE_COMPILER.getConfiguration().
					getExecutableSystem().getSystemInstance().getAstElement() );
		}
	}

	if( theMainObjectElement == nullptr )
	{
		bfInstance = getSymbolTable().searchDataInstance(aCTX, theUFI.str());
		if( bfInstance.valid() )
		{
			return( bfInstance );
		}
		else
		{
			bfInstance = getSymbolTable().searchSymbolByNameID(aCTX, (*it).str());
			if( bfInstance.valid() )
			{
				if( bfInstance.to< BaseInstanceForm >().hasAstElement() )
				{
					theMainObjectElement =  &( bfInstance.to<
							BaseInstanceForm >().getAstElement() );
				}
				else
				{
					theMainObjectElement = nullptr;
				}
			}
		}
	}


	if( theMainObjectElement != nullptr )
	{
		const ObjectElement * objElement = nullptr;

		ossUFI.str("");
		ossUFI << theMainObjectElement->getFullyQualifiedNameID();

		// CHECKING MAIN FORM
		for( ++it ; it != itEnd ; ++it )
		{
			if( (*it).is< ObjectElement >() )
			{
				objElement = (*it).to_ptr< ObjectElement >();

				if( objElement->getContainer() == theMainObjectElement )
				{
					theMainObjectElement = objElement;

					ossUFI.str("");
					ossUFI << theMainObjectElement->getFullyQualifiedNameID();
				}
				else
				{
					break;
				}
			}
			else if( (*it).isIdentifier() )
			{
				ossUFI << '.' << (*it).str();
			}
			else
			{
				break;
			}

			if( objElement != nullptr )
			{
				theMainObjectElement = objElement;

				//!![MIGRATION] i.e. isArrayType() isContainerType() isClassType()
				AVM_OS_FATAL_ERROR_EXIT
						<< "!!! DataTypeFactory::isCompositeType !!!"
						<< SEND_EXIT;
				break;
			}
			else
			{
				break;
			}
		}
	}
	else if( (*it).isFieldInvokable() )
	{
		const Operator * opExpr = AvmOperationFactory::get( (*it).str() );
		if( opExpr != nullptr )
		{
			BFCode anInvokeExpression( opExpr );

			BF arg;
			for( ++it ; it != itEnd ; ++it )
			{
				if( (*it).isFieldParameter() )
				{
					arg = compileArgRvalue(aCTX, *it);

					if( arg.valid() )
					{
						anInvokeExpression->append( arg );
					}
					else
					{
						getCompilerTable().incrErrorCount();
						aCTX->errorContext( AVM_OS_WARN )
								<< "AvmCode< statement > compilation error << "
								<< (*it).str() << " >>"
								<< std::endl << std::endl;

						anInvokeExpression->append( *it );
					}
				}
				else
				{
					break;
				}
			}

			if( it != itEnd )
			{
				getCompilerTable().incrErrorCount();
				aCTX->errorContext( AVM_OS_WARN )
						<< "AvmCode< statement > compilation error"
						" << (: " << anInvokeExpression.str()
						<< " " << (*it).str() <<  " ...) >> for "
						<< theUFI.str() << std::endl << std::endl;
			}

			return( anInvokeExpression );
		}
		else
		{
			getCompilerTable().incrErrorCount();
			AVM_OS_WARN << "Unfound the operation < " << (*it).str()
					<< " > in the UFI < " << theUFI.str() << " >"
					<< std::endl;

			return( BF::REF_NULL );
		}
	}

	else
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << "Unfound the invokable field < " << ossUFI.str()
				<< " > of UFI < " << theUFI.str() << " > in the system << "
				<< AVMCODE_COMPILER.getConfiguration().
						getExecutableSystem().rawSystemInstance()->
								safeAstElement().getFullyQualifiedNameID()
				<< " >>" << std::endl;

		return( BF::REF_NULL );
	}


	// CHECKING FIRST INSTANCE
	if( theMainObjectElement != nullptr )
	{
		bfInstance = getSymbolTable().searchInstance(
				aCTX, (* theMainObjectElement));
	}
	else
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << "Unfound the main object element < " << ossUFI.str()
				<< " > of UFI < " << theUFI.str() << " > in the system << "
				<< AVMCODE_COMPILER.getConfiguration().
						getExecutableSystem().rawSystemInstance()->
								safeAstElement().getFullyQualifiedNameID()
				<< " >>" << std::endl;

		return( BF::REF_NULL );
	}

	if( bfInstance.valid() )
	{
		if( it == itEnd )
		{
			return( bfInstance );
		}

		// CASE FIRST INSTANCE is a MACHINE
		if( bfInstance.is< InstanceOfMachine >() )
		{
			InstanceOfMachine * theInstanceMachine =
					bfInstance.to_ptr< InstanceOfMachine >();

			InstanceOfMachine * ptrInstance = nullptr;

			// CHECKING FOR MAIN MACHINE
			for( ; it != itEnd ; ++it )
			{
				if( (*it).isIdentifier() )
				{
					ossUFI.str("");
					ossUFI << theInstanceMachine->refExecutable().
							getAstFullyQualifiedNameID() << '.' << (*it).str();

					bfInstance = getSymbolTable().searchInstance(
							aCTX->newCTX(theInstanceMachine->getExecutable()),
							ossUFI.str() );

					if( bfInstance.valid() )
					{
						if( bfInstance.is< InstanceOfMachine >() )
						{
							ptrInstance = bfInstance.to_ptr< InstanceOfMachine >();

							if( ptrInstance->getContainer() ==
									theInstanceMachine->getExecutable() )
							{
								theInstanceMachine = ptrInstance;
							}
							else
							{
								getCompilerTable().incrErrorCount();
								AVM_OS_WARN << "Unexpected a non child machine "
										"instance < " << ptrInstance->getFullyQualifiedNameID()
										<< " of the machine instance < "
										<< theInstanceMachine->getFullyQualifiedNameID()
										<< " > > in the UFI < " << theUFI.str()
										<< " >" << std::endl;

								return( BF::REF_NULL );
							}
						}
						else if( bfInstance.is< InstanceOfData >() )
						{
							++it;

							break;
						}
					}
					else
					{
						getCompilerTable().incrErrorCount();
						AVM_OS_WARN << "Unfound machine attribute < "
								<< (*it).str() << " > of the UFI < "
								<< theUFI.str() << " >" << std::endl;

						return( BF::REF_NULL );
					}
				}
				else
				{
					getCompilerTable().incrErrorCount();
					AVM_OS_WARN << "Unexpected class attribute kind < "
							<< (*it).str() << " > of the UFI < "
							<< theUFI.str() << " >" << std::endl;

					return( BF::REF_NULL );
				}
			}

			if( it == itEnd )
			{
				bfInstance = getSymbolTable().createAliasIfNotAccessible(
						aCTX, theInstanceMachine, bfInstance);

				// ERROR REPORTING
				if( getSymbolTable().hasError() )
				{
					getCompilerTable().incrErrorCount();
					AVM_OS_WARN << theUFI.errorLocation(
							aCTX->mCompileCtx->safeAstElement() )
							<< getSymbolTable().getErrorMessage()
							<< std::endl << std::endl;
				}

				return( bfInstance );
			}
		}


		// CASE FIRST INSTANCE is a DATA
		if( bfInstance.is< InstanceOfData >() )
		{
			bfInstance = getSymbolTable().
					createAliasIfNotAccessible(aCTX, bfInstance);
			// ERROR REPORTING
			if( getSymbolTable().hasError() )
			{
				getCompilerTable().incrErrorCount();
				AVM_OS_WARN << theUFI.errorLocation(
						aCTX->mCompileCtx->safeAstElement() )
						<< getSymbolTable().getErrorMessage()
						<< std::endl << std::endl;
			}

			Symbol symbolData( bfInstance );

			const InstanceOfData & ptrInstance = bfInstance.to< InstanceOfData >();

			const BaseTypeSpecifier * aTypeSpecifier =
					ptrInstance.ptrTypeSpecifier();

			if( aTypeSpecifier->hasTypeStructureOrChoiceOrUnion() ||
					aTypeSpecifier->hasTypeArrayVector() )
			{
				const BaseSymbolTypeSpecifier * aStructTypeSpecifier = nullptr;

				bool isArrayIndex = false;
//				bool isNotArray = true;

				IPointerVariableNature::POINTER_VARIABLE_NATURE aPointerNature =
						IPointerVariableNature::POINTER_UNDEFINED_NATURE;

				TableOfSymbol aRelativeDataPath;
				std::ostringstream ossID;

				ossUFI.str( "" );
				ossUFI << ptrInstance.getFullyQualifiedNameID();

				ossID << ptrInstance.getNameID();


				for( ; it != itEnd ; ++it )
				{
					if( (*it).isFieldIndex() )
					{
						if( not aTypeSpecifier->hasTypeArrayVector() )
						{
							getCompilerTable().incrErrorCount();
							aCTX->errorContext( AVM_OS_WARN )
									<< "Unexpected a non Array field kind < "
									<< ossUFI.str() << " > of the UFI < "
									<< theUFI.str() << " >" << std::endl;

							return( BF::REF_NULL );
						}

						const BaseTypeSpecifier & contentTypeSpecifier =
								aTypeSpecifier->as_ptr< ContainerTypeSpecifier >()
								->getContentsTypeSpecifier();

						aTypeSpecifier = (& contentTypeSpecifier);

						BF index = compileArgRvalue(aCTX, (*it));
						if( index.valid() )
						{
//							isNotArray = false;
							if( index.isUInteger() )
							{
								symbolData = new InstanceOfData(
										IPointerVariableNature::
											POINTER_FIELD_ARRAY_OFFSET_NATURE,
										aCTX->mCompileCtx,
										contentTypeSpecifier.getAstElement(),
										contentTypeSpecifier, 0 );
								symbolData.setOffset( index.toInteger() );
							}
							else if( index.isInteger() )
							{
								isArrayIndex = true;
								aPointerNature = ( isArrayIndex )
									? IPointerVariableNature::POINTER_UFI_MIXED_NATURE
									: IPointerVariableNature::POINTER_UFI_OFFSET_NATURE;

								InstanceOfData * ptrSymbolIndex = nullptr;
								BF symbolIndex = aRelativeDataPath.empty()
										? bfInstance
										: BF( ptrSymbolIndex = new InstanceOfData(
												aPointerNature,
												ptrInstance.getContainer(),
												ptrInstance, aRelativeDataPath));

								if( ptrSymbolIndex != nullptr )
								{
									ptrSymbolIndex->updateFullyQualifiedNameID(
											ossUFI.str() , ossID.str() );
								}

								symbolData = new InstanceOfData(
										IPointerVariableNature::
											POINTER_FIELD_ARRAY_INDEX_NATURE,
										aCTX->mCompileCtx,
										contentTypeSpecifier.getAstElement(),
										contentTypeSpecifier, 0 );
								symbolData.setValue(
										ExpressionConstructor::addExpr(
											ExpressionConstructor::newCode(
												OperatorManager::OPERATOR_SIZE,
												symbolIndex ),
											index ) );
							}
							else
							{
								isArrayIndex = true;
								symbolData = new InstanceOfData(
										IPointerVariableNature::
											POINTER_FIELD_ARRAY_INDEX_NATURE,
										aCTX->mCompileCtx,
										contentTypeSpecifier.getAstElement(),
										contentTypeSpecifier, 0 );
								symbolData.setValue( index );
							}

							aRelativeDataPath.append( symbolData );

							ossUFI << "[" << index.str() << "]";
							ossID  << "[" << ( index.is< BaseInstanceForm >() ?
									index.to< BaseInstanceForm >().getNameID() :
									index.str() ) << "]";
						}
						else
						{
							getCompilerTable().incrErrorCount();
							AVM_OS_WARN << "Unfound array index < "
									<< (*it).str() << " > of the UFI element < "
									<< theUFI.str() << " >" << std::endl;

							return( BF::REF_NULL );
						}
					}

					else if( aTypeSpecifier->hasTypeStructureOrChoiceOrUnion() )
					{
//						AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTypeSpecifier->isTypedClass() )
//								<< "Unexpected a non Class/Struct type !!!"
//								<< SEND_EXIT;

						aStructTypeSpecifier =
								aTypeSpecifier->to_ptr< BaseSymbolTypeSpecifier >();
						if( (*it).isIdentifier() )
						{
							ossUFI << '.' << (*it).str();
							ossID << '.' << (*it).str();

							symbolData = symbolData.getAttributeByNameID( ossID.str() );
							if( symbolData.invalid() )
							{
								symbolData = aStructTypeSpecifier->
										getDataByNameID( (*it).str() );
							}

							//!! NO ELSE here
							if( symbolData.valid() )
							{
								if( aTypeSpecifier->isTypedUnion() )
								{
									// Not insertion in Data path
								}
								else
								{
									aRelativeDataPath.append( symbolData );
								}

								aTypeSpecifier = &( symbolData.getTypeSpecifier() );
							}
							else
							{
								getCompilerTable().incrErrorCount();
								AVM_OS_WARN << "Unfound structure attribute < "
										<< (*it).str() << " > of the UFI < "
										<< theUFI.str() << " >" << std::endl;

								return( BF::REF_NULL );
							}
						}
						else
						{
							getCompilerTable().incrErrorCount();
							AVM_OS_WARN << "Unexpected structure attribute kind < "
									<< (*it).str() << " > of the UFI < "
									<< theUFI.str() << " >" << std::endl;

							return( BF::REF_NULL );
						}
					}
					else
					{
						break;
					}

//					else
//					{
//						getCompilerTable().incrErrorCount();
//						AVM_OS_WARN << "Unexpected type < "
//								<< aTypeSpecifier->getFullyQualifiedNameID()
//								<< " > for the element < " << (*it).str()
//								<< " > of the instance of data < " << theUFI.str()
//								<< " >" << std::endl;
//						return( BF::REF_NULL );
//					}
				}

				aPointerNature = ( isArrayIndex )
					? IPointerVariableNature::POINTER_UFI_MIXED_NATURE
					: IPointerVariableNature::POINTER_UFI_OFFSET_NATURE;

				if( aRelativeDataPath.nonempty() )
				{
					aRelativeDataPath.pop_last_to( symbolData );

					symbolData = new InstanceOfData(aPointerNature,
							ptrInstance.getContainer(), ptrInstance,
							aRelativeDataPath, symbolData);
				}
				else
				{
					VectorOfInstanceOfMachine aRelativeMachinePath;

					symbolData = new InstanceOfData(ptrInstance.getContainer(),
							symbolData.variable(), aRelativeMachinePath);
				}

				symbolData.updateFullyQualifiedNameID( ossUFI.str() , ossID.str() );

//				if( isNotArray )
				{
					aCTX->mCompileCtx->refExecutable().
							appendVariableAlias( symbolData );
//					ptrInstance.getContainer()->appendVariableAlias( symbolData );
				}

				if( it == itEnd )
				{
					return( symbolData );
				}

				else if( (*it).isFieldInvokable() )
				{
					AVM_OS_ASSERT_FATAL_ERROR_EXIT( (*it).isIdentifier() )
							<< "Unexpected a non-Identifier << "
							<< (*it).str() << " >> as Invocable !!!"
							<< SEND_EXIT;

					const Operator * op = AvmOperationFactory::get(
							symbolData, (*it).toIdentifier());
					if( op != nullptr )
					{
						BFCode newCode(op, symbolData);
						BF arg;
						for( ++it ; it != itEnd ; ++it )
						{
							if( (*it).isFieldParameter() )
							{
								arg = compileArgRvalue(aCTX, *it);

								if( arg.valid() )
								{
									newCode->append( arg );
								}
								else
								{
									getCompilerTable().incrErrorCount();
									aCTX->errorContext( AVM_OS_WARN )
											<< "AvmCode< statement > "
												"compilation error << "
											<< (*it).str() << " >>"
											<< std::endl << std::endl;

									newCode->append( *it );
								}
							}
							else
							{
								break;
							}
						}
						if( it == itEnd )
						{
							return( newCode );
						}

						else
						{
							getCompilerTable().incrErrorCount();
							aCTX->errorContext( AVM_OS_WARN )
									<< "AvmCode< statement > "
											"compilation error << (: "
									<< symbolData.str() << " "
									<< (*it).str() << " ...) >> for "
									<< theUFI.str()
									<< std::endl << std::endl;

							return( symbolData );
						}
					}
					else
					{
						getCompilerTable().incrErrorCount();
						aCTX->errorContext( AVM_OS_WARN )
								<< "AvmCode< statement > "
									"compilation error << (: "
								<< symbolData.str() << " "
								<< (*it).str() << " ...) >> for "
								<< theUFI.str()
								<< std::endl << std::endl;

						return( symbolData );
					}
				}
				else
				{
					getCompilerTable().incrErrorCount();
					aCTX->errorContext( AVM_OS_WARN )
							<< "UFI compilation error << "
							<< symbolData.str() << " >> for "
							<< theUFI.str()
							<< std::endl << std::endl;

					return( symbolData );
				}
			}

			else if( aTypeSpecifier->isTypedLambda() /*&& (*(it-1)).isFieldInvokable()*/ )
			{
				BFCode invokeCode(OperatorManager::OPERATOR_INVOKE_LAMBDA_APPLY,
						symbolData);
//					(theInstanceData->getModifier().hasFeatureFinal() && theInstanceData->hasValue()) ?
//							theInstanceData->getValue() : theInstanceData);

				BF param;
				for( ; it != itEnd ; ++it )
				{
					param = compileArgRvalue(aCTX, (*it));

					if( param.invalid() )
					{
						getCompilerTable().incrErrorCount();
						AVM_OS_WARN << "Compilation Error of the parameter < "
								<< (*it).str() << " > of the invokable < "
								<< ptrInstance.getFullyQualifiedNameID() << " > in the UFI < "
								<< theUFI.str() << " >" << std::endl;

						continue;
					}

					invokeCode->append( param );
				}

				return( invokeCode );
			}

			else if( aTypeSpecifier->isTypedMachine() )
			{

			}

			else
			{
				getCompilerTable().incrErrorCount();
				AVM_OS_WARN << "Unexpected type < " << aTypeSpecifier->str()
						<< " > for instance of data < "
						<< ptrInstance.getFullyQualifiedNameID()
						<< " > int the UFI < " << theUFI.str() << " >"
						<< std::endl;

				return( BF::REF_NULL );
			}
		}

		// CASE FIRST INSTANCE is a PORT
		else if( bfInstance.is< InstanceOfPort >() )
		{
			getCompilerTable().incrErrorCount();
			AVM_OS_WARN << "Unexpected a port instance < "
					<< bfInstance.to< InstanceOfPort >().getFullyQualifiedNameID()
					<< " > int the UFI < " << theUFI.str() << " >" << std::endl;

			return( BF::REF_NULL );
		}

		else
		{
			getCompilerTable().incrErrorCount();
			AVM_OS_WARN << "Unexpected a base instance < "
					<< bfInstance.to< BaseInstanceForm >().getFullyQualifiedNameID()
					<< " > int the UFI < " << theUFI.str() << " >" << std::endl;

			return( BF::REF_NULL );
		}
	}

	else
	{
		const BF & tmpTransition =
				getSymbolTable().searchTransition(aCTX, (* theMainObjectElement));
		if( tmpTransition.valid() && (it == itEnd) )
		{
			return( tmpTransition );
		}

		const BF & tmpProgram =
				getSymbolTable().searchProgram(aCTX, (* theMainObjectElement));
		if( tmpProgram.valid() && (it == itEnd) )
		{
			return( tmpProgram );
		}


		const BF & aType = SymbolTable::searchTypeSpecifier(
				AVMCODE_COMPILER.getConfiguration().getExecutableSystem(),
				aCTX, (* theMainObjectElement));
		if( aType.valid() )
		{
			if( it == itEnd )
			{
				return( aType );
			}
			else
			{
				EnumTypeSpecifier * anEnumTS;

				for( ; it != itEnd ; ++it )
				{
					if( aType.is< EnumTypeSpecifier >() )
					{
						anEnumTS = aType.to_ptr< EnumTypeSpecifier >();

						if( (*it).isIdentifier() )
						{
							ossUFI.str("");
							ossUFI << anEnumTS->getFullyQualifiedNameID() << '.' << (*it).str();

							bfInstance = anEnumTS->getSymbolData(ossUFI.str());

							break;
						}
					}
				}

				if( bfInstance.valid() && (it == itEnd) )
				{
					return( bfInstance );
				}
			}
		}

		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << "Unfound a runtime symbol for the form < "
				<< theMainObjectElement->getFullyQualifiedNameID()
				<< " > in the UFI < " << theUFI.str() << " >"
				<< std::endl;

		return( BF::REF_NULL );
	}

	return( BF::REF_NULL );
}





BF AvmcodeUfiExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	UniFormIdentifier * runtimeUFI = new UniFormIdentifier(false);
	BF bfRuntimeUFI( runtimeUFI );

	BF arg;

	COMPILE_CONTEXT * containerCTX = aCTX->clone();

	AvmCode::const_iterator itOperand = aCode->begin();
	AvmCode::const_iterator endOperand = aCode->end();

	for( ; itOperand != endOperand ; ++itOperand )
	{
		arg = compileArgRvalue(containerCTX, *itOperand);

		if( arg.invalid() )
		{
			getCompilerTable().incrErrorCount();
			AVM_OS_WARN << "Compilation Error of  < " << (*itOperand).str()
					<< " > in the UFI < " << aCode->str() << " >" << std::endl;

			continue;
		}

		runtimeUFI->appendUndef(arg);

		containerCTX->mCompileCtx = aCTX->mCompileCtx;

		if( ExpressionTypeChecker::isCtor(arg) && (itOperand != endOperand) )
		{
			const BF & aCastType = arg.to< AvmCode >().first();
			if( aCastType.is< BaseAvmProgram >() )
			{
				containerCTX->mCompileCtx = aCastType.to_ptr< BaseAvmProgram >();
			}
		}
	}

	return( bfRuntimeUFI );

}

BFCode AvmcodeUfiExpressionCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Unexpected UFI EXPRESSION as statement !!!"
			<< SEND_EXIT;

	return( aCode );
}



}

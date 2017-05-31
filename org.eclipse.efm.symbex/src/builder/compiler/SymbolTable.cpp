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

#include <builder/compiler/SymbolTable.h>

#include <builder/primitive/CompilationEnvironment.h>

#include <fml/common/ObjectElement.h>
#include <fml/common/PropertyElement.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/AvmTransition.h>
#include <fml/executable/BaseAvmProgram.h>
#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/RoutingData.h>

#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/expression/AvmCode.h>

#include <fml/infrastructure/Channel.h>
#include <fml/infrastructure/Connector.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>

#include <fml/symbol/Symbol.h>

#include <fml/workflow/UniFormIdentifier.h>

#include <sew/Configuration.h>


namespace sep
{


/**
 *******************************************************************************
 * SEARCH
 *******************************************************************************
 */

	/**
 * SEARCH
 * for Type
 */
const TypeSpecifier & SymbolTable::searchTypeSpecifier(
		ExecutableSystem & anExecutableSystem,
		COMPILE_CONTEXT * aCTX, const ObjectElement * astElement)
{
	BaseAvmProgram * aProgram = aCTX->mCompileCtx;
	for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
	{
		if( aProgram->is< AvmProgram >() )
		{
			const TypeSpecifier & foundType =
					aProgram->to< AvmProgram >()->getTypeSpecifier(astElement);
			if( foundType.valid() )
			{
				return( foundType );
			}
		}
	}

	TableOfExecutableForm::const_raw_iterator itExec =
			anExecutableSystem.getExecutables().begin();
	TableOfExecutableForm::const_raw_iterator itEnd =
			anExecutableSystem.getExecutables().end();
	for(  ; itExec != itEnd ; ++itExec )
	{
		const TypeSpecifier & foundType =
				(itExec)->getTypeSpecifier(astElement);
		if( foundType.valid() )
		{
			return( foundType );
		}
	}

	return( TypeSpecifier::REF_NULL );
}


const TypeSpecifier & SymbolTable::searchTypeSpecifier(
		ExecutableSystem & anExecutableSystem, COMPILE_CONTEXT * aCTX,
		const std::string & aFullyQualifiedNameID)
{
	BaseAvmProgram * aProgram = aCTX->mCompileCtx;
	for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
	{
		if( aProgram->is< AvmProgram >() )
		{
			const TypeSpecifier & foundType = aProgram->to< AvmProgram >()->
					getTypeSpecifier( aFullyQualifiedNameID );
			if( foundType.valid() )
			{
				return( foundType );
			}
		}
	}

	TableOfExecutableForm::const_raw_iterator itExec =
			anExecutableSystem.getExecutables().begin();
	TableOfExecutableForm::const_raw_iterator itEnd =
			anExecutableSystem.getExecutables().end();
	for(  ; itExec != itEnd ; ++itExec )
	{
		const TypeSpecifier & foundType =
				(itExec)->getTypeSpecifier( aFullyQualifiedNameID );
		if( foundType.valid() )
		{
			return( foundType );
		}
	}

	return( TypeSpecifier::REF_NULL );
}


/*
 * SEARCH
 * for Data Instance
 */
const BF & SymbolTable::searchDataInstance(
		BaseAvmProgram * tmpProgram, const ObjectElement * astElement) const
{
	for( ; tmpProgram != NULL ; tmpProgram = tmpProgram->getContainer() )
	{
		{
			const BF & foundInstance =
					tmpProgram->getAllData().getByAstElement(astElement);
			if( foundInstance.valid() )
			{
				return( foundInstance );
			}
		}

		{
			const BF & foundInstance =
					tmpProgram->getDataAlias().getByAstElement(astElement);
			if( foundInstance.valid() )
			{
				return( foundInstance );
			}
		}

		if( tmpProgram->is< AvmProgram >() )
		{
			{
				const BF & foundInstance = tmpProgram->to< AvmProgram >()->
						getConstData().getByAstElement(astElement);
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}

			{
				const BF & foundInstance = tmpProgram->to< AvmProgram >()->
						getSymbolDataByAstElement(astElement);
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}
		}
	}

	return( BF::REF_NULL );
}

const BF & SymbolTable::searchDataInstance(
		COMPILE_CONTEXT * aCTX, const ObjectElement * objElement)
{
	// RESET ERROR
	resetError();

	const BF & foundInstance =
			searchDataInstance(aCTX->mCompileCtx, objElement);
	if( foundInstance.valid() )
	{
		return( foundInstance );
	}
	else if( aCTX->isSpecificRuntimeCtx() )
	{
		const BF & foundInstance =
				searchDataInstance(aCTX->mRuntimeCtx, objElement);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( searchDataInstanceAlias(aCTX, objElement) );
}



const BF & SymbolTable::searchDataInstance(BaseAvmProgram * tmpProgram,
		const std::string & aFullyQualifiedNameID) const
{
	for( ; tmpProgram != NULL ; tmpProgram = tmpProgram->getContainer() )
	{
		const BF & foundInstance = tmpProgram->getAllData().
				getByFQNameID( aFullyQualifiedNameID );
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}

		if( tmpProgram->is< AvmProgram >() )
		{
			{
				const BF & foundInstance = tmpProgram->to< AvmProgram >()->
						getConstData().getByFQNameID( aFullyQualifiedNameID );
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}

			{
				const BF & foundInstance = tmpProgram->to< AvmProgram >()->
						getSymbolData( aFullyQualifiedNameID );
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}

			if( tmpProgram->is< ExecutableForm >() )
			{
				const BF & foundInstance = tmpProgram->to< ExecutableForm >()->
						getDataAlias().getByFQNameID( aFullyQualifiedNameID );
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}
		}
	}

	return( BF::REF_NULL );
}

const BF & SymbolTable::searchDataInstance(COMPILE_CONTEXT * aCTX,
		const std::string & aFullyQualifiedNameID)
{
	// RESET ERROR
	resetError();

	const BF & foundInstance =
			searchDataInstance(aCTX->mCompileCtx, aFullyQualifiedNameID);
	if( foundInstance.valid() )
	{
		return( foundInstance );
	}
	else if( aCTX->isSpecificRuntimeCtx() )
	{
		const BF & foundInstance =
				searchDataInstance(aCTX->mRuntimeCtx, aFullyQualifiedNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( searchDataInstanceAlias(aCTX, aFullyQualifiedNameID) );
}



const BF & SymbolTable::searchDataInstanceByQualifiedNameID(
		BaseAvmProgram * tmpProgram, const std::string & aQualifiedNameID) const
{
	for( ; tmpProgram != NULL ; tmpProgram = tmpProgram->getContainer() )
	{
		const BF & foundInstance = tmpProgram->
				getAllData().getByQualifiedNameID(aQualifiedNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}

		if( tmpProgram->is< AvmProgram >() )
		{
			{
				const BF & foundInstance = tmpProgram->to< AvmProgram >()->
						getConstData().getByQualifiedNameID(aQualifiedNameID);
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}

			{
				const BF & foundInstance = tmpProgram->to< AvmProgram >()->
						getSymbolDataByQualifiedNameID(aQualifiedNameID);
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}

			if( tmpProgram->is< ExecutableForm >() )
			{
				const BF & foundInstance = tmpProgram->to< ExecutableForm >()->
						getDataAlias().getByQualifiedNameID(aQualifiedNameID);
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}
		}
	}

	return( BF::REF_NULL );
}

const BF & SymbolTable::searchDataInstanceByQualifiedNameID(
		COMPILE_CONTEXT * aCTX, const std::string & aQualifiedNameID)
{
	// RESET ERROR
	resetError();

	const BF & foundInstance = searchDataInstanceByQualifiedNameID(
			aCTX->mCompileCtx, aQualifiedNameID);
	if( foundInstance.valid() )
	{
		return( foundInstance );
	}
	else if( aCTX->isSpecificRuntimeCtx() )
	{
		const BF & foundInstance = searchDataInstanceByQualifiedNameID(
				aCTX->mRuntimeCtx, aQualifiedNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( BF::REF_NULL );
}



const BF & SymbolTable::searchDataInstanceByNameID(
		BaseAvmProgram * tmpProgram, const std::string & aNameID) const
{
	for( ; tmpProgram != NULL ; tmpProgram = tmpProgram->getContainer() )
	{
		const BF & foundInstance =
				tmpProgram->getAllData().getByNameID(aNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}

		if( tmpProgram->is< AvmProgram >() )
		{
			{
				const BF & foundInstance = tmpProgram->to<
						AvmProgram >()->getConstData().getByNameID(aNameID);
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}

			{
				const BF & foundInstance = tmpProgram->to<
						AvmProgram >()->getSymbolDataByNameID(aNameID);
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}

			if( tmpProgram->is< ExecutableForm >() )
			{
				const BF & foundInstance = tmpProgram->to<
						ExecutableForm >()->getDataAlias().getByNameID(aNameID);
				if( foundInstance.valid() )
				{
					return( foundInstance );
				}
			}
		}
	}

	return( BF::REF_NULL );
}


const BF & SymbolTable::searchDataInstanceAlias(
		COMPILE_CONTEXT * aCTX, const ObjectElement * astElement)
{
	ExecutableForm * tmpExecutable = NULL;
	BF foundInstance;
	InstanceOfData * foundData = NULL;

	TableOfExecutableForm::const_raw_iterator itExec =
			mConfiguration.getExecutableSystem().getExecutables().begin();
	TableOfExecutableForm::const_raw_iterator endExec =
			mConfiguration.getExecutableSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		foundInstance = (itExec)->getAllData().getByAstElement(astElement);
		if( foundInstance.valid() )
		{
			tmpExecutable = (itExec);
			break;
		}

		foundInstance = (itExec)->getConstData().getByAstElement(astElement);
		if( foundInstance.valid() )
		{
			tmpExecutable = (itExec);
			break;
		}

		foundInstance = (itExec)->getSymbolDataByAstElement(astElement);
		if( foundInstance.valid() )
		{
			tmpExecutable = (itExec);
			break;
		}
	}

	if( foundInstance.valid() )
	{
		foundData = foundInstance.to_ptr< InstanceOfData >();
		if( foundData->getModifier().isVisibilityPublic( aCTX->getModifier() ) )
		{
			return( createDataInstanceAlias(
					aCTX->mCompileCtx->getExecutable(),
					astElement->getFullyQualifiedNameID(),
					foundData, tmpExecutable) );
		}
		else
		{
			incrErrorCount();
			ERROR_OS << "Illegal acces of the NON-PUBLIC instance << &"
					<< astElement->getFullyQualifiedNameID() << " >> !!!";
		}
	}

	return( BF::REF_NULL );
}


const BF & SymbolTable::searchDataInstanceAlias(
		COMPILE_CONTEXT * aCTX, const std::string & aFullyQualifiedNameID)
{
	std::string fqnPrefix = aFullyQualifiedNameID.substr(0,
			aFullyQualifiedNameID.find_last_of('.'));

	std::string aliasFQN;

	VectorOfInstanceOfMachine theInstanceOfMachinePath;

	ExecutableForm * tmpExecutable = aCTX->mCompileCtx->getExecutable();

	Symbol aMachine;

	for( ; tmpExecutable != NULL ;
			tmpExecutable = tmpExecutable->getExecutableContainer() )
	{
		if( ((aMachine = tmpExecutable->getInstanceStatic().
				getByFQNameID(fqnPrefix)).valid() )
		|| ((aMachine = tmpExecutable->getInstanceStatic().
				getByQualifiedNameID(fqnPrefix)).valid()) )
		{
			theInstanceOfMachinePath.append( aMachine.rawMachine() );

			tmpExecutable = aMachine.getExecutable();

			aliasFQN = aMachine.getFullyQualifiedNameID();

			break;
		}
	}

	if( aMachine.invalid() )
	{
		fqnPrefix = aFullyQualifiedNameID.substr(0,
				aFullyQualifiedNameID.find('.'));
		tmpExecutable = NULL;

		TableOfExecutableForm::const_raw_iterator itExec =
				mConfiguration.getExecutableSystem().getExecutables().begin();
		TableOfExecutableForm::const_raw_iterator endExec =
				mConfiguration.getExecutableSystem().getExecutables().end();
		for( ; itExec != endExec ; ++itExec )
		{
			if( (itExec)->getAstFullyQualifiedNameID() == fqnPrefix )
			{
				tmpExecutable = (itExec);
				break;
			}
			else if( NamedElement::compareLocation(
					(itExec)->getAstFullyQualifiedNameID(), fqnPrefix) )
			{
				tmpExecutable = (itExec);
				break;
			}
			else if( (itExec)->getNameID() == fqnPrefix )
			{
				tmpExecutable = (itExec);
				break;
			}
		}
	}

	if( tmpExecutable != NULL )
	{
		ListOfString strList;

		NamedElement::collectNameID(strList,
				aFullyQualifiedNameID, fqnPrefix.size() + 1);

		if( strList.singleton() )
		{
			aliasFQN = aliasFQN + '.' + strList.first();
			fqnPrefix = tmpExecutable->getAstFullyQualifiedNameID() +
					'.' + strList.pop_first();

			if( tmpExecutable->getAllData().getByFQNameID(fqnPrefix).invalid() )
			{
				tmpExecutable = NULL;
			}
		}

		while( strList.populated() && (tmpExecutable != NULL) )
		{
			fqnPrefix = tmpExecutable->getAstFullyQualifiedNameID()
					+ '.' + strList.pop_first();

			aMachine = tmpExecutable->
					getInstanceStatic().getByFQNameID( fqnPrefix );
			if( aMachine != NULL )
			{
				aliasFQN = aMachine.getFullyQualifiedNameID();

				theInstanceOfMachinePath.append( aMachine.rawMachine() );

				tmpExecutable = aMachine.getExecutable();
			}
			else
			{
				if( tmpExecutable->getAllData().
						getByFQNameID(fqnPrefix).invalid() )
				{
					break;
				}
			}
		}

		if( tmpExecutable != NULL )
		{
			while( strList.nonempty() )
			{
				aliasFQN = aliasFQN + '.' + strList.first();
				fqnPrefix = fqnPrefix + '.' + strList.pop_first();
			}

			const BF & foundInstance =
					tmpExecutable->getAllData().getByFQNameID(fqnPrefix);

			if( foundInstance.valid() )
			{
				InstanceOfData * foundData =
						foundInstance.to_ptr< InstanceOfData >();
				if( foundData->getModifier().
						isVisibilityPublic( aCTX->getModifier() ) )
				{
					return( createDataInstanceAlias(
							aCTX->mCompileCtx->getExecutable(),
							aliasFQN, foundData, theInstanceOfMachinePath) );
				}
				else
				{
					incrErrorCount();
					ERROR_OS << "Illegal acces of the NON-PUBLIC instance << "
							<< aFullyQualifiedNameID << " >> !!!";
				}
			}
		}
	}

	return( BF::REF_NULL );
}


const BF & SymbolTable::createDataInstanceAlias(ExecutableForm * anExecutable,
		const std::string & aFullyQualifiedNameID,
		InstanceOfData * anInstance, ExecutableForm * instContainer)
{
	const ExecutableForm * lcaExecutable = anExecutable->LCA( instContainer );

	if( lcaExecutable != NULL )
	{
		std::string fqnPrefix = lcaExecutable->getAstFullyQualifiedNameID();

		ListOfString strList;
		NamedElement::collectNameID(strList, aFullyQualifiedNameID, fqnPrefix);

		VectorOfInstanceOfMachine theInstanceOfMachinePath;

		while( strList.populated() )
		{
			fqnPrefix = fqnPrefix + '.' + strList.pop_first();

			const Symbol & execInstance =
				lcaExecutable->getInstanceStatic().getByFQNameID( fqnPrefix );
			if( execInstance.valid() )
			{
				theInstanceOfMachinePath.append(execInstance.rawMachine());
				lcaExecutable = execInstance.getExecutable();
			}
			else
			{
				if( lcaExecutable->getAllData().
						getByFQNameID( fqnPrefix ).invalid() )
				{
					lcaExecutable = NULL;
				}
				break;
			}
		}

		if( lcaExecutable != NULL )
		{
			while( strList.nonempty() )
			{
				fqnPrefix = fqnPrefix + '.' + strList.pop_first();
			}

			BF foundInstance =
					lcaExecutable->getAllData().getByFQNameID( fqnPrefix );
			if( foundInstance.invalid() )
			{
				foundInstance =
						lcaExecutable->getConstData().getByFQNameID( fqnPrefix );

				if( foundInstance.invalid() )
				{
					foundInstance = lcaExecutable->getSymbolData(fqnPrefix);
				}
			}

			if( foundInstance == anInstance )
			{
				InstanceOfData * aliasInstance( new InstanceOfData(
						anExecutable, anInstance, theInstanceOfMachinePath) );
				aliasInstance->setFullyQualifiedNameID("alias" +
						aFullyQualifiedNameID.substr(
								aFullyQualifiedNameID.find(':')) );

				return( anExecutable->saveDataAlias(aliasInstance) );
			}
			else
			{
				incrErrorCount();
				ERROR_OS << "Failed to create ALIAS for instance << "
						<< aFullyQualifiedNameID << " >> !!!";
			}
		}
	}
	else
	{
		incrErrorCount();
		ERROR_OS << "Unfound LCA executable between "
				<< anExecutable->getFullyQualifiedNameID() << " & ";
		ERROR_OS << instContainer->getFullyQualifiedNameID()
				<< " for ALIAS creation for instance << "
				<< aFullyQualifiedNameID << " >> !!!";
	}


	return( BF::REF_NULL );
}


const BF & SymbolTable::createDataInstanceAlias(ExecutableForm * anExecutable,
		const std::string & aFullyQualifiedNameID, InstanceOfData * anInstance,
		VectorOfInstanceOfMachine & theInstanceOfMachinePath)
{
	const ExecutableForm * lcaExecutable = anExecutable->LCRA(
			theInstanceOfMachinePath.last()->getContainer()->getExecutable() );

	if( lcaExecutable != NULL )
	{
		if( lcaExecutable->hasContainer()
			&& theInstanceOfMachinePath.populated()
			&& (theInstanceOfMachinePath.first()
				!= mConfiguration.getExecutableSystem().rawSystemInstance()) )
		{
			while( theInstanceOfMachinePath.first()->getExecutable()
					!= lcaExecutable )
			{
				theInstanceOfMachinePath.remove_first();
			}
			if( lcaExecutable == anExecutable )
			{
				theInstanceOfMachinePath.remove_first();
			}
		}
		else
		{
			//!! NOTHING
		}

		InstanceOfData * aliasInstance( new InstanceOfData(anExecutable,
				anInstance, theInstanceOfMachinePath) );

		aliasInstance->setFullyQualifiedNameID( "alias" +
				aFullyQualifiedNameID.substr(aFullyQualifiedNameID.find(':')) );

		return( anExecutable->saveDataAlias(aliasInstance) );
	}

	return( BF::REF_NULL );
}


/*
 ******************************************************************************
 * SEARCH PORT CONNECT INSTANCE
 ******************************************************************************
 */

InstanceOfPort * SymbolTable::searchPortConnectorInstance(
		ExecutableForm * anExecutable,
		const std::string & aFullyQualifiedNameID) const
{
	// SEACH FOR INTERNAL PORT CONNEXION
	{
		const Symbol & foundInstance =
				anExecutable->getPort().getByFQNameID( aFullyQualifiedNameID );
		if( foundInstance.valid() )
		{
			return( foundInstance.rawPort() );
		}
	}

	// SEACH FOR MACHINE PORT CONNEXION
	TableOfSymbol::const_iterator itMachine =
			anExecutable->getInstanceStatic().begin();
	TableOfSymbol::const_iterator endMachine =
			anExecutable->getInstanceStatic().end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const Symbol & foundInstance = (*itMachine).getExecutable()->getPort().
				getByFQNameID( aFullyQualifiedNameID );
		if( foundInstance.valid() )
		{
			return( foundInstance.rawPort() );
		}
	}

	return( NULL );
}

InstanceOfPort * SymbolTable::searchPortConnectorInstance(
		ExecutableForm * anExecutable, const ObjectElement * aPort) const
{
	// SEACH FOR INTERNAL PORT CONNEXION
	{
		const Symbol & foundInstance =
				anExecutable->getPort().getByAstElement(aPort);
		if( foundInstance.valid() )
		{
			return( foundInstance.rawPort() );
		}
	}

	// SEACH FOR MACHINE PORT CONNEXION
	TableOfSymbol::const_iterator itMachine =
			anExecutable->getInstanceStatic().begin();
	TableOfSymbol::const_iterator endMachine =
			anExecutable->getInstanceStatic().end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const Symbol & foundInstance = (*itMachine).getExecutable()->
				getPort().getByAstElement(aPort);
		if( foundInstance.valid() )
		{
			return( foundInstance.rawPort() );
		}
	}

	const Symbol & foundInstance = XQuery.getSemPortByAstElement(
			anExecutable->getExecutableContainer(), aPort);
	if( foundInstance.valid() )
	{
		return( foundInstance.rawPort() );
	}

	return( NULL );
}


/*
 ******************************************************************************
 * SEARCH PORT SYMBOL INSTANCE
 ******************************************************************************
 */
const Symbol & SymbolTable::searchPortSymbolInstance(
		ExecutableForm * anExec, Port * aPort) const
{
	const Symbol & foundInstance = XQuery.getSemPortByAstElement(anExec, aPort);
	if( foundInstance.valid() )
	{
		return foundInstance;
	}

	if( aPort->hasRoutingChannel() )
	{
		const Symbol & foundChannel =
				XQuery.getChannel( aPort->getRoutingChannel() );
		if( foundChannel.valid() )
		{
			return foundChannel.channel().getContents().getByAstElement(aPort);
		}
	}

	return( Symbol::REF_NULL );
}


/*
 *******************************************************************************
 * SEARCH BUFFER SYMBOL INSTANCE
 *******************************************************************************
 */

const Symbol & SymbolTable::searchBufferInstance(
		ExecutableForm * anExecutable, const ObjectElement * objElement) const
{
	// SEARCH ON CURRENT BUFFER LIST
	{
		const Symbol & anInstance =
				anExecutable->getBuffer().getByAstElement(objElement);
		if( anInstance.valid() )
		{
			return( anInstance );
		}
	}

	// SEARCH ON CURRENT ALIAS BUFFER LIST
	{
		const Symbol & anInstance =
				anExecutable->getAlias().getByAstElement(objElement);
		if( anInstance.is< InstanceOfBuffer >() )
		{
			return( anInstance );
		}
	}


	// SEARCH ON CURRENT MODEL CHILD BUFFER LIST & MAKE AN ALIAS
	InstanceOfBuffer * aBufferInstance = NULL;

	TableOfSymbol::const_iterator itMachine = anExecutable->instance_model_begin();
	TableOfSymbol::const_iterator endMachine = anExecutable->instance_model_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		aBufferInstance = (*itMachine).getExecutable()->
				getBuffer().getByAstElement(objElement).rawBuffer();
		if( aBufferInstance != NULL )
		{
			break;
		}
	}

	if( aBufferInstance != NULL )
	{
		VectorOfInstanceOfMachine theInstanceOfMachinePath;
		theInstanceOfMachinePath.append( (*itMachine).rawMachine() );

		InstanceOfBuffer * aliasInstance = new InstanceOfBuffer(
				anExecutable, aBufferInstance, theInstanceOfMachinePath);

		std::string aFullyQualifiedNameID =
				aBufferInstance->getFullyQualifiedNameID();

		aliasInstance->setFullyQualifiedNameID( "alias" +
				aFullyQualifiedNameID.substr(aFullyQualifiedNameID.find(':')) );

		return( anExecutable->saveAlias(aliasInstance) );
	}

	return( searchBufferInstance(objElement) );
}



const Symbol & SymbolTable::searchBufferInstance(ExecutableForm * anExecutable,
		const std::string & aFullyQualifiedNameID)
{
	// SEARCH ON CURRENT BUFFER LIST
	{
		const Symbol & anInstance =
			anExecutable->getBuffer().getByFQNameID( aFullyQualifiedNameID );
		if( anInstance.valid() )
		{
			return( anInstance );
		}
	}

	// SEARCH ON CURRENT ALIAS BUFFER LIST
	{
		const Symbol & anInstance =
				anExecutable->getAlias().getByFQNameID( aFullyQualifiedNameID );
		if( anInstance.is< InstanceOfBuffer >() )
		{
			return( anInstance );
		}
	}

	// SEARCH ON CURRENT MODEL CHILD BUFFER LIST & MAKE AN ALIAS
	InstanceOfBuffer * aBufferInstance = NULL;

	TableOfSymbol::const_iterator itMachine = anExecutable->instance_model_begin();
	TableOfSymbol::const_iterator endMachine = anExecutable->instance_model_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		aBufferInstance = (*itMachine).getExecutable()->
				getBuffer().getByFQNameID( aFullyQualifiedNameID ).rawBuffer();
		if( aBufferInstance != NULL )
		{
			break;
		}
	}

	if( aBufferInstance != NULL )
	{
		VectorOfInstanceOfMachine theInstanceOfMachinePath;
		theInstanceOfMachinePath.append( (*itMachine).rawMachine() );

		InstanceOfBuffer * aliasInstance = new InstanceOfBuffer(
				anExecutable, aBufferInstance, theInstanceOfMachinePath );

		std::string fqnID = aBufferInstance->getFullyQualifiedNameID();
		aliasInstance->setFullyQualifiedNameID( "alias" +
				fqnID.substr(fqnID.find(':')) );

		return( anExecutable->saveAlias(aliasInstance) );
	}

	return( searchBufferInstanceAlias(anExecutable, aFullyQualifiedNameID) );
}


const Symbol & SymbolTable::searchBufferInstanceByQualifiedNameID(
		ExecutableForm * anExec, const std::string & aQualifiedNameID) const
{
	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const Symbol & anInstance =
				anExec->getBuffer().getByQualifiedNameID(aQualifiedNameID);
		if( anInstance.valid() )
		{
			return( anInstance );
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & SymbolTable::searchBufferInstanceByNameID(
		ExecutableForm * anExec, const std::string & aNameID) const
{
	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExec->getBuffer().getByNameID(aNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & SymbolTable::searchBufferInstanceAlias(
		ExecutableForm * anExecutable,
		const std::string & aFullyQualifiedNameID)
{
	std::string fqnPrefix = aFullyQualifiedNameID.substr(0,
			aFullyQualifiedNameID.find_last_of('.'));

	std::string aliasFQN;

	VectorOfInstanceOfMachine theInstanceOfMachinePath;

	ExecutableForm * tmpExecutable = anExecutable;

	Symbol aMachine;

	for( ; tmpExecutable != NULL ;
			tmpExecutable = tmpExecutable->getExecutableContainer() )
	{
		if( ((aMachine = tmpExecutable->getInstanceStatic().getByFQNameID(
				fqnPrefix)).valid())
		|| ((aMachine = tmpExecutable->getInstanceStatic().
				getByQualifiedNameID(fqnPrefix)).valid()) )
		{
			theInstanceOfMachinePath.append( aMachine.rawMachine() );

			tmpExecutable = aMachine.getExecutable();

			aliasFQN = aMachine.getFullyQualifiedNameID();

			break;
		}
	}

	if( aMachine.invalid() )
	{
		fqnPrefix = aFullyQualifiedNameID.substr(0,
				aFullyQualifiedNameID.find('.'));
		tmpExecutable = NULL;

		TableOfExecutableForm::const_raw_iterator itExec =
				mConfiguration.getExecutableSystem().getExecutables().begin();
		TableOfExecutableForm::const_raw_iterator endExec =
				mConfiguration.getExecutableSystem().getExecutables().end();
		for( ; itExec != endExec ; ++itExec )
		{
			if( (itExec)->getAstFullyQualifiedNameID() == fqnPrefix )
			{
				tmpExecutable = (itExec);
				break;
			}
			else if( NamedElement::compareLocation(
					(itExec)->getAstFullyQualifiedNameID(), fqnPrefix) )
			{
				tmpExecutable = (itExec);
				break;
			}
			else if( (itExec)->getNameID() == fqnPrefix )
			{
				tmpExecutable = (itExec);
				break;
			}
		}
	}

	if( tmpExecutable != NULL )
	{
		ListOfString strList;

		NamedElement::collectNameID(strList,
				aFullyQualifiedNameID, fqnPrefix.size() + 1);

		if( strList.singleton() )
		{
			aliasFQN = aliasFQN + '.' + strList.first();
			fqnPrefix = tmpExecutable->getAstFullyQualifiedNameID() +
					'.' + strList.pop_first();

			if( tmpExecutable->getBuffer().getByFQNameID(fqnPrefix).invalid() )
			{
				tmpExecutable = NULL;
			}
		}

		while( strList.populated() && (tmpExecutable != NULL) )
		{
			fqnPrefix = tmpExecutable->getAstFullyQualifiedNameID()
					+ '.' + strList.pop_first();

			aMachine = tmpExecutable->getInstanceStatic().
					getByFQNameID( fqnPrefix );
			if( aMachine.valid() )
			{
				aliasFQN = aMachine.getFullyQualifiedNameID();

				theInstanceOfMachinePath.append( aMachine.rawMachine() );

				tmpExecutable = aMachine.getExecutable();
			}
			else
			{
				if( tmpExecutable->getBuffer().
						getByFQNameID( fqnPrefix ).invalid() )
				{
					break;
				}
			}
		}

		if( tmpExecutable != NULL )
		{
			while( strList.nonempty() )
			{
				aliasFQN = aliasFQN + '.' + strList.first();
				fqnPrefix = fqnPrefix + '.' + strList.pop_first();
			}

			const Symbol & foundInstance =
					tmpExecutable->getBuffer().getByFQNameID( fqnPrefix );

			if( foundInstance.valid() )
			{
				if( foundInstance.getModifier().isVisibilityPublic() )
				{
					return( createBufferInstanceAlias(anExecutable, aliasFQN,
							foundInstance.rawBuffer(), theInstanceOfMachinePath) );
				}
				else
				{
					incrErrorCount();
					ERROR_OS << "Illegal acces of the NON-PUBLIC instance << "
							<< aFullyQualifiedNameID << " >> !!!";
				}
			}
		}
	}


	return( Symbol::REF_NULL );
}



const Symbol & SymbolTable::createBufferInstanceAlias(ExecutableForm * anExecutable,
		const std::string & aFullyQualifiedNameID, InstanceOfBuffer * anInstance,
		VectorOfInstanceOfMachine & theInstanceOfMachinePath)
{
	const ExecutableForm * lcaExecutable = anExecutable->LCRA(
			theInstanceOfMachinePath.last()->getContainer()->getExecutable() );

	if( lcaExecutable != NULL )
	{
		if( lcaExecutable->hasContainer()
			&& (theInstanceOfMachinePath.first()
				!= mConfiguration.getExecutableSystem().rawSystemInstance()) )
		{
			while( theInstanceOfMachinePath.first()->getExecutable()
					!= lcaExecutable )
			{
				theInstanceOfMachinePath.remove_first();
			}
			if( lcaExecutable == anExecutable )
			{
				theInstanceOfMachinePath.remove_first();
			}
		}
		else
		{
			//!! NOTHING
		}

		InstanceOfBuffer * aliasInstance( new InstanceOfBuffer(
				anExecutable, anInstance, theInstanceOfMachinePath) );

		aliasInstance->setFullyQualifiedNameID( "alias" +
				aFullyQualifiedNameID.substr(aFullyQualifiedNameID.find(':')) );

		return( anExecutable->saveAlias(aliasInstance) );
	}

	return( Symbol::REF_NULL );
}



/*
 *******************************************************************************
 * SEARCH CONNECT SYMBOL INSTANCE
 *******************************************************************************
 */

const Symbol & SymbolTable::searchConnectorInstance(
		ExecutableForm * anExecutable, const ObjectElement * objElement) const
{
	// SEARCH ON CURRENT BUFFER LIST
	{
		const Symbol & anInstance =
				anExecutable->getConnect().getByAstElement(objElement);
		if( anInstance.valid() )
		{
			return( anInstance );
		}
	}

	// SEARCH ON CURRENT ALIAS BUFFER LIST
	{
		const Symbol & anInstance =
				anExecutable->getAlias().getByAstElement(objElement);
		if( anInstance.is< InstanceOfConnect >() )
		{
			return( anInstance );
		}
	}


	// SEARCH ON CURRENT MODEL CHILD BUFFER LIST & MAKE AN ALIAS
	Symbol bfConnect;

	TableOfSymbol::const_iterator itMachine = anExecutable->instance_model_begin();
	TableOfSymbol::const_iterator itEnd = anExecutable->instance_model_end();
	for( ; itMachine != itEnd ; ++itMachine )
	{
		bfConnect = (*itMachine).getExecutable()->
				getConnect().getByAstElement(objElement);
		if( bfConnect.valid() )
		{
			break;
		}
	}

	if( bfConnect.valid() )
	{
		VectorOfInstanceOfMachine theInstanceOfMachinePath;
		theInstanceOfMachinePath.append( (*itMachine).rawMachine() );

		InstanceOfConnect * aliasInstance = new InstanceOfConnect(
				anExecutable, bfConnect.rawConnect(), theInstanceOfMachinePath );

		const std::string & aFullyQualifiedNameID =
				bfConnect.getFullyQualifiedNameID();

		aliasInstance->setFullyQualifiedNameID( "alias" +
				aFullyQualifiedNameID.substr(aFullyQualifiedNameID.find(':')) );

		return( anExecutable->saveAlias(aliasInstance) );
	}

	return( searchConnectorInstance(objElement) );
}



const Symbol & SymbolTable::searchConnectorInstance(ExecutableForm * anExecutable,
		const std::string & aFullyQualifiedNameID) const
{
	// SEARCH ON CURRENT BUFFER LIST
	{
		const Symbol & anInstance =
			anExecutable->getConnect().getByFQNameID( aFullyQualifiedNameID );
		if( anInstance.valid() )
		{
			return( anInstance );
		}
	}

	// SEARCH ON CURRENT ALIAS BUFFER LIST
	{
		const Symbol & anInstance =
				anExecutable->getAlias().getByFQNameID( aFullyQualifiedNameID );
		if( anInstance.is< InstanceOfConnect >() )
		{
			return( anInstance );
		}
	}

	// SEARCH ON CURRENT MODEL CHILD BUFFER LIST & MAKE AN ALIAS
	Symbol bfConnect;

	TableOfSymbol::const_iterator itMachine = anExecutable->instance_model_begin();
	TableOfSymbol::const_iterator endMachine = anExecutable->instance_model_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		bfConnect = (*itMachine).getExecutable()->getConnect().
				getByFQNameID( aFullyQualifiedNameID );
		if( bfConnect.valid() )
		{
			break;
		}
	}

	if( bfConnect.valid() )
	{
		VectorOfInstanceOfMachine theInstanceOfMachinePath;
		theInstanceOfMachinePath.append( (*itMachine).rawMachine() );

		InstanceOfConnect * aliasInstance = new InstanceOfConnect(
				anExecutable, bfConnect.rawConnect(), theInstanceOfMachinePath );

		const std::string & aFullyQualifiedNameID =
				bfConnect.getFullyQualifiedNameID();

		aliasInstance->setFullyQualifiedNameID( "alias" +
				aFullyQualifiedNameID.substr(aFullyQualifiedNameID.find(':')) );

		return( anExecutable->saveAlias(aliasInstance) );
	}

	return( searchConnectorInstance( aFullyQualifiedNameID ) );
}


const Symbol & SymbolTable::searchConnectorInstanceByQualifiedNameID(
		ExecutableForm * anExec, const std::string & aQualifiedNameID) const
{
	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExec->getConnect().getByQualifiedNameID(aQualifiedNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & SymbolTable::searchConnectorInstanceByNameID(
		ExecutableForm * anExec, const std::string & aNameID) const
{
	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExec->getConnect().getByNameID(aNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( Symbol::REF_NULL );
}


/*
 *******************************************************************************
 * SEARCH MACHINE INSTANCE
 *******************************************************************************
 */
const Symbol & SymbolTable::searchInstanceModelByNameID(
		ExecutableForm * anExec, const std::string & aNameID) const
{
	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExec->getInstanceModel().getByNameID(aNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & SymbolTable::searchInstanceModelByNameID(
		COMPILE_CONTEXT * aCTX, const std::string & aNameID) const
{
	return( searchInstanceModelByNameID(
			aCTX->mCompileCtx->getExecutable(), aNameID) );
}


const Symbol & SymbolTable::searchMachineInstanceByNameID(
		ExecutableForm * anExec, const std::string & aNameID) const
{
	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExec->getInstanceStatic().getByNameID(aNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & SymbolTable::searchMachineInstanceByNameID(
		COMPILE_CONTEXT * aCTX, const std::string & aNameID) const
{
	return( searchMachineInstanceByNameID(
			aCTX->mCompileCtx->getExecutable(), aNameID) );
}


/**
 * SEARCH
 * for Machine Instance
 */
const Symbol & SymbolTable::searchInstanceModel(
		COMPILE_CONTEXT * aCTX, const ObjectElement * astElement) const
{
	ExecutableForm * anExec = aCTX->mCompileCtx->getExecutable();

	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExec->getByAstInstanceModel(astElement);
		if( foundInstance.valid() && foundInstance.machine().isnotThis() )
		{
			return( foundInstance );
		}
	}

	return( searchInstanceStatic( astElement ) );
}


const Symbol & SymbolTable::searchInstanceStatic(
		COMPILE_CONTEXT * aCTX, const ObjectElement * astElement) const
{
	ExecutableForm * anExec = aCTX->mCompileCtx->getExecutable();

	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExec->getByAstInstanceStatic(astElement);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( searchInstanceStatic( astElement ) );
}


const Symbol & SymbolTable::searchInstanceDynamic(
		COMPILE_CONTEXT * aCTX, const ObjectElement * astElement) const
{
	ExecutableForm * anExec = aCTX->mCompileCtx->getExecutable();

	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExec->getByAstInstanceDynamic(astElement);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( searchInstanceStatic( astElement ) );
}




InstanceOfMachine * SymbolTable::searchInstanceStatic(
		const ObjectElement * fromMachine, const UniFormIdentifier & anUFI)
{
	// RESET ERROR
	resetError();

	BFList listofMachine;
	searchInstanceStatic(
			fromMachine->getContainerMachine(), anUFI, listofMachine);

	if( listofMachine.populated() )
	{
		incrErrorCount();
		ERROR_OS << "Too more statemachine << "
				<< anUFI.str() << " >> are found !";

		return( listofMachine.first().to_ptr< InstanceOfMachine >() );
	}
	else if( listofMachine.nonempty() )
	{
		return( listofMachine.first().to_ptr< InstanceOfMachine >() );
	}
	else
	{
		incrErrorCount();
		ERROR_OS << "Unfound statemachine << "
				<< anUFI.str() << " >> !";

		return( NULL );
	}
}

void SymbolTable::searchInstanceStatic(const ObjectElement * refMachine,
		const UniFormIdentifier & anUFI, BFList & foundList) const
{
	std::string strUFI = anUFI.str();
	SymbolPredicateByCompiledFQNameID pred(strUFI);

	if( not anUFI.hasLocator() )
	{
		std::string refUfi = refMachine->getFullyQualifiedNameID();
		refUfi = refUfi.substr(
				refUfi.find(FQN_ID_ROOT_SEPARATOR), refUfi.size());

		pred.mQualifiedNameID = refUfi + '.' + strUFI;
		searchCompiledElement(mListOfInstanceStatic, pred, foundList);

		if( anUFI.populated() )
		{
			std::string commonAncestor = anUFI.first().str();

			std::string::size_type pos;
			while( (pos = refUfi.rfind(commonAncestor)) != std::string::npos )
			{
				refUfi = refUfi.substr(0, pos);
				pred.mQualifiedNameID = refUfi + strUFI;
				searchCompiledElement(mListOfInstanceStatic, pred, foundList);
			}
		}
	}
	else
	{
		searchCompiledElement(mListOfInstanceStatic, pred, foundList);
	}
}


void SymbolTable::searchInstanceByNameID(COMPILE_CONTEXT * aCTX,
		const std::string & aNameID, BFList & foundList) const
{
	switch( aCTX->mType->getTypeSpecifierKind() )
	{
		case TYPE_MACHINE_SPECIFIER:
		{
			searchMachineInstanceByNameID(aNameID, foundList);
			break;
		}
		case TYPE_PORT_SPECIFIER:
		{
			searchPortInstanceByNameID(aNameID, foundList);
			break;
		}
		case TYPE_SIGNAL_SPECIFIER:
		{
			searchPortInstanceByNameID(aNameID, foundList);
			break;
		}

		case TYPE_BUFFER_SPECIFIER:
		{
			searchBufferInstanceByNameID(aNameID, foundList);
			break;
		}

		case TYPE_CONNECTOR_SPECIFIER:
		{
			searchConnectorInstanceByNameID(aNameID, foundList);
			break;
		}


		case TYPE_BOOLEAN_SPECIFIER:

		case TYPE_POS_INTEGER_SPECIFIER:
		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_INTEGER_SPECIFIER:

		case TYPE_URATIONAL_SPECIFIER:
		case TYPE_RATIONAL_SPECIFIER:

		case TYPE_UFLOAT_SPECIFIER:
		case TYPE_FLOAT_SPECIFIER:

		case TYPE_UREAL_SPECIFIER:
		case TYPE_REAL_SPECIFIER:

		case TYPE_ENUM_SPECIFIER:

		case TYPE_CHARACTER_SPECIFIER:
		case TYPE_STRING_SPECIFIER:

		case TYPE_CLOCK_SPECIFIER:
		case TYPE_TIME_SPECIFIER:
		case TYPE_CONTINUOUS_TIME_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:

		case TYPE_INTERVAL_SPECIFIER:
		case TYPE_OPERATOR_SPECIFIER:
		case TYPE_AVMCODE_SPECIFIER:
		case TYPE_MESSAGE_SPECIFIER:
		{
			searchDataInstanceByNameID(aNameID, foundList);

			if( foundList.empty() )
			{
				searchPortInstanceByNameID(aNameID, foundList);

				searchMachineInstanceByNameID(aNameID, foundList);

				searchBufferInstanceByNameID(aNameID, foundList);

				searchConnectorInstanceByNameID(aNameID, foundList);
			}
			break;
		}

		default:
		{
			searchDataInstanceByNameID(aNameID, foundList);

			searchPortInstanceByNameID(aNameID, foundList);

			searchMachineInstanceByNameID(aNameID, foundList);

			searchBufferInstanceByNameID(aNameID, foundList);

			searchConnectorInstanceByNameID(aNameID, foundList);

			break;
		}
	}

	if( foundList.empty() )
	{
		searchDataInstanceByNameID(aNameID, foundList);
	}
}



void SymbolTable::searchInstanceByQualifiedNameID(COMPILE_CONTEXT * aCTX,
		const std::string & aQualifiedNameID, BFList & foundList) const
{
	switch( aCTX->mType->getTypeSpecifierKind() )
	{
		case TYPE_MACHINE_SPECIFIER:
		{
			searchMachineInstanceByQualifiedNameID(aQualifiedNameID, foundList);
			break;
		}
		case TYPE_PORT_SPECIFIER:
		{
			searchPortInstanceByQualifiedNameID(aQualifiedNameID, foundList);
			break;
		}
		case TYPE_SIGNAL_SPECIFIER:
		{
			searchPortInstanceByQualifiedNameID(aQualifiedNameID, foundList);
			break;
		}

		case TYPE_BUFFER_SPECIFIER:
		{
			searchBufferInstanceByQualifiedNameID(aQualifiedNameID, foundList);
			break;
		}

		case TYPE_CONNECTOR_SPECIFIER:
		{
			searchConnectorInstanceByQualifiedNameID(aQualifiedNameID, foundList);
			break;
		}


		case TYPE_BOOLEAN_SPECIFIER:

		case TYPE_POS_INTEGER_SPECIFIER:
		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_INTEGER_SPECIFIER:

		case TYPE_URATIONAL_SPECIFIER:
		case TYPE_RATIONAL_SPECIFIER:

		case TYPE_UFLOAT_SPECIFIER:
		case TYPE_FLOAT_SPECIFIER:

		case TYPE_UREAL_SPECIFIER:
		case TYPE_REAL_SPECIFIER:

		case TYPE_ENUM_SPECIFIER:

		case TYPE_CHARACTER_SPECIFIER:
		case TYPE_STRING_SPECIFIER:

		case TYPE_CLOCK_SPECIFIER:
		case TYPE_TIME_SPECIFIER:
		case TYPE_CONTINUOUS_TIME_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:

		case TYPE_INTERVAL_SPECIFIER:
		case TYPE_OPERATOR_SPECIFIER:
		case TYPE_AVMCODE_SPECIFIER:
		case TYPE_MESSAGE_SPECIFIER:
		{
			searchDataInstanceByQualifiedNameID(aQualifiedNameID, foundList);

			if( foundList.empty() )
			{
				searchPortInstanceByQualifiedNameID(aQualifiedNameID, foundList);

				searchMachineInstanceByQualifiedNameID(aQualifiedNameID, foundList);

				searchBufferInstanceByQualifiedNameID(aQualifiedNameID, foundList);

				searchConnectorInstanceByQualifiedNameID(aQualifiedNameID, foundList);
			}
			break;
		}

		default:
		{
			searchDataInstanceByQualifiedNameID(aQualifiedNameID, foundList);

			searchPortInstanceByQualifiedNameID(aQualifiedNameID, foundList);

			searchMachineInstanceByQualifiedNameID(aQualifiedNameID, foundList);

			searchBufferInstanceByQualifiedNameID(aQualifiedNameID, foundList);

			searchConnectorInstanceByQualifiedNameID(aQualifiedNameID, foundList);

			break;
		}
	}

	if( foundList.empty() )
	{
		searchDataInstanceByNameID(aQualifiedNameID, foundList);
	}
}


/**
 * SEARCH
 * for DataFactory, Port or Machine
 */
const BF & SymbolTable::searchInstance(
		COMPILE_CONTEXT * aCTX, const ObjectElement * objElement)
{
	// CASE form is a PORT
	if( objElement->is< Port >() )
	{
		const Symbol & foundInstance = XQuery.getSemPortByAstElement(
				aCTX->mCompileCtx->getExecutable(), objElement);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	// CASE form is a [STATE]MACHINE
	if( objElement->is< Machine >() )
	{
		{
			const Symbol & foundInstance =
					searchInstanceStatic(aCTX, objElement);
			if( foundInstance.valid() )
			{
				return( foundInstance );
			}
		}
		{
			const Symbol & foundInstance =
					searchInstanceModel(aCTX, objElement);
			if( foundInstance.valid() )
			{
				return( foundInstance );
			}
		}

		return( searchInstanceStatic(objElement) );
	}

	// CASE form is a BUFFER
	if( objElement->is< Buffer >() )
	{
		const Symbol & foundInstance = searchBufferInstance(
				aCTX->mCompileCtx->getExecutable(), objElement);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}


	// CASE form is a CONNECT
	if( objElement->is< Connector >() )
	{
		const Symbol & foundInstance = searchConnectorInstance(
				aCTX->mCompileCtx->getExecutable(), objElement);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	{
		const BF & foundInstance = searchDataInstance(aCTX, objElement);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	// For the Case of undetected TYPE
	{
		const Symbol & foundInstance = searchInstanceStatic(objElement);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( BF::REF_NULL );
}



const BF & SymbolTable::searchInstance(COMPILE_CONTEXT * aCTX,
		const std::string & aFullyQualifiedNameID)
{
	// CASE element is a PORT
	if( aCTX->typeMustBePortFamily() )
	{
		const Symbol & foundInstance = XQuery.getSemPort(
				aCTX->mCompileCtx->getExecutable(), aFullyQualifiedNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	// CASE element is a [STATE]MACHINE
	if( aCTX->typeMustBeMachineFamily() )
	{
		const Symbol & foundInstance =
				searchInstanceStatic(aFullyQualifiedNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	// CASE element is a BUFFER
	if( aCTX->typeMustBeBufferFamily() )
	{
		const Symbol & foundInstance = searchBufferInstance(
				aCTX->mCompileCtx->getExecutable(), aFullyQualifiedNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}


	// CASE element is a CONNECT
	if( aCTX->typeMustBeConnectorFamily() )
	{
		const Symbol & foundInstance = searchConnectorInstance(
				aCTX->mCompileCtx->getExecutable(), aFullyQualifiedNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	// CASE element is anything ELSE
	// UNCONDITIONAL
	{
		const BF & foundInstance =
				searchDataInstance(aCTX, aFullyQualifiedNameID);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( BF::REF_NULL );
}


/*
 * SEARCH
 * Program for a given FORM
 */
const BF & SymbolTable::searchTransition(
		COMPILE_CONTEXT * aCTX, const ObjectElement * objElement) const
{
	ExecutableForm * anExec = aCTX->mCompileCtx->getExecutable();
	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const BF & tmpTransition =
				anExec->getTransitionByAstElement(objElement);
		if( tmpTransition.valid() )
		{
			return( tmpTransition );
		}
	}

	{
		const BF & aTransition = searchTransition(objElement);
		if( aTransition.valid() )
		{
			return( aTransition );
		}
	}

	return( BF::REF_NULL );
}


const BF & SymbolTable::searchTransition(
		COMPILE_CONTEXT * aCTX, const std::string & aFullyQualifiedNameID) const
{
	ExecutableForm * anExec = aCTX->mCompileCtx->getExecutable();

	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const BF & tmpTransition = anExec->getTransition(aFullyQualifiedNameID);
		if( tmpTransition.valid() )
		{
			return( tmpTransition );
		}
	}

	{
		const BF & aTransition = searchTransition(aFullyQualifiedNameID);
		if( aTransition.valid() )
		{
			return( aTransition );
		}
	}

	return( BF::REF_NULL );
}


const BF & SymbolTable::searchTransitionByNameID(
		COMPILE_CONTEXT * aCTX, const std::string & aNameID) const
{
	ExecutableForm * anExec = aCTX->mCompileCtx->getExecutable();

	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const BF & tmpTransition = anExec->getTransitionByNameID(aNameID);
		if( tmpTransition.valid() )
		{
			return( tmpTransition );
		}
	}

	{
		const BF & aTransition = searchTransitionByNameID(aNameID);
		if( aTransition.valid() )
		{
			return( aTransition );
		}
	}

	return( BF::REF_NULL );
}


const BF & SymbolTable::searchProgram(
		COMPILE_CONTEXT * aCTX, const ObjectElement * objElement) const
{
	ExecutableForm * anExec = aCTX->mCompileCtx->getExecutable();
	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const BF & tmpProgram = anExec->getProgramByAstElement(objElement);
		if( tmpProgram.valid() )
		{
			return( tmpProgram );
		}
	}

	{
		const BF & aProgram = searchProgram(objElement);
		if( aProgram.valid() )
		{
			return( aProgram );
		}
	}

	return( searchExecutable(objElement) );
}


const BF & SymbolTable::searchProgram(
		COMPILE_CONTEXT * aCTX, const std::string & aFullyQualifiedNameID) const
{
	ExecutableForm * anExec = aCTX->mCompileCtx->getExecutable();

	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const BF & tmpProgram = anExec->getProgram(aFullyQualifiedNameID);
		if( tmpProgram.valid() )
		{
			return( tmpProgram );
		}
	}

	{
		const BF & aProgram = searchProgram(aFullyQualifiedNameID);
		if( aProgram.valid() )
		{
			return( aProgram );
		}
	}

	return( searchExecutable(aFullyQualifiedNameID) );
}


const BF & SymbolTable::searchProgramByNameID(
		COMPILE_CONTEXT * aCTX, const std::string & aNameID) const
{
	ExecutableForm * anExec = aCTX->mCompileCtx->getExecutable();

	for( ; anExec != NULL ; anExec = anExec->getExecutableContainer() )
	{
		const BF & tmpProgram = anExec->getProgramByNameID(aNameID);
		if( tmpProgram.valid() )
		{
			return( tmpProgram );
		}
	}

	{
		const BF & aProgram = searchProgramByNameID(aNameID);
		if( aProgram.valid() )
		{
			return( aProgram );
		}
	}

	return( searchExecutableByNameID(aNameID) );
}


/*
 * SEARCH
 * Executable of the MODEL for a given FORM
 */
ExecutableForm * SymbolTable::searchExecutableModel(const Machine * aMachine)
{
	// RESET ERROR
	resetError();

	const BF & aModel = aMachine->getType();
	if( aModel.is< Machine >() )
	{
		if( aModel.to_ptr< Machine >()->getSpecifier().hasDesignModel() )
		{
			return( searchExecutable(aModel.to_ptr< Machine >()).
					to_ptr< ExecutableForm >() );
		}
		else
		{
			return( searchExecutableModel(aModel.to_ptr< Machine >()) );
		}
	}
	else if( aModel.is< Identifier >() )
	{
		std::string aNameID = aModel.to_ptr< Identifier >()->getValue();

		const BF & foundExec = searchExecutableByNameID(aNameID);

		return( foundExec.valid() ?
				foundExec.as_ptr< ExecutableForm >() : NULL );
	}

	else
	{
		std::string aQualifiedNameID = aModel.is< QualifiedIdentifier >()
				? aModel.to_ptr< QualifiedIdentifier >()->getValue()
				: ( aModel.is< UniFormIdentifier >()
					? aModel.to_ptr< UniFormIdentifier >()->toStringLocation()
					: aModel.str() );

		const BF & foundExec =
				searchExecutableByQualifiedNameID( aQualifiedNameID );

		return( foundExec.valid() ?
				foundExec.as_ptr< ExecutableForm >() : NULL );
	}
}


/**
 * SEARCH SYMBOL
 * for DataFactory, Port, Machine, Executable
 */
const BF & SymbolTable::searchSymbol(COMPILE_CONTEXT * aCTX,
		const ObjectElement * objElement)
{
	{
		const BF & theSymbol = searchInstance(aCTX, objElement);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	{
		const BF & theSymbol = searchTransition(aCTX, objElement);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}
	{
		const BF & theSymbol = searchProgram(aCTX, objElement);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	return( BF::REF_NULL );
}


const BF & SymbolTable::searchSymbol(COMPILE_CONTEXT * aCTX,
		const std::string & aFullyQualifiedNameID)
{
	{
		const BF & theSymbol = searchInstance(aCTX, aFullyQualifiedNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	{
		const BF & theSymbol = searchTransition(aCTX, aFullyQualifiedNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	{
		const BF & theSymbol = searchProgram(aCTX, aFullyQualifiedNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	return( BF::REF_NULL );
}


BF SymbolTable::searchSymbolByUFI(
		COMPILE_CONTEXT * aCTX, const UniFormIdentifier & anUFI)
{
	UniFormIdentifier::const_iterator it = anUFI.begin();
	UniFormIdentifier::const_iterator itEnd = anUFI.end();

	std::ostringstream ossUFI;
	const ObjectElement * TheMainObjectElement = NULL;

	BF bfInstance;
	InstanceOfMachine * theInstanceMachine;

	// CHECKING ROOT MACHINE INSTANCE
	if( (*it).is< ObjectElement >() )
	{
		TheMainObjectElement = (*it).to_ptr< ObjectElement >();

		if( (bfInstance = searchInstanceStatic(TheMainObjectElement)).valid() )
		{
			theInstanceMachine = bfInstance.to_ptr< InstanceOfMachine >();
		}
		else
		{
			incrErrorCount();
			ERROR_OS << "Unfound the main form < "
					<< TheMainObjectElement->getFullyQualifiedNameID()
					<< " > of UFI < " << anUFI.str() << " > in the system << "
					<< mConfiguration.getExecutableSystem().rawSystemInstance()
							->getAstElement()->getFullyQualifiedNameID() << " >>"
					<< std::endl;

			return( BF::REF_NULL );
		}
	}
	else
	{
		ossUFI << anUFI.toStringLocator()
				<< FQN_ID_ROOT_SEPARATOR << (*it).str();

		theInstanceMachine =
				mConfiguration.getExecutableSystem().rawSystemInstance();
		TheMainObjectElement = theInstanceMachine->getAstElement();
		if( (TheMainObjectElement != NULL)
			&& TheMainObjectElement->fqnEquals( ossUFI.str() ) )
		{
			if( it == itEnd )
			{
				return( mConfiguration.getExecutableSystem().getSystemInstance() );
			}
		}
		else
		{
			incrErrorCount();
			ERROR_OS << "Unfound the main form < "
					<< ossUFI.str() << " > of UFI < "
					<< anUFI.str() << " > in the system << "
					<< mConfiguration.getExecutableSystem().rawSystemInstance()
							->getAstElement()->getFullyQualifiedNameID() << " >>"
					<< std::endl;

			return( BF::REF_NULL );
		}
	}

	ossUFI.str("");
	ossUFI << theInstanceMachine->getFullyQualifiedNameID();

	// CHECKING MAIN MACHINE INSTANCE
	for( ++it ; it != itEnd ; ++it )
	{
		if( (*it).isIdentifier() )
		{
			ossUFI << '.' << (*it).str();

			bfInstance = theInstanceMachine->getExecutable()->
					getInstanceStatic().getByFQNameID( ossUFI.str() );

			if( bfInstance.invalid() )
			{
				bfInstance = theInstanceMachine->getExecutable()->
						getInstanceStatic().getByNameID( (*it).str() );
			}

			if( bfInstance.valid() )
			{
				theInstanceMachine = bfInstance.to_ptr< InstanceOfMachine >();

				continue;
			}
		}
		else if( (*it).is< ObjectElement >() )
		{
			if( (*it).to_ptr< ObjectElement >()->getContainer()
				== TheMainObjectElement )
			{
				TheMainObjectElement = (*it).to_ptr< ObjectElement >();

				if( (bfInstance = theInstanceMachine->getExecutable()->
						getByAstInstanceStatic(TheMainObjectElement)).valid() )
				{
					theInstanceMachine = bfInstance.to_ptr< InstanceOfMachine >();

					ossUFI.str("");
					ossUFI << theInstanceMachine->getFullyQualifiedNameID();

					continue;
				}
			}
			else
			{
				incrErrorCount();
				ERROR_OS << "MissFormed UFI < "
						<< anUFI.str() << " > : the field < "
						<< (*it).to_ptr<
								ObjectElement >()->getFullyQualifiedNameID()
						<< " > container is not < "
						<< TheMainObjectElement->getFullyQualifiedNameID()
						<< " > !!!" << std::endl;

				return( BF::REF_NULL );
			}
		}
		else
		{
			incrErrorCount();
			ERROR_OS << "Unexpected < " << it->str()
					<< " > as field of the UFI < "
					<< anUFI.str() << " > !!!"
					<< std::endl;

			return( BF::REF_NULL );
		}

		break;
	}

	if( bfInstance.valid() )
	{
		if( it == itEnd )
		{
			return( bfInstance );
		}

		// CHECKING FOR MAIN MACHINE
		ossUFI.str("");
		ossUFI << theInstanceMachine->getFullyQualifiedNameID();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).isUfid() )
			{
				ossUFI << '.' << it->str();
			}
			else
			{
				incrErrorCount();
				ERROR_OS << "Unexpected < " << it->str()
						<< " > as field of the UFI < " << anUFI.str()
						<< " > !!!" << std::endl;

				return( BF::REF_NULL );
			}
		}

		const BF & aSymbol = theInstanceMachine->getExecutable()->
				getSymbol(ossUFI.str(), aCTX->getTypeFamily());
		if( aSymbol.valid() )
		{
			return( aSymbol );
		}
		else
		{
			incrErrorCount();
			ERROR_OS << "Unfound a runtime symbol for the UFI < "
					<< anUFI.str() << " >" << std::endl;
		}
	}

	return( BF::REF_NULL );
}


const BF & SymbolTable::searchSemSymbol(
		COMPILE_CONTEXT * aCTX, const ObjectElement * astElement) const
{
	BaseAvmProgram * aProgram = aCTX->mCompileCtx;
	for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
	{
		const BF & theSymbol =
			aProgram->getSymbolByAstElement(astElement, aCTX->getTypeFamily());
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	if( aCTX->mRuntimeCtx != aCTX->mCompileCtx )
	{
		aProgram = aCTX->mRuntimeCtx;
		for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
		{
			const BF & theSymbol = aProgram->
					getSymbolByAstElement(astElement, aCTX->getTypeFamily());
			if( theSymbol.valid() )
			{
				return( theSymbol );
			}
		}
	}

	return( BF::REF_NULL );
}

const BF & SymbolTable::searchSemSymbolByQualifiedNameID(
		COMPILE_CONTEXT * aCTX, const std::string & aQualifiedNameID) const
{
	BaseAvmProgram * aProgram = aCTX->mCompileCtx;
	for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
	{
		const BF & theSymbol = aProgram->getSymbolByQualifiedNameID(
				aQualifiedNameID, aCTX->getTypeFamily());
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	if( aCTX->mRuntimeCtx != aCTX->mCompileCtx )
	{
		aProgram = aCTX->mRuntimeCtx;
		for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
		{
			const BF & theSymbol = aProgram->getSymbolByQualifiedNameID(
					aQualifiedNameID, aCTX->getTypeFamily());
			if( theSymbol.valid() )
			{
				return( theSymbol );
			}
		}
	}

	return( BF::REF_NULL );
}


const BF & SymbolTable::searchSemSymbolByNameID(
		COMPILE_CONTEXT * aCTX, const std::string & aNameID) const
{
	BaseAvmProgram * aProgram = aCTX->mCompileCtx;
	for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
	{
		const BF & theSymbol =
				aProgram->getSymbolByNameID(aNameID, aCTX->getTypeFamily());
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	if( aCTX->mRuntimeCtx != aCTX->mCompileCtx )
	{
		aProgram = aCTX->mRuntimeCtx;
		for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
		{
			const BF & theSymbol = aProgram->
					getSymbolByNameID(aNameID, aCTX->getTypeFamily());
			if( theSymbol.valid() )
			{
				return( theSymbol );
			}
		}
	}

	return( BF::REF_NULL );
}


// TODO Optimize searchSymbolByQualifiedNameID
BF SymbolTable::searchSymbolByQualifiedNameID(
		COMPILE_CONTEXT * aCTX, const std::string & aQualifiedNameID)
{
	{
		const BF & theSymbol =
				searchSemSymbolByQualifiedNameID(aCTX, aQualifiedNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	ListOfString listOfId;
	avm_size_t idCount = NamedElement::collectNameID(listOfId, aQualifiedNameID);
	if( idCount == 2 )
	{
		const Symbol & aMachine = aCTX->mCompileCtx->getExecutable()
				->getInstanceStatic().getByNameID(listOfId.first());
		if( aMachine.valid() )
		{
			const BF & theSymbol = aMachine.getExecutable()->
					getSymbolByNameID(listOfId.second(), aCTX->getTypeFamily());
			if( theSymbol.valid() )
			{
				if( theSymbol.is< BaseInstanceForm >() )
				{
					return( createAliasIfNotAccessible(
							aCTX, aMachine.rawMachine(), theSymbol) );
				}

				return( theSymbol );
			}
		}
	}

	BFList foundList;
	searchInstanceByQualifiedNameID(aCTX, aQualifiedNameID, foundList);
	if( foundList.singleton() )
	{
		return( foundList.pop_first() );
	}
	else if( foundList.populated() )
	{
		incrErrorCount();
		ERROR_OS << "Indeterminism:> found too many element < "
				<< aQualifiedNameID << " > from "
				<< ( aCTX->mCompileCtx->is< ExecutableForm >() ?
						"executable" : "program" )
				<< " < " << aCTX->mCompileCtx->getFullyQualifiedNameID()
				<< " > !!!";
		while( foundList.nonempty() )
		{
			ERROR_OS << "\n\tFound :> " << str_header( foundList.pop_first() );
		}

		return( BF::REF_NULL );
	}

	{
		const BF & theSymbol = searchTransition(aCTX, aQualifiedNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}
	{
		const BF & theSymbol = searchProgram(aCTX, aQualifiedNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	{
		const BF & theSymbol = searchInstanceStatic(aQualifiedNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}
	return( BF::REF_NULL );
}


BF SymbolTable::searchSymbolByNameID(
		COMPILE_CONTEXT * aCTX, const std::string & aNameID)
{
	{
		const BF & theSymbol = searchSemSymbolByNameID(aCTX, aNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	BFList foundList;
	searchInstanceByNameID(aCTX, aNameID, foundList);
	if( foundList.singleton() )
	{
		return( foundList.pop_first() );
	}
	else if( foundList.populated() )
	{
		incrErrorCount();
		ERROR_OS << "Indeterminism:> found too many element < " << aNameID
				<< " > from " << ( aCTX->mCompileCtx->is< ExecutableForm >() ?
						"executable" : "program" )
				<< " < " << aCTX->mCompileCtx->getFullyQualifiedNameID() << " > !!!";
		while( foundList.nonempty() )
		{
			ERROR_OS << "\n\tFound :> " << str_header( foundList.pop_first() );
		}

		return( BF::REF_NULL );
	}

	{
		const BF & theSymbol = searchMachineInstanceByNameID(aCTX, aNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}
	{
		const BF & theSymbol = searchInstanceModelByNameID(aCTX, aNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	{
		const BF & theSymbol = searchTransitionByNameID(aCTX, aNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}
	{
		const BF & theSymbol = searchProgramByNameID(aCTX, aNameID);
		if( theSymbol.valid() )
		{
			return( theSymbol );
		}
	}

	return( BF::REF_NULL );
}


BF SymbolTable::createAliasIfNotAccessible(COMPILE_CONTEXT * aCTX,
		InstanceOfMachine * aContainerInstance, const BF & bfInstance)
{
	if( not aContainerInstance->getSpecifier().isDesignInstanceStatic() )
	{
		return( createAliasIfNotAccessible(aCTX, bfInstance) );
	}

	ExecutableForm * anExecutable = aCTX->mCompileCtx->getExecutable();

	const ExecutableForm * lcaExecutable = anExecutable->LCRA(
			aContainerInstance->getContainer()->getExecutable() );

	if( lcaExecutable != NULL )
	{
		BaseInstanceForm * ptrInstance = bfInstance.to_ptr< BaseInstanceForm >();

		std::string fqnPrefix = lcaExecutable->getAstFullyQualifiedNameID();

		ListOfString strList;
		NamedElement::collectNameID(strList,
				aContainerInstance->getAstFullyQualifiedNameID() + '.' +
				ptrInstance->getNameID(), fqnPrefix);

		VectorOfInstanceOfMachine theInstanceOfMachinePath;

		while( strList.populated() )
		{
			fqnPrefix = fqnPrefix + '.' + strList.pop_first();

			const Symbol & execInstance = lcaExecutable->getInstanceStatic().
					getByFQNameID( fqnPrefix );
			if( execInstance.valid() )
			{
				theInstanceOfMachinePath.append(execInstance.rawMachine());
				lcaExecutable = execInstance.getExecutable();
			}
			else
			{
				if( lcaExecutable->getAllData().getByFQNameID( fqnPrefix ).valid()
				|| lcaExecutable->getBuffer().getByFQNameID( fqnPrefix ).valid()
				|| lcaExecutable->getPort().getByFQNameID( fqnPrefix ).valid()
				|| lcaExecutable->getConnect().getByFQNameID( fqnPrefix ).valid() )
				{
					lcaExecutable = NULL;
				}
				break;
			}
		}

		if( lcaExecutable != NULL )
		{
//			if( theInstanceOfMachinePath.last() != aContainerInstance )
//			{
//				theInstanceOfMachinePath.append(aContainerInstance);
//			}

			Symbol newInstance;

			switch ( ptrInstance->classKind() )
			{
				case FORM_INSTANCE_DATA_KIND:
				{
					if( lcaExecutable->containsAllData(
							bfInstance.to_ptr< InstanceOfData >()) )
					{
						newInstance = new InstanceOfData(anExecutable,
								ptrInstance->to< InstanceOfData >(),
								theInstanceOfMachinePath);
					}

					break;
				}

				case FORM_INSTANCE_MACHINE_KIND:
				{
					if( lcaExecutable->getInstanceStatic().contains(bfInstance) )
					{
						newInstance = new InstanceOfMachine( anExecutable,
								ptrInstance->to< InstanceOfMachine >(),
								theInstanceOfMachinePath);
					}
					break;
				}

				case FORM_INSTANCE_PORT_KIND:
				{
					if( lcaExecutable->getPort().contains(bfInstance) )
					{
						newInstance = new InstanceOfPort(anExecutable,
								ptrInstance->to< InstanceOfPort >(),
								theInstanceOfMachinePath);
					}
					break;
				}

				case FORM_INSTANCE_BUFFER_KIND:
				{
					if( lcaExecutable->getBuffer().contains(bfInstance) )
					{
						newInstance = new InstanceOfBuffer(anExecutable,
								ptrInstance->to< InstanceOfBuffer >(),
								theInstanceOfMachinePath);
					}
					break;
				}

				case FORM_INSTANCE_CONNECTOR_KIND:
				{
					if( lcaExecutable->getConnect().contains(bfInstance) )
					{
						newInstance = new InstanceOfConnect(anExecutable,
								ptrInstance->to< InstanceOfConnect >(),
								theInstanceOfMachinePath);
					}
					break;
				}

				default :
				{
					break;
				}
			}

			if( newInstance != NULL )
			{
				newInstance.setFullyQualifiedNameID( "alias"
					+ aContainerInstance->getFullyQualifiedNameID().substr(
						aContainerInstance->getFullyQualifiedNameID().find(':'))
					+ "." + ptrInstance->getNameID() );

				if( not newInstance.getModifier().
						isVisibilityPublic( aCTX->getModifier() ) )
				{
					incrErrorCount();
					ERROR_OS << "Failed to create ALIAS for a non PUBLIC instance << "
							<< str_header( ptrInstance ) << " >> !!!";
				}

				if( newInstance.is< InstanceOfData >() )
				{
					aCTX->mCompileCtx->getExecutable()->appendDataAlias(newInstance);
				}
				else
				{
					aCTX->mCompileCtx->getExecutable()->appendAlias(newInstance);
				}

				return( newInstance );
			}
			else
			{
				incrErrorCount();
				ERROR_OS << "Failed to create ALIAS for instance << "
						<< str_header( ptrInstance ) << " >> !!!";
			}
		}
	}

	return( bfInstance );
}


BF SymbolTable::createAliasIfNotAccessible(
		COMPILE_CONTEXT * aCTX, const BF & bfInstance)
{
	BaseInstanceForm * ptrInstance = bfInstance.to_ptr< BaseInstanceForm >();

	for( BaseAvmProgram * tmpProgram = aCTX->mCompileCtx ; tmpProgram != NULL ;
			tmpProgram = tmpProgram->getContainer() )
	{
		if( tmpProgram == ptrInstance->getContainer() )
		{
			return( bfInstance );
		}
	}

	ExecutableForm * anExecutable = aCTX->mCompileCtx->getExecutable();

	const ExecutableForm * lcaExecutable = anExecutable->LCRA(
			ptrInstance->getContainer()->getExecutable() );

	if( lcaExecutable != NULL )
	{
		std::string fqnPrefix = lcaExecutable->getAstFullyQualifiedNameID();

		ListOfString strList;
		NamedElement::collectNameID(strList,
				ptrInstance->getAstFullyQualifiedNameID(), fqnPrefix);

		VectorOfInstanceOfMachine theInstanceOfMachinePath;

		while( strList.populated() )
		{
			fqnPrefix = fqnPrefix + '.' + strList.pop_first();

			const Symbol & execInstance =
				lcaExecutable->getInstanceStatic().getByFQNameID( fqnPrefix );
			if( execInstance.valid() )
			{
				theInstanceOfMachinePath.append(execInstance.rawMachine());
				lcaExecutable = execInstance.getExecutable();
			}
			else
			{
				if( lcaExecutable->getAllData().getByFQNameID( fqnPrefix ).valid()
				|| lcaExecutable->getBuffer().getByFQNameID(fqnPrefix ).valid()
				|| lcaExecutable->getPort().getByFQNameID(fqnPrefix ).valid()
				|| lcaExecutable->getConnect().getByFQNameID(fqnPrefix ).valid() )
				{
					lcaExecutable = NULL;
				}
				break;
			}
		}

		if( lcaExecutable != NULL )
		{
			Symbol newInstance;

			switch ( bfInstance.classKind() )
			{
				case FORM_INSTANCE_DATA_KIND:
				{
					if( lcaExecutable->containsAllData(
							bfInstance.to_ptr< InstanceOfData >()) )
					{
						newInstance = new InstanceOfData(anExecutable,
								ptrInstance->to< InstanceOfData >(),
								theInstanceOfMachinePath);
					}

					break;
				}

				case FORM_INSTANCE_MACHINE_KIND:
				{
					if( lcaExecutable->getInstanceStatic().contains(bfInstance) )
					{
						newInstance = new InstanceOfMachine(anExecutable,
								ptrInstance->to< InstanceOfMachine >(),
								theInstanceOfMachinePath);
					}
					break;
				}

				case FORM_INSTANCE_PORT_KIND:
				{
					if( lcaExecutable->getPort().contains(bfInstance) )
					{
						newInstance = new InstanceOfPort(anExecutable,
								ptrInstance->to< InstanceOfPort >(),
								theInstanceOfMachinePath);
					}
					break;
				}

				case FORM_INSTANCE_BUFFER_KIND:
				{
					if( lcaExecutable->getBuffer().contains(bfInstance) )
					{
						newInstance = new InstanceOfBuffer(anExecutable,
								ptrInstance->to< InstanceOfBuffer >(),
								theInstanceOfMachinePath);
					}
					break;
				}

				case FORM_INSTANCE_CONNECTOR_KIND:
				{
					if( lcaExecutable->getConnect().contains(bfInstance) )
					{
						newInstance = new InstanceOfConnect(anExecutable,
								ptrInstance->to< InstanceOfConnect >(),
								theInstanceOfMachinePath);
					}
					break;
				}

				default :
				{
					break;
				}
			}

			if( newInstance.valid() )
			{
				newInstance.setFullyQualifiedNameID( "alias" +
						ptrInstance->getFullyQualifiedNameID().substr(
								ptrInstance->getFullyQualifiedNameID().find(':')) );

				if( not newInstance.getModifier().
						isVisibilityPublic( aCTX->getModifier() ) )
				{
					incrErrorCount();
					ERROR_OS << "Failed to create ALIAS for a non PUBLIC instance << "
							<< str_header( ptrInstance ) << " >> !!!";
				}

				if( newInstance.is< InstanceOfData >() )
				{
					aCTX->mCompileCtx->getExecutable()->appendDataAlias(newInstance);
				}
				else
				{
					aCTX->mCompileCtx->getExecutable()->appendAlias(newInstance);
				}

				return( newInstance );
			}
			else
			{
				incrErrorCount();
				ERROR_OS << "Failed to create ALIAS for instance << "
						<< str_header( ptrInstance ) << " >> !!!";
			}
		}
	}

	return( bfInstance );
}



}

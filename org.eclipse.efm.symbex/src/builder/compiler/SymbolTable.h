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
#ifndef BUILDER_COMPILER_SYMBOLTABLE_H_
#define BUILDER_COMPILER_SYMBOLTABLE_H_

#include <builder/compiler/SymbolPredicate.h>

#include <collection/Typedef.h>
#include <collection/BFContainer.h>

#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/symbol/Symbol.h>

#include <fml/type/BaseTypeSpecifier.h>


namespace sep
{


class COMPILE_CONTEXT;

class Configuration;

class ExecutableForm;
class ExecutableSystem;

class InstanceOfBuffer;
class InstanceOfPort;

class ObjectElement;

class Machine;
class Port;

class TypeSpecifier;

class UniFormIdentifier;



class SymbolTable
{

protected:
	/**
	 * ATTRIBUTE
	 */
	Configuration & mConfiguration;

	ListOfSymbol mListOfInstanceStatic;

	ListOfSymbol mListOfPortInstance;

	ListOfSymbol mListOfBufferInstance;

	ListOfSymbol mListOfConnectorInstance;

	ListOfSymbol mListOfDataInstance;


	BFList mListOfMachineExecutable;

	BFList mListOfAvmTransition;

	BFList mListOfAvmProgram;

	ExecutableQuery XQuery;


	avm_size_t mErrorCount;

	avm_size_t mWarningCount;

	StringOutStream ERROR_OS;

	StringOutStream WARNING_OS;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbolTable(Configuration & aConfiguration)
	: mConfiguration( aConfiguration ),
	XQuery( mConfiguration ),
	mErrorCount( 0 ),
	mWarningCount(0),
	ERROR_OS(),
	WARNING_OS()
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	SymbolTable(const SymbolTable & aSymbolTable)
	: mConfiguration( aSymbolTable.mConfiguration ),
	XQuery( mConfiguration ),
	mErrorCount( aSymbolTable.mErrorCount ),
	mWarningCount(aSymbolTable.mWarningCount ),
	ERROR_OS(),
	WARNING_OS()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbolTable()
	{
		//!! NOTHING
	}


	/*
	 * SETTER
	 * mExecutableSystem
	 */
	inline void setSymbolTable(SymbolTable & aSymbolTable)
	{
		mListOfInstanceStatic.append( aSymbolTable.mListOfInstanceStatic );

		mListOfPortInstance.append( aSymbolTable.mListOfPortInstance );

		mListOfBufferInstance.append( aSymbolTable.mListOfBufferInstance );

		mListOfConnectorInstance.append( aSymbolTable.mListOfConnectorInstance );

		mListOfDataInstance.append( aSymbolTable.mListOfDataInstance );

		mListOfAvmTransition.append( aSymbolTable.mListOfAvmTransition );

		mListOfAvmProgram.append( aSymbolTable.mListOfAvmProgram );
	}


	/**
	 * SEARCH
	 * for Port
	 */
	InstanceOfPort * searchPortConnectorInstance(
			ExecutableForm * anExecutable, const ObjectElement * aPort) const;

	InstanceOfPort * searchPortConnectorInstance(
			ExecutableForm * anExecutable,
			const std::string & aFullyQualifiedNameID) const;


	const Symbol & searchPortSymbolInstance(
			ExecutableForm * anExecutable, Port * aPort) const;


	/**
	 * SEARCH
	 * for Type
	 */
	static const TypeSpecifier & searchTypeSpecifier(
			ExecutableSystem & anExecutableSystem,
			COMPILE_CONTEXT * aCTX, const ObjectElement * objElement);

	static const TypeSpecifier & searchTypeSpecifier(
			ExecutableSystem & anExecutableSystem, COMPILE_CONTEXT * aCTX,
			const std::string & aFullyQualifiedNameID);

	/**
	 * SEARCH
	 * for Data
	 */
	const BF & searchDataInstance(BaseAvmProgram * tmpProgram,
			const ObjectElement * objElement) const;

	const BF & searchDataInstance(
			COMPILE_CONTEXT * aCTX, const ObjectElement * objElement);


	const BF & searchDataInstance(BaseAvmProgram * tmpProgram,
			const std::string & aFullyQualifiedNameID) const;

	const BF & searchDataInstance(COMPILE_CONTEXT * aCTX,
			const std::string & aFullyQualifiedNameID);


	const BF & searchDataInstanceByQualifiedNameID(BaseAvmProgram * tmpProgram,
			const std::string & aQualifiedNameID) const;

	const BF & searchDataInstanceByQualifiedNameID(
			COMPILE_CONTEXT * aCTX, const std::string & aQualifiedNameID);


	const BF & searchDataInstanceByNameID(
			BaseAvmProgram * tmpProgram, const std::string & aNameID) const;

//$DELETE
//	const BF & searchDataInstanceByNameID(
//			COMPILE_CONTEXT * aCTX, const std::string & aNameID);



	const BF & searchDataInstanceAlias(
			COMPILE_CONTEXT * aCTX, const ObjectElement * objElement);

	const BF & searchDataInstanceAlias(COMPILE_CONTEXT * aCTX,
			const std::string & aFullyQualifiedNameID);


	const BF & createDataInstanceAlias(ExecutableForm * anExecutable,
			const std::string & aFullyQualifiedNameID,
			InstanceOfData * anInstance, ExecutableForm * instContainer);

	const BF & createDataInstanceAlias(ExecutableForm * anExecutable,
			const std::string & aFullyQualifiedNameID,
			InstanceOfData * anInstance,
			VectorOfInstanceOfMachine & theInstanceOfMachinePath);

	/**
	 * SEARCH
	 * for Machine Instance
	 */
	const Symbol & searchInstanceModel(
			COMPILE_CONTEXT * aCTX, const ObjectElement * astElement) const;

	const Symbol & searchInstanceStatic(
			COMPILE_CONTEXT * aCTX, const ObjectElement * astElement) const;

	const Symbol & searchInstanceDynamic(
			COMPILE_CONTEXT * aCTX, const ObjectElement * astElement) const;


	const Symbol & searchInstanceModelByNameID(
			ExecutableForm * anExecutable, const std::string & aNameID) const;

	const Symbol & searchInstanceModelByNameID(
			COMPILE_CONTEXT * aCTX, const std::string & aNameID) const;

	const Symbol & searchMachineInstanceByNameID(
			ExecutableForm * anExecutable, const std::string & aNameID) const;

	const Symbol & searchMachineInstanceByNameID(
			COMPILE_CONTEXT * aCTX, const std::string & aNameID) const;


	InstanceOfMachine * searchInstanceStatic(
			const ObjectElement * fromMachine, const UniFormIdentifier & anUFI);

	void searchInstanceStatic(const ObjectElement * refMachine,
			const UniFormIdentifier & anUFI, BFList & foundList) const;


	void searchInstanceByNameID(COMPILE_CONTEXT * aCTX,
			const std::string & aQualifiedNameID, BFList & foundList) const;

	void searchInstanceByQualifiedNameID(COMPILE_CONTEXT * aCTX,
			const std::string & aQualifiedNameID, BFList & foundList) const;

	/**
	 * SEARCH
	 * for Data, Port or Machine
	 */
	const BF & searchInstance(
			COMPILE_CONTEXT * aCTX, const ObjectElement * objElement);

	const BF & searchInstance(COMPILE_CONTEXT * aCTX,
			const std::string & aFullyQualifiedNameID);


	/**
	 * SEARCH SYMBOL
	 * for Data, Port or Machine
	 */
	const BF & searchSymbol(
			COMPILE_CONTEXT * aCTX, const ObjectElement * objElement);

	const BF & searchSymbol(COMPILE_CONTEXT * aCTX,
			const std::string & aFullyQualifiedNameID);

	BF searchSymbolByUFI(COMPILE_CONTEXT * aCTX, const UniFormIdentifier & anUFI);


	const BF & searchSemSymbol(COMPILE_CONTEXT * aCTX,
			const ObjectElement * objElement) const;

	const BF & searchSemSymbolByQualifiedNameID(COMPILE_CONTEXT * aCTX,
			const std::string & aQualifiedNameID) const;

	const BF & searchSemSymbolByNameID(COMPILE_CONTEXT * aCTX,
			const std::string & aNameID) const;


	BF searchSymbolByQualifiedNameID(COMPILE_CONTEXT * aCTX,
			const std::string & aQualifiedNameID);

	BF searchSymbolByNameID(
			COMPILE_CONTEXT * aCTX, const std::string & aNameID);


	BF createAliasIfNotAccessible(COMPILE_CONTEXT * aCTX,
			InstanceOfMachine * aContainerInstance, const BF & bfInstance);

	BF createAliasIfNotAccessible(COMPILE_CONTEXT * aCTX, const BF & bfInstance);


	/**
	 * SEARCH
	 * Executable for a given FORM
	 */
	const BF & searchTransition(
			COMPILE_CONTEXT * aCTX, const ObjectElement * objElement) const;

	const BF & searchTransition(COMPILE_CONTEXT * aCTX,
			const std::string & aFullyQualifiedNameID) const;

	const BF & searchTransitionByNameID(
			COMPILE_CONTEXT * aCTX, const std::string & aNameID) const;


	const BF & searchProgram(COMPILE_CONTEXT * aCTX,
			const ObjectElement * objElement) const;

	const BF & searchProgram(COMPILE_CONTEXT * aCTX,
			const std::string & aFullyQualifiedNameID) const;

	const BF & searchProgramByNameID(
			COMPILE_CONTEXT * aCTX, const std::string & aNameID) const;

	/**
	 * SEARCH
	 * Executable of the MODEL for a given FORM
	 */
	ExecutableForm * searchExecutableModel(const Machine * aMachine);

	/**
	 * SEARCH
	 * Instance for a given FORM
	 */
	inline const BF & searchCompiledElement(
			const BFList & listOfInstance, const SymbolPredicate & pred) const
	{
		BFList::const_iterator it = listOfInstance.begin();
		for( ; it != listOfInstance.end() ; ++it )
		{
			if( pred( (*it).to_ptr< BaseCompiledForm >() ) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}

	inline const Symbol & searchCompiledElement(
			const ListOfSymbol & listOfInstance,
			const SymbolPredicate & pred) const
	{
		ListOfSymbol::const_iterator it = listOfInstance.begin();
		ListOfSymbol::const_iterator endIt = listOfInstance.end();
		for( ; it != endIt ; ++it )
		{
			if( pred( (*it) ) )
			{
				return( *it );
			}
		}

		return( Symbol::REF_NULL );
	}

	template< typename T >
	inline T * searchCompiledElement(BFVector & tableOfInstance,
			const SymbolPredicate & pred) const
	{
		BFVector::const_iterator it = tableOfInstance.begin();
		for( ; it != tableOfInstance.end() ; ++it )
		{
			if( pred( (*it).as_ptr< T >() ) )
			{
				return( (*it).to_ptr< T >() );
			}
		}

		return( NULL );
	}

	inline const Symbol & searchCompiledElement(
			VectorOfSymbol & tableOfInstance,
			const SymbolPredicate & pred) const
	{
		VectorOfSymbol::const_iterator it = tableOfInstance.begin();
		VectorOfSymbol::const_iterator endIt = tableOfInstance.end();
		for( ; it != endIt ; ++it )
		{
			if( pred( (*it) ) )
			{
				return( (*it) );
			}
		}

		return( Symbol::REF_NULL );
	}


	inline void searchCompiledElement(const ListOfSymbol & listOfInstance,
			const SymbolPredicate & pred, BFList & foundList) const
	{
		ListOfSymbol::const_iterator it = listOfInstance.begin();
		ListOfSymbol::const_iterator endIt = listOfInstance.end();
		for( ; it != endIt ; ++it )
		{
			if( pred( (*it) ) )
			{
				foundList.append( *it );
			}
		}
	}


	/**
	 ***************************************************************************
	 * GETTER / SETTER
	 * mListOfMachineExecutable
	 ***************************************************************************
	 */
	inline const BF & searchExecutable(const ObjectElement * anElement) const
	{
		SymbolPredicateByCompiledElement pred( anElement );

		return( searchCompiledElement(mListOfMachineExecutable, pred) );
	}

	inline const BF & searchExecutable(
			const std::string & aFullyQualifiedNameID) const
	{
		SymbolPredicateByCompiledFQNameID pred(aFullyQualifiedNameID);

		return( searchCompiledElement(mListOfMachineExecutable, pred) );
	}

	inline const BF & searchExecutableByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		SymbolPredicateByQualifiedNameID pred(aQualifiedNameID);

		return( searchCompiledElement(mListOfMachineExecutable, pred) );
	}

	inline const BF & searchExecutableByNameID(
			const std::string & aQualifiedNameID) const
	{
		SymbolPredicateByNameID pred(aQualifiedNameID);

		return( searchCompiledElement(mListOfMachineExecutable, pred) );
	}



	/**
	 ***************************************************************************
	 * GETTER / SETTER
	 * mListOfInstanceStatic
	 * "SYMBOL TABLE : MACHINE"
	 ***************************************************************************
	 */

	inline void addInstanceStatic(const Symbol & anInstance)
	{
		mListOfInstanceStatic.append(anInstance);
	}

	inline const Symbol & searchInstanceStatic(
			const ObjectElement * anElement) const
	{
		SymbolPredicateByCompiledElement pred( anElement );

		return( searchCompiledElement(mListOfInstanceStatic, pred) );
	}

	inline const Symbol & searchInstanceStatic(
			const std::string & aFullyQualifiedNameID) const
	{
		SymbolPredicateByCompiledFQNameID pred(aFullyQualifiedNameID);

		return( searchCompiledElement(mListOfInstanceStatic, pred) );
	}


	inline void searchMachineInstanceByNameID(
			const std::string & aNameID, BFList & foundList) const
	{
		SymbolPredicateByNameID pred(aNameID);

		searchCompiledElement(mListOfInstanceStatic, pred, foundList);
	}

	inline void searchMachineInstanceByQualifiedNameID(
			const std::string & aQualifiedNameID, BFList & foundList) const
	{
		SymbolPredicateByQualifiedNameID pred(aQualifiedNameID);

		searchCompiledElement(mListOfInstanceStatic, pred, foundList);
	}


	/**
	 ***************************************************************************
	 * GETTER / SETTER
	 * mListOfPortInstance
	 * "SYMBOL TABLE : PORT"
	 ***************************************************************************
	 */
	inline void addPortInstance(const Symbol & anInstance)
	{
		mListOfPortInstance.append(anInstance);
	}

	inline const Symbol & searchPortInstance(
			const ObjectElement * anElement) const
	{
		SymbolPredicateByCompiledElement pred( anElement );

		return( searchCompiledElement(mListOfPortInstance, pred) );
	}

	inline void searchPortInstanceByNameID(
			const std::string & aNameID, BFList & foundList) const
	{
		SymbolPredicateByNameID pred(aNameID);

		searchCompiledElement(mListOfPortInstance, pred, foundList);
	}

	inline void searchPortInstanceByQualifiedNameID(
			const std::string & aQualifiedNameID, BFList & foundList) const
	{
		SymbolPredicateByQualifiedNameID pred(aQualifiedNameID);

		searchCompiledElement(mListOfPortInstance, pred, foundList);
	}


	const Symbol & searchPortInstance(
			COMPILE_CONTEXT * aCTX, InstanceOfData * aData) const;


	/**
	 ***************************************************************************
	 * GETTER / SETTER
	 * mListOfBufferInstance
	 * "SYMBOL TABLE : BUFFER"
	 ***************************************************************************
	 */
	inline void addBufferInstance(const Symbol & anInstance)
	{
		mListOfBufferInstance.append(anInstance);
	}

	inline const Symbol & searchBufferInstance(
			const ObjectElement * anElement) const
	{
		SymbolPredicateByCompiledElement pred( anElement );

		return( searchCompiledElement(mListOfBufferInstance, pred) );
	}

	inline void searchBufferInstanceByNameID(
			const std::string & aNameID, BFList & foundList) const
	{
		SymbolPredicateByNameID pred(aNameID);

		searchCompiledElement(mListOfBufferInstance, pred, foundList);
	}

	inline void searchBufferInstanceByQualifiedNameID(
			const std::string & aQualifiedNameID, BFList & foundList) const
	{
		SymbolPredicateByQualifiedNameID pred(aQualifiedNameID);

		searchCompiledElement(mListOfBufferInstance, pred, foundList);
	}

	const Symbol & searchBufferInstance(ExecutableForm * anExecutable,
			const ObjectElement * objElement) const;

	const Symbol & searchBufferInstance(ExecutableForm * anExecutable,
			const std::string & aFullyQualifiedNameID);

	const Symbol & searchBufferInstanceByQualifiedNameID(
			ExecutableForm * anExecutable,
			const std::string & aQualifiedNameID) const;

	const Symbol & searchBufferInstanceByNameID(
			ExecutableForm * anExecutable, const std::string & aNameID) const;

	const Symbol & searchBufferInstanceAlias(ExecutableForm * anExecutable,
			const std::string & aFullyQualifiedNameID);


	const Symbol & createBufferInstanceAlias(ExecutableForm * anExecutable,
			const std::string & aFullyQualifiedNameID,
			InstanceOfBuffer * anInstance,
			VectorOfInstanceOfMachine & theInstanceOfMachinePath);

	/**
	 ***************************************************************************
	 * GETTER / SETTER
	 * theListOfConnectInstance
	 * "SYMBOL TABLE : CONNECT"
	 ***************************************************************************
	 */
	inline void addConnectInstance(const Symbol & anInstance)
	{
		mListOfConnectorInstance.append(anInstance);
	}

	inline const Symbol & searchConnectorInstance(
			const std::string & aFullyQualifiedNameID) const
	{
		SymbolPredicateByCompiledFQNameID pred(aFullyQualifiedNameID);

		return( searchCompiledElement(mListOfConnectorInstance, pred) );
	}


	inline const Symbol & searchConnectorInstance(
			const ObjectElement * anElement) const
	{
		SymbolPredicateByCompiledElement pred( anElement );

		return( searchCompiledElement(mListOfConnectorInstance, pred) );
	}

	inline void searchConnectorInstanceByNameID(
			const std::string & aNameID, BFList & foundList) const
	{
		SymbolPredicateByNameID pred(aNameID);

		searchCompiledElement(mListOfConnectorInstance, pred, foundList);
	}

	inline void searchConnectorInstanceByQualifiedNameID(
			const std::string & aQualifiedNameID, BFList & foundList) const
	{
		SymbolPredicateByQualifiedNameID pred(aQualifiedNameID);

		searchCompiledElement(mListOfConnectorInstance, pred, foundList);
	}


	const Symbol & searchConnectorInstance(ExecutableForm * anExecutable,
			const ObjectElement * objElement) const;

	const Symbol & searchConnectorInstance(ExecutableForm * anExecutable,
			const std::string & aFullyQualifiedNameID) const;

	const Symbol & searchConnectorInstanceByQualifiedNameID(
			ExecutableForm * anExecutable,
			const std::string & aQualifiedNameID) const;

	const Symbol & searchConnectorInstanceByNameID(
			ExecutableForm * anExecutable, const std::string & aNameID) const;



	/**
	 ***************************************************************************
	 * GETTER / SETTER
	 * mListOfDataInstance
	 * "SYMBOL TABLE : DATA"
	 ***************************************************************************
	 */
	inline void addDataInstance(const Symbol & anInstance)
	{
		mListOfDataInstance.append(anInstance);
	}

	inline void searchDataInstanceByNameID(
			const std::string & aNameID, BFList & foundList) const
	{
		SymbolPredicateByNameID pred(aNameID);

		searchCompiledElement(mListOfDataInstance, pred, foundList);
	}

	inline void searchDataInstanceByQualifiedNameID(
			const std::string & aQualifiedNameID, BFList & foundList) const
	{
		SymbolPredicateByQualifiedNameID pred(aQualifiedNameID);

		searchCompiledElement(mListOfDataInstance, pred, foundList);
	}

	/**
	 ***************************************************************************
	 * GETTER / SETTER
	 * mListOfMachineExecutable
	 * "SYMBOL TABLE : MACHINE EXECUTABLE"
	 ***************************************************************************
	 */
	inline void addMachineExecutable(const BF & anExecutable)
	{
		mListOfMachineExecutable.append( anExecutable );
	}

	/**
	 ***************************************************************************
	 * GETTER / SETTER
	 * mListOfAvmTransition
	 * "SYMBOL TABLE : AVM PROGRAM"
	 ***************************************************************************
	 */
	inline void addTransition(const BF & aTransition)
	{
		mListOfAvmTransition.append( aTransition );
	}

	inline const BF & searchTransition(const ObjectElement * anElement) const
	{
		SymbolPredicateByCompiledElement pred( anElement );

		return( searchCompiledElement(mListOfAvmTransition, pred) );
	}

	inline const BF & searchTransition(
			const std::string & aFullyQualifiedNameID) const
	{
		SymbolPredicateByCompiledFQNameID pred(aFullyQualifiedNameID);

		return( searchCompiledElement(mListOfAvmTransition, pred) );
	}

	inline const BF & searchTransitionByNameID(const std::string & aNameID) const
	{
		SymbolPredicateByNameID pred(aNameID);

		return( searchCompiledElement(mListOfAvmTransition, pred) );
	}


	/**
	 ***************************************************************************
	 * GETTER / SETTER
	 * mListOfAvmProgram
	 * "SYMBOL TABLE : AVM PROGRAM"
	 ***************************************************************************
	 */
	inline void addProgram(const BF & aProgram)
	{
		mListOfAvmProgram.append( aProgram );
	}

	inline const BF & searchProgram(const ObjectElement * anElement) const
	{
		SymbolPredicateByCompiledElement pred( anElement );

		return( searchCompiledElement(mListOfAvmProgram, pred) );
	}

	inline const BF & searchProgram(
			const std::string & aFullyQualifiedNameID) const
	{
		SymbolPredicateByCompiledFQNameID pred(aFullyQualifiedNameID);

		return( searchCompiledElement(mListOfAvmProgram, pred) );
	}

	inline const BF & searchProgramByNameID(const std::string & aNameID) const
	{
		SymbolPredicateByNameID pred(aNameID);

		return( searchCompiledElement(mListOfAvmProgram, pred) );
	}


	/*
	 * GETTER
	 * mErrorCount
	 */
	inline avm_size_t getErrorCount() const
	{
		return( mErrorCount );
	}

	inline bool hasError() const
	{
		return( mErrorCount > 0 );
	}

	inline bool hasZeroError() const
	{
		return( mErrorCount == 0 );
	}

	inline avm_size_t incrErrorCount()
	{
		return( ++mErrorCount );
	}



	/*
	 * GETTER
	 * mWarningCount
	 */
	inline avm_size_t getWarningCount() const
	{
		return( mWarningCount );
	}

	inline bool hasWarning() const
	{
		return( mWarningCount > 0 );
	}

	inline bool hasZeroWarning() const
	{
		return( mWarningCount == 0 );
	}

	inline avm_size_t incrWarningCount()
	{
		return( ++mWarningCount );
	}


	/**
	 * GETTER - SETTER
	 * ERROR_OS
	 */
	inline std::string getErrorMessage() const
	{
		return( ERROR_OS.str() );
	}

	inline bool hasErrorMessage() const
	{
		return( ! (ERROR_OS.str().empty()) );
	}


	inline void addErrorMessage(const std::string & anErrorMessage)
	{
		if( hasErrorMessage() )
		{
			ERROR_OS << "\n";
		}
		ERROR_OS << anErrorMessage;
	}


	inline void resetError()
	{
		mErrorCount = 0;

		ERROR_OS.str("");
	}

	inline void setErrorMessage(const std::string & anErrorMessage)
	{
		resetError();
		ERROR_OS << anErrorMessage;
	}


	/**
	 * GETTER - SETTER
	 * WARNING_OS
	 */
	inline std::string getWarningMessage() const
	{
		return( WARNING_OS.str() );
	}

	inline bool hasWarningMessage() const
	{
		return( ! (WARNING_OS.str().empty()) );
	}


	inline void addWarningMessage(const std::string & anWarningMessage)
	{
		if( hasWarningMessage() )
		{
			WARNING_OS << "\n";
		}
		WARNING_OS << anWarningMessage;
	}


	inline void resetWarning()
	{
		mWarningCount = 0;

		WARNING_OS.str("");
	}

	inline void setWarningMessage(const std::string & anWarningMessage)
	{
		resetWarning();
		WARNING_OS << anWarningMessage;
	}

};


}

#endif /* BUILDER_COMPILER_SYMBOLTABLE_H_ */

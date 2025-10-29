/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 sept. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BUILDER_COMPILER_BASECOMPILERTABLE_H_
#define BUILDER_COMPILER_BASECOMPILERTABLE_H_

#include <common/AvmObject.h>

#include <builder/compiler/SymbolTable.h>


namespace sep
{


class BaseCompilerTable : public AvmObject
{

protected:
	/**
	 * ATTRIBUTE
	 */
	SymbolTable mSymbolTable;

	std::size_t mErrorCount;

	std::size_t mWarningCount;

	StringOutStream ERROR_OS;

	StringOutStream WARNING_OS;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseCompilerTable(Configuration & aConfiguration)
	: AvmObject( ),
	mSymbolTable( aConfiguration ),
	mErrorCount( 0 ),
	mWarningCount( 0 ),
	ERROR_OS( ),
	WARNING_OS( )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BaseCompilerTable(const BaseCompilerTable & aCompilerTable)
	: AvmObject( aCompilerTable ),
	mSymbolTable( aCompilerTable.mSymbolTable ),
	mErrorCount( aCompilerTable.mErrorCount ),
	mWarningCount( aCompilerTable.mWarningCount ),
	ERROR_OS(),
	WARNING_OS()
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseCompilerTable()
	{
		//!! NOTHING
	}


	/*
	 * GETTER
	 * mSymbolTable
	 */
	inline SymbolTable & getSymbolTable()
	{
		return( mSymbolTable );
	}


	/*
	 * GETTER
	 * mErrorCount
	 */
	inline std::size_t getErrorCount() const
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

	inline std::size_t incrErrorCount()
	{
		return( ++mErrorCount );
	}

	inline void resetErrorCount()
	{
		mErrorCount = 0;
	}


	/*
	 * GETTER
	 * mWarningCount
	 */
	inline std::size_t getWarningCount() const
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

	inline std::size_t incrWarningCount()
	{
		return( ++mWarningCount );
	}

	inline void resetWarningCount()
	{
		mWarningCount = 0;
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
		WARNING_OS.str("");
	}

	inline void setWarningMessage(const std::string & anWarningMessage)
	{
		resetWarning();
		WARNING_OS << anWarningMessage;
	}


	/**
	 * REPORT
	 */
	void reportCompilation(OutStream & os) const
	{
		os << _SEW_ << "Compilation report:> " << mErrorCount
			<< " error" << ((mErrorCount > 1)? "s " : " ")
			<< mWarningCount << " warning"
			<< ((mWarningCount > 1)? "s" : "") << EOL_FLUSH;
	}

	inline void resetErrorWarning()
	{
		resetError();
		resetErrorCount();

		resetWarningCount();
		resetWarning();
	}

};


}

#endif /* BUILDER_COMPILER_BASECOMPILERTABLE_H_ */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 sept. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BUILDER_COMPILER_SYMBOLPREDICATE_H_
#define BUILDER_COMPILER_SYMBOLPREDICATE_H_

#include <fml/executable/BaseCompiledForm.h>

#include <fml/symbol/Symbol.h>


namespace sep
{


class SymbolPredicate
{
public:
	/**
	 * CONSTRUCTOR / DESTRUCTOR
	 */
	SymbolPredicate()
	{
		//!! NOTHING
	}

	virtual ~SymbolPredicate()
	{
		//!! NOTHING
	}

	/**
	 * OPERATOR API
	 */
	virtual bool operator() (const BaseCompiledForm * aSymbol) const = 0;

	virtual bool operator() (const Symbol & aSymbol) const = 0;

};




class SymbolPredicateByQualifiedNameID  :  public SymbolPredicate
{

public:
	/**
	 * ATTRIBUTE
	 */
	std::string mQualifiedNameID;

	/**
	 * CONSTRUCTOR / DESTRUCTOR
	 *
	 */
	SymbolPredicateByQualifiedNameID(const std::string & aQualifiedNameID)
	: SymbolPredicate( ),
	mQualifiedNameID( aQualifiedNameID )
	{
		//!! NOTHING
	}

	virtual ~SymbolPredicateByQualifiedNameID()
	{
		//!! NOTHING
	}

	/**
	 * OPERATOR
	 */
	inline virtual bool operator() (const BaseCompiledForm * aSymbol) const
	{
		return( aSymbol->fqnEndsWith(mQualifiedNameID) );
	}

	inline virtual bool operator() (const Symbol & aSymbol) const
	{
		return( aSymbol.fqnEndsWith(mQualifiedNameID) );
	}

};



class SymbolPredicateByNameID  :  public SymbolPredicateByQualifiedNameID
{
public:
	/**
	 * CONSTRUCTOR
	 */
	SymbolPredicateByNameID(const std::string & id)
	: SymbolPredicateByQualifiedNameID( id )
	{
		//!! NOTHING
	}

	/**
	 * OPERATOR
	 */
	inline virtual bool operator() (const BaseCompiledForm * aSymbol) const
	{
		return( aSymbol->getNameID() == mQualifiedNameID );
	}

	inline virtual bool operator() (const Symbol & aSymbol) const
	{
		return( aSymbol.getNameID() == mQualifiedNameID );
	}

};


class SymbolPredicateByCompiledFQNameID  :
		public SymbolPredicateByQualifiedNameID
{
public:
	/**
	 * CONSTRUCTOR
	 */
	SymbolPredicateByCompiledFQNameID(
			const std::string & aFullyQualifiedNameID)
	: SymbolPredicateByQualifiedNameID( aFullyQualifiedNameID )
	{
		//!! NOTHING
	}

	/**
	 * OPERATOR
	 */
	inline virtual bool operator() (const BaseCompiledForm * aSymbol) const
	{
		return( aSymbol->getAstFullyQualifiedNameID() == mQualifiedNameID );
	}

	inline virtual bool operator() (const Symbol & aSymbol) const
	{
		return( aSymbol.getAstFullyQualifiedNameID() == mQualifiedNameID );
	}

};



class SymbolPredicateByCompiledElement  :  public SymbolPredicate
{

protected:
	/**
	 * ATTRIBUTE
	 */
	const ObjectElement * mElement;

public:
	SymbolPredicateByCompiledElement(const ObjectElement * anElement)
	: SymbolPredicate( ),
	  mElement(anElement)
	{
		//!! NOTHING
	}
	virtual ~SymbolPredicateByCompiledElement()
	{
		//!! NOTHING
	}

	/**
	 * OPERATOR
	 */
	inline virtual bool operator() (const BaseCompiledForm * aSymbol) const
	{
		return( aSymbol->isAstElement( mElement ) );
	}

	inline virtual bool operator() (const Symbol & aSymbol) const
	{
		return( aSymbol.isAstElement( mElement ) );
	}

};


} /* namespace sep */
#endif /* BUILDER_COMPILER_SYMBOLPREDICATE_H_ */

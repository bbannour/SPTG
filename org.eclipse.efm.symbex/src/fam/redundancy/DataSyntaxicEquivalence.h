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
#ifndef DataSyntaxicEquivalence_H_
#define DataSyntaxicEquivalence_H_

#include "BaseDataComparator.h"


namespace sep
{

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// DATA SYNTAXIC EQUIVALENCE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class DataSyntaxicEquivalence : public BaseDataComparator
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	DataSyntaxicEquivalence(Configuration & aConfiguration)
	: BaseDataComparator( aConfiguration )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~DataSyntaxicEquivalence()
	{
		//!! NOTHING
	}


	/*
	 * COMPARE
	 */
	virtual bool compareMESSAGE(
			const Message & newMsg, const Message & oldMsg);

	virtual bool compareDATA(
			const ExecutionContext & newEC, const ExecutionContext & oldEC);

	/**
	 * strComparer
	 */
	inline virtual std::string strComparer() const
	{
		return( "=s= i.e. SEQ" );
	}

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// DATA ALPHA EQUIVALENCE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class DataAlphaEquivalence : public BaseDataComparator
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	DataAlphaEquivalence(Configuration & aConfiguration)
	: BaseDataComparator( aConfiguration )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~DataAlphaEquivalence()
	{
		//!! NOTHING
	}


	/*
	 * COMPARE
	 */
	virtual bool compareDATA(
			const ExecutionContext & newEC, const ExecutionContext & oldEC);

	/**
	 * strComparer
	 */
	inline virtual std::string strComparer() const
	{
		return( "=a= i.e. AEQ" );
	}

};


}

#endif /*DataSyntaxicEquivalence_H_*/

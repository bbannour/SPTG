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

#ifndef MAIN_LAUNCHER_H_
#define MAIN_LAUNCHER_H_

#include <util/avm_util.h>

#include <sew/Workflow.h>


namespace sep
{


class AvmLauncher
{

protected :
	/**
	 * ATTRIBUTES
	 */
	avm_size_t mArgNumber;
	char * *   mArgument;

	Workflow mWorkflow;


public :
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmLauncher( avm_size_t argc , char * argv[] )
	: mArgNumber( argc ),
	mArgument( argv ),
	mWorkflow( SYMBEX_BUILD_ID )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmLauncher()
	{
		//!! NOTHING
	}


	/**
	 * LOADER - DISPOSER
	 */
	bool load();
	void dispose();


	/*METHODS*/
	static void copyright();
	static void usage();

	void start();


	/*ATTRIBUTES*/
//	static const unsigned    SUBVERSION_REVISION_NUMBER;
//	static const std::string SUBVERSION_REVISION_STRING;

	static std::string SYMBEX_SCM_VERSION;
	static std::string SYMBEX_BUILD_ID;

	static std::string SYMBEX_BUILD_INFO;

	/**
	 * GETTER - SETTER
	 * mArgument
	 */
	inline avm_size_t getArgNumber()
	{
		return( mArgNumber );
	}

	inline char * getArgument(avm_size_t index)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( index , mArgNumber ) << SEND_EXIT;

		return( mArgument[index] );
	}

	/**
	 * run
	 */
	static int run( int argc , char * argv[] );

};


} /* namespace sep */

#endif /* MAIN_LAUNCHER_H_ */

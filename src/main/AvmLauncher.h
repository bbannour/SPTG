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
#include <sew/WorkflowParameter.h>


namespace sep
{


class AvmLauncher
{

protected :
	/**
	 * ATTRIBUTES
	 */
	std::size_t mArgNumber;
	char * *   mArgument;

	WorkflowParameter mWorkflowParameter;

	Workflow mWorkflow;


public :
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmLauncher( std::size_t argc , char * argv[] )
	: mArgNumber( argc ),
	mArgument( argv ),
	mWorkflowParameter( SYMBEX_BUILD_ID ),
	mWorkflow( nullptr )
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
	static void help();
	static void usage();

	void start();


	/*ATTRIBUTES*/
	static std::string SYMBEX_BUILD_ID;

	/**
	 * GETTER - SETTER
	 * mArgument
	 */
	inline std::size_t getArgNumber()
	{
		return( mArgNumber );
	}

	inline char * getArgument(std::size_t index)
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

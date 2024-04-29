/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 25 juil. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "MachineDependency.h"

#include <common/BF.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableSystem.h>

#include <fml/expression/AvmCode.h>


namespace sep
{

bool MachineDependency::computeVariableDependency(
		const ExecutableSystem & anExecSystem)
{
	const TableOfExecutableForm & executables = anExecSystem.getExecutables();

	TableOfExecutableForm::const_raw_iterator itExec = executables.begin();
	TableOfExecutableForm::const_raw_iterator endExec = executables.end();
	for( ; itExec != endExec ; ++itExec )
	{
		if( not computeVariableDependency( itExec ) )
		{
			return( false );
		}
	}

	return( true );
}



bool MachineDependency::computeVariableDependency(
		const ExecutableForm & anExecutable)
{
	std::size_t endOffset = anExecutable.getTransition().size();
	for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
	{
		if( not computeVariableDependency( anExecutable.rawTransition(offset) ) )
		{
			return( false );
		}
	}

	endOffset = anExecutable.getProgram().size();
	for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
	{
		if( not computeVariableDependency( anExecutable.rawProgram(offset) ) )
		{
			return( false );
		}
	}

	return( true );
}


bool MachineDependency::isVariableDependency(
		const ExecutableForm & anExecutable, AvmCode * aCode)
{
	return( false );
}

bool MachineDependency::isVariableDependency(
		const ExecutableForm & anExecutable, const BF & aVar)
{
	return( false );
}



bool MachineDependency::computeVariableDependency(AvmProgram * aProgram)
{
	return( false );
}

bool MachineDependency::isVariableDependency(
		AvmProgram * aProgram, AvmCode * aCode)
{
	return( false );
}

bool MachineDependency::isVariableDependency(
		AvmProgram * aProgram, const BF & aVar)
{
	return( false );
}



bool MachineDependency::computeVariableDependency(AvmLambda * aLambda)
{
	return( false );
}

bool MachineDependency::isVariableDependency(
		AvmLambda * aLambda, AvmCode * aCode)
{
	return( false );
}

bool MachineDependency::isVariableDependency(
		AvmLambda * aLambda, const BF & aVar)
{
	return( false );
}



} /* namespace sep */

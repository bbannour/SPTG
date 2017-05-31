/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 17 déc. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "avm_assert.h"

#include <util/avm_debug.h>
#include <util/avm_vfs.h>


namespace sep
{

/**
 *
 */
void AvmExitException::prologue()
{
	OS << EMPHASIS( mDescription , '>' , 80 );
//		OS << TAB << "<" << mDescription << "> ";

AVM_IF_DEBUG_ENABLED_AND( not mSourcePath.empty() )
	OS << TAB << "in " << VFS::wrapPath(mSourcePath,
			80 - OS.INDENT.tabSize() - 6 - ( (mLine > 0) ? 12 : 0 ), "...");
	// with 10 for size(TAB + "in " + "..." + ", line: " + mLine)
	if( mLine > 0 )
	{
		OS << ", line: " << mLine;
	}
	OS << std::endl;
AVM_ENDIF_DEBUG_ENABLED
}

/**
 * ERROR & WARNING
 * COUNT
 */
std::size_t AVM_ERROR_COUNT   = 0;

std::size_t AVM_WARNING_COUNT = 0;


AvmExitException AVM_OS_THROW_EXCEPTION(AVM_EXIT_FAILED_CODE);

AvmExitException AVM_OS_THROW_ALERT(AVM_EXIT_FAILED_CODE);


AvmEXIT_SIGNAL THROW_FATAL_ERROR( AVM_EXIT_FATAL_ERROR_CODE );


} /* namespace sep */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmObject.h"

#include <printer/OutStream.h>

#include <util/avm_debug.h>


namespace sep
{

/**
 * MEMORY MANAGEMENT
 * DESTROY
 */
void DestroyObjectPolicy::destroy(AvmObject * anObject)
{
	if( anObject != nullptr )
	{
		if( anObject->isUnique() )
		{
//			AVM_OS_TRACE << "destroy :> " << anObject->str() << std::endl;

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
	anObject->dbgDestroy();
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )

			delete( anObject );

			anObject = nullptr;
		}

		else if( anObject->getRefCount() == 0 )
		{
//AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
//			const char * classKindName = anObject->classKindName();
//			std::string strForm = "";//anObject->str();
//
//			AVM_OS_COUT << ">>> destroy AvmObject < " << classKindName
//					<< " > @ " << std::addressof(anObject) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//
//			AVM_OS_LOG << ">>> destroy AvmObject < " << classKindName
//					<< " > @ " << std::addressof(anObject) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//
//			AVM_OS_TRACE << ">>> destroy AvmObject < " << classKindName
//					<< " > @ " << std::addressof(anObject) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//_AVM_ELSE_
//			AVM_OS_WARNING_ALERT << ">>> destroy with refCount == 0 !!!"
//					<< SEND_ALERT;

			AVM_OS_COUT << ">>> destroy AvmObject @ "
					<< std::addressof(anObject)
					<< " with refCount == 0 !!!" << std::endl;

			AVM_OS_LOG << ">>> destroy AvmObject @ "
					<< std::addressof(anObject)
					<< " with refCount == 0 !!!" << std::endl;

			AVM_OS_TRACE << "\t>>> destroy AvmObject @ "
					<< std::addressof(anObject)
					<< " with refCount == 0 !!!" << std::endl;

			anObject->toStream(AVM_OS_COUT);
//AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
	anObject->dbgDestroy();
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
		}

		else
		{
			anObject->decrRefCount();
		}
	}
}

}

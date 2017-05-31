/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "SmartPointerUtil.h"

#include <util/avm_debug.h>		// util/avm_debug.h

#include <common/AvmObject.h>	// common/AvmObject.h
#include <common/Element.h>		// common/Element.h

#include <printer/OutStream.h>	// printer/OutStream.h


namespace sep
{


/**
 * MEMORY MANAGEMENT
 * DESTROY
 * FORM
 */
void destroy(AvmObject * anObject)
{
	DestroyObjectPolicy::destroy(anObject);
}


void DestroyObjectPolicy::destroy(AvmObject * anObject)
{
	if( anObject != NULL )
	{
		if( anObject->isUnique() )
		{
//			AVM_OS_TRACE << "destroy :> " << anObject->str() << std::endl;

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
	anObject->dbgDestroy();
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )

			delete( anObject );

			anObject = NULL;
		}

		else if( anObject->getRefCount() == 0 )
		{
//AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
//			const char * classKindName = anObject->classKindName();
//			std::string strForm = "";//anObject->str();
//
//			AVM_OS_COUT << ">>> destroy AvmObject < " << classKindName
//					<< " > @ " << avm_address_t(anObject) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//
//			AVM_OS_LOG << ">>> destroy AvmObject < " << classKindName
//					<< " > @ " << avm_address_t(anObject) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//
//			AVM_OS_TRACE << ">>> destroy AvmObject < " << classKindName
//					<< " > @ " << avm_address_t(anObject) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//_AVM_ELSE_
//			AVM_OS_WARNING_ALERT << ">>> destroy with refCount == 0 !!!"
//					<< SEND_ALERT;

			AVM_OS_COUT << ">>> destroy AvmObject @ "
					<< avm_address_t(anObject)
					<< " with refCount == 0 !!!" << std::endl;

			AVM_OS_LOG << ">>> destroy AvmObject @ "
					<< avm_address_t(anObject)
					<< " with refCount == 0 !!!" << std::endl;

			AVM_OS_TRACE << "\t>>> destroy AvmObject @ "
					<< avm_address_t(anObject)
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



void destroyElement(Element * anElement)
{
	DestroyElementPolicy::destroy(anElement);
}


void DestroyElementPolicy::destroy(Element * anElement)
{
	if( anElement != NULL )
	{
		if( anElement->isUnique() )
		{
//			AVM_OS_TRACE << "destroy :> " << anElement->str() << std::endl;

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
	anElement->dbgDestroy();
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )

			delete( anElement );

			anElement = NULL;
		}

		else if( anElement->getRefCount() == 0 )
		{
//AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
//
//			const char * classKindName = anElement->classKindName();
//			std::string strForm = "";//anElement->str();
//
//			AVM_OS_COUT << ">>> destroy Element < " << classKindName
//					<< " > @ " << avm_address_t(anElement) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//
//			AVM_OS_LOG << ">>> destroy Element < " << classKindName
//					<< " > @ " << avm_address_t(anElement) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//
//			AVM_OS_TRACE << ">>> destroy Element < " << classKindName
//					<< " > @ " << avm_address_t(anElement) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//_AVM_ELSE_
//			AVM_OS_WARNING_ALERT << ">>> destroy with refCount == 0 !!!"
//					<< SEND_ALERT;

			AVM_OS_COUT << ">>> destroy Element @ "
					<< avm_address_t(anElement)
					<< " with refCount == 0 !!!" << std::endl;
			AVM_OS_COUT << "\t>> " << anElement->str() << std::endl;

			AVM_OS_LOG << ">>> destroy Element @ "
					<< avm_address_t(anElement)
					<< " with refCount == 0 !!!" << std::endl;
			AVM_OS_LOG << "\t>> " << anElement->str() << std::endl;

			AVM_OS_TRACE << "\t>>> destroy Element @ "
					<< avm_address_t(anElement)
					<< " with refCount == 0 !!!" << std::endl;
			AVM_OS_TRACE << "\t>> " << anElement->str() << std::endl;

//AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
		}

		else
		{
			anElement->decrRefCount();
		}
	}
}


} /* namespace sep */

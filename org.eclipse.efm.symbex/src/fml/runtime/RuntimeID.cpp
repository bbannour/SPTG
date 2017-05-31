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
#include "RuntimeID.h"

#include <common/NamedElement.h>

#include <fml/common/SpecifierElement.h>

#include <fml/executable/BaseCompiledForm.h>
#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfMachine.h>


namespace sep
{


/**
 * DEFAULT NULL
 */
RuntimeID RuntimeID::REF_NULL;

/**
 * GETTER - SETTER
 * mFullyQualifiedNameID
 */
std::string RuntimeID::getFullyQualifiedNameID() const
{
	return( BaseCompiledForm::USE_ONLY_ID
			? rid_pointer()->getNameID()
			: rid_pointer()->getFullyQualifiedNameID() );
}

void _RuntimeID_::updateFullyQualifiedNameID()
{
	if( (mParent != NULL) && (mInstance != NULL) )
	{
		mNameID = mInstance->getNameID();

		mFullyQualifiedNameID = ( OSS()
				<< mParent->getFullyQualifiedNameID()
				<< '.' << mNameID );

		mQualifiedNameID = ( OSS() << "run::pid#" << mRid << ':'
				<< NamedElement::location(mFullyQualifiedNameID) );
	}
	else if( mInstance != NULL )
	{
		mNameID = mInstance->getNameID();

		std::string aQualifiedNameID = NamedElement::location(
				mInstance->getFullyQualifiedNameID() );

		mFullyQualifiedNameID = "run::" + aQualifiedNameID;

		mQualifiedNameID =
				( OSS() << "run::pid#" << mRid << ':' << aQualifiedNameID );
	}
	else
	{
		mNameID = ( OSS() << "pid#" << mRid );

		mFullyQualifiedNameID =
				mQualifiedNameID = ( OSS() << "run::pid#" << mRid );
	}
}

/**
 * GETTER
 * Executable
 */
ExecutableForm * _RuntimeID_::getExecutable() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mInstance )
			<< " Instance in _RID_ < "
			<< "pid#" << mRid << ":" << getNameID() << " > !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( mInstance->hasExecutable() )
			<< "Unexpected RID without Executable !!!"
			<< SEND_EXIT;

	return( mInstance->getExecutable() );
}


/**
 * initialize
 * finalize
 */
void RuntimeID::initialize()
{
	// Attention:> Reference circulaire (a la destruction)!!!!
	rid_pointer()->onRunning = StatementConstructor::newOptiNopCode(
			OperatorManager::OPERATOR_RUN, *this, AVM_ARG_MACHINE_RID);

	_RuntimeID_ * tmpRID;

	// the first hierarchical composite (contained concurrency spec) container
	if( getExecutable()->isCompositeComponent() )
	{
		rid_pointer()->mCompositeComponent = this->rid_pointer();
	}
	else if( (tmpRID = rid_pointer())->mParent != NULL )
	{
		tmpRID = tmpRID->mParent;
		for( ; (tmpRID != NULL) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->getExecutable()->isCompositeComponent() )
			{
				rid_pointer()->mCompositeComponent = tmpRID;
				break;
			}
		}

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT(
				rid_pointer()->mCompositeComponent )
				<< " as First Composite Parent Component of < "
				<< this->strUniqId() << " > !!!"
				<< SEND_EXIT;
	}

	// the first  composite parent of the first composite container
	if( rid_pointer()->mCompositeComponent != NULL )
	{
		rid_pointer()->mCompositeComponentParent =
				tmpRID = rid_pointer()->mCompositeComponent;

		if( tmpRID->mParent != NULL )
		{
			for( tmpRID = tmpRID->mParent ;
					(tmpRID != NULL) ; tmpRID = tmpRID->mParent )
			{
				if( tmpRID->getExecutable()->isCompositeComponent() )
				{
					rid_pointer()->mCompositeComponentParent = tmpRID;
					break;
				}
			}
		}
	}


	// the first (or this) Communicator container of this
	if( getExecutable()->isCommunicator() )
	{
		rid_pointer()->mCommunicator = this->rid_pointer();
	}
	else if( (tmpRID = rid_pointer())->mParent != NULL )
	{
		for( tmpRID = tmpRID->mParent ;
				(tmpRID != NULL) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->getExecutable()->isCommunicator() )
			{
				rid_pointer()->mCommunicator = tmpRID;
				break;
			}
		}
	}

	// the first (or this) Lifeline container of this
	if( getExecutable()->isLifeline() )
	{
		rid_pointer()->mLifeline = this->rid_pointer();
	}
	else if( (tmpRID = rid_pointer())->mParent != NULL )
	{
		for( tmpRID = tmpRID->mParent ;
				(tmpRID != NULL) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->getExecutable()->isLifeline() )
			{
				rid_pointer()->mLifeline = tmpRID;
				break;
			}
		}

		if( rid_pointer()->mLifeline == NULL )
		{
			rid_pointer()->mLifeline = rid_pointer()->mCommunicator;
		}
	}


	// the first hierarchical main Component container
	if( getExecutable()->isMainComponent() )
	{
		rid_pointer()->mComponentSelf = this->rid_pointer();
	}
	else if( (tmpRID = rid_pointer())->mParent != NULL )
	{
		tmpRID = tmpRID->mParent;
		for( ; (tmpRID != NULL) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->getExecutable()->isMainComponent() )
			{
				rid_pointer()->mComponentSelf = tmpRID;
				break;
			}
		}

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT(
				rid_pointer()->mCompositeComponent )
				<< " as Component Self of < " << this->strUniqId() << " > !!!"
				<< SEND_EXIT;
	}

	// the main Component container of mComponentSelf
	if( (rid_pointer()->mComponentSelf != NULL)
		&& ((tmpRID = rid_pointer()->mComponentSelf)->mParent != NULL) )
	{
		for( tmpRID = tmpRID->mParent ;
				(tmpRID != NULL) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->getExecutable()->isMainComponent() )
			{
				rid_pointer()->mComponentParent = tmpRID;
				break;
			}
		}
	}

	// the first (or this) main Component Communicator container of this
	if( getExecutable()->isMainComponent() && getExecutable()->hasPort() )
	{
		rid_pointer()->mComponentCommunicator = this->rid_pointer();
	}
	else if( (tmpRID = rid_pointer())->mParent != NULL )
	{
		for( tmpRID = tmpRID->mParent ;
				(tmpRID != NULL) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->getExecutable()->isMainComponent() &&
					tmpRID->getExecutable()->hasPort() )
			{
				rid_pointer()->mComponentCommunicator = tmpRID;
				break;
			}
		}
	}
}


/**
 * GETTER  API
 * Specifier
 */
const Specifier & RuntimeID::getSpecifier() const
{
	return( getExecutable()->getSpecifier() );
}


/**
 * GETTER - SETTER
 * mInstance
 * son Executable
 * ses variables
 */
// Model Machine
const InstanceOfMachine * RuntimeID::getModelInstance() const
{
	return( rid_pointer()->mInstance->getInstanceModel() );
}

bool RuntimeID::hasModelInstance() const
{
	return( (rid_pointer()->mInstance != NULL) &&
			rid_pointer()->mInstance->hasInstanceModel() );
}


// Executable
ExecutableForm * RuntimeID::getExecutable() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( rid_pointer()->mInstance )
			<< " Instance in RID < " << this->strUniqId() << " > !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT(
			rid_pointer()->mInstance->hasExecutable() )
			<< "Unexpected RID without Executable !!!"
			<< SEND_EXIT;

	return( getInstance()->getExecutable() );
}

bool RuntimeID::hasExecutable() const
{
	return( hasInstance() && getInstance()->hasExecutable() );
}


// Variable
const BF & RuntimeID::getVariable(avm_offset_t offset) const
{
	return( getExecutable()->getData().get(offset) );
}

InstanceOfData * RuntimeID::rawVariable(avm_offset_t offset) const
{
	return( getExecutable()->getData().rawAt(offset) );
}


bool RuntimeID::hasVariable() const
{
	return( getExecutable()->hasData() );
}


/**
 * GETTER - SETTER
 * Instance->mOnCreate
 */
const BFCode & RuntimeID::getOnCreate() const
{
	return( getInstance()->getOnCreate() );
}

bool RuntimeID::hasOnCreate() const
{
	return( getInstance()->hasOnCreate() );
}

/**
 * GETTER - SETTER
 * Instance->mOnInit
 */
const BFCode & RuntimeID::getOnStart() const
{
	return( getInstance()->getOnStart() );
}

bool RuntimeID::hasOnStart() const
{
	return( getInstance()->hasOnStart() );
}


/**
 * GETTER - SETTER
 * Ancestor
 */
bool RuntimeID::hasAsAncestor(const RuntimeID & aRID) const
{
	_RuntimeID_ * aPossibleAncestor = aRID.rid_pointer();

	_RuntimeID_ * tmpRID = rid_pointer();
	for( ; (tmpRID != NULL) ; tmpRID = tmpRID->mParent )
	{
		if( (tmpRID == aPossibleAncestor) )
		{
			return( true );
		}
	}

	return( false );
}

bool RuntimeID::hasAsAncestor(const InstanceOfMachine * anInstance) const
{
	ExecutableForm * aPossibleExecutableAncestor = anInstance->getExecutable();

	_RuntimeID_ * tmpRID = rid_pointer();
	for( ; (tmpRID != NULL) ; tmpRID = tmpRID->mParent )
	{
		if( (tmpRID->mInstance == anInstance)
			|| (anInstance->getSpecifier().hasDesignModel()
				&& (tmpRID->getExecutable() == aPossibleExecutableAncestor) ) )
		{
			return( true );
		}
	}

	return( false );
}

RuntimeID RuntimeID::getAncestorContaining(
		const BaseInstanceForm * anInstance) const
{
	BaseAvmProgram * aPossibleExecutableAncestor = anInstance->getContainer();

	_RuntimeID_ * tmpRID = rid_pointer();
	for( ; (tmpRID != NULL) ; tmpRID = tmpRID->mParent )
	{
		if( tmpRID->getExecutable() == aPossibleExecutableAncestor )
		{
			return( smartPointerOf( tmpRID ) );
		}
	}

	return( RuntimeID::REF_NULL );
}


/**
 * GETTER - SETTER
 * the Lifeline Ancestor container
 */
RuntimeID RuntimeID::getLifeline(InstanceOfMachine * aMachine) const
{
	_RuntimeID_ * tmpRID = rid_pointer();
	for( ; (tmpRID != NULL) ; tmpRID = tmpRID->mParent )
	{
		if( tmpRID->getExecutable() == aMachine->getContainer() )
		{
			return( smartPointerOf( tmpRID->mLifeline ) );
		}
	}

	return( RuntimeID::REF_NULL );
}


RuntimeID RuntimeID::getLifeline(InstanceOfPort * aPort) const
{
	if( aPort->hasAliasTarget() )
	{
		aPort = aPort->getAliasTarget()->as< InstanceOfPort >();
	}

	_RuntimeID_ * tmpRID = rid_pointer();
	for( ; (tmpRID != NULL) ; tmpRID = tmpRID->mParent )
	{
		if( (tmpRID->getExecutable() == aPort->getContainer())
			|| tmpRID->getExecutable()->getPort().contains(aPort) )
		{
			return( smartPointerOf( tmpRID->mLifeline ) );
		}
	}

	return( RuntimeID::REF_NULL );
}


/**
 * GETTER - SETTER
 * the Communicator Ancestor container
 */
RuntimeID RuntimeID::getCommunicator(InstanceOfMachine * aMachine) const
{
	_RuntimeID_ * tmpRID = rid_pointer();
	for( ; (tmpRID != NULL) ; tmpRID = tmpRID->mParent )
	{
		if( tmpRID->getExecutable() == aMachine->getContainer() )
		{
			return( smartPointerOf( tmpRID->mCommunicator ) );
		}
	}

	return( RuntimeID::REF_NULL );
}


RuntimeID RuntimeID::getCommunicator(InstanceOfPort * aPort) const
{
	if( aPort->hasAliasTarget() )
	{
		aPort = aPort->getAliasTarget()->as< InstanceOfPort >();
	}

	_RuntimeID_ * tmpRID = rid_pointer();
	for( ; (tmpRID != NULL) ; tmpRID = tmpRID->mParent )
	{
		if( (tmpRID->getExecutable() == aPort->getContainer())
			|| tmpRID->getExecutable()->isCommunicatorWith(aPort) )
		{
			return( smartPointerOf( tmpRID->mCommunicator ) );
		}
	}

	return( RuntimeID::REF_NULL );
}



/**
 * Serialization
 */
void _RuntimeID_::toStream(OutStream & os) const
{
	if( os.preferablyFQN() )
	{
		os << TAB << mQualifiedNameID;

		return;
	}

//
//	os << TAB << "rid " << getFullyQualifiedNameID() << " {" << EOL;
//
//	os << TAB2 << "rid = " << getRid() << ";" << EOL;
//	os << TAB2 << "prid = " << getPRid() << ";" << EOL;
//	os << TAB2 << "offset = " << getOffset() << ";" << EOL;
//	os << TAB2 << "instance = "
//			<< getInstance()->getFullyQualifiedNameID() << ";" << EOL;
//
//	os << TAB << "}" << EOL;

	os << TAB << "rid< offset:" << mOffset
			<< ( mDynamicLoaded ? " , dyna:true" : "" ) << " > "
//			<< "@" << avm_address_t( this ) << "  "
			<< getFullyQualifiedNameID() << " {" << EOL_TAB2;

	os <<   "this = "        << std::setw(3) << mRid << ";";
	os << "  this#parent = " << std::setw(3) << mRidOf( mParent ) << ";";
	os << "  this#lifeline = "   << mRidOf( mLifeline ) << ";";
	os << "  cthis#com = "   << mRidOf( mCommunicator ) << ";";

	os << EOL_TAB2;

	os <<   "self = " << std::setw(3) << mRidOf( mComponentSelf ) << ";";
	os << "  self#parent = " << std::setw(3)
			<< mRidOf( mComponentParent ) << ";";
	os << "  cself#com = " << mRidOf( mComponentCommunicator ) << ";";

	os << EOL_TAB2;

	os << "this#composite = " << mRidOf( mCompositeComponent ) << ";";
	os << "  this#composite#parent = "
			<< mRidOf( mCompositeComponentParent ) << ";";

	os << EOL;

//	os << TAB2 << "fqn = "  << mFullyQualifiedNameID << ";" << EOL;

	os << TAB2 << "instance = "
			<< mInstance->getFullyQualifiedNameID() << ";" << EOL;

	if( onRunning.valid() )
	{
		os << TAB2 << "@running{ " << onRunning.str() << " }" << EOL;
	}

	os << TAB << "}" << EOL_FLUSH;
}


}

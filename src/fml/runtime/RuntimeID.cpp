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

#include <fml/common/ObjectElement.h>
#include <fml/common/SpecifierElement.h>

#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfMachine.h>


namespace sep
{

/**
* GLOBALS
* BASE NAME PREFIX
*/
std::string RuntimeID::NAME_ID_SEPARATOR = "#";

std::string RuntimeID::BASENAME_PREFIX  = "pid";

std::string RuntimeID::BASENAME = "pid";


std::string RuntimeID::BASENAME_PARENT_PREFIX = "ppid";

std::string RuntimeID::BASENAME_PARENT = "ppid";

/**
 * GETTER - SETTER
 * mFullyQualifiedNameID
 */
std::string RuntimeID::getFullyQualifiedNameID() const
{
AVM_IF_DEBUG_FLAG( QUALIFIED_NAME_ID )

		return( rid_pointer()->getFullyQualifiedNameID() );

AVM_ELSE

		return( ObjectElement::USE_ONLY_ID
				? rid_pointer()->getNameID()
				: rid_pointer()->getFullyQualifiedNameID() );

AVM_ENDIF_DEBUG_FLAG( QUALIFIED_NAME_ID )
}

void _RuntimeID_::updateFullyQualifiedNameID()
{
	if( (mParent != nullptr) && (mInstance != nullptr) )
	{
		mNameID = mInstance->getNameID();

		mFullyQualifiedNameID = ( OSS()
				<< mParent->getFullyQualifiedNameID()
				<< '.' << mNameID );

		mQualifiedNameID = ( OSS() << "run::" << RuntimeID::BASENAME
							<< mRid << ':' << getLocationID() );
	}
	else if( mInstance != nullptr )
	{
		mNameID = mInstance->getNameID();

		std::string aQualifiedNameID = mInstance->getLocationID();

		mFullyQualifiedNameID = "run::" + aQualifiedNameID;

		mQualifiedNameID = ( OSS() << "run::"
				<< RuntimeID::BASENAME << mRid << ':' << aQualifiedNameID );
	}
	else
	{
		mNameID = ( OSS() << RuntimeID::BASENAME << mRid );

		mFullyQualifiedNameID = mQualifiedNameID =
				( OSS() << "run::" << RuntimeID::BASENAME << mRid );
	}
}

/**
 * GETTER
 * Executable
 */
ExecutableForm & _RuntimeID_::refExecutable() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mInstance )
			<< " Instance in _RID_ < "
			<< RuntimeID::BASENAME << mRid << ":" << getNameID() << " > !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( mInstance->hasExecutable() )
			<< "Unexpected RID without Executable !!!"
			<< SEND_EXIT;

	return( mInstance->refExecutable() );
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
	if( refExecutable().isCompositeComponent() )
	{
		rid_pointer()->mCompositeComponent = this->rid_pointer();
	}
	else if( (tmpRID = rid_pointer())->mParent != nullptr )
	{
		tmpRID = tmpRID->mParent;
		for( ; (tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->refExecutable().isCompositeComponent() )
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
	if( rid_pointer()->mCompositeComponent != nullptr )
	{
		rid_pointer()->mCompositeComponentParent =
				tmpRID = rid_pointer()->mCompositeComponent;

		if( tmpRID->mParent != nullptr )
		{
			for( tmpRID = tmpRID->mParent ;
					(tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
			{
				if( tmpRID->refExecutable().isCompositeComponent() )
				{
					rid_pointer()->mCompositeComponentParent = tmpRID;
					break;
				}
			}
		}
	}


	// the first (or this) Communicator container of this
	if( refExecutable().isCommunicator() )
	{
		rid_pointer()->mCommunicator = this->rid_pointer();
	}
	else if( (tmpRID = rid_pointer())->mParent != nullptr )
	{
		for( tmpRID = tmpRID->mParent ;
				(tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->refExecutable().isCommunicator() )
			{
				rid_pointer()->mCommunicator = tmpRID;
				break;
			}
		}
	}


	// the first (or this) Lifeline container of this
	if( refExecutable().isLifeline()
		|| refExecutable().getSpecifier().isComponentSystem())
	{
		rid_pointer()->mLifeline = this->rid_pointer();
	}
	else if( (tmpRID = rid_pointer())->mParent != nullptr )
	{
		_RuntimeID_ * aWeakLifeline =
				rid_pointer()->refExecutable().isWeakLifeline()
				? rid_pointer() : nullptr;

		for( tmpRID = tmpRID->mParent ;
				(tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->refExecutable().isLifeline() )
			{
				rid_pointer()->mLifeline = tmpRID;
				break;
			}
			else if( tmpRID->refExecutable().isWeakLifeline()
					&& (aWeakLifeline == nullptr) )
			{
				aWeakLifeline = tmpRID;
			}
			else if( (tmpRID->mParent != nullptr)
					&& (aWeakLifeline == nullptr)
					&& tmpRID->mParent->refExecutable()
							.getSpecifier().isComponentSystem() )
			{
				rid_pointer()->mLifeline =
					refExecutable().isCommunicator() ? rid_pointer() : tmpRID;
			}
			else if( tmpRID->refExecutable().getSpecifier().isComponentSystem() )
			{
				aWeakLifeline = tmpRID;
				break;
			}
		}

		if( rid_pointer()->mLifeline == nullptr )
		{
			rid_pointer()->mLifeline = (aWeakLifeline == nullptr) ?
					rid_pointer()->mCommunicator : aWeakLifeline;
		}
	}


	// the first hierarchical main Component container
	if( refExecutable().isMainComponent() )
	{
		rid_pointer()->mComponentSelf = this->rid_pointer();
	}
	else if( (tmpRID = rid_pointer())->mParent != nullptr )
	{
		tmpRID = tmpRID->mParent;
		for( ; (tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->refExecutable().isMainComponent() )
			{
				rid_pointer()->mComponentSelf = tmpRID;
				break;
			}
		}

		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT(
				rid_pointer()->mComponentSelf )
				<< " as Component Self of < " << this->strUniqId() << " > !!!"
				<< SEND_EXIT;
	}

	// the main Component container of mComponentSelf
	if( (rid_pointer()->mComponentSelf != nullptr)
		&& ((tmpRID = rid_pointer()->mComponentSelf)->mParent != nullptr) )
	{
		for( tmpRID = tmpRID->mParent ;
				(tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->refExecutable().isMainComponent() )
			{
				rid_pointer()->mComponentParent = tmpRID;
				break;
			}
		}
	}

	// the first (or this) main Component Communicator container of this
	if( refExecutable().isMainComponent() && refExecutable().hasPort() )
	{
		rid_pointer()->mComponentCommunicator = this->rid_pointer();
	}
	else if( (tmpRID = rid_pointer())->mParent != nullptr )
	{
		for( tmpRID = tmpRID->mParent ;
				(tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->refExecutable().isMainComponent() &&
					tmpRID->refExecutable().hasPort() )
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
	return( refExecutable().getSpecifier() );
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
	return( (rid_pointer()->mInstance != nullptr) &&
			rid_pointer()->mInstance->hasInstanceModel() );
}


// Executable
ExecutableForm & RuntimeID::refExecutable() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( rid_pointer()->mInstance )
			<< " Instance in RID < " << this->strUniqId() << " > !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT(
			rid_pointer()->mInstance->hasExecutable() )
			<< "Unexpected RID without Executable !!!"
			<< SEND_EXIT;

	return( getInstance()->refExecutable() );
}

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
	return( refExecutable().getVariables().get(offset) );
}

InstanceOfData * RuntimeID::rawVariable(avm_offset_t offset) const
{
	return( refExecutable().getVariables().rawAt(offset) );
}


bool RuntimeID::hasVariable() const
{
	return( refExecutable().hasVariable() );
}

bool RuntimeID::hasConstVariable() const
{
	return( refExecutable().hasConstVariable() );
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
	for( ; (tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
	{
		if( (tmpRID == aPossibleAncestor) )
		{
			return( true );
		}
	}

	return( false );
}

bool RuntimeID::hasAsAncestor(const InstanceOfMachine & anInstance) const
{
	const ExecutableForm & aPossibleExecutableAncestor =
			anInstance.refExecutable();

	_RuntimeID_ * tmpRID = rid_pointer();
	for( ; (tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
	{
		if( tmpRID->mInstance->isTEQ( anInstance )
			|| (anInstance.getSpecifier().hasDesignModel()
				&& (tmpRID->refExecutable().isTEQ(
						aPossibleExecutableAncestor) )) )
		{
			return( true );
		}
	}

	return( false );
}

RuntimeID RuntimeID::getAncestor(const InstanceOfMachine & anInstance) const
{
	const ExecutableForm & aPossibleExecutableAncestor =
			anInstance.refExecutable();

	_RuntimeID_ * tmpRID = rid_pointer();
	for( ; (tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
	{
		if( tmpRID->mInstance->isTEQ( anInstance )
			|| (anInstance.getSpecifier().hasDesignModel()
				&& tmpRID->refExecutable().isTEQ(
						aPossibleExecutableAncestor) ) )
		{
			return( smartPointerOf( tmpRID ) );
		}
	}

	return( RuntimeID::nullref() );
}


RuntimeID RuntimeID::getAncestorContaining(
		const BaseInstanceForm & anInstance) const
{
	const BaseAvmProgram * aPossibleExecutableAncestor = anInstance.getContainer();

	_RuntimeID_ * tmpRID = rid_pointer();
	for( ; (tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
	{
		if( tmpRID->refExecutable().isTEQ( aPossibleExecutableAncestor ) )
		{
			return( smartPointerOf( tmpRID ) );
		}
	}

	return( RuntimeID::nullref() );
}


/**
 * GETTER - SETTER
 * the Lifeline Ancestor container
 */
RuntimeID RuntimeID::getLifeline(const InstanceOfMachine & aMachine) const
{
	if( hasParent() )
	{
		_RuntimeID_ * tmpRID = rid_pointer();
		for( ; (tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->refExecutable().isTEQ( aMachine.getContainer() ) )
			{
				return( smartPointerOf( tmpRID->mLifeline ) );
			}
		}

		return( RuntimeID::nullref() );
	}

	return( *this );
}


RuntimeID RuntimeID::getLifeline(const InstanceOfPort & aPort) const
{
	if( hasParent() )
	{
		const InstanceOfPort & targetPort = aPort.hasAliasTarget() ?
				aPort.getAliasTarget()->to< InstanceOfPort >() : aPort;

		_RuntimeID_ * tmpRID = rid_pointer();
		for( ; (tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->refExecutable().isTEQ( targetPort.getContainer() )
				|| tmpRID->refExecutable().getPort().contains(& targetPort) )
			{
				return( smartPointerOf( tmpRID->mLifeline ) );
			}
		}

		return( RuntimeID::nullref() );
	}

	return( *this );
}


/**
 * GETTER - SETTER
 * the Communicator Ancestor container
 */
RuntimeID RuntimeID::getCommunicator(const InstanceOfMachine & aMachine) const
{
	if( hasParent() )
	{
		_RuntimeID_ * tmpRID = rid_pointer();
		for( ; (tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->refExecutable().isTEQ( aMachine.getContainer() ) )
			{
				return( smartPointerOf( tmpRID->mCommunicator ) );
			}
		}

		return( RuntimeID::nullref() );
	}

	return( *this );
}


RuntimeID RuntimeID::getCommunicator(const InstanceOfPort & aPort) const
{
	if( hasParent() )
	{
		const InstanceOfPort & targetPort = ( aPort.hasAliasTarget() ?
				aPort.getAliasTarget()->as< InstanceOfPort >() : aPort );

		_RuntimeID_ * tmpRID = rid_pointer();
		for( ; (tmpRID != nullptr) ; tmpRID = tmpRID->mParent )
		{
			if( tmpRID->refExecutable().isTEQ( targetPort.getContainer() )
				|| tmpRID->refExecutable().isCommunicatorWith( targetPort ) )
			{
				return( smartPointerOf( tmpRID->mCommunicator ) );
			}
		}

		return( RuntimeID::nullref() );
	}

	return( *this );
}



/**
 * Serialization
 */
void _RuntimeID_::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << mQualifiedNameID;

		return;
	}


//	out << TAB << "rid " << getFullyQualifiedNameID() << " {" << EOL
//
//		<< TAB2 << "rid = " << getRid() << ";" << EOL
//		<< TAB2 << "prid = " << getPRid() << ";" << EOL
//		<< TAB2 << "offset = " << getOffset() << ";" << EOL
//		<< TAB2 << "instance = "
//		<< getInstance()->getFullyQualifiedNameID() << ";" << EOL
//
//		<< TAB << "}" << EOL;

	out << TAB << "rid< offset:" << mOffset
		<< ( mDynamicLoaded ? " , dyna:true" : "" ) << " > "
//		<< "@" << std::addressof( this ) << "  "
		<< getFullyQualifiedNameID() << " {" << EOL_TAB2

		<<   "this = "        << std::setw(3) << mRid << ";"
		<< "  this#parent = " << std::setw(3) << ridOf( mParent ) << ";"
		<< "  this#lifeline = "   << ridOf( mLifeline ) << ";"
		<< "  cthis#com = "   << ridOf( mCommunicator ) << ";"

		<< EOL_TAB2

		<<   "self = " << std::setw(3) << ridOf( mComponentSelf ) << ";"
		<< "  self#parent = " << std::setw(3)
		<< ridOf( mComponentParent ) << ";"
		<< "  cself#com = " << ridOf( mComponentCommunicator ) << ";"

		<< EOL_TAB2

		<< "this#composite = " << ridOf( mCompositeComponent ) << ";"
		<< "  this#composite#parent = "
		<< ridOf( mCompositeComponentParent ) << ";"

		<< EOL

//		<< TAB2 << "fqn = "  << mFullyQualifiedNameID << ";" << EOL

		<< TAB2 << "instance = "
		<< mInstance->getFullyQualifiedNameID() << ";" << EOL;

	if( onRunning.valid() )
	{
		out << TAB2 << "@running{ " << onRunning.str() << " }" << EOL;
	}

	out << TAB << "}" << EOL_FLUSH;
}


}

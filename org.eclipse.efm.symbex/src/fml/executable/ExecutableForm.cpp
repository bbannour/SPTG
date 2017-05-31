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
#include "ExecutableForm.h"

#include <collection/List.h>

#include <fml/common/SpecifierElement.h>

#include <fml/executable/ExecutableSystem.h>

#include <fml/expression/StatementTypeChecker.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Transition.h>


namespace sep
{


/**
 * SETTER
 * updateFullyQualifiedNameID()
 */
void ExecutableForm::updateFullyQualifiedNameID(
		const std::string & aFullyQualifiedNameID)
{
	std::string::size_type pos =
			aFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);
	if( pos != std::string::npos )
	{
		setFullyQualifiedNameID( "exec" + aFullyQualifiedNameID.substr(pos) );
	}
	else
	{
		setFullyQualifiedNameID( "exec::" + aFullyQualifiedNameID );

		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected UFI without LOCATOR for executable:> "
				<< aFullyQualifiedNameID << " !!!"
				<< SEND_EXIT;
	}

	setNameID( NamedElement::extractNameID( aFullyQualifiedNameID ) );
}



/**
 * GETTER
 * any SYMBOL filtering by an optional type specifier family
 */

#define IF_MUST_BE_MACHINE_SYMBOL  \
		if( (typeFamily == TYPE_MACHINE_SPECIFIER)   ||  \
			(typeFamily == TYPE_UNIVERSAL_SPECIFIER) ||  \
			(typeFamily == TYPE_UNDEFINED_SPECIFIER) )


#define IF_MUST_BE_GENERIC_PORT_SYMBOL  \
		if( (typeFamily == TYPE_PORT_SPECIFIER)      ||  \
			(typeFamily == TYPE_SIGNAL_SPECIFIER)    ||  \
			(typeFamily == TYPE_MESSAGE_SPECIFIER)   ||  \
			(typeFamily == TYPE_UNIVERSAL_SPECIFIER) ||  \
			(typeFamily == TYPE_UNDEFINED_SPECIFIER) )


#define IF_MUST_BE_CHANNEL_SYMBOL  \
		if( (typeFamily == TYPE_CHANNEL_SPECIFIER)   ||  \
			(typeFamily == TYPE_UNIVERSAL_SPECIFIER) ||  \
			(typeFamily == TYPE_UNDEFINED_SPECIFIER) )


#define IF_MUST_BE_BUFFER_SYMBOL  \
		if( (typeFamily == TYPE_BUFFER_SPECIFIER)    ||  \
			(typeFamily == TYPE_UNIVERSAL_SPECIFIER) ||  \
			(typeFamily == TYPE_UNDEFINED_SPECIFIER) )


#define IF_MUST_BE_CONNECTOR_SYMBOL  \
		if( (typeFamily == TYPE_CONNECTOR_SPECIFIER) ||  \
			(typeFamily == TYPE_UNIVERSAL_SPECIFIER)  ||  \
			(typeFamily == TYPE_UNDEFINED_SPECIFIER) )


#define ANYTHING_ELSE_CONDITION  (  \
	( typeFamily != TYPE_MACHINE_SPECIFIER    ) &&  \
	( typeFamily != TYPE_PORT_SPECIFIER       ) &&  \
	( typeFamily != TYPE_SIGNAL_SPECIFIER     ) &&  \
	( typeFamily != TYPE_MESSAGE_SPECIFIER    ) &&  \
	( typeFamily != TYPE_CHANNEL_SPECIFIER    ) &&  \
	( typeFamily != TYPE_BUFFER_SPECIFIER     ) &&  \
	( typeFamily != TYPE_CONNECTOR_SPECIFIER ) )


#define IF_COULD_BE_TYPE_SPECIFIER_SYMBOL  \
		if( ANYTHING_ELSE_CONDITION )


#define IF_COULD_BE_TRANSITION_SYMBOL  \
		if( ANYTHING_ELSE_CONDITION )


#define IF_COULD_BE_GENERIC_PROGRAM_SYMBOL  \
		if( ANYTHING_ELSE_CONDITION )



const BF & ExecutableForm::getSymbol(
		const std::string & aFullyQualifiedNameID,
		avm_type_specifier_kind_t typeFamily) const
{
	IF_MUST_BE_GENERIC_PORT_SYMBOL
	{
		const Symbol & foundSymbol =
				mTableOfPort.getByFQNameID( aFullyQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_MACHINE_SYMBOL
	{
		const Symbol & foundSymbol =
				mTableOfInstanceStatic.getByFQNameID( aFullyQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}
//	IF_MUST_BE_MACHINE_SYMBOL
//	{
//		const Symbol & foundSymbol =
				mTableOfInstanceModel.getByFQNameID( aFullyQualifiedNameID );
//		if( foundSymbol.valid() )
//		{
//			return( foundSymbol );
//		}
//	}

	IF_MUST_BE_BUFFER_SYMBOL
	{
		const Symbol & foundSymbol =
				mTableOfBuffer.getByFQNameID( aFullyQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_CONNECTOR_SYMBOL
	{
		const Symbol & foundSymbol =
				mTableOfChannel.getByFQNameID( aFullyQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_CONNECTOR_SYMBOL
	{
		const Symbol & foundSymbol =
				mTableOfConnect.getByFQNameID( aFullyQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


	// UNCONDITIONAL
	{
		const BF & foundSymbol =
				AvmProgram::getSymbol(aFullyQualifiedNameID, typeFamily);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


	IF_COULD_BE_TYPE_SPECIFIER_SYMBOL
	{
		const BF & foundSymbol =
				getTypeSpecifier().getByFQNameID( aFullyQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_COULD_BE_TRANSITION_SYMBOL
	{
		const BF & foundSymbol =
				getTransition().getByFQNameID( aFullyQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_COULD_BE_GENERIC_PROGRAM_SYMBOL
	{
		const BF & foundSymbol =
				getProgram().getByFQNameID( aFullyQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	// UNCONDITIONAL
	{
		const Symbol & foundSymbol =
				getAlias().getByFQNameID( aFullyQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	return( BF::REF_NULL );
}


const BF & ExecutableForm::getSymbolByQualifiedNameID(
		const std::string & aQualifiedNameID,
		avm_type_specifier_kind_t typeFamily) const
{
	IF_MUST_BE_GENERIC_PORT_SYMBOL
	{
		const Symbol & foundSymbol =
				mTableOfPort.getByQualifiedNameID( aQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_MACHINE_SYMBOL
	{
		const Symbol & foundSymbol = mTableOfInstanceStatic.
				getByQualifiedNameID( aQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}
	IF_MUST_BE_MACHINE_SYMBOL
	{
		const Symbol & foundSymbol = mTableOfInstanceDynamic.
				getByQualifiedNameID( aQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}
//	IF_MUST_BE_MACHINE_SYMBOL
//	{
//		const Symbol & foundSymbol =
//				mTableOfInstanceModel.getByQualifiedNameID(aQualifiedNameID);
//		if( foundSymbol.valid() )
//		{
//			return( foundSymbol );
//		}
//	}

	IF_MUST_BE_BUFFER_SYMBOL
	{
		const Symbol & foundSymbol =
				mTableOfBuffer.getByQualifiedNameID(aQualifiedNameID);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_CONNECTOR_SYMBOL
	{
		const Symbol & foundSymbol =
				mTableOfConnect.getByQualifiedNameID(aQualifiedNameID);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


	// UNCONDITIONAL
	{
		const BF & foundSymbol =
				AvmProgram::getSymbolByQualifiedNameID(
						aQualifiedNameID, typeFamily);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


	IF_COULD_BE_TYPE_SPECIFIER_SYMBOL
	{
		const BF & foundSymbol = mTableOfTypeSpecifier.
				getByQualifiedNameID( aQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_COULD_BE_TRANSITION_SYMBOL
	{
		const BF & foundSymbol = mTableOfTransition.
				getByQualifiedNameID( aQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_COULD_BE_GENERIC_PROGRAM_SYMBOL
	{
		const BF & foundSymbol = mTableOfProgram.
				getByQualifiedNameID( aQualifiedNameID );
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


//	// UNCONDITIONAL
//	{
//		const Symbol & foundSymbol =
//				mTableOfAlias.getByQualifiedNameID( aQualifiedNameID );
//		if( foundSymbol.valid() )
//		{
//			return( foundSymbol );
//		}
//	}

	return( BF::REF_NULL );
}


const BF & ExecutableForm::getSymbolByNameID(const std::string & aNameID,
		avm_type_specifier_kind_t typeFamily) const
{
	IF_MUST_BE_GENERIC_PORT_SYMBOL
	{
		const Symbol & foundSymbol = mTableOfPort.getByNameID(aNameID);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_MACHINE_SYMBOL
	{
		const Symbol & foundSymbol =
				mTableOfInstanceStatic.getByNameID(aNameID);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}
//	IF_MUST_BE_MACHINE_SYMBOL
//	{
//		const Symbol & foundSymbol =
//				mTableOfInstanceModel.getByNameID(aNameID);
//		if( foundSymbol.valid() )
//		{
//			return( foundSymbol );
//		}
//	}

	IF_MUST_BE_BUFFER_SYMBOL
	{
		const Symbol & foundSymbol = mTableOfBuffer.getByNameID(aNameID);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_CONNECTOR_SYMBOL
	{
		const Symbol & foundSymbol = mTableOfConnect.getByNameID(aNameID);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


	// UNCONDITIONAL
	{
		const BF & foundSymbol =
				AvmProgram::getSymbolByNameID(aNameID, typeFamily);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


	IF_COULD_BE_TYPE_SPECIFIER_SYMBOL
	{
		const BF & foundSymbol = mTableOfTypeSpecifier.getByNameID(aNameID);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_COULD_BE_TRANSITION_SYMBOL
	{
		const BF & foundSymbol = mTableOfTransition.getByNameID(aNameID);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_COULD_BE_GENERIC_PROGRAM_SYMBOL
	{
		const BF & foundSymbol = mTableOfProgram.getByNameID(aNameID);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


//	// UNCONDITIONAL
//	{
//		const Symbol & foundSymbol = mTableOfAlias.getByNameID(id);
//		if( foundSymbol.valid() )
//		{
//			return( foundSymbol );
//		}
//	}

	return( BF::REF_NULL );
}


const BF & ExecutableForm::getSymbolByAstElement(
		const ObjectElement * astElement,
		avm_type_specifier_kind_t typeFamily) const
{
	IF_MUST_BE_GENERIC_PORT_SYMBOL
	{
		const Symbol & foundSymbol = mTableOfPort.getByAstElement(astElement);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_MACHINE_SYMBOL
	{
		const Symbol & foundSymbol = getByAstInstanceStatic(astElement);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_BUFFER_SYMBOL
	{
		const Symbol & foundSymbol = mTableOfBuffer.getByAstElement(astElement);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_CHANNEL_SYMBOL
	{
		const Symbol & foundSymbol = mTableOfChannel.getByAstElement(astElement);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_MUST_BE_CONNECTOR_SYMBOL
	{
		const Symbol & foundSymbol = mTableOfConnect.getByAstElement(astElement);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


	// UNCONDITIONAL
	{
		const BF & foundSymbol =
				AvmProgram::getSymbolByAstElement(astElement, typeFamily);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


	IF_COULD_BE_TYPE_SPECIFIER_SYMBOL
	{
		const BF & foundSymbol = getTypeSpecifier().getByAstElement(astElement);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_COULD_BE_TRANSITION_SYMBOL
	{
		const BF & foundSymbol = getTransition().getByAstElement(astElement);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	IF_COULD_BE_GENERIC_PROGRAM_SYMBOL
	{
		const BF & foundSymbol = getProgram().getByAstElement(astElement);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}


	// UNCONDITIONAL
	{
		const Symbol & foundSymbol = getAlias().getByAstElement(astElement);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	return( BF::REF_NULL );
}


/**
 * GETTER - SETTER
 * Machine Count
 */
avm_size_t ExecutableForm::getrecMachineCount() const
{
	avm_size_t count = 0;

	if( hasInstanceStatic() )
	{
		TableOfSymbol::const_iterator itMachine = instance_static_begin();
		TableOfSymbol::const_iterator endIt = instance_static_end();
		for( ; itMachine != endIt ; ++itMachine )
		{
			count += 1;

			if( (*itMachine).hasExecutable() )
			{
				count += (*itMachine).getExecutable()->getrecMachineCount();
			}
		}
	}
	return( count );
}



/**
 * ExecutableForm::LCA
 *
 */
const ExecutableForm * ExecutableForm::LCA(
		const ExecutableForm * anExecutable) const
{
	List< const ExecutableForm * > containerListOfThis;
	containerListOfThis.push_back(this);

	ExecutableForm * containerOfThis = this->getExecutableContainer();
	for ( ; containerOfThis != NULL ;
			containerOfThis = containerOfThis->getExecutableContainer() )
	{
		containerListOfThis.push_back(containerOfThis);
	}

	List< const ExecutableForm * > containerListOfOtherExecutable;
	containerListOfOtherExecutable.push_back(anExecutable);

	ExecutableForm * containerOfOtherForm = anExecutable->getExecutableContainer();
	for ( ; containerOfOtherForm != NULL ;
		containerOfOtherForm = containerOfOtherForm->getExecutableContainer() )
	{
		containerListOfOtherExecutable.push_back(containerOfOtherForm);
	}

	List< const ExecutableForm * >::const_iterator otherIt;
	List< const ExecutableForm * >::
	const_iterator oneIt = containerListOfThis.begin();
	for ( ; oneIt != containerListOfThis.end() ; oneIt++ )
	{
		otherIt = containerListOfOtherExecutable.begin();
		for ( ; otherIt != containerListOfOtherExecutable.end() ; ++otherIt )
		{
			if( (*oneIt) == (*otherIt) )
			{
//				AVM_OS_LOG << "LCA ( "
//					<< oneExecutable->getFullyQualifiedNameID()
//					<< " , " << otherExecutable->getFullyQualifiedNameID()
//					<< " ) = " << (*oneIt)->getFullyQualifiedNameID();

				return( *oneIt );
			}
		}
	}

	return( NULL );
}


/*
 * GETTER - SETTER
 * Single or Multiple
 * Instanciation Information
 * for Data Access optimisation
 */
void ExecutableForm::incrPossibleStaticInstanciationCount(avm_offset_t offset)
{
	mPossibleStaticInstanciationCount += offset;

	if( mPossibleStaticInstanciationCount > 1 )
	{
		TableOfSymbol::const_iterator itInstabce = instance_static_begin();
		TableOfSymbol::const_iterator endInstabce = instance_static_end();
		for( ; itInstabce != endInstabce ; ++itInstabce )
		{
			(*itInstabce).getExecutable()->
					incrPossibleStaticInstanciationCount(offset);
		}
	}
}


void ExecutableForm::incrPossibleDynamicInstanciationCount(avm_size_t offset)
{
	mPossibleDynamicInstanciationCount += offset;

	if( mPossibleDynamicInstanciationCount > 1 )
	{
		TableOfSymbol::const_iterator itInstabce = instance_static_begin();
		TableOfSymbol::const_iterator endInstabce = instance_static_end();
		for( ; itInstabce != endInstabce ; ++itInstabce )
		{
			(*itInstabce).getExecutable()->
					incrPossibleDynamicInstanciationCount(offset);
		}
	}
}


bool ExecutableForm::hasSingleRuntimeInstance()
{
//	AVM_OS_COUT << strModifier() << "executable< mok:"
//			<< getSpecifier().str()
//			<< " , id:" << getOffset()
//			<< " , pic:(static:" << mPossibleStaticInstanciationCount
//			<< " , dynamic:" << mPossibleDynamicInstanciationCount << ")"
//			<< " , instance:(init:" << mInitialInstanceCount
//			<< " , max:" << ( (mMaximalInstanceCount == AVM_NUMERIC_MAX_SIZE_T) ?
//					-1 : static_cast< avm_int64_t >(mMaximalInstanceCount) )
//			<< ") > " << getFullyQualifiedNameID() << std::endl;

	if( (mPossibleStaticInstanciationCount > 1) ||
		(mPossibleDynamicInstanciationCount > 0) )
	{
		return( false );
	}

	else
	{
		ExecutableForm * containerExec = getExecutableContainer();

		if( (containerExec != NULL) &&
			(not containerExec->hasSingleRuntimeInstance()) )
		{
			mPossibleDynamicInstanciationCount = 1;

			return( false );
		}

		return( true );
	}
}


/**
 * GETTER - SETTER
 * mMutableScheduleFlag
 * MOC Attribute for mutable Schedule
 */

bool ExecutableForm::isInlinableSchedule() const
{
//	if( not hasSingleRuntimeInstance() )
//	{
//		return( false );
//	}

	TableOfSymbol::const_iterator itModel = instance_model_begin();
	TableOfSymbol::const_iterator endModel = instance_model_end();
	for( ; itModel != endModel ; ++itModel )
	{
		if( not (*itModel).getExecutable()->hasSingleRuntimeInstance() )
		{
			return( false );
		}
	}

	return( (not mMutableScheduleFlag) );
}



/**
 * GETTER
 * on activity by opcode
 */
AvmProgram & ExecutableForm::getOnActivityRoutine(AVM_OPCODE opCode)
{
	switch( opCode )
	{
		case AVM_OPCODE_INIT:
		{
			return( getOnInitRoutine() );
		}
		case AVM_OPCODE_FINAL:
		case AVM_OPCODE_DESTROY:
		{
			return( getOnFinalRoutine() );
		}

		case AVM_OPCODE_RETURN:
		{
			return( getOnReturnRoutine() );
		}

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		{
			return( getOnStartRoutine() );
		}
		case AVM_OPCODE_STOP:
		{
			return( getOnStopRoutine() );
		}

//		case AVM_OPCODE_WAIT:
//		case AVM_OPCODE_SUSPEND:
//		case AVM_OPCODE_RESUME:

		case AVM_OPCODE_IENABLE_INVOKE:
		{
			return( getOnIEnableRoutine() );
		}
		case AVM_OPCODE_ENABLE_INVOKE:
		{
			return( getOnEnableRoutine() );
		}
//		case AVM_OPCODE_ENABLE_SET:

		case AVM_OPCODE_IDISABLE_INVOKE:
		{
			return( getOnIDisableRoutine() );
		}
		case AVM_OPCODE_DISABLE_INVOKE:
		{
			return( getOnDisableRoutine() );
		}
//		case AVM_OPCODE_DISABLE_SET:

//		case AVM_OPCODE_DISABLE_CHILD:
//		case AVM_OPCODE_DISABLE_SELF:
//		case AVM_OPCODE_DISABLE_SELVES:

		case AVM_OPCODE_IABORT_INVOKE:
		{
			return( getOnIAbortRoutine() );
		}
		case AVM_OPCODE_ABORT_INVOKE:
		{
			return( getOnAbortRoutine() );
		}
//		case AVM_OPCODE_ABORT_SET:

//		case AVM_OPCODE_ABORT_CHILD:
//		case AVM_OPCODE_ABORT_SELF:
//		case AVM_OPCODE_ABORT_SELVES:

		case AVM_OPCODE_IRUN:
		{
			return( getOnIRunRoutine() );
		}
		case AVM_OPCODE_RUN:
		{
			return( getOnRunRoutine() );
		}

		case AVM_OPCODE_RTC:
		{
			return( getOnRtcRoutine() );
		}

		case AVM_OPCODE_SCHEDULE_INVOKE:
		{
			return( getOnScheduleRoutine() );
		}

//		case AVM_OPCODE_DEFER_INVOKE:

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ExecutableForm::getOnActivityRoutine:> "
						"Unexpected AVM_OPCODE !!!"
					<< SEND_EXIT;

			return( getOnScheduleRoutine() );
		}
	}
}


const BFCode & ExecutableForm::getOnActivity(AVM_OPCODE opCode) const
{
	switch( opCode )
	{
		case AVM_OPCODE_INIT:
		{
			return( getOnInit() );
		}
		case AVM_OPCODE_FINAL:
		case AVM_OPCODE_DESTROY:
		{
			return( getOnFinal() );
		}

		case AVM_OPCODE_RETURN:
		{
			return( getOnReturn() );
		}

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		{
			return( getOnStart() );
		}
		case AVM_OPCODE_STOP:
		{
			return( getOnStop() );
		}

//		case AVM_OPCODE_WAIT:
//		case AVM_OPCODE_SUSPEND:
//		case AVM_OPCODE_RESUME:

		case AVM_OPCODE_IENABLE_INVOKE:
		{
			return( getOnIEnable() );
		}
		case AVM_OPCODE_ENABLE_INVOKE:
		{
			return( getOnEnable() );
		}
//		case AVM_OPCODE_ENABLE_SET:

		case AVM_OPCODE_IDISABLE_INVOKE:
		{
			return( getOnIDisable() );
		}
		case AVM_OPCODE_DISABLE_INVOKE:
		{
			return( getOnDisable() );
		}
//		case AVM_OPCODE_DISABLE_SET:

//		case AVM_OPCODE_DISABLE_CHILD:
//		case AVM_OPCODE_DISABLE_SELF:
//		case AVM_OPCODE_DISABLE_SELVES:

		case AVM_OPCODE_IABORT_INVOKE:
		{
			return( getOnIAbort() );
		}
		case AVM_OPCODE_ABORT_INVOKE:
		{
			return( getOnAbort() );
		}
//		case AVM_OPCODE_ABORT_SET:

//		case AVM_OPCODE_ABORT_CHILD:
//		case AVM_OPCODE_ABORT_SELF:
//		case AVM_OPCODE_ABORT_SELVES:

		case AVM_OPCODE_IRUN:
		{
			return( getOnIRun() );
		}
		case AVM_OPCODE_RUN:
		{
			return( getOnRun() );
		}

		case AVM_OPCODE_RTC:
		{
			return( getOnRtc() );
		}

		case AVM_OPCODE_SCHEDULE_INVOKE:
		{
			return( getOnSchedule() );
		}

//		case AVM_OPCODE_DEFER_INVOKE:

		default:
		{
			return( BFCode::REF_NULL );
		}
	}
}


/**
 * Serialization
 */
void ExecutableForm::header(OutStream & os) const
{
	os << getModifier().toString()
			<< getSpecifier().toString( Specifier::ENABLE_FEATURE_DESIGN_FIELD )
			<< "executable< moc: "
			<< getSpecifier().str( Specifier::DISABLE_FEATURE_DESIGN_FIELD )
			<< " , id:" << getOffset();

	InstanceSpecifierPart::strMultiplicity(
			os, mPossibleStaticInstanciationCount,
			mPossibleDynamicInstanciationCount,
			mMaximalInstanceCount, ", instanciation: [ ", " ]");

//AVM_IF_DEBUG_ENABLED_AND(
//		getSpecifier().isFamilyComponentComposite()
//		&& ( (mPossibleStaticInstanciationCount != 1)
//			|| (mPossibleDynamicInstanciationCount > 0) ) )
//	os << " , pic:(static:" << mPossibleStaticInstanciationCount
//			<< " , dynamic:" << mPossibleDynamicInstanciationCount << ")";
//AVM_ENDIF_DEBUG_ENABLED
//
//AVM_IF_DEBUG_ENABLED_AND(
//		getSpecifier().isFamilyComponentComposite()
//		&& ( (mInitialInstanceCount != 1)
//			|| (mMaximalInstanceCount != AVM_NUMERIC_MAX_SIZE_T) ) )
//	os << " , instance:(init:" << mInitialInstanceCount << " , max:"
//			<< ( (mMaximalInstanceCount == AVM_NUMERIC_MAX_SIZE_T) ?
//					-1 : static_cast< avm_int64_t >(mMaximalInstanceCount) )
//			<< " )";
//AVM_ENDIF_DEBUG_ENABLED

	os << " > ";
};


void ExecutableForm::strHeader(OutStream & os) const
{
	header( os );

AVM_IF_DEBUG_FLAG_AND( COMPILING , hasAstElement() )
	os << "&" << getAstFullyQualifiedNameID() << " ";
AVM_ENDIF_DEBUG_FLAG_AND( COMPILING )

	os << getFullyQualifiedNameID();
}


void ExecutableForm::toStream(OutStream & os,
		const TableOfRouter & aTableOfRouter, const std::string & sectionName)
{
	if( aTableOfRouter.nonempty() )
	{
		os << TAB << sectionName << EOL_INCR_INDENT;

		TableOfRouter::const_iterator itRouter = aTableOfRouter.begin();
		TableOfRouter::const_iterator endRouter = aTableOfRouter.end();

		for( ; itRouter != endRouter ; ++itRouter )
		{
			if( (*itRouter).valid() )
			{
				(*itRouter).toStream(os);
			}
			else
			{
				os << TAB << "routeur<null>";
			}

			os << EOL_FLUSH;
		}

		if( aTableOfRouter.last().invalid() )
		{
			os << EOL;
		}

		os << DECR_INDENT;
	}
}


void ExecutableForm::toStream(OutStream & os) const
{
	if(  os.preferablyFQN() )
	{
		os << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(os);

		return;
	}

	header( os << TAB );

AVM_IF_DEBUG_FLAG_AND( COMPILING , hasAstElement() )
	os << "&" << getAstFullyQualifiedNameID() << " ";
AVM_ENDIF_DEBUG_FLAG_AND( COMPILING )

	os << getFullyQualifiedNameID() << " {" << EOL;

//AVM_IF_DEBUG_ENABLED_AND(
//		getSpecifier().isFamilyComponentComposite()
//		&& ( (mPossibleStaticInstanciationCount != 1)
//			|| (mPossibleDynamicInstanciationCount > 0) ) )
//	os << TAB2 << "//possible_instanciation_count = (static:"
//			<< mPossibleStaticInstanciationCount << " , dynamic:"
//			<< mPossibleDynamicInstanciationCount << ");" << EOL;
//AVM_ENDIF_DEBUG_ENABLED


AVM_IF_DEBUG_FLAG( COMPILING )
	if( hasContainer() )
	{
		os << TAB2 << "//container = "
				<< str_header( getContainer()->as< ExecutableForm >() )
				<< ";" << EOL;
	}

	if( hasPrototypeInstance() )
	{
		os << TAB2 << "//prototype = "
				<< str_header( getPrototypeInstance() )
				<< ";" << EOL;
	}
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	// MOC Attribute
	if( isInputEnabledCommunication() )
	{
		os << TAB2 << "input_enabled = true;" << EOL << std::flush;
	}


	// Any program data
	toStreamData(os);

	if( hasAlias() )
	{
		( hasDataAlias() ? os : os << TAB << "alias:" ) << EOL_INCR_INDENT;

		getAlias().toStream(os);

		os << DECR_INDENT;
	}


	if( hasPort() )
	{
		if( (mMessageSignalCount == 0) ||
			(mMessageSignalCount == getPort().size()) )
		{
			os << TAB << "port:" << EOL;
		}
		else
		{
			os << TAB << "port< ms: " << mMessageSignalCount << " >:" << EOL;
		}

		os << incr_stream( getPort() );
	}


	if( hasBuffer() )
	{
		os << TAB << "buffer:" << EOL_INCR_INDENT;

		getBuffer().toStream(os);

		os << DECR_INDENT;
	}

	if( hasChannel() )
	{
		os << TAB << "channel:" << EOL_INCR_INDENT;

		getChannel().toStream(os);

		os << DECR_INDENT;
	}

	if( hasConnect() )
	{
		os << TAB << "connection:" << "/* < " << getFullyQualifiedNameID() << " > */"
				<< EOL_INCR_INDENT;

		getConnect().toStream(os);

		os << DECR_INDENT;
	}

	if( hasRdvCommunication() )
	{
		os << EOL_TAB2 << "rdv_communication = true;" << EOL << EOL;
	}

	// Table of Router for Instance
	toStream(os, mTableOfRouter4Instance, "router:");

	// Table of Router for Model
	toStream(os, mTableOfRouter4Model, "router#model:");


	if( hasExecutable() )
	{
		os << TAB << "procedure:" << EOL_INCR_INDENT;

		getExecutables().toStream(os);

		os << DECR_INDENT;
	}


	if( hasInstanceModel() )
	{
		os << TAB << "model:" << EOL_INCR_INDENT;

		getInstanceModel().toStream(os);

		os << DECR_INDENT;
	}

	if( hasInstanceStatic() )
	{
		os << TAB << "instance:" << EOL_INCR_INDENT;

		getInstanceStatic().toStream(os);

		os << DECR_INDENT;
	}

	if( hasInstanceDynamic() )
	{
		os << TAB << "instance#dynamic:" << EOL_INCR_INDENT;

		getInstanceDynamic().toStream(os);

		os << DECR_INDENT;
	}


	if( hasTransition() )
	{
		os << TAB << "transition:" << EOL_INCR_INDENT;

		getTransition().toStream(os);

		os << DECR_INDENT;
	}

	if( hasProgram() )
	{
		os << TAB << "program:" << EOL_INCR_INDENT;

		getProgram().toStream(os);

		os << DECR_INDENT;
	}

	if( mTableOfAnonymousInnerRoutine.nonempty() )
	{
		os << TAB << "routine< anonymous#inner >:" << EOL_INCR_INDENT;

		mTableOfAnonymousInnerRoutine.fqnStream(os);

		os << DECR_INDENT;
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// STATIC ANALYSIS ATTRIBUTE
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////


AVM_IF_DEBUG_FLAG2( COMPILING , DATA )
	if( hasTransition() || hasProgram() )
	{
		TableOfInstanceOfData::const_raw_iterator itData;
		TableOfInstanceOfData::const_raw_iterator endData;

		if( getRequiredData().nonempty() )
		{
			os << TAB << "data#required:" << EOL;
			itData = getRequiredData().begin();
			endData = getRequiredData().end();
			for( ; itData != endData ; ++itData )
			{
				os << TAB2 << itData->getFullyQualifiedNameID() << ";" << EOL;
			}
		}

		if( getUselessData().nonempty() )
		{
			os << TAB << "data#useless:" << EOL;
			itData = getUselessData().begin();
			endData = getUselessData().end();
			for( ; itData != endData ; ++itData )
			{
				os << TAB2 << itData->getFullyQualifiedNameID() << ";" << EOL;
			}
		}
	}
AVM_ENDIF_DEBUG_FLAG2( COMPILING , DATA )


	if( hasVariableDependency() )
	{
		os << TAB << "dependency#variable = "
				<< STATIC_ANALYSIS::to_string( getVariableDependent() ) << EOL;
	}


	if( (not isReachableStateFlag)
		&& (not getSpecifier().isPseudostateInitialOrStateStart()) )
	{
		os << TAB2 << "reachable#machine = false;" << EOL;
	}

	if( hasBackwardReachableMachine() )
	{
		os << TAB << "reachable#backward#machine:" << EOL;

		ListOfInstanceOfMachine::const_iterator itMachine =
				getBackwardReachableMachine().begin();
		ListOfInstanceOfMachine::const_iterator endMachine =
				getBackwardReachableMachine().end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			os << TAB2 << str_header( *itMachine ) << ";" << EOL;
		}
	}

	if( hasBackwardReachableTransition() )
	{
		os << TAB << "reachable#backward#transition:" << EOL;

		OutStream osHierarchy( os );
		osHierarchy.INDENT.CHAR = " ";

		ListOfAvmTransition::const_iterator itProg =
				getBackwardReachableTransition().begin();
		ListOfAvmTransition::const_iterator endProg =
				getBackwardReachableTransition().end();
		for( ; itProg != endProg ; ++itProg )
		{
			os << TAB2 << str_header( *itProg ) << ";" << EOL;
		}
	}


	if( hasForwardReachableMachine() )
	{
		os << TAB << "reachable#forward#machine:" << EOL;

		OutStream osHierarchy( os );
		osHierarchy.INDENT.CHAR = " ";

		ListOfInstanceOfMachine::const_iterator itMachine =
				getForwardReachableMachine().begin();
		ListOfInstanceOfMachine::const_iterator endMachine =
				getForwardReachableMachine().end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			os << TAB2 << str_header( *itMachine ) << ";" << EOL;
		}
	}

	if( hasForwardReachableTransition() )
	{
		os << TAB << "reachable#forward#transition:" << EOL;

		OutStream osHierarchy( os );
		osHierarchy.INDENT.CHAR = " ";

		ListOfAvmTransition::const_iterator itProg =
				getForwardReachableTransition().begin();
		ListOfAvmTransition::const_iterator endProg =
				getForwardReachableTransition().end();
		for( ; itProg != endProg ; ++itProg )
		{
			os << TAB2 << str_header( *itProg ) << ";" << EOL;
		}
	}


	os << TAB << "moe:" << EOL;

	if( hasOnCreate() )
	{
		os << TAB2 << "@create{" << INCR2_INDENT;
		getOnCreate()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnInit() )
	{
		os << TAB2 << "@init{" << INCR2_INDENT;
		getOnInit()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnReturn() )
	{
		os << TAB2 << "@return{" << INCR2_INDENT;
		getOnReturn()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnFinal() )
	{
		os << TAB2 << "@final{" << INCR2_INDENT;
		getOnFinal()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnStart() )
	{
		os << TAB2 << "@start{" << INCR2_INDENT;
		getOnStart()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnStop() )
	{
		os << TAB2 << "@stop{" << INCR2_INDENT;
		getOnStop()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnIEnable() )
	{
		os << TAB2 << "@ienable{" << INCR2_INDENT;
		getOnIEnable()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnEnable() )
	{
		os << TAB2 << "@enable{" << INCR2_INDENT;
		getOnEnable()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnIDisable() )
	{
		os << TAB2 << "@idisable{" << INCR2_INDENT;
		getOnIDisable()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnDisable() )
	{
		os << TAB2 << "@disable{" << INCR2_INDENT;
		getOnDisable()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnIAbort() )
	{
		os << TAB2 << "@iabort{" << INCR2_INDENT;
		getOnIAbort()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnAbort() )
	{
		os << TAB2 << "@abort{" << INCR2_INDENT;
		getOnAbort()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnIRun() )
	{
		os << TAB2 << "@irun{" << INCR2_INDENT;
		getOnIRun()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnRun() )
	{
		os << TAB2 << "@run{" << INCR2_INDENT;
		getOnRun()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnRtc() )
	{
		os << TAB2 << "@rtc{" << INCR2_INDENT;
		getOnRtc()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnSchedule() )
	{
		os << TAB2 << "@schedule" << (isMutableSchedule() ? "" : "<final>")
				<< "{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}
	else if( isMutableSchedule() )
	{
		os << TAB2 << "@schedule#mutable{ }" << EOL;
	}


	if( hasOnConcurrency() )
	{
		os << TAB2 << "@concurrency{";
		if( getOnConcurrency()->empty() )
		{
			os << " " << getOnConcurrencyOperator()->strOp() << " ";
		}
		else
		{
			getOnConcurrency()->toStreamRoutine( os << INCR2_INDENT )
					<< DECR2_INDENT_TAB2;
		}
		os << "}" << EOL;
	}


	if( hasOnSynchronize() )
	{
		os << TAB2 << "@synchronize{" << INCR2_INDENT;
		getOnSynchronize()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	// static class of Port/Message/Signal in communicated transition
	os << INCR_INDENT;
	toStreamStaticCom(os);
	os << DECR_INDENT;

	os << TAB << "}" << EOL << std::flush;
}


}

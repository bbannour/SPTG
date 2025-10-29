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
 * GETTER
 * Unique Null Reference
 */
ExecutableForm & ExecutableForm::nullref()
{
	static ExecutableForm _NULL_(ExecutableSystem::nullref(), 0);
	_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );
	_NULL_.setSpecifier( Specifier::OBJECT_NULL_SPECIFIER );

	return( _NULL_ );
}


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
 * SETTER
 * mTimeVariable
 * mDeltaTimeVariable
 */
void ExecutableForm::setDeltaTimeVariable()
{
	if( getSpecifier().hasFeatureTimed() )
	{
		const PropertyPart & aPropertyPart = getAstMachine().getPropertyPart();

		if( aPropertyPart.hasTimeVariable() )
		{
			const BF & timeVariable =
					getVariables().getByAstElement(
							*(aPropertyPart.getTimeVariable()) );

			AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( timeVariable )
					<< "Time Variable Symbol in "
					<< str_header( aPropertyPart.getContainerMachine() )
					<< " !!!"
					<< SEND_EXIT;

			setTimeVariable(timeVariable);

		}
		if( aPropertyPart.hasDeltaTimeVariable() )
		{
			const BF & deltaTimeVariable =
					getVariables().getByAstElement(
							*(aPropertyPart.getDeltaTimeVariable()) );

			AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( deltaTimeVariable )
					<< "Delta Time Variable Symbol in "
					<< str_header( aPropertyPart.getContainerMachine() )
					<< " !!!"
					<< SEND_EXIT;

			setDeltaTimeVariable(deltaTimeVariable);
		}
	}
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
				mTableOfConnector.getByFQNameID( aFullyQualifiedNameID );
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
				mTableOfConnector.getByQualifiedNameID(aQualifiedNameID);
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
		const Symbol & foundSymbol = mTableOfConnector.getByNameID(aNameID);
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
		const ObjectElement & astElement,
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
		const Symbol & foundSymbol = mTableOfConnector.getByAstElement(astElement);
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
std::size_t ExecutableForm::getrecMachineCount() const
{
	std::size_t count = 0;

	if( hasInstanceStatic() )
	{
		TableOfSymbol::const_iterator itMachine = instance_static_begin();
		TableOfSymbol::const_iterator endIt = instance_static_end();
		for( ; itMachine != endIt ; ++itMachine )
		{
			count += 1;

			if( (*itMachine).hasExecutable() )
			{
				count += (*itMachine).getExecutable().getrecMachineCount();
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
	for ( ; containerOfThis != nullptr ;
			containerOfThis = containerOfThis->getExecutableContainer() )
	{
		containerListOfThis.push_back(containerOfThis);
	}

	List< const ExecutableForm * > containerListOfOtherExecutable;
	containerListOfOtherExecutable.push_back(anExecutable);

	ExecutableForm * containerOfOtherForm = anExecutable->getExecutableContainer();
	for ( ; containerOfOtherForm != nullptr ;
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

	return( nullptr );
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
			const_cast< ExecutableForm & >( (*itInstabce).getExecutable() ).
					incrPossibleStaticInstanciationCount(offset);
		}
	}
}


void ExecutableForm::incrPossibleDynamicInstanciationCount(std::size_t offset)
{
	mPossibleDynamicInstanciationCount += offset;

	if( mPossibleDynamicInstanciationCount > 1 )
	{
		TableOfSymbol::const_iterator itInstabce = instance_static_begin();
		TableOfSymbol::const_iterator endInstabce = instance_static_end();
		for( ; itInstabce != endInstabce ; ++itInstabce )
		{
			const_cast< ExecutableForm & >( (*itInstabce).getExecutable() ).
					incrPossibleDynamicInstanciationCount(offset);
		}
	}
}


bool ExecutableForm::hasSingleRuntimeInstance() const
{
//	AVM_OS_COUT << strModifier() << "executable< mok:"
//			<< getSpecifier().str()
//			<< " , id:" << getOffset()
//			<< " , pic:(static:" << mPossibleStaticInstanciationCount
//			<< " , dynamic:" << mPossibleDynamicInstanciationCount << ")"
//			<< " , instance:(init:" << mInitialInstanceCount
//			<< " , max:" << ( (mMaximalInstanceCount == AVM_NUMERIC_MAX_SIZE_T) ?
//					-1 : static_cast< std::int64_t >(mMaximalInstanceCount) )
//			<< ") > " << getFullyQualifiedNameID() << std::endl;

	if( (mPossibleStaticInstanciationCount > 1) ||
		(mPossibleDynamicInstanciationCount > 0) )
	{
		return( false );
	}

	else
	{
		ExecutableForm * containerExec = getExecutableContainer();

		if( (containerExec != nullptr) &&
			(not containerExec->hasSingleRuntimeInstance()) )
		{
			const_cast< ExecutableForm * >(
					this )->mPossibleDynamicInstanciationCount = 1;

			return( false );
		}

		return( true );
	}
}


/**
 * TESTER
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
		if( not (*itModel).getExecutable().hasSingleRuntimeInstance() )
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
const AvmProgram & ExecutableForm::getOnActivityRoutine(AVM_OPCODE opCode) const
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
 * GETTER - SETTER
 * IOpcodeFamily
 */
void ExecutableForm::updateOpcodeFamily()
{
	for( auto & itTransition : getTransition() )
	{
		addStatementFamily(
				itTransition.to< AvmTransition >().getStatementFamily() );
	}

	for( auto & itStatic : getInstanceStatic() )
	{
		if( (! itStatic.getExecutable().hasStatementFamily())
			&& (! itStatic.isThis()) )
		{
			itStatic.getExecutable().updateOpcodeFamily();
		}
		addStatementFamily( itStatic.getExecutable().getStatementFamily() );
	}

	for( auto & itDynamic : getInstanceDynamic() )
	{
		if( (! itDynamic.getExecutable().hasStatementFamily())
			&& (! itDynamic.isThis()) )
		{
			itDynamic.getExecutable().updateOpcodeFamily();
		}
		addStatementFamily( itDynamic.getExecutable().getStatementFamily() );
	}
}


/**
 * Serialization
 */
void ExecutableForm::header(OutStream & out) const
{
	out << getModifier().toString()
		<< getSpecifier().toString( Specifier::ENABLE_FEATURE_DESIGN_FIELD )
		<< "executable< moc: "
		<< getSpecifier().str( Specifier::DISABLE_FEATURE_DESIGN_FIELD )
		<< " , id:" << getOffset();

	InstanceSpecifierPart::strMultiplicity(
			out, mPossibleStaticInstanciationCount,
			mPossibleDynamicInstanciationCount,
			mMaximalInstanceCount, ", instanciation: [ ", " ]");

//AVM_IF_DEBUG_ENABLED_AND(
//		getSpecifier().isFamilyCompositeComponent()
//		&& ( (mPossibleStaticInstanciationCount != 1)
//			|| (mPossibleDynamicInstanciationCount > 0) ) )
//	out << " , pic:(static:" << mPossibleStaticInstanciationCount
//		<< " , dynamic:" << mPossibleDynamicInstanciationCount << ")";
//AVM_ENDIF_DEBUG_ENABLED
//
//AVM_IF_DEBUG_ENABLED_AND(
//		getSpecifier().isFamilyCompositeComponent()
//		&& ( (mInitialInstanceCount != 1)
//			|| (mMaximalInstanceCount != AVM_NUMERIC_MAX_SIZE_T) ) )
//	out << " , instance:(init:" << mInitialInstanceCount << " , max:"
//		<< ( (mMaximalInstanceCount == AVM_NUMERIC_MAX_SIZE_T) ?
//				-1 : static_cast< std::int64_t >(mMaximalInstanceCount) )
//		<< " )";
//AVM_ENDIF_DEBUG_ENABLED

	out << " > ";
};


void ExecutableForm::strHeader(OutStream & out) const
{
	header( out );

AVM_IF_DEBUG_FLAG_AND( COMPILING , hasAstElement() )
	out << "&" << getAstFullyQualifiedNameID() << " ";
AVM_ENDIF_DEBUG_FLAG_AND( COMPILING )

	out << getFullyQualifiedNameID();
}


void ExecutableForm::toStream(OutStream & out,
		const TableOfRouter & aTableOfRouter, const std::string & sectionName)
{
	if( aTableOfRouter.nonempty() )
	{
		out << TAB << sectionName << EOL_INCR_INDENT;

		for( const auto & itRouter : aTableOfRouter )
		{
			if( itRouter.valid() )
			{
				itRouter.toStream(out);
			}
			else
			{
				out << TAB << "routeur<null>";
			}

			out << EOL_FLUSH;
		}

		if( aTableOfRouter.last().invalid() )
		{
			out << EOL;
		}

		out << DECR_INDENT;
	}
}


void ExecutableForm::toStream(OutStream & out) const
{
	if(  out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	header( out << TAB );

AVM_IF_DEBUG_FLAG_AND( COMPILING , hasAstElement() )
	out << "&" << getAstFullyQualifiedNameID() << " ";
AVM_ENDIF_DEBUG_FLAG_AND( COMPILING )

	out << getFullyQualifiedNameID() << " {" << EOL;

//AVM_IF_DEBUG_ENABLED_AND(
//		getSpecifier().isFamilyCompositeComponent()
//		&& ( (mPossibleStaticInstanciationCount != 1)
//			|| (mPossibleDynamicInstanciationCount > 0) ) )
//	out << TAB2 << "//possible_instanciation_count = (static:"
//		<< mPossibleStaticInstanciationCount << " , dynamic:"
//		<< mPossibleDynamicInstanciationCount << ");" << EOL;
//AVM_ENDIF_DEBUG_ENABLED


AVM_IF_DEBUG_FLAG( COMPILING )
	if( hasContainer() )
	{
		out << TAB2 << "//container = "
			<< str_header( getContainer()->as_ptr< ExecutableForm >() )
			<< ";" << EOL;
	}

	if( hasPrototypeInstance() )
	{
		out << TAB2 << "//prototype = "
			<< str_header( getPrototypeInstance() )
			<< ";" << EOL;
	}
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	// MOC Attribute
	if( isInputEnabledCommunication() )
	{
		out << TAB2 << "input_enabled = true;" << EOL << std::flush;
	}

	if( isWeakLifeline() )
	{
		out << TAB2 << "weak#lifeline = true;" << EOL << std::flush;
	}


	// All program variables
	toStreamVariables(out);

	if( hasTimeVariable() )
	{
		out << TAB << "time:" << EOL
			<< TAB2 << str_header( getTimeVariable() ) << EOL
			<< TAB2 << str_header( getDeltaTimeVariable() ) << EOL;
	}

	if( hasAlias() )
	{
		( hasVariableAlias() ? out : out << TAB << "alias:" ) << EOL_INCR_INDENT;

		getAlias().toStream(out);

		out << DECR_INDENT;
	}


	if( hasPort() )
	{
		if( (mMessageSignalCount == 0) ||
			(mMessageSignalCount == getPort().size()) )
		{
			out << TAB << "port:" << EOL;
		}
		else
		{
			out << TAB << "port< ms: " << mMessageSignalCount << " >:" << EOL;
		}

		out << incr_stream( getPort() );
	}


	if( hasBuffer() )
	{
		out << TAB << "buffer:" << EOL_INCR_INDENT;

		getBuffer().toStream(out);

		out << DECR_INDENT;
	}

	if( hasChannel() )
	{
		out << TAB << "channel:" << EOL_INCR_INDENT;

		getChannel().toStream(out);

		out << DECR_INDENT;
	}

	if( hasConnector() )
	{
		out << TAB << "connector:" << "/* < " << getFullyQualifiedNameID()
				<< " > */"
				<< EOL_INCR_INDENT;

		getConnector().toStream(out);

		out << DECR_INDENT;
	}

	if( hasRdvCommunication() )
	{
		out << EOL_TAB2 << "rdv_communication = true;" << EOL << EOL;
	}

	// Table of Router for Instance
	toStream(out, mTableOfRouter4Instance, "router:");

	// Table of Router for Model
	toStream(out, mTableOfRouter4Model, "router#model:");


	if( hasExecutable() )
	{
		out << TAB << "procedure:" << EOL_INCR_INDENT;

		getExecutables().toStream(out);

		out << DECR_INDENT;
	}


	if( hasInstanceModel() )
	{
		out << TAB << "model:" << EOL_INCR_INDENT;

		getInstanceModel().toStream(out);

		out << DECR_INDENT;
	}

	if( hasInstanceStatic() )
	{
		out << TAB << "instance:" << EOL_INCR_INDENT;

		getInstanceStatic().toStream(out);

		out << DECR_INDENT;
	}

	if( hasInstanceDynamic() )
	{
		out << TAB << "instance#dynamic:" << EOL_INCR_INDENT;

		getInstanceDynamic().toStream(out);

		out << DECR_INDENT;
	}


	if( hasTransition() )
	{
		out << TAB << "transition:" << EOL_INCR_INDENT;

		getTransition().toStream(out);

		out << DECR_INDENT;
	}

	if( hasProgram() )
	{
		out << TAB << "program:" << EOL_INCR_INDENT;

		getProgram().toStream(out);

		out << DECR_INDENT;
	}

	if( mTableOfAnonymousInnerRoutine.nonempty() )
	{
		out << TAB << "routine< anonymous#inner >:" << EOL_INCR_INDENT;

		mTableOfAnonymousInnerRoutine.fqnStream(out);

		out << DECR_INDENT;
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// STATIC ANALYSIS ATTRIBUTE
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////


AVM_IF_DEBUG_FLAG2( COMPILING , DATA )
	if( hasTransition() || hasProgram() )
	{
		TableOfInstanceOfData::const_raw_iterator itVar;
		TableOfInstanceOfData::const_raw_iterator endVar;

		if( getRequiredData().nonempty() )
		{
			out << TAB << "data#required:" << EOL;
			itVar = getRequiredData().begin();
			endVar = getRequiredData().end();
			for( ; itVar != endVar ; ++itVar )
			{
				out << TAB2 << itVar->getFullyQualifiedNameID() << ";" << EOL;
			}
		}

		if( getUselessData().nonempty() )
		{
			out << TAB << "data#useless:" << EOL;
			itVar = getUselessData().begin();
			endVar = getUselessData().end();
			for( ; itVar != endVar ; ++itVar )
			{
				out << TAB2 << itVar->getFullyQualifiedNameID() << ";" << EOL;
			}
		}
	}
AVM_ENDIF_DEBUG_FLAG2( COMPILING , DATA )


	if( hasVariableDependency() )
	{
		out << TAB << "dependency#variable = "
				<< STATIC_ANALYSIS::to_string( getVariableDependent() ) << EOL;
	}


	if( (not isReachableStateFlag)
		&& (not getSpecifier().isPseudostateInitialOrStateStart()) )
	{
		out << TAB2 << "reachable#machine = false;" << EOL;
	}

	if( hasBackwardReachableMachine() )
	{
		out << TAB << "reachable#backward#machine:" << EOL;

		ListOfInstanceOfMachine::const_iterator itMachine =
				getBackwardReachableMachine().begin();
		ListOfInstanceOfMachine::const_iterator endMachine =
				getBackwardReachableMachine().end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			out << TAB2 << str_header( *itMachine ) << ";" << EOL;
		}
	}

	if( hasBackwardReachableTransition() )
	{
		out << TAB << "reachable#backward#transition:" << EOL;

		OutStream osHierarchy( out );
		osHierarchy.INDENT.CHAR = " ";

		ListOfAvmTransition::const_iterator itProg =
				getBackwardReachableTransition().begin();
		ListOfAvmTransition::const_iterator endProg =
				getBackwardReachableTransition().end();
		for( ; itProg != endProg ; ++itProg )
		{
			out << TAB2 << str_header( *itProg ) << ";" << EOL;
		}
	}


	if( hasForwardReachableMachine() )
	{
		out << TAB << "reachable#forward#machine:" << EOL;

		OutStream osHierarchy( out );
		osHierarchy.INDENT.CHAR = " ";

		ListOfInstanceOfMachine::const_iterator itMachine =
				getForwardReachableMachine().begin();
		ListOfInstanceOfMachine::const_iterator endMachine =
				getForwardReachableMachine().end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			out << TAB2 << str_header( *itMachine ) << ";" << EOL;
		}
	}

	if( hasForwardReachableTransition() )
	{
		out << TAB << "reachable#forward#transition:" << EOL;

		OutStream osHierarchy( out );
		osHierarchy.INDENT.CHAR = " ";

		ListOfAvmTransition::const_iterator itProg =
				getForwardReachableTransition().begin();
		ListOfAvmTransition::const_iterator endProg =
				getForwardReachableTransition().end();
		for( ; itProg != endProg ; ++itProg )
		{
			out << TAB2 << str_header( *itProg ) << ";" << EOL;
		}
	}


	out << TAB << "moe:" << EOL;

	if( hasOnCreate() )
	{
		out << TAB2 << "@create{" << INCR2_INDENT;
		getOnCreate()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnInit() )
	{
		out << TAB2 << "@init{" << INCR2_INDENT;
		getOnInit()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnReturn() )
	{
		out << TAB2 << "@return{" << INCR2_INDENT;
		getOnReturn()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnFinal() )
	{
		out << TAB2 << "@final{" << INCR2_INDENT;
		getOnFinal()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnStart() )
	{
		out << TAB2 << "@start{" << INCR2_INDENT;
		getOnStart()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnStop() )
	{
		out << TAB2 << "@stop{" << INCR2_INDENT;
		getOnStop()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnIEnable() )
	{
		out << TAB2 << "@ienable{" << INCR2_INDENT;
		getOnIEnable()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnEnable() )
	{
		out << TAB2 << "@enable{" << INCR2_INDENT;
		getOnEnable()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnIDisable() )
	{
		out << TAB2 << "@idisable{" << INCR2_INDENT;
		getOnIDisable()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnDisable() )
	{
		out << TAB2 << "@disable{" << INCR2_INDENT;
		getOnDisable()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnIAbort() )
	{
		out << TAB2 << "@iabort{" << INCR2_INDENT;
		getOnIAbort()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnAbort() )
	{
		out << TAB2 << "@abort{" << INCR2_INDENT;
		getOnAbort()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnIRun() )
	{
		out << TAB2 << "@irun{" << INCR2_INDENT;
		getOnIRun()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnRun() )
	{
		out << TAB2 << "@run{" << INCR2_INDENT;
		getOnRun()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnRtc() )
	{
		out << TAB2 << "@rtc{" << INCR2_INDENT;
		getOnRtc()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasOnSchedule() )
	{
		out << TAB2 << "@"
				<< ( getSpecifier().hasFeatureUserDefinedSchedule()? "x" : "" )
				<< "schedule"
				<< (isMutableSchedule() ? "" : "< final >")
				<< "{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}
	else if( isMutableSchedule() )
	{
		out << TAB2 << "@schedule#mutable{ }" << EOL;
	}


	if( hasOnConcurrency() )
	{
		out << TAB2 << "@concurrency{";
		if( getOnConcurrency()->noOperand() )
		{
			out << " " << getOnConcurrencyOperator()->strOp() << " ";
		}
		else
		{
			getOnConcurrency()->toStreamRoutine( out << INCR2_INDENT )
					<< DECR2_INDENT_TAB2;
		}
		out << "}" << EOL;
	}


	if( hasOnSynchronize() )
	{
		out << TAB2 << "@synchronize{" << INCR2_INDENT;
		getOnSynchronize()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	if( hasStatementFamily() )
	{
		out << TAB2 << "opcode#family = " << strStatementFamily() << ";" << EOL;
	}

	// static class of Port/Message/Signal in communicated transition
	out << INCR_INDENT;
	toStreamStaticCom(out);
	out << DECR_INDENT;

	out << TAB << "}" << EOL << std::flush;
}


}

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Machine.h"

#include <fml/type/TypeManager.h>

#include <fml/infrastructure/Buffer.h>
#include <fml/infrastructure/Channel.h>
#include <fml/infrastructure/Connector.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/Variable.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/InstanceSpecifierPart.h>
#include <fml/infrastructure/InteractionPart.h>
#include <fml/infrastructure/ModelOfComputationPart.h>
#include <fml/infrastructure/PropertyPart.h>


namespace sep
{

////////////////////////////////////////////////////////////////////////////////
// MACHINE POINTER
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// MACHINE SMART POINTER
////////////////////////////////////////////////////////////////////////////////

/**
 * CONSTRUCTOR
 * Default
 */
Machine::Machine(Machine * aContainer,
		const std::string & aNameID, const Specifier & aMocSpecifier)
: BehavioralElement(CLASS_KIND_T( Machine ), aContainer, aNameID),
SpecifierImpl( aMocSpecifier ),

mGroupId( ),
mOwnedElements( ),
mOwnedElementsSpecifier( ),
mModel( ),

mPropertyDeclaration( this , "property" ),

mModelOfComputation( NULL ),

mCompositeSpecification( new CompositePart(this, "composite") ),

mInteractionSpecification( NULL ),
mBehavioralSpecification( NULL ),
mInstanceSpecifier( new InstanceSpecifierPart(this, "instance") )
{
	//!! NOTHING
}


/**
 * CONSTRUCTOR
 * Other
 */
Machine::Machine(Machine * aContainer, const std::string & aNameID,
		const Specifier & aMocSpecifier, const BF & aModel,
		avm_size_t anInitialInstanceCount, avm_size_t aMaximalInstanceCount)
: BehavioralElement(CLASS_KIND_T( Machine ), aContainer, aNameID),
SpecifierImpl( aMocSpecifier ),

mGroupId( ),
mOwnedElements( ),
mOwnedElementsSpecifier( ),
mModel( aModel ),

mPropertyDeclaration( this , "property" ),

mModelOfComputation( NULL ),

mCompositeSpecification( new CompositePart(this, "composite") ),

mInteractionSpecification( NULL ),
mBehavioralSpecification( NULL ),
mInstanceSpecifier( new InstanceSpecifierPart(this, aModel,
		anInitialInstanceCount, aMaximalInstanceCount, "instance") )
{
	//!! NOTHING
}

Machine::Machine(class_kind_t aClassKind, Machine * aContainer,
		const std::string & aFullyQualifiedNameID, const std::string & aNameID,
		const std::string & name, const Specifier & aMocSpecifier)
: BehavioralElement(aClassKind, aContainer, aFullyQualifiedNameID, aNameID, name),
SpecifierImpl( aMocSpecifier ),

mGroupId( ),
mOwnedElements( ),
mOwnedElementsSpecifier( ),
mModel( ),

mPropertyDeclaration( this , "property" ),

mModelOfComputation( NULL ),

mCompositeSpecification( new CompositePart(this, "composite") ),

mInteractionSpecification( NULL ),
mBehavioralSpecification( NULL ),
mInstanceSpecifier( new InstanceSpecifierPart(this, "instance") )
{
	//!! NOTHING
}


/**
 * DESTRUCTOR
 */
Machine::~Machine()
{
	delete mModelOfComputation;
	delete mCompositeSpecification;
	delete mInteractionSpecification;
	delete mBehavioralSpecification;
	delete mInstanceSpecifier;
}


/**
 * SETTER
 * mGroupId
 */
void Machine::setGroupId()
{
	if( getSpecifier().hasGroupMask() )
	{
		StringOutStream oss;

		oss << ( getSpecifier().isGroupEvery() ? "[*" :
				( getSpecifier().isGroupExcept() ? "[^" : "[" ) );
		if( mGroupId.nonempty() )
		{
			ListOfString::const_iterator it = mGroupId.begin();
			ListOfString::const_iterator endIt = mGroupId.end();
			oss << (*it);
			for( ++it ; it != endIt ; ++it)
			{
				oss << " , " << (*it);
			}
		}
		oss << "]";

		fullyUpdateAllNameID( oss.str() );
	}
}

void Machine::expandGroupStatemachine()
{
	if( mCompositeSpecification != NULL )
	{
		mCompositeSpecification->expandGroupStatemachine();
	}
}


/**
 * GETTER
 * the machine container
 * LC[R]A
 */
const Machine * Machine::LCA(const Machine * aMachine) const
{
	List< const Machine * > containerListOfThis;
	const Machine * itContainer = this->getContainerMachine();
	for ( ; itContainer != NULL ;
			itContainer = itContainer->getContainerMachine() )
	{
		containerListOfThis.push_back(itContainer);
	}

	List< const Machine * >::iterator it;
	List< const Machine * >::iterator endIt = containerListOfThis.end();
	itContainer = aMachine->getContainerMachine();
	for ( ; itContainer != NULL ;
			itContainer = itContainer->getContainerMachine() )
	{
		for ( it = containerListOfThis.begin() ; it != endIt ; ++it )
		{
			if ( (*it) == itContainer )
			{
//				AVM_OS_LOG << "LCA( " << this->getFullyQualifiedNameID()
//						<< " , " << aMachine->getFullyQualifiedNameID()
//						<< " ) = " << itContainer->getFullyQualifiedNameID();

				return( itContainer );
			}
		}
	}

	return( NULL );
}



/**
 * DISPATCH
 * mOwnedElements
 */
void Machine::dispatchOwnedElement(const BF & anElement)
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anElement )
			<< "Executable Machine owned element !!!"
			<< SEND_EXIT;

	switch( anElement.classKind() )
	{
		// PROPERTY ELEMENT
		case FORM_XFSP_VARIABLE_KIND:
		case FORM_XFSP_DATATYPE_KIND:
		case FORM_XFSP_BUFFER_KIND:
		case FORM_XFSP_CHANNEL_KIND:
		case FORM_XFSP_PORT_KIND:
		{
			mPropertyDeclaration.dispatchOwnedElement( anElement );
			break;
		}

		// COMPOSITE STRUCTURE ELEMENT

		case FORM_XFSP_MACHINE_KIND:
		{
			addOwnedElementSpecifier(
					anElement.to_ptr< Machine >()->getSpecifier() );

			getUniqCompositePart()->dispatchOwnedElement( anElement );

			break;
		}

		case FORM_XFSP_TRANSITION_KIND:
		{
			getUniqBehaviorPart()->appendOutgoingTransition( anElement );
			break;
		}

		// INTERACTION ELEMENT
		case FORM_XFSP_CONNECTOR_KIND:
		{
			getUniqInteraction()->appendConnector( anElement );
			break;
		}

		// BEHAVIORAL ELEMENT
		case FORM_XFSP_ROUTINE_KIND:
		{
			getUniqBehaviorPart()->appendRoutine( anElement );
			break;
		}


		case FORM_XFSP_PACKAGE_KIND:

		default:
		{ // TODO
			AVM_OS_FATAL_ERROR_EXIT
					<< "dispatchOwnedElement() unexpected object, typeinfo: "
					<< anElement.classKindInfo() << "\n\t<< "
					<< anElement.to_ptr< ObjectElement >()->strHeader()
					<< " >> !!!"
					<< SEND_EXIT;
			break;
		}
	}
}


/**
 * GETTER - SETTER
 * mModelOfComputation
 */
ModelOfComputationPart * Machine::getUniqModelOfComputation()
{
	if( mModelOfComputation == NULL )
	{
		mModelOfComputation = new ModelOfComputationPart(this, "moc");
	}

	return( mModelOfComputation );
}

/**
 * GETTER - SETTER
 * mCompositeSpecification
 */
CompositePart * Machine::getUniqCompositePart()
{
	if( mCompositeSpecification == NULL )
	{
		mCompositeSpecification = new CompositePart(this, "composite");
	}

	return( mCompositeSpecification );
}


/**
 * GETTER - SETTER
 * mCompositeSpecification->mProcedures
 */
bool Machine::hasProcedure() const
{
	return( (mCompositeSpecification != NULL) &&
			mCompositeSpecification->hasProcedure() );
}

void Machine::saveProcedure(Machine * aProcedure)
{
	mCompositeSpecification->saveProcedure( aProcedure );
}

/**
 * GETTER - SETTER
 * mCompositeSpecification->mStates
 */
bool Machine::hasState() const
{
	return( (mCompositeSpecification != NULL) &&
			mCompositeSpecification->hasState() );
}


/**
 * GETTER - SETTER
 * mCompositeSpecification->mMachines
 */
bool Machine::hasMachine() const
{
	return( (mCompositeSpecification != NULL) &&
			mCompositeSpecification->hasMachine() );
}

void Machine::saveMachine(Machine * aMachine)
{
	mCompositeSpecification->saveMachine( aMachine );
}


/**
 * GETTER - SETTER
 * mInteractionSpecification
 */
InteractionPart * Machine::getUniqInteraction()
{
	if( mInteractionSpecification == NULL )
	{
		mInteractionSpecification = new InteractionPart(this, "com");
	}

	return( mInteractionSpecification );
}


/**
 * GETTER - SETTER
 * mBehavioralSpecification
 */
BehavioralPart * Machine::getUniqBehaviorPart()
{
	if( mBehavioralSpecification == NULL )
	{
		mBehavioralSpecification = new BehavioralPart(this, "moe");
	}

	return( mBehavioralSpecification );
}


bool Machine::hasRunnableBehavior() const
{
	return( (mBehavioralSpecification != NULL)
			&& (mBehavioralSpecification->hasOnRun()
				|| mBehavioralSpecification->hasOnSchedule()
				|| mBehavioralSpecification->hasOnConcurrency()) );
}

bool Machine::hasOnEnable() const
{
	return( ( (mBehavioralSpecification != NULL)
				&& mBehavioralSpecification->hasOnEnable() )
			|| getSpecifier().hasPseudostateHistory() );
}

bool Machine::isInlinableEnable() const
{
	return( (not getSpecifier().isPseudostate())
			&& (mBehavioralSpecification != NULL)
			&& (mBehavioralSpecification->hasOnEnable()
				|| mBehavioralSpecification->hasOnIEnable()) );
}


/**
 * GETTER - SETTER
 * mBehavioralSpecification->mOutgoingTransitions
 * mBehavioralSpecification->mIncomingTransitions
 */
bool Machine::hasOutgoingTransition() const
{
	return( (mBehavioralSpecification != NULL)
			&& mBehavioralSpecification->hasOutgoingTransition() );
}

bool Machine::hasIncomingTransition() const
{
	return( (mBehavioralSpecification != NULL)
			&& mBehavioralSpecification->hasIncomingTransition() );
}


/**
 * GETTER - SETTER
 * mInstanceSpecifier
 */
InstanceSpecifierPart * Machine::getUniqInstanceSpecifier()
{
	if( mInstanceSpecifier == NULL )
	{
		mInstanceSpecifier = new InstanceSpecifierPart(this, "instance");
	}

	return( mInstanceSpecifier );
}

/**
 * GETTER - SETTER
 * "autostart" modifier of Instance
 */
bool Machine::isAutoStart() const
{
	return( hasInstanceSpecifier()
			&& getInstanceSpecifier()->isAutoStart() );
}

void Machine::setAutoStart(bool bAutoStart)
{
	getUniqInstanceSpecifier()->setAutoStart( bAutoStart );
}


/**
 * GETTER - SETTER
 * mDeclarationParameter
 */
const TableOfVariable & Machine::getVariableParameters() const
{
	return( mPropertyDeclaration.getVariableParameters() );
}

const BF & Machine::getVariableParameter(avm_size_t offset) const
{
	return( mPropertyDeclaration.getVariableParameter(offset) );
}

avm_size_t Machine::getVariableParametersCount() const
{
	return( mPropertyDeclaration.getVariableParametersCount() );
}

avm_offset_t Machine::getVariableParameterOffset(const std::string & aNameID) const
{
	return( mPropertyDeclaration.getVariableParameterOffsetByNameID(aNameID) );
}


/**
 * GETTER - SETTER
 * mDeclarationReturn
 */
const TableOfVariable & Machine::getVariableReturns() const
{
	return( mPropertyDeclaration.getVariableReturns() );
}

const BF & Machine::getVariableReturn(avm_size_t offset) const
{
	return( mPropertyDeclaration.getVariableReturn(offset) );
}

avm_offset_t Machine::getVariableReturnsCount() const
{
	return( mPropertyDeclaration.getVariableReturnsCount() );
}

avm_offset_t Machine::getVariableReturnOffset(const std::string & aNameID) const
{
	return( mPropertyDeclaration.getVariableReturnOffsetByNameID(aNameID) );
}


/**
 * GETTER - SETTER
 * mPropertyPart
 */
bool Machine::hasProperty() const
{
	return( mPropertyDeclaration.nonempty() );
}

bool Machine::hasPortSignal() const
{
	return( mPropertyDeclaration.hasPort()
			|| mPropertyDeclaration.hasSignal() );
}


/**
 * Serialization
 */
void Machine::header(OutStream & os) const
{
	os << getModifier().toString()
			<< getSpecifier().strDesign_not(
					Specifier::DESIGN_PROTOTYPE_STATIC_KIND)
			<< getSpecifier().keywordComponent();

	bool hasChevron = false;

	if( hasSpecifier_otherThan( Specifier(
			getSpecifier().getComponentKind() ).setStateMocSIMPLE() ) )
	{
		Specifier aSpecifier( getSpecifier() );
		aSpecifier.unsetComponentKind();
		aSpecifier.remStateMoc( Specifier::STATE_SIMPLE_MOC );
		aSpecifier.unsetDesignKind();

		if( aSpecifier.isDefined() )
		{
			hasChevron = true;

			os << "< " << aSpecifier.str();
		}
	}

	if( hasOwnedElementsSpecifier() )
	{
		Specifier aSpecifier( getOwnedElementsSpecifier() );
		aSpecifier.unsetDesignKind();

		if( aSpecifier.isDefined() )
		{
			if( hasChevron ) { os << " , "; }
			else { os << "< "; hasChevron = true; }

			os << "owned: " << aSpecifier.str();
		}
	}

	if( hasInstanceSpecifier() )
	{
		mInstanceSpecifier->header(os, hasChevron);
	}

	os << ( hasChevron ? " > " : " " );

	if( getSpecifier().hasGroupMask() )
	{
		os << ( getSpecifier().isGroupEvery() ? "[*" :
				( getSpecifier().isGroupExcept() ? "[^" : "[" ) );
		if( mGroupId.nonempty() )
		{
			ListOfString::const_iterator it = mGroupId.begin();
			ListOfString::const_iterator endIt = mGroupId.end();
			os << (*it);
			for( ++it ; it != endIt ; ++it)
			{
				os << " , " << (*it);
			}
		}
		os << "]";
	}
	else
	{
		os << getNameID();
	}
}


void Machine::strHeader(OutStream & os) const
{
	header( os );

	mPropertyDeclaration.strVariableParameters(os, " [ ", " ]", ", ");

	mPropertyDeclaration.strVariableReturns(os, " returns: [ ", " ]", ", ");
}


void Machine::toStream(OutStream & os) const
{
	os << TAB;

	header( os );

	os << " {" << EOL;

	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	//
	if( mOwnedElements.nonempty() )
	{
		os << TAB << "/*owned: [" << EOL_INCR_INDENT
				<< str_header( mOwnedElements ) << DECR_INDENT_TAB
				<< "] // end owned*/" << EOL2_FLUSH;
	}
	//
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////


	if( hasProperty() )
	{
		mPropertyDeclaration.toStream(os);
		os << EOL;
	}

	if( (mBehavioralSpecification != NULL) &&
		mBehavioralSpecification->hasAnyRoutine() )
	{
		mBehavioralSpecification->toStreamAnyRoutine( os );
	}

	if( mCompositeSpecification != NULL )
	{
		mCompositeSpecification->toStream( os );
	}

	if( mModelOfComputation != NULL )
	{
		mModelOfComputation->toStream(os);
	}

	if( mInteractionSpecification != NULL  )
	{
		mInteractionSpecification->toStream(os);
		os << EOL;
	}

	if( mBehavioralSpecification != NULL  )
	{
		mBehavioralSpecification->toStreamMoe(os);
		os << EOL;
	}

	os << TAB << "}" << EOL_FLUSH;
}


}

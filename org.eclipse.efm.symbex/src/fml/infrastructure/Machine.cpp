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
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/Variable.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/Connector.h>
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
mOwnedElementsSpecifier( ),
mModel( ),

mPropertyDeclaration( this , "property" ),

mModelOfComputation( nullptr ),

mCompositeSpecification( new CompositePart(this, "composite") ),

mInteractionSpecification( nullptr ),
mBehavioralSpecification( nullptr ),
mInstanceSpecifier( new InstanceSpecifierPart(this, "instance") )
{
	//!! NOTHING
}


/**
 * CONSTRUCTOR
 * Instance
 */
Machine::Machine(Machine & aContainer, const std::string & aNameID,
		const Specifier & aMocSpecifier, const BF & aModel,
		std::size_t anInitialInstanceCount, std::size_t aMaximalInstanceCount)
: BehavioralElement(CLASS_KIND_T( Machine ), (& aContainer), aNameID),
SpecifierImpl( aMocSpecifier ),

mGroupId( ),
mOwnedElementsSpecifier( ),
mModel( aModel ),

mPropertyDeclaration( this , "property" ),

mModelOfComputation( nullptr ),

mCompositeSpecification( new CompositePart(this, "composite") ),

mInteractionSpecification( nullptr ),
mBehavioralSpecification( nullptr ),
mInstanceSpecifier( new InstanceSpecifierPart(this, aModel,
		anInitialInstanceCount, aMaximalInstanceCount, "instance") )
{
	//!! NOTHING
}

/**
 * CONSTRUCTOR
 * Other
 */
Machine::Machine(class_kind_t aClassKind, Machine * aContainer,
		const std::string & aFullyQualifiedNameID, const std::string & aNameID,
		const std::string & name, const Specifier & aMocSpecifier)
: BehavioralElement(aClassKind, aContainer, aFullyQualifiedNameID, aNameID, name),
SpecifierImpl( aMocSpecifier ),

mGroupId( ),
mOwnedElementsSpecifier( ),
mModel( ),

mPropertyDeclaration( this , "property" ),

mModelOfComputation( nullptr ),

mCompositeSpecification( new CompositePart(this, "composite") ),

mInteractionSpecification( nullptr ),
mBehavioralSpecification( nullptr ),
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
 * GETTER
 * EXECUTABLE MACHINE COUNT
 */
std::size_t Machine::getExecutableMachineCount() const
{
	return( 1 + mCompositeSpecification->getExecutableMachineCount() );
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
	if( mCompositeSpecification != nullptr )
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
	for ( ; itContainer != nullptr ;
			itContainer = itContainer->getContainerMachine() )
	{
		containerListOfThis.push_back(itContainer);
	}

	List< const Machine * >::iterator it;
	List< const Machine * >::iterator endIt = containerListOfThis.end();
	itContainer = aMachine->getContainerMachine();
	for ( ; itContainer != nullptr ;
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

	return( nullptr );
}



/**
 * DISPATCH
 * mOwnedElements
 */
const BF & Machine::saveOwnedElement(Machine * ptrElement)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( ptrElement )
			<< "Composite owned element !!!"
			<< SEND_EXIT;

	addOwnedElementSpecifier( ptrElement->getSpecifier() );

	return( getUniqCompositePart()->saveOwnedElement(ptrElement) );
}

const BF & Machine::saveOwnedElement(BehavioralElement * ptrElement)
{
	return( getUniqBehaviorPart()->saveOwnedElement(ptrElement) );
}


/**
 * GETTER - SETTER
 * mModelOfComputation
 */
ModelOfComputationPart * Machine::getUniqModelOfComputation()
{
	if( mModelOfComputation == nullptr )
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
	if( mCompositeSpecification == nullptr )
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
	return( (mCompositeSpecification != nullptr) &&
			mCompositeSpecification->hasProcedure() );
}

/**
 * GETTER - SETTER
 * mCompositeSpecification->mStates
 */
bool Machine::hasState() const
{
	return( (mCompositeSpecification != nullptr) &&
			mCompositeSpecification->hasState() );
}

/**
 * GETTER - SETTER
 * mCompositeSpecification->mMachines
 */
bool Machine::hasMachine() const
{
	return( (mCompositeSpecification != nullptr) &&
			mCompositeSpecification->hasMachine() );
}


/**
 * GETTER - SETTER
 * mInteractionSpecification
 */
InteractionPart * Machine::getUniqInteraction()
{
	if( mInteractionSpecification == nullptr )
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
	if( mBehavioralSpecification == nullptr )
	{
		mBehavioralSpecification = new BehavioralPart(this, "moe");
	}

	return( mBehavioralSpecification );
}


bool Machine::hasOwnedBehavior() const
{
	return( (mBehavioralSpecification != nullptr)
			&& mBehavioralSpecification->hasOwnedBehavior() );
}

bool Machine::hasRunnableBehavior() const
{
	return( (mBehavioralSpecification != nullptr)
			&& (mBehavioralSpecification->hasOnRun()
				|| mBehavioralSpecification->hasOnSchedule()
				|| mBehavioralSpecification->hasOnConcurrency()) );
}

bool Machine::hasOnInitMachine() const
{
	return( (mBehavioralSpecification != nullptr)
				&& mBehavioralSpecification->hasOnInitMachine() );
}

bool Machine::hasOnEnable() const
{
	return( ( (mBehavioralSpecification != nullptr)
				&& mBehavioralSpecification->hasOnEnable() )
			|| getSpecifier().hasPseudostateHistory() );
}

bool Machine::isInlinableEnable() const
{
	return( (not getSpecifier().isPseudostate())
			&& (mBehavioralSpecification != nullptr)
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
	return( (mBehavioralSpecification != nullptr)
			&& mBehavioralSpecification->hasOutgoingTransition() );
}

bool Machine::hasIncomingTransition() const
{
	return( (mBehavioralSpecification != nullptr)
			&& mBehavioralSpecification->hasIncomingTransition() );
}


/**
 * GETTER - SETTER
 * mInstanceSpecifier
 */
InstanceSpecifierPart * Machine::getUniqInstanceSpecifier()
{
	if( mInstanceSpecifier == nullptr )
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
 * mDeclarationVariables
 */
const TableOfVariable & Machine::getVariables() const
{
	return( mPropertyDeclaration.getVariables() );
}

/**
 * GETTER - SETTER
 * mDeclarationParameters
 */
const TableOfVariable & Machine::getVariableParameters() const
{
	return( mPropertyDeclaration.getVariableParameters() );
}

TableOfVariable & Machine::getVariableParameters()
{
	return( mPropertyDeclaration.getVariableParameters() );
}

const BF & Machine::getVariableParameter(std::size_t offset) const
{
	return( mPropertyDeclaration.getVariableParameter(offset) );
}

std::size_t Machine::getVariableParametersCount() const
{
	return( mPropertyDeclaration.getVariableParametersCount() );
}

avm_offset_t Machine::getVariableParameterOffset(const std::string & aNameID) const
{
	return( mPropertyDeclaration.getVariableParameterOffsetByNameID(aNameID) );
}


/**
 * GETTER - SETTER
 * mDeclarationReturns
 */
const TableOfVariable & Machine::getVariableReturns() const
{
	return( mPropertyDeclaration.getVariableReturns() );
}

TableOfVariable & Machine::getVariableReturns()
{
	return( mPropertyDeclaration.getVariableReturns() );
}

const BF & Machine::getVariableReturn(std::size_t offset) const
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
void Machine::header(OutStream & out) const
{
	out << getSpecifier().strFeature(" ")
		<< getModifier().toString()
		<< getSpecifier().strDesign_not(Specifier::DESIGN_PROTOTYPE_STATIC_KIND)
		<< getSpecifier().keywordComponent();

	bool hasChevron = false;

	if( hasSpecifier_otherThan( Specifier(
			getSpecifier().getComponentKind() ).setStateMocSIMPLE() ) )
	{
		Specifier aSpecifier( getSpecifier() );
		aSpecifier.unsetComponentKind();
		aSpecifier.remStateMoc( Specifier::STATE_SIMPLE_MOC );
		aSpecifier.unsetDesignKind();
		aSpecifier.unsetFeatureKind();

		if( aSpecifier.isDefined() )
		{
			hasChevron = true;

			out << "< " << aSpecifier.str();
		}
	}
	
	if( hasInstanceSpecifier()  )
	{
		mInstanceSpecifier->header(out, hasChevron);
	}

	out << ( hasChevron ? " > " : " " );

	if( getSpecifier().hasGroupMask() )
	{
		out << ( getSpecifier().isGroupEvery() ? "[*" :
				( getSpecifier().isGroupExcept() ? "[^" : "[" ) );
		if( mGroupId.nonempty() )
		{
			ListOfString::const_iterator it = mGroupId.begin();
			ListOfString::const_iterator endIt = mGroupId.end();
			out << (*it);
			for( ++it ; it != endIt ; ++it)
			{
				out << " , " << (*it);
			}
		}
		out << "]";
	}
	else
	{
		out << getNameID();
	}
}


void Machine::strHeader(OutStream & out) const
{
	header( out );

	mPropertyDeclaration.strVariableParameters(out, " [ ", " ]", ", ");

	mPropertyDeclaration.strVariableReturns(out, " returns: [ ", " ]", ", ");
}


void Machine::headerDebug(OutStream & out) const
{
	bool hasChevron = false;

	out << "//" << getSpecifier().strFeature(" ") << getModifier().toString()
		<< getSpecifier().strDesign_not(Specifier::DESIGN_PROTOTYPE_STATIC_KIND)
		<< getSpecifier().keywordComponent();

	if( hasOwnedElementsSpecifier() )
	{
		Specifier aSpecifier( getOwnedElementsSpecifier() );
		aSpecifier.unsetDesignKind();
		aSpecifier.unsetFeatureKind();

		if( aSpecifier.isDefined() )
		{
			hasChevron = true;
			out << " < owned: " << aSpecifier.str();
		}
	}

	if( hasInstanceSpecifier() )
	{
		mInstanceSpecifier->header(out, hasChevron);
	}

	if( hasChevron )
	{
		out << " >" << EOL;
		hasChevron = false;
	}
}

void Machine::toStream(OutStream & out) const
{
AVM_IF_DEBUG_FLAG2( COMPILING , STATEMACHINE )
	if( hasOwnedElementsSpecifier() )
	{
		out << TAB;
		headerDebug( out );
	}
AVM_ENDIF_DEBUG_FLAG2( COMPILING , STATEMACHINE )

	out << TAB;

	header( out );

	if( hasReallyUnrestrictedName() )
	{
		out << " \"" << getUnrestrictedName() << "\"";
	}

	out << " {";

	if( hasProperty() )
	{
		out << EOL;
		mPropertyDeclaration.toStream(out);
	}

	if( (mBehavioralSpecification != nullptr) &&
		mBehavioralSpecification->hasAnyRoutine() )
	{
		out << EOL;
		mBehavioralSpecification->toStreamAnyRoutine( out );
	}

	if( mCompositeSpecification != nullptr )
	{
		mCompositeSpecification->toStream( out );
	}

	if( mModelOfComputation != nullptr )
	{
		out << EOL;
		mModelOfComputation->toStream(out);
	}

	if( mInteractionSpecification != nullptr  )
	{
		out << EOL;
		mInteractionSpecification->toStream(out);
	}

	if( mBehavioralSpecification != nullptr  )
	{
		out << EOL;
		mBehavioralSpecification->toStreamMoe(out);
	}

	if( (not hasProperty())
		&& ((mBehavioralSpecification  == nullptr)
			|| mBehavioralSpecification->empty())
		&& ((mCompositeSpecification   == nullptr)
			|| mCompositeSpecification->empty())
		&& (mModelOfComputation        == nullptr)
		&& ((mInteractionSpecification == nullptr)
			|| mInteractionSpecification->empty()) )
	{
		out << EOL;
	}

	out << TAB << "}" << EOL_FLUSH;
}


}

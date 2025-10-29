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

#ifndef MACHINE_H_
#define MACHINE_H_

#include <fml/infrastructure/MachineQuery.h>

#include <fml/common/BehavioralElement.h>
#include <fml/common/SpecifierElement.h>

#include <common/BF.h>

#include <collection/BFContainer.h>
#include <collection/Typedef.h>

#include <fml/common/ObjectElement.h>

//#include <fml/infrastructure/BehavioralPart.h>
//#include <fml/infrastructure/CompositePart.h>
//#include <fml/infrastructure/InteractionPart.h>
//#include <fml/infrastructure/ModelOfComputationPart.h>
#include <fml/infrastructure/PropertyPart.h>


namespace sep
{

class BehavioralPart;

class CompositePart;

class InstanceSpecifierPart;
class InteractionPart;

class ModelOfComputationPart;

class PropertyPart;

class Transition;


////////////////////////////////////////////////////////////////////////////////
// MACHINE POINTER
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// MACHINE SMART POINTER
////////////////////////////////////////////////////////////////////////////////

class Machine :
		public MachineQuery,
		public BehavioralElement,
		public SpecifierImpl,
		AVM_INJECT_STATIC_NULL_REFERENCE( Machine ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Machine )
{

	AVM_DECLARE_CLONABLE_CLASS( Machine )

protected:
	/**
	 * ATTRIBUTES
	 */
	ListOfString mGroupId;

	Specifier mOwnedElementsSpecifier;

	BF mModel;

	PropertyPart             mPropertyDeclaration;

	ModelOfComputationPart * mModelOfComputation;

	CompositePart          * mCompositeSpecification;

	InteractionPart        * mInteractionSpecification;

	BehavioralPart         * mBehavioralSpecification;

	InstanceSpecifierPart  * mInstanceSpecifier;

public:
	/**
	 * CONSTRUCTOR
	 * Executable
	 */
	Machine(Machine * aContainer, const std::string & aNameID,
			const Specifier & aMocSpecifier);

	/**
	 * CONSTRUCTOR
	 * Instance
	 */
	Machine(Machine & aContainer, const std::string & aNameID,
			const Specifier & aMocSpecifier, const BF & model,
			std::size_t anInitialInstanceCount = 1,
			std::size_t aMaximalInstanceCount = AVM_NUMERIC_MAX_SIZE_T);

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	Machine(class_kind_t aClassKind, Machine * aContainer,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID, const std::string & name,
			const Specifier & aMocSpecifier);


	/**
	 * DESTRUCTOR
	 */
	virtual ~Machine();


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static Machine & nullref()
	{
		static Machine _NULL_(nullptr, "$null<Machine>",
				Specifier::OBJECT_NULL_SPECIFIER );
		_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );
		_NULL_.setSpecifier( Specifier::OBJECT_NULL_SPECIFIER );

		return( _NULL_ );
	}


	/**
	 * API
	 * MachineQuery
	 */
	inline virtual const Machine * thisMachine() const override
	{
		return( this );
	}


	/**
	 * CONSTRUCTOR
	 * executable
	 */
	inline static Machine * newExecutable(Machine * aContainer,
			const std::string & aNameID, Specifier aMocSpecifier)
	{
		if( aMocSpecifier.noneComponentKind() )
		{
			aMocSpecifier.setComponentExecutable();
		}
		if( aMocSpecifier.noneDesignKind() )
		{
			aMocSpecifier.setDesignPrototypeStatic();
		}

		return( new Machine(aContainer, aNameID, aMocSpecifier) );
	}


	/**
	 * CONSTRUCTOR
	 * Statemachine
	 */
	inline static Machine * newState(Machine * aContainer,
			const std::string & aNameID, Specifier aMocSpecifier)
	{
		if( aMocSpecifier.noneDesignKind() )
		{
			aMocSpecifier.setDesignPrototypeStatic();
		}

		aMocSpecifier.hasPseudostateMoc()
				? aMocSpecifier.setComponentPseudostate()
				: aMocSpecifier.setComponentState();

		return( new Machine(aContainer, aNameID, aMocSpecifier) );
	}

	inline static Machine * newState(Machine * aContainer,
			const std::string & aNameID, Specifier aMocSpecifier,
			const std::string & anUnrestrictedName)
	{
		if( aMocSpecifier.noneDesignKind() )
		{
			aMocSpecifier.setDesignPrototypeStatic();
		}

		aMocSpecifier.hasPseudostateMoc()
				? aMocSpecifier.setComponentPseudostate()
				: aMocSpecifier.setComponentState();

		Machine * aState = new Machine(aContainer, aNameID, aMocSpecifier);
		aState->setUnrestrictedName(anUnrestrictedName);

		return( aState );
	}


	inline static Machine * newPseudostate(Machine * aContainer,
			const std::string & aNameID, Specifier aMocSpecifier)
	{
		if( aMocSpecifier.noneDesignKind() )
		{
			aMocSpecifier.setDesignPrototypeStatic();
		}

		return( new Machine(aContainer, aNameID,
				aMocSpecifier.setComponentPseudostate() ) );
	}

	inline static Machine * newStatemachine(Machine * aContainer,
			const std::string & aNameID, Specifier aMocSpecifier)
	{
		if( aMocSpecifier.noneDesignKind() )
		{
			aMocSpecifier.setDesignPrototypeStatic();
		}

		return( new Machine(aContainer, aNameID,
				aMocSpecifier.setComponentStatemachine() ) );
	}
  


	/**
	 * CONSTRUCTOR
	 * Instance
	 */
	static Machine * newInstance(Machine * aContainer,
			const std::string & aNameID, const BF & aModel,
			std::size_t anInitialInstanceCount = 1,
			std::size_t aMaximalInstanceCount = AVM_NUMERIC_MAX_SIZE_T)
	{
		Specifier aSpecifier(
				Specifier::COMPONENT_EXECUTABLE_KIND,
				Specifier::DESIGN_INSTANCE_STATIC_KIND);

		return( new Machine((* aContainer), aNameID, aSpecifier, aModel,
				anInitialInstanceCount, aMaximalInstanceCount) );
	}


	/**
	 * CONSTRUCTOR
	 * Procedure
	 */
	inline static Machine * newProcedure(
			Machine * aContainer, const std::string & aNameID,
			const Specifier & aMocSpecifier)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aMocSpecifier.isComponentProcedure() )
				<< "Machine::newProcedure:> Unexpected Specifier << "
				<< aMocSpecifier.str() << " >> !!!"
				<< SEND_EXIT;

		return( new Machine(aContainer, aNameID, aMocSpecifier ) );
	}

	inline static Machine * newProcedureInstance(Machine * aContainer,
			const std::string & aNameID, const BF & aModel)
	{
		return( new Machine((* aContainer), aNameID,
				Specifier::EXECUTABLE_PROCEDURE_INSTANCE_STATIC_SPECIFIER,
				aModel) );
	}


	/**
	 * GETTER
	 * EXECUTABLE MACHINE COUNT
	 */
	std::size_t getExecutableMachineCount() const;


	/**
	 * GETTER
	 * the machine container
	 * LC[R]A
	 */
	inline virtual Machine * getContainerMachine() const override
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isContainerMachine() )
				<< "Invalid << Machine Container >> Type <"
				<< (hasContainer() ?
						getContainer()->classKindName() : "$null<container>")
				<< "> Cast !!!"
				<< SEND_EXIT;

		return( getContainer()->to_ptr< Machine >() );
	}

	const Machine * LCA(const Machine * aMachine) const;

	inline const Machine * LCRA(const Machine * aMachine) const
	{
		return( (this == aMachine) ? this : LCA( aMachine ) );
	}


	/**
	 * GETTER - DISPATCH - SAVE
	 */
	inline const BF & saveOwnedElement(PropertyElement * ptrElement)
	{
		return( mPropertyDeclaration.saveOwnedElement( ptrElement ) );
	}

	const BF & saveOwnedElement(Machine * ptrElement);

	const BF & saveOwnedElement(BehavioralElement * ptrElement);


	/**
	 * GETTER
	 * mOwnedElementsSpecifier
	 */
	inline const Specifier & getOwnedElementsSpecifier() const
	{
		return( mOwnedElementsSpecifier );
	}

	inline bool hasOwnedElementsSpecifier() const
	{
		return( mOwnedElementsSpecifier.isDefined() );
	}

	inline void addOwnedElementSpecifier(const Specifier & ownedSpecifier)
	{
		mOwnedElementsSpecifier |= ownedSpecifier;
	}


	/**
	 * GETTER - SETTER
	 * the Type Specifier
	 */
	inline const BF & getType() const
	{
		return( mModel );
	}

	inline BF & getType()
	{
		return( mModel );
	}

	inline bool hasType() const
	{
		return( mModel.valid() );
	}

	inline std::string strType() const
	{
		return( mModel.is< Machine >() ?
				mModel.to< Machine >().getFullyQualifiedNameID() :
				mModel.str() );
	}


	/**
	  * GETTER
	 * the machine type model
	 */
	inline const Machine * getModelMachine() const
	{
		if( getSpecifier().hasDesignModel() )
		{
			return( this );
		}
		else //if( isDesignInstance() )
		{
			return( mModel.is< Machine >() ?
					mModel.to_ptr< Machine >() : nullptr );
		}
	}

	inline bool hasModelMachine() const
	{
		return( getSpecifier().hasDesignModel()
				|| (getSpecifier().hasDesignInstance()
					&& mModel.is< Machine >()) );
	}


	/**
	  * GETTER - TEST
	 * MachineMocKindImpl
	 */
	inline bool isFamilyComponentComposite() const
	{
		return( getSpecifier().isFamilyComponentComposite()
				|| (mModel.valid() && mModel.is_exactly< Machine >()
					&& mModel.to< Machine >().isFamilyComponentComposite()) );
	}


	/**
	 * GETTER - SETTER
	 * mDeclarationVariable
	 */
	const TableOfVariable & getVariables() const;

	/**
	 * GETTER - SETTER
	 * mDeclarationParameter
	 */
	const TableOfVariable & getVariableParameters() const;

	TableOfVariable & getVariableParameters();

	const BF & getVariableParameter(std::size_t offset) const;

	std::size_t getVariableParametersCount() const;

	avm_offset_t getVariableParameterOffset(const std::string & aNameID) const;

	inline bool hasVariableParameter() const
	{
		return( getVariableParametersCount() > 0 );
	}


	/**
	 * GETTER - SETTER
	 * mDeclarationReturn
	 */
	const TableOfVariable & getVariableReturns() const;

	TableOfVariable & getVariableReturns();

	const BF & getVariableReturn(std::size_t offset) const;

	avm_offset_t getVariableReturnsCount() const;

	avm_offset_t getVariableReturnOffset(const std::string & aNameID) const;

	inline bool hasVariableReturn() const
	{
		return( getVariableReturnsCount() > 0 );
	}


	/**
	 * GETTER
	 * mDeclarationParameter
	 * mDeclarationReturn
	 */
	inline avm_offset_t getParamReturnCount() const
	{
		return( getVariableParametersCount() + getVariableReturnsCount() );
	}

	inline bool hasParamReturn() const
	{
		return( getParamReturnCount() > 0 );
	}

	/**
	 * GETTER - SETTER
	 * mPropertyPart
	 */
	inline virtual const PropertyPart & getPropertyPart() const override final
	{
		return( mPropertyDeclaration );
	}

	inline PropertyPart & getPropertyPart()
	{
		return( mPropertyDeclaration );
	}


	bool hasProperty() const;

	bool hasPortSignal() const;

	/**
	 * GETTER
	 * Time Variable
	 */
	inline Variable * getTimeVariable() const
	{
		for( const Machine * machine = this ; (machine != nullptr) ;
				machine = machine->getContainerMachine() )
		{
			if( machine->mPropertyDeclaration.hasTimeVariable() )
			{
				return( machine->mPropertyDeclaration.getTimeVariable() );
			}
		}

		return( nullptr );
	}

	inline const BF & exprTimeVariable() const
	{
		for( const Machine * machine = this ; (machine != nullptr) ;
				machine = machine->getContainerMachine() )
		{
			if( machine->getPropertyPart().hasTimeVariable() )
			{
				return( machine->mPropertyDeclaration.exprTimeVariable() );
			}
		}

		return( BF::REF_NULL );
	}


	/**
	 * GETTER
	 * Delta Time Variable
	 */
	inline Variable * getDeltaTimeVariable() const
	{
		for( const Machine * machine = this ; (machine != nullptr) ;
				machine = machine->getContainerMachine() )
		{
			if( machine->mPropertyDeclaration.hasDeltaTimeVariable() )
			{
				return( machine->mPropertyDeclaration.getDeltaTimeVariable() );
			}
		}

		return( nullptr );
	}


	inline const BF & exprDeltaTimeVariable() const
	{
		for( const Machine * machine = this ; (machine != nullptr) ;
				machine = machine->getContainerMachine() )
		{
			if( machine->mPropertyDeclaration.hasDeltaTimeVariable() )
			{
				return( machine->mPropertyDeclaration.exprDeltaTimeVariable() );
			}
		}

		return( BF::REF_NULL );
	}


	/**
	 * GETTER - SETTER
	 * mGroupId
	 */
	inline const ListOfString & getGroupId() const
	{
		return( mGroupId );
	}

	bool hasGroupId() const
	{
		return( mGroupId.empty() );
	}

	inline void appendGroupId(const std::string & aNameID)
	{
		mGroupId.append(aNameID);
	}

	void setGroupId();

	void expandGroupStatemachine();


	/**
	 * GETTER - SETTER
	 * mModelOfComputation
	 */
	inline ModelOfComputationPart * getModelOfComputation()
	{
		return( mModelOfComputation );
	}

	ModelOfComputationPart * getUniqModelOfComputation();

	inline bool hasModelOfComputation() const
	{
		return( mModelOfComputation != nullptr );
	}


	/**
	 * GETTER - SETTER
	 * mCompositeSpecification
	 */
	inline virtual const CompositePart * getCompositePart() const override final
	{
		return( mCompositeSpecification );
	}

	inline CompositePart * getCompositePart()
	{
		return( mCompositeSpecification );
	}

	CompositePart * getUniqCompositePart();

	inline bool hasCompositePart() const override final
	{
		return( mCompositeSpecification != nullptr );
	}

	/**
	 * GETTER - SETTER
	 * mCompositeSpecification->mProcedures
	 */
	bool hasProcedure() const;

	/**
	 * GETTER - SETTER
	 * mCompositeSpecification->mStates
	 */
	bool hasState() const;

	/**
	 * GETTER - SETTER
	 * mCompositeSpecification->mMachines
	 */
	bool hasMachine() const;

	/**
	 * GETTER - SETTER
	 * mInteractionSpecification
	 */
	inline const InteractionPart * getInteraction() const
	{
		return( mInteractionSpecification );
	}

	InteractionPart * getUniqInteraction();

	inline bool hasInteraction() const
	{
		return( mInteractionSpecification != nullptr );
	}


	/**
	 * GETTER - SETTER
	 * mBehavioralSpecification
	 */
	BehavioralPart * getUniqBehaviorPart();

	inline virtual BehavioralPart * getBehaviorPart() const override final
	{
		return( mBehavioralSpecification );
	}

	inline virtual bool hasBehaviorPart() const override final
	{
		return( mBehavioralSpecification != nullptr );
	}

	inline BehavioralPart * getBehavior() const
	{
		return( mBehavioralSpecification );
	}

	inline bool hasBehavior() const
	{
		return( (mBehavioralSpecification != nullptr)
				/*&& mBehavioralSpecification->nonempty()*/ );
	}

	inline bool noBehavior() const
	{
		return( (mBehavioralSpecification == nullptr)
				/*|| mBehavioralSpecification->empty()*/ );
	}


	bool hasOwnedBehavior() const;

	bool hasRunnableBehavior() const;

	bool hasOnInitMachine() const;

	bool hasOnEnable() const;

	bool isInlinableEnable() const;

	bool isInlinableProcedure() const
	{
		return( true );
	}

	/**
	 * GETTER - SETTER
	 * mBehavioralSpecification->mOutgoingTransitions
	 * mBehavioralSpecification->mIncomingTransitions
	 */
	bool hasOutgoingTransition() const;

	bool hasIncomingTransition() const;


	/**
	 * GETTER - SETTER
	 * mInstanceSpecifier
	 */
	inline InstanceSpecifierPart * getInstanceSpecifier() const
	{
		return( mInstanceSpecifier );
	}

	InstanceSpecifierPart * getUniqInstanceSpecifier();

	inline bool hasInstanceSpecifier() const
	{
		return( mInstanceSpecifier != nullptr );
	}

	/**
	 * GETTER - SETTER
	 * "autostart" modifier of Instance
	 */
	bool isAutoStart() const;

	void setAutoStart(bool bAutoStart = true);


	/**
	 * Serialization
	 */
	void header(OutStream & out) const;

	virtual void strHeader(OutStream & out) const override;

	void headerDebug(OutStream & out) const;

	virtual void toStream(OutStream & out) const override;

};

typedef TableOfBF_T< Machine >  TableOfMachine;



}

#endif /* MACHINE_H_ */

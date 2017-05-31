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

#include <common/AvmPointer.h>
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
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Machine )
{

	AVM_DECLARE_CLONABLE_CLASS( Machine )


public:
	/**
	 * TYPEDEF
	 */
	typedef TableOfBF_T< ObjectElement >  TableOfOwnedElement;

	typedef TableOfOwnedElement::const_raw_iterator  const_owned_iterator;

protected:
	/**
	 * ATTRIBUTES
	 */
	ListOfString mGroupId;

	TableOfOwnedElement mOwnedElements;
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
	Machine(Machine * aContainer, const std::string & aNameID,
			const Specifier & aMocSpecifier, const BF & model,
			avm_size_t anInitialInstanceCount = 1,
			avm_size_t aMaximalInstanceCount = AVM_NUMERIC_MAX_SIZE_T);

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
	 * API
	 * MachineQuery
	 */
	inline virtual const Machine * thisMachine() const
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

	inline static Machine * newPseudotate(Machine * aContainer,
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
			avm_size_t anInitialInstanceCount = 1,
			avm_size_t aMaximalInstanceCount = AVM_NUMERIC_MAX_SIZE_T)
	{
		Specifier aSpecifier(
				Specifier::COMPONENT_EXECUTABLE_KIND,
				Specifier::DESIGN_INSTANCE_STATIC_KIND);

		return( new Machine(aContainer, aNameID, aSpecifier, aModel,
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
		return( new Machine(aContainer, aNameID,
				Specifier::EXECUTABLE_PROCEDURE_INSTANCE_STATIC_SPECIFIER,
				aModel) );
	}


	/**
	 * GETTER
	 * the machine container
	 * LC[R]A
	 */
	inline virtual Machine * getContainerMachine() const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT(
			hasContainer() && getContainer()->is< Machine >() )
				<< "Invalid << Machine Container >> Type <"
				<< (hasContainer() ?
						getContainer()->classKindName() : "null<container>")
				<< "> Cast !!!"
				<< SEND_EXIT;

		return( getContainer()->to< Machine >() );
	}

	const Machine * LCA(const Machine * aMachine) const;

	inline const Machine * LCRA(const Machine * aMachine) const
	{
		return( (this == aMachine) ? this : LCA( aMachine ) );
	}


	/**
	 * GETTER - DISPATCH - SAVE
	 * mOwnedElements
	 */
	inline const TableOfOwnedElement & getOwnedElements() const
	{
		return( mOwnedElements );
	}

	void dispatchOwnedElement(const BF & anElement);

	inline const BF & saveOwnedElement(ObjectElement * ptrElement)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( ptrElement )
				<< "Executable Machine owned element !!!"
				<< SEND_EXIT;

		ptrElement->setOffset( mOwnedElements.size() );

		mOwnedElements.append( INCR_BF( ptrElement ) );

		dispatchOwnedElement( mOwnedElements.last() );

		return( mOwnedElements.last() );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_owned_iterator owned_begin() const
	{
		return( mOwnedElements.begin() );
	}

	inline const_owned_iterator owned_end() const
	{
		return( mOwnedElements.end() );
	}


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

	inline bool hasType() const
	{
		return( mModel.valid() );
	}

	inline std::string strType() const
	{
		return( mModel.is< Machine >() ?
				mModel.to_ptr< Machine >()->getFullyQualifiedNameID() :
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
					mModel.to_ptr< Machine >() : NULL );
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
	inline bool isFamilyMachineComposite() const
	{
		return( getSpecifier().isFamilyComponentComposite()
				|| ( mModel.valid() && mModel.is_exactly< Machine >()
					&& mModel.to_ptr< Machine >()->isFamilyMachineComposite() ) );
	}


	/**
	 * GETTER - SETTER
	 * mDeclarationParameter
	 */
	const TableOfVariable & getVariableParameters() const;

	const BF & getVariableParameter(avm_size_t offset) const;

	avm_size_t getVariableParametersCount() const;

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

	const BF & getVariableReturn(avm_size_t offset) const;

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
	inline virtual const PropertyPart & getPropertyPart() const
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
		return( mModelOfComputation != NULL );
	}


	/**
	 * GETTER - SETTER
	 * mCompositeSpecification
	 */
	inline virtual const CompositePart * getCompositePart() const
	{
		return( mCompositeSpecification );
	}

	inline CompositePart * getCompositePart()
	{
		return( mCompositeSpecification );
	}

	CompositePart * getUniqCompositePart();

	inline bool hasCompositePart() const
	{
		return( mCompositeSpecification != NULL );
	}

	/**
	 * GETTER - SETTER
	 * mCompositeSpecification->mProcedures
	 */
	bool hasProcedure() const;

	void saveProcedure(Machine * aProcedure);

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

	void saveMachine(Machine * aMachine);


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
		return( mInteractionSpecification != NULL );
	}


	/**
	 * GETTER - SETTER
	 * mBehavioralSpecification
	 */
	BehavioralPart * getUniqBehaviorPart();

	inline virtual BehavioralPart * getBehaviorPart() const
	{
		return( mBehavioralSpecification );
	}

	inline virtual bool hasBehaviorPart() const
	{
		return( mBehavioralSpecification != NULL );
	}


	inline BehavioralPart * getBehavior() const
	{
		return( mBehavioralSpecification );
	}

	inline bool hasBehavior() const
	{
		return( (mBehavioralSpecification != NULL)
				/*&& mBehavioralSpecification->nonempty()*/ );
	}

	inline bool noBehavior() const
	{
		return( (mBehavioralSpecification == NULL)
				/*|| mBehavioralSpecification->empty()*/ );
	}


	bool hasRunnableBehavior() const;

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
		return( mInstanceSpecifier != NULL );
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
	void header(OutStream & os) const;

	virtual void strHeader(OutStream & os) const;

	virtual void toStream(OutStream & os) const;

};


}

#endif /* MACHINE_H_ */

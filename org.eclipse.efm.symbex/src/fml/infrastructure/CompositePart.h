/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_INFRASTRUCTURE_COMPOSITEPART_H_
#define FML_INFRASTRUCTURE_COMPOSITEPART_H_

#include <fml/common/ObjectClassifier.h>

#include <collection/BFContainer.h>
#include <collection/Collection.h>

#include <fml/infrastructure/Machine.h>


namespace sep
{


class Machine;


class CompositePart :
		public ObjectClassifier,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( CompositePart )
{

	AVM_DECLARE_CLONABLE_CLASS( CompositePart )


public:
	/**
	 * TYPEDEF
	 */
	typedef TableOfBF_T< BehavioralElement >  TableOfOwnedElement;

	typedef TableOfOwnedElement::const_raw_iterator  const_owned_iterator;

	typedef TableOfBF_T< Machine >  TableOfMachine;

	typedef TableOfMachine::ref_iterator        procedure_iterator;
	typedef TableOfMachine::const_ref_iterator  const_procedure_iterator;

	typedef TableOfMachine::ref_iterator        state_iterator;
	typedef TableOfMachine::const_ref_iterator  const_state_iterator;

	typedef TableOfMachine::ref_iterator        machine_iterator;
	typedef TableOfMachine::const_ref_iterator  const_machine_iterator;

	typedef TableOfMachine::const_ref_iterator  instance_iterator;
	typedef TableOfMachine::const_raw_iterator  const_instance_iterator;

protected:
	/**
	 * ATTRIBUTES
	 */
	TableOfOwnedElement mOwnedElements;

	TableOfMachine mProcedures;

	TableOfMachine mStates;

	TableOfMachine mMachines;

	TableOfMachine mInstanceStatics;

	TableOfMachine mInstanceDynamics;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	CompositePart(Machine * aContainer,
			const std::string & aNameID = "composite")
	: ObjectClassifier( CLASS_KIND_T( CompositePart ) , aContainer , aNameID ),
	mProcedures( ),
	mStates( ),
	mMachines( ),
	mInstanceStatics( ),
	mInstanceDynamics( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~CompositePart()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * EXECUTABLE MACHINE COUNT
	 */
	std::size_t getExecutableMachineCount() const;


	/**
	 * DISPATCH
	 * mOwnedElements
	 */
	void dispatchOwnedElement(BF & anElement);

	inline const BF & saveOwnedElement(BehavioralElement * ptrElement)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( ptrElement )
				<< "Composite owned element !!!"
				<< SEND_EXIT;

		// Should be set by the executable machine container !
		ptrElement->setOwnedOffset( mOwnedElements.size() );

		mOwnedElements.append( INCR_BF( ptrElement ) );

		if( (ptrElement->getContainer() == nullptr)
			|| (ptrElement->getContainer() != this->getContainer()) )
		{
			ptrElement->updateContainer( this->getContainer() );
		}

		dispatchOwnedElement( mOwnedElements.last() );

		return( mOwnedElements.last() );
	}

	inline bool empty() const
	{
		return( mOwnedElements.empty() );
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
	 * GETTER - SETTER
	 * mProcedures
	 */
	inline const TableOfMachine & getProcedures() const
	{
		return( mProcedures );
	}

	inline bool hasProcedure() const
	{
		return( mProcedures.nonempty() );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_procedure_iterator procedure_begin() const
	{
		return( mProcedures.begin() );
	}

	inline const_procedure_iterator procedure_end() const
	{
		return( mProcedures.end() );
	}

	/**
	 * GETTER for PARSER / COMPILER
	 * Procedure
	 */
	inline const BF & getProcedureByNameID(const std::string & aNameID) const
	{
		return( mProcedures.getByNameID(aNameID) );
	}

	inline Machine * rawProcedureByNameID(const std::string & aNameID) const
	{
		return( mProcedures.rawByNameID(aNameID) );
	}


	/**
	 * GETTER - SETTER
	 * mStates
	 */
	inline const TableOfMachine & getStates() const
	{
		return( mStates );
	}

	inline bool hasState() const
	{
		return( mStates.nonempty() );
	}

//	inline void appendState(const BF & aState)
//	{
//		mStates.append( aState );
//	}
//
//	inline void saveState(Machine * aState)
//	{
//		mStates.append( BF(aState) );
//	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline state_iterator state_begin()
	{
		return( mStates.begin() );
	}

	inline state_iterator state_end()
	{
		return( mStates.end() );
	}


	inline const_state_iterator state_begin() const
	{
		return( mStates.begin() );
	}

	inline const_state_iterator state_end() const
	{
		return( mStates.end() );
	}


	/**
	 * GETTER - SETTER
	 * mOutgoingTransitions
	 */
	void appendOutgoingTransitionToEveryState(Machine & aGroupState);

	void appendOutgoingTransitionToSomeState(Machine & aGroupState);

	void appendOutgoingTransitionToExceptState(Machine & aGroupState);

	void expandGroupStatemachine();


	/**
	 * GETTER - SETTER
	 * mMachines
	 */
	inline const TableOfMachine & getMachines() const
	{
		return( mMachines );
	}

	inline bool hasMachine() const
	{
		return( mMachines.nonempty() );
	}

//	inline void appendMachine(const BF & aMachine)
//	{
//		mMachines.append( aMachine );
//	}
//
//	inline void saveMachine(Machine * aMachine)
//	{
//		mMachines.append( BF(aMachine) );
//	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline machine_iterator machine_begin()
	{
		return( mMachines.begin() );
	}

	inline machine_iterator machine_end()
	{
		return( mMachines.end() );
	}


	inline const_machine_iterator machine_begin() const
	{
		return( mMachines.begin() );
	}

	inline const_machine_iterator machine_end() const
	{
		return( mMachines.end() );
	}


	/**
	 * GETTER for PARSER / COMPILER
	 * Machine
	 */
	inline const BF & getMachineByNameID(const std::string & aNameID) const
	{
		return( mMachines.getByNameID(aNameID) );
	}

	inline Machine * rawMachineByNameID(const std::string & aNameID) const
	{
		return( mMachines.rawByNameID(aNameID) );
	}


	inline Machine * rawExecutableMachineByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		return( mMachines.rawByQualifiedNameID(aQualifiedNameID) );
	}


	/**
	 * GETTER - SETTER
	 * mInstanceStatics
	 */
	inline const TableOfMachine & getInstanceStatics() const
	{
		return( mInstanceStatics );
	}

	inline bool hasInstanceStatic() const
	{
		return( mInstanceStatics.nonempty() );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_instance_iterator instance_static_begin() const
	{
		return( mInstanceStatics.begin() );
	}

	inline const_instance_iterator instance_static_end() const
	{
		return( mInstanceStatics.end() );
	}


	/**
	 * GETTER - SETTER
	 * mInstanceDynamics
	 */
	inline const TableOfMachine & getInstanceDynamics() const
	{
		return( mInstanceDynamics );
	}

	inline bool hasInstanceDynamic() const
	{
		return( mInstanceDynamics.nonempty() );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_instance_iterator instance_dynamic_begin() const
	{
		return( mInstanceDynamics.begin() );
	}

	inline const_instance_iterator instance_dynamic_end() const
	{
		return( mInstanceDynamics.end() );
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const override;

};


} /* namespace sep */

#endif /* FML_INFRASTRUCTURE_COMPOSITEPART_H_ */

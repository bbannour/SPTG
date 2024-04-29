/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 janv. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMTRANSITION_H_
#define AVMTRANSITION_H_

#include <fml/executable/AvmProgram.h>

#include <collection/BFContainer.h>
#include <collection/List.h>

#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/AvmCode.h>


namespace sep
{

class AvmTransition;

typedef   List < const AvmTransition * > ListOfAvmTransition;

class ExecutableForm;

class ObjectElement;


class AvmTransition :
		public AvmProgram ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( AvmTransition )
{

	AVM_DECLARE_CLONABLE_CLASS( AvmTransition )

protected:
	/*
	 * ATTRIBUTES
	 */
	// Transition Target machine
	BF mTarget;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmTransition(AvmProgram * aContainer,
			const ObjectElement & astTransition, std::size_t aSize)
	: AvmProgram(CLASS_KIND_T( AvmTransition ),
			Specifier::SCOPE_TRANSITION_KIND, aContainer, astTransition, aSize),
	mTarget( )
	{
		updateFullyQualifiedNameID();
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmTransition()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * theCompiledForm
	 */
	inline const Transition & getAstTransition() const
	{
		return( safeAstElement().as< Transition >() );
	}

	inline bool isAstTransition() const
	{
		return( safeAstElement().is< Transition >() );
	}


	/**
	 * GETTER - SETTER
	 * mTarget machine
	 */
	inline BF & getTarget()
	{
		return( mTarget );
	}

	inline const BF & getTarget() const
	{
		return( mTarget );
	}

	InstanceOfMachine * getTargetMarchine() const;

	inline bool hasTarget() const
	{
		return( mTarget.valid() );
	}

	inline void setTarget(const BF & aTarget)
	{
		mTarget = aTarget;
	}


	std::string strTargetId() const;


	/**
	 * Control flow analysis
	 * source & targets Executable<machine> for Program<transition>
	 */
	ExecutableForm * getTransitionSource() const;


	static InstanceOfMachine * getrecTargetMachine(const AvmCode & aCode);

	inline InstanceOfMachine * getTransitionTarget() const
	{
		if( hasTarget() )
		{
			return( getTargetMarchine() );
		}
		else
		{
			return( hasCode() ? getrecTargetMachine( getAvmCode() ) : nullptr );
		}
	}


	static void getrecTargetMachine(
			ListOfInstanceOfMachine & listOfTargets, const AvmCode & aCode);

	inline void getTransitionTarget(
			ListOfInstanceOfMachine & listOfTargets) const
	{
		if( hasCode() )
		{
			AvmTransition::getrecTargetMachine(listOfTargets, getAvmCode());
		}
	}


	/**
	 * TEST
	 * the source/target machine
	 */
	bool isUnstableSource() const;
	bool isUnstableTarget() const;

	bool isUnstableSourceOrTarget() const;


	/**
	 * Serialization
	 */
	virtual void strHeader(OutStream & out) const override;

	inline std::string strTransitionHeader() const
	{
		StringOutStream oss;

		toStreamHeader( oss );

		return( oss.str() );
	}

	void toStreamHeader(OutStream & out) const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isAstTransition() )
				<< "Unexpected a non Transition program scope !!!"
				<< SEND_EXIT;

		getAstTransition().toStreamHeader(out);
	}


	virtual void toStream(OutStream & out) const override;

	static void toStream(OutStream & out,
			const ListOfAvmTransition & listofTransition);

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// AvmTransition
// TYPE DEFINITION for TABLE , SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

typedef  TableOfBF_T< AvmTransition >  TableOfTransition;


} /* namespace sep */

#endif /* AVMTRANSITION_H_ */

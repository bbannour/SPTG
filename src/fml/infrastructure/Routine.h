/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 déc. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef ROUTINE_H_
#define ROUTINE_H_

#include <fml/common/BehavioralElement.h>
#include <fml/common/SpecifierElement.h>

#include <collection/BFContainer.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementTypeChecker.h>

#include <fml/infrastructure/PropertyPart.h>

#include <fml/operator/Operator.h>


namespace sep
{

class BehavioralPart;

class Machine;

class ObjectElement;

class Variable;


class Routine final :
		public BehavioralElement,
		public SpecifierImpl,
		AVM_INJECT_STATIC_NULL_REFERENCE( Routine ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Routine )
{

	AVM_DECLARE_CLONABLE_CLASS( Routine )

protected:
	/**
	* ATTRIBUTES
	*/
	BF mModel;

	PropertyPart mPropertyDeclaration;

	BFCode mCode;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Routine(Machine & aContainer, const std::string & aNameID,
			const Modifier & aModifier, const Specifier & aSpecifier,
			const BF & aModel = BF::REF_NULL);


	Routine(BehavioralElement & aContainer, const std::string & aNameID,
			const Specifier & aSpecifier =
					Specifier::DESIGN_PROTOTYPE_STATIC_SPECIFIER,
			const BF & aModel = BF::REF_NULL)
	: BehavioralElement( CLASS_KIND_T( Routine ), (& aContainer), aNameID ),
	SpecifierImpl( aSpecifier ),

	mModel( aModel ),

	mPropertyDeclaration( this , "property" ),

	mCode( )
	{
		//!! NOTHING
	}

	Routine(const BehavioralPart & aBehavioralPart,
			const std::string & aNameID,
			const Specifier & aSpecifier =
					Specifier::DESIGN_PROTOTYPE_STATIC_SPECIFIER);


public:
	inline static Routine * newDefine(
			Machine * aContainer, Modifier aModifier,
			Specifier aSpecifier, const std::string & aNameID)
	{

		return( new Routine((* aContainer), aNameID, aModifier,
				aSpecifier.setDesignModel()) );
	}

	static Routine * newDefine(
			Machine & aContainer, const std::string & aNameID);

	inline static Routine * newDefine(
			const BehavioralPart & aBehavioralPart, const std::string & aNameID)
	{

		return( new Routine(aBehavioralPart, aNameID,
				Specifier::DESIGN_MODEL_SPECIFIER) );
	}

	inline static Routine * newInvoke(
			BehavioralElement * aContainer, const std::string & aNameID)
	{
		return( new Routine((* aContainer), aNameID,
				Specifier::DESIGN_INSTANCE_DYNAMIC_SPECIFIER) );
	}

	static Routine * newInvoke(Machine & aContainer, const BF & aModel);


	/**
	 * DESTRUCTOR
	 */
	virtual ~Routine()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	static Routine & nullref();


	/**
	 * GETTER - SETTER
	 * the Type Specifier
	 */
	inline const BF & getType() const
	{
		return( mModel );
	}

	/**
	 * GETTER - SETTER
	 * mModel as Routine Model
	 */
	inline Routine * getModel() const
	{
		return( mModel.as_ptr< Routine >() );
	}

	inline bool hasModel() const
	{
		return( mModel.is< Routine >() );
	}

	inline void setModel(const BF & aModel)
	{
		mModel = aModel;

		if( aModel.is< Routine >() )
		{
			BehavioralElement::setNameID( aModel.to< Routine >().getNameID() );
		}
		else
		{
			BehavioralElement::setNameID( aModel.str() );
		}
	}

	// Model as Invokable Operator
	inline const Operator * getModelOperator() const
	{
		return( mModel.as_ptr< Operator >() );
	}

	inline bool hasModelOperator() const
	{
		return( mModel.is< Operator >() );
	}


	/**
	 * GETTER - SETTER
	 * mPropertyPart
	 */
	inline const PropertyPart & getPropertyPart() const
	{
		return( mPropertyDeclaration );
	}

	inline PropertyPart & getPropertyPart()
	{
		return( mPropertyDeclaration );
	}


	/**
	 * GETTER - SETTER
	 * mCode
	 */
	inline const BFCode & getCode() const
	{
		return( mCode );
	}

	inline BFCode & getCode()
	{
		return( mCode );
	}

	inline bool hasCode() const
	{
		return( mCode.valid() );
	}

	inline bool doSomething() const
	{
		return( mCode.valid() && StatementTypeChecker::doSomething(* mCode) );
	}

	inline void setCode(const BFCode & aCode)
	{
		mCode = aCode;
	}

	inline void seqCode(const BFCode & aCode)
	{
		if( mCode.valid() )
		{
			mCode = StatementConstructor::newCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE, mCode, aCode);
		}
		else
		{
			mCode = aCode;
		}
	}


	/**
	 * MACRO
	 * INLINING
	 */
	inline bool isInlinableStatement() const
	{
		return( getSpecifier().isDesignInstanceDynamic() && hasModel()
				&& getModel()->getModifier().hasNatureMacro() );
	}

	inline BFCode inlineStatement() const
	{
		return( inlineCode( getModel()->mCode ) );
	}


	inline bool isInlinableExpression() const
	{
		return( getSpecifier().isDesignInstanceDynamic() && hasModel()
				&& getModel()->getModifier().hasNatureMacro()
				&& getModel()->getPropertyPart().getVariableReturns().singleton()
				&& getModel()->getCode()->isOpCode( AVM_OPCODE_RETURN ) );
	}

	inline BF inlineExpression() const
	{
		return( inlineCode( getModel()->mCode->first() ) );
	}


	BFCode inlineCode(const BFCode & aCode) const;

	BF inlineCode(const BF & aCode) const;


	////////////////////////////////////////////////////////////////////////////
	// ROUTINE INVOKATION
	static BFCode invokeRoutine(Routine * aRoutineInstance);

	static BFCode invokeRoutineStatement(Routine * aRoutineInstance);

	static BF invokeRoutineExpression(Routine * aRoutineInstance);


	/**
	 * Serialization
	 */
	void strParameters(OutStream & out, const std::string & sep = ", ") const;

	void strReturns(OutStream & out, const std::string & sep = ", ") const;

	virtual void strHeader(OutStream & out) const override;

	// Due to [-Woverloaded-virtual=]
	using BehavioralElement::strHeader;

	virtual void toStream(OutStream & out) const override;


	void strInvokeParameters(
			OutStream & out, const std::string & sep = ", ") const;

	void strInvokeReturns(
			OutStream & out, const std::string & sep = ", ") const;

	void toStreamInvoke(OutStream & out, const std::string & sep = ", ") const;

};


} /* namespace sep */
#endif /* ROUTINE_H_ */

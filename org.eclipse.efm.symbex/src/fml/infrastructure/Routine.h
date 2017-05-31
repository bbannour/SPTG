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

#include <fml/operator/Operator.h>


namespace sep
{

class BehavioralPart;

class Machine;

class ObjectElement;

class Variable;


class Routine :
		public BehavioralElement,
		public SpecifierImpl,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Routine )
{

	AVM_DECLARE_CLONABLE_CLASS( Routine )


protected:
	/**
	* ATTRIBUTES
	*/
	BF mModel;

	BFVector mParameters;

	BFVector mReturns;

	BFCode mCode;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Routine(Machine * aContainer, const std::string & aNameID,
			const Modifier & aModifier, const Specifier & aSpecifier,
			const BF & aModel = BF::REF_NULL);


	Routine(BehavioralElement * aContainer, const std::string & aNameID,
			const Specifier & aSpecifier =
					Specifier::DESIGN_PROTOTYPE_STATIC_SPECIFIER,
			const BF & aModel = BF::REF_NULL)
	: BehavioralElement( CLASS_KIND_T( Routine ), aContainer, aNameID ),
	SpecifierImpl( aSpecifier ),

	mModel( aModel ),

	mParameters( ),
	mReturns( ),
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

		return( new Routine(aContainer, aNameID, aModifier,
				aSpecifier.setDesignModel()) );
	}

	static Routine * newDefine(
			Machine * aContainer, const std::string & aNameID);

	inline static Routine * newDefine(
			const BehavioralPart & aBehavioralPart,
			const std::string & aNameID)
	{

		return( new Routine(aBehavioralPart, aNameID,
				Specifier::DESIGN_MODEL_SPECIFIER) );
	}

	inline static Routine * newInvoke(
			BehavioralElement * aContainer, const std::string & aNameID)
	{
		return( new Routine(aContainer, aNameID,
				Specifier::DESIGN_INSTANCE_DYNAMIC_SPECIFIER) );
	}

	static Routine * newInvoke(Machine * aContainer, const BF & aModel);


	/**
	 * DESTRUCTOR
	 */
	virtual ~Routine()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * the Type Specifier
	 */
	inline const BF & getType() const
	{
		return( mModel );
	}

//	inline bool hasType() const
//    {
//		return( mModel.valid() );
//    }
//
//	inline void setType(const BF & aType)
//	{
//		mModel = aType;
//	}
//

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
			BehavioralElement::setNameID(
					aModel.to_ptr< Routine >()->getNameID() );
		}
		else
		{
			BehavioralElement::setNameID( aModel.str() );
		}
	}

	// Model as Invokable Operator
	inline Operator * getModelOperator() const
	{
		return( mModel.as_ptr< Operator >() );
	}

	inline bool hasModelOperator() const
	{
		return( mModel.is< Operator >() );
	}


	/**
	 * GETTER - SETTER
	 * mCode
	 */
	inline BFCode & getCode()
	{
		return( mCode );
	}

	inline const BFCode & getCode() const
	{
		return( mCode );
	}

	inline bool hasCode() const
	{
		return( mCode.valid() );
	}

	inline bool doSomething() const
	{
		return( mCode.valid() && StatementTypeChecker::doSomething(mCode) );
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
	 * GETTER - SETTER
	 * mParameters
	 */
	inline BFVector & getParameters()
	{
		return( mParameters );
	}

	inline const BF & getParameter(avm_offset_t offset) const
	{
		return( mParameters[offset] );
	}

	inline const BF & getParameter(const std::string & aNameID) const
	{
		return( getByNameID(mParameters, aNameID) );
	}

	avm_offset_t getParameterOffset(const std::string & label) const
	{
		return( getOffsetByNameID(mParameters, label) );
	}


	inline bool hasParameters() const
	{
		return( mParameters.nonempty() );
	}

	bool hasParameterOffset(Variable * aParameter) const;


	inline void appendParameter(const BF & anInput)
	{
		mParameters.append( anInput );
	}

	void saveParameter(Variable * anInput);

	inline void appendParameter(const std::string & label, const BF & anInput)
	{
		mParameters.append( anInput );
	}


	/**
	 * GETTER - SETTER
	 * mReturns
	 */
	inline BFVector & getReturns()
	{
		return( mReturns );
	}

	inline const BF & getReturn(avm_offset_t offset) const
	{
		return( mReturns[offset] );
	}

	inline const BF & getReturn(const std::string & aNameID) const
	{
		return( getByNameID(mReturns, aNameID) );
	}

	avm_offset_t getReturnOffset(const std::string & label) const
	{
		return( getOffsetByNameID(mReturns, label) );
	}


	inline bool hasReturns() const
	{
		return( mReturns.nonempty() );
	}

	bool hasReturnOffset(Variable * aReturn) const;


	inline void appendReturn(const BF & anOutput)
	{
		mReturns.append( anOutput );
	}

	void saveReturn(Variable * anOutput);

	inline void appendReturn(const std::string & label, const BF & anOutput)
	{
		mReturns.append( anOutput );
	}


	/**
	 * GETTER
	 * the parameters / returns
	 */
	inline const BF & getParamReturn(const std::string & aNameID) const
	{
		const BF & bfParam = getParameter(aNameID);

		return( bfParam.valid() ? bfParam : getReturn(aNameID)  );

	}

	static const BF & getByNameID(
			const BFVector & params, const std::string & aNameID);

	static avm_offset_t getOffsetByNameID(
			const BFVector & params, const std::string & label);


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
				&& getModel()->getReturns().singleton()
				&& getModel()->getCode()->isOpCode( AVM_OPCODE_RETURN ) );
	}

	inline BF inlineExpression() const
	{
		return( inlineCode( getModel()->mCode->first() ) );
	}


	BFCode inlineCode(const BFCode & aCode) const;

	BF inlineCode(const BF & aCode) const;


	/**
	 * Serialization
	 */
	void strParameters(OutStream & os, const std::string & sep = ", ") const;

	void strReturns(OutStream & os, const std::string & sep = ", ") const;

	void strHeader(OutStream & os) const;

	void toStream(OutStream & os) const;


	void strInvokeParameters(OutStream & os, const std::string & sep = ", ") const;

	void strInvokeReturns(OutStream & os, const std::string & sep = ", ") const;

	void toStreamInvoke(OutStream & os, const std::string & sep = ", ") const;

};


} /* namespace sep */
#endif /* ROUTINE_H_ */

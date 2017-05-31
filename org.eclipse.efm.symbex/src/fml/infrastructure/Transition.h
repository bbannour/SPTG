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

#ifndef TRANSITION_H_
#define TRANSITION_H_

#include <fml/common/BehavioralElement.h>
#include <fml/common/SpecifierElement.h>

#include <common/AvmPointer.h>
#include <common/BF.h>

#include <fml/expression/AvmCode.h>


namespace sep
{

class Machine;
class PropertyPart;


class Transition :
		public BehavioralElement,
		public SpecifierImpl,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Transition )
{

	AVM_DECLARE_CLONABLE_CLASS( Transition )


public:
	/**
	 * TYPEDEF
	 */
	typedef avm_uint8_t         moc_kind_t;

	enum MOC_KIND
	{
		MOC_UNDEFINED_KIND      = 0x000,


		MOC_SIMPLE_KIND         = 0x001,

		MOC_ABORT_KIND          = 0x002,

		MOC_FINAL_KIND          = 0x004,


		MOC_ELSE_KIND           = 0x010,


		MOC_INTERNAL_KIND       = 0x020,

		MOC_AUTO_KIND           = 0x040,


		MOC_FLOW_KIND           = 0x080,

		//ELSE CASE
		MOC_SIMPLE_ELSE_KIND    = MOC_ELSE_KIND | MOC_SIMPLE_KIND,
		MOC_ABORT_ELSE_KIND     = MOC_ELSE_KIND | MOC_ABORT_KIND,
		MOC_FINAL_ELSE_KIND     = MOC_ELSE_KIND | MOC_FINAL_KIND,

		MOC_INTERNAL_ELSE_KIND  = MOC_ELSE_KIND | MOC_INTERNAL_KIND,
		MOC_AUTO_ELSE_KIND      = MOC_ELSE_KIND | MOC_AUTO_KIND,
		MOC_FLOW_ELSE_KIND      = MOC_ELSE_KIND | MOC_FLOW_KIND,


		MOC_MASK_ALL_KIND       = 0x0FF
	};


protected:
	/**
	 * ATTRIBUTES
	 */
	moc_kind_t mMocKind;

	int   mPriority;

	float mProbability;

	int   mTokenCount;

	Machine * mSource;
	BF        mTarget;

	PropertyPart * mDeclaration;

	BFCode mStatement;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Transition(Machine * aContainer);

	Transition(Machine * aContainer, const std::string & aNameID,
			MOC_KIND aKind = MOC_SIMPLE_KIND);

	Transition(Machine * aContainer, const Transition * aTransitionPattern);

	/**
	 * DESTRUCTOR
	 */
	virtual ~Transition();


	/**
	 * GETTER - SETTER
	 * UFI , ID
	 */
	void updateNameID(const std::string & id);


	/**
	 * GETTER - SETTER
	 * mMocKind
	 */
	inline moc_kind_t getMocKind() const
	{
		return( mMocKind );
	}

	inline void setMocKind(moc_kind_t aMocKind)
	{
		mMocKind = aMocKind;
	}

	inline bool hasMocSimple() const
	{
		return( mMocKind & MOC_SIMPLE_KIND );
	}

	inline bool isMocSimple() const
	{
		return( mMocKind == MOC_SIMPLE_KIND );
	}

	inline bool isMocSimpleOrElse() const
	{
		return( (mMocKind == MOC_ELSE_KIND)
				|| (mMocKind == MOC_SIMPLE_ELSE_KIND) );
	}


	inline bool hasMocAbort() const
	{
		return( mMocKind & MOC_ABORT_KIND );
	}

	inline bool isMocAbort() const
	{
		return( mMocKind == MOC_ABORT_KIND );
	}

	inline bool isMocAbortElse() const
	{
		return( mMocKind == MOC_ABORT_ELSE_KIND );
	}


	inline bool hasMocFinal() const
	{
		return( mMocKind & MOC_FINAL_KIND );
	}

	inline bool isMocFinal() const
	{
		return( mMocKind == MOC_FINAL_KIND );
	}

	inline bool isMocFinalElse() const
	{
		return( mMocKind == MOC_FINAL_ELSE_KIND );
	}


	inline bool hasMocElse() const
	{
		return( mMocKind & MOC_ELSE_KIND );
	}

	inline bool isMocElse() const
	{
		return( mMocKind == MOC_ELSE_KIND );
	}


	inline bool isMocInternal() const
	{
		return( mMocKind == MOC_INTERNAL_KIND );
	}

	inline bool isMocAuto() const
	{
		return( mMocKind == MOC_AUTO_KIND );
	}

	inline bool isMocFlow() const
	{
		return( mMocKind == MOC_AUTO_KIND );
	}


	/**
	 * GETTER - SETTER
	 * mPriority
	 */
	inline int getPriority() const
	{
		return( mPriority );
	}

	inline void setPriority(int aPriority)
	{
		mPriority = aPriority;
	}


	/**
	 * GETTER - SETTER
	 * mProbability
	 */
	inline float getProbability() const
	{
		return( mProbability );
	}

	inline void setProbability(float aProbability)
	{
		mProbability = aProbability;
	}


	/**
	 * GETTER - SETTER
	 * mTokenCount
	 */
	inline int getTokenCount() const
	{
		return( mTokenCount );
	}

	inline void setTokenCount(int aTokenCount)
	{
		mTokenCount = aTokenCount;
	}


	/**
	 * GETTER - SETTER
	 * mSource
	 */
	inline Machine * getSource() const
	{
		return( mSource );
	}

	inline void setSource(Machine * aSource)
	{
		mSource = aSource;
	}

	Machine * getSourceContainer() const;


	/**
	 * GETTER - SETTER
	 * mTarget
	 */
	inline BF & getTarget()
	{
		return( mTarget );
	}

	inline const BF & getTarget() const
	{
		return( mTarget );
	}

	inline bool hasTarget() const
	{
		return( mTarget.valid() );
	}

	inline void setTarget(const BF & aTarget)
	{
		mTarget = aTarget;
	}


	/**
	 * GETTER - SETTER
	 * mDeclaration
	 */
	inline PropertyPart * getDeclaration() const
	{
		return( mDeclaration );
	}

	bool hasDeclaration() const;

	inline void setDeclaration(PropertyPart * aDeclaration)
	{
		mDeclaration = aDeclaration;
	}


	/**
	 * GETTER - SETTER
	 * mStatement
	 */
	inline const BFCode & getStatement() const
	{
		return( mStatement );
	}

	inline bool hasStatement() const
	{
		return( mStatement.valid() );
	}

	inline void setStatement(const BFCode & aStatement)
	{
		mStatement = aStatement;
	}


	/**
	 * Serialization
	 */
	static MOC_KIND toMocKind(const std::string & id);

	std::string strMocKind(
			moc_kind_t mask = MOC_MASK_ALL_KIND,
			const std::string & SEPARATOR = "%") const;


	virtual void strHeader(OutStream & os) const;


	inline std::string strTransitionHeader() const
	{
		StringOutStream oss;

		toStreamHeader( oss );

		return( oss.str() );
	}

	void toStreamHeader(OutStream & os) const;


	virtual void toStream(OutStream & os) const;

};


}

#endif /* TRANSITION_H_ */

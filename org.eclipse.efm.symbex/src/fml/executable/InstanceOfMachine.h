/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef INSTANCEOFMACHINE_H_
#define INSTANCEOFMACHINE_H_

#include <fml/executable/BaseInstanceForm.h>
#include <fml/common/SpecifierElement.h>

#include <collection/Typedef.h>

#include <fml/common/ModifierElement.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/lib/IComPoint.h>

#include <fml/runtime/RuntimeID.h>
#include <fml/runtime/TableOfData.h>

#include <fml/infrastructure/Machine.h>


namespace sep
{

class BaseAvmProgram;

class ExecutableForm;

class Specifier;


class InstanceOfMachine :
		public BaseInstanceForm,
		public SpecifierImpl,
		AVM_INJECT_STATIC_NULL_REFERENCE( InstanceOfMachine ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( InstanceOfMachine )
{

	AVM_DECLARE_CLONABLE_CLASS( InstanceOfMachine )

protected:
	/*
	 * ATTRIBUTES
	 */
	// the Executable Code for Machine
	ExecutableForm * mExecutable;

	bool mThisFlag;

	AvmProgram onCreateRoutine;
	AvmProgram onStartRoutine;

	std::size_t mPossibleDynamicInstanciationCount;
	std::size_t mMaximalInstanceCount;

	APTableOfData mParamReturnTable;

	std::size_t mReturnOffset;

	InstanceOfMachine * mInstanceModel;

	// The runtime machine RID for RID access optimization
	RuntimeID mRuntimeRID;

	bool mModifierAutoStart;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstanceOfMachine(ExecutableForm * aContainer,
			const Machine & astMachine, ExecutableForm & anExecutable,
			InstanceOfMachine * anInstanceModel, avm_offset_t anOffset);

	InstanceOfMachine(ExecutableForm * aContainer, const Machine & astMachine,
			ExecutableForm & anExecutable, InstanceOfMachine * anInstanceModel,
			avm_offset_t anOffset, const Specifier & aSpecifier);


	/**
	 * CONSTRUCTOR
	 * copy
	 */
	InstanceOfMachine(const InstanceOfMachine & aMachine)
	: BaseInstanceForm( aMachine ),
	SpecifierImpl( aMachine ),

	mExecutable( aMachine.mExecutable ),

	mThisFlag( aMachine.mThisFlag ),

	onCreateRoutine ( aMachine.onCreateRoutine ),
	onStartRoutine( aMachine.onStartRoutine ),

	mPossibleDynamicInstanciationCount(
			aMachine.mPossibleDynamicInstanciationCount ),
	mMaximalInstanceCount( aMachine.mMaximalInstanceCount ),
	mParamReturnTable( aMachine.mParamReturnTable ),
	mReturnOffset( aMachine.mReturnOffset ),
	mInstanceModel(  aMachine.mInstanceModel ),
	mRuntimeRID( aMachine.mRuntimeRID ),
	mModifierAutoStart(  aMachine.mModifierAutoStart )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * for Alias
	 */
	InstanceOfMachine(BaseAvmProgram * aContainer,
			const InstanceOfMachine & aTarget,
			VectorOfInstanceOfMachine & aRelativeMachinePath)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfMachine ),
			aContainer, aTarget, aRelativeMachinePath),
	SpecifierImpl( aTarget.getSpecifier() ),

	mExecutable( aTarget.mExecutable ),

	mThisFlag( aTarget.mThisFlag ),

	onCreateRoutine ( aTarget.onCreateRoutine ),
	onStartRoutine( aTarget.onStartRoutine ),

	mPossibleDynamicInstanciationCount(
			aTarget.mPossibleDynamicInstanciationCount ),
	mMaximalInstanceCount( aTarget.mMaximalInstanceCount ),
	mParamReturnTable( aTarget.mParamReturnTable ),
	mReturnOffset( aTarget.mReturnOffset ),
	mInstanceModel(  aTarget.mInstanceModel ),
	mRuntimeRID( aTarget.mRuntimeRID ),
	mModifierAutoStart(  aTarget.mModifierAutoStart )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~InstanceOfMachine()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	static InstanceOfMachine & nullref();


	/**
	 * GETTER
	 * Compiled ObjectElement as Compiled Machine
	 */
	inline const Machine & getAstMachine() const
	{
		return( safeAstElement().as< Machine >() );
	}


	/**
	 * SETTER
	 * mFullyQualifiedNameID
	 */
	virtual void updateFullyQualifiedNameID() override;


	/**
	 * GETTER - SETTER
	 * mExecutable
	 */
	inline ExecutableForm * getExecutable() const
	{
		return( mExecutable );
	}

	inline const ExecutableForm & refExecutable() const
	{
		return( * mExecutable );
	}

	inline ExecutableForm & refExecutable()
	{
		return( * mExecutable );
	}

	inline bool hasExecutable() const
	{
		return( mExecutable != nullptr );
	}

	bool hasnotNullExecutable() const;

	inline void setExecutable(ExecutableForm * anExecutable)
	{
		mExecutable = anExecutable;
	}


	/**
	 * GETTER - SETTER
	 * mExecutable
	 */
	inline bool isThis() const
	{
		return( mThisFlag );
	}

	inline bool isnotThis() const
	{
		return( not mThisFlag );
	}

	inline bool isThis(const ExecutableForm * anExecutable) const
	{
		return( mThisFlag && (mExecutable == anExecutable) );
	}

	inline bool isnotThis(const ExecutableForm * anExecutable) const
	{
		return( (mExecutable != anExecutable) || (not mThisFlag) );
	}

	inline void setThis(bool isThisFlag = true)
	{
		mThisFlag = isThisFlag;
	}

	/**
	 * CONSTRUCTION
	 * the instance << this >>
	 */
	static std::string THIS_FQN_SUFFIX;
	static std::string THIS_ID;

	static InstanceOfMachine * newThis(ExecutableForm & anExecutable,
			InstanceOfMachine * anInstanceModel, avm_offset_t anOffset);

	static InstanceOfMachine * newInstanceModelThis(
			ExecutableForm * aContainer, const Machine & astMachine,
			ExecutableForm & anExecutable, InstanceOfMachine * anInstanceModel,
			avm_offset_t anOffset, const Specifier & aSpecifier);

	/**
	 * GETTER - SETTER
	 * onCreateRoutine
	 */
	inline AvmProgram & getOnCreateRoutine()
	{
		return( onCreateRoutine );
	}

	inline const BFCode & getOnCreate() const
	{
		return( onCreateRoutine.getCode() );
	}

	inline bool hasOnCreate() const
	{
		return( onCreateRoutine.hasCode() );
	}

	inline void setOnCreate(const BFCode & aProgram)
	{
		onCreateRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onStartRoutine
	 */
	inline AvmProgram & getOnStartRoutine()
	{
		return( onStartRoutine );
	}

	inline const BFCode & getOnStart() const
	{
		return( onStartRoutine.getCode() );
	}

	inline bool hasOnStart() const
	{
		return( onStartRoutine.hasCode() );
	}

	inline void setOnStart(const BFCode & aProgram)
	{
		onStartRoutine.setCode( aProgram );
	}


	/**
	 * UTIL
	 */
	inline bool hasBehavior() const
	{
		return( hasOnCreate() || hasOnStart() );
	}

	/*
	 * GETTER - SETTER
	 * mPossibleDynamicInstanciationCount
	 * Single or Multiple
	 * Instanciation Information
	 * for Data Access optimisation
	 */
	inline std::size_t getStaticInstanciationCount() const
	{
		return( mInstanciationCount );
	}

	inline bool hasStaticInstanciation() const
	{
		return( mInstanciationCount > 0 );
	}


	inline std::size_t getPossibleDynamicInstanciationCount() const
	{
		return( mPossibleDynamicInstanciationCount );
	}

	inline bool hasPossibleDynamicInstanciation() const
	{
		return( mPossibleDynamicInstanciationCount > 0 );
	}

	void incrPossibleDynamicInstanciationCount(std::size_t offset = 1);


	inline bool hasSingleRuntimeInstance()
	{
		return( (mInstanciationCount > 1) ||
				(mPossibleDynamicInstanciationCount > 0) );
	}


	/**
	 * GETTER - SETTER
	 * mMaximalInstanceCount
	 */
	inline std::size_t getMaximalInstanceCount() const
	{
		return( mMaximalInstanceCount );
	}

	inline bool hasMaximalInstance() const
	{
		return( mMaximalInstanceCount != AVM_NUMERIC_MAX_SIZE_T );
	}

	inline bool hasMaximalNewInstance() const
	{
		return( (mMaximalInstanceCount > 1)
				&& (mMaximalInstanceCount != AVM_NUMERIC_MAX_SIZE_T) );
	}

	inline void setMaximalInstanceCount(std::size_t aMaximalInstanceCount)
	{
		mMaximalInstanceCount = aMaximalInstanceCount;
	}


	inline void setInstanceCount(
			std::uint32_t anInitialCount, std::size_t aMaximalInstanceCount)
	{
		BaseInstanceForm::setInstanciationCount( anInitialCount );

		mMaximalInstanceCount = aMaximalInstanceCount;
	}


	/**
	 * GETTER - SETTER
	 * mParamReturnTable
	 */
	inline APTableOfData & getParamReturnTable()
	{
		return( mParamReturnTable );
	}

	inline const APTableOfData & getParamReturnTable() const
	{
		return( mParamReturnTable );
	}


	inline bool hasParamReturnTable() const
	{
		return( mParamReturnTable.valid() );
	}


	inline void setParamReturnTable(const APTableOfData & aParamTable)
	{
		mParamReturnTable = aParamTable;
	}


	inline BF & getParamReturn(std::size_t offset)
	{
		return( mParamReturnTable->at(offset) );
	}

	inline const BF & getParamReturn(std::size_t offset) const
	{
		return( mParamReturnTable->at(offset) );
	}


	inline bool hasParamReturn() const
	{
		return( mParamReturnTable.valid() && mParamReturnTable->nonempty() );
	}

	inline void setParamReturn(std::size_t offset, const BF & aParam)
	{
		mParamReturnTable->set(offset, aParam);
	}


	/**
	 * GETTER - SETTER
	 * mParamReturnTable
	 * mReturnOffset
	 */

	inline std::size_t getParamOffset() const
	{
		return( 0 );
	}

	inline std::size_t getParamCount() const
	{
		return( mReturnOffset );
	}

	inline BF & getParam(std::size_t offset)
	{
		return( mParamReturnTable->at(offset) );
	}

	inline const BF & getParam(std::size_t offset) const
	{
		return( mParamReturnTable->at(offset) );
	}


	const BaseTypeSpecifier & getParamType(std::size_t offset) const;


	inline bool hasParam() const
	{
		return( mParamReturnTable.valid()
				&& mParamReturnTable->nonempty()
				&& (mReturnOffset > 0) );
	}


	inline void setParam(std::size_t offset, const BF & aParam)
	{
		mParamReturnTable->set(offset, aParam);
	}


	/**
	 * GETTER - SETTER
	 * mParamReturnTable
	 * mReturnOffset
	 */
	inline void setReturnOffset(std::size_t aReturnOffset)
	{
		mReturnOffset = aReturnOffset;
	}

	inline std::size_t getReturnCount() const
	{
		return( mParamReturnTable->size() - mReturnOffset );
	}


	inline bool hasReturn() const
	{
		return( mParamReturnTable.valid()
				&& (mReturnOffset <  mParamReturnTable->size()) );
	}


	/**
	 * GETTER - SETTER
	 * mInstanceModel
	 */
	inline InstanceOfMachine * getInstanceModel() const
	{
		return( mInstanceModel );
	}

	inline bool hasInstanceModel() const
	{
		return( mInstanceModel != nullptr );
	}

	inline bool isInstanceModel(InstanceOfMachine * anOtherModel) const
	{
		return( (mInstanceModel != nullptr)
				&& ( (mInstanceModel == anOtherModel)
					|| (anOtherModel->getSpecifier().isDesignPrototypeStatic()
						&& (mInstanceModel
							== anOtherModel->getInstanceModel()) )));
	}

	inline void setInstanceModel(InstanceOfMachine * anInstanceModel)
	{
		mInstanceModel = anInstanceModel;
	}


	/**
	 * GETTER - SETTER
	 * mRuntimeRID
	 */
	inline const RuntimeID & getRuntimeRID() const
	{
		return( mRuntimeRID );
	}

	inline bool hasRuntimeRID() const
	{
		return( mRuntimeRID.valid() );
	}

	inline void setRuntimeRID(const RuntimeID & aRID)
	{
		mRuntimeRID = aRID;
	}


	/**
	 * GETTER - SETTER
	 * "autostart" modifier of Instance
	 */
	inline bool isAutoStart() const
	{
		return( mModifierAutoStart );
	}

	inline void setAutoStart(bool bAutoStart = true)
	{
		mModifierAutoStart = bAutoStart;
	}


	/**
	 * Serialization
	 */
	void header(OutStream & out) const;

	void strHeader(OutStream & out) const override;

	void toStream(OutStream & out) const override;

};


}

#endif /* INSTANCEOFMACHINE_H_ */

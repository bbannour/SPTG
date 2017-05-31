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

#include <common/AvmPointer.h>

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

	avm_size_t mPossibleDynamicInstanciationCount;
	avm_size_t mMaximalInstanceCount;

	APTableOfData mParamReturnTable;

	avm_size_t mReturnOffset;

	InstanceOfMachine * mInstanceModel;

	// The runtime machine RID for RID access optimization
	RuntimeID mRuntimeRID;

	bool mModifierAutoStart;

	// static class of Port/Message/Signal in communicated statement
	ListOfInstanceOfBuffer mInputEnabledBuffer;
	ListOfInstanceOfPort mInputEnabledCom;
	ListOfInstanceOfPort mInputEnabledSave;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstanceOfMachine(ExecutableForm * aContainer,
			const Machine * astMachine, ExecutableForm * anExecutable,
			InstanceOfMachine * anInstanceModel, avm_offset_t anOffset);

	InstanceOfMachine(ExecutableForm * aContainer, const Machine * astMachine,
			ExecutableForm * anExecutable, InstanceOfMachine * anInstanceModel,
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
	mModifierAutoStart(  aMachine.mModifierAutoStart ),

	mInputEnabledBuffer( aMachine.mInputEnabledBuffer ),
	mInputEnabledCom( aMachine.mInputEnabledCom ),
	mInputEnabledSave( aMachine.mInputEnabledSave )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * for Alias
	 */
	InstanceOfMachine(BaseAvmProgram * aContainer, InstanceOfMachine * aTarget,
			VectorOfInstanceOfMachine & aRelativeMachinePath)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfMachine ),
			aContainer, aTarget, aRelativeMachinePath),
	SpecifierImpl( aTarget->getSpecifier() ),

	mExecutable( aTarget->mExecutable ),

	mThisFlag( aTarget->mThisFlag ),

	onCreateRoutine ( aTarget->onCreateRoutine ),
	onStartRoutine( aTarget->onStartRoutine ),

	mPossibleDynamicInstanciationCount(
			aTarget->mPossibleDynamicInstanciationCount ),
	mMaximalInstanceCount( aTarget->mMaximalInstanceCount ),
	mParamReturnTable( aTarget->mParamReturnTable ),
	mReturnOffset( aTarget->mReturnOffset ),
	mInstanceModel(  aTarget->mInstanceModel ),
	mRuntimeRID( aTarget->mRuntimeRID ),
	mModifierAutoStart(  aTarget->mModifierAutoStart ),

	mInputEnabledBuffer( aTarget->mInputEnabledBuffer ),
	mInputEnabledCom( aTarget->mInputEnabledCom ),
	mInputEnabledSave( aTarget->mInputEnabledSave )
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
	 * Compiled ObjectElement as Compiled Machine
	 */
	inline const Machine * getAstMachine() const
	{
		return( getAstElement()->as< Machine >() );
	}


	/**
	 * SETTER
	 * mFullyQualifiedNameID
	 */
	virtual void updateFullyQualifiedNameID();


	/**
	 * GETTER - SETTER
	 * mExecutable
	 */
	inline ExecutableForm * getExecutable() const
	{
		return( mExecutable );
	}

	inline bool hasExecutable() const
	{
		return( mExecutable != NULL );
	}

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

	static InstanceOfMachine * newThis(ExecutableForm * anExecutable,
			InstanceOfMachine * anInstanceModel, avm_offset_t anOffset);

	static InstanceOfMachine * newInstanceModelThis(
			ExecutableForm * aContainer, Machine * aCompiled,
			ExecutableForm * anExecutable, InstanceOfMachine * anInstanceModel,
			avm_offset_t anOffset, const Specifier & aSpecifier);

	/**
	 * GETTER - SETTER
	 * onCreateRoutine
	 */
	inline AvmProgram & getOnCreateRoutine()
	{
		return( onCreateRoutine );
	}

	inline BFCode & getOnCreate()
	{
		return( onCreateRoutine.getCode() );
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

	inline BFCode & getOnStart()
	{
		return( onStartRoutine.getCode() );
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
	inline avm_size_t getStaticInstanciationCount() const
	{
		return( mInstanciationCount );
	}

	inline bool hasStaticInstanciation() const
	{
		return( mInstanciationCount > 0 );
	}


	inline avm_size_t getPossibleDynamicInstanciationCount() const
	{
		return( mPossibleDynamicInstanciationCount );
	}

	inline bool hasPossibleDynamicInstanciation() const
	{
		return( mPossibleDynamicInstanciationCount > 0 );
	}

	void incrPossibleDynamicInstanciationCount(avm_size_t offset = 1);


	inline bool hasSingleRuntimeInstance()
	{
		return( (mInstanciationCount > 1) ||
				(mPossibleDynamicInstanciationCount > 0) );
	}


	/**
	 * GETTER - SETTER
	 * mMaximalInstanceCount
	 */
	inline avm_size_t getMaximalInstanceCount() const
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

	inline void setMaximalInstanceCount(avm_size_t aMaximalInstanceCount)
	{
		mMaximalInstanceCount = aMaximalInstanceCount;
	}


	inline void setInstanceCount(
			avm_uint32_t anInitialCount, avm_size_t aMaximalInstanceCount)
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


	inline BF & getParamReturn(avm_size_t offset)
	{
		return( mParamReturnTable->at(offset) );
	}

	inline const BF & getParamReturn(avm_size_t offset) const
	{
		return( mParamReturnTable->at(offset) );
	}


	inline bool hasParamReturn() const
	{
		return( mParamReturnTable.valid() && mParamReturnTable->nonempty() );
	}

	inline void setParamReturn(avm_size_t offset, const BF & aParam)
	{
		mParamReturnTable->set(offset, aParam);
	}


	/**
	 * GETTER - SETTER
	 * mParamReturnTable
	 * mReturnOffset
	 */

	inline avm_size_t getParamOffset() const
	{
		return( 0 );
	}

	inline avm_size_t getParamCount() const
	{
		return( mReturnOffset );
	}

	inline BF & getParam(avm_size_t offset)
	{
		return( mParamReturnTable->at(offset) );
	}

	inline const BF & getParam(avm_size_t offset) const
	{
		return( mParamReturnTable->at(offset) );
	}


	BaseTypeSpecifier * getParamType(avm_size_t offset) const;


	inline bool hasParam() const
	{
		return( mParamReturnTable.valid()
				&& mParamReturnTable->nonempty()
				&& (mReturnOffset > 0) );
	}


	inline void setParam(avm_size_t offset, const BF & aParam)
	{
		mParamReturnTable->set(offset, aParam);
	}


	/**
	 * GETTER - SETTER
	 * mParamReturnTable
	 * mReturnOffset
	 */
	inline void setReturnOffset(avm_size_t aReturnOffset)
	{
		mReturnOffset = aReturnOffset;
	}

	inline avm_size_t getReturnCount() const
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
		return( mInstanceModel != NULL );
	}

	inline bool isInstanceModel(InstanceOfMachine * anOtherModel) const
	{
		return( (mInstanceModel != NULL)
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
	 * GETTER - SETTER
	 * mInputEnabledBuffer
	 */
	inline void addInputEnabledBuffer(InstanceOfBuffer * aBuffer)
	{
		mInputEnabledBuffer.add_union( aBuffer );
	}

	inline void addInputEnabledBuffer(ListOfInstanceOfBuffer & inputEnabledBuffer)
	{
		mInputEnabledBuffer.add_union( inputEnabledBuffer );
	}


	inline ListOfInstanceOfBuffer & getInputEnabledBuffer()
	{
		return( mInputEnabledBuffer );
	}

	inline const ListOfInstanceOfBuffer & getInputEnabledBuffer() const
	{
		return( mInputEnabledBuffer );
	}


	bool containsInputEnabledBuffer(InstanceOfBuffer * aBuffer) const
	{
		return( mInputEnabledBuffer.contains(aBuffer) );
	}

	inline bool hasInputEnabledBuffer() const
	{
		return( mInputEnabledBuffer.nonempty() );
	}


	inline void setInputEnabledBuffer(ListOfInstanceOfBuffer & inputEnabledBuffer)
	{
		mInputEnabledBuffer.clear();

		mInputEnabledBuffer.add_union( inputEnabledBuffer );
	}


	/**
	 * GETTER - SETTER
	 * mInputEnabledCom
	 */
	inline void addInputEnabledCom(InstanceOfPort * aPort)
	{
		mInputEnabledCom.add_union( aPort );
	}

	inline void addInputEnabledCom(ListOfInstanceOfPort & inputEnabledPort)
	{
		mInputEnabledCom.add_union( inputEnabledPort );
	}


	inline ListOfInstanceOfPort & getInputEnabledCom()
	{
		return( mInputEnabledCom );
	}

	inline const ListOfInstanceOfPort & getInputEnabledCom() const
	{
		return( mInputEnabledCom );
	}


	bool containsInputEnabledCom(InstanceOfPort * aPort) const
	{
		return( mInputEnabledCom.contains(aPort) );
	}

	inline bool hasInputEnabledCom() const
	{
		return( mInputEnabledCom.nonempty() );
	}


	inline void setInputEnabledCom(ListOfInstanceOfPort & inputEnabledPort)
	{
		mInputEnabledCom.clear();

		mInputEnabledCom.add_union( inputEnabledPort );
	}


	/**
	 * GETTER - SETTER
	 * mInputEnabledSave
	 */
	inline void addInputEnabledSave(InstanceOfPort * aPort)
	{
		mInputEnabledSave.add_union( aPort );
	}

	inline void addInputEnabledSave(ListOfInstanceOfPort & inputEnabledSavePort)
	{
		mInputEnabledSave.add_union( inputEnabledSavePort );
	}


	inline ListOfInstanceOfPort & getInputEnabledSave()
	{
		return( mInputEnabledSave );
	}

	inline const ListOfInstanceOfPort & getInputEnabledSave() const
	{
		return( mInputEnabledSave );
	}


	bool containsInputEnabledSave(InstanceOfPort * aPort) const
	{
		return( mInputEnabledSave.contains(aPort) );
	}

	inline bool hasInputEnabledSave() const
	{
		return( mInputEnabledSave.nonempty() );
	}


	inline void setInputEnabledSave(ListOfInstanceOfPort & inputEnabledSavePort)
	{
		mInputEnabledSave.clear();

		mInputEnabledSave.add_union( inputEnabledSavePort );
	}


	/**
	 * Serialization
	 */
	void header(OutStream & out) const;

	void strHeader(OutStream & out) const;

	void toStream(OutStream & out) const;

};


}

#endif /* INSTANCEOFMACHINE_H_ */

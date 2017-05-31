/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#ifndef RUNTIMEFORM_H_
#define RUNTIMEFORM_H_

#include <base/SmartTable.h>

#include <common/AvmPointer.h>
#include <common/Element.h>
#include <common/BF.h>

#include <collection/Typedef.h>

#include <fml/buffer/BaseBufferForm.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/Router.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/runtime/RuntimeID.h>
#include <fml/runtime/TableOfData.h>


namespace sep
{


class ExecutableForm;
class ExecutionData;
class InstanceOfData;
class InstanceOfMachine;

/**
 * TYPEDEF
 */
typedef SmartTable< BaseBufferForm , DestroyElementPolicy > TableOfBufferT;


class RuntimeForm  :  public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( RuntimeForm )
{

	AVM_DECLARE_CLONABLE_CLASS( RuntimeForm )


protected:
	/*
	 * ATTRIBUTES
	 */
	avm_size_t mInstanciationCount;

	RuntimeID mRID;

	APTableOfRuntimeID mChildTable;

	APTableOfData mDataTable;

	TableOfBufferT mBufferTable;
	Router mRouter;

	BFCode mOnSchedule;

	BFCode mOnDefer;

	// MOC Attribute for Communication
	bool mEnvironmentEnabledCommunicationFlag;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	RuntimeForm(const RuntimeID & aRID)
	: Element( CLASS_KIND_T( RuntimeForm ) ),

	mInstanciationCount( aRID.getInstance()->getInstanciationCount() ),

	mRID( aRID ),

	mChildTable( ),

	mDataTable( ),

	mBufferTable( ),
	mRouter( ),

	mOnSchedule( ),
	mOnDefer( ),

	mEnvironmentEnabledCommunicationFlag( true )
	{
		//!! NOTHING
	}


	RuntimeForm(class_kind_t aClassKind, const RuntimeID & aRID)
	: Element( aClassKind ),

	mInstanciationCount( aRID.getInstance()->getInstanciationCount() ),

	mRID( aRID ),

	mChildTable( ),

	mDataTable( ),

	mBufferTable( ),
	mRouter( ),

	mOnSchedule( ),
	mOnDefer( ),

	mEnvironmentEnabledCommunicationFlag( true )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	RuntimeForm(const RuntimeForm & aRuntime)
	: Element( aRuntime ),

	mInstanciationCount( aRuntime.mInstanciationCount ),

	mRID( aRuntime.mRID ),

	mChildTable( aRuntime.mChildTable ),

	mDataTable( aRuntime.mDataTable ),

	mBufferTable( aRuntime.mBufferTable ),
	mRouter( aRuntime.mRouter ),

	mOnSchedule( aRuntime.mOnSchedule ),
	mOnDefer( aRuntime.mOnDefer ),

	mEnvironmentEnabledCommunicationFlag( true )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~RuntimeForm()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mRID
	 */
	inline const RuntimeID & getRID() const
	{
		return( mRID );
	}

	inline bool hasParentRID() const
	{
		return( mRID.hasPRID() );
	}

	inline RuntimeID getParentRID() const
	{
		return( mRID.getPRID() );
	}


	inline int getRid() const
	{
		return( mRID.getRid() );
	}


	inline int getOffset() const
	{
		return( mRID.getOffset() );
	}


	inline InstanceOfMachine * getInstance() const
	{
		return( mRID.getInstance() );
	}

	inline ExecutableForm * getExecutable() const
	{
		return( mRID.getExecutable() );
	}

	inline bool hasExecutable() const
	{
		return( mRID.hasExecutable() );
	}


	inline std::string getFullyQualifiedNameID() const
	{
		return( mRID.getFullyQualifiedNameID() );
	}

	inline std::string getNameID() const
	{
		return( mRID.getNameID() );
	}


	/**
	 * GETTER - SETTER
	 * mInstanciationCount
	 */
	inline avm_size_t getInstanciationCount() const
	{
		return( mInstanciationCount );
	}

	inline avm_size_t decrInstanciationCount()
	{
		return( --mInstanciationCount );
	}

	inline avm_size_t incrInstanciationCount()
	{
		return( ++mInstanciationCount );
	}


	inline bool isInstanciated() const
	{
		return( mInstanciationCount > 0 );
	}

	inline bool isnotInstanciated() const
	{
		return( mInstanciationCount == 0 );
	}


	inline void setInstanciationCount(avm_size_t anInstanciationNumber)
	{
		mInstanciationCount = anInstanciationNumber;
	}


	/**
	 * GETTER - SETTER
	 * mChildTable
	 */
	inline const APTableOfRuntimeID & getChildTable() const
	{
		return( mChildTable );
	}


	TableOfRuntimeID::iterator beginChild()
	{
		// don't forget the instance THIS at offset 0 !!!
		return( hasInstanceThis() ?
				++(mChildTable->begin()) : mChildTable->begin() );
	}

	TableOfRuntimeID::const_iterator beginChild() const
	{
		// don't forget the instance THIS at offset 0 !!!
		return( hasInstanceThis() ?
				++(mChildTable->begin()) : mChildTable->begin() );
	}

	TableOfRuntimeID::iterator endChild()
	{
		return( mChildTable->end() );
	}

	TableOfRuntimeID::const_iterator endChild() const
	{
		return( mChildTable->end() );
	}


	inline bool hasInstanceThis() const
	{
		return( mChildTable->nonempty() && (mChildTable->first() == mRID) );
	}

	inline bool hasChild() const
	{
		return( mChildTable.valid() && (mChildTable->populated() ||
			(mChildTable->nonempty() && (mChildTable->first() != mRID))) );
	}

	inline bool hasChildTable() const
	{
		return( mChildTable.valid() );
	}

	inline void makeWritableChildTable()
	{
		mChildTable.makeWritable();
	}

	inline void setChildTable(const APTableOfRuntimeID & aChilTable)
	{
		mChildTable = aChilTable;
	}


	inline void appendChild(const RuntimeID & aRID)
	{
		if( mChildTable.invalid() )
		{
			mChildTable.replacePointer( new TableOfRuntimeID() );
		}

		mChildTable->append(aRID);
	}


	inline const RuntimeID & getChild(avm_offset_t offset) const
	{
		return( mChildTable->get(offset) );
	}

	const RuntimeID & getChild(const std::string & aFullyQualifiedNameID) const;


	/**
	 * GETTER - SETTER
	 * mDataTable
	 */
	inline APTableOfData & getDataTable()
	{
		return( mDataTable );
	}

	inline const APTableOfData & getDataTable() const
	{
		return( mDataTable );
	}

	inline bool hasData() const
	{
		return( mDataTable.valid() && mDataTable->nonempty() );
	}

	inline bool hasDataTable() const
	{
		return( mDataTable.valid() );
	}

	// Writable mDataTable
	inline APTableOfData & getWritableDataTable()
	{
		mDataTable.makeWritable();

		return( mDataTable );
	}

	inline void makeWritableDataTable()
	{
		mDataTable.makeWritable();
	}

	//??COMPILE!!
	inline void setDataTable(TableOfData * aDataTable)
	{
		mDataTable = aDataTable;
	}

	inline void setDataTable(const APTableOfData & aDataTable)
	{
		mDataTable = aDataTable;
	}


	inline virtual const TableOfInstanceOfData & getVariables() const
	{
		return( mRID.getExecutable()->getData() );
	}

	inline virtual InstanceOfData * rawVariable(avm_offset_t offset) const
	{
		return( mRID.rawVariable(offset) );
	}

	inline virtual const BF & getVariable(avm_offset_t offset) const
	{
		return( mRID.getVariable(offset) );
	}


	inline BF & getData(avm_offset_t offset) const
	{
		return( mDataTable->at(offset) );
	}

	inline BF & getWritableData(avm_offset_t offset) const
	{
		return( mDataTable->getWritable(offset) );
	}

	inline const BF & getData(const InstanceOfData * anInstance) const
	{
		return( mDataTable->get(anInstance) );
	}


	inline const BF & getData(const std::string & aFullyQualifiedNameID) const
	{
		InstanceOfData * anInstance = getExecutable()->getAllData().
				rawByFQNameID( aFullyQualifiedNameID );
		if( anInstance != NULL )
		{
			return( mDataTable->get(anInstance) );
		}
		return( BF::REF_NULL );
	}

	inline const BF & getDataByQualifiedNameID(
			const std::string & aQualifiedNameID, InstanceOfData * & var) const
	{
		var = getExecutable()->getAllData().rawByQualifiedNameID(aQualifiedNameID);
		if( var != NULL )
		{
			return( mDataTable->get(var) );
		}
		return( BF::REF_NULL );
	}

	inline const BF & getDataByNameID(const std::string & aNameID) const
	{
		InstanceOfData * anInstance =
				getExecutable()->getAllData().rawByNameID(aNameID);
		if( anInstance != NULL )
		{
			return( mDataTable->get(anInstance) );
		}
		return( BF::REF_NULL );
	}


	inline void setData(avm_offset_t offset, const BF & aData) const
	{
		mDataTable->set(offset, aData);
	}

	inline void setData(
			const InstanceOfData * anInstance, const BF & aData) const
	{
		mDataTable->set(anInstance, aData);
	}


	/**
	 * GETTER - SETTER
	 * mDataTable
	 */
	inline const TableOfBufferT & getBufferTable() const
	{
		return( mBufferTable );
	}

	inline bool hasBuffer() const
	{
		return( mBufferTable.nonempty() );
	}

	inline bool hasBufferTable() const
	{
		return( mBufferTable.valid() );
	}

	inline TableOfBufferT & getWritableBufferTable()
	{
		mBufferTable.makeWritable();

		return( mBufferTable );
	}

	inline void makeWritableBufferTable()
	{
		mBufferTable.makeWritable();
	}

	inline void setBufferTable(const TableOfBufferT & aBufferTable)
	{
		mBufferTable = aBufferTable;
	}


	inline const BaseBufferForm & getBuffer(
			const InstanceOfBuffer * aBuffer) const
	{
		return( mBufferTable.ref( aBuffer->getOffset() ) );
	}

	inline BaseBufferForm & getWritableBuffer(const InstanceOfBuffer * aBuffer)
	{
		return( mBufferTable.refWritable( aBuffer->getOffset() ) );
	}

	inline BF bfWritableBuffer(const InstanceOfBuffer * aBuffer)
	{
		return( mBufferTable.spWritable< BF >( aBuffer->getOffset() ) );
	}


	/**
	 * GETTER - SETTER
	 * mRouter
	 */
	inline const Router & getRouter() const
	{
		return( mRouter );
	}

	inline bool hasRouter() const
	{
		return( mRouter.valid() );
	}

	inline void makeWritableRouter()
	{
		mRouter.makeWritable();
	}

	inline void setRouter(const Router & aRouter)
	{
		mRouter = aRouter;
	}


	/**
	 * GETTER - SETTER
	 * mOnSchedule
	 */
	inline const BFCode & getOnSchedule() const
	{
		return( mOnSchedule );
	}

	inline bool hasOnSchedule() const
	{
		return( mOnSchedule.valid() );
	}

	inline void setOnSchedule(const BFCode & onSchedule)
	{
		mOnSchedule = onSchedule;
	}


	/**
	 * GETTER - SETTER
	 * mOnDefer
	 */
	inline const BFCode & getOnDefer() const
	{
		return( mOnDefer );
	}

	inline bool hasOnDefer() const
	{
		return( mOnDefer.valid() );
	}

	inline void setOnDefer(const BFCode & onDefer)
	{
		mOnDefer = onDefer;
	}


	/**
	 * GETTER
	 * the Input Enabled Flag
	 * MOC Attribute for Communication
	 */
	inline bool isInputEnabled() const
	{
		return( getRID().getInstance()->getSpecifier().hasFeatureInputEnabled()
				|| getRID().getExecutable()->
						getSpecifier().hasFeatureInputEnabled() );
	}


	/**
	 * GETTER - SETTER
	 * mEnvironmentEnabledCommunicationFlag
	 * MOC Attribute for Communication
	 */
	inline bool isEnvironmentEnabledCommunication() const
	{
		return( mEnvironmentEnabledCommunicationFlag );
	}

	inline void setEnvironmentEnabledCommunication(
			bool isEnvironmentEnabled = true)
	{
		mEnvironmentEnabledCommunicationFlag = isEnvironmentEnabled;
	}


	/**
	 * Serialization
	 */
	inline virtual void toStream(OutStream & os) const
	{
		toStream(NULL, os);
	}

	inline virtual std::string str() const
	{
		return( getRID().str() );
	}

	virtual void toStream(const ExecutionData * anED, OutStream & os) const;

	virtual void toStreamData(const ExecutionData * anED, OutStream & os) const;


	virtual void toFscnData(OutStream & os,
			const ExecutionData * anED, const RuntimeForm * aPreviousRF) const;

	void toFscnBuffer(OutStream & os,
			const ExecutionData * anED, const RuntimeForm * aPreviousRF) const;

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// PARAMETERS RUNTIME FORM
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class ParametersRuntimeForm  :  public RuntimeForm ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ParametersRuntimeForm )
{

	AVM_DECLARE_CLONABLE_CLASS( ParametersRuntimeForm )


protected:
	/*
	 * ATTRIBUTES
	 */
	TableOfInstanceOfData mParameters;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ParametersRuntimeForm(const RuntimeID & aRID)
	: RuntimeForm( CLASS_KIND_T( ParametersRuntimeForm ) , aRID ),
	mParameters( )
	{
		mDataTable = new TableOfData(0);
	}

	ParametersRuntimeForm(const RuntimeID & aRID, avm_size_t nbParams)
	: RuntimeForm( CLASS_KIND_T( ParametersRuntimeForm ) , aRID ),
	mParameters( nbParams )
	{
		mDataTable = new TableOfData(nbParams);
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ParametersRuntimeForm(const ParametersRuntimeForm & aRuntime)
	: RuntimeForm( aRuntime ),
	mParameters( aRuntime.mParameters )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ParametersRuntimeForm()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mParameters
	 */
	const BF & saveParameter(InstanceOfData * anInstance);

	void appendParameter(const BF & anInstance, const BF & rvalue);


	void appendParameters(const BFList & paramsList);

	void appendParameters(const BFVector & paramsVector);


	inline const TableOfInstanceOfData & getParameters() const
	{
		return( mParameters );
	}


	inline avm_size_t getParametersSize() const
	{
		return( mParameters.size() );
	}


	inline const BF & getParameter(avm_offset_t offset) const
	{
		return( mParameters.get(offset) );
	}

	inline InstanceOfData * rawParameter(avm_offset_t offset) const
	{
		return( mParameters.rawAt(offset) );
	}

	inline bool hasParameter() const
	{
		return( mParameters.nonempty() );
	}


	inline void setParameter(avm_offset_t offset, const BF & anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anInstance )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		anInstance.to_ptr< InstanceOfData >()->setContainer( getExecutable() );
		mParameters.set(offset, anInstance);
	}

	inline void setParameter(avm_offset_t offset,
			const BF & anInstance, const BF & rvalue )
	{
//		anInstance->setContainer( getExecutable() );
//		anInstance->setOffset( offset );
		mParameters[ offset ] = anInstance;

		mDataTable->set(offset, rvalue);

//		anInstance->setRuntimeContainerRID( mRID );
	}


	// Variable
	inline virtual const TableOfInstanceOfData & getVariables() const
	{
		return( mParameters );
	}

	inline virtual InstanceOfData * rawVariable(avm_offset_t offset) const
	{
		return( mParameters.rawAt(offset) );
	}

	inline void resetOffset() const
	{
		TableOfInstanceOfData::const_raw_iterator itParam = mParameters.begin();
		TableOfInstanceOfData::const_raw_iterator endParam = mParameters.end();
		avm_offset_t offset = 0;
		for( ; itParam != endParam ; ++offset , ++itParam )
		{
			(itParam)->setOffset( offset );
		}
	}


	/**
	 * RUNTIME UPDATE
	 */
	void update(const BF & paramExpr);


	/**
	 * Serialization
	 */
	inline virtual void toStream(OutStream & os) const
	{
		toStream(NULL, os);
	}

	virtual void toStream(const ExecutionData * anED, OutStream & os) const;

	virtual void toStreamData(const ExecutionData * anED, OutStream & os) const;

	virtual void toFscnData(OutStream & os,
			const ExecutionData * anED, const RuntimeForm * aPreviousRF) const;

};


}

#endif /*RUNTIMEFORM_H_*/

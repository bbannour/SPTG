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
#ifndef TABLEOFDATA_H_
#define TABLEOFDATA_H_

#include <common/AvmObject.h>
#include <common/AvmPointer.h>
#include <common/Element.h>

#include <collection/BFContainer.h>
//#include <collection/Bitset.h>


namespace sep
{


class ArrayBF;
class BuiltinContainer;
class InstanceOfData;


class TableOfData :
		public AvmObject,
		public ArrayOfBF,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TableOfData )
{

	AVM_DECLARE_CLONABLE_BASE_CLASS( TableOfData )

protected:
	/**
	 * ATTRIBUTES
	 */
//	Bitset * mAssignedFlags;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TableOfData(std::size_t aSize)
	: AvmObject( ),
	ArrayOfBF( aSize )
//	mAssignedFlags( nullptr )
	{
		//!! NOTHING
	}

	TableOfData(const BFVector & dataTable)
	: AvmObject( ),
	ArrayOfBF( dataTable )
//	mAssignedFlags( nullptr )
	{
		//!! NOTHING
	}

	TableOfData(const TableOfData & aData)
	: AvmObject( aData ),
	ArrayOfBF( aData )
//	mAssignedFlags( nullptr )
	{
		//!! NOTHING
	}


	virtual ~TableOfData()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * for container of BF
	 */
	inline virtual BF & at(std::size_t offset)
	{
		return( mTable[offset] );
	}

	inline virtual const BF & at(std::size_t offset) const
	{
		return( mTable[offset] );
	}


	inline virtual BF & operator[](std::size_t offset)
	{
		return( mTable[offset] );
	}

	inline virtual const BF & operator[](std::size_t offset) const
	{
		return( mTable[offset] );
	}


	inline virtual BF & getWritable(std::size_t offset) const
	{
		mTable[offset].makeWritable();

		return( mTable[offset] );
	}

	inline virtual void makeWritable(std::size_t offset) const
	{
		mTable[offset].makeWritable();
	}

	inline virtual void set(std::size_t offset, const BF & bf) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset] = bf;
	}

	inline virtual void assign(std::size_t offset, const BF & bf)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset] = bf;

//		setAssigned( offset );
	}


	/**
	 * GETTER - SETTER
	 * mTable
	 */
	const BF & get(const InstanceOfData * aVariable) const;

	void set(const InstanceOfData * aVariable, const BF & aData) const;


	/**
	 * Serialization
	 */
	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const override
	{
		StringOutStream oss(indent);

		toStream(oss);

		return( oss.str() );
	}

	inline std::string toString(const BFVector & vars,
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream oss(indent);

		toStream(oss, vars);

		return( oss.str() );
	}

//	/**
//	 * TESTER -- SETTER
//	 * mAssignedFlags
//	 */
//	inline const Bitset * getAssigned() const
//	{
//		return( mAssignedFlags );
//	}
//
//	inline bool isAssigned(avm_offset_t offset) const
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;
//
//		return( (mAssignedFlags != nullptr)
//				&& mAssignedFlags->test(offset) );
//	}
//
//	inline void setAssigned(avm_offset_t offset)
//	{
//		if( mAssignedFlags == nullptr )
//		{
//			mAssignedFlags = new Bitset( mSize , false );
//		}
//		mAssignedFlags->set(offset, true);
//	}
//
//	inline void unsetAssigned(avm_offset_t offset)
//	{
//		if( mAssignedFlags != nullptr )
//		{
//			mAssignedFlags->set(offset, false);
//		}
//	}
//
//	inline void setAssigned(const Bitset * assignedFlags)
//	{
//		mAssignedFlags = ( (assignedFlags != nullptr) ?
//				new Bitset( * assignedFlags ) : nullptr );
//	}
//
//	inline void setAssignedUnion(const Bitset * assignedFlags)
//	{
//		if( assignedFlags != nullptr )
//		{
//			if( mAssignedFlags != nullptr )
//			{
//				(* mAssignedFlags) |= (* assignedFlags);
//			}
//			else
//			{
//				mAssignedFlags = new Bitset( * assignedFlags );
//			}
//		}
//	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const override;

	void toStream(OutStream & os, const BFVector & vars) const;

	// Due to [-Woverloaded-virtual=]
	using AvmObject::toStream;

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION for SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

AVM_DEFINE_AP_CLASS( TableOfData )

}

#endif /*TABLEOFDATA_H_*/

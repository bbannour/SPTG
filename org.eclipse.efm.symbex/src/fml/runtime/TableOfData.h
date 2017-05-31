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

#include <common/AvmPointer.h>
#include <common/AvmObject.h>

#include <collection/BFContainer.h>


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

	AVM_DECLARE_CLONABLE_CLASS( TableOfData )

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TableOfData(avm_size_t aSize)
	: AvmObject( ),
	ArrayOfBF( aSize )
	{
		//!! NOTHING
	}

	TableOfData(const BFVector & dataTable)
	: AvmObject( ),
	ArrayOfBF( dataTable )
	{
		//!! NOTHING
	}

	TableOfData(const TableOfData & aData)
	: AvmObject( aData ),
	ArrayOfBF( aData )
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
	inline virtual BF & at(avm_size_t offset)
	{
		return( mTable[offset] );
	}

	inline virtual const BF & at(avm_size_t offset) const
	{
		return( mTable[offset] );
	}


	inline virtual BF & operator[](avm_size_t offset)
	{
		return( mTable[offset] );
	}

	inline virtual const BF & operator[](avm_size_t offset) const
	{
		return( mTable[offset] );
	}


	inline virtual BF & getWritable(avm_size_t offset) const
	{
		mTable[offset].makeWritable();

		return( mTable[offset] );
	}

	inline virtual void makeWritable(avm_size_t offset) const
	{
		mTable[offset].makeWritable();
	}

	inline virtual void set(avm_size_t offset, const BF & bf) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , mSize ) << SEND_EXIT;

		mTable[offset] = bf;
	}


	/**
	 * GETTER - SETTER
	 * mTable
	 */
	const BF & get(const InstanceOfData * anInstance) const;

	void set(const InstanceOfData * anInstance, const BF & aData) const;


	/**
	 * Serialization
	 */
	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
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


	virtual void toStream(OutStream & os) const;

	void toStream(OutStream & os, const BFVector & vars) const;

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION for SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

AVM_DEFINE_AP_CLASS( TableOfData )



}

#endif /*TABLEOFDATA_H_*/

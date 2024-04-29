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
#ifndef LOCALRUNTIME_H_
#define LOCALRUNTIME_H_

#include <base/SmartPointer.h>

#include <common/Element.h>

#include <fml/executable/BaseAvmProgram.h>

#include <fml/expression/BuiltinArray.h>

#include <fml/runtime/TableOfData.h>


namespace sep
{

class BF;

class LocalRuntime;


class LocalRuntimeElement : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( LocalRuntimeElement )
{

	friend LocalRuntime;

	AVM_DECLARE_CLONABLE_CLASS( LocalRuntimeElement )


protected:
	/**
	 * ATTRIBUTES
	 */
	const BaseAvmProgram & mProgram;

	avm_offset_t mOffset;

	TableOfData mDataTable;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	LocalRuntimeElement(const BaseAvmProgram & aProgram)
	: Element( CLASS_KIND_T( LocalRuntime ) ),

	mProgram( aProgram ),
	mOffset( 0 ),
	mDataTable( aProgram.getVariablesSize() )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	LocalRuntimeElement(const LocalRuntimeElement & anElement)
	: Element( anElement ),

	mProgram( anElement.mProgram ),
	mOffset( anElement.mOffset ),
	mDataTable( anElement.mDataTable )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~LocalRuntimeElement()
	{
		//!! NOTHING
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const override;

};




class LocalRuntime :
		public SmartPointer< LocalRuntimeElement , DestroyElementPolicy >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( LocalRuntime )
{

private:
	/**
	 * TYPEDEF
	 */
	typedef SmartPointer< LocalRuntimeElement ,
						DestroyElementPolicy >  base_this_type;


public:
	/*
	 * STATIC ATTRIBUTES
	 */
	static LocalRuntime _NULL_;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	LocalRuntime()
	: base_this_type( )
	{
		//!! NOTHING
	}

	LocalRuntime(const BaseAvmProgram & aProgram)
	: base_this_type( new LocalRuntimeElement(aProgram) )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	LocalRuntime(const LocalRuntime & anElement)
	: base_this_type( anElement )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~LocalRuntime()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mProgram
	 */
	inline const BaseAvmProgram * getProgram() const
	{
		return( &( base_this_type::mPTR->mProgram ) );
	}


	/**
	 * GETTER - SETTER
	 * mInstance
	 */
	inline const ExecutableForm * getExecutable() const
	{
		return( getProgram()->getExecutable() );
	}


	/**
	 * GETTER - SETTER
	 * mOffset
	 */
	inline avm_offset_t getOffset() const
	{
		return( base_this_type::mPTR->mOffset );
	}

	inline void setOffset(avm_offset_t anOffset) const
	{
		base_this_type::mPTR->mOffset = anOffset;
	}


	/**
	 * GETTER - SETTER
	 * mDataTable
	 */
	inline TableOfData & getDataTable()
	{
		return( base_this_type::mPTR->mDataTable );
	}

	inline const TableOfData & getDataTable() const
	{
		return( base_this_type::mPTR->mDataTable );
	}


	inline BF & getData(std::size_t index) const
	{
		return( base_this_type::mPTR->mDataTable.at(index) );
	}

	inline bool hasData() const
	{
		return( base_this_type::mPTR->mDataTable.nonempty() );
	}

	inline void setData(std::size_t index, const BF & aData) const
	{
		base_this_type::mPTR->mDataTable.set(index, aData);
	}


	/**
	 * Serialization
	 */
	inline void toStream(OutStream & os) const
	{
		if( base_this_type::mPTR != nullptr )
		{
			base_this_type::mPTR->toStream(os);
		}
		else
		{
			os << "LocalRuntime<null>" << std::flush;
		}
	}

};


/**
 * Stack of LocalRuntime
 */
class StackOfLocalRuntime :  public AvmObject ,
		public Vector< LocalRuntime > ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( StackOfLocalRuntime )
{

	AVM_DECLARE_CLONABLE_BASE_CLASS( StackOfLocalRuntime )


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	StackOfLocalRuntime()
	: AvmObject( ),
	Vector< LocalRuntime >()
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	StackOfLocalRuntime(const StackOfLocalRuntime & aStack)
	: AvmObject( aStack ),
	Vector< LocalRuntime >( aStack )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~StackOfLocalRuntime()
	{
		//!! NOTHING
	}


	/**
	 * SETTER
	 * For LocalRuntime
	 */

	inline void setLocalRuntime(
			std::size_t offset, const LocalRuntime & aLocalRuntime)
	{
		Vector< LocalRuntime >::set(offset, aLocalRuntime);
	}


	/**
	 * PUSH - POP
	 * anAvmProgram
	 * BaseRuntimeForm
	 */

	inline void push(const LocalRuntime & aLocalRuntime)
	{
		aLocalRuntime.setOffset( size() );
		push_back( aLocalRuntime );
	}


	inline void pop()
	{
		if( nonempty() )
		{
			pop_last();
		}
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const override
	{
		for( const_iterator it = begin() ; it != end() ; ++it )
		{
			os << TAB << (*it).raw_pointer()->AVM_DEBUG_REF_COUNTER()
					<< "${ := " << AVM_NO_INDENT;

			(*it).toStream(os);

			os << END_INDENT << " }" << EOL_FLUSH;
		}
	}

};


}

#endif /*LOCALRUNTIME_H_*/

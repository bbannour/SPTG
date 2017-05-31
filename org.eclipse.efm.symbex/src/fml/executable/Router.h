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
#ifndef ROUTER_H_
#define ROUTER_H_

#include <base/SmartPointer.h>
#include <common/Element.h>

#include <collection/Vector.h>
#include <common/BF.h>

#include <fml/executable/RoutingData.h>


namespace sep
{


class InstanceOfMachine;
class InstanceOfPort;

class Router;


class RouterElement :
		public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( RouterElement )
{

	friend class Router;

	AVM_DECLARE_CLONABLE_CLASS( RouterElement )

protected:
	/*
	 * ATTRIBUTES
	 */
	// The container instance
	InstanceOfMachine * mMachine;

	avm_size_t mRouteID;

	TableOfRoutingData mInputRoutingTable;
	TableOfRoutingData mOutputRoutingTable;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	RouterElement(InstanceOfMachine * aMachine,
			avm_size_t aRouteID, avm_size_t msgCount = 0)
	: Element( CLASS_KIND_T( Router ) ),
	mMachine( aMachine ),
	mRouteID( aRouteID ),
	mInputRoutingTable( msgCount ),
	mOutputRoutingTable( msgCount )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	explicit RouterElement(const RouterElement & anElement)
	: Element( anElement ),
	mMachine( anElement.mMachine ),
	mRouteID( anElement.mRouteID ),
	mInputRoutingTable( anElement.mInputRoutingTable ),
	mOutputRoutingTable( anElement.mOutputRoutingTable )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~RouterElement()
	{
		//!! NOTHING
	}

	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const;

};


class Router :
		public SmartPointer< RouterElement , DestroyElementPolicy >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Router )
{

private:
	/**
	 * TYPEDEF
	 */
	typedef SmartPointer< RouterElement ,
						DestroyElementPolicy >  base_this_type;


public:
	/*
	 * STATIC ATTRIBUTES
	 */
	static Router _NULL_;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Router()
	: base_this_type( )
	{
		//!! NOTHING
	}

	Router(InstanceOfMachine * aMachine,
			avm_size_t aRouteID, avm_size_t msgCount = 0)
	: base_this_type( new RouterElement(aMachine, aRouteID, msgCount) )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Router(const Router & anElement)
	: base_this_type( anElement )
	{
		//!! NOTHING
	}

public:
	/**
	 * DESTRUCTOR
	 */
	virtual ~Router()
	{
		//!! NOTHING
	}


	/**
	 * operator=
	 */
	inline Router & operator=(const BF & other)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( other.is< Router >() )
				<< "Invalid Assignment Cast of an inherit BF Class !!"
				<< SEND_EXIT;

		if( base_this_type::mPTR != other.raw_pointer() )
		{
			release_acquire(
					static_cast< RouterElement * >( other.raw_pointer() ) );
		}
		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * mMachine
	 */
	inline InstanceOfMachine * getMachine() const
	{
		return( base_this_type::mPTR->mMachine );
	}

	inline bool hasMachine() const
	{
		return( base_this_type::mPTR->mMachine != NULL );
	}


	/**
	 * GETTER
	 * mRouteID
	 */
	inline avm_size_t getRouteID() const
	{
		return( base_this_type::mPTR->mRouteID );
	}

	inline avm_size_t getTotalRouteCount() const
	{
		return( std::max(base_this_type::mPTR->mInputRoutingTable.size(),
				base_this_type::mPTR->mOutputRoutingTable.size()) );
	}


	/**
	 * GETTER - SETTER
	 * mInputRoutingTable
	 */
	inline TableOfRoutingData & getInputRoutingTable()
	{
		return( base_this_type::mPTR->mInputRoutingTable );
	}

	inline const TableOfRoutingData & getInputRoutingTable() const
	{
		return( base_this_type::mPTR->mInputRoutingTable );
	}

	inline RoutingData & getInputRouting(avm_offset_t offset)
	{
		return( base_this_type::mPTR->mInputRoutingTable.get(offset) );
	}

	inline const RoutingData & getInputRouting(avm_offset_t offset) const
	{
		return( base_this_type::mPTR->mInputRoutingTable.get(offset) );
	}

	inline bool hasInputRouting(avm_offset_t offset) const
	{
		return( base_this_type::mPTR->mInputRoutingTable.get(offset).valid() );
	}

	inline bool hasntInputRouting(avm_offset_t offset) const
	{
		return( base_this_type::mPTR->mInputRoutingTable.get(offset).invalid() );
	}


	inline void appendInputRouting(const RoutingData & aRoutingData) const
	{
		base_this_type::mPTR->mInputRoutingTable.append(aRoutingData);
	}

	void appendInputRouting(InstanceOfPort * aPortInstance,
			const RoutingData & aRoutingData);


	void setInputRouting(InstanceOfPort * aPortInstance,
			const RoutingData & aRoutingData) const;

	void setInputRouting(avm_offset_t offset,
			const RoutingData & aRoutingData) const
	{
		base_this_type::mPTR->mInputRoutingTable.set(offset, aRoutingData);
	}


	/**
	 * GETTER - SETTER
	 * mOutputRoutingTable
	 */
	inline TableOfRoutingData & getOutputRoutingTable()
	{
		return( base_this_type::mPTR->mOutputRoutingTable );
	}

	inline const TableOfRoutingData & getOutputRoutingTable() const
	{
		return( base_this_type::mPTR->mOutputRoutingTable );
	}

	inline RoutingData & getOutputRouting(avm_offset_t offset)
	{
		return( base_this_type::mPTR->mOutputRoutingTable.get(offset) );
	}

	inline const RoutingData & getOutputRouting(avm_offset_t offset) const
	{
		return( base_this_type::mPTR->mOutputRoutingTable.get(offset) );
	}

	inline bool hasOutputRouting(avm_offset_t offset) const
	{
		return( base_this_type::mPTR->mOutputRoutingTable.get(offset).valid() );
	}

	inline bool hasntOutputRouting(avm_offset_t offset) const
	{
		return( base_this_type::mPTR->mOutputRoutingTable.get(offset).invalid() );
	}


	inline void appendOutputRouting(const RoutingData & aRoutingData) const
	{
		base_this_type::mPTR->mOutputRoutingTable.append(aRoutingData);
	}

	void appendOutputRouting(InstanceOfPort * aPortInstance,
			const RoutingData & aRoutingData);


	void setOutputRouting(InstanceOfPort * aPortInstance,
			const RoutingData & aRoutingData) const;

	void setOutputRouting(avm_offset_t offset,
			const RoutingData & aRoutingData) const
	{
		base_this_type::mPTR->mOutputRoutingTable.set(offset, aRoutingData);
	}


	/**
	 * TESTER
	 */
	inline bool hasRouting(InstanceOfPort * aPort) const
	{
		return( hasInputRouting(aPort) || hasOutputRouting(aPort) );
	}

	bool hasInputRouting(InstanceOfPort * aPort) const;

	bool hasOutputRouting(InstanceOfPort * aPort) const;


	/**
	 * Serialization
	 */
	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		if( base_this_type::mPTR != NULL )
		{
			StringOutStream oss(indent);

			base_this_type::mPTR->toStream( oss );

			return( oss.str() );
		}
		else
		{
			return( indent.TABS + "Router<null>" + indent.EOL );
		}
	}

	inline void toStream(OutStream & os) const
	{
		if( base_this_type::mPTR != NULL )
		{
			base_this_type::mPTR->toStream(os);
		}
		else
		{
			os << "Router<null>" << std::flush;
		}
	}

};


/**
 * TYPE DEFINITION
 * TABLE of ROUTER
 */
typedef  Vector< Router >  TableOfRouter;




}

#endif /*ROUTER_H_*/

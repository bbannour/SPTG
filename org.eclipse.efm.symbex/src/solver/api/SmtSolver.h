/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 déc. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SOLVER_BASESMTSOLVER_H_
#define SOLVER_BASESMTSOLVER_H_

#include <solver/api/SatSolver.h>

#include <common/BF.h>

#include <collection/Bitset.h>
#include <collection/Vector.h>

#include <fml/executable/InstanceOfData.h>


#define SMT_ARGS_DATA_INITIAL_COUNT      16

#define SMT_ARGS_DATA_ROOT_CAPACITY     512
#define SMT_ARGS_DATA_DEFAULT_CAPACITY   64

#define SMT_ARGS_DATA_INCR_CAPACITY      16


namespace sep
{

class Configuration;

/**
 * if 'array_else_vector' is true
 *  then using ARRAY   for element of cache
 *  else using VECTOR  for element of cache
 */
template< class VarDecl_T , class Sort_T , class Expr_T , bool array_else_vector >
class SmtSolverTraits  :  public SatSolver
{

protected:
	/**
	 * ATTRIBUTES
	 **/
	TableOfInstanceOfData  mTableOfParameterInstance;
	Vector< VarDecl_T >    mTableOfParameterDecl;

	Vector< Expr_T    >    mTableOfParameterExpr;
	Bitset                 mBitsetOfConstrainedParameter;
	Bitset                 mBitsetOfPositiveParameter;
	Bitset                 mBitsetOfStrictlyPositiveParameter;

	Vector< VarDecl_T >    mTableOfVariableDecl;
	Vector< Expr_T    >    mTableOfVariableExpr;

	Vector< Expr_T >       mTableOfParameterExprForNewFormula;
	Vector< Expr_T >       mTableOfParameterExprForOldFormula;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SmtSolverTraits()
	: SatSolver(),
	mTableOfParameterInstance( ),
	mTableOfParameterDecl( ),

	mTableOfParameterExpr( ),
	mBitsetOfConstrainedParameter( ),
	mBitsetOfPositiveParameter( ),
	mBitsetOfStrictlyPositiveParameter( ),

	mTableOfVariableDecl( ),
	mTableOfVariableExpr( ),

	mTableOfParameterExprForNewFormula( ),
	mTableOfParameterExprForOldFormula( )
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~SmtSolverTraits()
	{
		destroyChecker();
	}


	/**
	 * CREATE - DESTROY
	 * ValidityChecker
	 */
	inline virtual bool destroyChecker()
	{
		resetTable();

		return( true );
	}


	virtual bool resetTable()
	{
		if( mTableOfParameterInstance.nonempty() )
		{
			BFVector::raw_iterator< InstanceOfData > it =
					mTableOfParameterInstance.begin();
			BFVector::raw_iterator< InstanceOfData > itEnd =
					mTableOfParameterInstance.end();
			for( ++it /* ignore sentinel */ ; it != itEnd ; ++it )
			{
				(it)->setMark(0);
			}
			mTableOfParameterInstance.clear();
		}
		mTableOfParameterInstance.append( BF::REF_NULL );

		mTableOfParameterDecl.clear();
		mTableOfParameterExpr.clear();

		mTableOfVariableDecl.clear();
		mTableOfVariableExpr.clear();

		mTableOfParameterExprForNewFormula.clear();
		mTableOfParameterExprForOldFormula.clear();

		return( true );
	}


};


/**
 * if 'need_type_cst_decl' is true
 *  then declare Types for BOOL, INT, RAT, REAL, ...
 *   and Constants for TRUE, FALE, ZERO, ONE, ...
 *  else using nop
 */
template< class VarDecl_T , class Sort_T , class Expr_T ,
		bool array_else_vector , bool need_type_cst_decl >
class SmtSolver;


template< class VarDecl_T , class Sort_T , class Expr_T , bool array_else_vector >
class SmtSolver< VarDecl_T , Sort_T , Expr_T , array_else_vector , true > :
	public SmtSolverTraits< VarDecl_T , Sort_T , Expr_T , array_else_vector >
{


protected:
	/**
	 * TYPEDEF
	 */
	typedef SmtSolver< VarDecl_T , Sort_T , Expr_T ,
			array_else_vector , true >  base_this_type;


protected:
	/**
	 * ATTRIBUTES
	 **/
	Sort_T SMT_TYPE_BOOL;

	Sort_T SMT_TYPE_ENUM;

	Sort_T SMT_TYPE_UINTEGER;
	Sort_T SMT_TYPE_INTEGER;

	Sort_T SMT_TYPE_BV32;
	Sort_T SMT_TYPE_BV64;

	Sort_T SMT_TYPE_URATIONAL;
	Sort_T SMT_TYPE_RATIONAL;

	Sort_T SMT_TYPE_UREAL;
	Sort_T SMT_TYPE_REAL;

	Sort_T SMT_TYPE_NUMBER;

	Sort_T SMT_TYPE_STRING;

	Expr_T SMT_CST_BOOL_TRUE;
	Expr_T SMT_CST_BOOL_FALSE;

	Expr_T SMT_CST_INT_ZERO;
	Expr_T SMT_CST_INT_ONE;

public:
	/**
	* CONSTRUCTOR
	* Default
	*/
	SmtSolver(Sort_T nullSort, Expr_T nullExpr)
	: SmtSolverTraits< VarDecl_T , Sort_T , Expr_T , array_else_vector >( ),

	SMT_TYPE_BOOL( nullSort ),

	SMT_TYPE_UINTEGER( nullSort ),
	SMT_TYPE_INTEGER ( nullSort ),

	SMT_TYPE_BV32( nullSort ),
	SMT_TYPE_BV64( nullSort ),

	SMT_TYPE_URATIONAL( nullSort ),
	SMT_TYPE_RATIONAL ( nullSort ),

	SMT_TYPE_UREAL( nullSort ),
	SMT_TYPE_REAL ( nullSort ),

	SMT_TYPE_NUMBER( nullSort ),

	SMT_TYPE_STRING( nullSort ),

	SMT_CST_BOOL_TRUE ( nullExpr ),
	SMT_CST_BOOL_FALSE( nullExpr ),

	SMT_CST_INT_ZERO( nullExpr ),
	SMT_CST_INT_ONE ( nullExpr )
	{
		//!!! NOTHING
	}


	/**
	* DESTRUCTOR
	*/
	virtual ~SmtSolver()
	{
		//!!! NOTHING
	}


protected:

	template< class data_t , bool is_array_else_vector >
	struct _ARGS_DATA_TRAITS_;

	template< class data_t >
	struct _ARGS_DATA_TRAITS_< data_t , true >
	{
		/**
		 * ATTRIBUTES
		 */
		data_t * table;

		std::size_t capacity;
		std::size_t count;
		std::size_t idx;

		/**
		 * CONSTRUCTOR
		 * Default
		 */
		_ARGS_DATA_TRAITS_( std::size_t aCapacity , std::size_t aCount )
		: table( new data_t[aCapacity] ),
		capacity( aCapacity ),
		count( aCount ),
		idx( 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
			AVM_OS_TRACE << "new _ARGS_DATA_ as array  :>"
					<< " capacity = " << std::setw(4) << capacity
					<< " : count = " << std::setw(4) << count
					<< " @" << std::intptr_t( this ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
		}

		virtual ~_ARGS_DATA_TRAITS_()
		{
			delete[]( table );
		}


		inline void intialize()
		{
			//!!! NOTHING
		}

		inline void finalize()
		{
//			for( idx = 0 ; idx < count ; ++idx )
//			{
//				table[ idx ] = nullptr;
//			}
			//!!! NOTHING
		}

	};


	template< class data_t >
	struct _ARGS_DATA_TRAITS_< data_t , false >
	{
		/**
		 * ATTRIBUTES
		 */
		std::vector< data_t > table;

		std::size_t capacity;
		std::size_t count;
		std::size_t idx;

		/**
		 * CONSTRUCTOR
		 * Default
		 */
		_ARGS_DATA_TRAITS_( std::size_t aCapacity , std::size_t aCount )
		: table( aCapacity ),
		capacity( aCapacity ),
		count( aCount ),
		idx( 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
			AVM_OS_TRACE << "new _ARGS_DATA_ as array  :>"
					<< " capacity = " << std::setw(4) << capacity
					<< " : count = " << std::setw(4) << count
					<< " @" << std::intptr_t( this ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
		}

		virtual ~_ARGS_DATA_TRAITS_()
		{
			table.clear();
		}


		inline void intialize()
		{
			table.resize( count );

//AVM_IF_DEBUG_LEVEL_FLAG_AND( HIGH , SMT_SOLVING , (capacity != table.capacity()) )
			if(  capacity != table.capacity() )
			{
				AVM_OS_TRACE << "new _ARGS_TRAITS_ as vector :>"
						<< " capacity = " << capacity
						<< " vector<" << table.capacity()
						<< "> : count = " << count
						<< " @" << std::intptr_t( this ) << std::endl;
			}
//AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( HIGH , SMT_SOLVING )
		}

		inline void finalize()
		{
			table.clear();
		}

	};


	typedef _ARGS_DATA_TRAITS_<Expr_T, array_else_vector > ARGS_DATA;


	static List< ARGS_DATA * > ARG_CACHE;


	inline static ARGS_DATA * newARGS( std::size_t count )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
		AVM_OS_TRACE << "newARGS :> count = " << std::setw(4) << count;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )

		ARGS_DATA * arg = nullptr;
//		if( ARG_CACHE.populated() )
//		{
//			if( ARG_CACHE.nonempty() &&
//					(ARG_CACHE.last()->capacity > count) )
//			{
//				ARG_CACHE.pop_last_to( arg );
//				arg->count = count;
//			}
//			else if( ARG_CACHE.nonempty() &&
//					(ARG_CACHE.first()->capacity > count) )
//			{
//				ARG_CACHE.pop_first_to( arg );
//				arg->count = count;
//			}
//			else
//			{
//				arg = new ARGS_TABLE(count, count);
//			}
//		}
//		else
			if( ARG_CACHE.nonempty() && (ARG_CACHE.last()->capacity > count) )
		{
			ARG_CACHE.pop_last_to( arg );
			arg->count = count;
			arg->idx = 0;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
			AVM_OS_TRACE << " @" << std::intptr_t( arg )
					<< " with capacity = " << arg->capacity << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
		}
		else
		{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
			AVM_OS_TRACE << " ==> " << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )

			arg = new ARGS_DATA(count + SMT_ARGS_DATA_INCR_CAPACITY, count);
		}

		return( arg );
	}


	inline static void freeARGS( ARGS_DATA * & arg )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
		AVM_OS_TRACE << "freeARGS:> count = " << std::setw(4) << arg->count
				<< " @" << std::intptr_t( arg )
				<< " with capacity = " << arg->capacity << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )

		ARG_CACHE.append( arg );
	}


public:

	/**
	* Cache lifecycle
	*/
	inline static void initCache()
	{
		for( std::size_t i = 0 ; i < SMT_ARGS_DATA_INITIAL_COUNT ; ++i )
		{
			ARG_CACHE.append(new ARGS_DATA( SMT_ARGS_DATA_DEFAULT_CAPACITY, 0) );
		}
		ARG_CACHE.append(new ARGS_DATA( SMT_ARGS_DATA_ROOT_CAPACITY, 0) );
	}

	inline static void finalizeCache( )
	{
		std::size_t args_count = 0;

		while( ARG_CACHE.nonempty() )
		{
			++args_count;
			delete( ARG_CACHE.pop_last() );
		}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
		AVM_OS_TRACE << "Solver::finalize#cache:> count = " << args_count
				<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SMT_SOLVING , MEMORY_MANAGEMENT )
	}


	struct ARGS
	{
		/**
		 * ATTRIBUTES
		 */
		ARGS_DATA * mData;

		/**
		 * CONSTRUCTOR
		 * Default
		 */
		ARGS( std::size_t count )
		: mData( newARGS(count) )
		{
			mData->intialize( );
		}

		virtual ~ARGS()
		{
			mData->finalize( );

			freeARGS( mData );
		}


		/**
		* OPERATORS
		*/
		inline ARGS_DATA * operator-> () const
		{
AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mData ) << "ARGS_DATA Pointer !!!"
			<< SEND_EXIT;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

			return( mData );
		}

		inline Expr_T & operator[](std::size_t offset) const
		{
			return( mData->table[ offset ] );
		}

		// Table Iterator
		inline bool hasNext() const
		{
			return( mData->idx < mData->count );
		}

		inline std::size_t offset() const
		{
			return( mData->idx );
		}

		inline void iter()
		{
			mData->idx = 0;
		}

		inline Expr_T & current()
		{
			return( mData->table[ mData->idx ] );
		}

		inline Expr_T & next()
		{
			return( mData->table[ mData->idx++ ] );
		}

		inline void next(Expr_T val)
		{
			mData->table[ mData->idx++ ] = val;
		}

//		inline void next(const data_t & val)
//		{
//			mData->table[ mData->idx++ ] = val;
//		}

	};

};



template< class VarDecl_T , class Sort_T , class Expr_T , bool array_else_vector >
List< typename SmtSolver< VarDecl_T , Sort_T , Expr_T ,
		array_else_vector , true >::ARGS_DATA * >
SmtSolver< VarDecl_T , Sort_T , Expr_T , array_else_vector , true >::ARG_CACHE;




template< class VarDecl_T , class Sort_T , class Expr_T , bool array_else_vector >
class SmtSolver< VarDecl_T , Sort_T , Expr_T ,  array_else_vector , false > :
	public SmtSolverTraits< VarDecl_T , Sort_T , Expr_T , array_else_vector >
{


protected:
	/**
	 * TYPEDEF
	 */
	typedef SmtSolver< VarDecl_T , Sort_T , Expr_T ,
			array_else_vector , false >  base_this_type;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SmtSolver()
	: SmtSolverTraits< VarDecl_T , Sort_T , Expr_T , array_else_vector >( )
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~SmtSolver()
	{
		//!!! NOTHING
	}


	/**
	* Cache lifecycle
	*/
	inline static void initCache()
	{
		//!!! NOTHING
	}

	inline static void finalizeCache( )
	{
		//!!! NOTHING
	}

};



} /* namespace sep */
#endif /* SOLVER_BASESMTSOLVER_H_ */

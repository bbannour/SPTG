/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 05 nov. 2017
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_COMMON_LIFECYCLEELEMENT_H_
#define FML_COMMON_LIFECYCLEELEMENT_H_

#include <util/avm_numeric.h>

namespace sep
{

class Lifecycle
{

protected:
	/**
	 * CREATION_STAGE
	 * 3 bits
	 */
	enum CREATION_STAGE
	{
		CREATION_UNDEFINED_STAGE         = 0x000,

		CREATION_PARSING_STAGE           = 0x001,

		CREATION_CONFIGURING_STAGE       = 0x002,

		CREATION_COMPILING_STAGE         = 0x003,

		CREATION_LOADING_STAGE           = 0x004,

		CREATION_EVALUATION_STAGE        = 0x005,

	};


	/**
	 * LIFECYCLE_STATUS
	 * 8 bits
	 */
	enum LIFECYCLE_STATUS
	{
		LIFECYCLE_UNDEFINED_STATUS       = 0x000,

		LIFECYCLE_CREATED_STATUS         = 0x001,

		LIFECYCLE_COMPILING_STATUS       = 0x002,

		LIFECYCLE_COMPILED_STATUS        = 0x004,

		LIFECYCLE_OPTIMIZING_STATUS      = 0x008,

		LIFECYCLE_OPTIMIZED_STATUS       = 0x010,

		LIFECYCLE_FULLY_BUILT_STATUS     = LIFECYCLE_CREATED_STATUS
		                                 | LIFECYCLE_COMPILED_STATUS
		                                 | LIFECYCLE_OPTIMIZED_STATUS,

		LIFECYCLE_EVALUATED_STATUS       = 0x020,

		LIFECYCLE_FINALIZING_STATUS      = 0x040,

		LIFECYCLE_FINALIZED_STATUS       = 0x080
	};



	/**
	 * TYPEDEF
	 */
	typedef std::uint8_t  bit_field_t;

	/**
	 * BIT FIELDS
	 */
	bit_field_t creation  : 3;

	bit_field_t lifecycle : 8;


public:
	/**
	 * CONSTRUCTORS
	 */
	Lifecycle(CREATION_STAGE allocStage = CREATION_UNDEFINED_STAGE)
	: creation( allocStage ),
	lifecycle( LIFECYCLE_CREATED_STATUS )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Lifecycle()
	{
		//!! NOTHING
	}


	/**
	 *
	 */
	inline bool hasFlag() const
	{
		return( (creation != CREATION_UNDEFINED_STAGE)
				&& (lifecycle != LIFECYCLE_CREATED_STATUS) );
	}


	/**
	 * GETTER
	 * creation stage
	 */
	inline bit_field_t getCreationStage() const
	{
		return( creation );
	}


	/**
	 * GETTER - SETTER
	 * creation CREATION_PARSING_STAGE
	 */
	inline bool isCreateAtParsingStage() const
	{
		return( creation == CREATION_PARSING_STAGE );
	}

	inline void setCreateAtParsingStage()
	{
		creation = CREATION_PARSING_STAGE;
	}


	/**
	 * GETTER - SETTER
	 * creation CREATION_COMPILING_STAGE
	 */
	inline bool isCreateAtCompilingStage() const
	{
		return( creation == CREATION_COMPILING_STAGE );
	}

	inline void setCreateAtCompilingStage()
	{
		creation = CREATION_COMPILING_STAGE;
	}


	/**
	 * GETTER - SETTER
	 * creation CREATION_LOADING_STAGE
	 */
	inline bool isCreateAtLoadingStage() const
	{
		return( creation == CREATION_LOADING_STAGE );
	}

	inline void setCreateAtLoadingStage()
	{
		creation = CREATION_LOADING_STAGE;
	}


	/**
	 * GETTER - SETTER
	 * creation CREATION_EVALUATION_STAGE
	 */
	inline bool isCreateAtEvaluationStage() const
	{
		return( creation == CREATION_EVALUATION_STAGE );
	}

	inline void setCreateAtEvaluationStage()
	{
		creation = CREATION_EVALUATION_STAGE;
	}


	/**
	 * GETTER
	 * lifecycle status
	 */
	inline bit_field_t getLifecycleFlags() const
	{
		return( lifecycle );
	}


	/**
	 * GETTER - SETTER
	 * lifecycle LIFECYCLE_CREATED_STATUS
	 */
	inline bool isCreated() const
	{
		return( (lifecycle & LIFECYCLE_CREATED_STATUS) != 0 );
	}


	/**
	 * GETTER - SETTER
	 * lifecycle LIFECYCLE_COMPILED_STATUS
	 */
	inline bool isCompiling() const
	{
		return( (lifecycle & LIFECYCLE_COMPILING_STATUS) != 0 );
	}

	inline void setCompiling()
	{
		lifecycle |= LIFECYCLE_COMPILING_STATUS;
	}

	/**
	 * GETTER - SETTER
	 * lifecycle LIFECYCLE_COMPILED_STATUS
	 */
	inline bool isCompiled() const
	{
		return( (lifecycle & LIFECYCLE_COMPILED_STATUS) != 0 );
	}

	inline void setCompiled()
	{
		if( (lifecycle & LIFECYCLE_COMPILING_STATUS) != 0 )
		{
			lifecycle &= (~ LIFECYCLE_COMPILING_STATUS);
		}

		lifecycle |= LIFECYCLE_COMPILED_STATUS;
	}


	/**
	 * GETTER - SETTER
	 * lifecycle LIFECYCLE_OPTIMIZED_STATUS
	 */
	inline bool isOptimizing() const
	{
		return( (lifecycle & LIFECYCLE_OPTIMIZING_STATUS) != 0 );
	}

	inline void setOptimizing()
	{
		lifecycle |= LIFECYCLE_OPTIMIZING_STATUS;
	}


	/**
	 * GETTER - SETTER
	 * lifecycle LIFECYCLE_OPTIMIZED_STATUS
	 */
	inline bool isOptimized() const
	{
		return( (lifecycle & LIFECYCLE_OPTIMIZED_STATUS) != 0 );
	}

	inline void setOptimized()
	{
		if( (lifecycle & LIFECYCLE_OPTIMIZING_STATUS) != 0 )
		{
			lifecycle &= (~ LIFECYCLE_OPTIMIZING_STATUS);
		}

		lifecycle |= LIFECYCLE_OPTIMIZED_STATUS;
	}


	/**
	 * GETTER
	 * lifecycle LIFECYCLE_FULLY_BUILT_STATUS
	 */
	inline bool isFullyBuilt() const
	{
		return( lifecycle == LIFECYCLE_FULLY_BUILT_STATUS );
	}


	/**
	 * GETTER - SETTER
	 * lifecycle LIFECYCLE_EVALUATED_STATUS
	 */
	inline bool isEvaluated() const
	{
		return( (lifecycle & LIFECYCLE_EVALUATED_STATUS) != 0 );
	}

	inline void setEvaluated()
	{
		lifecycle |= LIFECYCLE_EVALUATED_STATUS;
	}


	/**
	 * GETTER - SETTER
	 * lifecycle LIFECYCLE_FINALIZED_STATUS
	 */
	inline bool isFinalizing() const
	{
		return( (lifecycle & LIFECYCLE_FINALIZING_STATUS) != 0 );
	}

	inline void setFinalizing()
	{
		lifecycle |= LIFECYCLE_FINALIZING_STATUS;
	}


	/**
	 * GETTER - SETTER
	 * lifecycle LIFECYCLE_FINALIZED_STATUS
	 */
	inline bool isFinalized() const
	{
		return( (lifecycle & LIFECYCLE_FINALIZED_STATUS) != 0 );
	}

	inline void setFinalized()
	{
		if( (lifecycle & LIFECYCLE_FINALIZING_STATUS) != 0 )
		{
			lifecycle &= (~ LIFECYCLE_FINALIZING_STATUS);
		}

		lifecycle |= LIFECYCLE_FINALIZED_STATUS;
	}



};


/**
 * Lifecycle Implementation
 */
class LifecycleImpl
{

protected:
	/**
	 * ATTRIBUTES
	 */
	Lifecycle mlifecycle;


public:
	/**
	 * CONSTRUCTOR
	 */
	LifecycleImpl()
	: mlifecycle( )
	{
		//!! NOTHING
	}

	LifecycleImpl(const Lifecycle & aObjectFlags)
	: mlifecycle( aObjectFlags )
	{
		//!! NOTHING
	}

	LifecycleImpl(const LifecycleImpl & aCopy)
	: mlifecycle( aCopy.mlifecycle )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	~LifecycleImpl()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * mObjectFlags
	 */
	inline const Lifecycle & getLifecycle() const
	{
		return( mlifecycle );
	}

	inline Lifecycle & getwLifecycle()
	{
		return( mlifecycle );
	}

	inline bool hasLifecycle() const
	{
		return( mlifecycle.hasFlag() );
	}

	inline void set(const Lifecycle & aLifecycle)
	{
		mlifecycle = aLifecycle;
	}

};



} /* namespace sep */

#endif /* FML_COMMON_LIFECYCLEELEMENT_H_ */

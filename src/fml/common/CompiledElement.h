/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_COMMON_COMPILEDELEMENT_H_
#define FML_COMMON_COMPILEDELEMENT_H_


namespace sep
{


class CompiledElement
{

protected:
	/**
	 * ATTRIBUTES
	 */
	bool mCompiledFlag;

	bool mOptimizedFlag;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	CompiledElement()
	: mCompiledFlag( false ),
	mOptimizedFlag( false )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	CompiledElement(const CompiledElement & anElement)
	: mCompiledFlag( anElement.mCompiledFlag ),
	mOptimizedFlag( anElement.mOptimizedFlag )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~CompiledElement()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mCompiledFlag
	 */
	inline bool isCompiled() const
	{
		return( mCompiledFlag );
	}

	inline void setCompiled(bool isCompiled = true)
	{
		mCompiledFlag = isCompiled;
	}


	/**
	 * GETTER - SETTER
	 * mOptimizedFlag
	 */
	inline bool isOptimized() const
	{
		return( mOptimizedFlag );
	}

	inline void setOptimized(bool isOptimized = true)
	{
		mOptimizedFlag = isOptimized;
	}

	/**
	 * GETTER - SETTER
	 * mCompiledFlag
	 * mOptimizedFlag
	 */
	inline void setCompiledOptimized(bool isCompiled, bool isOptimized)
	{
		setCompiled( isCompiled );

		setOptimized( isOptimized );
	}


};


} /* namespace sep */

#endif /* FML_COMMON_COMPILEDELEMENT_H_ */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 févr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SOLVER_SOLVERDEF_H_
#define SOLVER_SOLVERDEF_H_


/**
 * DEFINE MACRO W.R.T. LICENSE CONSTRAINT
 */
#if defined( _ECLIPSE_PUBLIC_LICENSE_ )


//// Default
//#define _AVM_SOLVER_CVC5_
//#define _AVM_SOLVER_CVC4_
//
//// Incubation
//#define _AVM_SOLVER_Z3_

// Experimental
#if defined( _AVM_SOLVER_YICES_V2_ )
	#undef _AVM_SOLVER_YICES_V2_
#endif /* _AVM_SOLVER_YICES_V2_ */

// Deprecated
#if defined( _AVM_SOLVER_OMEGA_ )
	#undef _AVM_SOLVER_OMEGA_
#endif /* _AVM_SOLVER_OMEGA_ */


#else


//// Default
//#if not defined( _AVM_SOLVER_CVC5_ )
//#define _AVM_SOLVER_CVC5_
//#endif /* _AVM_SOLVER_CVC5_ */
//
//#if not defined( _AVM_SOLVER_CVC4_ )
//#define _AVM_SOLVER_CVC4_
//#endif /* _AVM_SOLVER_CVC4_ */
//
//// Incubation
//#if not defined( _AVM_SOLVER_Z3_ )
//#define _AVM_SOLVER_Z3_
//#endif /* _AVM_SOLVER_Z3_ */
//
//// Experimental
//#if not defined( _AVM_SOLVER_YICES_V2_ )
//#define _AVM_SOLVER_YICES_V2_
//#endif /* _AVM_SOLVER_YICES_V2_ */
//
//
//// Deprecated
//#if not defined( _AVM_SOLVER_OMEGA_ )
//#define _AVM_SOLVER_OMEGA_
//#endif /* _AVM_SOLVER_OMEGA_ */


#endif /* _ECLIPSE_PUBLIC_LICENSE_ */


#include <string>

//#if defined( _AVM_SOLVER_OMEGA_ )
//
//#endif /* _AVM_SOLVER_OMEGA_ */


//#if defined( _AVM_SOLVER_CVC5_ )
//
//#elif defined( _AVM_SOLVER_CVC4_ )
//
//#endif /* _AVM_SOLVER_CVC_ */
//
//
//#if defined( _AVM_SOLVER_YICES_V2_ )
//
//#elif defined( _AVM_SOLVER_YICES_V1_ )
//
//#endif /* _AVM_SOLVER_YICES_ */
//
//
//#if defined( _AVM_SOLVER_Z3_ )
//
//#endif /* _AVM_SOLVER_Z3_ */


namespace sep
{


class OutStream;


class SolverDef
{

public:
	/**
	 * TYPE DECLARATIONS
	 */

	enum SATISFIABILITY_RING {
		UNSATISFIABLE = 0,
		SATISFIABLE = 1,

		ABORT_SAT,
		UNKNOWN_SAT
	};


	enum VALIDITY_RING {
		INVALID = 0,
		VALID = 1,

		ABORT_VALID,
		UNKNOWN_VALID
	};


	/**
	 * TYPE DECLARATIONS
	 */
	enum SOLVER_KIND
	{
		SOLVER_UNDEFINED_KIND   = 0x0000,

		SOLVER_OMEGA_KIND       = 0x00001,

		SOLVER_YICES1_KIND      = 0x00010,
		SOLVER_YICES2_KIND      = 0x00020,

		SOLVER_YICES_KIND       = SOLVER_YICES1_KIND
	                            | SOLVER_YICES2_KIND,

		SOLVER_Z3_KIND          = 0x00100,

		SOLVER_CVC4_KIND        = 0x01000,
		SOLVER_CVC4_BV32_KIND   = 0x02000,

		SOLVER_CVC5_KIND        = 0x04000,
		SOLVER_CVC5_BV32_KIND   = 0x08000,


		SOLVER_CVC_KIND         = SOLVER_CVC4_KIND
	                            | SOLVER_CVC5_KIND,

		SOLVER_CVC_BV_KIND      = SOLVER_CVC4_BV32_KIND
								| SOLVER_CVC5_BV32_KIND
	};


public:
	/**
	* CONSTRUCTOR
	* Default
	*/
	SolverDef()
	{
		//!! NOTHING
	}


	/**
	* DESTRUCTOR
	*/
	virtual ~SolverDef()
	{
		//!! NOTHING
	}

	/**
	 * ATTRIBUTES
	 */
	static bool DEFAULT_SOLVER_USAGE_FLAG;

	static SolverDef::SOLVER_KIND DEFAULT_SOLVER_KIND;


	/**
	 * toString
	 */
	static std::string strSatisfiability(SATISFIABILITY_RING ring);

	static std::string strValidity(VALIDITY_RING ring);

	static std::string strSolver(SOLVER_KIND king);

	/**
	 * toSolver
	 */
	static SOLVER_KIND toSolver(std::string strKing,
			SOLVER_KIND defaultKind /*= SOLVER_UNDEFINED_KIND*/);

	/**
	 * SOLVER
	 * Available
	 * List
	 */
	static bool isAvailableSolver(SOLVER_KIND king);

	static void toStreamSolverList(OutStream & os,
			const std::string & aHeader = "solvers");


};

} /* namespace sep */
#endif /* SOLVER_SOLVERDEF_H_ */

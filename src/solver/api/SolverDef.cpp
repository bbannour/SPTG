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

#include "SolverDef.h"

#include <util/avm_string.h>

#include <printer/OutStream.h>

#if defined( _AVM_SOLVER_CVC5_ )
#include <solver/CVC5Solver.h>
#endif /* _AVM_SOLVER_CVC5_ */

#if defined( _AVM_SOLVER_CVC4_ )
#include <solver/CVC4Solver.h>
#endif /* _AVM_SOLVER_CVC4_ */

#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
#include <solver/Z3Solver.h>
#endif /* _AVM_SOLVER_Z3_ */

#if defined( _AVM_SOLVER_YICES_V2_ )
#include <solver/Yices2Solver.h>
#endif /* _AVM_SOLVER_YICES_V2_ */

// Mandatory after other Solver for compilation FIX
#if defined( _AVM_SOLVER_OMEGA_ )
#include <solver/OmegaSolver.h>
#endif /* _AVM_SOLVER_OMEGA_ */


namespace sep
{


/**
 * ATTRIBUTES
 */
bool SolverDef::DEFAULT_SOLVER_USAGE_FLAG = false;

SolverDef::SOLVER_KIND SolverDef::DEFAULT_SOLVER_KIND =
		SolverDef::SOLVER_Z3_KIND;
//		SolverDef::SOLVER_CVC4_KIND;


/**
 * toString
 */
std::string SolverDef::strSatisfiability(SolverDef::SATISFIABILITY_RING ring)
{
	switch (ring)
	{
		case UNSATISFIABLE :  return( "unsatisfiable" );
		case SATISFIABLE   :  return( "satisfiable"   );
		case ABORT_SAT     :  return( "abort_sat"     );
		case UNKNOWN_SAT   :  return( "unknown_sat"   );
		default            :  return( "undefined_sat" );
	}
}

std::string SolverDef::strValidity(SolverDef::VALIDITY_RING ring)
{
	switch (ring)
	{
		case INVALID       :  return( "invalid"         );
		case VALID         :  return( "valid"           );
		case ABORT_VALID   :  return( "abort_valid"     );
		case UNKNOWN_VALID :  return( "unknown_valid"   );
		default            :  return( "undefined_valid" );
	}
}


std::string SolverDef::strSolver(SolverDef::SOLVER_KIND king)
{
	switch (king)
	{
#if defined( _AVM_SOLVER_OMEGA_ )
		case SOLVER_OMEGA_KIND      :  return( OmegaSolver::ID );
#endif /* _AVM_SOLVER_OMEGA_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
		case SOLVER_YICES_KIND      :  return( Yices2Solver::ID );
		case SOLVER_YICES2_KIND     :  return( Yices2Solver::ID );
#endif /* _AVM_SOLVER_YICES_V2_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
		case SOLVER_Z3_KIND         :  return( Z3Solver::ID  );
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_CVC5_ )
		case SOLVER_CVC_KIND        :  return( CVC5Solver::ID );
		case SOLVER_CVC5_KIND       :  return( CVC5Solver::ID );
		case SOLVER_CVC5_BV32_KIND  :  return( CVC5Solver::ID + "_BV32" );
#endif /* _AVM_SOLVER_CVC5_ */

#if defined( _AVM_SOLVER_CVC4_ )
//		case SOLVER_CVC_KIND        :  return( CVC4Solver::ID );
		case SOLVER_CVC4_KIND       :  return( CVC4Solver::ID );
		case SOLVER_CVC4_BV32_KIND  :  return( CVC4Solver::ID + "_BV32" );
#endif /* _AVM_SOLVER_CVC4_ */


		case SOLVER_UNDEFINED_KIND  :  return( "UNDEFINED_SOLVER" );

		default                     :  return( "UNKNOWN_SOLVER"   );
	}
}

/**
 * toSolver
 */
SolverDef::SOLVER_KIND SolverDef::toSolver(
		std::string strKing, SolverDef::SOLVER_KIND defaultKind)
{
	StringTools::toupper(strKing);

#if defined( _AVM_SOLVER_OMEGA_ )
	if( strKing == OmegaSolver::ID  )  return( SOLVER_OMEGA_KIND     );
#endif /* _AVM_SOLVER_OMEGA_ */


#if defined( _AVM_SOLVER_CVC5_ )
	if( strKing == "CVC"            )  return( SOLVER_CVC5_KIND      );
	if( strKing == "CVC_INT"        )  return( SOLVER_CVC5_KIND      );
	if( strKing == "CVC_BV32"       )  return( SOLVER_CVC5_BV32_KIND );
	if( strKing == CVC5Solver::ID   )  return( SOLVER_CVC5_KIND      );
	if( strKing == "CVC5_INT"       )  return( SOLVER_CVC5_KIND      );
	if( strKing == "CVC5_BV32"      )  return( SOLVER_CVC5_BV32_KIND );
#endif /* _AVM_SOLVER_CVC5_ */


#if defined( _AVM_SOLVER_CVC4_ )
	if( strKing == "CVC"            )  return( SOLVER_CVC4_KIND      );
	if( strKing == "CVC_INT"        )  return( SOLVER_CVC4_KIND      );
	if( strKing == "CVC_BV32"       )  return( SOLVER_CVC4_BV32_KIND );
	if( strKing == CVC4Solver::ID   )  return( SOLVER_CVC4_KIND      );
	if( strKing == "CVC4_INT"       )  return( SOLVER_CVC4_KIND      );
	if( strKing == "CVC4_BV32"      )  return( SOLVER_CVC4_BV32_KIND );
#endif /* _AVM_SOLVER_CVC4_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
	if( strKing == Yices2Solver::ID )  return( SOLVER_YICES2_KIND    );
#if not defined( _AVM_SOLVER_YICES_V1_ )
	if( strKing == "YICES"          )  return( SOLVER_YICES2_KIND    );
#endif /* not _AVM_SOLVER_YICES_V1_ */
#endif /* _AVM_SOLVER_YICES_V2_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
	if( strKing == Z3Solver::ID     )  return( SOLVER_Z3_KIND        );
#endif /* _AVM_SOLVER_Z3_ */

	return( defaultKind );
}


/**
 * SOLVER
 * Available
 * List
 */
bool SolverDef::isAvailableSolver(SOLVER_KIND king)
{
	switch (king)
	{
#if defined( _AVM_SOLVER_OMEGA_ )
		case SOLVER_OMEGA_KIND      :  return( true );
#endif /* _AVM_SOLVER_OMEGA_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
		case SOLVER_YICES_KIND      :  return( true );
		case SOLVER_YICES2_KIND     :  return( true );
#endif /* _AVM_SOLVER_YICES_V2_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
		case SOLVER_Z3_KIND         :  return( true  );
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_CVC5_ )
		case SOLVER_CVC_KIND        :  return( true );
		case SOLVER_CVC5_KIND       :  return( true );
		case SOLVER_CVC5_BV32_KIND  :  return( true );
#endif /* _AVM_SOLVER_CVC5_ */

#if defined( _AVM_SOLVER_CVC4_ )
//		case SOLVER_CVC_KIND        :  return( true );
		case SOLVER_CVC4_KIND       :  return( true );
		case SOLVER_CVC4_BV32_KIND  :  return( true );
#endif /* _AVM_SOLVER_CVC4_ */


		case SOLVER_UNDEFINED_KIND  :  return( false );

		default                     :  return( false );
	}
}


void SolverDef::toStreamSolverList(OutStream & os, const std::string & aHeader)
{
#define SOLVER_FACTORY_SHOW_DESCRIPTION( SolverClass )  \
	os << TAB2 << SolverClass::DESCRIPTION << EOL;

	os << TAB1 << aHeader << "< usable > {" << EOL;

#if defined( _AVM_SOLVER_OMEGA_ )
	SOLVER_FACTORY_SHOW_DESCRIPTION( OmegaSolver )
#endif /* _AVM_SOLVER_OMEGA_ */


#if defined( _AVM_SOLVER_CVC5_ )
	SOLVER_FACTORY_SHOW_DESCRIPTION( CVC5Solver )
#endif /* _AVM_SOLVER_CVC5_ */

#if defined( _AVM_SOLVER_CVC4_ )
	SOLVER_FACTORY_SHOW_DESCRIPTION( CVC4Solver )
#endif /* _AVM_SOLVER_CVC4_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
	SOLVER_FACTORY_SHOW_DESCRIPTION( Z3Solver )
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
	SOLVER_FACTORY_SHOW_DESCRIPTION( Yices2Solver )
#endif /* _AVM_SOLVER_YICES_V2_ */

	os << TAB1 << "}" << EOL_FLUSH;

}




} /* namespace sep */

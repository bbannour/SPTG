/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 sept. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TransitionMoc.h"

#include <fml/expression/AvmCode.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>

#include <printer/OutStream.h>


namespace sep
{


/**
 *******************************************************************************
 * MODEL OF COMPILATION
 *******************************************************************************
 *
prototype spec::system.statemachine.mos4transition "mos4transition" as &meta::xlia.moc.Transition is
section PRIORITY
	@user = |>|;

	@lca = |>|;
	@source = |>|;
	@target = |>|;
endsection PRIORITY
section MOE
	@run{
		${ |;|
			${ disable }
			${ run }
			${ enable }
		}
	}
endsection MOE
endprototype
*/


void TransitionMoc::setFlags(WObject * moc)
{
//!![MIGRATION]
//	WObject * thePRIORITY = Query::getRegexWSequence(moc,
//			OR_WID2("priority", "PRIORITY"));
//
//	if( thePRIORITY != WObject::_NULL_ )
//	{
//		WObject * aWProperty =
//				Query::getWProperty(thePRIORITY, "priority", WObject::_NULL_);
//		if( aWProperty == WObject::_NULL_ )
//		{
//			aWProperty = Query::getWProperty(
//					thePRIORITY, "user", WObject::_NULL_);
//		}
//
//		// DEFAULT
//		theUserPriorityEnabledFlag = false;
//		if( aWProperty != WObject::_NULL_  )
//		{
//			theUserPriorityEnabledFlag = true;
//
//			// DEFAULT
//			theUserPriorityMinFirstFlag = true;
//			if( aWProperty->getValue().is< Operator >() )
//			{
//				theUserPriorityMinFirstFlag = ( aWProperty->getOperatorValue() ==
//						OperatorManager::OPERATOR_PRIOR_LT );
//			}
//		}
//
//
//		aWProperty = Query::getWProperty(thePRIORITY, "lca", NULL);
//
//		// DEFAULT
//		theLcaEnabledFlag = false;
//		if( aWProperty != NULL )
//		{
//			theLcaEnabledFlag = true;
//
//			// DEFAULT
//			theLcaMinFirstFlag = true;
//			if( aWProperty->getValue().is< Operator >() )
//			{
//				theLcaMinFirstFlag = ( aWProperty->getOperatorValue() ==
//						OperatorManager::OPERATOR_PRIOR_LT );
//			}
//		}
//
//
//		aWProperty = Query::getWProperty( thePRIORITY, "source", NULL);
//
//		// DEFAULT
//		theSourceEnabledFlag = false;
//		if( aWProperty != NULL )
//		{
//			theSourceEnabledFlag = true;
//
//			// DEFAULT
//			theSourceMinFirstFlag = true;
//			if( aWProperty->getValue().is< Operator >() )
//			{
//				theSourceMinFirstFlag = ( aWProperty->getOperatorValue() ==
//						OperatorManager::OPERATOR_PRIOR_LT );
//			}
//		}
//
//
//		aWProperty = Query::getWProperty(thePRIORITY, "target", NULL);
//
//		// DEFAULT
//		theTargetEnabledFlag = false;
//		if( aWProperty != NULL )
//		{
//			theTargetEnabledFlag = true;
//
//			// DEFAULT
//			theTargetMinFirstFlag = true;
//			if( aWProperty->getValue().is< Operator >() )
//			{
//				theTargetMinFirstFlag = ( aWProperty->getOperatorValue() ==
//						OperatorManager::OPERATOR_PRIOR_LT );
//			}
//		}
//
//
//		WObject * theMOE = Query::getRegexWSequence(moc, OR_WID2("moe", "MOE"));
//
//		if( theMOE != WObject::_NULL_ )
//		{
//			// DEFAULT
//			theMoeRun = MOE_DRE_RUN;
//
//			const BFCode & moeRun = Query::getWPropertyAvmCode(theMOE, "run");
//			if( moeRun.valid() && (moeRun->size() == 3) )
//			{
//				if( (moeRun->first().is< Operator >() && moeRun->first().
//						to_ptr< Operator >()->isOpCode( AVM_OPCODE_RUN )) ||
//					(moeRun->first().is< AvmCode >() && moeRun->first().
//							to_ptr< AvmCode >()->isOpCode( AVM_OPCODE_RUN )) )
//				{
//					theMoeRun = MOE_RDE_RUN;
//				}
//				if( (moeRun->second().is< Operator >() && moeRun->second().
//						to_ptr< Operator >()->isOpCode( AVM_OPCODE_RUN )) ||
//					(moeRun->second().is< AvmCode >() && moeRun->second().
//							to_ptr< AvmCode >()->isOpCode( AVM_OPCODE_RUN )) )
//				{
//					theMoeRun = MOE_DRE_RUN;
//				}
//				if( (moeRun->third().is< Operator >() && moeRun->third().
//						to_ptr< Operator >()->isOpCode( AVM_OPCODE_RUN )) ||
//					(moeRun->third().is< AvmCode >() && moeRun->third().
//							to_ptr< AvmCode >()->isOpCode( AVM_OPCODE_RUN )) )
//				{
//					theMoeRun = MOE_DER_RUN;
//				}
//			}
//		}
//		else
//		{
//			theMoeRun = MOE_UNDEFINED_RUN;
//		}
//	}
}

/**
 * Serialization
 */
void TransitionMoc::toStream(OutStream & out) const
{
	out << TAB << "transition {" << EOL;

	if( theUserPriorityEnabledFlag || theLcaEnabledFlag
		|| theSourceEnabledFlag    || theTargetEnabledFlag )
	{
		out << TAB2 << "priority:" << EOL;
	}

	// User specific priority number
	if( theUserPriorityEnabledFlag )
	{
		out << TAB3 << "user = "
			<< ((theUserPriorityMinFirstFlag)? "|<|" : "|>|") << ";" << EOL;
	}

	// Implicit formalism priority
	if( theLcaEnabledFlag )
	{
		out << TAB3 << "lca = "
			<< ((theLcaMinFirstFlag)? "|<|" : "|>|") << ";" << EOL;
	}
	if( theSourceEnabledFlag )
	{
		out << TAB3 << "source = "
			<< ((theSourceMinFirstFlag)? "|<|" : "|>|") << ";" << EOL;
	}
	if( theTargetEnabledFlag )
	{
		out << TAB3 << "target = "
			<< ((theTargetMinFirstFlag)? "|<|" : "|>|") << ";" << EOL;
	}

	if( theMoeRun != MOE_UNDEFINED_RUN )
	{
		out << TAB2 << "moe:" << EOL
			<< TAB3 << "@run { " << EOL;

		switch( theMoeRun )
		{
			case MOE_RDE_RUN:
			{
				out << "${ run } ${ disable } ${ enable }";
				break;
			}

			case MOE_DRE_RUN:
			{
				out << "${ disable } ${ run } ${ enable }";
				break;
			}

			case MOE_DER_RUN:
			{
				out << "${ disable } ${ enable } ${ run }";
				break;
			}

			case MOE_UNDEFINED_RUN:
			default:
			{
				//!!! NOTHING
				break;
			}
		}

		out << " }" << EOL;

	}

	out << TAB << "}" << EOL_FLUSH;
}





} /* namespace sep */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BaseHitProcessor.h"

#include <builder/Builder.h>

#include <computer/EvaluationEnvironment.h>

#include <fam/hitorjump/AvmHitOrJumpProcessor.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/expression/AvmCode.h>

#include <fml/type/TypeSpecifier.h>

#include <fml/trace/TraceFactory.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>

#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
BaseHitProcessor::BaseHitProcessor(AvmHitOrJumpProcessor & hojProcessor,
		EvaluationEnvironment & anENV, Operator * op)
: mHitOrJumpProcessor( hojProcessor ),
mCoverageStatistics( hojProcessor.getCoverageStatistics() ),
ENV( anENV ),

mSolverKind(  SolverDef::SOLVER_UNDEFINED_KIND  ),
mLocalExecutableForm(
		mHitOrJumpProcessor.getConfiguration().getExecutableSystem(), 0 ),
mTraceChecker( anENV, &mLocalExecutableForm ),

mTraceObjective( op ),
isPureStateTransitionNatureFlag( false ),

// Computing Local Variables
traceOffset( 0 ),

mRelativeRootEC( hojProcessor.mRelativeRootEC ),
ecIt( ),
ecItEnd( ),
mRelativeLeafEC( hojProcessor.mRelativeLeafEC ),

mAbsoluteLeafEC( hojProcessor.mAbsoluteLeafEC ),

mBlackHoleEC( hojProcessor.mBlackHoleEC ),

mBacktrackHitEC( hojProcessor.mBacktrackHitEC ),
mBacktrackFlag( hojProcessor.mBacktrackFlag ),

mJumpHeight( 0 ),

mMaxHitEC( ),

hitOffset( 0 ),
hitOffsetEnd( 0 ),

mHitCount( 0 ),

ecChildIt( ),
ecChildItEnd( )
{
	//!! NOTHING
}


/**
 * GETTER
 * mTraceObjective
 */
bool BaseHitProcessor::isPureStateTransitionObjective() const
{
	for( avm_size_t offset = 0 ; offset < mTraceObjective.size() ; ++offset )
	{
		if( mTraceChecker.isPointNature(mTraceObjective[offset],
				ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE) )
		{
			//!! CONTINUE
		}
		else if( mTraceChecker.isPointNature(mTraceObjective[offset],
				ENUM_TRACE_POINT::TRACE_STATE_NATURE) )
		{
			//!! CONTINUE
		}
		else if( mTraceChecker.isPointNature(mTraceObjective[offset],
				ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE) )
		{
			//!! CONTINUE
		}
		else
		{
			return( false );
		}
	}

	return( true );
}


/*
prototype process::hit_or_jump as &avm::processor.HIT_OR_JUMP is
 section REPORT
  ...
 endsection REPORT

 section PROPERTY
  ...
 endsection PROPERTY

 // Declaration part
 section POINT
  @assign = "sens";

  @newfresh = "sens";

  @signal#sens = "sens";

  @port = "env";

  @input = "env";
  @output = "env";

  @output = "Thermostat->dt";
  @input  = "Thermostat->equip";
  @output2 = "Equipment->error";
 endsection POINT

 section TRACE
  @trace = ${ && "signal#sens" "output2" };
  @trace = [ "signal#sens" , "output2" ];
  @point = ( "signal#sens" || "output2" );
  @composite = ${ xor "signal#sens" "output2" };

  @assign = "sens";

  @newfresh = "sens";

  @signal = "sens";

  @port = "env";

  @input = "env";
  @output = "env";

  @output = "Thermostat->dt";
  @input  = "Thermostat->equip";
  @output = "Equipment->error";
 endsection TRACE
endprototype
*/


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool BaseHitProcessor::configure(WObject * wfParameterObject)
{
	const ExecutableSystem & anExecutableSystem =
			mHitOrJumpProcessor.getConfiguration().getExecutableSystem();

	mCoverageStatistics.resetCounter();


	WObject * thePROPERTY = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("property", "PROPERTY"));
	if( thePROPERTY != WObject::_NULL_ )
	{
		std::string mSolverName =
				Query::getWPropertyString(thePROPERTY, "solver", "");
		if( mSolverName.empty() )
		{
AVM_IF_DEBUG_FLAG( SOLVING )
	thePROPERTY->warningLocation(AVM_OS_WARN)
			<< "Unexpected an empty solver engine kind!!!!!" << std::endl;
AVM_ENDIF_DEBUG_FLAG( SOLVING )
		}
		mSolverKind = SolverDef::toSolver(
				mSolverName, SolverDef::DEFAULT_SOLVER_KIND);
	}
	else
	{
		mSolverKind = SolverDef::SOLVER_CVC4_KIND;
	}

	mTraceChecker.setSolverKind( mSolverKind );


	WObject * theDATA = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("data", "DATA"));
	if( theDATA != WObject::_NULL_ )
	{
		anExecutableSystem.initProcessExecutableForm(
				mLocalExecutableForm, theDATA->ownedSize());

		List< WObject * > listOfLocalVar;
		Query::getListWObject(theDATA, listOfLocalVar);

		TypeSpecifier aTypeSpecifier;

		List< WObject * >::iterator it = listOfLocalVar.begin();
		List< WObject * >::iterator itEnd = listOfLocalVar.end();
		for( avm_offset_t offset = 0 ; it != itEnd ; ++it , ++offset )
		{
			aTypeSpecifier = ENV.getBuilder().getCompiler().
					compileTypeSpecifier(&mLocalExecutableForm,
							(*it)->getQualifiedTypeNameID() );

			BF anInstance( new InstanceOfData(
					IPointerDataNature::POINTER_STANDARD_NATURE,
					&mLocalExecutableForm, NULL, aTypeSpecifier,
					(*it)->getFullyQualifiedNameID(), offset) );

			mLocalExecutableForm.setData( offset , anInstance );
		}
	}
	else
	{
		anExecutableSystem.initProcessExecutableForm(
				mLocalExecutableForm, 0);
	}


	WObject * theTRACE = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("trace", "TRACE"));
	if( (theTRACE == WObject::_NULL_) || theTRACE->hasnoOwnedElement() )
	{
		return true;
	}

	// Configuration of TRACE
	TraceFactory traceFactory(mHitOrJumpProcessor.getConfiguration(),
			ENV, wfParameterObject, &mLocalExecutableForm);

	if( traceFactory.configure(& mTraceObjective) )
	{
//		return( false );
	}

AVM_IF_DEBUG_LEVEL_FLAG( LOW , CONFIGURING )
	AVM_OS_LOG << "The parsed trace :> " << std::endl;
	mTraceObjective.toStream( AVM_OS_LOG << AVM_TAB1_INDENT );

	mLocalExecutableForm.toStream( AVM_OS_LOG);

	AVM_OS_LOG << END_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , CONFIGURING )


	mCoverageStatistics.mNumberOfElements = mTraceObjective.size();

	mCoverageStatistics.mCoverageBitset.resize(
			mCoverageStatistics.mNumberOfElements, false);


	isPureStateTransitionNatureFlag = isPureStateTransitionObjective();

	return( mCoverageStatistics.mNumberOfElements > 0 );
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool BaseHitProcessor::resetConfig()
{
	mCoverageStatistics.resetCoverageCounter();

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// FILTERING TOOLS
////////////////////////////////////////////////////////////////////////////////

bool BaseHitProcessor::isAbsoluteLeaf(ExecutionContext * anEC)
{
	if( (not anEC->hasNext()) && ((anEC->getHeight() < mJumpHeight) ||
			(not mRelativeLeafEC.contains(anEC)) ) )
	{
		//!! DeadLock or Absolute Stop ?
		mAbsoluteLeafEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << "<<<<< HoJ< DeadLock or Absolute Stop > >>>>> EC< id:"
			<< anEC->getIdNumber() << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		return( true );
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void BaseHitProcessor::toStreamCovered(OutStream & os) const
{
	os << TAB << "hit<covered> { " << mHitOrJumpProcessor.strScheduler();
	if( mCoverageStatistics.mCoverageBitset.anyTrue() )
	{
		os << EOL_INCR_INDENT;
		for( avm_size_t traceOffset = 0 ;
				traceOffset != mCoverageStatistics.mNumberOfElements ;
				++traceOffset )
		{
			if( mCoverageStatistics.mCoverageBitset.test(traceOffset) )
			{
				mTraceObjective[traceOffset].toStream(os);
			}
		}
		os << DECR_INDENT_TAB ;
	}
	else
	{
		os << " ";
	}
	os << "}" << EOL;
}


void BaseHitProcessor::toStreamUncovered(OutStream & os) const
{
	os << TAB << "hit<uncovered> { " << mHitOrJumpProcessor.strScheduler();
	if( mCoverageStatistics.mCoverageBitset.anyFalse() )
	{
		os << EOL_INCR_INDENT;
		avm_size_t offset = 0;
		for( ; offset != mCoverageStatistics.mNumberOfElements ; ++offset )
		{
			if( not mCoverageStatistics.mCoverageBitset.test(offset) )
			{
				mTraceObjective[offset].toStream(os);
			}
		}
		os << DECR_INDENT_TAB ;
	}
	else
	{
		os << " ";
	}
	os << "}" << EOL;
}



} /* namespace sep */

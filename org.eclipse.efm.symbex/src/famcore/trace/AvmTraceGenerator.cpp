/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmTraceGenerator.h"

#include "BasicTraceBuilder.h"
#include "BasicTraceFormatter.h"
#include "SequenceDiagramTraceBuilder.h"
#include "SequenceDiagramTraceFormatter.h"
#include "TTCNTraceFormatter.h"
#include "TTCNTitanTraceFormatter.h"

#include <collection/Typedef.h>

#include <computer/PathConditionProcessor.h>

#include  <famcore/api/MainProcessorUnit.h>

#include <fml/template/TimedMachine.h>

#include <fml/executable/ExecutableSystem.h>

#include <fml/runtime/ExecutionContext.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>
#include <sew/SymbexControllerUnitManager.h>

#include  <famcore/queue/ExecutionQueue.h>

namespace sep
{


/*
prototype process::trace_generator as &avm::processor.TRACE_GENERATOR is
 section REPORT
  @uri = std      ":" ( "cout" | "cerr"  )
       | avm      ":" ( "log"  | "trace" )
       | folder   ":" path
       | file     ":" path
       | filename ":" path
       | socket   ":" host ":" port
       ;
  @uri = ...;

  @when = [ init ][:][ otf | (every | after | before)?value#unit][:][ exit ] ;

endsection REPORT

 section PROPERTY
  // 'OMEGA' | 'CVC4' | 'Z3' | 'YICES'
  @solver = 'CVC4';

  // 'BASIC' | 'BASIC#XLIA' | 'BASIC#SDL'
  // 'TTCN'  | 'TTCN#XLIA'  | 'TTCN#SDL'
  @format = 'BASIC';

  // Remove redundant <<numeric>> Trace !
  // true | false
  @normalize = true;

  @numerizer = 'SOLVER';  // SOLVER | NONE | NEWFRESH

  // true | false
  @print_initialization_values = false;

  print#lifelines = true

  @data#selection = 'ALL';	// ALL | MODIFIED
 endsection PROPERTY

 section TRACE
  // AND --> conjunctive
  // OR  --> disjunctive
  // XOR --> exclusive
  // NOT --> negative
  @combinator = 'OR';

  @path#condition = "[*]";
  @path#timed#condition = "[*]";

  @time = "$delta";
  @time = "$time";

  @assign = "sens";

  @newfresh = "sens";

  @com    = "env";

  @signal = "sens";
  @port   = "env";

  @input  = "env";
  @output = "env";

  @output = "Thermostat->dt";
  @input  = "Thermostat->equip";
  @output = "Equipment->error";

  @transition = "t8";
  @machine = "m1";
  @procedure = "[*]";
 endsection TRACE

 section FORMAT
  @line#wrap#width = 80;
  @line#wrap#separator = "\n\t";

  @value#struct#begin = "{ ";
  @value#struct#separator = " , ";
  @value#struct#end = " }";

  @value#array#begin = "[ ";
  @value#array#separator = " , ";
  @value#array#end = " ]";

  // %1% --> trace number
  // %2% --> execution context leaf identifier
  @header = "TRACE NUMBER %1%\n";
  @end    = "\n";

  // %1% --> string message
  // %2% --> execution context identifier
  @comment   = "//%1%";
  @separator = "%1%"  ;
  @newline   = "\n%1%";

  // %1% --> step identifier
  // %2% --> execution context identifier
  @step#begin = "#step#begin %1%\n";
  @step#end   = "#step#end %1%\n";

  // %1% --> condition
  // %2% --> execution context identifier
  @path#condition = "PC: %1%";
  @path#timed#condition = "PtC: %1%";
  @node#condition = "NC: %1%";
  @node#timed#condition = "NtC: %1%";

  // %1% --> machine runtime pid
  // %2% --> machine container identifier
  // %3% --> port | signal | variable | machine | transition | routine
  // %4% --> value

  @time   = "\t%4%\n";

  @assign = "\t%2%:%3% = %4%\n";

  @newfresh = "\tnewfresh %2%->%3%( %4% )\n";

  @transition = "\nfired  %3%->%3%";

  @machine    = "\nrun  %3%";

  @procedure  = "\ncall  %3%";

  @input  = "\tinput  %2%->%3%%4%\n";
  @output = "\toutput %2%->%3%%4%\n";
 endsection FORMAT
endprototype
*/


/**
 * DESTRUCTOR
 */
AvmTraceGenerator::~AvmTraceGenerator()
{
	delete( mTraceBuilder );

	delete( mTraceFormatter );
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool AvmTraceGenerator::configureImpl()
{
	const WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));

	if( thePROPERTY == WObject::_NULL_ )
	{
		mConfigFlag = false;
	}

	std::string solver = Query::getWPropertyString(thePROPERTY, "solver", "");

	mSolverKind = SolverDef::toSolver(solver, SolverDef::DEFAULT_SOLVER_KIND);

	mNormalizedFlag = Query::getWPropertyBoolean(thePROPERTY, "normalize", false);


	// the Trace Formatter configuration
	mTraceTypeID = Query::getWPropertyString(
			thePROPERTY, "format", "BASIC#XLIA");

	// the Trace Point Numerizer configuration
	mConfigFlag = mTraceNumerizer.configure(getParameterWObject())
			&& mConfigFlag;

	// the Trace Point Filter configuration
	mConfigFlag = mTracePointFilter.configure(ENV, getParameterWObject())
			&& mConfigFlag;

	if ( StringTools::startsWith(mTraceTypeID,"SEQUENCE_DIAGRAM") )
	{
		// the Sequence Diagram Trace Builder configuration
		mTraceBuilder = new SequenceDiagramTraceBuilder(*this,
				mSolverKind, mTracePointFilter);
	}
	else
	{
		// the Default Trace Builder configuration
		mTraceBuilder = new BasicTraceBuilder(*this,
				mSolverKind, mTracePointFilter);
	}


	mConfigFlag = (mTraceBuilder != nullptr) &&
				mTraceBuilder->configure(getParameterWObject())
			&& mConfigFlag;

	if( StringTools::startsWith(mTraceTypeID, "TTCN") )
	{
//		if( StringTools::startsWith(mTraceTypeID, "TTCN#TITAN") )
		if( mTraceTypeID.find("TITAN") != std::string::npos )
		{
			mTraceFormatter = new TTCNTitanTraceFormatter( *this );
		}
		else
		{
			mTraceFormatter = new TTCNTraceFormatter( *this );
		}
	}
	else if( StringTools::startsWith(mTraceTypeID,"BASIC") )
	{
		mTraceFormatter = new BasicTraceFormatter( *this );
	}
	else if( StringTools::startsWith(mTraceTypeID,"SEQUENCE_DIAGRAM") )
	{
		mTraceFormatter = new SequenceDiagramTraceFormatter( *this );
	}

	mConfigFlag = (mTraceFormatter != nullptr)
			&& mTraceFormatter->configure(getParameterWObject())
			&& mConfigFlag;

	if( mConfigFlag && mTracePointFilter.hasNodeConditionTracePoint() )
	{
		getConfiguration().setNodeConditionComputationEnabled( true );
	}

	return mConfigFlag;
}


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void AvmTraceGenerator::reportDefault(OutStream & out) const
{
	out << TAB << mTraceTypeID << " TRACE GENERATOR" << EOL;

	if( mTraceManager.nonempty() )
	{
		out << TAB2 << "The TRACE count : " << mTraceBuilder->getPathCount()
			<< EOL;

		if( mTraceBuilder->getPathCountLimit() ==
				AbstractTraceBuilder::DEFAULT_TRACE_COUNT_LIMIT )
		{
			out << TAB2 << "Warning : The default trace count limit is reached !" << EOL
				<< "You could fix it with the parameter attribute " << EOL
				<< "< trace#count = -1 > to serialize all computed traces !" << EOL;
		}
		else if( mTraceBuilder->getPathCountLimit() <
				getControllerUnitManager().getMainProcessor().getMaxReachWidth() )
		{
			out << TAB2 << "Warning : The user trace count limit "
				<< "is less than the computed trace count: !" << EOL;
		}


		out << TAB2 << "DONE !" << EOL_FLUSH;
	}
	else
	{
		out << TAB2 << "NO TRACE!" << EOL_FLUSH;
	}
}


////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void AvmTraceGenerator::tddRegressionReportImpl(OutStream & out) const
{
	out << TAB << "NB TRACES : " << mTraceManager.size() << std::endl;
}


////////////////////////////////////////////////////////////////////////////////
// PROCESS API
////////////////////////////////////////////////////////////////////////////////

bool AvmTraceGenerator::postprocess()
{
	mTraceBuilder->build( mTraceManager, getConfiguration().getExecutionTrace());

	// Numerize all TraceSequence
	mTraceNumerizer.numerize( mTraceManager );

	// Normalize a Trace
	if( mNormalizedFlag )
	{
		mTraceManager.normalize();

		mTraceManager.resetTraceID();
	}

	// Format all TraceSequence
	mTraceFormatter->format(mTraceManager);

	return( true );
}


////////////////////////////////////////////////////////////////////////////
// FACTORY API used by PYTHON BINDINGS
////////////////////////////////////////////////////////////////////////////

bool AvmTraceGenerator::configureDefaultImpl(const std::string & traceTypeID,
		bool showAssign, bool showTransition, bool enabledNumerization)
{
	mConfigFlag = true;

	mTraceTypeID = traceTypeID;

	mSolverKind = SolverDef::DEFAULT_SOLVER_KIND;

	mNormalizedFlag = true;

	// the Trace Formatter configuration
//	mTraceTypeID = "SEQUENCE_DIAGRAM";

	// the Trace Point Numerizer configuration
	mConfigFlag = mTraceNumerizer.configure(getParameterWObject())
			&& mConfigFlag;
	mTraceNumerizer.setSolverKing( mSolverKind );

	if( enabledNumerization )
	{
		mTraceNumerizer.setNumerizer(AVM_OPCODE_CHECK_SAT);
	}
	else
	{
		mTraceNumerizer.setNumerizer(AVM_OPCODE_NOP);
	}

	// the Trace Point Filter configuration
//	mConfigFlag = mTracePointFilter.configure(ENV, getParameterWObject())
//			&& mConfigFlag;
	if( true )
	{
		mTracePointFilter.addAnyComFilter();
	}
	if( showAssign )
	{
		mTracePointFilter.addAnyAssignFilter();
	}
	if( showTransition )
	{
		mTracePointFilter.addAnyTransitionFilter();
	}


	mTracePointFilter.setTracePointID(0);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

	AVM_OS_TRACE << "AvmTraceGenerator->TraceFilter:> ";
	mTracePointFilter.toStream(AVM_OS_TRACE);

AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

	if ( StringTools::startsWith(mTraceTypeID,"SEQUENCE_DIAGRAM") )
	{
		// the Sequence Diagram Trace Builder configuration
		mTraceBuilder = new SequenceDiagramTraceBuilder(*this, mSolverKind, mTracePointFilter);
	}
	else
	{
		// the Default Trace Builder configuration
		mTraceBuilder = new BasicTraceBuilder(*this, mSolverKind, mTracePointFilter);
	}


	mConfigFlag = (mTraceBuilder != nullptr) &&
				mTraceBuilder->configure(getParameterWObject())
			&& mConfigFlag;

	if( StringTools::startsWith(mTraceTypeID, "TTCN") )
	{
//		if( StringTools::startsWith(mTraceTypeID, "TTCN#TITAN") )
		if( mTraceTypeID.find("TITAN") != std::string::npos )
		{
			mTraceFormatter = new TTCNTitanTraceFormatter( *this );
		}
		else
		{
			mTraceFormatter = new TTCNTraceFormatter( *this );
		}
	}
	else if( StringTools::startsWith(mTraceTypeID,"BASIC") )
	{
		mTraceFormatter = new BasicTraceFormatter( *this );
	}
	else if( StringTools::startsWith(mTraceTypeID,"SEQUENCE_DIAGRAM") )
	{
		mTraceFormatter = new SequenceDiagramTraceFormatter( *this );
	}

	mConfigFlag = (mTraceFormatter != nullptr)
			&& mTraceFormatter->configure(getParameterWObject())
			&& mConfigFlag;

	if( mConfigFlag && mTracePointFilter.hasNodeConditionTracePoint() )
	{
		getConfiguration().setNodeConditionComputationEnabled( true );

	}

	return mConfigFlag;
}


void AvmTraceGenerator::generate(
		OutStream & out, const ListOfExecutionContext & rootECs)
{
	mTraceBuilder->build( mTraceManager, rootECs);

	// Numerize all TraceSequence
	mTraceNumerizer.numerize( mTraceManager );

	// Normalize a Trace
	if( mNormalizedFlag )
	{
		mTraceManager.normalize();

		mTraceManager.resetTraceID();
	}

	// Format all TraceSequence
	mTraceFormatter->formatOneFile(out, mTraceManager);
}


void AvmTraceGenerator::generate(
		SymbexControllerUnitManager & aManager,
		OutStream & out, const std::string & traceTypeID,
		const ListOfExecutionContext & rootECs,
		bool showAssign, bool showTransition, bool enabledNumerization)
{
	AvmTraceGenerator traceGenerator(aManager, WObject::_NULL_);

	if( traceGenerator.configureDefaultImpl(
			traceTypeID, showAssign, showTransition, enabledNumerization) )
	{
		traceGenerator.generate(out, rootECs);
	}
	else
	{
		out << "DEBUG AvmTraceGenerator::generate( " << traceTypeID
			<< " ) Configure FAILED" << std::endl;
	}
}



} /* namespace sep */

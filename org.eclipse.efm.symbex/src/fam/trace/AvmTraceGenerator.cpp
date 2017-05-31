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
#include "TTCNTraceFormatter.h"
#include "TTCNTitanTraceFormatter.h"

#include <collection/Typedef.h>

#include <fml/template/TimedMachine.h>

#include <fml/executable/ExecutableSystem.h>

#include <fml/runtime/ExecutionContext.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>

#include <fam/queue/ExecutionQueue.h>

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
	WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));

	if( thePROPERTY == WObject::_NULL_ )
	{
		mConfigFlag = false;
	}

	std::string solver = Query::getWPropertyString(thePROPERTY, "solver", "");

	mSolverKind = SolverDef::toSolver(solver, SolverDef::DEFAULT_SOLVER_KIND);

	mNormalizedFlag = Query::getWPropertyBoolean(thePROPERTY, "normalize", false);


	// the Trace Point Numerizer configuration
	mConfigFlag = mTraceNumerizer.configure(getParameterWObject())
			&& mConfigFlag;

	// the Trace Point Filter configuration
	mConfigFlag = mTracePointFilter.configure(ENV, getParameterWObject())
			&& mConfigFlag;

	// the Trace Builder configuration
	mTraceBuilder = new BasicTraceBuilder(*this, mSolverKind, mTracePointFilter);

	mConfigFlag = (mTraceBuilder != NULL) &&
				mTraceBuilder->configure(getParameterWObject())
			&& mConfigFlag;


	// the Trace Formatter configuration
	mTraceTypeID = Query::getWPropertyString(
			thePROPERTY, "format", "BASIC#XLIA");
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
	else //if( StringTools::startsWith(format,"BASIC") )
	{
		mTraceFormatter = new BasicTraceFormatter( *this );
	}

	mConfigFlag = (mTraceFormatter != NULL)
			&& mTraceFormatter->configure(getParameterWObject())
			&& mConfigFlag;

	return mConfigFlag;
}


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void AvmTraceGenerator::reportDefault(OutStream & os) const
{
	os << TAB << mTraceTypeID << " TRACE GENERATOR" << EOL;

	if( mTraceManager.nonempty() )
	{
		os << TAB2 << "The TRACE count : " << mTraceManager.size() << EOL;
		os << TAB2 << "DONE !" << EOL_FLUSH;
	}
	else
	{
		os << TAB2 << "NO TRACE!" << EOL_FLUSH;
	}
}


////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void AvmTraceGenerator::tddRegressionReportImpl(OutStream & os)
{
	os << TAB << "NB TRACES : " << mTraceManager.size() << std::endl;

	os << std::flush;
}


////////////////////////////////////////////////////////////////////////////////
// PROCESS API
////////////////////////////////////////////////////////////////////////////////

bool AvmTraceGenerator::postprocess()
{
	ExecutionContext * rootEC = getConfiguration().getFirstTrace();
	if( rootEC->isRoot() && rootEC->isLeafNode() )
	{
		return( true );
	}

	// Build Trace
	mTraceBuilder->build( mTraceManager );

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


} /* namespace sep */

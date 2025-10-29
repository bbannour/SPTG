/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2014
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SEQUENCEDIAGRAMTRACEBUILDER_H_
#define SEQUENCEDIAGRAMTRACEBUILDER_H_

#include "BasicTraceBuilder.h"

#include <collection/List.h>
#include <collection/Typedef.h>

#include <fml/lib/ITracePoint.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/Message.h>

#include <solver/api/SolverDef.h>

#include <map>


namespace sep
{

class AvmTraceGenerator;
class EvaluationEnvironment;
class ExecutableSystem;
class ExecutionData;

class TraceFilter;
class TraceManager;
class TracePoint;
class TraceSequence;


class SequenceDiagramTraceBuilder  :  public BasicTraceBuilder
{

protected:
	/**
	 * ATTRIBUTES
	 */
	std::map< Message::pointer_t , List< RuntimeID > > mMapMessageReceiver;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SequenceDiagramTraceBuilder(AvmTraceGenerator & aProcessor,
			SolverDef::SOLVER_KIND aSolverKind,
			TraceFilter & aTracePointFilter);

	/**
	 * DESTRUCTOR
	 */
	virtual ~SequenceDiagramTraceBuilder()
	{
		//!! NOTHING
	}



	/*
	 *
	 */
	const std::map< Message::pointer_t , List< RuntimeID > > & getMapMessageReceiver() const
	{
		return( mMapMessageReceiver );
	}

	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl(const WObject * wfParameterObject) override;


	////////////////////////////////////////////////////////////////////////////
	// CONSTRUCTION API
	////////////////////////////////////////////////////////////////////////////

//	virtual void build(TraceManager & aTraceManager) override;

	virtual void buildTrace() override;

	virtual void buildTraceVariable(
			const ExecutionContext & anEC, bool isnotRoot = true) override;

	void analyse( const TraceSequence & aTraceElt );

	void analyse( const TracePoint & aTracePoint );


	////////////////////////////////////////////////////////////////////////////
	// REDUCING API
	////////////////////////////////////////////////////////////////////////////

	void reduce( TraceSequence & aTraceSequence );

};


} /* namespace sep */

#endif /* SEQUENCEDIAGRAMTRACEBUILDER_H_ */

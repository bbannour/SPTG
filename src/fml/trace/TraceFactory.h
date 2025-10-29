/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 sept. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TRACEFACTORY_H_
#define TRACEFACTORY_H_

#include <collection/BFContainer.h>
#include <collection/Typedef.h>

#include <fml/trace/TracePoint.h>


namespace sep
{


class AvmCode;

class BuiltinArray;

class Configuration;

class EvaluationEnvironment;
class ExecutionData;

class InstanceOfData;
class TraceSequence;

class WObject;


class TraceFactory final
{

protected:
	/**
	 * ATTRIBUTE
	 */
	const Configuration & mConfiguration;

	EvaluationEnvironment & ENV;

	const ExecutionData * mED;

	const WObject * mParameterWObject;

	BFVector         mDeclaredPoint;
	VectorOfString   mDeclaredPointID;

	ExecutableForm & mLocalExecutableForm;

	const InstanceOfData * mVarTime;
	BF                     bfVarTime;

	ListOfTracePoint listOfBufferTracePoint;
	ListOfTracePoint listOfPortTracePoint;
	ListOfTracePoint listOfVariableTracePoint;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	BF  bfTP;
	TracePoint * aTracePoint;
	ListOfTracePoint otherTracePoint;

public:
	std::size_t TP_ID;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TraceFactory(const Configuration & aConfiguration,
			EvaluationEnvironment & anENV, const WObject * wfParameterObject,
			ExecutableForm & aLocalExecutable, InstanceOfData * aVarTime = nullptr)
	: mConfiguration( aConfiguration ),
	ENV( anENV ),

	mED( nullptr ),

	mParameterWObject( wfParameterObject ),

	mDeclaredPoint( ),
	mDeclaredPointID( ),

	mLocalExecutableForm( aLocalExecutable ),

	mVarTime( aVarTime ),
	bfVarTime( ),

	listOfBufferTracePoint( ),
	listOfPortTracePoint( ),
	listOfVariableTracePoint( ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	bfTP( ),
	aTracePoint( nullptr ),
	otherTracePoint( ),
	TP_ID( 0 )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TraceFactory()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * listOfBufferTracePoint
	 * listOfPortTracePoint
	 * listOfVariableTracePoint
	 */
	inline const ListOfTracePoint & getBufferTracePoints() const
	{
		return( listOfBufferTracePoint );
	}

	inline const ListOfTracePoint & getPortTracePoints() const
	{
		return( listOfPortTracePoint );
	}

	inline const ListOfTracePoint & getVariableTracePoints() const
	{
		return( listOfVariableTracePoint );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configure(TraceSequence & aTraceElement, const ExecutionData * anED = nullptr);

	bool configure(AvmCode & aTraceExpression, const ExecutionData * anED = nullptr);

	bool collectIO(AvmCode & aTraceExpression, AvmCode & aTraceIO);

	bool configure(const WObject * aTraceSequence,
			BFCollection & tracePoints, const ExecutionData * anED = nullptr);

	bool configure(const WObject * aTraceSequence,
			TraceSequence & aTraceElement, const ExecutionData * anED = nullptr);

	bool configure(const WObject * aTraceSequence,
			AvmCode * aTraceExpression, const ExecutionData * anED = nullptr);

	bool configure(BFCollection & tracePoints, const WObject * wfProperty);

	bool configure(BFCollection & tracePoints, const WObject * wfProperty,
			ENUM_TRACE_POINT::TRACE_NATURE nature, const std::string & object);

	bool configure(BFCollection & tracePoints, const WObject * wfProperty,
			AVM_OPCODE opNature, const std::string & object);

	bool configureArray(BFCollection & tracePoints,
			const WObject * wfProperty, BuiltinArray * anArray,
			ENUM_TRACE_POINT::TRACE_NATURE nature, AVM_OPCODE opNature);

	bool configureExpression(BFCollection & tracePoints,
			const WObject * wfProperty, const AvmCode & aCode,
			ENUM_TRACE_POINT::TRACE_NATURE nature, AVM_OPCODE opNature);


	bool configureComposite(
			BFCollection & tracePoints, const std::string & object);


	bool configurePort(
			BFCollection & tracePoints, const std::string & object);

	bool configureTime(
			BFCollection & tracePoints, const std::string & object);

	bool configureVariable(
			BFCollection & tracePoints, const std::string & object);

	bool configureBuffer(
			BFCollection & tracePoints, const std::string & object);

	bool configureFormula(
			BFCollection & tracePoints, const BF & object);

	bool configureNodePathCondition(
			BFCollection & tracePoints, const BF & object);

	bool configureNodeInformation(
			BFCollection & tracePoints, const BF & object);

	bool configureMachine(
			BFCollection & tracePoints, const std::string & object);

	bool configureState(
			BFCollection & tracePoints, const std::string & object);
	bool configureStatemachine(
			BFCollection & tracePoints, const std::string & object);

	bool configureTransition(
			BFCollection & tracePoints, const std::string & object);

	bool configureRoutine(
			BFCollection & tracePoints, const std::string & object);

	bool configureRunnable(
			BFCollection & tracePoints, const std::string & object);


	////////////////////////////////////////////////////////////////////////////
	// BASIC PARSER API
	////////////////////////////////////////////////////////////////////////////

	bool parseBasicTrace(TraceSequence & aTraceElement,
			std::ifstream & inFile, const BF & aVarTime);

	bool parseBasicXliaTrace(TraceSequence & aTraceElement,
			std::ifstream & inFile, const BF & aVarTime);


	////////////////////////////////////////////////////////////////////////////
	// OTHER API
	////////////////////////////////////////////////////////////////////////////

	static bool appendTransitionPoint(
			const Configuration & aConfiguration,
			TraceSequence & aTraceElement,
			const std::string & aTransitionUfid);

	//TODO: removeTracePoint ?


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	void toStream(OutStream & os, ListOfTracePoint & listofTracePoint) const;

};


} /* namespace sep */

#endif /* TRACEFACTORY_H_ */

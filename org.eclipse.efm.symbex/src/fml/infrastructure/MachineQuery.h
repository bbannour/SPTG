/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 8 mars 2017
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_INFRASTRUCTURE_MACHINEQUERY_H_
#define FML_INFRASTRUCTURE_MACHINEQUERY_H_

#include <list>
#include <string>
#include <vector>


namespace sep
{

class BF;
class BehavioralPart;
class CompositePart;
class PropertyPart;
class Machine;
class Routine;
class System;

class MachineQuery
{

public:
	/**
	 * CONSTRUCTOR
	 * Executable
	 */
	MachineQuery()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~MachineQuery()
	{
		//!! NOTHING
	}

	/**
	 * API
	 */
	virtual const Machine * thisMachine() const = 0;

	virtual const PropertyPart & getPropertyPart() const = 0;


	virtual const CompositePart * getCompositePart() const = 0;

	virtual bool hasCompositePart() const = 0;


	virtual BehavioralPart * getBehaviorPart() const = 0;

	virtual bool hasBehaviorPart() const = 0;


	/**
	 * GETTER for PARSER / COMPILER
	 * any Property Element
	 */
	const BF & getPropertyByNameID(const std::string & aNameID) const;
	const BF & getrecPropertyByNameID(const std::string & aNameID) const;
	const BF & getsemPropertyByNameID(const std::string & aNameID) const;

	const BF & getPropertyByQualifiedNameID(
			const std::string & aQualifiedNameID) const;
	const BF & getrecPropertyByQualifiedNameID(
			const std::string & aQualifiedNameID) const;
	const BF & getsemPropertyByQualifiedNameID(
			const std::string & aQualifiedNameID) const;


	/**
	 * GETTER for PARSER / COMPILER
	 * Variable
	 */
	const BF & getVariable(const std::string & aQualifiedNameID) const;
	const BF & getrecVariable(const std::string & aQualifiedNameID) const;
	const BF & getsemVariable(const std::string & aQualifiedNameID) const;

	const BF & getDataType(const std::string & aQualifiedNameID) const;
	const BF & getrecDataType(const std::string & aQualifiedNameID) const;
	const BF & getsemDataType(const std::string & aQualifiedNameID) const;

	std::vector< std::string> getVariableNames() const;


	/**
	 * GETTER for PARSER / COMPILER
	 * Buffer
	 */
	const BF & getBuffer(const std::string & aQualifiedNameID) const;
	const BF & getrecBuffer(const std::string & aQualifiedNameID) const;
	const BF & getsemBuffer(const std::string & aQualifiedNameID) const;

	std::vector< std::string> getBufferNames() const;


	/**
	 * GETTER for PARSER / COMPILER
	 * Channel
	 */
	const BF & getChannel(const std::string & aQualifiedNameID) const;
	const BF & getrecChannel(const std::string & aQualifiedNameID) const;
	const BF & getsemChannel(const std::string & aQualifiedNameID) const;

	std::vector< std::string> getChannelNames() const;


	/**
	 * GETTER for PARSER / COMPILER
	 * Port
	 */
	const BF & getPort(const std::string & aQualifiedNameID) const;
	const BF & getrecPort(const std::string & aQualifiedNameID) const;
	const BF & getsemPort(const std::string & aQualifiedNameID) const;

	std::vector< std::string> getPortNames() const;


	/**
	 * GETTER for PARSER / COMPILER
	 * Signal
	 */
	const BF & getSignal(const std::string & aQualifiedNameID) const;
	const BF & getrecSignal(const std::string & aQualifiedNameID) const;
	const BF & getsemSignal(const std::string & aQualifiedNameID) const;

	std::vector< std::string> getSignalNames() const;


	/**
	 * GETTER for PARSER / COMPILER
	 * Port / Signal
	 */
	const BF & getPortSignal(const std::string & aQualifiedNameID) const;
	const BF & getrecPortSignal(const std::string & aQualifiedNameID) const;
	const BF & getsemPortSignal(const std::string & aQualifiedNameID) const;


	/**
	 * GETTER for PARSER / COMPILER
	 * any Behavior Element
	 */
	const BF & getBehaviorByNameID(const std::string & aNameID) const;
	const BF & getrecBehaviorByNameID(const std::string & aNameID) const;
	const BF & getsemBehaviorByNameID(const std::string & aNameID) const;

	const BF & getBehaviorByQualifiedNameID(
			const std::string & aQualifiedNameID) const;
	const BF & getrecBehaviorByQualifiedNameID(
			const std::string & aQualifiedNameID) const;
	const BF & getsemBehaviorByQualifiedNameID(
			const std::string & aQualifiedNameID) const;

	/**
	 * GETTER for PARSER / COMPILER
	 * Transition
	 */
	std::vector< std::string> getTransitionNames() const;


	/**
	 * GETTER for PARSER / COMPILER
	 * Routine
	 */
	Routine * rawRoutineByNameID(const std::string & aNameID) const;
	Routine * rawsemRoutineByNameID(const std::string & aNameID) const;

	std::vector< std::string> getRoutineNames() const;


	/**
	 * GETTER for PARSER / COMPILER
	 * Procedure
	 */
	Machine * rawProcedureByNameID(const std::string & aNameID) const;
	Machine * rawsemProcedureByNameID(const std::string & aNameID) const;

	std::vector< std::string> getProcedureNames() const;


	/**
	 * GETTER for PARSER / COMPILER
	 * Machine
	 */
	Machine * getMachineByNameID(const std::string & aNameID) const;
	Machine * getsemMachineByNameID(const std::string & aNameID) const;

	Machine * getMachine(const std::string & aQualifiedNameID) const;
	Machine * getrecMachine(const std::string & aQualifiedNameID,
			Machine * ignoreChildMachine = nullptr) const;
	Machine * getsemMachine(const std::string & aQualifiedNameID) const;

	Machine * getsemMachine(const std::vector< std::string > & aQualifiedNameID) const;

	Machine * getExecutableMachine(const std::string & aQualifiedNameID) const;
	Machine * getrecExecutableMachine(const std::string & aQualifiedNameID) const;
	Machine * getsemExecutableMachine(const std::string & aQualifiedNameID) const;

	Machine * getSelfExecutableMachine(const std::string & aQualifiedNameID) const;

	System * getContainerSystem() const;

	std::vector< std::string> getMachineNames() const;

	std::vector< std::string> getStateNames() const;

	std::vector< std::string> getInstanceNames() const;


	/**
	 * GETTER for PARSER / COMPILER
	 * any Object Element
	 */
	const BF & getObjectByNameID(const std::string & aNameID) const;
	const BF & getrecObjectByNameID(const std::string & aNameID) const;
	const BF & getsemObjectByNameID(const std::string & aNameID) const;

	const BF & getObjectByQualifiedNameID(
			const std::string & aQualifiedNameID) const;
	const BF & getrecObjectByQualifiedNameID(
			const std::string & aQualifiedNameID) const;
	const BF & getsemObjectByQualifiedNameID(
			const std::string & aQualifiedNameID) const;

};


} /* namespace sep */

#endif /* FML_INFRASTRUCTURE_MACHINEQUERY_H_ */

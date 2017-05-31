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

#ifndef FML_EXECUTABLE_EXECUTABLEQUERY_H_
#define FML_EXECUTABLE_EXECUTABLEQUERY_H_

#include <fml/common/ModifierElement.h>
#include <fml/common/SpecifierElement.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableSystem.h>

#include <sew/Configuration.h>


namespace sep
{

class BF;
class ObjectElement;
class Symbol;


class ExecutableQuery
{

protected:
	/**
	 * TYPEDEF
	 */
	typedef TableOfExecutableForm::const_raw_iterator  const_exec_iterator;

	/**
	 * ATTRIBUTES
	 */
	const Configuration & mConfiguration;


public:
	/**
	 * CONSTRUCTOR
	 */
	ExecutableQuery(const Configuration & aConfiguration)
	: mConfiguration( aConfiguration )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutableQuery()
	{
		//!! NOTHING
	}


	/*
	 * GETTER
	 * the Executable System
	 */
	inline const ExecutableSystem & getSystem() const
	{
		return( mConfiguration.getExecutableSystem() );
	}


	/**
	 * SEARCH
	 * ExecutableForm
	 */
	inline const BF & getExecutable(
			const std::string & aFullyQualifiedNameID) const
	{
		return( getSystem().getExecutables().getByFQNameID(
				aFullyQualifiedNameID ) );
	}


	inline const BF &  getExecutableByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		return( getSystem().getExecutables().
				getByQualifiedNameID(aQualifiedNameID) );
	}


	/**
	 * GETTER
	 * List of all RUNTIME Executable Element
	 */
	inline void getRuntimeExecutable(
			Collection< ExecutableForm * > & listOfExecutable)
	{
		listOfExecutable.append(
				getSystem().rawSystemInstance()->getExecutable() );

		getRuntimeExecutable(getSystem().rawSystemInstance(), listOfExecutable);
	}

	void getRuntimeExecutable(InstanceOfMachine * aMachine,
			Collection< ExecutableForm * > & listOfExecutable);


	/**
	 * SEARCH
	 * AvmTransition
	 */
	const BF & getTransitionByAstElement(
			const ObjectElement * astElement) const;

	const BF & getTransition(const std::string & aFullyQualifiedNameID) const;

	const BF & getTransitionByNameID(const std::string & aNameID) const;

	const BF & getTransitionByQualifiedNameID(
			const std::string & aQualifiedNameID) const;


	/**
	 * SEARCH
	 * AvmProgram
	 */
	const BF & getProgram(const std::string & aFullyQualifiedNameID) const;


	/**
	 * SEARCH
	 * AvmProgram
	 * ExecutableForm
	 */
	const BF & getExecutableOrProgram(
			const std::string & aFullyQualifiedNameID) const;

	// Getter by AST-Element
	const BF & getExecutableOrProgram(const ObjectElement * astElement) const;


	/**
	 * SEARCH
	 * InstanceOfBuffer
	 */
	const Symbol & getBuffer(const std::string & aFullyQualifiedNameID) const;

	const Symbol & getBufferByNameID(const std::string & aNameID) const;

	const Symbol & getBufferByQualifiedNameID(
			const std::string & aQualifiedNameID) const;

	const Symbol & getBufferByAstElement(
			const ObjectElement * astElement) const;


	/**
	 * SEARCH
	 * InstanceOfData
	 */
	const BF & getDataByNameID(const std::string & aNameID) const;
	const BF & getDataByQualifiedNameID(
			const std::string & aQualifiedNameID) const;

	const BF & getData(const std::string & aFullyQualifiedNameID) const;
	const BF & getDataByAstElement(const ObjectElement * astElement) const;


	/**
	 * SEARCH
	 * Symbol as InstanceOfPort
	 * by ID
	 */
	const Symbol & getPortByNameID(const std::string & aNameID,
			Modifier::DIRECTION_KIND direction) const;

	const Symbol & getPortByNameID(const std::string & aNameID) const;

	avm_size_t getPortByNameID(
			const std::string & aNameID, ListOfSymbol & listofPort,
			Modifier::DIRECTION_KIND direction, bool isStrongly = true) const;

	avm_size_t getPortByNameID(
			const std::string & aNameID, ListOfSymbol & listofPort) const;


	/**
	 * SEARCH
	 * Symbol as InstanceOfPort
	 * by [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	const Symbol & getPortByQualifiedNameID(
			const std::string & aQualifiedNameID,
			Modifier::DIRECTION_KIND direction,bool isStrongly = true) const;

	avm_size_t getPortByQualifiedNameID(
			const std::string & aQualifiedNameID, ListOfSymbol & listofPort,
			Modifier::DIRECTION_KIND direction, bool isStrongly = true) const;

	avm_size_t getPortByQualifiedNameID(
			const std::string & aQualifiedNameID,
			ListOfSymbol & listofPort) const;


	const Symbol & getPort(const std::string & aFullyQualifiedNameID) const;

	static const Symbol & getSemPort(const ExecutableForm * anExecutable,
			const std::string & aFullyQualifiedNameID);

	const Symbol & getPortByAstElement(const ObjectElement * astElement) const;

	static const Symbol & getSemPortByAstElement(
			const ExecutableForm * anExecutable,
			const ObjectElement * astElement);


	/**
	 * SEARCH
	 * InstanceOfChannel
	 */
	const Symbol & getChannel(const ObjectElement * astElement) const;


	/**
	 * SEARCH
	 * InstanceOfMachine
	 */
	const Symbol & getMachine(Specifier::DESIGN_KIND aDesign,
			const std::string & aFullyQualifiedNameID) const;

	const Symbol & getMachineByNameID(Specifier::DESIGN_KIND aDesign,
			const std::string & aNameID) const;

	const Symbol & getMachineByQualifiedNameID(Specifier::DESIGN_KIND aDesign,
			const std::string & aQualifiedNameID) const;

	InstanceOfMachine * rawMachineByNameID(
			Specifier::DESIGN_KIND aDesign, const std::string & aNameID) const;

	InstanceOfMachine * rawMachineByQualifiedNameID(
			Specifier::DESIGN_KIND aDesign,
			const std::string & aQualifiedNameID) const;

	const Symbol & getMachineByAstElement(Specifier::DESIGN_KIND aDesign,
			const ObjectElement * astElement) const;

	const BF & searchMachine(
			Specifier::DESIGN_KIND aDesign,
			const std::string & aQualifiedNameID);


	/**
	 * SEARCH
	 * for Machine Instance Model
	 */
	const Symbol & getInstanceModel(const ObjectElement * astElement) const;

	const Symbol & getSemInstanceModel(
			const ExecutableForm * anExecutable,
			const ObjectElement * astElement) const;

	/**
	 * SEARCH
	 * for Machine Instance Static
	 */
	const Symbol & getInstanceStatic(const ObjectElement * astElement) const;

	const Symbol & getSemInstanceStatic(
			const ExecutableForm * anExecutable,
			const ObjectElement * astElement) const;

	/**
	 * SEARCH
	 * for Machine Instance Dynamic
	 */
	const Symbol & getInstanceDynamic(const ObjectElement * astElement) const;

	const Symbol & getSemInstanceDynamic(
			const ExecutableForm * anExecutable,
			const ObjectElement * astElement) const;


	/**
	 * SEARCH
	 * any Instance
	 */
	const BF & getInstanceByAstElement(const ObjectElement * astElement) const;

};


} /* namespace sep */

#endif /* FML_EXECUTABLE_EXECUTABLEQUERY_H_ */

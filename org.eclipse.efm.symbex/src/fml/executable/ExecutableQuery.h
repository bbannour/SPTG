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
			Collection< const ExecutableForm * > & listOfExecutable)
	{
		listOfExecutable.append(
				getSystem().rawSystemInstance()->getExecutable() );

		getRuntimeExecutable(getSystem().rawSystemInstance(), listOfExecutable);
	}

	void getRuntimeExecutable(InstanceOfMachine * aMachine,
			Collection< const ExecutableForm * > & listOfExecutable);


	/**
	 * SEARCH
	 * AvmTransition
	 */
	const BF & getTransitionByAstElement(
			const ObjectElement & astElement) const;

	const BF & getTransition(const std::string & aFullyQualifiedNameID) const;

	inline const BF & getTransitionByID(const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getTransitionByNameID( anID ) );
		}
		else
		{
			return( getTransitionByQualifiedNameID( anID ) );
		}
	}

	const BF & getTransitionByNameID(const std::string & aNameID) const;

	const BF & getTransitionByQualifiedNameID(
			const std::string & aQualifiedNameID) const;


	std::size_t getTransitionByID(const ExecutableForm & anExecutable,
			const std::string & anID, BFList & listofTransition) const;


	// REGEX
	std::size_t getTransitionByREGEX(
			const std::string & aRedexID, BFList & listofTransition) const;

	std::size_t getTransitionByNameREGEX(const ExecutableForm & anExecutable,
			const std::string & aRedexID, BFList & listofTransition) const;


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
	const BF & getExecutableOrProgram(const ObjectElement & astElement) const;


	/**
	 * SEARCH
	 * InstanceOfBuffer
	 */
	const Symbol & getBuffer(const std::string & aFullyQualifiedNameID) const;

	inline const Symbol & getBufferByID(const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getBufferByNameID( anID ) );
		}
		else
		{
			return( getBufferByQualifiedNameID( anID ) );
		}
	}

	inline const Symbol & getBufferByID(
			const ExecutableForm & anExecutable, const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( anExecutable.getBuffer().getByNameID( anID ) );
		}
		else
		{
			return( getBuffer( NamedElement::makeFullyQualifiedNameID(
						anExecutable.getFullyQualifiedNameID(), anID, false) ) );
		}
	}


	const Symbol & getBufferByNameID(const std::string & aNameID) const;

	const Symbol & getBufferByQualifiedNameID(
			const std::string & aQualifiedNameID) const;

	const Symbol & getBufferByAstElement(
			const ObjectElement & astElement) const;


	/**
	 * SEARCH
	 * InstanceOfData
	 */
	inline const BF & getVariableByID(const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getVariableByNameID( anID ) );
		}
		else
		{
			return( getVariableByQualifiedNameID( anID ) );
		}
	}

	inline std::size_t getVariableByID(
			const std::string & anID, BFList & listofVariable) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getVariableByNameID( anID , listofVariable) );
		}
		else
		{
			return( getVariableByQualifiedNameID( anID , listofVariable ) );
		}
	}


	inline const BF & getVariableByID(
			const ExecutableForm & anExecutable, const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( anExecutable.getVariables().getByNameID( anID ) );
		}
		else
		{
			return( getVariable( NamedElement::makeFullyQualifiedNameID(
						anExecutable.getFullyQualifiedNameID(), anID, false) ) );
		}
	}

	const BF & getVariableByNameID(const std::string & aNameID) const;
	std::size_t getVariableByNameID(
			const std::string & aNameID, BFList & listofVariable) const;

	const BF & getVariableByQualifiedNameID(
			const std::string & aQualifiedNameID) const;
	std::size_t getVariableByQualifiedNameID(
			const std::string & aQualifiedNameID, BFList & listofVariable) const;

	const BF & getVariable(const std::string & aFullyQualifiedNameID) const;
	const BF & getVariableByAstElement(const ObjectElement & astElement) const;


	// REGEX
	std::size_t getVariableByREGEX(
			const std::string & aRedexID, BFList & listofVariable) const;

	std::size_t getVariableByNameREGEX(const ExecutableForm & anExecutable,
			const std::string & aRedexID, BFList & listofVariable) const;



	/**
	 * SEARCH
	 * Symbol as InstanceOfPort
	 * by ID
	 */
	inline const Symbol & getPortByID(const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getPortByNameID( anID ) );
		}
		else
		{
			return( getPortByQualifiedNameID( anID ) );
		}
	}

	inline const Symbol & getPortByID(
			const ExecutableForm & anExecutable, const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( anExecutable.getPort().getByNameID( anID ) );
		}
		else
		{
			return( getPort( NamedElement::makeFullyQualifiedNameID(
						anExecutable.getFullyQualifiedNameID(), anID, false) ) );
		}
	}


	inline const Symbol & getPortByID(const std::string & anID,
			Modifier::DIRECTION_KIND direction) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getPortByNameID( anID , direction ) );
		}
		else
		{
			return( getPortByQualifiedNameID( anID , direction ) );
		}
	}

	inline std::size_t getPortByID(
			const std::string & anID, ListOfSymbol & listofPort) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getPortByNameID(anID, listofPort) );
		}
		else
		{
			return( getPortByQualifiedNameID(anID, listofPort) );
		}
	}

	inline std::size_t getPortByID(
			const std::string & anID, ListOfSymbol & listofPort,
			Modifier::DIRECTION_KIND direction, bool isStrongly = true) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getPortByNameID(anID, listofPort, direction, isStrongly) );
		}
		else
		{
			return( getPortByQualifiedNameID(
					anID, listofPort, direction, isStrongly) );
		}
	}


	/**
	 * SEARCH
	 * Symbol as InstanceOfPort
	 * by Name ID
	 */
	const Symbol & getPortByNameID(const std::string & aNameID) const;

	const Symbol & getPortByNameID(const std::string & aNameID,
			Modifier::DIRECTION_KIND direction) const;

	std::size_t getPortByNameID(
			const std::string & aNameID, ListOfSymbol & listofPort) const;

	std::size_t getPortByNameID(
			const std::string & aNameID, ListOfSymbol & listofPort,
			Modifier::DIRECTION_KIND direction, bool isStrongly = true) const;


	/**
	 * SEARCH
	 * Symbol as InstanceOfPort
	 * by [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	const Symbol & getPortByQualifiedNameID(
			const std::string & aQualifiedNameID) const;

	const Symbol & getPortByQualifiedNameID(
			const std::string & aQualifiedNameID,
			Modifier::DIRECTION_KIND direction,bool isStrongly = true) const;

	std::size_t getPortByQualifiedNameID(
			const std::string & aQualifiedNameID,
			ListOfSymbol & listofPort) const;

	std::size_t getPortByQualifiedNameID(
			const std::string & aQualifiedNameID, ListOfSymbol & listofPort,
			Modifier::DIRECTION_KIND direction, bool isStrongly = true) const;


	const Symbol & getPort(const std::string & aFullyQualifiedNameID) const;

	static const Symbol & getSemPort(const ExecutableForm * anExecutable,
			const std::string & aFullyQualifiedNameID);

	const Symbol & getPortByAstElement(const ObjectElement & astElement) const;

	static const Symbol & getSemPortByAstElement(
			const ExecutableForm * anExecutable,
			const ObjectElement & astElement);

	// REGEX
	std::size_t getPortByREGEX(
			const std::string & aRedexID, ListOfSymbol & listofPort) const;

	std::size_t getPortByNameREGEX(const ExecutableForm & anExecutable,
			const std::string & aRedexID, ListOfSymbol & listofPort) const;



	/**
	 * SEARCH
	 * InstanceOfChannel
	 */
	const Symbol & getChannel(const ObjectElement & astElement) const;


	/**
	 * SEARCH
	 * InstanceOfMachine
	 */
	const Symbol & getMachine(Specifier::DESIGN_KIND aDesign,
			const std::string & aFullyQualifiedNameID) const;


	inline const Symbol & getMachineByID(
			Specifier::DESIGN_KIND aDesign, const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getMachineByNameID( aDesign , anID ) );
		}
		else
		{
			return( getMachineByQualifiedNameID( aDesign , anID ) );
		}
	}

	inline const Symbol & getMachineByID(const ExecutableForm & anExecutable,
			Specifier::DESIGN_KIND aDesign, const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( anExecutable.getInstanceByDesign(aDesign).getByNameID(anID) );
		}
		else
		{
			return( getMachine(aDesign, NamedElement::makeFullyQualifiedNameID(
						anExecutable.getFullyQualifiedNameID(), anID, false) ) );
		}
	}



	inline std::size_t getMachineByID(Specifier::DESIGN_KIND aDesign,
			const std::string & anID, ListOfSymbol & listofMachine) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getMachineByNameID(aDesign, anID, listofMachine) );
		}
		else
		{
			return( getMachineByQualifiedNameID(aDesign, anID, listofMachine) );
		}
	}


	const Symbol & getMachineByNameID(Specifier::DESIGN_KIND aDesign,
			const std::string & aNameID) const;

	std::size_t getMachineByNameID(Specifier::DESIGN_KIND aDesign,
			const std::string & aNameID, ListOfSymbol & listofMachine) const;


	const Symbol & getMachineByQualifiedNameID(Specifier::DESIGN_KIND aDesign,
			const std::string & aQualifiedNameID) const;

	std::size_t getMachineByQualifiedNameID(
			Specifier::DESIGN_KIND aDesign,
			const std::string & aQualifiedNameID,
			ListOfSymbol & listofMachine) const;


	InstanceOfMachine * rawMachineByNameID(
			Specifier::DESIGN_KIND aDesign, const std::string & aNameID) const;

	InstanceOfMachine * rawMachineByQualifiedNameID(
			Specifier::DESIGN_KIND aDesign,
			const std::string & aQualifiedNameID) const;

	const Symbol & getMachineByAstElement(Specifier::DESIGN_KIND aDesign,
			const ObjectElement & astElement) const;

	const BF & searchMachine(
			Specifier::DESIGN_KIND aDesign,
			const std::string & aQualifiedNameID);


	/**
	 * SEARCH
	 * for Machine Instance Model
	 */
	const Symbol & getInstanceModel(const ObjectElement & astElement) const;

	const Symbol & getSemInstanceModel(
			const ExecutableForm * anExecutable,
			const ObjectElement & astElement) const;

	/**
	 * SEARCH
	 * for Machine Instance Static
	 */
	const Symbol & getInstanceStatic(const ObjectElement & astElement) const;

	const Symbol & getSemInstanceStatic(
			const ExecutableForm * anExecutable,
			const ObjectElement & astElement) const;

	/**
	 * SEARCH
	 * for Machine Instance Dynamic
	 */
	const Symbol & getInstanceDynamic(const ObjectElement & astElement) const;

	const Symbol & getSemInstanceDynamic(
			const ExecutableForm * anExecutable,
			const ObjectElement & astElement) const;


	/**
	 * SEARCH
	 * any Instance
	 */
	const BF & getInstanceByAstElement(const ObjectElement & astElement) const;

};


} /* namespace sep */

#endif /* FML_EXECUTABLE_EXECUTABLEQUERY_H_ */

/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 avr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMOPERATIONVARIABLE_H_
#define AVMOPERATIONVARIABLE_H_

#include <map>

#include <fml/operator/Operator.h>


namespace sep
{


class BF;
class BaseInstanceForm;
class BaseTypeSpecifier;

class Variable;


class AvmOperationVariable
{

public:
	/**
	 * LOADER - DISPOSER
	 */
	static void load();
	static void dispose();


	/**
	 * GETTER - SETTER
	 * theVariableMap
	 */
	static std::map< std::string , const Operator * > theVariableMap;

	inline static const Operator * getVariable(const std::string & method)
	{
		return( theVariableMap[ method ] );
	}

	inline static bool isVariable(const std::string & method)
	{
		return( theVariableMap.find( method ) != theVariableMap.end() );
	}

	inline static void putVariable(
			const std::string & method, const Operator * anOperator)
	{
		theVariableMap[ method ] = anOperator;
	}



	/**
	 * GETTER - SETTER
	 * theContainerMap
	 */
	static std::map< std::string , const Operator * > theContainerMap;

	inline static const Operator * getContainer(const std::string & method)
	{
		return( theContainerMap[ method ] );
	}

	inline static bool isContainer(const std::string & method)
	{
		return( theContainerMap.find( method ) != theContainerMap.end() );
	}

	inline static void putContainer(
			const std::string & method, const Operator * anOperator)
	{
		theContainerMap[ method ] = anOperator;
	}



	/**
	 * GETTER - SETTER
	 * theQueueMap
	 */
	static std::map< std::string , const Operator * > theQueueMap;

	inline static const Operator * getQueue(const std::string & method)
	{
		return( theQueueMap[ method ] );
	}

	inline static bool isQueue(const std::string & method)
	{
		return( theQueueMap.find( method ) != theQueueMap.end() );
	}

	inline static void putQueue(
			const std::string & method, const Operator * anOperator)
	{
		theQueueMap[ method ] = anOperator;
	}



	/**
	 * GETTER - SETTER
	 * theTimeMap
	 */
	static std::map< std::string , const Operator * > theTimeMap;

	inline static const Operator * getTime(const std::string & method)
	{
		return( theTimeMap[ method ] );
	}

	inline static bool isTime(const std::string & method)
	{
		return( theTimeMap.find( method ) != theTimeMap.end() );
	}

	inline static void putTime(
			const std::string & method, const Operator * anOperator)
	{
		theTimeMap[ method ] = anOperator;
	}


	/**
	 * GETTER - SETTER
	 * theActivityMap
	 */
	static std::map< std::string , const Operator * > theActivityMap;

	inline static const Operator * getActivity(const std::string & method)
	{
		return( theActivityMap[ method ] );
	}

	inline static bool isActivity(const std::string & method)
	{
		return( theActivityMap.find( method ) != theActivityMap.end() );
	}

	inline static void putActivity(
			const std::string & method, const Operator * anOperator)
	{
		theActivityMap[ method ] = anOperator;
	}


	/**
	 * GETTER - SETTER
	 * theOtherMap
	 */
	static std::map< std::string , const Operator * > theOtherMap;

	inline static const Operator * getOther(const std::string & method)
	{
		return( theOtherMap[ method ] );
	}

	inline static bool isOther(const std::string & method)
	{
		return( theOtherMap.find( method ) != theOtherMap.end() );
	}

	inline static void putOther(
			const std::string & method, const Operator * anOperator)
	{
		theOtherMap[ method ] = anOperator;
	}



	/**
	 * GETTER - SETTER
	 */
	static const Operator * get(const std::string & method);

	static const Operator * get(
			const BF & aReceiver, const std::string & method);

	static const Operator * get(
			Variable * aVariable, const std::string & method);

	static const Operator * get(
			BaseInstanceForm * anInstance, const std::string & method);

	static const Operator * get(const BaseTypeSpecifier & aTypeSpecifier,
			const std::string & method);


	inline static bool exists(const std::string & method)
	{
		return( isVariable(method) || isContainer(method) ||
				isQueue(method)    || isTime(method)      ||
				isActivity(method) || isOther(method) );
	}

	static bool exists(BaseInstanceForm * anInstance, const std::string & method);

	inline static bool exists(
			const std::string & method, const Operator * anOperator)
	{
		return( (anOperator == getVariable(method))  ||
				(anOperator == getContainer(method)) ||
				(anOperator == getQueue(method))     ||
				(anOperator == getTime(method))      ||
				(anOperator == getActivity(method))  ||
				(anOperator == getOther(method)) );
	}


	static void put(BaseInstanceForm * anInstance,
			const std::string & method, const Operator * anOperator);


};



} /* namespace sep */
#endif /* AVMOPERATIONVARIABLE_H_ */

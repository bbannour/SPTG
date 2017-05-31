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
	static std::map< std::string , Operator * > theVariableMap;

	inline static Operator * getVariable(const std::string & method)
	{
		return( theVariableMap[ method ] );
	}

	inline static bool isVariable(const std::string & method)
	{
		return( theVariableMap.find( method ) != theVariableMap.end() );
	}

	inline static void putVariable(const std::string & method,
			Operator * anOperator)
	{
		theVariableMap[ method ] = anOperator;
	}



	/**
	 * GETTER - SETTER
	 * theContainerMap
	 */
	static std::map< std::string , Operator * > theContainerMap;

	inline static Operator * getContainer(const std::string & method)
	{
		return( theContainerMap[ method ] );
	}

	inline static bool isContainer(const std::string & method)
	{
		return( theContainerMap.find( method ) != theContainerMap.end() );
	}

	inline static void putContainer(const std::string & method,
			Operator * anOperator)
	{
		theContainerMap[ method ] = anOperator;
	}



	/**
	 * GETTER - SETTER
	 * theQueueMap
	 */
	static std::map< std::string , Operator * > theQueueMap;

	inline static Operator * getQueue(const std::string & method)
	{
		return( theQueueMap[ method ] );
	}

	inline static bool isQueue(const std::string & method)
	{
		return( theQueueMap.find( method ) != theQueueMap.end() );
	}

	inline static void putQueue(const std::string & method, Operator * anOperator)
	{
		theQueueMap[ method ] = anOperator;
	}



	/**
	 * GETTER - SETTER
	 * theTimeMap
	 */
	static std::map< std::string , Operator * > theTimeMap;

	inline static Operator * getTime(const std::string & method)
	{
		return( theTimeMap[ method ] );
	}

	inline static bool isTime(const std::string & method)
	{
		return( theTimeMap.find( method ) != theTimeMap.end() );
	}

	inline static void putTime(const std::string & method, Operator * anOperator)
	{
		theTimeMap[ method ] = anOperator;
	}


	/**
	 * GETTER - SETTER
	 * theActivityMap
	 */
	static std::map< std::string , Operator * > theActivityMap;

	inline static Operator * getActivity(const std::string & method)
	{
		return( theActivityMap[ method ] );
	}

	inline static bool isActivity(const std::string & method)
	{
		return( theActivityMap.find( method ) != theActivityMap.end() );
	}

	inline static void putActivity(const std::string & method,
			Operator * anOperator)
	{
		theActivityMap[ method ] = anOperator;
	}


	/**
	 * GETTER - SETTER
	 * theOtherMap
	 */
	static std::map< std::string , Operator * > theOtherMap;

	inline static Operator * getOther(const std::string & method)
	{
		return( theOtherMap[ method ] );
	}

	inline static bool isOther(const std::string & method)
	{
		return( theOtherMap.find( method ) != theOtherMap.end() );
	}

	inline static void putOther(const std::string & method, Operator * anOperator)
	{
		theOtherMap[ method ] = anOperator;
	}



	/**
	 * GETTER - SETTER
	 */
	static Operator * get(const std::string & method);

	static Operator * get(const BF & aReceiver, const std::string & method);

	static Operator * get(Variable * aVariable, const std::string & method);

	static Operator * get(BaseInstanceForm * anInstance,
			const std::string & method);

	static Operator * get(BaseTypeSpecifier * aTypeSpecifier,
			const std::string & method);


	inline static bool exist(const std::string & method)
	{
		return( isVariable(method) || isContainer(method) ||
				isQueue(method)    || isTime(method)      ||
				isActivity(method) || isOther(method) );
	}

	static bool exist(BaseInstanceForm * anInstance, const std::string & method);

	inline static bool exist(const std::string & method, Operator * anOperator)
	{
		return( (anOperator == getVariable(method))  ||
				(anOperator == getContainer(method)) ||
				(anOperator == getQueue(method))     ||
				(anOperator == getTime(method))      ||
				(anOperator == getActivity(method))  ||
				(anOperator == getOther(method)) );
	}


	static void put(BaseInstanceForm * anInstance,
			const std::string & method, Operator * anOperator);


};



} /* namespace sep */
#endif /* AVMOPERATIONVARIABLE_H_ */

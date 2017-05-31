/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 avr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMOPERATIONMACHINE_H_
#define AVMOPERATIONMACHINE_H_

#include <map>

#include <fml/operator/Operator.h>


namespace sep
{


class BF;
class BaseInstanceForm;
class Machine;


class AvmOperationMachine
{

public:
	/**
	 * LOADER - DISPOSER
	 */
	static void load();
	static void dispose();



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
	 * theStatusMap
	 */
	static std::map< std::string , Operator * > theStatusMap;

	inline static Operator * getStatus(const std::string & method)
	{
		return( theStatusMap[ method ] );
	}

	inline static bool isStatus(const std::string & method)
	{
		return( theStatusMap.find( method ) != theStatusMap.end() );
	}

	inline static void putStatus(const std::string & method,
			Operator * anOperator)
	{
		theStatusMap[ method ] = anOperator;
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

	inline static void putOther(const std::string & method,
			Operator * anOperator)
	{
		theOtherMap[ method ] = anOperator;
	}



	/**
	 * GETTER - SETTER
	 */
	static Operator * get(const std::string & method);

	static Operator * get(const BF & aReceiver, const std::string & method);

	inline static Operator * get(Machine * aMachine, const std::string & method)
	{
		return( get(method) );
	}

	inline static Operator * get(BaseInstanceForm * anInstance,
			const std::string & method)
	{
		return( get(method) );
	}


	inline static bool exist(const std::string & method)
	{
		return( isActivity(method) || isStatus(method) ||
				isOther(method) );
	}

	inline static bool exist(BaseInstanceForm * anInstance,
			const std::string & method)
	{
		return( exist(method) );
	}

	inline static bool exist(const std::string & method, Operator * anOperator)
	{
		return( (anOperator == getActivity(method)) ||
				(anOperator == getStatus(method))   ||
				(anOperator == getOther(method))    );
	}


	inline static void put(BaseInstanceForm * anInstance,
			const std::string & method, Operator * anOperator)
	{
		putOther(method, anOperator);
	}





};

} /* namespace sep */
#endif /* AVMOPERATIONMACHINE_H_ */

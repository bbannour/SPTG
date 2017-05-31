/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 avr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMOPERATIONFACTORY_H_
#define AVMOPERATIONFACTORY_H_

#include <map>

#include <fml/operator/Operator.h>


namespace sep
{


class BF;
class BaseInstanceForm;


class AvmOperationFactory
{


public:
	/**
	 * LOADER - DISPOSER
	 */
	static void load();
	static void dispose();


	/**
	 * GETTER - SETTER
	 * theGlobalMap
	 */
	static std::map< std::string , Operator * > theGlobalMap;

	inline static Operator * getGlobal(const std::string & method)
	{
		return( theGlobalMap[ method ] );
	}

	inline static bool isGlobal(const std::string & method)
	{
		return( theGlobalMap.find( method ) != theGlobalMap.end() );
	}

	inline static void putGlobal(const std::string & method,
			Operator * anOperator)
	{
		theGlobalMap[ method ] = anOperator;
	}

	inline static void resetGlobal(const std::string & method)
	{
		return( theGlobalMap.clear() );
	}


	/**
	 * GETTER - SETTER
	 */
	static Operator * get(const std::string & method);

	static Operator * get(const BF & aReceiver, const std::string & method);

	static Operator * get(BaseInstanceForm * anInstance,
			const std::string & method);


	static bool exist(const std::string & method);

	static bool exist(BaseInstanceForm * anInstance,
			const std::string & method);

	static bool exist(const std::string & method, Operator * anOperator);


	static void put(const std::string & method, Operator * anOperator);

	static void put(BaseInstanceForm * anInstance,
			const std::string & method, Operator * anOperator);


};



} /* namespace sep */
#endif /* AVMOPERATIONFACTORY_H_ */

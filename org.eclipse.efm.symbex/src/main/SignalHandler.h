/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#ifndef MAIN_SIGNALHANDLER_H_
#define MAIN_SIGNALHANDLER_H_


namespace sep
{

class SignalHandler
{

private :
	/**
	 * ATTRIBUTES
	 */
	static bool SIGNAL_INTERRUPT_FLAG;

public :
   static bool SIGNAL_QUIT_FLAG;


	/**
	 * clearSIGINT
	 *
	 */
	inline static void clearSIGINT()
	{
		SIGNAL_INTERRUPT_FLAG = false;
	}

	/**
	 * isSIGINT
	 *
	 */
	inline static bool isSIGINT()
	{
		return( SIGNAL_INTERRUPT_FLAG );
	}

	/**
	 * setSIGINT
	 *
	 */
	inline static void setSIGINT()
	{
		SIGNAL_INTERRUPT_FLAG = true;
	}

	static void SIGINT_handler(int nFlag);

	static void setSIGINT_handler();

};


}

#endif /* MAIN_SIGNALHANDLER_H_ */

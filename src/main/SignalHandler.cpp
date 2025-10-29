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

#include <csignal>

#include "SignalHandler.h"

#include <printer/OutStream.h>


namespace sep
{

bool SignalHandler::SIGNAL_INTERRUPT_FLAG = false;


/**
 * SignalHandler::SIGINT_handler
 *
 */
void SignalHandler::SIGINT_handler(int nFlag)
{
	setSIGINT();

	AVM_OS_WARN << std::endl << EMPHASIS(
			"SIGINT::handler< CTRL-C INTERRUPTION >", '*', 80);
}

/**
 * SignalHandler::setSIGINT_handler
 *
 */
void SignalHandler::setSIGINT_handler()
{
	clearSIGINT();

#ifdef __AVM_UNIX__

	static struct ::sigaction SIGINT_action;
	::sigemptyset( & SIGINT_action.sa_mask );
	SIGINT_action.sa_flags = 0;

	SIGINT_action.sa_handler = SIGINT_handler;

	/* Register the handler for SIGINT. */
	::sigaction(SIGINT, &SIGINT_action, 0);

// ::sigaction(SIGCONT, &SIGINT_action, 0);

#endif /* __AVM_UNIX__ */
}


}

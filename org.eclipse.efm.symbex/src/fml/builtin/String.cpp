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
#include "String.h"


namespace sep
{


/**
 * GLOBALS
 */
char String::DEFAULT_DELIMITER = DOUBLE_QUOTE_DELIMITER;

bool String::USE_BACKSLASH_QUOTE  = false;

const char String::BACKSLASH_CHAR = '\\';


/**
 * The empty string
 * EMPTY
 */
BF String::_EMPTY_;


}

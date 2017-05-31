/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 1 mars 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_EXPRESSION_RATIONAL_H_
#define FML_EXPRESSION_RATIONAL_H_

#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

#include <fml/numeric/gmp/RationalImpl.h>

#elif defined( _AVM_BUILTIN_NUMERIC_BOOST_ )

#include <fml/numeric/boost/RationalImpl.h>

#else

#include <fml/numeric/basic/RationalImpl.h>

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


namespace sep
{


} /* namespace sep */

#endif /* FML_EXPRESSION_RATIONAL_H_ */

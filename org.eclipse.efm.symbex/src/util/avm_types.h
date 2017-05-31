/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVM_TYPES_H_
#define AVM_TYPES_H_

#include <string>

#include <util/avm_numeric.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// The TIME UNIT, ...
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

typedef avm_uint64_t      avm_delay_value_t;

typedef avm_uint16_t       avm_unit_t;

enum {
	AVM_UNDEFINED_UNIT    = 0x0000,

	AVM_NANO_SECOND_UNIT  = 0x0001,
	AVM_MICRO_SECOND_UNIT = 0x0002,
	AVM_MILLI_SECOND_UNIT = 0x0004,
	AVM_SECOND_UNIT       = 0x0008,

	AVM_MINUTE_UNIT       = 0x0010,
	AVM_HOUR_UNIT         = 0x0020,

	AVM_MICRO_STEP_UNIT   = 0x0040,
	AVM_STEP_UNIT         = 0x0080,
	AVM_MACRO_STEP_UNIT   = 0x0100,
};


#define IS_UNDEFINED_UNIT(unit)    (unit == AVM_UNDEFINED_UNIT)

#define IS_NANO_SECOND_UNIT(unit)  (unit & AVM_NANO_SECOND_UNIT)
#define IS_MILLI_SECOND_UNIT(unit) (unit & AVM_MILLI_SECOND_UNIT)
#define IS_SECOND_UNIT(unit)       (unit & AVM_SECOND_UNIT)

#define IS_MINUTE_UNIT(unit)       (unit & AVM_MINUTE_UNIT)
#define IS_HOUR_UNIT(unit)         (unit & AVM_HOUR_UNIT)

#define IS_MICRO_STEP_UNIT(unit)   (unit & AVM_MICRO_STEP_UNIT)
#define IS_STEP_UNIT(unit)         (unit & AVM_STEP_UNIT)
#define IS_MACRO_STEP_UNIT(unit)   (unit & AVM_MACRO_STEP_UNIT)


extern std::string strUnit(avm_unit_t unit);



}

#endif /* AVM_TYPES_H_ */

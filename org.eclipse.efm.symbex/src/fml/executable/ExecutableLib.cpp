/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 juil. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExecutableLib.h"

#include <fml/common/ModifierElement.h>

#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/type/TypeManager.h>


namespace sep
{

/**
 * PRE DEFINED MACHINE VARIABLE
 */
Symbol ExecutableLib::MACHINE_NULL;
Symbol ExecutableLib::MACHINE_ENVIRONMENT;

Symbol ExecutableLib::MACHINE_SELF;
Symbol ExecutableLib::MACHINE_PARENT;
Symbol ExecutableLib::MACHINE_COMMUNICATOR;

Symbol ExecutableLib::MACHINE_COMPONENT_SELF;
Symbol ExecutableLib::MACHINE_COMPONENT_PARENT;
Symbol ExecutableLib::MACHINE_COMPONENT_COMMUNICATOR;

Symbol ExecutableLib::MACHINE_SYSTEM;


/**
 * PRE DEFINED NULL FORM
 */
Symbol ExecutableLib::CHANNEL_NIL;
Symbol ExecutableLib::PORT_NIL;
Symbol ExecutableLib::BUFFER_NIL;


/**
 * BOTTOM
 * TOP
 */
Symbol ExecutableLib::BOTTOM;
Symbol ExecutableLib::TOP;

Symbol ExecutableLib::_NULL_;

Symbol ExecutableLib::_INFINITY_;


/**
 * LOADER
 */
void ExecutableLib::load()
{
	MACHINE_NULL = new InstanceOfMachine(NULL, NULL, NULL, NULL, 0,
			Specifier::DESIGN_INSTANCE_STATIC_SPECIFIER);
	MACHINE_NULL.machine().getwModifier().setModifierPublicFinalStatic();
	MACHINE_NULL.setAllNameID("null#machine", "null#machine");
//	MACHINE_NULL.setAllNameID("null< machine >", "null< machine >");
	MACHINE_NULL.machine().setInstanceModel(MACHINE_NULL.rawMachine());

	MACHINE_SELF = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::MACHINE, "const::self", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);

	MACHINE_PARENT = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::MACHINE, "const::parent", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);

	MACHINE_COMMUNICATOR = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::MACHINE, "const::machine#com", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);


	MACHINE_COMPONENT_SELF = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::MACHINE, "const::machine#component#self", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);

	MACHINE_COMPONENT_PARENT = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::MACHINE, "const::machine#component#parent", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);

	MACHINE_COMPONENT_COMMUNICATOR = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::MACHINE, "const::machine#component#communicator", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);


	MACHINE_SYSTEM = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::MACHINE, "const::system", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);

	MACHINE_ENVIRONMENT = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::MACHINE, "const::env", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);


	CHANNEL_NIL = InstanceOfPort::newChannel(
			NULL, NULL, AVM_NUMERIC_MAX_OFFSET);
	CHANNEL_NIL.setAllNameID("null#channel", "null#channel");
//	CHANNEL_NIL.setAllNameID("null< channel >", "null< channel >");

	PORT_NIL = new InstanceOfPort(NULL, NULL,
			AVM_NUMERIC_MAX_OFFSET, 0, IComPoint::IO_UNDEFINED_NATURE);
	PORT_NIL.setAllNameID("null#port", "null#port");
//	PORT_NIL.setAllNameID("null< port >", "null< port >");

	BUFFER_NIL = new InstanceOfBuffer(NULL, NULL, AVM_NUMERIC_MAX_OFFSET,
			TYPE_UNDEFINED_SPECIFIER, -1);
	BUFFER_NIL.setAllNameID("null#buffer", "null#buffer");
//	BUFFER_NIL.setAllNameID("null< buffer >", "null< buffer >");


	BOTTOM = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::UNIVERSAL, "const::BOTTOM", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);

	TOP = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::UNIVERSAL, "const::TOP", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);

	_NULL_ = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::UNIVERSAL, "const::NULL", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);

	_INFINITY_ = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			TypeManager::UNIVERSAL, "const::INFINITY", 0,
			Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);
}


/**
 * DISPOSER
 */
void ExecutableLib::dispose()
{
	MACHINE_NULL.destroy();
	MACHINE_ENVIRONMENT.destroy();

	MACHINE_SELF.destroy();
	MACHINE_PARENT.destroy();
	MACHINE_COMMUNICATOR.destroy();
	MACHINE_COMPONENT_SELF.destroy();
	MACHINE_COMPONENT_PARENT.destroy();
	MACHINE_COMPONENT_COMMUNICATOR.destroy();
	MACHINE_SYSTEM.destroy();

	CHANNEL_NIL.destroy();
	PORT_NIL.destroy();
	BUFFER_NIL.destroy();

	BOTTOM.destroy();
	TOP.destroy();

	_NULL_.destroy();

	_INFINITY_.destroy();
}



}

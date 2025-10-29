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
#ifndef CONTAINER_TYPEDEF_H_
#define CONTAINER_TYPEDEF_H_


#include <collection/Array.h>

#include <collection/Collection.h>

#include <collection/List.h>

#include <collection/Multiset.h>

#include <collection/Pair.h>

#include <collection/Set.h>

#include <collection/Vector.h>



namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// MACRO FOR TYPEDEF DEFINITION
////////////////////////////////////////////////////////////////////////////////


// LIST
#define DEFINE_LIST_REF_T(ClassName, TypedefName) \
	typedef List < ClassName > ListOf##TypedefName;

#define DEFINE_LIST_REF(ClassName)              \
	typedef List < ClassName > ListOf##ClassName;

#define DEFINE_LIST_PTR_T(ClassName, TypedefName)   \
	typedef List < ClassName * > ListOf##TypedefName;

#define DEFINE_LIST_PTR(ClassName)                \
	typedef List < ClassName * > ListOf##ClassName;

#define DEFINE_LIST_CONST_PTR(ClassName)                \
	typedef List < const ClassName * > ListOf##ClassName;


// VECTOR
#define DEFINE_VECTOR_REF_T(ClassName, TypedefName)   \
	typedef Vector < ClassName > VectorOf##TypedefName;

#define DEFINE_VECTOR_REF(ClassName)                \
	typedef Vector < ClassName > VectorOf##ClassName;

#define DEFINE_VECTOR_PTR_T(ClassName, TypedefName)     \
	typedef Vector < ClassName * > VectorOf##TypedefName;

#define DEFINE_VECTOR_PTR(ClassName)                  \
	typedef Vector < ClassName * > VectorOf##ClassName;

#define DEFINE_APVECTOR_PTR(ClassName)                    \
	typedef APVector < ClassName * > APVectorOf##ClassName;



// PAIR
#define DEFINE_PAIR_REF(ClassNameA, ClassNameB, TypedefName) \
	typedef Pair < ClassNameA , ClassNameB > TypedefName;

#define DEFINE_PAIR_PTR(ClassNameA, ClassNameB, TypedefName) \
	typedef Pair < ClassNameA  * , ClassNameB * > TypedefName;




////////////////////////////////////////////////////////////////////////////////
// CLASS
////////////////////////////////////////////////////////////////////////////////


class BFCode;
class RuntimeID;

class AvmProgram;
class AvmTransition;

class ExecutableForm;

class InstanceOfBuffer;
class InstanceOfData;
class InstanceOfMachine;
class InstanceOfPort;

class Machine;


////////////////////////////////////////////////////////////////////////////////
// TYPEDEF FOR COLLECTION < BFCode >
////////////////////////////////////////////////////////////////////////////////

typedef Collection < BFCode > BFCodeCollection;
typedef       List < BFCode > BFCodeList;
typedef     Vector < BFCode > BFCodeVector;


/**
 * TYPE LIST DECLARATIONS
 */

DEFINE_LIST_REF_T(int , Int)

DEFINE_LIST_REF_T( std::string , String )


////////////////////////////////////////////////////////////////////////////////
// List
////////////////////////////////////////////////////////////////////////////////

DEFINE_LIST_PTR( Machine )

DEFINE_LIST_PTR( AvmProgram )

DEFINE_LIST_PTR( ExecutableForm )

DEFINE_LIST_PTR( InstanceOfBuffer )
DEFINE_LIST_PTR( InstanceOfData )
DEFINE_LIST_PTR( InstanceOfMachine )
DEFINE_LIST_PTR( InstanceOfPort )


/**
 * TYPE VECTOR DECLARATIONS
 */
DEFINE_VECTOR_REF_T(int , Int)

DEFINE_VECTOR_REF_T( std::string , String )


////////////////////////////////////////////////////////////////////////////////
// Vector
////////////////////////////////////////////////////////////////////////////////

DEFINE_VECTOR_PTR( AvmProgram )

DEFINE_VECTOR_PTR( AvmTransition )

DEFINE_VECTOR_PTR( InstanceOfData )

DEFINE_VECTOR_PTR( InstanceOfMachine )


////////////////////////////////////////////////////////////////////////////////
// Set & Multiset
////////////////////////////////////////////////////////////////////////////////

/**
 * TYPE MIXED DECLARATIONS
 */

DEFINE_PAIR_REF( RuntimeID , ListOfInstanceOfData , PairMachineData )

DEFINE_LIST_REF( PairMachineData )


}

#endif /*CONTAINER_TYPEDEF_H_*/


/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 juin 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmLookupPrimitive.h"

#include <computer/EvaluationEnvironment.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/numeric/Float.h>
#include <fml/numeric/Integer.h>

#include <fml/type/TypeManager.h>



namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// LOOKUP MACRO
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

#define linearInterpolation1D(x, xa, xb, ya, yb) 	\
	( ya + ( x - xa ) * (yb - ya) / (xb - xa) )



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// LOOKUP Int
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

double AvmPrimitive_Lookup_Int::lookup(double anInput,
		ArrayFloat * anInputTable, ArrayFloat * anOutputTable)
{
	avm_offset_t index = 0;

	for( ; index < anInputTable->size() ; ++index )
	{
		if( anInputTable->get(index) >= anInput )
		{
			break;
		}
	}

	if( index == anInputTable->size() )
	{
		return anOutputTable->get(index-1);
	}
	else if( index == 0 )
	{
		return anOutputTable->get(0);
	}
	else if( anInput == anInputTable->get(index) )
	{
		return anOutputTable->get(index);
	}
	else
	{
		return linearInterpolation1D(anInput, anInputTable->get(index-1),
				anInputTable->get(index), anOutputTable->get(index-1),
				anOutputTable->get(index));
	}
}


bool AvmPrimitive_Lookup_Int::seval(EvaluationEnvironment & ENV)
{
	BF inputValue = ENV.mARG->at(0);

	const BF & inputTable = ENV.mARG->at(1);
	const BF & outputTable = ENV.mARG->at(2);

	// CASE of NUMERIC VALUE
	if( inputValue.isInteger() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup(inputValue.toInteger(),
						inputTable.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayFloat >()) );
	}
	else if( inputValue.isFloat() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup(inputValue.toFloat(),
						inputTable.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayFloat >()) );
	}
	// CASE of SYMBOLIC VALUE
	else if( inputValue.is< InstanceOfData >() )
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID,
				"lookupInt", TypeManager::FLOAT,
				ExpressionConstructor::newCode(ENV.inCODE->getOperator(),
						inputValue, inputTable, outputTable));
	}
	// CASE of SYMBOLIC EXPRESSION
	else
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID,
				"lookupInt", TypeManager::FLOAT,
				ExpressionConstructor::newCode(ENV.inCODE->getOperator(),
						inputValue, inputTable, outputTable));
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// LOOKUP IntExt
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

double AvmPrimitive_Lookup_IntExt::lookup(double anInput,
		ArrayFloat * anInputTable, ArrayFloat * anOutputTable)
{
	avm_offset_t index = 0;

	for( ; index < anInputTable->size() ; ++index )
	{
		if( anInputTable->get(index) >= anInput )
		{
			break;
		}
	}

	if( index == anInputTable->size() )
	{
		return linearInterpolation1D(anInput, anInputTable->get(index-2),
				anInputTable->get(index-1), anOutputTable->get(index-2),
				anOutputTable->get(index-1));
	}
	else if( anInput == anInputTable->get(index) )
	{
		return anOutputTable->get(index);
	}
	else if( index == 0 )
	{
		return linearInterpolation1D(anInput, anInputTable->get(0),
				anInputTable->get(1), anOutputTable->get(0),
				anOutputTable->get(1));
	}
	else
	{
		return linearInterpolation1D(anInput, anInputTable->get(index-1),
				anInputTable->get(index), anOutputTable->get(index-1),
				anOutputTable->get(index));
	}
}


bool AvmPrimitive_Lookup_IntExt::seval(EvaluationEnvironment & ENV)
{
	BF inputValue = ENV.mARG->at(0);

	const BF & inputTable = ENV.mARG->at(1);
	const BF & outputTable = ENV.mARG->at(2);

	// CASE of NUMERIC VALUE
	if( inputValue.isInteger() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup(inputValue.toInteger(),
						inputTable.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayFloat >()) );
	}
	else if( inputValue.isFloat() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup(inputValue.toFloat(),
						inputTable.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayFloat >()) );
	}
	// CASE of SYMBOLIC VALUE
	else if( inputValue.is< InstanceOfData >() )
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID,
				"lookupIntExt", TypeManager::FLOAT,
				ExpressionConstructor::newCode(ENV.inCODE->getOperator(),
						inputValue, inputTable, outputTable));
	}
	// CASE of SYMBOLIC EXPRESSION
	else
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID,
				"lookupIntExt", TypeManager::FLOAT,
				ExpressionConstructor::newCode(ENV.inCODE->getOperator(),
						inputValue, inputTable, outputTable));
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// LOOKUP Nearest
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

double AvmPrimitive_Lookup_Nearest::lookup(double anInput,
		ArrayFloat * anInputTable, ArrayFloat * anOutputTable)
{
	avm_offset_t index = 0;

	for( ; index < anInputTable->size() ; ++index )
	{
		if( anInputTable->get(index) >= anInput )
		{
			break;
		}
	}

	if( index == anInputTable->size() )
	{
		index = index - 1;
	}
	else if( index > 0 )
	{
		if( (anInput - anInputTable->get(index - 1)) <
				(anInputTable->get(index) - anInput) )
		{
			index = index - 1;
		}
	}

	return( anOutputTable->get(index) );
}


bool AvmPrimitive_Lookup_Nearest::seval(EvaluationEnvironment & ENV)
{
	BF inputValue = ENV.mARG->at(0);

	const BF & inputTable = ENV.mARG->at(1);
	const BF & outputTable = ENV.mARG->at(2);

	// CASE of NUMERIC VALUE
	if( inputValue.isInteger() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup(inputValue.toInteger(),
						inputTable.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayFloat >()) );
	}
	else if( inputValue.isFloat() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup(inputValue.toFloat(),
						inputTable.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayFloat >()) );
	}
	// CASE of SYMBOLIC VALUE
	else if( inputValue.is< InstanceOfData >() )
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID,
				"lookupNearest", TypeManager::FLOAT,
				ExpressionConstructor::newCode(ENV.inCODE->getOperator(),
						inputValue, inputTable, outputTable));
	}
	// CASE of SYMBOLIC EXPRESSION
	else
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID,
				"lookupNearest", TypeManager::FLOAT,
				ExpressionConstructor::newCode(ENV.inCODE->getOperator(),
						inputValue, inputTable, outputTable));
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// LOOKUP Below
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

double AvmPrimitive_Lookup_Below::lookup(double anInput,
		ArrayFloat * anInputTable, ArrayFloat * anOutputTable)
{
	avm_offset_t index = 0;

	for( ; index < anInputTable->size() ; ++index )
	{
		if( anInputTable->get(index) >= anInput )
		{
			break;
		}
	}

	if( (index > 0) && (anInputTable->get(index) != anInput))
	{
		index = index - 1;
	}

	return( anOutputTable->get(index) );
}


bool AvmPrimitive_Lookup_Below::seval(EvaluationEnvironment & ENV)
{
	BF inputValue = ENV.mARG->at(0);

	const BF & inputTable = ENV.mARG->at(1);
	const BF & outputTable = ENV.mARG->at(2);

	// CASE of NUMERIC VALUE
	if( inputValue.isInteger() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup(inputValue.toInteger(),
						inputTable.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayFloat >()) );
	}
	else if( inputValue.isFloat() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup(inputValue.toFloat(),
						inputTable.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayFloat >()) );
	}
	// CASE of SYMBOLIC VALUE
	else if( inputValue.is< InstanceOfData >() )
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID,
				"lookupBelow", TypeManager::FLOAT,
				ExpressionConstructor::newCode(ENV.inCODE->getOperator(),
						inputValue, inputTable, outputTable));
	}
	// CASE of SYMBOLIC EXPRESSION
	else
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID,
				"lookupBelow", TypeManager::FLOAT,
				ExpressionConstructor::newCode(ENV.inCODE->getOperator(),
						inputValue, inputTable, outputTable));
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// LOOKUP Above
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

double AvmPrimitive_Lookup_Above::lookup(double anInput,
		ArrayFloat * anInputTable, ArrayFloat * anOutputTable)
{
	avm_offset_t index = 0;

	for( ; index < anInputTable->size() ; ++index )
	{
		if( anInputTable->get(index) >= anInput )
		{
			break;
		}
	}

	if( (index == anInputTable->size()) &&
			(anInputTable->get(index) != anInput))
	{
		index = index - 1;
	}

	return( anOutputTable->get(index) );
}


bool AvmPrimitive_Lookup_Above::seval(EvaluationEnvironment & ENV)
{
	BF inputValue = ENV.mARG->at(0);

	const BF & inputTable = ENV.mARG->at(1);
	const BF & outputTable = ENV.mARG->at(2);

	// CASE of NUMERIC VALUE
	if( inputValue.isInteger() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup(inputValue.toInteger(),
						inputTable.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayFloat >()) );
	}
	else if( inputValue.isFloat() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup(inputValue.toFloat(),
						inputTable.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayFloat >()) );
	}
	// CASE of SYMBOLIC VALUE
	else if( inputValue.is< InstanceOfData >() )
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID,
				"lookupAbove", TypeManager::FLOAT,
				ExpressionConstructor::newCode(ENV.inCODE->getOperator(),
						inputValue, inputTable, outputTable));
	}
	// CASE of SYMBOLIC EXPRESSION
	else
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID,
				"lookupAbove", TypeManager::FLOAT,
				ExpressionConstructor::newCode(ENV.inCODE->getOperator(),
						inputValue, inputTable, outputTable));
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// LOOKUP2D IntExt
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

double AvmPrimitive_Lookup2D_IntExt::lookup2D(
		double anInput1, double anInput2,
		ArrayFloat * anInputTable1, ArrayFloat * anInputTable2,
		ArrayBF * anOutputTable)
{
	// Recherche ic1 et ic2 (index des colonnes à considérer)
	avm_offset_t index = 0;
	for( ; index < anInputTable2->size() ; ++index )
	{
		if( anInputTable2->get(index) >= anInput2 )
		{
			break;
		}
	}

	avm_offset_t il1;
	avm_offset_t il2;
	avm_offset_t ic1;
	avm_offset_t ic2;

	if( index == anInputTable2->size() )
	{
		ic1 = index-2;
		ic2 = index-1;
	}
	else if( anInput2 == anInputTable2->get(index) )
	{
		ic1 = index;
		ic2 = index;
	}
	else if( index == 0 )
	{
		ic1 = 0;
		ic2 = 1;
	}
	else
	{
		ic1 = index-1;
		ic2 = index;
	}

	// Interpolation linéaire de anInput1 sur il1 puis sur il2
	index = 0;
	for( ; index < anInputTable1->size() ; ++index )
	{
		if( anInputTable1->get(index) >= anInput1 )
		{
			break;
		}
	}

	double intermediateResult1;
	double intermediateResult2;
	if( index == anInputTable1->size() )
	{
		il1 = index - 2;
		il2 = index - 1;

		intermediateResult1 = linearInterpolation1D(anInput1,
				anInputTable1->get(il1),anInputTable1->get(il2),
				anOutputTable->at(il1).to_ptr< ArrayFloat >()->get(ic1),
				anOutputTable->at(il1).to_ptr< ArrayFloat >()->get(ic2));

		intermediateResult2 = linearInterpolation1D(anInput1,
				anInputTable1->get(il1),anInputTable1->get(il2),
				anOutputTable->at(il2).to_ptr< ArrayFloat >()->get(ic1),
				anOutputTable->at(il2).to_ptr< ArrayFloat >()->get(ic2));
	}
	else if( anInput1 == anInputTable1->get(index) )
	{
		intermediateResult1 =
				anOutputTable->at(index).to_ptr< ArrayFloat >()->get(ic1);

		intermediateResult2 =
				anOutputTable->at(index).to_ptr< ArrayFloat >()->get(ic2);
	}
	else if( index == 0 )
	{
		intermediateResult1 = linearInterpolation1D(anInput1,
				anInputTable1->get(0),anInputTable1->get(1),
				anOutputTable->at(0).to_ptr< ArrayFloat >()->get(ic1),
				anOutputTable->at(1).to_ptr< ArrayFloat >()->get(ic1));

		intermediateResult2 = linearInterpolation1D(anInput1,
				anInputTable1->get(0),anInputTable1->get(1),
				anOutputTable->at(0).to_ptr< ArrayFloat >()->get(ic2),
				anOutputTable->at(1).to_ptr< ArrayFloat >()->get(ic2));
	}
	else
	{
		intermediateResult1 = linearInterpolation1D(anInput1,
				anInputTable1->get(index-1),anInputTable1->get(index),
				anOutputTable->at(index-1).to_ptr< ArrayFloat >()->get(ic1),
				anOutputTable->at(index).to_ptr< ArrayFloat >()->get(ic1));

		intermediateResult2 = linearInterpolation1D(anInput1,
				anInputTable1->get(index-1),anInputTable1->get(index),
				anOutputTable->at(index-1).to_ptr< ArrayFloat >()->get(ic2),
				anOutputTable->at(index).to_ptr< ArrayFloat >()->get(ic2));
	}

	if ( ic1 == ic2 )
	{
		return( intermediateResult1 );
	}

	return( ((anInputTable2->get(ic2) - anInput2) /
				(anInputTable2->get(ic2) - anInputTable2->get(ic1)) * intermediateResult1) +
			((anInput2 - anInputTable2->get(ic1)) /
				(anInputTable2->get(ic2) - anInputTable2->get(ic1)) * intermediateResult2) );
}


bool AvmPrimitive_Lookup2D_IntExt::seval(EvaluationEnvironment & ENV)
{
	BF inputValue1 = ENV.mARG->at(0);
	BF inputValue2 = ENV.mARG->at(1);

	const BF & inputTable1 = ENV.mARG->at(2);
	const BF & inputTable2 = ENV.mARG->at(3);
	const BF & outputTable = ENV.mARG->at(4);


	double fInput1;
	// CASE of NUMERIC VALUE
	if( inputValue1.isInteger() )
	{
		fInput1 = inputValue1.toInteger();
	}
	else if( inputValue1.isFloat() )
	{
		fInput1 = inputValue1.toFloat();
	}
	// CASE of SYMBOLIC VALUE
	else if( inputValue1.is< InstanceOfData >() ||
			inputValue2.is< InstanceOfData >() )
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID, "lookup2DIntExt",
				TypeManager::FLOAT, ExpressionConstructor::newCode(
						ENV.inCODE->getOperator(), inputValue1, inputValue2,
						inputTable1, inputTable2, outputTable ) );
		return( true );
	}
	// CASE of SYMBOLIC EXPRESSION
	else
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID, "lookup2DIntExt",
				TypeManager::FLOAT, ExpressionConstructor::newCode(
						ENV.inCODE->getOperator(), inputValue1, inputValue2,
						inputTable1, inputTable2, outputTable ) );
		return( true );
	}

	// CASE of NUMERIC VALUE
	if( inputValue2.isInteger() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup2D(fInput1, inputValue2.toInteger(),
						inputTable1.to_ptr< ArrayFloat >(),
						inputTable2.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayBF >()) );
	}
	else if( inputValue2.isFloat() )
	{
		ENV.outVAL = ExpressionConstructor::newExpr(
				lookup2D(fInput1, inputValue2.toFloat(),
						inputTable1.to_ptr< ArrayFloat >(),
						inputTable2.to_ptr< ArrayFloat >(),
						outputTable.to_ptr< ArrayBF >()) );
	}
	// CASE of SYMBOLIC EXPRESSION
	else
	{
		ENV.outVAL = ENV.create(ENV.outED->mRID, "lookup2DIntExt",
				TypeManager::FLOAT, ExpressionConstructor::newCode(
						ENV.inCODE->getOperator(), inputValue1, inputValue2,
						inputTable1, inputTable2, outputTable ) );
	}

	return( true );
}



}

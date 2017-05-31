/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 déc. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODEFACTORY_H_
#define AVMCODEFACTORY_H_

#include <collection/BFContainer.h>
#include <collection/Typedef.h>

#include <fml/expression/AvmCode.h>
#include <fml/builtin/String.h>

#include <computer/instruction/AvmBytecode.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorLib.h>
#include <fml/operator/OperatorManager.h>


namespace sep
{


class ExecutableForm;


class AvmCodeFactory
{

public:

	/**
	 * STATEMENT EXPRESSION
	 */
	inline static BFCode newCode()
	{
		return( BFCode( new AvmCode() ) );
	}

	inline static BFCode newCode(Operator * anOperator)
	{
		return( BFCode( new AvmCode(anOperator) ) );
	}

	inline static BFCode newCode(Operator * anOperator, const BF & arg)
	{
		return( BFCode( new AvmCode( anOperator, arg) ) );
	}

	inline static BFCode newOptiNopCode(Operator * anOperator,
			const BF & arg, avm_arg_operand_t operand)
	{
		AvmCode * aCode = new AvmCode( anOperator, arg);
		aCode->setInstruction( AvmInstruction::nopsUnaryCode(operand) );

		return( BFCode( aCode ) );
	}



	inline static BFCode newCode(Operator * anOperator,
			const BF & arg1, const BF & arg2)
	{
		return( BFCode( new AvmCode(anOperator, arg1, arg2) ) );
	}


	inline static BFCode xnewCode(Operator * anOperator,
			const BFCode & aCode1, const BFCode & aCode2)
	{
		if( aCode1.invalid() )
		{
			return( aCode2 );
		}
		else if( aCode2.invalid() )
		{
			return( aCode1 );
		}
		else
		{
			return( newCode(anOperator, aCode1, aCode2) );
		}
	}



	inline static BFCode newCodeFlat(Operator * anOperator, const BFCode & aCode)
	{
		BFCode newCode( anOperator );

		if( anOperator->isWeakAssociative() &&
				(aCode->getOperator() == anOperator) )
		{
			newCode->append( aCode->getArgs() );
		}
		else
		{
			newCode->append( aCode );
		}

		return newCode;
	}

	inline static BFCode newCodeFlat(Operator * anOperator,
			const BFCode & aCode, const BF & arg)
	{
		BFCode newCode( anOperator );

		if( anOperator->isWeakAssociative() &&
				(aCode->getOperator() == anOperator) )
		{
			newCode->append( aCode->getArgs() );
		}
		else
		{
			newCode->append( aCode );
		}

		newCode->append( arg );

		return newCode;
	}

	inline static BFCode newCodeFlat(Operator * anOperator,
			const BF & arg, const BFCode & aCode)
	{
		BFCode newCode( anOperator , arg );

		if( anOperator->isWeakAssociative() &&
				(aCode->getOperator() == anOperator) )
		{
			newCode->append( aCode->getArgs() );
		}
		else
		{
			newCode->append( aCode );
		}

		return newCode;
	}

	inline static BFCode newCodeFlat(Operator * anOperator,
			const BFCode & aCode1, const BFCode & aCode2)
	{
		if( anOperator->isWeakAssociative() )
		{
			BFCode newCode( anOperator );

			if( aCode1->getOperator() == anOperator )
			{
				newCode->append( aCode1->getArgs() );
			}
			else
			{
				newCode->append( aCode1 );
			}

			if( aCode2->getOperator() == anOperator )
			{
				newCode->append( aCode2->getArgs() );
			}
			else
			{
				newCode->append( aCode2 );
			}

			return newCode;
		}
		else
		{
			return( newCode(anOperator, aCode1, aCode2) );
		}
	}


	inline static BFCode xnewCodeFlat(Operator * anOperator,
			const BFCode & aCode1, const BFCode & aCode2)
	{
		if( aCode1.invalid() )
		{
			return( aCode2 );
		}
		else if( aCode2.invalid() )
		{
			return( aCode1 );
		}
		else
		{
			return( newCodeFlat(anOperator, aCode1, aCode2) );
		}
	}


	inline static BFCode newCodeFlat(Operator * anOperator,
			const BF & arg1, const BF & arg2)
	{
		if( arg1.is< AvmCode >() )
		{
			if( arg2.is< AvmCode >() )
			{
				return( newCodeFlat(anOperator, arg1.bfCode(), arg2.bfCode()) );
			}
			else
			{
				return( newCodeFlat(anOperator, arg1.bfCode(), arg2) );
			}
		}
		else if( arg2.is< AvmCode >() )
		{
			return( newCodeFlat(anOperator, arg1, arg2.bfCode()) );
		}
		else
		{
			return( newCode(anOperator, arg1, arg2) );
		}
	}

	inline static BFCode newCodeFlat(Operator * anOperator,
			const BFCode & aCode1, const BFCode & aCode2, const BFCode & aCode3)
	{
		if( anOperator->isWeakAssociative() )
		{
			BFCode newCode( anOperator );

			if( aCode1->getOperator() == anOperator )
			{
				newCode->append( aCode1->getArgs() );
			}
			else
			{
				newCode->append( aCode1 );
			}

			if( aCode2->getOperator() == anOperator )
			{
				newCode->append( aCode2->getArgs() );
			}
			else
			{
				newCode->append( aCode2 );
			}

			if( aCode3->getOperator() == anOperator )
			{
				newCode->append( aCode3->getArgs() );
			}
			else
			{
				newCode->append( aCode3 );
			}

			return newCode;
		}
		else
		{
			return( newCode(anOperator, aCode1, aCode2, aCode3) );
		}
	}


	inline static BFCode xnewCodeFlat(Operator * anOperator,
			const BFCode & aCode1, const BFCode & aCode2, const BFCode & aCode3)
	{
		if( aCode1.invalid() )
		{
			if( aCode2.invalid() )
			{
				return( aCode3 );
			}
			else if( aCode3.invalid() )
			{
				return( aCode2 );
			}
			else
			{
				return( newCodeFlat(anOperator, aCode2, aCode3) );
			}
		}
		else if( aCode2.invalid() )
		{
			if( aCode3.invalid() )
			{
				return( aCode1 );
			}
			else
			{
				return( newCodeFlat(anOperator, aCode1, aCode3) );
			}
		}
		else if( aCode3.invalid() )
		{
			return( newCodeFlat(anOperator, aCode1, aCode2) );
		}
		else
		{
			return( newCodeFlat(anOperator, aCode1, aCode2, aCode3) );
		}
	}


	inline static BFCode newCodeFlatMiddle(Operator * anOperator,
			const BFCode & aCode1, const BFCode & aCode2, const BFCode & aCode3)
	{
		if( anOperator->isWeakAssociative() &&
				(aCode2->getOperator() == anOperator) )
		{
			BFCode newCode( anOperator , aCode1 );

			newCode->append( aCode2->getArgs() );

			newCode->append( aCode3 );

			return newCode;
		}
		else
		{
			return( newCode(anOperator, aCode1, aCode2, aCode3) );
		}
	}


	inline static BFCode newCode(Operator * anOperator,
			const BF & arg1, const BF & arg2, const BF & arg3)
	{
		return( BFCode( new AvmCode(anOperator, arg1, arg2, arg3) ) );
	}

	inline static BFCode newCode(Operator * anOperator,
			const BF & arg1, const BF & arg2, const BF & arg3, const BF & arg4)
	{
		return( BFCode( new AvmCode(anOperator, arg1, arg2, arg3, arg4) ) );
	}

	inline static BFCode newCode(Operator * anOperator, const BF & arg1,
			const BF & arg2, const BF & arg3, const BF & arg4, const BF & arg5)
	{
		return( BFCode( new AvmCode(anOperator, arg1, arg2, arg3, arg4, arg5) ) );
	}


	inline static BFCode newCode(Operator * anOperator,
			const BFCodeList & listOfArg)
	{
		BFCode aCode( new AvmCode(anOperator) );
		aCode->append(listOfArg);

		return( aCode );
	}


	inline static BFCode newCode(Operator * anOperator,
			const BF & arg, const BFCodeList & listOfArg)
	{
		BFCode aCode( new AvmCode(anOperator, arg) );
		aCode->append(listOfArg);

		return( aCode );
	}


	inline static BFCode newCode(Operator * anOperator,
			const AvmCode::this_container_type & listOfArg)
	{
		BFCode aCode( new AvmCode(anOperator) );
		aCode->append(listOfArg);

		return( aCode );
	}

	inline static BFCode newCode(Operator * anOperator,
			const BF & arg, const AvmCode::this_container_type & listOfArg)
	{
		BFCode aCode( new AvmCode(anOperator, arg) );
		aCode->append(listOfArg);

		return( aCode );
	}


	inline static BFCode newCodeTail(Operator * anOperator,
			const AvmCode::this_container_type & listOfArg)
	{
		BFCode aCode( new AvmCode(anOperator) );
		aCode->appendTail(listOfArg);

		return( aCode );
	}


	/**
	 * METHODS
	 * ${ comment arg }
	 * ${ comment "string" }
	 */
	inline static BFCode newComment(const BF & arg)
	{
		return BFCode( new AvmCode(OperatorManager::OPERATOR_COMMENT, arg) );
	}

	inline static BFCode newComment(const std::string & comment)
	{
		return newComment( BF(new String(comment) ) );
	}


	/**
	 * METHODS
	 * flatten
	 */
	static BF flatten(BF aCode);

	static BFCode flattenCode(BFCode anAvmCode);


	/**
	 * METHODS
	 * contains subCode with a specific operator
	 */
	static bool contains(ExecutableForm * anExecutable,
			const BFCode & aCode, AVM_OPCODE anOpcode);

	static bool contains(ExecutableForm * anExecutable,
			const BFCode & aCode, AVM_OPCODE anOpcode1, AVM_OPCODE anOpcode2);

};

} /* namespace sep */
#endif /* AVMCODEFACTORY_H_ */

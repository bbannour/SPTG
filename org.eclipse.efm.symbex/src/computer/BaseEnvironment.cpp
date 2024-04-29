/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BaseEnvironment.h"

#include <collection/Bitset.h>

#include <computer/ExecutionEnvironment.h>
#include <computer/EvaluationEnvironment.h>
#include <computer/PathConditionProcessor.h>

#include <computer/primitive/AvmPrimitiveProcessor.h>

#include <fml/executable/ExecutableLib.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/BuiltinContainer.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionTypeChecker.h>

#include <fml/symbol/TableOfSymbol.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/LocalRuntime.h>
#include <fml/runtime/RuntimeLib.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/ClassTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/TypeAliasSpecifier.h>

#include <sew/Configuration.h>


namespace sep
{


/**
 * INDEX FOR NEW SYMBOLIC PARAMETER
 */
std::uint32_t BaseEnvironment::NEW_PARAM_OFFSET = 0;


/**
 * GETTER
 * Builder
 * Configuration
 * ExecutableSystem
 */
Builder & BaseEnvironment::getBuilder() const
{
	return( PRIMITIVE_PROCESSOR.getBuilder() );
}

Loader & BaseEnvironment::getLoader() const
{
	return( PRIMITIVE_PROCESSOR.getLoader() );
}

SymbexEngine & BaseEnvironment::getSymbexEngine() const
{
	return( PRIMITIVE_PROCESSOR.getSymbexEngine() );
}

Configuration & BaseEnvironment::getConfiguration() const
{
	return( PRIMITIVE_PROCESSOR.getConfiguration() );
}

ExecutableSystem & BaseEnvironment::getExecutableSystem() const
{
	return( PRIMITIVE_PROCESSOR.getConfiguration().getExecutableSystem() );
}



/**
 * Serialization
 */
void BaseEnvironment::toStream(OutStream & os) const
{
	os << TAB << "inEC : ";
	inEC->traceDefault(os << NEW_LTRIM_INDENT(os));

	os << END_INDENT << TAB << "inED : ";
	inED.toStream(os << NEW_LTRIM_INDENT(os));

	os << END_INDENT << TAB << "inFORM : " << inFORM.str() << EOL;
	os << TAB << "inCODE : " << inCODE.str() << EOL;

}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// SYMBOLIC PARAMETRE CREATION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

InstanceOfData * BaseEnvironment::create(const RuntimeID & aRID,
		const BaseTypeSpecifier & aTypeSpecifier, const InstanceOfData & lvalue)
{
	/*
	 * préfixage de l'UFI de la constante symbolique
	 * par le nom de l'instance conteneur
	 */
	std::ostringstream ossUfi;
	std::ostringstream ossId;

//AVM_IF_DEBUG_FLAG( LOADING )
//	ossUfi << aRID.getInstance()->getFullyQualifiedNameID()
//			<< lvalue.getAstFullyQualifiedNameID().substr(
//					aRID.refExecutable().getFullyQualifiedNameID().size());
//_AVM_ELSE_
	ossUfi << "param::"; // << NamedElement::NAME_ID_SEPARATOR << "newfresh::";
	if( getConfiguration().isNewfreshParameterNameBasedPID() )
	{
		ossUfi << aRID.strPid() << ":";
	}
//	else
//	{
//		ossUfi << aRID.getInstance()->getLocationID() << ":";
//	}
	ossUfi << lvalue.getLocationID(); // lvalue.getNameID();

	ossId << lvalue.getNameID();
//AVM_ENDIF_DEBUG_FLAG( LOADING )

	if( getConfiguration().isNewfreshParameterExperimentalHeightBasedUID() )
	{
		if( inEC != nullptr )
		{

//			const std::uint32_t heightNumber = 1 + inEC->getHeight();
//!@! On suppose qu'on a un state< start > et non state< initial > !
			const std::uint32_t heightNumber = inEC->getHeight();

//			ossUfi << getConfiguration().getNameIdSeparator() << "H_" << heightNumber;
//			ossId << getConfiguration().getNameIdSeparator()  << "H_" << heightNumber;
			ossUfi << getConfiguration().getNameIdSeparator() << heightNumber;
			ossId << getConfiguration().getNameIdSeparator()  << heightNumber;
		}
		else if( const_cast< InstanceOfData & >(lvalue).instanciationCountIncr() == 0 )
		{
			ossUfi << getConfiguration().getNameIdSeparator() << 0;
			ossId << getConfiguration().getNameIdSeparator()  << 0;
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BaseEnvironment::create with "
						"NewfreshParameterExperimentalHeightBasedUID enable :> "
						"Unexpected an instance << "
					<< str_header( lvalue )	<< " >> without an ExecutionContext "
						"for the required heightNumber >> !!!"
					<< SEND_EXIT;
		}
	}
	else
	{
		const std::uint32_t instNumber =
				const_cast< InstanceOfData & >(lvalue).instanciationCountIncr();

		ossUfi << getConfiguration().getNameIdSeparator() << instNumber;
		ossId  << getConfiguration().getNameIdSeparator() << instNumber;
	}

	InstanceOfData * theSymbolicParam = new InstanceOfData(
			IPointerVariableNature::POINTER_STANDARD_NATURE,
			aRID.getExecutable(), lvalue.getAstElement(),
			aTypeSpecifier, ossUfi.str(), 0,
			Modifier::PARAMETER_PUBLIC_FINAL_STATIC_MODIFIER );

	theSymbolicParam->setCreatorContainerRID( aRID );
	theSymbolicParam->setNameID( ossId.str() );

	return( theSymbolicParam );
}


BF BaseEnvironment::evalInitial(
		ExecutionData & anED, const RuntimeID & aRID,
		const InstanceOfData & lvalue, const BF & anInitialValue)
{
	if( anInitialValue.invalid() )
	{
		return( anInitialValue );
	}

	else if( anInitialValue.is< InstanceOfData >() )
	{
		if( anInitialValue.isTEQ(ExecutableLib::MACHINE_THIS) )
		{
			return( aRID );
		}
		if( anInitialValue.isTEQ(ExecutableLib::MACHINE_SELF) )
		{
			return( aRID.getComponentSelf() );
		}
		else if( anInitialValue.isTEQ(ExecutableLib::MACHINE_PARENT) )
		{
			return( aRID.getPRID() );
		}
	}

	else if( anInitialValue.is< InstanceOfMachine >() )
	{
		if( anInitialValue.isTEQ(ExecutableLib::MACHINE_ENVIRONMENT) )
		{
			return( RuntimeLib::RID_ENVIRONMENT );
		}
		else if( anInitialValue.isTEQ(ExecutableLib::MACHINE_NULL) )
		{
			return( RuntimeLib::RID_NIL );
		}
	}

	else if( anInitialValue.is< ArrayBF >() )
	{
		ArrayBF * anInitialBuiltinArray = anInitialValue.to_ptr< ArrayBF >();

		std::size_t aSize = anInitialBuiltinArray->size();
		for( std::size_t offset = 0 ; offset < aSize ; ++offset )
		{
			BF & valOffset = anInitialBuiltinArray->at(offset);

			valOffset = evalInitial(anED, aRID, lvalue, valOffset);
		}

		return( anInitialValue );
	}

	else if( anInitialValue.is< BuiltinArray >() )
	{
		return( anInitialValue );
	}

	else if( anInitialValue.is< BuiltinContainer >() )
	{
		BuiltinContainer * anInitialBuiltinContainer =
				anInitialValue.to_ptr< BuiltinContainer >();

		std::size_t aSize = anInitialBuiltinContainer->size();
		for( std::size_t offset = 0 ; offset < aSize ; ++offset )
		{
			BF valOffset = anInitialBuiltinContainer->at(offset);

			valOffset = evalInitial(anED, aRID, lvalue, valOffset);
		}

		return( anInitialValue );
	}

	return( anInitialValue );
}

BF BaseEnvironment::createInitial(ExecutionData & anED,
		const RuntimeID & aRID, const InstanceOfData & lvalue)
{
	BF theInitialValue = lvalue.getValue();

	if( lvalue.getModifier().hasNatureMacro() )
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( theInitialValue )
				<< "BaseEnvironment::createInitial:> "
					"Unexpected an instance macro << "
				<< lvalue.getFullyQualifiedNameID()
				<< " >> without initial value !!!"
				<< SEND_EXIT;

		return( theInitialValue );
	}
	else if( lvalue.getModifier().hasNatureReference() )
	{
		if( theInitialValue.is< InstanceOfData >() )
		{
			const InstanceOfData & theInitialInstance =
					theInitialValue.to< InstanceOfData >();

			if( theInitialInstance.getModifier().hasFeatureMutable() )
			{
				if( ExpressionTypeChecker::weaklyTyped(lvalue.getTypeSpecifier(),
						theInitialInstance.getTypeSpecifier()))
				{
					return( theInitialValue );
				}
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::createInitial:> "
							"Unexpected an instance << "
						<< str_header( lvalue )
						<< " >> with non mutable initial instance << "
						<< str_header( theInitialInstance ) << " >> !!!"
						<< SEND_EXIT;
			}
		}
		else if( theInitialValue.valid() )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BaseEnvironment::createInitial:> "
						"Unexpected an instance << "
					<< str_header( lvalue ) << " >> with initial value <<"
					<< str_indent( theInitialValue ) << " >> !!!"
					<< SEND_EXIT;
		}
		else
		{
			return( anED.saveParameter( create(aRID, lvalue) ) );
		}
	}

	else if( theInitialValue.is< InstanceOfData >() )
	{
		InstanceOfData & theInitialInstance =
				theInitialValue.to< InstanceOfData >();

		if( theInitialInstance.getModifier().
					hasModifierPublicFinalStaticParameter() )
		{
			if( ExpressionTypeChecker::weaklyTyped(lvalue.getTypeSpecifier(),
					theInitialInstance.getTypeSpecifier()))
			{
				return( theInitialValue );
			}
		}
		else if( theInitialInstance.hasValue() )
		{
			theInitialValue = theInitialInstance.getValue();
		}
		else if( theInitialInstance.getModifier().hasFeatureMutable() )
		{
			theInitialValue = getRvalue(anED, aRID, theInitialInstance);
			if( theInitialValue.invalid() )
			{
				theInitialValue = createInitial(anED, aRID, theInitialInstance);

				theInitialInstance.setValue(theInitialValue);
			}

			if( ExpressionTypeChecker::weaklyTyped(lvalue.getTypeSpecifier(),
					theInitialInstance.getTypeSpecifier()))
			{
				return( theInitialValue );
			}
		}
	}

	theInitialValue = evalInitial(anED, aRID, lvalue, theInitialValue);


	if( lvalue.hasTypeSpecifier() )
	{
		const BaseTypeSpecifier & aTypeSpecifier =
				lvalue.getTypeSpecifier().referedTypeSpecifier();

		if( aTypeSpecifier.isTypedArray() )
		{
			const ContainerTypeSpecifier & containerT =
					aTypeSpecifier.as< ContainerTypeSpecifier >();
			std::size_t sizeT = containerT.size();

			if( theInitialValue.valid() )
			{
				if( theInitialValue.is< BuiltinArray >() )
				{
					return( createInitial(anED, aRID, lvalue,
							theInitialValue.to_ptr< BuiltinArray >()) );
				}
				else
				{
					return( BF( new ArrayBF(containerT, theInitialValue) ));
				}
			}
			else
			{
				ArrayBF * arrayValue = new ArrayBF(aTypeSpecifier, sizeT);

				TableOfSymbol::iterator it = lvalue.getAttribute()->begin();
				for( std::size_t idx = 0 ; idx < sizeT ; ++idx , ++it )
				{
					arrayValue->set(idx, createInitial(anED, aRID, (*it)));
				}

				return( BF(arrayValue) );
			}
		}

		else if( aTypeSpecifier.hasTypeCollection() )
		{
			BuiltinContainer * containerValue = BuiltinContainer::create(
					aTypeSpecifier.as< ContainerTypeSpecifier >() );

			if( theInitialValue.valid() )
			{
				if( theInitialValue.is< BuiltinArray >() )
				{
					const BuiltinArray & theInitialBuiltinArray =
							theInitialValue.to< BuiltinArray >();

					containerValue->copy( theInitialBuiltinArray,
							std::min(containerValue->capacity(),
									theInitialBuiltinArray.size()) );
				}
				else
				{
					containerValue->add( theInitialValue );
				}
			}

			return( BF(containerValue) );
		}

		else if( aTypeSpecifier.isTypedClass() )
		{
			std::size_t sizeT = aTypeSpecifier.size();

			if( theInitialValue.valid() )
			{
				if( theInitialValue.is< BuiltinArray >() )
				{
					return( createInitial(anED, aRID, lvalue,
							theInitialValue.to_ptr< BuiltinArray >()) );
				}
				else
				{
					return( BF( new ArrayBF(
							aTypeSpecifier, sizeT, theInitialValue )));
				}
			}
			else
			{
				ArrayBF * arrayValue = new ArrayBF(aTypeSpecifier, sizeT);

				TableOfSymbol::iterator it = lvalue.getAttribute()->begin();
				for( std::size_t idx = 0 ; idx < sizeT ; ++idx , ++it )
				{
					arrayValue->set(idx, createInitial(anED, aRID, (*it)));
				}

				return( BF(arrayValue) );
			}
		}

		else //if( aTypeSpecifier.isTypedSimple() )
		{
			if( theInitialValue.valid() )
			{
				return( theInitialValue );
			}

//			else if( aTypeSpecifier.isTypedString() )
//			{
//				return( ExpressionConstructor::newString("") );
//			}
			else if( aTypeSpecifier.isTypedMachine() )
			{
				return( RuntimeLib::RID_NIL );
			}
			else if( aTypeSpecifier.isTypedChannel() )
			{
				return( ExecutableLib::CHANNEL_NIL );
			}
			else if( aTypeSpecifier.isTypedPort() )
			{
				return( ExecutableLib::PORT_NIL );
			}
			else if( aTypeSpecifier.isTypedBuffer() )
			{
				return( ExecutableLib::BUFFER_NIL );
			}
			else
			{
				return( anED.saveParameter( create(aRID, lvalue) ) );
			}
		}
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "BaseEnvironment::createInitial:> Unexpected an instance << "
				<< lvalue.getFullyQualifiedNameID()
				<< " >> without typeSpecifier !!!"
				<< SEND_EXIT;

		return( BF::REF_NULL );
	}
}



BF BaseEnvironment::createInitial(
		ExecutionData & anED, const RuntimeID & aRID,
		const InstanceOfData & lvalue, BuiltinArray * initialArray)
{
	std::size_t sizeT = lvalue.getTypeSpecifier().size();

	ArrayBF * bfValue = new ArrayBF(
			( initialArray->hasTypeSpecifier() ?
					initialArray->getTypeSpecifier() :
					lvalue.getTypeSpecifier() ), sizeT);

	if( ExpressionTypeChecker::isFinalSymbolicCompositeSymbol(initialArray) )
	{
		std::size_t idx = initialArray->size();

		if( idx <= sizeT )
		{
			bfValue->copy(initialArray, idx);

			for( ; idx < sizeT ; ++idx )
			{
				bfValue->set(idx, createInitial(anED, aRID,
						lvalue.getAttribute()->at(idx)));
			}
		}
		else
		{
			bfValue->copy(initialArray, sizeT);
		}
	}
	else //if( initialArray->is< ArrayBF >() )
	{
		ArrayBF * bfInitialArray = initialArray->to_ptr< ArrayBF >();

		std::size_t initSizeT = bfInitialArray->size();

		if( initSizeT > sizeT )
		{
			initSizeT = sizeT;
		}

		for( std::size_t idx = 0 ; idx < initSizeT ; ++idx )
		{
			if( ExpressionTypeChecker::isFinalSymbolicSymbol(
					bfInitialArray->at(idx)) )
			{
				bfValue->set(idx, bfInitialArray->at(idx));
			}
			else
			{
				bfValue->set(idx, createInitial(anED, aRID,
						lvalue.getAttribute()->at(idx)));
			}
		}

		for( std::size_t idx = initSizeT ; idx < sizeT ; ++idx )
		{
			bfValue->set(idx, createInitial(anED, aRID,
					lvalue.getAttribute()->at(idx)));
		}
	}

	return( BF(bfValue) );
}


BF BaseEnvironment::createNewFreshParam(const RuntimeID & aRID,
		const BaseTypeSpecifier & theTypeSpecifier,
		const InstanceOfData & lvalue, BFCollection & paramList)
{
	if( theTypeSpecifier.isnotNullref() )
	{
		const BaseTypeSpecifier & aTypeSpecifier =
				theTypeSpecifier.referedTypeSpecifier();

		if( aTypeSpecifier.isTypedArray() )
		{
			const ContainerTypeSpecifier & containerT =
					aTypeSpecifier.as< ContainerTypeSpecifier >();
			std::size_t sizeT = containerT.size();

			ArrayBF * arrayValue = new ArrayBF(containerT, sizeT);

			TableOfSymbol::iterator it = lvalue.getAttribute()->begin();
			for( std::size_t idx = 0 ; (idx < sizeT) ; ++idx , ++it )
			{
				arrayValue->set(idx, createNewFreshParam(aRID, (*it), paramList));
			}

			return( BF(arrayValue) );
		}

		//TODO
		else if( aTypeSpecifier.hasTypeCollection() )
		{
			BuiltinContainer * containerValue = BuiltinContainer::create(
					aTypeSpecifier.as< ContainerTypeSpecifier >());

			return( BF(containerValue) );
		}

		else if( aTypeSpecifier.isTypedClass() )
		{
			std::size_t sizeT =
					aTypeSpecifier.as< ClassTypeSpecifier >().size();

			ArrayBF * arrayValue = new ArrayBF(aTypeSpecifier, sizeT);

			TableOfSymbol::iterator it = lvalue.getAttribute()->begin();
			for( std::size_t idx = 0 ; idx < sizeT ; ++idx , ++it )
			{
				arrayValue->set(idx,
						createNewFreshParam(aRID, (*it), paramList));
			}

			return( BF(arrayValue) );
		}

		else //if( aTypeSpecifier.isTypedSimple() )
		{
//			if( aTypeSpecifier.isTypedString() )
//			{
//				return( ExpressionConstructor::newString("") );
//			}
//			else
//				if( aTypeSpecifier.isTypedMachine() )
//			{
//				return( RuntimeLib::RID_NIL );
//			}
//			else
			{
				BF aNewFreshParam( create(aRID, theTypeSpecifier, lvalue) );

				paramList.append( aNewFreshParam );

				return( aNewFreshParam );
			}
		}
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "getInitialValue:> Unexpected an instance << "
				<< lvalue.getFullyQualifiedNameID()
				<< " >> without typeSpecifier !!!"
				<< SEND_EXIT;

		return( BF::REF_NULL );
	}

	return( BF::REF_NULL );
}


void BaseEnvironment::createNewFreshParam(
		const RuntimeID & aPRID, const InstanceOfPort & port,
		BFCollection & newfreshList, BFCollection & paramList)
{
	for( const auto & param : port.getParameters() )
	{
		if( param.is< BaseTypeSpecifier >() )
		{
//			newfreshList.append(
//					createNewFreshParam(aPRID,
//							param.to_ptr< BaseTypeSpecifier >(), aVar, paramList) );
		}
		else if( param.is< InstanceOfData >() )
		{
			const InstanceOfData & aVar = param.to< InstanceOfData >();

			newfreshList.append(
					createNewFreshParam(aPRID,
							aVar.getTypeSpecifier(), aVar, paramList) );
		}

	}
}


Symbol BaseEnvironment::create(
		const RuntimeID & aRID, const std::string & paramID,
		const TypeSpecifier & aTypeSpecifier, const BF & aValue)
{
	std::ostringstream ossUfi;

	if( getConfiguration().isNewfreshParameterNameBasedPID() )
	{
		ossUfi << aRID.strPid() << ":" << paramID
				<< getConfiguration().getNameIdSeparator() << ++NEW_PARAM_OFFSET;
	}
	else
	{
		ossUfi << aRID.getInstance()->getFullyQualifiedNameID()
				<< "." << paramID
				<< getConfiguration().getNameIdSeparator() << ++NEW_PARAM_OFFSET;
	}

	Symbol theSymbolicParam( new InstanceOfData(
			IPointerVariableNature::POINTER_STANDARD_NATURE,
			aRID.getExecutable(), Variable::nullref(), aTypeSpecifier,
			ossUfi.str(), 0, Modifier::PARAMETER_PUBLIC_FINAL_STATIC_MODIFIER) );

	theSymbolicParam.setCreatorContainerRID( aRID );
	theSymbolicParam.setNameID( ossUfi.str() );
	theSymbolicParam.setValue( aValue );

	theSymbolicParam.setInstanciationCount(NEW_PARAM_OFFSET);

	return( Symbol( theSymbolicParam ) );
}



Symbol BaseEnvironment::create4ArrayAccess(ExecutionData & apED,
		const RuntimeID & aRID, const BF & arrayValue,
		const InstanceOfData & lvalueOfIndex)
{
	std::ostringstream ossUfi;
	std::ostringstream ossId;

	ossId << lvalueOfIndex.getContainer()->getVariables().rawAt(
			lvalueOfIndex.getOffset() )->getNameID()
		<< getConfiguration().getNameIdSeparator() << ++NEW_PARAM_OFFSET;

	if( getConfiguration().isNewfreshParameterNameBasedPID() )
	{
		ossUfi << aRID.strPid() << ":" << ossId.str();
	}
	else
	{
		ossUfi << aRID.getInstance()->getFullyQualifiedNameID() << "."
				<< ossId.str();
	}
// lvalueOfIndex.incrInstanciationCount();
//	ossId << ossUfi.str();

	Symbol newParam;
	TableOfSymbol aRelativeDataPath;

	TableOfSymbol::iterator itEnd = lvalueOfIndex.getDataPath()->end();
	TableOfSymbol::iterator it = lvalueOfIndex.getDataPath()->begin();

	switch( lvalueOfIndex.getPointerNature() )
	{
		case IPointerVariableNature::POINTER_UFI_OFFSET_NATURE:
		{
			for( ; it != itEnd ; ++it )
			{
				ossUfi << "[" << (*it).getOffset() << "]";
				ossId  << "[" << (*it).getOffset() << "]";
			}

			newParam = new InstanceOfData(
					lvalueOfIndex.getPointerNature(), aRID.getExecutable(),
					lvalueOfIndex, *(lvalueOfIndex.getDataPath()) );

			break;
		}

		case IPointerVariableNature::POINTER_UFI_RUNTIME_NATURE:
		{
			// NO +1 for << this >> which is the root of the path
			std::size_t pathLength = lvalueOfIndex.getDataPath()->size();
			std::size_t * theOffsetPath = lvalueOfIndex.getOffsetPath();

			for( std::size_t k = 1 ; k < pathLength ; ++k )
			{
				ossUfi << "[" << theOffsetPath[k] << "]";
				ossId  << "[" << theOffsetPath[k] << "]";
			}

			newParam = new InstanceOfData(
					lvalueOfIndex.getPointerNature(), aRID.getExecutable(),
					lvalueOfIndex, *(lvalueOfIndex.getDataPath()) );

			break;
		}
		case IPointerVariableNature::POINTER_UFI_MIXED_NATURE:
		{
			Symbol symbolicIndex;
			for( ; it != itEnd ; ++it )
			{
				switch( (*it).getPointerNature() )
				{
					case IPointerVariableNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
					{
						symbolicIndex = new InstanceOfData(
								IPointerVariableNature::
										POINTER_FIELD_ARRAY_OFFSET_NATURE,
								(*it).getContainer(), (*it).getAstElement(),
								(*it).getTypeSpecifier(), (*it).getOffset() );

						ossUfi << "." << symbolicIndex.str();
						ossId  << "." << symbolicIndex.str();

						break;
					}
					case IPointerVariableNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
					{
						symbolicIndex = new InstanceOfData(
								IPointerVariableNature::
										POINTER_FIELD_ARRAY_OFFSET_NATURE,
								(*it).getContainer(), (*it).getAstElement(),
								(*it).getTypeSpecifier(), (*it).getOffset() );

						ossUfi << "[" << symbolicIndex.str() << "]";
						ossId  << "[" << symbolicIndex.str() << "]";

						break;
					}
					case IPointerVariableNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
					{
						EvaluationEnvironment eENV(*this, apED, aRID);
						if( eENV.eval((*it).getValue()) )
						{
							apED = eENV.outED;
						}
						else
						{
							AVM_OS_FATAL_ERROR_EXIT
									<< "Failed to eval ARRAY index << "
									<< (*it).strValue() << " >> in variable << "
									<< lvalueOfIndex.str()
									<< " >> for initializing a VVT !!!"
									<< SEND_EXIT;

							return( Symbol::REF_NULL );
						}

						if( eENV.outVAL.isNumeric() )
						{
							symbolicIndex = new InstanceOfData(
									IPointerVariableNature::
											POINTER_FIELD_ARRAY_OFFSET_NATURE,
									(*it).getContainer(), (*it).getAstElement(),
									(*it).getTypeSpecifier(),
									eENV.outVAL.toInteger() );
						}
						else
						{
							symbolicIndex = new InstanceOfData(
									IPointerVariableNature::
											POINTER_FIELD_ARRAY_INDEX_NATURE,
									(*it).getContainer(), (*it).getAstElement(),
									(*it).getTypeSpecifier(), 0 );
							symbolicIndex.setValue( eENV.outVAL );
						}
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , DATA )
	AVM_OS_TRACE << "indexArray:> " << eENV.outVAL.toString() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , DATA )

						ossUfi << "[" << eENV.outVAL.str() << "]";
						ossId  << "[" << eENV.outVAL.str() << "]";

						break;
					}
					default:
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "SymbolicParameterFactory::create4ArrayAccess:> "
									"Unexpected POINTER NATURE "
									"for the instance of data :>\n"
								<< (*it).toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

						return( Symbol::REF_NULL );
					}
				}
				aRelativeDataPath.append(symbolicIndex);
			}

			newParam = new InstanceOfData(lvalueOfIndex.getPointerNature(),
					aRID.getExecutable(), lvalueOfIndex, aRelativeDataPath);

			break;
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "SymbolicParameterFactory::create4ArrayAccess:> "
						"Unexpected POINTER NATURE "
						"for the instance of index :>\n"
					<< lvalueOfIndex.toString( AVM_TAB1_INDENT )
					<< SEND_EXIT;

			return( Symbol::REF_NULL );
		}
	}

	newParam.setValue( arrayValue );
	newParam.updateFullyQualifiedNameID( ossUfi.str() , ossId.str() );


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , DATA )
	AVM_OS_TRACE << newParam.toString() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , DATA )

	return( newParam );

}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// the DATA ACCESS statement
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/*
 *******************************************************************************
 * GETTER
 * Assigned Flags
 *******************************************************************************
 */

bool BaseEnvironment::isAssigned(const ExecutionData & apED,
		const RuntimeID & aRID, const InstanceOfData & lvalue)
{
	if( lvalue.hasRuntimeContainerRID() )
	{
		return( apED.isAssigned(
				lvalue.getRuntimeContainerRID(), lvalue.getOffset()) );
	}
	else
	{
		RuntimeID aDataRID;

		if( getRuntimeForm(apED, aRID,
				const_cast< const InstanceOfData & >(lvalue), aDataRID) )
		{
			return( apED.isAssigned(aDataRID, lvalue.getOffset()) );
		}
	}

	return( false );
}


/*
 *******************************************************************************
 * GETTER
 * runtime instance
 *******************************************************************************
 */
bool BaseEnvironment::getRuntimeForm(
		const ExecutionData & apED, const RuntimeID & aRID,
		const InstanceOfData & lvalue, RuntimeID & aDataRID)
{
	aDataRID = aRID;

//	if( lvalue.hasRuntimeContainerRID() )
//	{
//		aDataRID = lvalue.getRuntimeContainerRID();
//
//		return( true );
//	}
//	else
	if( lvalue.isAlias() )
	{
		if( lvalue.hasAliasTarget() &&
				lvalue.getAliasTarget()->hasRuntimeContainerRID() )
		{
			InstanceOfData & wrlvalue = const_cast< InstanceOfData & >(lvalue);

			aDataRID = wrlvalue.getAliasTarget()->getRuntimeContainerRID();
			wrlvalue.setRuntimeContainerRID( aDataRID );

			return( true );
		}

		ArrayOfInstanceOfMachine::iterator it =
				lvalue.getMachinePath()->begin();

		// SEARCH of the RUNTIME FORM container
		// where this INSTANCE of variable was declared
		// SEARCH of the LCA(RID) of the current RID an the ALIAS container
		while( aDataRID.valid()
				&& (aDataRID.getExecutable() != (*it)->getContainer()) )
		{
			aDataRID = aDataRID.getPRID();
		}

		if( aDataRID.valid() )
		{
			// Use of Alias PATH to find the INSTANCE of variable
			ArrayOfInstanceOfMachine::iterator itEnd =
					lvalue.getMachinePath()->end();
			for( ; it != itEnd ; ++it )
			{
				aDataRID = apED.getRuntimeFormChild(aDataRID, (*it));
			}

//			AVM_OS_ASSERT_FATAL_ERROR_EXIT( aDataRID.getVariable(
//				lvalue.getOffset() )->isAstElement( lvalue.getAstElement() ) )
//					<< "Assign error " << aDataRID.getExecutable()
//						->getData(lvalue.getOffset())->getFullyQualifiedNameID()
//					<< " != " << lvalue.getFullyQualifiedNameID() << " !!!"
//					<< SEND_EXIT;
//
//AVM_IF_DEBUG_FLAG( DATA )
//	AVM_OS_TRACE << INCR_INDENT_TAB << "begin BaseEnvironment::getRvalue\n";
//	lvalue.toStream(AVM_OS_TRACE);
//	apED.getRuntime(aDataRID).toStream(AVM_OS_TRACE);
//
//	rvalue->toStream(AVM_OS_TRACE);
//	AVM_OS_TRACE << TAB_DECR_INDENT << "end BaseEnvironment::getRvalue\n";
//AVM_ENDIF_DEBUG_FLAG( DATA )

			return( true );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Access error : Unfound Runtime Data Container for << "
					<< lvalue.getFullyQualifiedNameID() << " >> !!!"
					<< SEND_EXIT;
		}
	}
	else
	{
		////////////////////////////////////////////////////////////////////////
		// NORMAL IMPLEMENTATION
		////////////////////////////////////////////////////////////////////////

		// SEARCH of the RUNTIME FORM container
		// where this INSTANCE of variable was declared
		while( aDataRID.valid() &&
				(aDataRID.getExecutable() != lvalue.getContainer()) )
		{
			aDataRID = aDataRID.getPRID();
		}

		if( aDataRID.valid() )
		{
//			AVM_OS_ASSERT_FATAL_ERROR_EXIT( aDataRID.getVariable(
//				lvalue.getOffset() )->isAstElement( lvalue.getAstElement() ) )
//					<< "Assign error "
//					<< aDataRID.getVariable(
//							lvalue.getOffset() )->getFullyQualifiedNameID()
//					<< " != " << lvalue.getFullyQualifiedNameID() << " !!!"
//					<< SEND_EXIT;
//
//AVM_IF_DEBUG_FLAG( DATA )
//	AVM_OS_TRACE << INCR_INDENT_TAB << "begin BaseEnvironment::getRvalue\n";
//	lvalue.toStream(AVM_OS_TRACE);
//	apED.getRuntime(aDataRID).toStream(AVM_OS_TRACE);
//
//	rvalue->toStream(AVM_OS_TRACE);
//	AVM_OS_TRACE << TAB_DECR_INDENT << "end BaseEnvironment::getRvalue\n";
//AVM_ENDIF_DEBUG_FLAG( DATA )

			return( true );
		}
//		else
//		{
//			AVM_OS_FATAL_ERROR_EXIT
//					<< "Access error : Unfound Runtime Data Container for :> "
//					<< aRID.str() << " |=> \n"
//					<< str_header( lvalue )
//					<< SEND_EXIT;
//		}
	}

	return( false );
}


bool BaseEnvironment::getRuntimeForm(const ExecutionData & apED,
		const InstanceOfData & lvalue, LocalRuntime & aLocalRuntime)
{
	if( apED.hasLocalRuntimeStack() )
	{
		StackOfLocalRuntime::
		reverse_iterator it = apED.getLocalRuntimes()->rbegin();
		StackOfLocalRuntime::
		reverse_iterator itEnd = apED.getLocalRuntimes()->rend();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).getProgram() == lvalue.getContainer() )
			{
				aLocalRuntime = (*it) ;

				break;
			}
		}

		if( aLocalRuntime.valid() )
		{
//			AVM_OS_ASSERT_FATAL_ERROR_EXIT( aLocalRuntime.getProgram()->getData(
//				lvalue.getOffset())->isAstElement( lvalue.getAstElement() ) )
//					<< "Assign error "
//					<< aLocalRuntime.getProgram()->getData(
//							lvalue.getOffset() )->getFullyQualifiedNameID()
//					<< " != " + lvalue.getFullyQualifiedNameID() << " !!!"
//					<< SEND_EXIT;

			return( true );
		}
	}

	return( false );
}


/**
 * Generate numeric offset for array access using symbolic expression
 */
std::size_t BaseEnvironment::genNumericOffset(
		ExecutionData & apED, const RuntimeID & aRID,
		const Symbol & lvSymbolicOffset, const BF & rvEvaluatedOffset,
		std::size_t offsetMin, std::size_t offsetMax)
{
	std::size_t offset = AVM_NUMERIC_MAX_SIZE_T;

	BF offsetExpr;

	Bitset unusedOffsetBitset( offsetMax + 1 , true );

	std::size_t idx = offsetMin;

	if( rvEvaluatedOffset.is< InstanceOfData >() )
	{
		offsetExpr = getRvalue( apED, apED.getParametersRID(),
				rvEvaluatedOffset.to< InstanceOfData >() );

		if( offsetExpr.isUInteger() &&
			((offset = offsetExpr.toInteger()) <= offsetMax) )
		{
//			AVM_OS_INFO << "BaseEnvironment::genNumericOffset:> "
//						"TRY PREVIOUS NUMERIC ARRAY INDEX in [ "
//					<< offsetMin << " , " << offsetMax
//					<< " ]\n for the expression: "
//					<< lvSymbolicOffset.strValue() << " |=> "
//					<< no_indent( rvEvaluatedOffset ) << " |-> "
//					<< offsetExpr.str() << "\n with constraint:> \n"
//					<< apED.getPathCondition().wrapStr() << " !!!"
//					<< std::endl;

			if( PathConditionProcessor::addPathCondition(apED,
				ExpressionConstructor::eqExpr(rvEvaluatedOffset, offsetExpr)) )
			{
				// forced to used << previous offset >>
				idx = AVM_NUMERIC_MAX_SIZE_T;

//				AVM_OS_INFO << "BaseEnvironment::genNumericOffset:> "
//							"USED OLD NUMERIC ARRAY INDEX in [ "
//						<< offsetMin << " , " << offsetMax
//						<< " ]\n for the expression: "
//						<< lvSymbolicOffset.strValue() << " |=> "
//						<< no_indent( rvEvaluatedOffset ) << " |-> "
//						<< offset << "\n with constraint:> \n"
//						<< apED.getPathCondition().wrapStr() << " !!!"
//						<< std::endl << std::endl;
			}
		}
	}


	for( ; idx <= offsetMax ; ++idx )
	{
		offset = RANDOM::gen_uinteger(offsetMin, offsetMax);

		if( unusedOffsetBitset[ offset ] )
		{
			unusedOffsetBitset[ offset ] = false;

			offsetExpr = ExpressionConstructor::newInteger(offset);

			if( PathConditionProcessor::addPathCondition(apED,
				ExpressionConstructor::eqExpr(rvEvaluatedOffset, offsetExpr)) )
			{
				// forced to used this << random offset >>
				idx = AVM_NUMERIC_MAX_SIZE_T;

				break;
			}
		}
	}

	if( idx != AVM_NUMERIC_MAX_SIZE_T )
	{
		for( offset = offsetMin ; offset <= offsetMax ; ++offset )
		{
			if( unusedOffsetBitset[ offset ] )
			{
				offsetExpr = ExpressionConstructor::newInteger(offset);

				if( PathConditionProcessor::addPathCondition(
						apED, ExpressionConstructor::eqExpr(
								rvEvaluatedOffset, offsetExpr)) )
				{
//					AVM_OS_INFO << "BaseEnvironment::genNumericOffset:> "
//								"Found NUMERIC<RANDOM> ARRAY INDEX in [ "
//							<< offsetMin << " , " << offsetMax
//							<< " ]\n for the expression: "
//							<< lvSymbolicOffset.strValue() << " |=> "
//							<< no_indent( rvEvaluatedOffset ) << " |-> "
//							<< offset << "\n with constraint:> \n"
//							<< apED.getPathCondition().wrapStr() << " !!!"
//							<< std::endl;

					break;
				}
			}
		}
	}

	if( offset <= offsetMax )
	{
		if( lvSymbolicOffset.getValue().is< InstanceOfData >() )
		{
			const InstanceOfData * lvIndex =
					lvSymbolicOffset.getValue().to_ptr< InstanceOfData >();

			if( lvIndex->getModifier().hasFeatureMutable() )
			{
				if( lvIndex->getModifier().hasNatureReference() )
				{
					lvIndex = getRvalue(apED, aRID, (* lvIndex)).
							to_ptr< InstanceOfData >();
				}

				if( lvIndex->getModifier().anyNatureReferenceMacro() )
				{
					setRvalue(apED, aRID, (* lvIndex), offsetExpr);
				}
			}

			if( rvEvaluatedOffset.is< InstanceOfData >() )
			{
				lvIndex = rvEvaluatedOffset.to_ptr< InstanceOfData >();
				if( not lvIndex->hasValue() )
				{
					setRvalue(apED,
							apED.getParametersRID(), (* lvIndex), offsetExpr);

//					AVM_OS_INFO << "BaseEnvironment::genNumericOffset:> "
//								"SAVE NUMERIC<RANDOM> ARRAY INDEX in [ "
//							<< offsetMin << " , " << offsetMax
//							<< " ]\n for the expression: "
//							<< lvSymbolicOffset.strValue() << " |=> "
//							<< no_indent( rvEvaluatedOffset ) << " |-> "
//							<< offset << "\n with constraint:> \n"
//							<< apED.getPathCondition().wrapStr() << " !!!"
//							<< std::endl << std::endl;
				}
			}
		}

		return( offset );
	}


//	apED.mwsetAEES( AEES_SYMBOLIC_EXECUTION_LIMITATION );

	AVM_OS_FATAL_ERROR_EXIT
			<< "BaseEnvironment::genNumericOffset:> "
				"Unfound NUMERIC<RANDOM> ARRAY INDEX in [ " << offsetMin
			<< " , " << offsetMax << " ]\n for the expression: "
			<< lvSymbolicOffset.strValue() << " |=> "
			<< no_indent( rvEvaluatedOffset ) << "\n with constraint:> \n"
			<< apED.getPathCondition().wrapStr() << " !!!"
			<< SEND_EXIT;

	return( AVM_NUMERIC_MAX_SIZE_T );
}


/*
 *******************************************************************************
 * GETTER
 * rvalue for an lvalue
 *******************************************************************************
 */
BF & BaseEnvironment::getRvalue(
		ExecutionData & apED, const RuntimeID & aRID,
		const InstanceOfData & lvUFI, BF & rvalue, const Symbol & offsetValue)
{
	switch( offsetValue.getPointerNature() )
	{
		case IPointerVariableNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
		case IPointerVariableNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
		case IPointerVariableNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE:
		case IPointerVariableNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE:
		{
			return( rvalue.at( offsetValue.getOffset() ) );
		}
		case IPointerVariableNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
		{
			EvaluationEnvironment eENV(*this, apED, aRID);
			if( eENV.evalOffset(offsetValue.getValue()) )
			{
				apED = eENV.outED;
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Failed to eval ARRAY index << "
						<< offsetValue.strValue() << " >> in UFI << "
						<< lvUFI.str() << " >> for reading in VVT !!!"
						<< SEND_EXIT;

				return( BF::REF_NULL );
			}


			if( eENV.outVAL.isNumeric() )
			{
				AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( eENV.outVAL.toInteger(),
					static_cast< avm_integer_t >(rvalue.size()) )
						<< "Failed to read in VVT with index << "
						<< offsetValue.strValue() << " >> using UFI << "
						<< lvUFI.str() << " >> !!!"
						<< SEND_EXIT;

				return( rvalue.at( eENV.outVAL.toInteger() ) );
			}
			else if( rvalue.size() > 0 )
			{
				std::size_t offset = genNumericOffset( apED, aRID,
						offsetValue, eENV.outVAL, 0, (rvalue.size() - 1) );

				if( offset != AVM_NUMERIC_MAX_SIZE_T )
				{
					return( rvalue.at( offset ) );
				}
				else
				{
					return( BF::REF_NULL );
				}
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::getRvalue:> "
							"Unexpected variable << " << lvUFI.str()
						<< " >> with empty rvalue << " << rvalue.str()
						<< " >> for the instance of data :>\n"
						<< offsetValue.toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				return( BF::REF_NULL );
			}
		}
		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BaseEnvironment::getRvalue:> "
						"Unexpected POINTER NATURE in UFI << "
					<< lvUFI.str() << " >> for the instance of data :>\n"
					<< offsetValue.toString( AVM_TAB1_INDENT )
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}
	}
}


BF & BaseEnvironment::getRvalue(ExecutionData & apED,
		const RuntimeID & aRID, const InstanceOfData & lvalue)
{
	TableOfData * aDataTable = nullptr;

	if( lvalue.hasRuntimeContainerRID() )
	{
		aDataTable = apED.getRuntime(
				lvalue.getRuntimeContainerRID()).getDataTable();
	}
	else
	{
		RuntimeID aDataRID;
		if( getRuntimeForm(apED, aRID, lvalue, aDataRID) )
		{
			aDataTable = apED.getRuntime(aDataRID).getDataTable();
		}
		else
		{
			LocalRuntime aLocalRuntime;
			if( getRuntimeForm(apED, lvalue, aLocalRuntime) )
			{
				aDataTable = &( aLocalRuntime.getDataTable() );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::getRvalue:> Failed to found "
							"data table for the instance of data:\n\t"
						<< str_header( lvalue )
						<< "\nin the runtime context: " << str_header( aRID )
						<< SEND_EXIT;

				return( BF::REF_NULL );
			}
		}
	}

	switch( lvalue.getPointerNature() )
	{
		case IPointerVariableNature::POINTER_STANDARD_NATURE:
		case IPointerVariableNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE:
		case IPointerVariableNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE:
		{
			return( aDataTable->at( lvalue.getOffset() ) );
		}
		case IPointerVariableNature::POINTER_UFI_OFFSET_NATURE:
		case IPointerVariableNature::POINTER_UFI_RUNTIME_NATURE:
		{
			BF rvalue = aDataTable->at( lvalue.getOffset() );

			// NO +1 for << this >> which is the root of the path
			std::size_t pathLength = lvalue.getDataPath()->size();
			std::size_t * theOffsetPath = lvalue.getOffsetPath();

			for( std::size_t k = 1 ; k < pathLength ; ++k )
			{
				if( rvalue.is< BuiltinCollection >() )
				{
					rvalue.moveAt( theOffsetPath[k] );
				}
				else
				{
					BF * value = new BF( create4ArrayAccess(
							apED, aRID, rvalue, lvalue) );

					return( *value );
				}
			}

			if( rvalue.is< BuiltinCollection >() )
			{
				return( rvalue.at( theOffsetPath[pathLength] ) );
			}
			else
			{
				BF * value = new BF( create4ArrayAccess(
						apED, aRID, rvalue, lvalue) );

				return( *value );
			}
		}
		case IPointerVariableNature::POINTER_UFI_MIXED_NATURE:
		{
			BF rvalue = aDataTable->at( lvalue.getOffset() );

			TableOfSymbol::iterator it = lvalue.getDataPath()->begin();
			TableOfSymbol::iterator itEnd = lvalue.getDataPath()->pred_end();

			bool isSymbolicAccess = false;

			for( ; it != itEnd ; ++it )
			{
				if( rvalue.is< BuiltinCollection >() )
				{
					rvalue = getRvalue(apED, aRID, lvalue, rvalue, (*it));
				}
				else
				{
					isSymbolicAccess = true;

					break;
				}
			}

			if( rvalue.is< BuiltinCollection >() )
			{
				return( getRvalue(apED, aRID, lvalue, rvalue, (*it)) );
			}
			else
			{
				isSymbolicAccess = true;
			}

			if( isSymbolicAccess )
			{
				BF * value = new BF( create4ArrayAccess(apED, aRID,
						aDataTable->at( lvalue.getOffset() ),
						lvalue) );

				return( *value );
			}

			break;
		}
		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BaseEnvironment::getRvalue:> Unexpected "
						"POINTER NATURE for the instance of data:\n\t"
					<< str_header( lvalue )
					<< "\nin the runtime context: " << str_header( aRID )
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}
	}

	return( BF::REF_NULL );
}


/*
 * GETTER
 * writable rvalue for an lvalue
 */
BF & BaseEnvironment::getWvalue(
		ExecutionData & apED, const RuntimeID & aRID,
		ArrayBF * rvArray, const Symbol & lvalue)
{
	switch( lvalue.getPointerNature() )
	{
		case IPointerVariableNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
		case IPointerVariableNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
		case IPointerVariableNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE:
		case IPointerVariableNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE:
		{
			return( rvArray->getWritable( lvalue.getOffset() ));
		}
		case IPointerVariableNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
		{
			EvaluationEnvironment eENV(*this, apED, aRID);
			if( eENV.evalOffset(lvalue.getValue()) )
			{
				apED = eENV.outED;
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Failed to eval ARRAY index << "
						<< lvalue.strValue() << " >> in variable << "
						<< lvalue.str() << " >> for reading in VVT !!!"
						<< SEND_EXIT;

				return( BF::REF_NULL );
			}

			if( eENV.outVAL.isNumeric() )
			{
				AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( eENV.outVAL.toInteger(),
					static_cast< avm_integer_t >(rvArray->size()) )
						<< "Failed to access to an ARRAY with index << "
						<< lvalue.strValue() << " >> for reading in VVT !!!"
						<< SEND_EXIT;

				return( rvArray->getWritable( eENV.outVAL.toInteger() ));
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::getWvalue:> "
							"unexpected NON-INTEGER ARRAY OFFSET << "
						<< eENV.outVAL.str() << " >> in instance FQN-ID :>\n"
						<< lvalue.toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				return( BF::REF_NULL );
			}
		}
		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BaseEnvironment::getWvalue:> Unexpected "
						"POINTER NATURE for the instance of data :>\n"
					<< lvalue.toString( AVM_TAB1_INDENT )
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}
	}
}


BF & BaseEnvironment::getWvalue(
		ExecutionData & apED, const RuntimeID & aRID,
		BuiltinContainer * rvArray, const Symbol & lvalue)
{
	switch( lvalue.getPointerNature() )
	{
		case IPointerVariableNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
		case IPointerVariableNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
		case IPointerVariableNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE:
		case IPointerVariableNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE:
		{
			return( rvArray->getWritable( lvalue.getOffset() ));
		}
		case IPointerVariableNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
		{
			EvaluationEnvironment eENV(*this, apED, aRID);
			if( eENV.evalOffset(lvalue.getValue()) )
			{
				apED = eENV.outED;
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Failed to eval ARRAY index << "
						<< lvalue.strValue() << " >> in variable << "
						<< lvalue.str() << " >> for reading in VVT !!!"
						<< SEND_EXIT;

				return( BF::REF_NULL );
			}

			if( eENV.outVAL.isNumeric() )
			{
				AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( eENV.outVAL.toInteger(),
					static_cast< avm_integer_t >(rvArray->size()) )
						<< "Failed to access to an ARRAY with index << "
						<< lvalue.strValue() << " >> for reading in VVT !!!"
						<< SEND_EXIT;

				return( rvArray->getWritable( eENV.outVAL.toInteger() ) );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::getWvalue:> "
							"unexpected NON-INTEGER ARRAY OFFSET << "
						<< eENV.outVAL.str() << " >> in instance FQN-ID :>\n"
						<< lvalue.toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

				return( BF::REF_NULL );
			}
		}
		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BaseEnvironment::getWvalue:> Unexpected "
						"POINTER NATURE for the instance of data :>\n"
					<< lvalue.toString( AVM_TAB1_INDENT )
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}
	}
}



BF & BaseEnvironment::getWvalue(ExecutionData & apED,
		const RuntimeID & aRID, const InstanceOfData & lvalue)
{
	TableOfData * aDataTable = nullptr;

	if( lvalue.hasRuntimeContainerRID() )
	{
		aDataTable = apED.getWritableRuntime(
				lvalue.getRuntimeContainerRID() ).getWritableDataTable();
	}
	else
	{
		RuntimeID aDataRID;
		if( getRuntimeForm(apED, aRID, lvalue, aDataRID) )
		{
			aDataTable = apED.getWritableRuntime(
					aDataRID ).getWritableDataTable();
		}
		else
		{
			LocalRuntime aLocalRuntime;
			if( getRuntimeForm(apED, lvalue, aLocalRuntime) )
			{
				apED.makeModifiableLocalRuntime( aLocalRuntime );

				aDataTable = &( aLocalRuntime.getDataTable() );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::getWvalue:> Failed to found "
							"data table for the instance of data :>\n"
						<< str_header( lvalue )
						<< SEND_EXIT;

				return( BF::REF_NULL );
			}
		}
	}

	switch( lvalue.getPointerNature() )
	{
		case IPointerVariableNature::POINTER_STANDARD_NATURE:
		case IPointerVariableNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE:
		case IPointerVariableNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE:
		{
			return( aDataTable->getWritable( lvalue.getOffset() ) );
		}
		case IPointerVariableNature::POINTER_UFI_OFFSET_NATURE:
		case IPointerVariableNature::POINTER_UFI_RUNTIME_NATURE:
		{
			BF rvalue = aDataTable->getWritable( lvalue.getOffset() );

			// NO +1 for << this >> which is the root of the path
			std::size_t pathLength = lvalue.getDataPath()->size();
			std::size_t * theOffsetPath = lvalue.getOffsetPath();

			for( std::size_t k = 1 ; k < pathLength ; ++k )
			{
				if( rvalue.is< BuiltinCollection >() )
				{
					rvalue.moveAtWritable( theOffsetPath[k] );
				}
				else
				{
					break;
				}
			}

			if( rvalue.is< BuiltinCollection >() )
			{
				return( rvalue.getWritable( theOffsetPath[pathLength] ) );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::getWvalue:> Unexpected "
							"rvalue container for the instance of data:\n\t"
						<< str_header( lvalue )
						<< "\nin the runtime context: " << str_header( aRID )
						<< SEND_EXIT;

				return( BF::REF_NULL );
			}
		}
		case IPointerVariableNature::POINTER_UFI_MIXED_NATURE:
		{
			BF rvalue = aDataTable->getWritable( lvalue.getOffset() );

			TableOfSymbol::iterator it = lvalue.getDataPath()->begin();
			TableOfSymbol::iterator itEnd = lvalue.getDataPath()->pred_end();

			for( ; it != itEnd ; ++it )
			{
				if( rvalue.is< ArrayBF >() )
				{
					rvalue = getWvalue(apED, aRID,
							rvalue.to_ptr< ArrayBF >(), (*it));
				}
				else if( rvalue.is< BuiltinContainer >() )
				{
					rvalue = getWvalue(apED, aRID,
							rvalue.to_ptr< BuiltinContainer >(), (*it));
				}
				else
				{
					break;
				}
			}

			if( rvalue.is< ArrayBF >() )
			{
				return( getWvalue(apED,
						aRID, rvalue.to_ptr< ArrayBF >(), (*it)) );
			}
			else if( rvalue.is< BuiltinContainer >() )
			{
				return( getWvalue(apED, aRID,
						rvalue.to_ptr< BuiltinContainer >(), (*it)) );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::getWvalue:> Unexpected "
						"rvalue container for the instance of data:\n\t"
						<< str_header( lvalue )
						<< "\nin the runtime context: " << str_header( aRID )
						<< SEND_EXIT;

				return( BF::REF_NULL );
			}

			break;
		}
		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BaseEnvironment::getWvalue:> Unexpected "
						"POINTER NATURE for the instance of data:\n\t"
					<< str_header( lvalue )
					<< "\nin the runtime context: " << str_header( aRID )
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}
	}

	return( BF::REF_NULL );
}


/*
 *******************************************************************************
 * SETTER
 * lvalue := rvalue
 *******************************************************************************
 */

bool BaseEnvironment::setRvalue(ExecutionData & apED,
		const InstanceOfData & lvalue, const BF & rvalue)
{
	if( lvalue.hasRuntimeContainerRID() )
	{
		return( writeData(apED,
				lvalue.getRuntimeContainerRID(), lvalue, rvalue) );
	}
	else
	{
		RuntimeID aDataRID;
		if( getRuntimeForm(apED, apED.getRID(), lvalue, aDataRID) )
		{
			return( writeData(apED, aDataRID, lvalue, rvalue) );
		}
		else
		{
			LocalRuntime aLocalRuntime;
			if( getRuntimeForm(apED, lvalue, aLocalRuntime) )
			{
				return( setLocalRuntime(apED, aLocalRuntime, lvalue, rvalue) );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "BaseEnvironment::setRvalue:> Failed to found "
							"data table for the instance of data:\n\t"
						<< str_header( lvalue )
						<< "\nin the runtime context: "
						<< str_header( apED.getRID() )
						<< SEND_EXIT;
			}
		}
	}

	return( false );
}


bool BaseEnvironment::invokeOnWriteRoutine(ExecutionData & apED,
		const RuntimeID & aRID, const InstanceOfData & lvalue, const BF & rvalue)
{
	if( lvalue.hasOnWriteRoutine() )
	{
		ExecutionEnvironment tmpENV(*this, apED, aRID, BFCode::REF_NULL);
		if( not PRIMITIVE_PROCESSOR.invokeRoutine(
				tmpENV, lvalue.getOnWriteRoutine(), rvalue) )
		{
			return( false );
		}

		if( tmpENV.outEDS.nonempty() )
		{
			RuntimeID saveRID = apED.getRID();

			tmpENV.outEDS.pop_last_to( apED );

			apED.setRID( saveRID );

			if( tmpENV.outEDS.nonempty() )
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unsupported << onWrite >> Routine which execution "
							"create more than one Execution Context\n\t"
						<< str_header( lvalue )
						<< "\nin the runtime context: " << str_header( aRID )
						<< SEND_EXIT;
			}
		}
		else
		{
			return( false );
		}
	}

	return( true );
}


/**
 * setData
 */
bool BaseEnvironment::setData(
		ExecutionData & apED, const RuntimeID & aRID,
		const InstanceOfData & lvalue, const BF & rvalue)
{
	RuntimeForm & aRuntime = apED.getWritableRuntime( aRID );
	aRuntime.makeWritableDataTable();

	switch( lvalue.getPointerNature() )
	{
		case IPointerVariableNature::POINTER_STANDARD_NATURE:
		case IPointerVariableNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE:
		case IPointerVariableNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE:
		{
			aRuntime.assign(lvalue.getOffset(), rvalue);

			break;
		}
		case IPointerVariableNature::POINTER_UFI_OFFSET_NATURE:
		case IPointerVariableNature::POINTER_UFI_RUNTIME_NATURE:
		{
			BF rvContainer = aRuntime.getWritableData( lvalue.getOffset() );

//			TableOfSymbol::iterator it = lvalue.getDataPath()->begin();
//			TableOfSymbol::iterator itEnd = lvalue.getDataPath()->pred_end();
//			for( ; it != itEnd ; ++it )
//			{
//				rvContainer.moveAtWritable( (*it)->getOffset() );
//			}
//			rvContainer->set((*it)->getOffset(), rvalue);

			// NO +1 for << this >> which is the root of the path
			std::size_t pathLength = lvalue.getDataPath()->size();
			std::size_t * theOffsetPath = lvalue.getOffsetPath();

			for( std::size_t k = 1 ; k < pathLength ; ++k )
			{
				rvContainer.moveAtWritable( theOffsetPath[k] );
			}

			rvContainer.set(theOffsetPath[pathLength], rvalue);

			break;
		}
		case IPointerVariableNature::POINTER_UFI_MIXED_NATURE:
		{
			BF rvContainer = aRuntime.getWritableData( lvalue.getOffset() );

			TableOfSymbol::iterator it = lvalue.getDataPath()->begin();
			TableOfSymbol::iterator itEnd = lvalue.getDataPath()->pred_end();
			for( ; it != itEnd ; ++it )
			{
				switch( (*it).getPointerNature() )
				{
					case IPointerVariableNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
					case IPointerVariableNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
					{
						rvContainer.moveAtWritable( (*it).getOffset() );

						break;
					}
					case IPointerVariableNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
					{
						EvaluationEnvironment eENV(*this, apED);
						if( eENV.evalOffset( (*it).getValue() ) )
						{
							apED = eENV.outED;
						}
						else
						{
							AVM_OS_FATAL_ERROR_EXIT
									<<  "Failed to eval ARRAY index << "
									<< (*it).strValue()
									<< " >> in variable << " << (*it).str()
									<< " >> for writing in VVT !!!"
									<< SEND_EXIT;

							return( false );
						}

						if( eENV.outVAL.isNumeric() )
						{
							AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT(
								eENV.outVAL.toInteger(),
								static_cast< avm_integer_t >(rvContainer.size()) )
									<< "Failed to write in ARRAY with index << "
									<< eENV.outVAL.toInteger()
									<< " >> in variable << " << lvalue.str()
									<< " >> for writing in VVT !!!"
									<< SEND_EXIT;

							rvContainer.moveAtWritable( eENV.outVAL.toInteger() );

							break;
						}

						else
						{
							std::size_t offset = genNumericOffset(
									apED, aRID, (*it), eENV.outVAL, 0,
									(rvContainer.size() - 1) );

							if( offset != AVM_NUMERIC_MAX_SIZE_T )
							{
								rvContainer.moveAtWritable( offset );

								break;
							}
						}

						apED.mwsetAEES( AEES_SYMBOLIC_EXECUTION_LIMITATION );

						AVM_OS_FATAL_ERROR_EXIT
								<< "BaseEnvironment::setData:> "
									"unexpected NON-INTEGER ARRAY INDEX << "
								<< eENV.outVAL.str()
								<< " >> in instance FQN-ID :>\n"
								<< str_header( lvalue )
								<< SEND_EXIT;

						return( false );
					}
					default:
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "BaseEnvironment::setData:> Unexpected "
									"POINTER NATURE for the instance of data :>\n"
								<< str_header( lvalue )
								<< SEND_EXIT;

						return( false );
					}
				}
			}

			switch( (*it).getPointerNature() )
			{
				case IPointerVariableNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
				case IPointerVariableNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
				case IPointerVariableNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE:
				case IPointerVariableNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE:
				{
					rvContainer.set((*it).getOffset(), rvalue);

					break;
				}
				case IPointerVariableNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
				{
					EvaluationEnvironment eENV(*this, apED);
					if( eENV.evalOffset((*it).getValue()) )
					{
						apED = eENV.outED;
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Failed to eval ARRAY index << "
								<< (*it).strValue() << " >> in variable << "
								<< (*it).str() << " >> for writing in VVT !!!"
								<< SEND_EXIT;

						return( false );
					}

					if( eENV.outVAL.isNumeric() )
					{
						AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT(
							eENV.outVAL.toInteger(),
							static_cast< avm_integer_t >(rvContainer.size()) )
								<< "Failed to access to an ARRAY with index << "
								<< lvalue.strValue()
								<< " >> for writing in VVT !!!"
								<< SEND_EXIT;

						rvContainer.set(eENV.outVAL.toInteger(), rvalue);

						break;
					}

					else
					{
						std::size_t offset = genNumericOffset(apED, aRID, (*it),
								eENV.outVAL, 0, (rvContainer.size() - 1) );

						if( offset != AVM_NUMERIC_MAX_SIZE_T )
						{
							rvContainer.set(offset, rvalue);

							break;
						}
					}

					// SYMBOLIC ACCES ERROR
					apED.mwsetAEES( AEES_SYMBOLIC_EXECUTION_LIMITATION );

					AVM_OS_FATAL_ERROR_EXIT
							<< "BaseEnvironment::setData:> Unexpected "
								"NON-INTEGER ARRAY INDEX << "
							<< eENV.outVAL.str() << " >> in instance FQN-ID :>\n"
							<< str_header( lvalue )
							<< SEND_EXIT;

					return( false );
				}
				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "BaseEnvironment::setData:> "
								"Unexpected POINTER NATURE "
								"for the instance of data :>\n"
							<< str_header( lvalue )
							<< SEND_EXIT;

					return( false );
				}
			}

			break;
		}
		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BaseEnvironment::setData:> Unexpected "
						"POINTER NATURE for the instance of data :>\n"
					<< str_header( lvalue )
					<< SEND_EXIT;

			return( false );
		}
	}

	apED.setAssigned(aRID, lvalue.getOffset());
//	aRuntime.setAssigned( lvalue.getOffset() );

	return( true );
}


/**
 * setLocalRuntime
 */
bool BaseEnvironment::setLocalRuntime(
		ExecutionData & apED, LocalRuntime & aLocalRuntime,
		const InstanceOfData & lvalue, const BF & rvalue)
{
	apED.makeModifiableLocalRuntime( aLocalRuntime );

	// TODO what to do with monitor in this case

	aLocalRuntime.setData(lvalue.getOffset(), rvalue);

	return( true );
}


/**
 * TOOLS
 */
BFCode BaseEnvironment::searchTraceIO(const BF & aTrace)
{
	if( aTrace.valid() )
	{
		BFCode ioTrace;

		if( aTrace.is< AvmCode >() )
		{
			for( const auto & itOperand : aTrace.to< AvmCode >().getOperands() )
			{
				ioTrace = searchTraceIO(itOperand);
				if( ioTrace.valid() )
				{
					return( ioTrace );
				}
			}
		}
		else if( aTrace.is< ExecutionConfiguration >() )
		{
			const ExecutionConfiguration & execConf =
					aTrace.to< ExecutionConfiguration >();

			if( execConf.isAvmCode() )
			{
				ioTrace = execConf.getAvmCode();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )
	AVM_OS_TRACE << std::endl
			<< "Is ioTrace : " << ioTrace.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )

				if( StatementTypeChecker::isCommunication(ioTrace) )
				{
					return( ioTrace );
				}
				else
				{
					return( BFCode::REF_NULL );
				}
			}
		}
	}

	return( BFCode::REF_NULL );
}


BFCode BaseEnvironment::searchTraceIO(
		const BF & aTrace, const AvmCode & ioFormula)
{
	if( aTrace.valid() )
	{
		BFCode ioTrace;

		if( aTrace.is< AvmCode >() )
		{
			for( const auto & itOperand : aTrace.to< AvmCode >().getOperands() )
			{
				ioTrace = searchTraceIO(itOperand, ioFormula);
				if( ioTrace.valid() )
				{
					return( ioTrace );
				}
			}
		}
		else if( aTrace.is< ExecutionConfiguration >() )
		{
			const ExecutionConfiguration & execConf =
					aTrace.to< ExecutionConfiguration >();

			if( execConf.isAvmCode() )
			{
				ioTrace = execConf.getAvmCode();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )
	AVM_OS_TRACE << std::endl
			<< "ioFormula  : " << ioFormula.str()<< std::endl
			<< "Is ioTrace : " << ioTrace.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )

				if( ioTrace->sameOperator( ioFormula ) &&
					(ioTrace->size() >= ioFormula.size()) )
				{
					BaseInstanceForm * ioTraceInstance =
							ioTrace->first().as_ptr< BaseInstanceForm >();

					BaseInstanceForm * ioFormulaInstance =
							ioFormula.first().as_ptr< BaseInstanceForm >();

					if( ioTraceInstance->equals(ioFormulaInstance) )
					{
						if( ioFormulaInstance->isAlias() )
						{
							const InstanceOfMachine * anInstanceMachine =
									ioFormulaInstance->getMachinePath()->last();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )
	AVM_OS_TRACE << "Is instance: " << execConf.getRuntimeID().getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )

							if( not execConf.getRuntimeID()
									.hasAsAncestor(* anInstanceMachine) )
							{
								return( BFCode::REF_NULL );
							}
						}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )
	AVM_OS_TRACE << "Found match: YES !!!" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )

						return( ioTrace );
					}
				}
				else
				{
					return( BFCode::REF_NULL );
				}
			}
		}
	}

	return( BFCode::REF_NULL );
}


BFCode BaseEnvironment::searchTraceIO(const BF & aTrace,
		const RuntimeID & ctxRID, const AvmCode & ioFormula)
{
	if( aTrace.valid() )
	{
		BFCode ioTrace;

		if( aTrace.is< AvmCode >() )
		{
			for( const auto & itOperand : aTrace.to< AvmCode >().getOperands() )
			{
				ioTrace = searchTraceIO(itOperand, ctxRID, ioFormula);
				if( ioTrace.valid() )
				{
					return( ioTrace );
				}
			}
		}
		else if( aTrace.is< ExecutionConfiguration >() )
		{
			const ExecutionConfiguration & execConf =
					aTrace.to< ExecutionConfiguration >();

			if( execConf.getRuntimeID().hasAsAncestor(ctxRID)
				&& execConf.isAvmCode() )
			{
				ioTrace = execConf.getAvmCode();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )
	AVM_OS_TRACE
			<< "ioTrace    : " << ioTrace.str()	<< std::endl
			<< "ioFormula  : " << ioFormula.str()<< std::endl << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )

				if( ioTrace->sameOperator( ioFormula ) &&
					(ioTrace->size() >= ioFormula.size()) )
				{
					BaseInstanceForm * ioTraceInstance =
							ioTrace->first().as_ptr< BaseInstanceForm >();

					BaseInstanceForm * ioFormulaInstance =
							ioFormula.first().as_ptr< BaseInstanceForm >();

					if( ioTraceInstance->equals(ioFormulaInstance) )
					{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )
	AVM_OS_TRACE << "Found match : YES !!!" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )

						return( ioTrace );
					}
				}
				else
				{
					return( BFCode::REF_NULL );
				}
			}
		}
	}

	return( BFCode::REF_NULL );
}


const ExecutionConfiguration & BaseEnvironment::searchTraceIOExecConf(const BF & aTrace)
{
	if( aTrace.valid() )
	{
		if( aTrace.is< AvmCode >() )
		{
			for( const auto & itOperand : aTrace.to< AvmCode >().getOperands() )
			{
				const ExecutionConfiguration & ioExecConf = searchTraceIOExecConf(itOperand);
				if( ioExecConf.isnotNullref() )
				{
					return( ioExecConf );
				}
			}
		}
		else if( aTrace.is< ExecutionConfiguration >() )
		{
			const ExecutionConfiguration & execConf =
					aTrace.to< ExecutionConfiguration >();

			if( execConf.isAvmCode() )
			{
				const AvmCode & ioTrace = execConf.toAvmCode();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )
	AVM_OS_TRACE << std::endl
			<< "Is ioTrace : " << ioTrace.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PORT )

				if( StatementTypeChecker::isCommunication(ioTrace) )
				{
					return( execConf );
				}
				else
				{
					return( ExecutionConfiguration::nullref() );
				}
			}
		}
	}

	return( ExecutionConfiguration::nullref() );
}



} /* namespace sep */

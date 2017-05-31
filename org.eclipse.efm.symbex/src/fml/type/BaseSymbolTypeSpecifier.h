/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 juin 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASESYMBOLTYPESPECIFIER_H_
#define BASESYMBOLTYPESPECIFIER_H_

#include <fml/type/BaseTypeSpecifier.h>

#include <common/BF.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/symbol/TableOfSymbol.h>


namespace sep
{

class DataType;
class ObjectElement;


class BaseSymbolTypeSpecifier  :  public BaseTypeSpecifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BaseSymbolTypeSpecifier )
{

	AVM_DECLARE_UNCLONABLE_CLASS(BaseSymbolTypeSpecifier)


protected:
	/*
	 * ATTRIBUTES
	 */
	TableOfSymbol mSymbolData;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseSymbolTypeSpecifier(class_kind_t aClassKind,
			avm_type_specifier_kind_t aSpecifierKind,
			DataType * aCompiledType,
			avm_size_t aSize, avm_size_t aDataSize, avm_size_t aBitSize)
	: BaseTypeSpecifier(aClassKind, aSpecifierKind, aCompiledType,
			aSize, aDataSize, aBitSize),
	mSymbolData()
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseSymbolTypeSpecifier()
	{
		//!!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mSymbolData
	 */
	inline void saveSymbolData(InstanceOfData * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		mSymbolData.save(anInstance);
	}


	/**
	 * GETTER - SETTER
	 * mSymbolData
	 */
	inline void appendSymbolData(const Symbol & aSymbol)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aSymbol )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		mSymbolData.append(aSymbol);
	}

	inline TableOfSymbol & getSymbolData()
	{
		return( mSymbolData );
	}

	inline const TableOfSymbol & getSymbolData() const
	{
		return( mSymbolData );
	}


	inline const Symbol & getSymbolData(avm_offset_t offset) const
	{
		return( mSymbolData.get(offset) );
	}

	inline const Symbol & getSymbolData(
			const std::string & aFullyQualifiedNameID) const
	{
		return( mSymbolData.getByFQNameID(aFullyQualifiedNameID) );
	}

	inline const Symbol & getDataByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		return( mSymbolData.getByQualifiedNameID( aQualifiedNameID ) );
	}

	inline const Symbol & getDataByNameID(const std::string & id) const
	{
		return( mSymbolData.getByNameID(id) );
	}


	inline const Symbol & getDataByAstElement(
			const ObjectElement * astElement) const
	{
		return( mSymbolData.getByAstElement(astElement) );
	}


	inline BaseTypeSpecifier * getSymbolType(avm_offset_t offset) const
	{
		return( mSymbolData.get(offset).getTypeSpecifier() );
	}


	inline bool hasSymbolData() const
	{
		return( mSymbolData.nonempty() );
	}


	/**
	 * SETTER
	 * the Data Size
	 */
	inline virtual void updateSize()
	{
		avm_size_t aDataSize = 0;

		TableOfSymbol::iterator it = getSymbolData().begin();
		TableOfSymbol::iterator itEnd = getSymbolData().end();
		for( ; it != itEnd ; ++it )
		{
			aDataSize = aDataSize + (*it).getTypeSpecifier()->getDataSize();
		}

		setDataSize( aDataSize );

		setSize( getSymbolData().size() );
	}

};



} /* namespace sep */

#endif /* BASESYMBOLTYPESPECIFIER_H_ */

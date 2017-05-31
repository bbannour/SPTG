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

#ifndef TABLEOFSYMBOL_H_
#define TABLEOFSYMBOL_H_

#include <common/AvmObject.h>

#include <collection/Vector.h>

#include <fml/symbol/Symbol.h>
#include <collection/List.h>


namespace sep
{


class BF;

class ObjectElement;


class TableOfSymbol :
		public AvmObject,
		public VectorOfSymbol,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TableOfSymbol )
{

	AVM_DECLARE_CLONABLE_CLASS( TableOfSymbol )


public:
	/**
	 * TYPEDEF
	 */
	typedef BaseInstanceForm        * PointerBaseT;
	typedef const BaseInstanceForm  * ConstPointerBaseT;

	typedef VectorOfSymbol            ContainerOfSymbol;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TableOfSymbol()
	: AvmObject( ),
	ContainerOfSymbol( )
	{
		//!! NOTHING
	}

	TableOfSymbol(avm_size_t aSize)
	: AvmObject( ),
	ContainerOfSymbol( aSize )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TableOfSymbol(const TableOfSymbol & aTable)
	: AvmObject( aTable ),
	ContainerOfSymbol( aTable )
	{
		//!! NOTHING
	}

	TableOfSymbol(const TableOfSymbol & aTable, const Symbol & lastSymbol)
	: AvmObject( aTable ),
	ContainerOfSymbol( aTable )
	{
		ContainerOfSymbol::push_back( lastSymbol );
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~TableOfSymbol()
	{
		//!! NOTHING
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * iterator predecessor of end
	 ***************************************************************************
	 */
	inline ContainerOfSymbol::iterator pred_end()
	{
		return( ContainerOfSymbol::empty() ? ContainerOfSymbol::end() :
				--( ContainerOfSymbol::end() ) );
	}

	inline ContainerOfSymbol::const_iterator pred_end() const
	{
		return( ContainerOfSymbol::empty() ? ContainerOfSymbol::end() :
				--( ContainerOfSymbol::end() ) );
	}


	/**
	 * GETTER
	 */
	inline const Symbol & get(avm_size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( offset, ContainerOfSymbol::size() )
				<< "Unbound Symbol offset !!!" << std::endl << str_header( this )
				<< SEND_EXIT;

		return( ContainerOfSymbol::at(offset) );
	}


	const Symbol & getByFQNameID(
			const std::string & aFullyQualifiedNameID) const;


	const Symbol & getByQualifiedNameID(
			const std::string & aQualifiedNameID) const;

	avm_size_t getByQualifiedNameID(
			const std::string & aQualifiedNameID,
			ListOfSymbol & listofFound) const;


	const Symbol & getByNameID(const std::string & id) const;

	avm_size_t getByNameID(
			const std::string & id, ListOfSymbol & listofFound) const;


	const Symbol & getByAstElement(const ObjectElement * objElement) const;


	/**
	 * SAVE
	 * APPEND
	 */
	inline const Symbol & save(PointerBaseT aSymbol)
	{
		ContainerOfSymbol::push_back( Symbol(aSymbol) );

		return( ContainerOfSymbol::back() );
	}

	inline void append(const Symbol & aSymbol)
	{
		ContainerOfSymbol::append( aSymbol );
	}

	inline void append(const ListOfSymbol & dataList)
	{
		ContainerOfSymbol::append( dataList );
	}

	inline void append(const VectorOfSymbol & dataList)
	{
		ContainerOfSymbol::append( dataList );
	}


	/**
	 * SETTER
	 */
	inline void set(avm_offset_t offset, const Symbol & aSymbol)
	{
		ContainerOfSymbol::set(offset, aSymbol);
	}

	inline void set(avm_offset_t offset, PointerBaseT aSymbol)
	{
		ContainerOfSymbol::set(offset, Symbol(aSymbol));
	}


	/**
	 * contains a particular element
	 */
	bool contains(ConstPointerBaseT aSymbol) const;

	bool contains(const Symbol & aSymbol) const
	{
		return( ContainerOfSymbol::contains(aSymbol) );
	}

	bool contains(const BF & aSymbol) const;


	/**
	 * Serialization
	 */
	virtual void strHeader(OutStream & os) const;

	virtual void toStream(OutStream & os) const;

	virtual void toFscn(OutStream & os) const;


};


} /* namespace sep */

#endif /* TABLEOFSYMBOL_H_ */

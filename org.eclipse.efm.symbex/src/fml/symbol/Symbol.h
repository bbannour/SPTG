/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 juin 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SYMBOL_H_
#define SYMBOL_H_

#include <fml/common/BasePointer.h>
#include <fml/type/TypeSpecifier.h>

#include <common/Element.h>

#include <collection/List.h>
#include <collection/Vector.h>

#include <fml/executable/BaseInstanceForm.h>

#include <fml/lib/AvmLang.h>
#include <fml/lib/ITypeSpecifier.h>



#define AVM_DEBUG_SYMBOL_POINTER  true
#undef AVM_DEBUG_SYMBOL_POINTER

#if defined(AVM_DEBUG_SYMBOL_POINTER)

	#define AVM_DECLARE_DEBUG_SYMBOL_PTR      const BaseInstanceForm * debugPTR;

	#define AVM_INIT_DEBUG_SYMBOL_PTR( ptr )  , debugPTR( ptr )

	#define AVM_ASSIGN_STMNT_DEBUG_SYMBOL_PTR( ptr )  debugPTR = ptr;

	#define AVM_ASSIGN_EXPR_DEBUG_SYMBOL_PTR( ptr )   debugPTR = ptr

#else

	#define AVM_DECLARE_DEBUG_SYMBOL_PTR

	#define AVM_INIT_DEBUG_SYMBOL_PTR( ptr )

	#define AVM_ASSIGN_STMNT_DEBUG_SYMBOL_PTR( ptr )

	#define AVM_ASSIGN_EXPR_DEBUG_SYMBOL_PTR( ptr )  ptr

#endif




namespace sep
{


class ArrayBF;
class BF;
class Specifier;
class TableOfSymbol;
class TypeSpecifier;

class ExecutableForm;

class InstanceOfBuffer;
class InstanceOfConnector;
class InstanceOfData;
class InstanceOfMachine;
class InstanceOfPort;

class Machine;

class RoutingData;


class Symbol :
		public BasePointer< BaseInstanceForm >,
		public ITypeSpecifier,
		public IPointerVariableNature,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Symbol )
{

private:
	/**
	 * TYPEDEF
	 */
	typedef  BasePointer< BaseInstanceForm >  base_this_type;


public:
	/**
	 * DEFAULT REF_NULL
	 */
	static Symbol REF_NULL;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Symbol()
	: base_this_type( )
	{
		//!!! NOTHING
	}

	explicit Symbol(BaseInstanceForm * anInstance)
	: base_this_type( anInstance )
	{
		//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Symbol(const Symbol & aSymbol)
	: base_this_type( aSymbol )
	{
		//!! NOTHING
	}

	explicit Symbol(const BF & aSymbol)
	: base_this_type( aSymbol )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Symbol()
	{
		//!!! NOTHING
	}


	/**
	 * GETTER
	 * pointer
	 */
	inline pointer_t rawSymbol() const
	{
		return( static_cast< pointer_t >( mPTR ) );
	}


public:

	/**
	 * ASSIGNMENT
	 * BF
	 */
	Symbol & operator=(const BF & aSymbol);

	Symbol & operator=(pointer_t aPtr)
	{
		if( mPTR != aPtr )
		{
			AVM_ASSIGN_DEBUG_BF_PTR( aPtr )

			release( aPtr );
		}
		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// BaseInstanceForm
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER BaseAvmProgram * aContainer
	 * mContainer
	 */
	inline BaseAvmProgram * getContainer() const
	{
		return( rawSymbol()->getContainer() );
	}

	inline void setContainer(ObjectElement * aContainer)
	{
		rawSymbol()->setContainer( aContainer );
	}

	/**
	 * GETTER - SETTER - TESTER
	 * mTypeSpecifier
	 */
//	inline virtual const TypeSpecifier & thisTypeSpecifier() const
//	{
//		return( rawSymbol()->thisTypeSpecifier() );
//	}
//
//	inline virtual const TypeSpecifier & getTypeSpecifier() const
//	{
//		return( rawSymbol()->getTypeSpecifier() );
//	}

	inline virtual const BaseTypeSpecifier & thisTypeSpecifier() const override
	{
		return( rawSymbol()->thisTypeSpecifier() );
	}

	inline const BaseTypeSpecifier & getTypeSpecifier() const
	{
		return( rawSymbol()->getTypeSpecifier() );
	}

	inline const BaseTypeSpecifier & referedTypeSpecifier() const
	{
		return( rawSymbol()->referedTypeSpecifier() );
	}

	inline virtual avm_type_specifier_kind_t getTypeSpecifierKind() const override
	{
		return( rawSymbol()->getTypeSpecifierKind() );
	}

	inline bool hasTypeSpecifier() const
	{
		return( rawSymbol()->hasTypeSpecifier() );
	}


	/**
	 * GETTER - SETTER
	 * mOffset
	 */
	inline avm_offset_t getOffset() const
	{
		return( rawSymbol()->getOffset() );
	}

	inline void setOffset(avm_offset_t anOffset)
	{
		rawSymbol()->setOffset( anOffset );
	}


	/**
	 * GETTER - SETTER
	 * mCreatorContainerID
	 */
	inline const RuntimeID & getCreatorContainerRID() const
	{
		return( rawSymbol()->getCreatorContainerRID() );
	}

	inline bool hasCreatorContainerRID() const
	{
		return( rawSymbol()->hasCreatorContainerRID() );
	}

	inline void setCreatorContainerRID(const RuntimeID & aRID)
	{
		rawSymbol()->setCreatorContainerRID( aRID );
	}


	/**
	 * GETTER - SETTER
	 * mRuntimeContainerID
	 */
	inline const RuntimeID & getRuntimeContainerRID() const
	{
		return( rawSymbol()->getRuntimeContainerRID() );
	}

	inline bool hasRuntimeContainerRID() const
	{
		return( rawSymbol()->hasRuntimeContainerRID() );
	}

	inline void setRuntimeContainerRID(const RuntimeID & aRID)
	{
		rawSymbol()->setRuntimeContainerRID( aRID );
	}


	/**
	 * GETTER - SETTER
	 * mRelativeMachinePath
	 */
//	inline void appendMachinePath(InstanceOfMachine * anInstance)
//	{
//		rawSymbol()->appendMachinePath(anInstance);
//	}

	inline void appendMachinePath(ArrayOfInstanceOfMachine & aliasPath) const
	{
		rawSymbol()->appendMachinePath( aliasPath );
	}

	inline ArrayOfInstanceOfMachine * getMachinePath() const
	{
		return( rawSymbol()->getMachinePath() );
	}

	inline bool hasMachinePath() const
	{
		return( rawSymbol()->hasMachinePath() );
	}


	inline bool isAlias() const
	{
		return( rawSymbol()->isAlias() );
	}


	/**
	 * GETTER - SETTER
	 * mAliasTarget
	 */
	inline const BaseInstanceForm * getAliasTarget() const
	{
		return( rawSymbol()->getAliasTarget() );
	}

	inline bool hasAliasTarget() const
	{
		return( rawSymbol()->hasAliasTarget() );
	}

	inline void setAliasTarget(const BaseInstanceForm & anAliasTarget)
	{
		rawSymbol()->setAliasTarget( anAliasTarget );
	}

	/**
	 * GETTER - SETTER
	 * mInstanciationCount
	 */
	inline std::uint32_t instanciationCountIncr() const
	{
		return( rawSymbol()->instanciationCountIncr() );
	}

	inline std::uint32_t getInstanciationCount() const
	{
		return( rawSymbol()->getInstanciationCount() );
	}

	inline void setInstanciationCount(std::uint32_t anIndex)
	{
		rawSymbol()->setInstanciationCount( anIndex );
	}


	/**
	 * is equals
	 */
	inline virtual bool equals(BaseInstanceForm * anInstance) const
	{
		return( rawSymbol()->equals( anInstance ) );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// InstanceOfBuffer
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	InstanceOfBuffer & asBuffer();

	const InstanceOfBuffer & asBuffer() const;

	InstanceOfBuffer * rawBuffer() const;


	/**
	 * GETTER - SETTER
	 * mPolicySpecifierKind
	 */
	avm_type_specifier_kind_t getPolicySpecifierKind() const;

	void setPolicySpecifierKind(avm_type_specifier_kind_t aSpecifierKind);

	/**
	 * GETTER - SETTER
	 * mCapacity
	 */
	std::size_t getCapacity() const;

	long realCapacity() const;

	void setCapacity(long aCapacity);


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// InstanceOfChannel
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	InstanceOfPort & channel();

	const InstanceOfPort & channel() const;

	InstanceOfPort * rawChannel() const;


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// InstanceOfConnector
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	InstanceOfConnector & asConnector();

	const InstanceOfConnector & asConnector() const;

	InstanceOfConnector * rawConnector() const;


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// InstanceOfData
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	InstanceOfData & variable();

	const InstanceOfData & variable() const;

	InstanceOfData * rawVariable() const;


	/**
	 * SETTER
	 * mFullyQualifiedNameID
	 */
	void updateFullyQualifiedNameID(
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID);

	/**
	 * GETTER - SETTER
	 * mPointerNature
	 */
	virtual POINTER_VARIABLE_NATURE getPointerNature() const override;


	/**
	 * GETTER - SETTER
	 * mValue
	 */
	BF & getValue();

	const BF & getValue() const;

	bool hasValue() const;

	void setValue(const BF & aValue);

	// ArrayValue
	ArrayBF * getArrayValue() const;

	bool hasArrayValue() const;


	void formatStream(OutStream & os, const BF & aValue) const;

	void strValue(OutStream & os, const BF & aValue) const;

	std::string strValue(const BF & aValue) const;

	std::string strValue() const;


	/**
	 * GETTER - SETTER
	 * mAttributeTable
	 */
	TableOfSymbol * getAttribute() const;

	const Symbol & getAttributeByNameID(const std::string & id) const;

	bool hasAttribute() const;

	void setAttribute(TableOfSymbol * anAttributeTable);

	void setAttribute(avm_offset_t offset, const Symbol & aWProperty);


	/**
	 * GETTER - SETTER
	 * mRelativeDataPath
	 * mRelativeOffsetPath
	 */
	TableOfSymbol * getDataPath() const;

	bool hasDataPath() const;

	void setDataPath(TableOfSymbol & aRelativeDataPath);

	std::size_t * getOffsetPath() const;


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// InstanceOfMachine
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	InstanceOfMachine & machine();

	const InstanceOfMachine & machine() const;

	InstanceOfMachine * rawMachine() const;


	/**
	 * GETTER
	 * Specifier
	 */
	const Specifier & getSpecifier() const;


	/**
	 * GETTER
	 * Compiled ObjectElement as Compiled Machine
	 */
	const Machine & getAstMachine() const;


	/**
	 * GETTER
	 * THIS
	 */
	bool isThis() const;

	bool isnotThis(const ExecutableForm * anExecutable) const;

	/**
	 * GETTER - SETTER
	 * mExecutable
	 */
	const ExecutableForm & getExecutable() const;

	ExecutableForm & getExecutable();

	const ExecutableForm * ptrExecutable() const;

	bool hasExecutable() const;

	/**
	 * GETTER - SETTER
	 * mInstanceModel
	 */
	InstanceOfMachine * getInstanceModel() const;

	bool hasInstanceModel() const;

	bool isInstanceModel(InstanceOfMachine * anInstanceModel) const;

	void setInstanceModel(InstanceOfMachine * anInstanceModel);

	/**
	 * GETTER - SETTER
	 * mParam
	 * mParamReturnTable
	 * mReturnOffset
	 */
	bool hasParam() const;

	/**
	 * GETTER - SETTER
	 * mRuntimeRID
	 */
	const RuntimeID & getRuntimeRID() const;

	bool hasRuntimeRID() const;

	void setRuntimeRID(const RuntimeID & aRID);


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// InstanceOfPort
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	InstanceOfPort & asPort();

	const InstanceOfPort & asPort() const;

	InstanceOfPort * rawPort() const;


	/**
	 * GETTER - SETTER
	 * mRouteOffset
	 */
	std::size_t getRouteOffset() const;

	void setRouteOffset(std::size_t aRouteOffset);

	/**
	 * GETTER - SETTER
	 * mInputRoutingData
	 * mOutputRoutingData
	 */
	const RoutingData & getInputRoutingData() const;

	bool hasInputRoutingData() const;

	void setInputRoutingData(const RoutingData & anInputRoutingData);


	const RoutingData & getOutputRoutingData() const;

	bool hasOutputRoutingData() const;

	void setOutputRoutingData(const RoutingData & anOutputRoutingData);



	////////////////////////////////////////////////////////////////////////////
	// Serialization
	////////////////////////////////////////////////////////////////////////////
	inline virtual std::string strHeader() const override
	{
		return( ( mPTR != nullptr ) ?
				rawSymbol()->strHeader() : "Symbol::header<null>" );
	}

	inline virtual void strHeader(OutStream & os) const override
	{
		if( mPTR != nullptr )
		{
			rawSymbol()->strHeader(os);
		}
		else
		{
			os << "Symbol::header<null>";
		}
	}

	inline virtual void toStream(OutStream & os) const override
	{
		if( mPTR != nullptr )
		{
			rawSymbol()->toStream( os );
		}
		else
		{
			os << TAB << "Symbol::stream<null>" << EOL_FLUSH;
		}
	}

	inline virtual void toFscn(OutStream & os) const
	{
		if( mPTR != nullptr )
		{
			rawSymbol()->toFscn( os );
		}
		else
		{
			os << TAB << "Symbol::fscn<null>" << EOL_FLUSH;
		}
	}

	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const override
	{
		StringOutStream oss(indent);

		toStream( oss );

		return( oss.str() );
	}

	inline virtual std::string str() const override
	{
		return( ( mPTR != nullptr ) ?
				rawSymbol()->str() : "Symbol::str<null>" );
	}

	inline virtual std::string strNum(
			uint8_t precision = AVM_MUMERIC_PRECISION) const override
	{
		return( ( mPTR != nullptr ) ?
				rawSymbol()->strNum(precision) : "Symbol::num<null>" );
	}

};




////////////////////////////////////////////////////////////////////////////////
// TYPEDEF FOR COLLECTION < Symbol >
////////////////////////////////////////////////////////////////////////////////

typedef           List < Symbol > ListOfSymbol;
typedef         Vector < Symbol > VectorOfSymbol;


/**
 * operator<<
 */
//AVM_OS_STREAM( Symbol )
//
//AVM_OS_STREAM_COLLECTION( ListOfSymbol     )
//AVM_OS_STREAM_COLLECTION( VectorOfSymbol   )



} /* namespace sep */

#endif /* SYMBOL_H_ */

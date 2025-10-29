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
#ifndef RUNTIMEFORMID_H_
#define RUNTIMEFORMID_H_

#include <common/NamedElement.h>
#include <common/BF.h>

#include <collection/Vector.h>

#include <fml/expression/AvmCode.h>


namespace sep
{

class BaseInstanceForm;

class ExecutableForm;

class InstanceOfData;
class InstanceOfPort;
class InstanceOfMachine;

class Specifier;

class RuntimeID;


class _RuntimeID_ final :
		public NamedElement,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( _RuntimeID_ )
{
	friend RuntimeID;

	AVM_DECLARE_CLONABLE_CLASS( _RuntimeID_ )

public:
	/**
	 * ATTRIBUTES
	 */
	std::string mQualifiedNameID;

	bool mDynamicLoaded;

	_RuntimeID_ * mModel;

	_RuntimeID_ * mParent;

	_RuntimeID_ * mCompositeComponent;
	_RuntimeID_ * mCompositeComponentParent;

	_RuntimeID_ * mLifeline;
	_RuntimeID_ * mCommunicator;

	_RuntimeID_ * mComponentSelf;
	_RuntimeID_ * mComponentParent;
	_RuntimeID_ * mComponentCommunicator;

	int mRid;

	avm_offset_t mOffset;

	InstanceOfMachine * mInstance;

	BFCode onRunning;


public:
	/**
	* CONSTRUCTOR
	* Default
	*/
	_RuntimeID_(_RuntimeID_ * aModel, _RuntimeID_ * aParent,
			int aPid, avm_offset_t anOffset, InstanceOfMachine * anInstance)
	: NamedElement( CLASS_KIND_T( RuntimeID ) ),
	mQualifiedNameID( ),

	mDynamicLoaded( false ),

	mModel( aModel ),

	mParent( aParent ),

	mCompositeComponent( ),
	mCompositeComponentParent( ),

	mLifeline( ),
	mCommunicator( ),

	mComponentSelf( ),
	mComponentParent( ),
	mComponentCommunicator( ),

	mRid( aPid ),
	mOffset( anOffset ),
	mInstance( anInstance ),

	onRunning( )
	{
		updateFullyQualifiedNameID();
	}

	/**
	* CONSTRUCTOR
	* Copy
	*/
	_RuntimeID_(const _RuntimeID_ & aRID)
	: NamedElement( aRID ),
	mQualifiedNameID( aRID.mQualifiedNameID ),

	mDynamicLoaded( aRID.mDynamicLoaded ),

	mModel( aRID.mModel ),

	mParent( aRID.mParent ),

	mCompositeComponent( aRID.mCompositeComponent ),
	mCompositeComponentParent( aRID.mCompositeComponentParent ),

	mLifeline( aRID.mLifeline ),
	mCommunicator( aRID.mCommunicator ),

	mComponentSelf( aRID.mComponentSelf ),
	mComponentParent( aRID.mComponentParent ),
	mComponentCommunicator( aRID.mComponentCommunicator ),

	mRid( aRID.mRid ),
	mOffset( aRID.mOffset ),
	mInstance( aRID.mInstance ),

	onRunning( aRID.onRunning )
	{
		//!! NOTHING
	}


	/**
	* DESTRUCTOR
	*/
	virtual ~_RuntimeID_()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mFullyQualifiedNameID
	 */
	void updateFullyQualifiedNameID();

	/**
	 * GETTER - SETTER
	 * mFullyQualifiedNameID
	 */
	inline std::string getQualifiedNameID() const override
	{
		return( mQualifiedNameID );
	}

	inline void setQualifiedNameID(const std::string & anUfid)
	{
		mQualifiedNameID = anUfid;
	}

	/**
	 * GETTER - SETTER
	 * mNameID
	 */
	inline virtual const std::string & getNameID() const override
	{
		if( mNameID.empty() )
		{
			return( NamedElement::UNNAMED_ID );
		}
		return( mNameID );
	}

	/**
	 * GETTER
	 * Executable
	 */
	ExecutableForm & refExecutable() const;

	/**
	 * mRID of shortcut
	 */
	inline static int ridOf(_RuntimeID_ * anElement)
	{
		return( ( anElement != nullptr ) ? anElement->mRid : -1 );
	}

	/**
	 * Serialization
	 */
	inline virtual std::string str() const override
	{
		return( mQualifiedNameID );
	}

	inline virtual std::string strHeader() const
	{
		return( mQualifiedNameID );
	}

	inline virtual void strHeader(OutStream & out) const
	{
		out << mQualifiedNameID;
	}

	virtual void toStream(OutStream & out) const override;

};


class RuntimeID final : public BF,
		AVM_INJECT_STATIC_NULL_REFERENCE( RuntimeID ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( RuntimeID )
{

private:
	/**
	 * TYPEDEF
	 */
	typedef BF          base_this_type;

public:
	typedef _RuntimeID_ raw_value_t;


public:
	/**
	* GLOBALS
	* BASE NAME PREFIX
	*/
	static std::string NAME_ID_SEPARATOR;

	static std::string BASENAME_PREFIX;

	static std::string BASENAME;

	static std::string BASENAME_PARENT_PREFIX;

	static std::string BASENAME_PARENT;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	RuntimeID()
	: BF( )
	{
		//!! NOTHING
	}

	RuntimeID(_RuntimeID_ * anElement)
	: BF( anElement )
	{
		//!! NOTHING
	}

	RuntimeID(const RuntimeID & aModel, const RuntimeID & aParent,
			int aPid, avm_offset_t anOffset, InstanceOfMachine * anInstance)
	: BF( new _RuntimeID_(aModel.rid_pointer(),
			aParent.rid_pointer(), aPid, anOffset, anInstance) )
	{
		initialize();
	}

	RuntimeID(const RuntimeID & aParent, int aPid,
			avm_offset_t anOffset, InstanceOfMachine * anInstance)
	: BF( new _RuntimeID_(nullptr,
			aParent.rid_pointer(), aPid, anOffset, anInstance) )
	{
		initialize();
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	RuntimeID(const RuntimeID & aRID)
	: BF( aRID )
	{
		//!! NOTHING
	}

	explicit RuntimeID(const BF & other)
	: BF( ( other.is< RuntimeID >() ) ? other : RuntimeID::nullref() )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( other.invalid() || other.is< AvmCode >() )
				<< "Invalid Constructor Cast of a BF to a RuntimeID !!!"
				<< SEND_EXIT;
	}


	/**
	 * CONSTRUCTOR
	 * other
	 */
	void create(int aPid, avm_offset_t anOffset, InstanceOfMachine * anInstance)
	{
		release( new _RuntimeID_(nullptr, nullptr, aPid, anOffset, anInstance) );
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~RuntimeID()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static RuntimeID & nullref()
	{
		static RuntimeID _NULL_;

		return( _NULL_ );
	}


	/**
	 * initialize
	 * finalize
	 */
	void initialize();

	inline void finalize()
	{
		// Attention:> Necessaire pour briser des references circulaires !!!!
		rid_pointer()->onRunning.destroy();
	}


	/**
	 * GETTER  API
	 * Specifier
	 */
	const Specifier & getSpecifier() const;


	/**
	 * CAST
	 */
	inline _RuntimeID_ * rid_pointer() const
	{
		return( static_cast< _RuntimeID_ * >( base_this_type::mPTR )  );
	}


	/**
	 * GETTER - SETTER
	 * mNameID
	 */
	inline bool isDynamicLoaded() const
	{
		return( rid_pointer()->mDynamicLoaded );
	}

	inline void setDynamicLoaded(bool isDynamic = true)
	{
		rid_pointer()->mDynamicLoaded = isDynamic;
	}

	inline bool isStaticLoaded() const
	{
		return( not rid_pointer()->mDynamicLoaded );
	}

	/**
	 * ASSIGNMENT
	 */
	inline RuntimeID & operator=(const BF & other)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT(
				other.invalid() || other.is< RuntimeID >() )
				<< "Invalid Assignment Cast of a BF to a RuntimeID !!!"
				<< SEND_EXIT;

		if( base_this_type::mPTR != other.raw_pointer() )
		{
			release_acquire( other.raw_pointer() );
		}
		return( *this );
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	inline int compare(const RuntimeID & other) const
	{
		return( (base_this_type::mPTR == other.base_this_type::mPTR ) ? 0 :
				rid_pointer()->getFullyQualifiedNameID().compare(
						other.rid_pointer()->getFullyQualifiedNameID()) );
	}

	inline bool operator==(const RuntimeID & other) const
	{
		return( base_this_type::mPTR == other.base_this_type::mPTR );
	}

	inline bool operator==(const BF & other) const
	{
		return( base_this_type::mPTR == other.raw_pointer() );
	}


	inline bool operator!=(const RuntimeID & other) const
	{
		return( base_this_type::mPTR != other.base_this_type::mPTR );
	}

	inline bool operator!=(const BF & other) const
	{
		return( base_this_type::mPTR != other.raw_pointer() );
	}


	/**
	 * GETTER - SETTER
	 * mFullyQualifiedNameID
	 */
	std::string getFullyQualifiedNameID() const;

	inline bool isLocationID(const std::string & aLocationID) const
	{
		return( rid_pointer()->isLocationID(aLocationID) );
	}

	/**
	 * GETTER - SETTER
	 * mQualifiedNameID
	 */
	inline std::string getQualifiedNameID() const
	{
		return( rid_pointer()->mQualifiedNameID );
	}

	inline void setQualifiedNameID(const std::string & anUfid)
	{
		rid_pointer()->mQualifiedNameID = anUfid;
	}

	/**
	 * GETTER - SETTER
	 * mNameID
	 */
	inline std::string getNameID() const
	{
		return( rid_pointer()->getNameID() );
	}

	inline std::string getPortableNameID() const
	{
		return( rid_pointer()->getPortableNameID() );
	}

	inline std::string getUniqNameID() const
	{
		return( rid_pointer()->getUniqNameID() );
	}

	inline void setNameID(const std::string & aNameID)
	{
		rid_pointer()->setNameID( aNameID );
	}

	inline bool fqnEndsWith(const std::string & aQualifiedNameID) const
	{
		return( rid_pointer()->fqnEndsWith(aQualifiedNameID) );
	}


	/**
	 * GETTER - SETTER
	 * mPid
	 */
	inline int getRid() const
	{
		return( rid_pointer()->mRid );
	}

	inline std::string strPid() const
	{
		return( OSS() << BASENAME << getRid() );
	}

	inline std::string strPPid() const
	{
		return( OSS() << BASENAME_PARENT << getPRid() );
	}

	inline std::string strUniqId() const
	{
		return( OSS() << BASENAME << getRid() << ":" << getNameID() );
	}


	/**
	 * Util for shortcut
	 */
	inline static RuntimeID smartPointerOf(_RuntimeID_ * anElement)
	{
		if( anElement != nullptr )
		{
			anElement->incrRefCount();

			return( RuntimeID( anElement ) );
		}
		else
		{
			return( RuntimeID::nullref() );
		}
	}

	inline static int ridOf(_RuntimeID_ * anElement)
	{
		return( ( anElement != nullptr ) ? anElement->mRid : -1 );
	}


	/**
	 * GETTER - SETTER
	 * mParent
	 */
	inline RuntimeID getPRID() const
	{
		return( smartPointerOf( rid_pointer()->mParent ) );
	}

	inline bool hasPRID() const
	{
		return( rid_pointer()->mParent!= nullptr );
	}

	inline int getPRid() const
	{
		return( ridOf( rid_pointer()->mParent ) );
	}

	inline int getParentOffset() const
	{
		return( ( rid_pointer()->mParent != nullptr ) ?
				rid_pointer()->mParent->mOffset : 0 );
	}


	/**
	 * GETTER - SETTER
	 * mOffset
	 */
	inline avm_offset_t getOffset() const
	{
		return( rid_pointer()->mOffset );
	}


	/**
	 * GETTER - SETTER
	 * mInstance
	 * son Executable
	 * ses variables
	 */

	inline InstanceOfMachine * getInstance() const
	{
		return( rid_pointer()->mInstance );
	}

	inline bool hasInstance() const
	{
		return( rid_pointer()->mInstance != nullptr );
	}


	const InstanceOfMachine * getModelInstance() const;

	bool hasModelInstance() const;


	ExecutableForm & refExecutable() const;

	ExecutableForm * getExecutable() const;

	bool hasExecutable() const;


	const BF & getVariable(avm_offset_t offset) const;

	InstanceOfData * rawVariable(avm_offset_t offset) const;

	bool hasVariable() const;

	bool hasConstVariable() const;

	/**
	 * GETTER - SETTER
	 * Instance->mOnCreate
	 */
	const BFCode & getOnCreate() const;

	bool hasOnCreate() const;

	/**
	 * GETTER - SETTER
	 * Instance->mOnStart
	 */
	const BFCode & getOnStart() const;

	bool hasOnStart() const;


	/**
	 * GETTER - SETTER
	 * mRunning
	 */
	inline const BFCode & getOnRunning() const
	{
		return( rid_pointer()->onRunning );
	}

	inline bool hasOnRunning() const
	{
		return( rid_pointer()->onRunning.valid() );
	}

	inline void setOnRunning(const BFCode & aProgram)
	{
		rid_pointer()->onRunning = aProgram;
	}


	inline RuntimeID getModel() const
	{
		return( smartPointerOf( rid_pointer()->mModel ) );
	}

	inline int getModelRid() const
	{
		return( ridOf( rid_pointer()->mModel ) );
	}

	inline bool hasModel() const
	{
		return( rid_pointer()->mModel != nullptr );
	}


	/**
	 * GETTER - SETTER
	 * mParent
	 */
	inline RuntimeID getParent() const
	{
		return( smartPointerOf( rid_pointer()->mParent ) );
	}

	inline int getParentRid() const
	{
		return( ridOf( rid_pointer()->mParent ) );
	}

	inline bool hasParent() const
	{
		return( rid_pointer()->mParent != nullptr );
	}


	/**
	 * GETTER - SETTER
	 * Ancestor
	 */
	inline bool isAncestorOf(const RuntimeID & aRID) const
	{
		return( aRID.valid() && aRID.hasAsAncestor( *this ) );
	}

	bool hasAsAncestor(const RuntimeID & aRID) const;

	bool hasAsAncestor(const InstanceOfMachine & anInstance) const;

	RuntimeID getAncestor(const InstanceOfMachine & anInstance) const;

	RuntimeID getAncestorContaining(const BaseInstanceForm & anInstance) const;


	/**
	 * GETTER - SETTER
	 * mCompositeComponent
	 */
	inline RuntimeID getCompositeComponent() const
	{
		if( rid_pointer()->mCompositeComponent != nullptr )
		{
			rid_pointer()->mCompositeComponent->incrRefCount();
		}

		return( RuntimeID( rid_pointer()->mCompositeComponent) );
	}

	inline int getCompositeComponentRid() const
	{
		return( ( hasCompositeComponent() ) ?
				rid_pointer()->mCompositeComponent->mRid : -1 );
	}

	inline bool hasCompositeComponent() const
	{
		return( rid_pointer()->mCompositeComponent != nullptr );
	}


	/**
	 * GETTER - SETTER
	 * mCompositeComponentParent
	 */
	inline RuntimeID getCompositeComponentParent() const
	{
		if( rid_pointer()->mCompositeComponentParent != nullptr )
		{
			rid_pointer()->mCompositeComponentParent->incrRefCount();
		}

		return( RuntimeID(
				rid_pointer()->mCompositeComponentParent ) );
	}

	inline int getCompositeComponentParentRid() const
	{
		return( ridOf( rid_pointer()->mCompositeComponentParent ) );
	}

	inline bool hasCompositeComponentParent() const
	{
		return( rid_pointer()->mCompositeComponentParent != nullptr );
	}


	/**
	 * GETTER - SETTER
	 * the Lifeline Ancestor container
	 */
	RuntimeID getLifeline(const InstanceOfMachine & aMachine) const;

	RuntimeID getLifeline(const InstanceOfPort & aPort) const;

	inline RuntimeID getLifeline() const
	{
		return( smartPointerOf( rid_pointer()->mLifeline ) );
	}

	inline int getLifelineRid() const
	{
		return( ridOf( rid_pointer()->mLifeline ) );
	}

	inline bool hasLifeline() const
	{
		return( rid_pointer()->mLifeline != nullptr );
	}



	/**
	 * GETTER - SETTER
	 * the Communicator Ancestor container
	 */
	RuntimeID getCommunicator(const InstanceOfMachine & aMachine) const;

	RuntimeID getCommunicator(const InstanceOfPort & aPort) const;

	inline RuntimeID getCommunicator() const
	{
		return( smartPointerOf( rid_pointer()->mCommunicator ) );
	}

	inline int getCommunicatorRid() const
	{
		return( ridOf( rid_pointer()->mCommunicator ) );
	}

	inline bool hasCommunicator() const
	{
		return( rid_pointer()->mCommunicator != nullptr );
	}



	/**
	 * GETTER - SETTER
	 * the first hierarchical main Component container
	 */
	inline RuntimeID getComponentSelf() const
	{
		return( smartPointerOf( rid_pointer()->mComponentSelf ) );
	}

	inline int getComponentSelfRid() const
	{
		return( ridOf( rid_pointer()->mComponentSelf ) );
	}

	inline bool hasComponentSelf() const
	{
		return( rid_pointer()->mComponentSelf != nullptr );
	}


	/**
	 * GETTER - SETTER
	 * the first hierarchical main Component container
	 */
	inline RuntimeID getComponentParent() const
	{
		return( smartPointerOf( rid_pointer()->mComponentParent ) );
	}

	inline int getComponentParentRid() const
	{
		return( ridOf( rid_pointer()->mComponentParent ) );
	}

	inline bool hasComponentParent() const
	{
		return( rid_pointer()->mComponentParent != nullptr );
	}


	/**
	 * GETTER - SETTER
	 * the first hierarchical main Component container
	 */
	inline RuntimeID getComponentCommunicator() const
	{
		if( rid_pointer()->mComponentCommunicator != nullptr )
		{
			rid_pointer()->mComponentCommunicator->incrRefCount();
		}

		return( RuntimeID( rid_pointer()->mComponentCommunicator) );
	}

	inline int getComponentCommunicatorRid() const
	{
		return( ridOf( rid_pointer()->mComponentCommunicator ) );
	}

	inline bool hasComponentCommunicator() const
	{
		return( rid_pointer()->mComponentCommunicator != nullptr );
	}


   /**
	 * Serialization
	 */
	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const override
	{
		StringOutStream oss(indent);

		toStream(oss);

		return( oss.str() );
	}

	inline virtual std::string str() const override
	{
		return( ( base_this_type::mPTR == nullptr ) ?
				"RuntimeID<null>"  : rid_pointer()->str() );
	}


	inline virtual void AVM_DEBUG_REF_COUNTER(OutStream & out) const override
	{
		if( base_this_type::mPTR != nullptr )
		{
			base_this_type::mPTR->AVM_DEBUG_REF_COUNTER(out);
		}
		else
		{
			out << "RuntimeID<null, ref:0>" << std::flush;
		}
	}

	inline virtual std::string AVM_DEBUG_REF_COUNTER() const override
	{
		return( ( base_this_type::mPTR != nullptr )
				? base_this_type::mPTR->AVM_DEBUG_REF_COUNTER()
				: "RuntimeID<null, ref:0>" );
	}

	inline virtual std::string strHeader() const override
	{
		return( ( base_this_type::mPTR == nullptr ) ?
				"RuntimeID<null>"  : rid_pointer()->strHeader() );
	}

	inline virtual void strHeader(OutStream & out) const override
	{
		if( base_this_type::mPTR != nullptr )
		{
			rid_pointer()->strHeader(out);
		}
		else
		{
			out << "RuntimeID<null>" << std::flush;
		}
	}


	inline virtual void toStream(OutStream & out) const override
	{
		if( base_this_type::mPTR != nullptr )
		{
			rid_pointer()->toStream(out);
		}
		else
		{
			out << "RuntimeID<null>" << std::flush;
		}
	}

	/*
	 * !UNUSED!
	inline static void toStream(OutStream & out,
			const Vector< RuntimeID > & aTable,
			const std::string & aSectionName = "child")
	{
		out << TAB << aSectionName;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM

		out << EOL_INCR_INDENT;
		Vector< RuntimeID >::const_iterator it = aTable.begin();
		Vector< RuntimeID >::const_iterator itEnd = aTable.end();
		for( ; it != itEnd ; ++it )
		{
	AVM_IF_DEBUG_LEVEL_GTE_HIGH

			(*it).toStream(out);

	AVM_DEBUG_ELSE

			out << TAB << (*it).getFullyQualifiedNameID() << EOL;

	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
		}
		out << DECR_INDENT;

AVM_ELSEIF_DEBUG_LEVEL_GTE_LOW

		out << " = [| ";
		Vector< RuntimeID >::const_iterator it = aTable.begin();
		Vector< RuntimeID >::const_iterator itEnd = aTable.end();
		for( ; it != itEnd ; ++it )
		{
			out << (*it).getOffset() << " ";
		}
		out << "|];" << EOL;

AVM_ENDIF_DEBUG_LEVEL_GTE_LOW

		out << std::flush;
	}
	* !UNUSED!
	*/

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION for SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class TableOfRuntimeID final :  public AvmObject ,
		public Vector< RuntimeID >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TableOfRuntimeID )
{

	AVM_DECLARE_CLONABLE_BASE_CLASS( TableOfRuntimeID )


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TableOfRuntimeID()
	: AvmObject( ),
	Vector< RuntimeID >()
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TableOfRuntimeID(const TableOfRuntimeID & aTable)
	: AvmObject( aTable ),
	Vector< RuntimeID >( aTable )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~TableOfRuntimeID()
	{
		//!! NOTHING
	}

};


}

#endif /*RUNTIMEFORMID_H_*/

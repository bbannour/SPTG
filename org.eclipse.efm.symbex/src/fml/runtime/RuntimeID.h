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

#include <common/AvmPointer.h>
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


class _RuntimeID_ :
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
	inline std::string getQualifiedNameID() const
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
	inline virtual const std::string & getNameID() const
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
	ExecutableForm * getExecutable() const;

	/**
	 * mRID of shortcut
	 */
	inline static int mRidOf(_RuntimeID_ * anElement)
	{
		return( ( anElement != NULL ) ? anElement->mRid : -1 );
	}

	/**
	 * Serialization
	 */
	inline virtual std::string str() const
	{
		return( mQualifiedNameID );
	}

	inline virtual std::string strHeader() const
	{
		return( mQualifiedNameID );
	}

	inline virtual void strHeader(OutStream & os) const
	{
		os << mQualifiedNameID;
	}

	virtual void toStream(OutStream & os) const;

};


class RuntimeID :
		public BF,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( RuntimeID )
{

private:
	/**
	 * TYPEDEF
	 */
	typedef BF base_this_type;


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
	: BF( new _RuntimeID_(NULL,
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
	: BF( ( other.is< RuntimeID >() ) ? other : RuntimeID::REF_NULL )
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
		release( new _RuntimeID_(NULL, NULL, aPid, anOffset, anInstance) );
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~RuntimeID()
	{
		//!! NOTHING
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

	inline void setNameID(const std::string & aNameID)
	{
		rid_pointer()->setNameID( aNameID );
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
		return( OSS() << "pid#" << getRid() );
	}

	inline std::string strUniqId() const
	{
		return( OSS() << "pid#" << getRid() << ":" << getNameID() );
	}


	/**
	 * Util for shortcut
	 */
	inline static RuntimeID smartPointerOf(_RuntimeID_ * anElement)
	{
		if( anElement != NULL )
		{
			anElement->incrRefCount();
		}

		return( RuntimeID( anElement ) );
	}

	inline static int mRidOf(_RuntimeID_ * anElement)
	{
		return( ( anElement != NULL ) ? anElement->mRid : -1 );
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
		return( rid_pointer()->mParent!= NULL );
	}

	inline int getPRid() const
	{
		return( mRidOf( rid_pointer()->mParent ) );
	}

	inline int getPOffset() const
	{
		return( ( rid_pointer()->mParent != NULL ) ?
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

	inline void setOffset(avm_offset_t anOffset)
	{
		rid_pointer()->mOffset = anOffset;
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
		return( rid_pointer()->mInstance != NULL );
	}


	const InstanceOfMachine * getModelInstance() const;

	bool hasModelInstance() const;


	ExecutableForm * getExecutable() const;

	bool hasExecutable() const;


	const BF & getVariable(avm_offset_t offset) const;

	InstanceOfData * rawVariable(avm_offset_t offset) const;

	bool hasVariable() const;


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
		return( mRidOf( rid_pointer()->mModel ) );
	}

	inline bool hasModel() const
	{
		return( rid_pointer()->mModel != NULL );
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
		return( mRidOf( rid_pointer()->mParent ) );
	}

	inline bool hasParent() const
	{
		return( rid_pointer()->mParent != NULL );
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

	bool hasAsAncestor(const InstanceOfMachine * anInstance) const;

	RuntimeID getAncestorContaining(const BaseInstanceForm * anInstance) const;


	/**
	 * GETTER - SETTER
	 * mCompositeComponent
	 */
	inline RuntimeID getCompositeComponent() const
	{
		if( rid_pointer()->mCompositeComponent != NULL )
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
		return( rid_pointer()->mCompositeComponent != NULL );
	}


	/**
	 * GETTER - SETTER
	 * mCompositeComponentParent
	 */
	inline RuntimeID getCompositeComponentParent() const
	{
		if( rid_pointer()->mCompositeComponentParent != NULL )
		{
			rid_pointer()->mCompositeComponentParent->incrRefCount();
		}

		return( RuntimeID(
				rid_pointer()->mCompositeComponentParent ) );
	}

	inline int getCompositeComponentParentRid() const
	{
		return( mRidOf( rid_pointer()->mCompositeComponentParent ) );
	}

	inline bool hasCompositeComponentParent() const
	{
		return( rid_pointer()->mCompositeComponentParent != NULL );
	}


	/**
	 * GETTER - SETTER
	 * the Lifeline Ancestor container
	 */
	RuntimeID getLifeline(InstanceOfMachine * aMachine) const;

	RuntimeID getLifeline(InstanceOfPort * aPort) const;

	inline RuntimeID getLifeline() const
	{
		return( smartPointerOf( rid_pointer()->mLifeline ) );
	}

	inline int getLifelineRid() const
	{
		return( mRidOf( rid_pointer()->mLifeline ) );
	}

	inline bool hasLifeline() const
	{
		return( rid_pointer()->mLifeline != NULL );
	}



	/**
	 * GETTER - SETTER
	 * the Communicator Ancestor container
	 */
	RuntimeID getCommunicator(InstanceOfMachine * aMachine) const;

	RuntimeID getCommunicator(InstanceOfPort * aPort) const;

	inline RuntimeID getCommunicator() const
	{
		return( smartPointerOf( rid_pointer()->mCommunicator ) );
	}

	inline int getCommunicatorRid() const
	{
		return( mRidOf( rid_pointer()->mCommunicator ) );
	}

	inline bool hasCommunicator() const
	{
		return( rid_pointer()->mCommunicator != NULL );
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
		return( mRidOf( rid_pointer()->mComponentSelf ) );
	}

	inline bool hasComponentSelf() const
	{
		return( rid_pointer()->mComponentSelf != NULL );
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
		return( mRidOf( rid_pointer()->mComponentParent ) );
	}

	inline bool hasComponentParent() const
	{
		return( rid_pointer()->mComponentParent != NULL );
	}


	/**
	 * GETTER - SETTER
	 * the first hierarchical main Component container
	 */
	inline RuntimeID getComponentCommunicator() const
	{
		if( rid_pointer()->mComponentCommunicator != NULL )
		{
			rid_pointer()->mComponentCommunicator->incrRefCount();
		}

		return( RuntimeID( rid_pointer()->mComponentCommunicator) );
	}

	inline int getComponentCommunicatorRid() const
	{
		return( mRidOf( rid_pointer()->mComponentCommunicator ) );
	}

	inline bool hasComponentCommunicator() const
	{
		return( rid_pointer()->mComponentCommunicator != NULL );
	}


	/**
	 * DEFAULT NULL
	 */
	static RuntimeID REF_NULL;


   /**
	 * Serialization
	 */
	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream oss(indent);

		toStream(oss);

		return( oss.str() );
	}

	inline virtual std::string str() const
	{
		return( ( base_this_type::mPTR == NULL ) ?
				"RuntimeID<null>"  : rid_pointer()->str() );
	}


	inline virtual void AVM_DEBUG_REF_COUNTER(OutStream & os) const
	{
		if( base_this_type::mPTR != NULL )
		{
			base_this_type::mPTR->AVM_DEBUG_REF_COUNTER(os);
		}
		else
		{
			os << "RuntimeID<null, ref:0>" << std::flush;
		}
	}

	inline virtual std::string AVM_DEBUG_REF_COUNTER() const
	{
		return( ( base_this_type::mPTR != NULL )
				? base_this_type::mPTR->AVM_DEBUG_REF_COUNTER()
				: "RuntimeID<null, ref:0>" );
	}

	inline virtual std::string strHeader() const
	{
		return( ( base_this_type::mPTR == NULL ) ?
				"RuntimeID<null>"  : rid_pointer()->strHeader() );
	}

	inline virtual void strHeader(OutStream & os) const
	{
		if( base_this_type::mPTR != NULL )
		{
			rid_pointer()->strHeader(os);
		}
		else
		{
			os << "RuntimeID<null>" << std::flush;
		}
	}


	inline virtual void toStream(OutStream & os) const
	{
		if( base_this_type::mPTR != NULL )
		{
			rid_pointer()->toStream(os);
		}
		else
		{
			os << "RuntimeID<null>" << std::flush;
		}
	}

	/*
	 * !UNUSED!
	inline static void toStream(OutStream & os,
			const Vector< RuntimeID > & aTable,
			const std::string & aSectionName = "child")
	{
		os << TAB << aSectionName;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM

		os << EOL_INCR_INDENT;
		Vector< RuntimeID >::const_iterator it = aTable.begin();
		Vector< RuntimeID >::const_iterator itEnd = aTable.end();
		for( ; it != itEnd ; ++it )
		{
	AVM_IF_DEBUG_LEVEL_GTE_HIGH

			(*it).toStream(os);

	AVM_DEBUG_ELSE

			os << TAB << (*it).getFullyQualifiedNameID() << EOL;

	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
		}
		os << DECR_INDENT;

AVM_ELSEIF_DEBUG_LEVEL_GTE_LOW

		os << " = [| ";
		Vector< RuntimeID >::const_iterator it = aTable.begin();
		Vector< RuntimeID >::const_iterator itEnd = aTable.end();
		for( ; it != itEnd ; ++it )
		{
			os << (*it).getOffset() << " ";
		}
		os << "|];" << EOL;

AVM_ENDIF_DEBUG_LEVEL_GTE_LOW

		os << std::flush;
	}
	* !UNUSED!
	*/

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION for SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class TableOfRuntimeID :  public AvmObject ,
	public Vector< RuntimeID >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TableOfRuntimeID )
{

	AVM_DECLARE_CLONABLE_CLASS( TableOfRuntimeID )


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


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION for SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

AVM_DEFINE_AP_CLASS( TableOfRuntimeID )



}

#endif /*RUNTIMEFORMID_H_*/

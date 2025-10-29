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
#ifndef EXECUTIONCONTEXT_H_
#define EXECUTIONCONTEXT_H_

#include <common/Element.h>
#include <fml/runtime/ExecutionContextFlags.h>

#include <collection/TypedefCollection.h>

#include <common/BF.h>

#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/ExecutionInformation.h>


namespace sep
{

class AbstractProcessorUnit;
class ExecutionContext;
class RuntimeID;


/**
 * TYPEDEF
 */
typedef List  < ExecutionContext * >  ListOfExecutionContext;
typedef Vector< ExecutionContext * >  VectorOfExecutionContext;

typedef List  < const ExecutionContext * >  ListOfConstExecutionContext;
typedef Vector< const ExecutionContext * >  VectorOfConstExecutionContext;


class ExecutionContextHeader final : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionContextHeader )
{

	AVM_DECLARE_CLONABLE_CLASS( ExecutionContextHeader )


public:
	/**
	* ATTRIBUTES
	* static
	*/
	static std::uint32_t ID_NUMBER;

protected:
	/**
	 * ATTRIBUTES
	 */
	std::uint32_t mIdNumber;
	std::uint32_t mEvalNumber;

	std::uint32_t mHeight;
	std::uint32_t mWidth;

	std::uint8_t  mWeight;



public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionContextHeader()
	: Element( CLASS_KIND_T( ExecutionContextHeader ) ),
	mIdNumber( ID_NUMBER++ ),
	mEvalNumber( 0 ),
	mHeight( 0 ),
	mWidth( 1 ),
	mWeight( 0 )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutionContextHeader(const ExecutionContextHeader & aHeader)
	: Element( aHeader ),
	mIdNumber( ID_NUMBER++ ),
	mEvalNumber( aHeader.mEvalNumber ),
	mHeight( aHeader.mHeight ),
	mWidth( aHeader.mWidth ),
	mWeight( 0 )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Other
	 */
	ExecutionContextHeader(std::uint32_t aHeight, std::uint32_t aWidth)
	: Element( CLASS_KIND_T( ExecutionContextHeader ) ),
	mIdNumber( ID_NUMBER++ ),
	mEvalNumber( 0 ),
	mHeight( aHeight ),
	mWidth( aWidth ),
	mWeight( 0 )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionContextHeader()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * ID_NUMBER
	 */
	inline static std::uint32_t getCreateCounter()
	{
		return( ID_NUMBER );
	}

	inline static void setCreateCounter(std::uint32_t aCreateCounter)
	{
		ID_NUMBER = aCreateCounter;
	}


	/**
	 * GETTER - SETTER
	 * mIdNumber
	 */
	inline std::uint32_t getIdNumber() const
	{
		return( mIdNumber );
	}

	inline void setIdNumber(std::uint32_t anIdNumber)
	{
		mIdNumber = anIdNumber;
	}


	/**
	 * GETTER - SETTER
	 *
	 */
	inline std::uint32_t getEvalNumber() const
	{
		return( mEvalNumber );
	}

	inline void setEvalNumber(std::uint32_t anEvalNumber)
	{
		mEvalNumber = anEvalNumber;
	}


	/**
	 * GETTER - SETTER
	 * mHeight
	 */
	inline std::uint32_t getHeight() const
	{
		return( mHeight );
	}

	inline void setHeight(std::uint32_t aHeight)
	{
		mHeight = aHeight;
	}


	/**
	 * GETTER - SETTER
	 * mWidth
	 */
	inline std::uint32_t getWidth() const
	{
		return( mWidth );
	}

	inline void setWidth(std::uint32_t aWidth)
	{
		mWidth = aWidth;
	}


	/**
	 * GETTER - SETTER
	 * mWeight
	 */
	inline std::uint8_t getWeight() const
	{
		return( mWeight );
	}

	inline std::uint32_t getStrWeight() const
	{
		return( mWeight );
	}

	inline static std::uint8_t getWeightMax()
	{
		return( UINT8_MAX );
	}

	inline bool isWeightMax() const
	{
		return( mWeight == UINT8_MAX );
	}

	inline bool isWeight(std::uint8_t aWeight) const
	{
		return( mWeight == aWeight );
	}


	inline void setWeight(std::uint8_t aWeight)
	{
		mWeight = aWeight;
	}


	inline void setWeightMax()
	{
		mWeight = UINT8_MAX;
	}


	inline void decrWeight(std::uint8_t aWeight = 1)
	{
		if( mWeight != UINT8_MAX )
		{
			mWeight -= aWeight;
		}
	}

	inline void incrWeight(std::uint8_t aWeight = 1)
	{
		if( mWeight != UINT8_MAX )
		{
			mWeight += aWeight;
		}
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */

	inline virtual std::string str() const override
	{
		StringOutStream oss;

		oss <<   "Id:" << getIdNumber()	<< ", Ev:" << getEvalNumber()
			<<  ", H:" << getHeight()	<<  ", W:" << getWidth();
		if( getWeight() > 0 )
		{
			oss << ", Q:" << getStrWeight();
		}

		return( oss.str() );
	}

	virtual void toStream(OutStream & out) const override
	{
		out << TAB
			<<    "Id:" << getIdNumber() << " , Ev:" << getEvalNumber()
			<<  " , H:" << getHeight()   <<  " , W:" << getWidth()
			<<  " , Q:" << getStrWeight()
			<< EOL_FLUSH;
	}

};



class ExecutionContext final : public Element ,
		public ExecutionContextFlagsImpl ,
		AVM_INJECT_STATIC_NULL_REFERENCE( ExecutionContext ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionContext )
{

	AVM_DECLARE_CLONABLE_CLASS( ExecutionContext )

	AVM_TYPEDEF_COLLECTION_CLASS( ExecutionContext )

public:
	/**
	 * TRACE CONSTANT
	 */
	static std::size_t EC_CHILD_TRACE_DEFAULT_SIZE;

	static std::size_t EXECUTION_CONTEXT_CHILD_TRACE_MAX;

	/*
	 * DEFAULT NO CHILD EMPTY LIST
	 */
	static ListOfExecutionContext NO_CHILD;


public:
	typedef ListOfExecutionContext::iterator        rw_child_iterator;

	typedef ListOfExecutionContext::const_iterator  child_iterator;


	typedef AvmPointer< ExecutionContextHeader , DestroyElementPolicy >  header_type;


   /**
	* ATTRIBUTES
	*/
	ExecutionContext * mContainer;

	ListOfExecutionContext mChildContexts;

	header_type mHeader;

	ExecutionData mExecutionData;

	BF mInformation;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionContext()
	: Element( CLASS_KIND_T( ExecutionContext ) ),
	ExecutionContextFlagsImpl( ),
	mContainer( nullptr ),
	mChildContexts( ),
	mHeader(),
	mExecutionData( ),
	mInformation( )
	{
		//!! NOTHING

		AVM_OS_TRACE << ">>> construct ExecutionContext @ " << std::addressof(* this) << std::endl;
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutionContext(const ExecutionContext & aContext)
	: Element( aContext ),
	ExecutionContextFlagsImpl( aContext ),
	mContainer( aContext.mContainer ),
	mChildContexts( aContext.mChildContexts ),

	mHeader( new ExecutionContextHeader(aContext.getHeader()) ),
	mExecutionData( aContext.mExecutionData ),
	mInformation( aContext.mInformation )
	{
		//!! NOTHING

		AVM_OS_TRACE << ">>> construct ExecutionContext @ " << std::addressof(* this) << std::endl;
	}

	ExecutionContext(ExecutionContext * aContainer,
			const ExecutionContext & aContext, bool withChild)
	: Element( aContext ),
	ExecutionContextFlagsImpl( aContext ),
	mContainer( aContainer ),
	mChildContexts( withChild ? aContext.mChildContexts : NO_CHILD ),

	mHeader( new ExecutionContextHeader(aContext.getHeader()) ),
	mExecutionData( aContext.mExecutionData ),
	mInformation( aContext.mInformation )
	{
		//!! NOTHING

//AVM_OS_TRACE << ">>> construct ExecutionContext @ " << std::addressof(* this) << std::endl;
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	ExecutionContext(ExecutionData & anExecutionData,
			std::uint32_t aHeight, std::uint32_t aWidth)
	: Element( CLASS_KIND_T( ExecutionContext ) ),
	ExecutionContextFlagsImpl( ),
	mContainer( nullptr ),
	mChildContexts( ),

	mHeader( new ExecutionContextHeader(aHeight , aWidth) ),
	mExecutionData( anExecutionData ),
	mInformation( )
	{
		anExecutionData.setExecutionContext( this );

//AVM_OS_TRACE << ">>> construct ExecutionContext @ " << std::addressof(* this) << std::endl;
	}

	ExecutionContext(const ExecutionContext & aContainer,
			ExecutionData & anExecutionData,
			std::uint32_t aHeight, std::uint32_t aWidth)
	: Element( CLASS_KIND_T( ExecutionContext ) ),
	ExecutionContextFlagsImpl( ),
	mContainer( const_cast< ExecutionContext * >(& aContainer) ),
	mChildContexts( ),

	mHeader( new ExecutionContextHeader(aHeight , aWidth) ),
	mExecutionData( anExecutionData ),
	mInformation( )
	{
		anExecutionData.setExecutionContext( this );

//AVM_OS_TRACE << ">>> construct ExecutionContext @ " << std::addressof(* this) << std::endl;
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionContext()
	{
		sep::destroy( mChildContexts );

		if( hasContainer() )
		{
			//getContainer()->remove(this);
		}

//AVM_OS_COUT << ">>> destroy ExecutionContext @ "<< std::addressof(* this) << std::endl;
	}

	inline void destroy()
	{
		sep::destroy( mChildContexts );

		mHeader.destroy();

		mExecutionData.destroy();

		mInformation.destroy();
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static ExecutionContext & nullref()
	{
		static ExecutionContext _NULL_;

		return( _NULL_ );
	}


	/**
	 * GETTER - SETTER
	 * mContainer
	 */
	inline ExecutionContext * getContainer() const
	{
		return( mContainer );
	}

	inline const ExecutionContext & refContainer() const
	{
		return( * mContainer );
	}


	inline bool hasContainer() const
	{
		return( mContainer != nullptr );
	}

	inline void setContainer(ExecutionContext * anEC)
	{
		mContainer = anEC;
	}


	/**
	 * CLONE ALL DATA
	 * CHILD EMPTY
	 */
	inline ExecutionContext * cloneData(
			ExecutionContext * aContainer, bool requireWritableExecData) const
	{
		ExecutionContext * aCloneEC =
				new ExecutionContext( aContainer, *this , false );

		if( requireWritableExecData )
		{
			aCloneEC->makeWritableExecutionData();

			aCloneEC->getwExecutionData().setExecutionContext(aCloneEC);
		}

		return( aCloneEC );
	}

	/**
	 * CLONE LEVEL ONE
	 */
	inline ExecutionContext * cloneNode(
			ExecutionContext * aContainer, bool requireWritableExecData) const
	{
		ExecutionContext * aCloneEC =
				new ExecutionContext( aContainer, *this , true );

		if( requireWritableExecData )
		{
			aCloneEC->makeWritableExecutionData();
		}

		return( aCloneEC );
	}

	inline ExecutionContext * cloneNode(bool requireWritableExecData) const
	{
		ExecutionContext * aCloneEC =
				new ExecutionContext( getContainer(), *this , true );

		if( requireWritableExecData )
		{
			aCloneEC->makeWritableExecutionData();
		}

		return( aCloneEC );
	}

	/**
	 * RECURSIVE CLONE
	 */
	ExecutionContext * cloneGraph(
			ExecutionContext * aContainer, bool requireWritableExecData) const
	{
		ExecutionContext * aCloneEC =
				cloneData( aContainer, requireWritableExecData );

		for( const auto & itChildEC : getChildContexts() )
		{
			aCloneEC->appendChildContext(
					itChildEC->cloneGraph( aCloneEC, requireWritableExecData ) );
		}

		return( aCloneEC );
	}


	/**
	 * INITIALIZATION with EXECUTION DATA / CONTEXT
	 */
	inline void initialize(const ExecutionContext & anInitialContext)
	{
		mContainer = anInitialContext.mContainer;
		mChildContexts = anInitialContext.mChildContexts;

		mHeader = anInitialContext.mHeader;
		mExecutionData = anInitialContext.mExecutionData;

		mInformation = anInitialContext.mInformation;
	}

	inline void initialize(const ExecutionData & anInitialData,
			std::uint32_t aHeight = 0, std::uint32_t aWidth = 1)
	{
		mContainer = nullptr;

		mHeader = new ExecutionContextHeader(aHeight, aWidth);
		mExecutionData = anInitialData;
	}


	/**
	 * GETTER
	 * mChildContexts
	 * Iterators
	 */
	inline rw_child_iterator begin()
	{
		return( mChildContexts.begin() );
	}

	inline rw_child_iterator end()
	{
		return( mChildContexts.end() );
	}

	inline rw_child_iterator eraseChildContext(
			const rw_child_iterator & itChildCtx)
	{
		return( mChildContexts.erase( itChildCtx ) );
	}


	inline child_iterator begin() const
	{
		return( mChildContexts.begin() );
	}

	inline child_iterator end() const
	{
		return( mChildContexts.end() );
	}


	/**
	 * GETTER
	 * mChildContexts
	 */
	inline ExecutionContext * firstChildContext() const
	{
		return( mChildContexts.first() );
	}

	inline ExecutionContext * lastChildContext() const
	{
		return( mChildContexts.last() );
	}


	inline bool hasChildContext() const
	{
		return( mChildContexts.nonempty() );
	}

	inline bool noChildContext() const
	{
		return( mChildContexts.empty() );
	}

	inline bool populatedChildContext() const
	{
		return( mChildContexts.populated() );
	}

	inline bool singleChildContext() const
	{
		return( mChildContexts.singleton() );
	}


	inline bool isLeafNode() const
	{
		return( mChildContexts.empty() );
	}

	inline virtual std::size_t size() const override
	{
		return( mChildContexts.size() );
	}


	/**
	 * SETTER
	 * mChildContexts
	 */
	inline void appendChildContext(ExecutionContext * anEC)
	{
		if( anEC->getContainer() == nullptr )
		{
			anEC->setContainer( this );
		}
		else
		{
			AVM_OS_ASSERT_FATAL_ERROR_EXIT( anEC->getContainer() == this )
				<< "The Execution Context< " << anEC->str()
				<< " > has a parent < " << anEC->getContainer()->str()
				<< " > different of his new one < " << this->str() << " > !"
				<< SEND_EXIT;
		}

		mChildContexts.append( anEC );
	}

	inline void spliceChildContext(ListOfExecutionContext & newChildsEC)
	{
		mChildContexts.splice( newChildsEC );
	}

	inline void clearChildContext()
	{
		mChildContexts.clear();
	}

	inline void popLastChildContextTo(ExecutionContext * & anEC)
	{
		mChildContexts.pop_last_to( anEC );
	}

	inline void removeChildContext(ExecutionContext * anEC)
	{
		mChildContexts.remove( anEC );
	}



	inline ListOfExecutionContext & getChildContexts()
	{
		return( mChildContexts );
	}

	inline const ListOfExecutionContext & getChildContexts() const
	{
		return( mChildContexts );
	}

	inline const ListOfExecutionContext & getNext() const
	{
		return( mChildContexts );
	}

	inline bool hasNext() const
	{
		return( mChildContexts.nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mHeader
	 */
	inline const header_type & rawHeader() const
	{
		return( mHeader );
	}

	inline ExecutionContextHeader & getHeader()
	{
		return( *mHeader );
	}

	inline const ExecutionContextHeader & getHeader() const
	{
		return( *mHeader );
	}


	/**
	 * GETTER - SETTER
	 * Container
	 */
	inline  bool isRoot() const
	{
		return( not hasContainer() );
	}

	inline  bool isnotRoot() const
	{
		return( hasContainer() );
	}


	inline ExecutionContext * getPrevious() const
	{
		return( getContainer() );
	}


	inline bool hasPrevious() const
	{
		return( hasContainer() );
	}


	/**
	 * GETTER - SETTER
	 * mHeader trace indices
	 */
	inline static std::uint32_t getCreateCounter()
	{
		return( ExecutionContextHeader::ID_NUMBER );
	}

	inline std::uint32_t getIdNumber() const
	{
		return( getHeader().getIdNumber() );
	}


	inline std::uint32_t getEvalNumber() const
	{
		return( getHeader().getEvalNumber() );
	}

	inline bool isEvaluated() const
	{
		return( getHeader().getEvalNumber() > 0 );
	}

	inline void setEvalNumber(std::uint32_t anEvalNumber)
	{
		getHeader().setEvalNumber(anEvalNumber);
	}


	inline std::uint32_t getHeight() const
	{
		return( getHeader().getHeight() );
	}

	inline void setHeight(std::uint32_t aHeight)
	{
		getHeader().setHeight(aHeight);
	}


	inline std::uint32_t getWidth() const
	{
		return( getHeader().getWidth() );
	}

	inline void setWidth(std::uint32_t aWidth)
	{
		getHeader().setWidth(aWidth);
	}


	inline std::uint8_t getWeight() const
	{
		return( getHeader().getWeight() );
	}

	inline std::uint32_t getStrWeight() const
	{
		return( getHeader().getStrWeight() );
	}

	inline static std::uint8_t getWeightMax()
	{
		return( ExecutionContextHeader::getWeightMax() );
	}

	inline bool isWeightMax() const
	{
		return( getHeader().isWeightMax() );
	}

	inline bool isWeight(std::uint8_t aWeight) const
	{
		return( getHeader().isWeight(aWeight) );
	}


	inline void setWeight(std::uint8_t aWeight)
	{
		getHeader().setWeight(aWeight);
	}

	inline void setWeightMax()
	{
		getHeader().setWeightMax();
	}


	inline std::uint32_t getPrevEvalNumber() const
	{
		return( isRoot() ? 0 : getContainer()->getEvalNumber() );
	}

	inline std::uint32_t getPrevHeight() const
	{
		return( isRoot() ? 0 : getContainer()->getHeight() );
	}

	inline std::uint32_t getPrevIdNumber() const
	{
		return( isRoot() ? 0 : getContainer()->getIdNumber() );
	}

	inline std::uint32_t getPrevWidth() const
	{
		return( isRoot() ? 0 : getContainer()->getWidth() );
	}

	inline std::uint8_t getPrevsWeight() const
	{
		return( isRoot() ? 0 : getContainer()->getWeight() );
	}


	/**
	 * LCA -LCRA
	 */
	const ExecutionContext * LCA(const ExecutionContext * anEC) const ;

	/**
	 * GETTER - SETTER
	 * mExecutionData
	 */
	inline const ExecutionData & getExecutionData() const
	{
		return( mExecutionData );
	}

	inline ExecutionData & getwExecutionData()
	{
		return( mExecutionData );
	}


	inline  bool hasExecutionData() const
	{
		return( mExecutionData.valid() );
	}

	inline void setExecutionData(const ExecutionData & anExecutionData)
	{
		mExecutionData = anExecutionData;
	}

	inline void makeWritableExecutionData()
	{
		mExecutionData.makeWritable();
	}


	/**
	 * TRIVIAL EQUALITY
	 */
	inline bool edTEQ(const ExecutionContext & anEC) const
	{
		return( mExecutionData.isTEQ( anEC.getExecutionData() ) );
	}


	/**
	 * GETTER - SETTER
	 * mRunnableElementTrace
	 */
	inline const BF & getRunnableElementTrace() const
	{
		return( mExecutionData.getRunnableElementTrace() );
	}

	inline bool hasRunnableElementTrace() const
	{
		return( mExecutionData.hasRunnableElementTrace() );
	}

	/**
	 * GETTER - SETTER
	 * mIOElementTrace
	 */
	inline const BF & getIOElementTrace() const
	{
		return( mExecutionData.getIOElementTrace() );
	}

	inline bool hasIOElementTrace() const
	{
		return( mExecutionData.hasIOElementTrace() );
	}


	/**
	 * GETTER - SETTER
	 * ExecutionData::mPathCondition
	 */
	inline const BF & getPathCondition() const
	{
		return( mExecutionData.getPathCondition() );
	}

	/**
	 * GETTER - SETTER
	 * ExecutionData::mPathTimedCondition
	 */
	inline const BF & getPathTimedCondition() const
	{
		return( mExecutionData.getPathTimedCondition() );
	}

	/**
	 * GETTER - SETTER
	 * ExecutionData::mPathCondition AND ExecutionData::mPathTimedCondition
	 */
	inline BF getAllPathCondition() const
	{
		return( mExecutionData.getAllPathCondition() );
	}

	/**
	 * GETTER - SETTER
	 * mNodeCondition
	 */
	inline const BF & getNodeCondition() const
	{
		return( mExecutionData.getNodeCondition() );
	}

	inline bool hasNodeCondition() const
	{
		return( mExecutionData.hasNodeCondition() );
	}

	/**
	 * GETTER - SETTER
	 * mNodeTimedCondition
	 */
	inline const BF & getNodeTimedCondition() const
	{
		return( mExecutionData.getNodeTimedCondition() );
	}

	inline bool hasNodeTimedCondition() const
	{
		return( mExecutionData.hasNodeTimedCondition() );
	}


	/**
	 * GETTER - SETTER
	 * mNodeCondition AND mNodeTimedCondition
	 */
	inline BF getAllNodeCondition() const
	{
		return( mExecutionData.getAllNodeCondition() );
	}

	/**
	 * GETTER - SETTER - TESTER
	 * mInformation
	 */
	inline void addInfo(
			const AbstractProcessorUnit & aProcessor, const BF & aData)
	{
		getUniqInformation()->addInfo(aProcessor, aData);
	}

	inline void addInfo(const AbstractProcessorUnit & aProcessor,
			const BF & anID, const BF & aData)
	{
		getUniqInformation()->addInfo(aProcessor, anID, aData);
	}

	inline static void addInfo(ListOfExecutionContext & listOfEC,
			const AbstractProcessorUnit & aProcessor, const BF & aData)
	{
		for( const auto & itEC : listOfEC )
		{
			itEC->addInfo(aProcessor,aData);
		}
	}

	inline GenericInfoData * getInfo(
			const AbstractProcessorUnit & aProcessor, const BF & anID) const
	{
		return( mInformation.invalid() ?  nullptr :
				mInformation.to< ExecutionInformation >().
				getInfo(aProcessor, anID) );
	}


	inline const BF & getInfoData(
			const IProcessorUnitRegistration & aRegisterTool) const
	{
		return( mInformation.invalid() ?  BF::REF_NULL :
				mInformation.to< ExecutionInformation >().
				getInfoData(aRegisterTool) );
	}

	inline const BF & getInfoData(const AbstractProcessorUnit & aProcessor) const
	{
		return( mInformation.invalid() ?  BF::REF_NULL :
				mInformation.to< ExecutionInformation >().
				getInfoData(aProcessor) );
	}

	inline const BF & getInfoData(
			const AbstractProcessorUnit & aProcessor, const BF & anID) const
	{
		return( mInformation.invalid() ?  BF::REF_NULL :
				mInformation.to< ExecutionInformation >().
				getInfoData(aProcessor, anID) );
	}


	inline const BFList & getInfos() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mInformation )
				<< "Execution Information !!!"
				<< SEND_EXIT;

		return( getInformation()->getInfos() );
	}

	inline bool hasInfo() const
	{
		return( mInformation.valid() &&
				mInformation.to< ExecutionInformation >().hasInfo() );
	}

	inline bool hasInfo(const AbstractProcessorUnit & aProcessor) const
	{
		return( mInformation.valid() && mInformation.to<
				ExecutionInformation >().hasInfo(aProcessor) );
	}

	inline bool noneInfo(const AbstractProcessorUnit & aProcessor) const
	{
		return( mInformation.invalid() || mInformation.to<
				ExecutionInformation >().noneInfo(aProcessor) );
	}

	inline bool hasInfo(
			const AbstractProcessorUnit & aProcessor, const BF & anID) const
	{
		return( mInformation.valid() && mInformation.to<
				ExecutionInformation >().hasInfo(aProcessor, anID) );
	}


	inline bool hasInfoWithData(
			const AbstractProcessorUnit & aProcessor, const BF & aData) const
	{
		return( mInformation.valid() && mInformation.to<
				ExecutionInformation >().hasInfoWithData(aProcessor, aData) );
	}

	inline bool hasInfo(const BF & anID) const
	{
		return( mInformation.valid() &&
				mInformation.to< ExecutionInformation >().hasInfo(anID) );
	}

	inline bool hasInfo(Element * anID) const
	{
		return( mInformation.valid() &&
				mInformation.to< ExecutionInformation >().hasInfo(anID) );
	}


	inline ExecutionInformation * getUniqInformation()
	{
		if( not hasInformation() )
		{
			mInformation.setPointer( new ExecutionInformation() );
		}
		return( mInformation.to_ptr< ExecutionInformation >() );
	}

	inline ExecutionInformation * getInformation() const
	{
		return( mInformation.to_ptr< ExecutionInformation >() );
	}

	inline bool hasInformation() const
	{
		return( mInformation.valid() );
	}

	inline void setInformation(ExecutionInformation * anInformation)
	{
		mInformation.setPointer( anInformation );
	}

	inline void unsetInformation()
	{
		mInformation.setPointer( nullptr );
	}


	/**
	 * Serialization
	 */
	void toDebug(OutStream & out) const;

	void toDebugFet(OutStream & out) const;


	template< class OS_T >
	OS_T & osStrPosition(OS_T & out) const
	{
		out << "Id:" /*<< std::setw(4)*/ << getIdNumber();

		out << " PE:";
		if ( hasContainer() )
		{
			out /*<< std::setw(4)*/ << getContainer()->getEvalNumber();
		}
		else
		{
			out <<  "ROOT";
		}

		out << " H:" /*<< std::setw(4)*/ << getHeight()
			<< " W:" /*<< std::setw(4)*/ << getWidth()
			<< " Q:" /*<< std::setw(2)*/ << getStrWeight();

		return( out );
	}


	inline virtual std::string str() const override
	{
		return( osStrPosition( OSS() << "EC< " ) << " > "
				<< getExecutionData().strStateConf() );
	}

	virtual void toStream(OutStream & out) const override;

	virtual void toFscn(OutStream & out,
			const ExecutionData & aPreviousExecData) const;

	std::string str_min() const;
	std::string str_position() const;

	void traceMinimum(OutStream & out) const;

	void traceDefault(OutStream & out) const;

	inline void traceDefault(PairOutStream & out) const
	{
		traceDefault(out.OS1);
		traceDefault(out.OS2);
	}
	void debugDefault(OutStream & out) const;


	static void traceMinimum(OutStream & out,
			ListOfExecutionContext & listofEC, const std::string & header = "");

	static void traceMinimum(OutStream & out,
			VectorOfExecutionContext & listofEC, const std::string & header = "");


	static void traceDefault(OutStream & out,
			ListOfExecutionContext & listofEC, const std::string & header = "");

	static void traceDefault(OutStream & out,
			VectorOfExecutionContext & listofEC, const std::string & header = "");

	static void debugDefault(OutStream & out,
			ListOfExecutionContext & listofEC, const std::string & header = "");

	static void debugDefault(OutStream & out,
			VectorOfExecutionContext & listofEC, const std::string & header = "");


	void writeTraceAfterExec(OutStream & out) const;
	void traceDefaultPostEval(OutStream & out) const;

	inline void traceDefaultEval(OutStream & out) const
	{
		traceDefault(out);
		if( hasNext() )
		{
			traceDefaultPostEval(out);
		}
	}


	void writeTraceBeforeExec(OutStream & out) const;

	void writeTraceForDeadlock(OutStream & out,
			std::uint32_t nDeadlockCounter) const;

	void writeTraceForRedundancy(OutStream & out,
			ExecutionContext * aRedundantExecContext,
			std::uint32_t nRedundancyCounter) const;

};


} /* namespace sep */

#endif /*EXECUTIONCONTEXT_H_*/

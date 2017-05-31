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

#include <collection/List.h>
#include <collection/Vector.h>

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


class ExecutionContextHeader :
		public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionContextHeader )
{

	AVM_DECLARE_CLONABLE_CLASS( ExecutionContextHeader )


public:
   /**
	* ATTRIBUTES
	* static
	*/
	static avm_uint32_t ID_NUMBER;

protected:
	/**
	 * ATTRIBUTES
	 */
	avm_uint32_t mIdNumber;
	avm_uint32_t mEvalNumber;

	avm_uint32_t mHeight;
	avm_uint32_t mWidth;

	avm_uint8_t  mWeight;



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
	ExecutionContextHeader(avm_uint32_t aHeight, avm_uint32_t aWidth)
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
	inline static avm_uint32_t getCreateCounter()
	{
		return( ID_NUMBER );
	}

	inline static void setCreateCounter(avm_uint32_t aCreateCounter)
	{
		ID_NUMBER = aCreateCounter;
	}


	/**
	 * GETTER - SETTER
	 * mIdNumber
	 */
	inline avm_uint32_t getIdNumber() const
	{
		return( mIdNumber );
	}

	inline void setIdNumber(avm_uint32_t anIdNumber)
	{
		mIdNumber = anIdNumber;
	}


	/**
	 * GETTER - SETTER
	 *
	 */
	inline avm_uint32_t getEvalNumber() const
	{
		return( mEvalNumber );
	}

	inline void setEvalNumber(avm_uint32_t anEvalNumber)
	{
		mEvalNumber = anEvalNumber;
	}


	/**
	 * GETTER - SETTER
	 * mHeight
	 */
	inline avm_uint32_t getHeight() const
	{
		return( mHeight );
	}

	inline void setHeight(avm_uint32_t aHeight)
	{
		mHeight = aHeight;
	}


	/**
	 * GETTER - SETTER
	 * mWidth
	 */
	inline avm_uint32_t getWidth() const
	{
		return( mWidth );
	}

	inline void setWidth(avm_uint32_t aWidth)
	{
		mWidth = aWidth;
	}


	/**
	 * GETTER - SETTER
	 * mWeight
	 */
	inline avm_uint8_t getWeight() const
	{
		return( mWeight );
	}

	inline avm_uint32_t getStrWeight() const
	{
		return( mWeight );
	}

	inline static avm_uint8_t getWeightMax()
	{
		return( AVM_NUMERIC_MAX_UINT8 );
	}

	inline bool isWeightMax() const
	{
		return( mWeight == AVM_NUMERIC_MAX_UINT8 );
	}

	inline bool isWeight(avm_uint8_t aWeight) const
	{
		return( mWeight == aWeight );
	}


	inline void setWeight(avm_uint8_t aWeight)
	{
		mWeight = aWeight;
	}


	inline void setWeightMax()
	{
		mWeight = AVM_NUMERIC_MAX_UINT8;
	}


	inline void decrWeight(avm_uint8_t aWeight = 1)
	{
		if( mWeight != AVM_NUMERIC_MAX_UINT8 )
		{
			mWeight -= aWeight;
		}
	}

	inline void incrWeight(avm_uint8_t aWeight = 1)
	{
		if( mWeight != AVM_NUMERIC_MAX_UINT8 )
		{
			mWeight += aWeight;
		}
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */

	inline virtual std::string str() const
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

	virtual void toStream(OutStream & out) const
	{
		out << TAB
			<<    "Id:" << getIdNumber() << " , Ev:" << getEvalNumber()
			<<  " , H:" << getHeight()   <<  " , W:" << getWidth()
			<<  " , Q:" << getStrWeight()
			<< EOL_FLUSH;
	}

};



class ExecutionContext : public Element ,
		public ExecutionContextFlagsImpl ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionContext )
{

	AVM_DECLARE_CLONABLE_CLASS( ExecutionContext )

public:
	/**
	 * TRACE CONSTANT
	 */
	static avm_size_t EC_CHILD_TRACE_DEFAULT_SIZE;

	static avm_size_t EXECUTION_CONTEXT_CHILD_TRACE_MAX;

	/*
	 * DEFAULT NULL REFERENCE
	 */
	static ExecutionContext _NULL_;


protected:
	/**
	 * TYPEDEF
	 */
	typedef APList < ExecutionContext * >  APListOfExecutionContext;

public:
	typedef APListOfExecutionContext::iterator        rw_child_iterator;

	typedef APListOfExecutionContext::const_iterator  child_iterator;


   /**
	* ATTRIBUTES
	*/
	ExecutionContext * mContainer;
	APListOfExecutionContext mChildContexts;

	BF mHeader;

	APExecutionData mExecutionData;

	BF mNodeCondition;
	BF mNodeTimedCondition;

	BF mRunnableElementTrace;
	BF mIOElementTrace;

	TableOfRuntimeFormState::TableOfAssignedFlag mTableOfAssignedFlag;

	BF mInformation;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionContext()
	: Element( CLASS_KIND_T( ExecutionContext ) ),
	mContainer( NULL ),
	mChildContexts( ),
	mHeader(),
	mExecutionData( ),
	mNodeCondition( ),
	mNodeTimedCondition( ),
	mRunnableElementTrace( ),
	mIOElementTrace( ),
	mTableOfAssignedFlag( NULL ),
	mInformation( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutionContext(const ExecutionContext & aContext)
	: Element( aContext ),
	mContainer( aContext.mContainer ),
	mChildContexts( aContext.mChildContexts ),

	mHeader( aContext.mHeader ),
	mExecutionData( aContext.mExecutionData ),
	mNodeCondition( aContext.mNodeCondition ),
	mNodeTimedCondition( aContext.mNodeTimedCondition ),
	mRunnableElementTrace( aContext.mRunnableElementTrace ),
	mIOElementTrace( aContext.mIOElementTrace ),
	mTableOfAssignedFlag( aContext.mTableOfAssignedFlag ),
	mInformation( aContext.mInformation )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	ExecutionContext(APExecutionData & anExecutionData,
			avm_uint32_t aHeight, avm_uint32_t aWidth)
	: Element( CLASS_KIND_T( ExecutionContext ) ),
	mContainer( NULL ),
	mChildContexts( ),

	mHeader( new ExecutionContextHeader(aHeight , aWidth) ),
	mExecutionData( anExecutionData ),
	mNodeCondition( anExecutionData->getNodeCondition() ),
	mNodeTimedCondition( anExecutionData->getNodeTimedCondition() ),
	mRunnableElementTrace( anExecutionData->getRunnableElementTrace() ),
	mIOElementTrace( anExecutionData->getIOElementTrace() ),
	mTableOfAssignedFlag( anExecutionData->getTableOfAssignedFlag() ),
	mInformation( )
	{
		anExecutionData->setExecutionContext( this );
	}

	ExecutionContext(const ExecutionContext & aContainer,
			APExecutionData & anExecutionData,
			avm_uint32_t aHeight, avm_uint32_t aWidth)
	: Element( CLASS_KIND_T( ExecutionContext ) ),
	mContainer( const_cast< ExecutionContext * >(& aContainer) ),
	mChildContexts( ),

	mHeader( new ExecutionContextHeader(aHeight , aWidth) ),
	mExecutionData( anExecutionData ),
	mNodeCondition( anExecutionData->getNodeCondition() ),
	mNodeTimedCondition( anExecutionData->getNodeTimedCondition() ),
	mRunnableElementTrace( anExecutionData->getRunnableElementTrace() ),
	mIOElementTrace( anExecutionData->getIOElementTrace() ),
	mTableOfAssignedFlag( anExecutionData->getTableOfAssignedFlag() ),
	mInformation( )
	{
		anExecutionData->setExecutionContext( this );
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionContext()
	{
		if( hasContainer() )
		{
			//getContainer()->remove(this);
		}
	}

	inline void destroy()
	{
		mChildContexts.clear();

		mHeader.destroy();

		mExecutionData.destroy();

		mNodeCondition.destroy();
		mNodeTimedCondition.destroy();

		mRunnableElementTrace.destroy();
		mIOElementTrace.destroy();

		mInformation.destroy();
	}

	/**
	 * _NULL_
	 */
	inline bool isNull() const
	{
		return( this == (& ExecutionContext::_NULL_) );
	}

	inline bool isnotNull() const
	{
		return( this != (& ExecutionContext::_NULL_) );
	}

	/**
	 * cast to reference
	 */
	inline static const ExecutionContext & REF(const ExecutionContext * anEC)
	{
		return( ( anEC != NULL ) ?  (* anEC) : ExecutionContext::_NULL_ );
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
		return( mContainer != NULL );
	}

	inline void setContainer(ExecutionContext * anEC)
	{
		mContainer = anEC;
	}


	/**
	 * CLONE
	 */
	inline virtual ExecutionContext * cloneData() const
	{
		ExecutionContext * mCloneEC = new ExecutionContext( *this );
		mCloneEC->getAPExecutionData().makeWritable();

		return( mCloneEC );
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

		mNodeCondition = anInitialContext.mNodeCondition;
		mNodeTimedCondition = anInitialContext.mNodeTimedCondition;

		mRunnableElementTrace = anInitialContext.mRunnableElementTrace;
		mIOElementTrace = anInitialContext.mIOElementTrace;

		mTableOfAssignedFlag = anInitialContext.mTableOfAssignedFlag;

		mInformation = anInitialContext.mInformation;
	}

	inline void initialize(const APExecutionData & anInitialData,
			avm_uint32_t aHeight = 0, avm_uint32_t aWidth = 1)
	{
		mContainer = NULL;

		mHeader = new ExecutionContextHeader(aHeight, aWidth);
		mExecutionData = anInitialData;

		if( anInitialData.valid() )
		{
			mNodeCondition = anInitialData->getNodeCondition();
			mNodeTimedCondition = anInitialData->getNodeTimedCondition();

			mRunnableElementTrace = anInitialData->getRunnableElementTrace();
			mIOElementTrace = anInitialData->getIOElementTrace();

			mTableOfAssignedFlag = anInitialData->getTableOfAssignedFlag();
		}
	}


	/**
	 * RESET DATA BEFORE EVALUATION
	 */
	inline void resetDataBeforeEvaluation()
	{
		mExecutionData->setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
		mExecutionData->setNodeTimedCondition( ExpressionConstant::BOOLEAN_TRUE );

		mExecutionData->setRunnableElementTrace( BF::REF_NULL );
		mExecutionData->setIOElementTrace( BF::REF_NULL );

		// Due to basic pointer, not smart pointer
		mTableOfAssignedFlag = mExecutionData->getTableOfAssignedFlag();
		mExecutionData->setTableOfAssignedFlag( NULL );
	}


	/**
	 * RESTORE DATA AFTER EVALUATION
	 */
	inline void restoreDataAfterEvaluation()
	{
		mExecutionData->setNodeCondition( mNodeCondition );
		mExecutionData->setNodeTimedCondition( mNodeTimedCondition );

		mExecutionData->setRunnableElementTrace( mRunnableElementTrace );
		mExecutionData->setIOElementTrace( mIOElementTrace );

		mExecutionData->setTableOfAssignedFlag( mTableOfAssignedFlag );
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

	inline avm_size_t size() const
	{
		return( mChildContexts.size() );
	}


	/**
	 * SETTER
	 * mChildContexts
	 */
	inline void appendChildContext(ExecutionContext * anEC)
	{
		mChildContexts.append( anEC );
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



	inline APListOfExecutionContext & getNext()
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
	inline const BF & getHeader() const
	{
		return( mHeader );
	}

	inline ExecutionContextHeader * rawHeader() const
	{
		return( mHeader.to_ptr< ExecutionContextHeader >() );
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


	inline APExecutionData & getPreviousExecutionData()
	{
		return( getContainer()->getAPExecutionData() );
	}

	inline const APExecutionData & getPreviousExecutionData() const
	{
		return( getContainer()->getAPExecutionData() );
	}

	inline bool hasPrevious() const
	{
		return( hasContainer() );
	}


	/**
	 * GETTER - SETTER
	 * mHeader trace indices
	 */
	inline static avm_uint32_t getCreateCounter()
	{
		return( ExecutionContextHeader::ID_NUMBER );
	}

	inline avm_uint32_t getIdNumber() const
	{
		return( rawHeader()->getIdNumber() );
	}


	inline avm_uint32_t getEvalNumber() const
	{
		return( rawHeader()->getEvalNumber() );
	}

	inline bool isEvaluated() const
	{
		return( rawHeader()->getEvalNumber() > 0 );
	}

	inline void setEvalNumber(avm_uint32_t anEvalNumber)
	{
		rawHeader()->setEvalNumber(anEvalNumber);
	}


	inline avm_uint32_t getHeight() const
	{
		return( rawHeader()->getHeight() );
	}

	inline void setHeight(avm_uint32_t aHeight)
	{
		rawHeader()->setHeight(aHeight);
	}


	inline avm_uint32_t getWidth() const
	{
		return( rawHeader()->getWidth() );
	}

	inline void setWidth(avm_uint32_t aWidth)
	{
		rawHeader()->setWidth(aWidth);
	}


	inline avm_uint8_t getWeight() const
	{
		return( rawHeader()->getWeight() );
	}

	inline avm_uint32_t getStrWeight() const
	{
		return( rawHeader()->getStrWeight() );
	}

	inline static avm_uint8_t getWeightMax()
	{
		return( ExecutionContextHeader::getWeightMax() );
	}

	inline bool isWeightMax() const
	{
		return( rawHeader()->isWeightMax() );
	}

	inline bool isWeight(avm_uint8_t aWeight) const
	{
		return( rawHeader()->isWeight(aWeight) );
	}


	inline void setWeight(avm_uint8_t aWeight)
	{
		rawHeader()->setWeight(aWeight);
	}

	inline void setWeightMax()
	{
		rawHeader()->setWeightMax();
	}


	inline avm_uint32_t getPrevEvalNumber() const
	{
		return( isRoot() ? 0 : getContainer()->getEvalNumber() );
	}

	inline avm_uint32_t getPrevHeight() const
	{
		return( isRoot() ? 0 : getContainer()->getHeight() );
	}

	inline avm_uint32_t getPrevIdNumber() const
	{
		return( isRoot() ? 0 : getContainer()->getIdNumber() );
	}

	inline avm_uint32_t getPrevWidth() const
	{
		return( isRoot() ? 0 : getContainer()->getWidth() );
	}

	inline avm_uint8_t getPrevsWeight() const
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
	inline APExecutionData & getAPExecutionData()
	{
		return( mExecutionData );
	}

	inline const APExecutionData & getAPExecutionData() const
	{
		return( mExecutionData );
	}

	inline ExecutionData * getExecutionData() const
	{
		return( mExecutionData );
	}

	inline const ExecutionData & refExecutionData() const
	{
		return( * mExecutionData );
	}

	inline ExecutionData & rwExecutionData() const
	{
		return( * mExecutionData );
	}


	inline  bool hasExecutionData() const
	{
		return( mExecutionData.valid() );
	}

	inline void setExecutionData(const APExecutionData & anExecutionData)
	{
		mExecutionData = anExecutionData;
	}

	inline void makeWritableExecutionData()
	{
		mExecutionData.makeWritable();
	}



	/**
	 * GETTER - SETTER
	 * mRunnableElementTrace
	 */
	inline BF & getRunnableElementTrace()
	{
		return( mRunnableElementTrace );
	}

	inline const BF & getRunnableElementTrace() const
	{
		return( mRunnableElementTrace );
	}

	inline bool hasRunnableElementTrace() const
	{
		return( mRunnableElementTrace.valid() );
	}

	inline void setRunnableElementTrace(const BF & aRunnableElementTrace)
	{
		mRunnableElementTrace = aRunnableElementTrace;
	}


	/**
	 * GETTER
	 * tableOfRuntimeFormState
	 */

	bool checkRunningForm(const RuntimeID & aRID)
	{
		return( getAPExecutionData()->checkRunningForm(
				getRunnableElementTrace(), aRID) );
	}


	/**
	 * GETTER
	 * mTableOfAssignedFlag
	 */
	TableOfRuntimeFormState::TableOfAssignedFlag getTableOfAssignedFlag() const
	{
		return( mTableOfAssignedFlag );
	}

	void setTableOfAssignedFlag(
			TableOfRuntimeFormState::TableOfAssignedFlag aTableOfAssignedFlag)
	{
		mTableOfAssignedFlag = aTableOfAssignedFlag;
	}



	/**
	 * GETTER
	 * mNodeCondition  &&  mNodeTimedCondition
	 */
	inline BF getAllNodeCondition() const
	{
		return( ExpressionConstructor::andExpr(
				mNodeCondition, mNodeTimedCondition) );
	}


	/**
	 * GETTER - SETTER
	 * mNodeCondition
	 */
	inline BF & getNodeCondition()
	{
		return( mNodeCondition );
	}

	inline const BF & getNodeCondition() const
	{
		return( mNodeCondition );
	}

	inline bool hasNodeCondition() const
	{
		return( mNodeCondition.valid() );
	}

	inline void setNodeCondition(const BF & aCondition)
	{
		mNodeCondition = aCondition;
	}


	/**
	 * GETTER - SETTER
	 * mNodeTimedCondition
	 */
	inline BF & getNodeTimedCondition()
	{
		return( mNodeTimedCondition );
	}

	inline const BF & getNodeTimedCondition() const
	{
		return( mNodeTimedCondition );
	}

	inline bool hasNodeTimedCondition() const
	{
		return( mNodeTimedCondition.valid() );
	}

	inline void setNodeTimedCondition(const BF & aTimedCondition)
	{
		mNodeTimedCondition = aTimedCondition;
	}


	/**
	 * GETTER - SETTER
	 * mIOElementTrace
	 */
	inline BF & getIOElementTrace()
	{
		return( mIOElementTrace );
	}

	inline const BF & getIOElementTrace() const
	{
		return( mIOElementTrace );
	}

	inline bool hasIOElementTrace() const
	{
		return( mIOElementTrace.valid() );
	}

	inline void setIOElementTrace(const BF & anIOElementTrace)
	{
		mIOElementTrace = anIOElementTrace;
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
		ListOfExecutionContext::iterator it = listOfEC.begin();
		ListOfExecutionContext::iterator itEnd = listOfEC.end();
		for( ; it != itEnd ; ++it )
		{
			(*it)->addInfo(aProcessor,aData);
		}
	}

	inline GenericInfoData * getInfo(
			const AbstractProcessorUnit & aProcessor, const BF & anID) const
	{
		return( mInformation.invalid() ?  NULL :
				mInformation.to_ptr< ExecutionInformation >()->
				getInfo(aProcessor, anID) );
	}


	inline const BF & getInfoData(
			const IProcessorUnitRegistration & aRegisterTool) const
	{
		return( mInformation.invalid() ?  BF::REF_NULL :
				mInformation.to_ptr< ExecutionInformation >()->
				getInfoData(aRegisterTool) );
	}

	inline const BF & getInfoData(const AbstractProcessorUnit & aProcessor) const
	{
		return( mInformation.invalid() ?  BF::REF_NULL :
				mInformation.to_ptr< ExecutionInformation >()->
				getInfoData(aProcessor) );
	}

	inline const BF & getInfoData(
			const AbstractProcessorUnit & aProcessor, const BF & anID) const
	{
		return( mInformation.invalid() ?  BF::REF_NULL :
				mInformation.to_ptr< ExecutionInformation >()->
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
				mInformation.to_ptr< ExecutionInformation >()->hasInfo() );
	}

	inline bool hasInfo(const AbstractProcessorUnit & aProcessor) const
	{
		return( mInformation.valid() && mInformation.to_ptr<
				ExecutionInformation >()->hasInfo(aProcessor) );
	}

	inline bool noneInfo(const AbstractProcessorUnit & aProcessor) const
	{
		return( mInformation.invalid() || mInformation.to_ptr<
				ExecutionInformation >()->noneInfo(aProcessor) );
	}

	inline bool hasInfo(
			const AbstractProcessorUnit & aProcessor, const BF & anID) const
	{
		return( mInformation.valid() && mInformation.to_ptr<
				ExecutionInformation >()-> hasInfo(aProcessor, anID) );
	}


	inline bool hasInfoWithData(
			const AbstractProcessorUnit & aProcessor, const BF & aData) const
	{
		return( mInformation.valid() && mInformation.to_ptr<
				ExecutionInformation >()->hasInfoWithData(aProcessor, aData) );
	}

	inline bool hasInfo(const BF & anID) const
	{
		return( mInformation.valid() &&
				mInformation.to_ptr< ExecutionInformation >()->hasInfo(anID) );
	}

	inline bool hasInfo(Element * anID) const
	{
		return( mInformation.valid() &&
				mInformation.to_ptr< ExecutionInformation >()->hasInfo(anID) );
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


	inline virtual std::string str() const
	{
		return( osStrPosition( OSS() << "EC< " ) << " > "
				<< refExecutionData().strStateConf() );
	}

	virtual void toStream(OutStream & out) const;

	virtual void toFscn(OutStream & out,
			const ExecutionData * aPreviousExecData) const;

	std::string str_min() const;
	std::string str_position() const;

	void traceMinimum(OutStream & out) const;
	void traceDefault(OutStream & out) const;
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
			avm_uint32_t nDeadlockCounter) const;

	void writeTraceForRedundancy(OutStream & out,
			ExecutionContext * aRedundantExecContext,
			avm_uint32_t nRedundancyCounter) const;

};


} /* namespace sep */

#endif /*EXECUTIONCONTEXT_H_*/

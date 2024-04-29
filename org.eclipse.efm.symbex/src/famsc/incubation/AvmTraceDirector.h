/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 févr. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVM_PROCESS_AVMTRACEDIRECTOR_H_
#define AVM_PROCESS_AVMTRACEDIRECTOR_H_

#include <famcore/api/BaseCoverageFilter.h>
#include <famcore/debug/IDebugProcessorProvider.h>

#include <util/avm_string.h>
#include <util/avm_vfs.h>
#include <common/BF.h>

#include <collection/Bitset.h>

#include <fml/symbol/TableOfSymbol.h>
#include <fml/type/TableOfTypeSpecifier.h>

#include <fml/operator/OperatorLib.h>

#include <fml/trace/TraceChecker.h>
#include <fml/trace/TraceSequence.h>

#include <iosfwd>
#include <vector>


namespace sep
{

class AvmTraceDirector;
class ExecutionContext;
class SymbexControllerUnitManager;
class Symbol;
class TracePoint;


class AvmTraceDirective  :  public TraceSequence
{

public:
	/**
	 * TYPEDEF
	 */
	enum STATUS { UNDEFINED , PENDING , COVERED , REDUNDANT , ABORTED , UNKNOWN };

	/**
	 * ATTRIBUTE
	 */
	std::string mTraceID;

	std::string mTraceLabel;
	std::string mTraceLocation;

	AvmTraceDirective * mRedundantTrace;
	ListOfExecutionContext mRedundantEC;

	STATUS mStatus;

	std::size_t mTimePointOffset;

	Bitset mRequiredPointFlags;

	bool mReducedFlag;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmTraceDirective()
	: TraceSequence( CLASS_KIND_T( AvmTraceDirective ) ),
	mTraceID( ),
	mTraceLabel( ),
	mTraceLocation( ),

	mRedundantTrace( nullptr ),
	mRedundantEC( ),

	mStatus( UNDEFINED ),
	mTimePointOffset( 0 ),
	mRequiredPointFlags( ),
	mReducedFlag( false )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	AvmTraceDirective(const TraceSequence & aTrace)
	: TraceSequence( aTrace ),
	mTraceID( ),
	mTraceLabel( ),
	mTraceLocation( ),

	mRedundantTrace( nullptr ),
	mRedundantEC( ),

	mStatus( UNDEFINED ),
	mTimePointOffset( 0 ),
	mRequiredPointFlags( ),
	mReducedFlag( false )
	{
		//!! NOTHING
	}

	AvmTraceDirective(const AvmTraceDirective & aTraceDirective)
	: TraceSequence( aTraceDirective ),
	mTraceID( aTraceDirective.mTraceID ),
	mTraceLabel( aTraceDirective.mTraceLabel ),
	mTraceLocation( aTraceDirective.mTraceLocation ),

	mRedundantTrace( aTraceDirective.mRedundantTrace ),
	mRedundantEC( aTraceDirective.mRedundantEC ),

	mStatus( aTraceDirective.mStatus ),
	mTimePointOffset( aTraceDirective.mTimePointOffset ),
	mRequiredPointFlags( aTraceDirective.mRequiredPointFlags ),
	mReducedFlag( aTraceDirective.mReducedFlag )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmTraceDirective()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mFoldedBitset
	 */
	inline void initFoldedBitset()
	{
		mRequiredPointFlags.clear();
		mRequiredPointFlags.resize(points.size(), false);
	}

	/**
	 * copy an existing trace
	 */
	inline void copyTrace(AvmTraceDirective & aTraceElement)
	{
		TraceSequence::copyTrace( aTraceElement );

		mStatus = aTraceElement.mStatus;

		mTraceID = aTraceElement.mTraceID;

		mTraceLocation = aTraceElement.mTraceLocation;

		mRedundantTrace = aTraceElement.mRedundantTrace;

		mRedundantEC.append( aTraceElement.mRedundantEC );

		mTimePointOffset = aTraceElement.mTimePointOffset;

		mRequiredPointFlags = aTraceElement.mRequiredPointFlags;

		mReducedFlag = aTraceElement.mReducedFlag;
	}


	/**
	 * GETTER - SETTER
	 * APPEND -- SAVE
	 * POP_FRONT
	 * SIZE
	 */
	inline void clear()
	{
		TraceSequence::clear();

		mStatus = UNDEFINED;

		mTraceID.clear();

		mTraceLabel.clear();
		mTraceLocation.clear();

		mRedundantTrace = nullptr;
		mRedundantEC.clear();

		mTimePointOffset = 0;

		mRequiredPointFlags.clear();

		mReducedFlag = false;
	}

	void setCoverage(std::size_t & offset, std::size_t count);

	void setGoalAchieved(AvmTraceDirector & aTraceDirector);

	void normalize(AvmTraceDirector & aTraceDirector);


	/**
	 * GETTER
	 * mStatus
	 */
	inline bool goalPending()
	{
		return( mStatus == PENDING );
	}

	inline bool goalAchieved()
	{
		return( (mStatus == COVERED) || (mStatus == REDUNDANT) );
	}

	inline bool goalAborted()
	{
		return( mStatus == ABORTED );
	}


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	inline std::string strStatus() const
	{
	#define PRINT_STATUS( OBJ )   case OBJ : return( QUOTEME( OBJ ) )

		switch ( mStatus )
		{
			PRINT_STATUS( COVERED   );
			PRINT_STATUS( REDUNDANT );

			PRINT_STATUS( ABORTED   );
			PRINT_STATUS( UNKNOWN   );

			PRINT_STATUS( PENDING );

			PRINT_STATUS( UNDEFINED );

			default :  return( "UNEXPECTED" );
		}
	}


	virtual std::string str() const override
	{
		return( OSS() << mTraceLabel << FQN_ID_ROOT_SEPARATOR << mTraceID );
//		return( OSS() << "trace#" << tid << FQN_ID_ROOT_SEPARATOR << mTraceID );
	}

	std::string strInfo() const
	{
//		return( OSS() << "trace#" << tid << FQN_ID_ROOT_SEPARATOR << mTraceID
//				<< "< ", << VFS::relativeProjectPath(mTraceLocation) << " >" );
		return( OSS() << mTraceLabel << FQN_ID_ROOT_SEPARATOR
				<< VFS::relativeProjectPath(mTraceLocation) );
	}

	virtual void toStream(OutStream & os) const override;

	void traceAbstract(OutStream & os) const;

	void traceMinimum(OutStream & os) const;

};



class AvmTraceDirector  :
		public AutoRegisteredCoverageProcessorUnit< AvmTraceDirector >,
		public IDebugProcessorProvider
{

	AVM_DECLARE_CLONABLE_CLASS( AvmTraceDirector )

	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3(
			"coverage#trace",
			"coverage#trace#director",
			"avm::processor.TRACE_DIRECTOR");


protected:
	/**
	 * ATTRIBUTE
	 */
	bool mConsecutiveFlag;
	bool mDeterminismFlag;
	bool mFoldingFlag;


	std::string mSchemaFileLocation;
	VectorOfString mTableOfTraceFileLocation;
	VectorOfString mTableOfTraceLabel;

	TableOfSymbol mSpecVariables;
	TableOfSymbol mTraceVariables;
	TableOfTypeSpecifier mTableOfTypeSpecifier;

	TraceChecker mTraceChecker;

	std::size_t TRACE_ID;
	BFVector   mTableOfAnalyzingTrace;

	BFVector mTableOfAnalyzedTrace;

	std::size_t mParsedFileCount;
	bool mSortedFileFlag;

	std::size_t mRedundancyCount;
	BFVector mTableOfRedundantTrace;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	std::size_t TP_ID;

	AvmTraceDirective   mPendingTrace;
	AvmTraceDirective * mSelectedTrace;

	AvmTraceDirective * mProcessedTrace;

	ListOfExecutionContext mInitialRootEC;
	ListOfExecutionContext mNextRootEC;

	ListOfExecutionContext mDirectiveEC;
	ListOfExecutionContext mCurrentEC;

	std::size_t mFileCount;
	std::size_t mFileOffset;

	std::size_t mTraceCount;
	std::size_t mTraceOffset;

	TracePoint * mTracePoint;
	std::size_t mCoverageOffset;

	std::vector< AVM_OPCODE > mBindOP;

	std::size_t saveCoverageMax;
	std::size_t coverageMax;
	std::size_t coverageCount;

	std::string mParseLine;
	std::string mParseToken;
	bool mEndOfFile;

	std::size_t mParseErrorCount;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmTraceDirector(SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject)
	: AutoRegisteredCoverageProcessorUnit(
			aControllerUnitManager, wfParameterObject,
			AVM_PRE_PROCESSING_STAGE | AVM_PREPOST_FILTERING_STAGE,
			PRECEDENCE_OF_ACTIVE_COVERAGE_PROCESSOR ),
	IDebugProcessorProvider( this ),
	mConsecutiveFlag( ),
	mDeterminismFlag( ),
	mFoldingFlag( ),

	mSchemaFileLocation( ),
	mTableOfTraceFileLocation( ),
	mTableOfTraceLabel( ),

	mSpecVariables( ),
	mTraceVariables( ),
	mTableOfTypeSpecifier( ),

	mTraceChecker( ENV ),

	TRACE_ID( 0 ),
	mTableOfAnalyzingTrace( ),

	mTableOfAnalyzedTrace( ),

	mParsedFileCount( AVM_NUMERIC_MAX_SIZE_T ),
	mSortedFileFlag( false ),

	mRedundancyCount( 0 ),
	mTableOfRedundantTrace( ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	TP_ID( 0 ),

	mPendingTrace( ),
	mSelectedTrace( nullptr ),

	mProcessedTrace( nullptr ),

	mInitialRootEC( ),
	mNextRootEC( ),

	mDirectiveEC( ),
	mCurrentEC( ),

	mFileCount( 0 ),
	mFileOffset( 0 ),

	mTraceCount( 0 ),
	mTraceOffset( 0 ),

	mTracePoint( nullptr ),
	mCoverageOffset( 0 ),

	mBindOP( ),

	saveCoverageMax( 0 ),
	coverageMax( 0 ),
	coverageCount( 0 ),

	mParseLine( ),
	mParseToken( ),
	mEndOfFile( false ),

	mParseErrorCount( 0 )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmTraceDirector()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 */
	bool isFoldingFlag()
	{
		return( mFoldingFlag );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl() override;

	bool loadTrace();

	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	virtual void reportDefault(OutStream & os) const override;

	virtual void reportMaximum(OutStream & os) const override;

	virtual void reportTrace(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// PARSER TOOLS
	////////////////////////////////////////////////////////////////////////////

	bool nextLine(std::ifstream & aStream);

	bool nextToken(std::ifstream & aStream);
	bool nextToken(std::ifstream & aStream, const std::string & separator);

	unsigned int nextTokenNewLine(std::ifstream & aStream);

	bool nextTokenChar(std::ifstream & aStream, char expectedChar);
	char nextTokenChar(
			std::ifstream & aStream, const std::string & expectedChars);

	bool nextTokenWord(
			std::ifstream & aStream, const std::string & expectedWord);

	bool nextTokenID(std::ifstream & aStream);
	bool nextTokenUFID(std::ifstream & aStream);

	bool nextTokenAfter(std::ifstream & aStream, char expectedChar);
	bool nextTokenAfter(
			std::ifstream & aStream, const std::string & expectedWord);


	/**
	 * SCHEMA
	 */
	bool parseSchema();

	bool parseSchemaDataType(std::ifstream & aSchemaStream);
	bool parseSchemaDataTypeEnum(
			std::ifstream & aSchemaStream, const std::string & typeID);

	bool parseSchemaTracedef(std::ifstream & aSchemaStream);

	bool parseSchemaSpecBind(std::ifstream & aSchemaStream);

	/**
	 * TRACE
	 */
	bool parseTrace(const std::string & aTraceLocation,
			const std::string & aTraceLabel);

	bool parseTraceHeader(std::ifstream & aTraceStream);
	bool parseTraceUFID(std::ifstream & aTraceStream);

	bool parseTraceNumeric(std::ifstream & aTraceStream);
	BF parseTraceNumeric(const Symbol & aVar,
			AVM_OPCODE bindOP, const std::string & term);


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

	virtual bool preprocess() override;

	virtual bool postprocess() override;


	////////////////////////////////////////////////////////////////////////////
	// FILTER API
	////////////////////////////////////////////////////////////////////////////

	virtual bool filteringInitialize() override;

	virtual bool prefilter() override;
	virtual bool prefilter(ExecutionContext & anEC) override;

	virtual bool postfilter() override;
	virtual bool postfilter(ExecutionContext & anEC) override;

	void initDriver();
	void checkDriver(ExecutionContext * anEC);
	bool electDriver();

	void selectDriver();
	void initWaitingQueue();

	/**
	 * PROCESSOR REQUEST API :> CONITNUE , GOAL_ACHIEVED
	 */
	virtual void handleRequestContinue() override;

	virtual void handleRequestGoalAchieved() override;

	/**
	 * FILTERING FINALIZE
	 */
	virtual bool filteringFinalize() override;

	void finalizeTrace() const;


	////////////////////////////////////////////////////////////////////////////
	// DEBUG PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	virtual bool debugEvalCommandImpl() override;

	void dbgCommandDirectiveTrace();


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	virtual void toStream(OutStream & os) const override
	{
		if( mParameterWObject != WObject::_NULL_ )
		{
			mParameterWObject->toStream(os);
		}
	}

};

} /* namespace sep */

#endif /* AVM_PROCESS_AVMTRACEDIRECTOR_H_ */

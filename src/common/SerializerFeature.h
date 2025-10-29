/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef COMMON_SERIALIZERFEATURE_H_
#define COMMON_SERIALIZERFEATURE_H_

#include <util/avm_numeric.h>
#include <util/avm_types.h>
#include <util/avm_uri.h>

#include <collection/Vector.h>

#include <printer/OutStream.h>

namespace sep
{

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// The PERIOD for reporting, ...
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

typedef std::uint16_t            avm_period_kind_t;

enum {
	AVM_PERIOD_UNDEFINED_KIND    = 0x0000,

	AVM_PERIOD_INIT_KIND         = 0x0001,
	AVM_PERIOD_EXIT_KIND         = 0x0002,

	AVM_PERIOD_PREPROCESS_KIND   = 0x0004,
	AVM_PERIOD_POSTPROCESS_KIND  = 0x0008,

	AVM_PERIOD_PREFILTER_KIND    = 0x0010,
	AVM_PERIOD_POSTFILTER_KIND   = 0x0020,


	AVM_PERIOD_OTF_KIND          = 0x0040,
	AVM_PERIOD_EVERY_KIND        = 0x0080,

	AVM_PERIOD_AFTER_KIND        = 0x0100,
	AVM_PERIOD_BEFORE_KIND       = 0x0200,

};

#define IS_PERIOD_UNDEFINED_KIND(kind)    (kind == AVM_PERIOD_UNDEFINED_KIND)

#define IS_PERIOD_INIT_KIND(kind)         (kind & AVM_PERIOD_INIT_KIND)
#define IS_PERIOD_EXIT_KIND(kind)         (kind & AVM_PERIOD_EXIT_KIND)

#define IS_PERIOD_PREPROCESS_KIND(kind)   (kind & AVM_PERIOD_PREPROCESS_KIND)
#define IS_PERIOD_POSTPROCESS_KIND(kind)  (kind & AVM_PERIOD_POSTPROCESS_KIND)

#define IS_PERIOD_PREFILTER_KIND(kind)    (kind & AVM_PERIOD_PREFILTER_KIND)
#define IS_PERIOD_POSTFILTER_KIND(kind)   (kind & AVM_PERIOD_POSTFILTER_KIND)

#define IS_PERIOD_OTF_KIND(kind)          (kind & AVM_PERIOD_OTF_KIND)
#define IS_PERIOD_EVERY_KIND(kind)        (kind & AVM_PERIOD_EVERY_KIND)

#define IS_PERIOD_AFTER_KIND(kind)        (kind & AVM_PERIOD_AFTER_KIND)
#define IS_PERIOD_BEFORE_KIND(kind)       (kind & AVM_PERIOD_BEFORE_KIND)


class WObject;


class SerializerFeature
{

protected:
	/**
	 * TYPEDEF
	 */
	typedef Vector< AvmUri >  VectorOfAvmUri;


	/**
	 * ATTRIBUTES
	 */
	VectorOfAvmUri mTableOfURI;

	AvmUri lastFolder;
	AvmUri lastFile;
	AvmUri lastFilename;

	AvmUri newIndexFile;

	VectorOfAvmUri::iterator itURI;
	VectorOfAvmUri::iterator endURI;
	AvmUri * currentURI;

	avm_period_kind_t mPeriodKind;

	avm_delay_value_t  mPeriodEveryValue;
	avm_unit_t   mPeriodEveryUnit;

	avm_delay_value_t  mPeriodAfterValue;
	avm_unit_t   mPeriodAfterUnit;

	avm_delay_value_t  mPeriodBeforeValue;
	avm_unit_t   mPeriodBeforeUnit;

	// Only for RUNTIME
	avm_delay_value_t mTimeInitValue;
	avm_delay_value_t mTimePreviousValue;


	// Auto Open File
	bool mAutoOpenFileFlag;

	// DETAILS REPORTING
	bool mReportDetailsFlag;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SerializerFeature()
	: mTableOfURI( ),
	lastFolder( "last#folder" , AVM_URI_FOLDER_KIND , "." ),
	lastFile( "last#file" , AVM_URI_FILE_KIND , "_" ),
	lastFilename( "last#filename" , AVM_URI_FILENAME_KIND , "_" ),
	newIndexFile( "new#index#file" , AVM_URI_FILENAME_KIND , "newFile.txt" ),
	itURI( ),
	endURI( ),
	currentURI( nullptr ),

	mPeriodKind( AVM_PERIOD_EXIT_KIND ),

	mPeriodEveryValue( 0 ),
	mPeriodEveryUnit( AVM_UNDEFINED_UNIT ),

	mPeriodAfterValue( 0 ),
	mPeriodAfterUnit( AVM_UNDEFINED_UNIT ),

	mPeriodBeforeValue( 0 ),
	mPeriodBeforeUnit( AVM_UNDEFINED_UNIT ),

	mTimeInitValue( 0 ),
	mTimePreviousValue( 0 ),

	mAutoOpenFileFlag( true ),

	mReportDetailsFlag( false )

	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~SerializerFeature()
	{
		//!! NOTHING
	}


	/**
	 * CONFIGURE
	 */
	bool configure(const WObject * wfParameterObject);

	bool configureStream(const WObject * theVFS, AvmUri & uri);

	bool configureFolder(const WObject * theVFS, AvmUri & uri);

	bool configureFile(const WObject * theVFS, AvmUri & uri);
	bool configureFilename(const WObject * theVFS, AvmUri & uri);

	bool configureSocket(const WObject * theVFS, AvmUri & uri);

	bool configurePeriod(const WObject * theVFS, const std::string & strPeriod);


	/**
	 * SCHEDULE REPORT
	 */
	virtual bool scheduleReport()
	{
		return( true );
	}


	/**
	 * GETTER -- SETTER
	 * mTableOfURI
	 */
	inline AvmUri & appendUri( std::string id, const std::string & rawLocation )
	{
		return mTableOfURI.emplace_back( id , rawLocation );
	}

	inline void destroyLastUri()
	{
		mTableOfURI.pop_back();
	}



	inline const VectorOfAvmUri & getUri() const
	{
		return( mTableOfURI );
	}

	inline bool hasUri() const
	{
		return( mTableOfURI.empty() );
	}

	inline const AvmUri & getFolder() const
	{
		return( lastFolder );
	}

	inline const AvmUri & getLastFolder() const
	{
		return( lastFolder );
	}

//	inline const AvmUri & getLastFile() const
//	{
//		return( lastFile );
//	}
//
//	inline const AvmUri & getLastFilename() const
//	{
//		return( lastFilename );
//	}


	inline bool openStream()
	{
		endURI = mTableOfURI.end();
		for( itURI = mTableOfURI.begin() ; itURI != endURI ; ++itURI )
		{
			if( not (*itURI).open() )
			{

			}
		}

		itURI = mTableOfURI.begin();
		return( true );
	}

	inline void closeStream()
	{
		endURI = mTableOfURI.end();
		for( itURI = mTableOfURI.begin() ; itURI != endURI ; ++itURI )
		{
			(*itURI).close();
		}

		newIndexFile.close();
	}


	inline void beginStream()
	{
		itURI = mTableOfURI.begin();
		endURI = mTableOfURI.end();
	}

	inline bool hasStream()
	{
		while( itURI != endURI )
		{
			currentURI = &( *(itURI++) );
			if( currentURI->outStream.good() )
			{
				return( true );
			}
		}

		return( false );
	}

	inline OutStream & currentStream() const
	{
		return( currentURI->outStream );
	}


	/**
	 * GETTER -- SETTER
	 * mTableOfURI
	 */
	inline OutStream & getStream(const std::string & key)
	{
		for( auto & anUri : mTableOfURI )
		{
			if( (anUri.alias_id == key) && anUri.outStream.good() )
			{
				return( anUri.outStream );
			}
		}

		return( newFileStream(key) );
	}

	inline OutStream & getFileStream()
	{
		for( auto & anUri : mTableOfURI )
		{
			if( ((anUri.kind & AVM_URI_FILE_KIND) != 0)
				&& anUri.outStream.good() )
			{
				return( anUri.outStream );
			}
		}

		return( AVM_OS_COUT );
	}

	inline OutStream & getLastFileStream()
	{
		const auto & endIt = mTableOfURI.rend();
		for( auto it = mTableOfURI.rbegin() ; it != endIt ; ++it )
		{
			if( (((*it).kind & AVM_URI_FILE_KIND) != 0)
				&& (*it).outStream.good() )
			{
				return( (*it).outStream );
			}
		}

		return( AVM_OS_COUT );
	}


	/**
	 * GETTER
	 * Generate new outStream for a given index
	 */
	OutStream & newFileStream(std::size_t index);

	OutStream & newFileStream(const std::string & filename = "");


	/**
	 * GETTER
	 * PERIOD KIND
	 */
	inline avm_period_kind_t getPeriodKind() const
	{
		return( mPeriodKind );
	}

	inline bool hasPeriodKind() const
	{
		return( mPeriodKind != AVM_PERIOD_UNDEFINED_KIND );
	}

	inline void setPeriodKind(avm_period_kind_t kind)
	{
		mPeriodKind = kind;
	}

	inline void unsetPeriodKind()
	{
		mPeriodKind = AVM_PERIOD_UNDEFINED_KIND;
	}


	/**
	 * GETTER
	 * PERIOD EVERY KIND
	 */
	inline avm_unit_t getPeriodEveryUnit() const
	{
		return( mPeriodEveryUnit );
	}

	inline bool hasPeriodEveryUnit() const
	{
		return( mPeriodEveryUnit != AVM_PERIOD_UNDEFINED_KIND );
	}

	inline void setPeriodEveryUnit(avm_unit_t unit)
	{
		mPeriodEveryUnit = unit;
	}

	inline void unsetPeriodEveryUnit()
	{
		mPeriodEveryUnit = AVM_PERIOD_UNDEFINED_KIND;
	}


	/**
	 * GETTER
	 * PERIOD EVERY VALUE
	 */
	inline avm_delay_value_t getPeriodEveryValue() const
	{
		return( mPeriodEveryValue );
	}

	inline bool hasPeriodEveryValue() const
	{
		return( mPeriodEveryValue > 0 );
	}

	inline void setPeriodEveryValue(avm_delay_value_t value)
	{
		mPeriodEveryValue = value;
	}


	/**
	 * GETTER
	 * PERIOD AFTER KIND
	 */
	inline avm_unit_t getPeriodAfterUnit() const
	{
		return( mPeriodAfterUnit );
	}

	inline bool hasPeriodAfterUnit() const
	{
		return( mPeriodAfterUnit != AVM_PERIOD_UNDEFINED_KIND );
	}

	inline void setPeriodAfterUnit(avm_unit_t unit)
	{
		mPeriodAfterUnit = unit;
	}

	inline void unsetPeriodAfterUnit()
	{
		mPeriodAfterUnit = AVM_PERIOD_UNDEFINED_KIND;
	}


	/**
	 * GETTER
	 * PERIOD AFTER VALUE
	 */
	inline avm_delay_value_t getPeriodAfterValue() const
	{
		return( mPeriodAfterValue );
	}

	inline bool hasPeriodAfterValue() const
	{
		return( mPeriodAfterValue > 0 );
	}

	inline void setPeriodAfterValue(avm_delay_value_t value)
	{
		mPeriodAfterValue = value;
	}


	/**
	 * GETTER
	 * PERIOD BEFORE KIND
	 */
	inline avm_unit_t getPeriodBeforeUnit() const
	{
		return( mPeriodBeforeUnit );
	}

	inline bool hasPeriodBeforeUnit() const
	{
		return( mPeriodBeforeUnit != AVM_PERIOD_UNDEFINED_KIND );
	}

	inline void setPeriodBeforeUnit(avm_unit_t unit)
	{
		mPeriodBeforeUnit = unit;
	}

	inline void unsetPeriodBeforeUnit()
	{
		mPeriodBeforeUnit = AVM_PERIOD_UNDEFINED_KIND;
	}


	/**
	 * GETTER
	 * PERIOD BEFORE VALUE
	 */
	inline avm_delay_value_t getPeriodBeforeValue() const
	{
		return( mPeriodBeforeValue );
	}

	inline bool hasPeriodBeforeValue() const
	{
		return( mPeriodBeforeValue > 0 );
	}

	inline void setPeriodBeforeValue(avm_delay_value_t value)
	{
		mPeriodBeforeValue = value;
	}


	/**
	 * GETTER
	 * PERIOD BEGIN VALUE
	 */
	inline avm_delay_value_t getTimeInitValue() const
	{
		return( mTimeInitValue );
	}

	inline bool hasTimeInitValue() const
	{
		return( mTimeInitValue > 0 );
	}

	inline void setTimeInitValue(avm_delay_value_t value)
	{
		mTimeInitValue = value;
	}


	/**
	 * GETTER
	 * PERIOD PREVIOUS VALUE
	 */
	inline avm_delay_value_t getTimePreviousValue() const
	{
		return( mTimePreviousValue );
	}

	inline bool hasTimePreviousValue() const
	{
		return( mTimePreviousValue > 0 );
	}

	inline void setTimePreviousValue(avm_delay_value_t value)
	{
		mTimePreviousValue = value;
	}


	/**
	 * GETTER
	 * mReportDetailsFlag
	 */
	inline bool isReportDetails() const
	{
		return( mReportDetailsFlag );
	}

	inline void setReportDetailsFlag(bool value)
	{
		mReportDetailsFlag = value;
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	static std::string strPeriodKind(avm_period_kind_t kind);

	virtual void toStream(OutStream & os) const;

};


} /* namespace sep */

#endif /* COMMON_SERIALIZERFEATURE_H_ */

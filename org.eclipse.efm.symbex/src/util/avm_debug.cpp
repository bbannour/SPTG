/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 févr. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "avm_debug.h"

#include <sstream>

#include <util/avm_string.h>


namespace sep {


/**
 ***************************************************************************
 * AVM DEBUG LEVEL
 ***************************************************************************
 */
std::uint16_t  _AVM_DEBUG_LEVEL_ = AVM_DEBUG_ZERO_LEVEL;


/**
 ***************************************************************************
 * AVM DEBUG KIND
 ***************************************************************************
 */
std::size_t  _AVM_DEBUG_FLAG_ = AVM_DEBUG_NOTHING_FLAG;


/**
 * avm_setDebugLevel
 * avm_unsetDebugLevel
 */
void avm_setDebugLevel(std::string strDebugLevel)
{
#define SET_DEBUG_LEVEL( level )   \
	else if( strDebugLevel == #level )  AVM_DEBUG_SET_LEVEL( level )

	StringTools::toupper(strDebugLevel);

	if( strDebugLevel.empty() )  AVM_DEBUG_SET_LEVEL( ZERO )

	SET_DEBUG_LEVEL( ZERO     )

	SET_DEBUG_LEVEL( LOW      )
	SET_DEBUG_LEVEL( MEDIUM   )

	SET_DEBUG_LEVEL( HIGH     )
	SET_DEBUG_LEVEL( ULTRA    )

	SET_DEBUG_LEVEL( GOD_MODE )

	else AVM_DEBUG_SET_LEVEL( ZERO )
}


void avm_unsetDebugLevel(std::string strDebugLevel)
{
#define UNSET_DEBUG_EXCEPT_LEVEL( level )   \
	else if( strDebugLevel == #level )  AVM_DEBUG_SET_LEVEL( ZERO )

#define UNSET_DEBUG_LEVEL( level )   \
	else if( strDebugLevel == #level )  AVM_DEBUG_UNSET_LEVEL( level )

	StringTools::toupper(strDebugLevel);

	if( strDebugLevel.empty() )  AVM_DEBUG_SET_LEVEL( ZERO )

	UNSET_DEBUG_LEVEL( LOW    )
	UNSET_DEBUG_LEVEL( MEDIUM )

	UNSET_DEBUG_LEVEL( HIGH   )
	UNSET_DEBUG_LEVEL( ULTRA  )

	UNSET_DEBUG_EXCEPT_LEVEL( ZERO     )
	UNSET_DEBUG_EXCEPT_LEVEL( GOD_MODE )

	else AVM_DEBUG_SET_LEVEL( ZERO )
}

std::string avm_strDebugLevel()
{
#define PRINT_DEBUG_LEVEL( level )   \
	case AVM_DEBUG_##level##_LEVEL :  return( #level );

	switch( _AVM_DEBUG_LEVEL_ )
	{
		PRINT_DEBUG_LEVEL( ZERO     )

		PRINT_DEBUG_LEVEL( LOW      )
		PRINT_DEBUG_LEVEL( MEDIUM   )

		PRINT_DEBUG_LEVEL( HIGH     )
		PRINT_DEBUG_LEVEL( ULTRA    )

		PRINT_DEBUG_LEVEL( GOD_MODE )

		default: return( "DEBUG#LEVEL< UNKNOWN >" );
	}
}


/**
 * avm_setDebugFlag
 * avm_unsetDebugFlag
 */
void avm_setDebugFlag(std::string strDebugFlag)
{
#define SET_DEBUG_FLAG( flag )   \
		else if( strDebugFlag == #flag  )  AVM_DEBUG_ENABLE_FLAG( flag )


	if( _AVM_DEBUG_FLAG_ == AVM_DEBUG_ALL_FLAG )
	{
		return;
	}
	else if( strDebugFlag.empty() || strDebugFlag == "NOTHING" ) {
		_AVM_DEBUG_FLAG_ = AVM_DEBUG_NOTHING_FLAG;
	}

	// General Context

	SET_DEBUG_FLAG( PARSING                 )

	SET_DEBUG_FLAG( CONFIGURING             )

	SET_DEBUG_FLAG( COMPILING               )

	SET_DEBUG_FLAG( LOADING                 )

	SET_DEBUG_FLAG( COMPUTING               )

	SET_DEBUG_FLAG( REPORTING               )

	SET_DEBUG_FLAG( SOLVING                 )
	SET_DEBUG_FLAG( SAT_SOLVING             )
	SET_DEBUG_FLAG( SMT_SOLVING             )

	SET_DEBUG_FLAG( PROFILING               )


	// Process Stage: Processing, Filtering, ...

	SET_DEBUG_FLAG( ALL_PROCESS_STAGE       )
	SET_DEBUG_FLAG( PROCESSOR               )

	SET_DEBUG_FLAG( PROCESSING              )
	SET_DEBUG_FLAG( PRE_PROCESSING          )
	SET_DEBUG_FLAG( POST_PROCESSING         )

	SET_DEBUG_FLAG( FILTERING               )
	SET_DEBUG_FLAG( PRE_FILTERING           )
	SET_DEBUG_FLAG( POST_FILTERING          )

	SET_DEBUG_FLAG( QUEUE                   )
	SET_DEBUG_FLAG( QUEUING                 )


	// Statement Evaluation

	SET_DEBUG_FLAG( PROGRAM                 )

	SET_DEBUG_FLAG( STATEMENT               )

	SET_DEBUG_FLAG( ASSIGNMENT              )
	SET_DEBUG_FLAG( STATEMENT_ASSIGNMENT    )

	SET_DEBUG_FLAG( COMMUNICATION           )
	SET_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	SET_DEBUG_FLAG( STATEMENT_CONTROL       )
	SET_DEBUG_FLAG( STATEMENT_SCHEDULING    )

	SET_DEBUG_FLAG( TEST_DECISION           )
	SET_DEBUG_FLAG( STATEMENT_TEST_DECISION )

	SET_DEBUG_FLAG( BYTECODE                )

	SET_DEBUG_FLAG( DATA                    )

	SET_DEBUG_FLAG( TRACE                   )


	// Element: Property, Signal...

	SET_DEBUG_FLAG( VARIABLE                )

	SET_DEBUG_FLAG( BUFFER                  )

	SET_DEBUG_FLAG( PORT                    )

	SET_DEBUG_FLAG( SIGNAL                  )

	SET_DEBUG_FLAG( CONNEXION               )

	SET_DEBUG_FLAG( TIME                    )


	// Executable Component...

	SET_DEBUG_FLAG( EXECUTABLE              )

	SET_DEBUG_FLAG( PRIMITIVE               )

	SET_DEBUG_FLAG( ACTIVITY                )

	SET_DEBUG_FLAG( ROUTINE                 )

	SET_DEBUG_FLAG( TRANSITION              )

	SET_DEBUG_FLAG( MACHINE                 )

	SET_DEBUG_FLAG( STATEMACHINE            )


	// Others: [Qualified]NameID, RefCount, ...

	SET_DEBUG_FLAG( NAME_ID                 )

	SET_DEBUG_FLAG( QUALIFIED_NAME_ID       )

	SET_DEBUG_FLAG( FULLY_QUALIFIED_NAME_ID )

	SET_DEBUG_FLAG( ALL_NAME_ID             )

	SET_DEBUG_FLAG( CAS                     )

	SET_DEBUG_FLAG( REDUNDANCE              )


	SET_DEBUG_FLAG( MEMORY_ALLOCATION       )
	SET_DEBUG_FLAG( REFERENCE_COUNTING      )
	SET_DEBUG_FLAG( MEMORY_DEALLOCATION     )
	SET_DEBUG_FLAG( MEMORY_MANAGEMENT       )

	// God Mode
	SET_DEBUG_FLAG( ALL                     )
	SET_DEBUG_FLAG( GOD_MODE                )
}


void avm_unsetDebugFlag(std::string strDebugFlag)
{
#define UNSET_DEBUG_FLAG( flag )   \
		else if( strDebugFlag == #flag )  AVM_DEBUG_DISABLE_FLAG( flag )


	if( _AVM_DEBUG_FLAG_ == AVM_DEBUG_NOTHING_FLAG )
	{
		return;
	}
	else if( strDebugFlag.empty()
		|| strDebugFlag == "NOTHING" ) {
		_AVM_DEBUG_FLAG_ = AVM_DEBUG_NOTHING_FLAG;

		return;
	}

	// General Context

	UNSET_DEBUG_FLAG( PARSING                 )

	UNSET_DEBUG_FLAG( CONFIGURING             )

	UNSET_DEBUG_FLAG( COMPILING               )

	UNSET_DEBUG_FLAG( LOADING                 )

	UNSET_DEBUG_FLAG( COMPUTING               )

	UNSET_DEBUG_FLAG( REPORTING               )

	UNSET_DEBUG_FLAG( SOLVING                 )
	UNSET_DEBUG_FLAG( SAT_SOLVING             )
	UNSET_DEBUG_FLAG( SMT_SOLVING             )

	UNSET_DEBUG_FLAG( PROFILING               )


	// Process Stage: Processing, Filtering, ...

	UNSET_DEBUG_FLAG( ALL_PROCESS_STAGE       )
	UNSET_DEBUG_FLAG( PROCESSOR               )

	UNSET_DEBUG_FLAG( PROCESSING              )
	UNSET_DEBUG_FLAG( PRE_PROCESSING          )
	UNSET_DEBUG_FLAG( POST_PROCESSING         )

	UNSET_DEBUG_FLAG( FILTERING               )
	UNSET_DEBUG_FLAG( PRE_FILTERING           )
	UNSET_DEBUG_FLAG( POST_FILTERING          )

	UNSET_DEBUG_FLAG( QUEUE                   )
	UNSET_DEBUG_FLAG( QUEUING                 )


	// Statement Evaluation

	UNSET_DEBUG_FLAG( PROGRAM                 )

	UNSET_DEBUG_FLAG( STATEMENT               )

	UNSET_DEBUG_FLAG( ASSIGNMENT              )
	UNSET_DEBUG_FLAG( STATEMENT_ASSIGNMENT    )

	UNSET_DEBUG_FLAG( COMMUNICATION           )
	UNSET_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	UNSET_DEBUG_FLAG( STATEMENT_CONTROL       )
	UNSET_DEBUG_FLAG( STATEMENT_SCHEDULING    )

	UNSET_DEBUG_FLAG( TEST_DECISION           )
	UNSET_DEBUG_FLAG( STATEMENT_TEST_DECISION )

	UNSET_DEBUG_FLAG( BYTECODE                )

	UNSET_DEBUG_FLAG( DATA                    )

	UNSET_DEBUG_FLAG( TRACE                   )


	// Element: Property, Signal...

	UNSET_DEBUG_FLAG( VARIABLE                )

	UNSET_DEBUG_FLAG( BUFFER                  )

	UNSET_DEBUG_FLAG( PORT                    )

	UNSET_DEBUG_FLAG( SIGNAL                  )

	UNSET_DEBUG_FLAG( CONNEXION               )

	UNSET_DEBUG_FLAG( TIME                    )


	// Executable Component...

	UNSET_DEBUG_FLAG( EXECUTABLE              )

	UNSET_DEBUG_FLAG( PRIMITIVE               )

	UNSET_DEBUG_FLAG( ACTIVITY                )

	UNSET_DEBUG_FLAG( ROUTINE                 )

	UNSET_DEBUG_FLAG( TRANSITION              )

	UNSET_DEBUG_FLAG( MACHINE                 )

	UNSET_DEBUG_FLAG( STATEMACHINE            )


	// Others: [Qualified]NameID, RefCount, ...

	UNSET_DEBUG_FLAG( NAME_ID                 )

	UNSET_DEBUG_FLAG( QUALIFIED_NAME_ID       )

	UNSET_DEBUG_FLAG( FULLY_QUALIFIED_NAME_ID )


	UNSET_DEBUG_FLAG( CAS                     )

	UNSET_DEBUG_FLAG( REDUNDANCE              )


	UNSET_DEBUG_FLAG( REFERENCE_COUNTING      )

	// God Mode
	UNSET_DEBUG_FLAG( ALL                     )
	UNSET_DEBUG_FLAG( GOD_MODE                )
}


std::string avm_strDebugFlag(const std::string & sep)
{
	if( _AVM_DEBUG_FLAG_ == AVM_DEBUG_NOTHING_FLAG )
	{
		return( "NOTHING" );
	}
	if( _AVM_DEBUG_FLAG_ == AVM_DEBUG_GOD_MODE_FLAG )
	{
		return( "GOD_MODE" );
	}
	if( _AVM_DEBUG_FLAG_ == AVM_DEBUG_ALL_FLAG )
	{
		return( "ALL" );
	}
	else
	{
		std::ostringstream oss;
		bool needSep = false;

#define STR_DEBUG_FLAG( flag )  \
		if( AVM_DEBUG_FLAG_ENABLED( flag ) )  \
		{ oss << (needSep ? sep : "") << #flag; needSep = true; }

#define STR_DEBUG_GROUP( flag )   \
		if( AVM_DEBUG_FLAG_GROUP_ENABLED( flag ) )  \
		{ oss << (needSep ? sep : "") << #flag; needSep = true; }

		// General Context

		STR_DEBUG_FLAG( PARSING                 )

		STR_DEBUG_FLAG( CONFIGURING             )

		STR_DEBUG_FLAG( COMPILING               )

		STR_DEBUG_FLAG( LOADING                 )

		STR_DEBUG_FLAG( COMPUTING               )

		STR_DEBUG_FLAG( REPORTING               )

		STR_DEBUG_FLAG( SOLVING                 )
//		STR_DEBUG_FLAG( SAT_SOLVING             )
//		STR_DEBUG_FLAG( SMT_SOLVING             )

		STR_DEBUG_FLAG( PROFILING               )


		// Process Stage: Processing, Filtering, ... ...

		STR_DEBUG_FLAG( QUEUE                   )
		STR_DEBUG_FLAG( QUEUING                 )


		// Statement Evaluation

		STR_DEBUG_FLAG( PROGRAM                 )

		STR_DEBUG_FLAG( STATEMENT               )

		STR_DEBUG_FLAG( ASSIGNMENT              )
//		STR_DEBUG_FLAG( STATEMENT_ASSIGNMENT    )

		STR_DEBUG_FLAG( COMMUNICATION           )
//		STR_DEBUG_FLAG( STATEMENT_COMMUNICATION )

		STR_DEBUG_FLAG( STATEMENT_CONTROL       )
		STR_DEBUG_FLAG( STATEMENT_SCHEDULING    )

		STR_DEBUG_FLAG( TEST_DECISION           )
//		STR_DEBUG_FLAG( STATEMENT_TEST_DECISION )

		STR_DEBUG_FLAG( BYTECODE                )

		STR_DEBUG_FLAG( DATA                    )

		STR_DEBUG_FLAG( TRACE                   )


		// Element: Property, Signal...

		STR_DEBUG_FLAG( VARIABLE                )

		STR_DEBUG_FLAG( BUFFER                  )

		STR_DEBUG_FLAG( PORT                    )

		STR_DEBUG_FLAG( SIGNAL                  )

		STR_DEBUG_FLAG( CONNEXION               )

		STR_DEBUG_FLAG( TIME                    )


		// Executable Component...

		STR_DEBUG_FLAG( EXECUTABLE              )

		STR_DEBUG_FLAG( PRIMITIVE               )

		STR_DEBUG_FLAG( ACTIVITY                )

		STR_DEBUG_FLAG( ROUTINE                 )

		STR_DEBUG_FLAG( TRANSITION              )

		STR_DEBUG_FLAG( MACHINE                 )

		STR_DEBUG_FLAG( STATEMACHINE            )


		// Others: [Qualified]NameID, RefCount, ...

		STR_DEBUG_FLAG( NAME_ID                 )

		STR_DEBUG_FLAG( QUALIFIED_NAME_ID       )

		STR_DEBUG_FLAG( FULLY_QUALIFIED_NAME_ID )


		STR_DEBUG_FLAG( CAS                     )

		STR_DEBUG_FLAG( REDUNDANCE              )


		STR_DEBUG_FLAG( REFERENCE_COUNTING      )


		// ... Process Stage: Processing, Filtering, ...
		else
		{
			STR_DEBUG_GROUP( ALL_PROCESS_STAGE      )
			else
			{
				STR_DEBUG_GROUP( PROCESSING         )
				else
				{
					STR_DEBUG_FLAG( PRE_PROCESSING  )

					STR_DEBUG_FLAG( POST_PROCESSING )
				}

				STR_DEBUG_GROUP( FILTERING          )
				else
				{
					STR_DEBUG_FLAG( PRE_FILTERING   )

					STR_DEBUG_FLAG( POST_FILTERING  )
				}
			}
		}

		return( oss.str() );
	}
}



}

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

#ifndef AVM_DEBUG_H_
#define AVM_DEBUG_H_


#include <string>


namespace sep {


#define  AVM_COMPILE_DEBUG_ENABLED
//#undef AVM_COMPILE_DEBUG_ENABLED


#if defined( AVM_COMPILE_DEBUG_ENABLED )


#define AVM_DEBUG_IF( condition )            if( condition ) {

#define AVM_DEBUG_ELSE                       } else {

#define AVM_DEBUG_ELSE_IF( condition )       } else if( condition ) {

#define AVM_DEBUG_ENDIF                      } ;
// << ; >> prevent << else >> without explicit << if >>

#else


#define AVM_DEBUG_IF( condition )            if( false ) {
//#define AVM_DEBUG_IF( condition )          #if( condition )

#define AVM_DEBUG_ELSE                       } else {
//#define AVM_DEBUG_ELSE                     } else if( false ) {
//#define AVM_DEBUG_ELSE                     #else

#define AVM_DEBUG_ELSE_IF( condition )       } else if( false ) {
//#define AVM_DEBUG_ELSE_IF( condition )     #elif( condition )

#define AVM_DEBUG_ENDIF                      } ;
//#define AVM_DEBUG_ENDIF                    #endif


#endif


#define AVM_IF( condition )            if( condition ) {
#define AVM_ELSE_IF( condition )       } else if( condition ) {
#define AVM_ELSE                       } else {
#define AVM_ENDIF                      } ;


/**
 *******************************************************************************
 * AVM DEBUG LEVEL
 *******************************************************************************
 */

extern unsigned short  _AVM_DEBUG_LEVEL_;

enum AVM_DEBUG_LEVEL_T
{
	AVM_DEBUG_ZERO_LEVEL          = 0x00,

	AVM_DEBUG_LOW_STRICT_LEVEL    = 0x01,
	AVM_DEBUG_LOW_LEVEL           = AVM_DEBUG_LOW_STRICT_LEVEL,

	AVM_DEBUG_MEDIUM_STRICT_LEVEL = 0x02,
	AVM_DEBUG_MEDIUM_LEVEL        = AVM_DEBUG_MEDIUM_STRICT_LEVEL
	                              | AVM_DEBUG_LOW_LEVEL,

	AVM_DEBUG_HIGH_STRICT_LEVEL   = 0x04,
	AVM_DEBUG_HIGH_LEVEL          = AVM_DEBUG_HIGH_STRICT_LEVEL
	                              | AVM_DEBUG_MEDIUM_LEVEL,

	AVM_DEBUG_ULTRA_STRICT_LEVEL  = 0x08,
	AVM_DEBUG_ULTRA_LEVEL         = AVM_DEBUG_ULTRA_STRICT_LEVEL
	                              | AVM_DEBUG_HIGH_LEVEL,

	AVM_DEBUG_GOD_MODE_LEVEL      = 0xFF
};


/**
 * DEBUG LEVEL SET
 * DEBUG LEVEL TEST
 */
#define AVM_DEBUG_SET_STRICT_LEVEL( level )  \
	{ _AVM_DEBUG_LEVEL_ = AVM_DEBUG_##level##_STRICT_LEVEL; }

#define AVM_DEBUG_SET_LEVEL( level )  \
	{ _AVM_DEBUG_LEVEL_ = AVM_DEBUG_##level##_LEVEL; }

#define AVM_DEBUG_UNSET_LEVEL( level )  \
	{ _AVM_DEBUG_LEVEL_ &= (~ AVM_DEBUG_##level##_STRICT_LEVEL); }

#define AVM_DEBUG_IS_LEVEL( level )  \
	( _AVM_DEBUG_LEVEL_ == AVM_DEBUG_##level##_LEVEL )

#define AVM_DEBUG_HAS_LEVEL( level )  \
	( (_AVM_DEBUG_LEVEL_ & AVM_DEBUG_##level##_LEVEL) != 0 )


/**
 * DEBUG LEVEL <
 * DEBUG LEVEL <=
 */
#define AVM_DEBUG_LEVEL_LT( level )  \
	( _AVM_DEBUG_LEVEL_ <  AVM_DEBUG_##level##_LEVEL )

#define AVM_DEBUG_LEVEL_LTE( level )  \
	( _AVM_DEBUG_LEVEL_ <= AVM_DEBUG_##level##_LEVEL )


/**
 * DEBUG LEVEL >
 * DEBUG LEVEL >=
 */
#define AVM_DEBUG_LEVEL_GT( level )  \
	( _AVM_DEBUG_LEVEL_ >  AVM_DEBUG_##level##_LEVEL )

#define AVM_DEBUG_LEVEL_GTE( level )  \
	( _AVM_DEBUG_LEVEL_ >= AVM_DEBUG_##level##_LEVEL )



/**
 * DEBUG ENABLED
 */
#define AVM_DEBUG_ENABLED          AVM_DEBUG_LEVEL_GT( ZERO )

#define AVM_IF_DEBUG_ENABLED  \
	AVM_DEBUG_IF( AVM_DEBUG_ENABLED )

#define AVM_ELSEIF_DEBUG_ENABLED  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_ENABLED )

#define AVM_ENDIF_DEBUG_ENABLED  AVM_DEBUG_ENDIF

/**
 * DEBUG ENABLED and CONDITION
 */
#define AVM_DEBUG_ENABLED_AND( condition )  \
	( AVM_DEBUG_ENABLED && (condition) )

#define AVM_IF_DEBUG_ENABLED_AND( condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_ENABLED_AND( condition ) )

#define AVM_ELSEIF_DEBUG_ENABLED_AND( condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_ENABLED_AND( condition ) )

#define AVM_ENDIF_DEBUG_ENABLED_AND  AVM_DEBUG_ENDIF

/**
 * DEBUG ENABLED or CONDITION
 */
#define AVM_DEBUG_ENABLED_OR( condition )  \
	( AVM_DEBUG_ENABLED || (condition) )

#define AVM_IF_DEBUG_ENABLED_OR( condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_ENABLED_OR( condition ) )

#define AVM_ELSEIF_DEBUG_ENABLED_OR( condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_ENABLED_OR( condition ) )

#define AVM_ENDIF_DEBUG_ENABLED_OR  AVM_DEBUG_ENDIF



/**
 * DEBUG  LEVEL > LOW
 */
#define AVM_DEBUG_LEVEL_GT_LOW           AVM_DEBUG_LEVEL_GT( LOW )

#define AVM_IF_DEBUG_LEVEL_GT_LOW  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GT_LOW )

#define AVM_ELSEIF_DEBUG_LEVEL_GT_LOW  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GT_LOW )

#define AVM_ENDIF_DEBUG_LEVEL_GT_LOW  AVM_DEBUG_ENDIF

/**
 * DEBUG  LEVEL >= LOW
 */
#define AVM_DEBUG_LEVEL_GTE_LOW          AVM_DEBUG_LEVEL_GTE( LOW )

#define AVM_IF_DEBUG_LEVEL_GTE_LOW  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GTE_LOW )

#define AVM_ELSEIF_DEBUG_LEVEL_GTE_LOW  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GTE_LOW )

#define AVM_ENDIF_DEBUG_LEVEL_GTE_LOW  AVM_DEBUG_ENDIF



/**
 * DEBUG  LEVEL > MEDIUM
 */
#define AVM_DEBUG_LEVEL_GT_MEDIUM        AVM_DEBUG_LEVEL_GT( MEDIUM )

#define AVM_IF_DEBUG_LEVEL_GT_MEDIUM  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GT_MEDIUM )

#define AVM_ELSEIF_DEBUG_LEVEL_GT_MEDIUM  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GT_MEDIUM )

#define AVM_ENDIF_DEBUG_LEVEL_GT_MEDIUM  AVM_DEBUG_ENDIF

/**
 * DEBUG  ( LEVEL > MEDIUM ) or CONDITION
 */
#define AVM_DEBUG_LEVEL_GT_MEDIUM_OR( condition )  \
	( AVM_DEBUG_LEVEL_GT_MEDIUM || (condition) )

#define AVM_IF_DEBUG_LEVEL_GT_MEDIUM_OR( condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GT_MEDIUM_OR( condition ) )

#define AVM_ELSEIF_DEBUG_LEVEL_GT_MEDIUM_OR( condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GT_MEDIUM_OR( condition ) )

#define AVM_ENDIF_DEBUG_LEVEL_GT_MEDIUM_OR  AVM_DEBUG_ENDIF


/**
 * DEBUG  LEVEL >= MEDIUM
 */
#define AVM_DEBUG_LEVEL_GTE_MEDIUM       AVM_DEBUG_LEVEL_GTE( MEDIUM )

#define AVM_IF_DEBUG_LEVEL_GTE_MEDIUM  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GTE_MEDIUM )

#define AVM_ELSEIF_DEBUG_LEVEL_GTE_MEDIUM  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GTE_MEDIUM )

#define AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM  AVM_DEBUG_ENDIF


/**
 * DEBUG  ( LEVEL > MEDIUM ) or CONDITION
 */
#define AVM_DEBUG_LEVEL_GTE_MEDIUM_OR( condition )  \
	( AVM_DEBUG_LEVEL_GTE_MEDIUM || (condition) )

#define AVM_IF_DEBUG_LEVEL_GTE_MEDIUM_OR( condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GTE_MEDIUM_OR( condition ) )

#define AVM_ELSEIF_DEBUG_LEVEL_GTE_MEDIUM_OR( condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GTE_MEDIUM_OR( condition ) )

#define AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM_OR  AVM_DEBUG_ENDIF


/**
 * DEBUG  LEVEL > HIGH
 */
#define AVM_DEBUG_LEVEL_GT_HIGH          AVM_DEBUG_LEVEL_GT( HIGH )

#define AVM_IF_DEBUG_LEVEL_GT_HIGH  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GT_HIGH )

#define AVM_ELSEIF_DEBUG_LEVEL_GT_HIGH  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GT_HIGH )

#define AVM_ENDIF_DEBUG_LEVEL_GT_HIGH  AVM_DEBUG_ENDIF

/**
 * DEBUG  LEVEL >= HIGH
 */
#define AVM_DEBUG_LEVEL_GTE_HIGH         AVM_DEBUG_LEVEL_GTE( HIGH )

#define AVM_IF_DEBUG_LEVEL_GTE_HIGH  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GTE_HIGH )

#define AVM_ELSEIF_DEBUG_LEVEL_GTE_HIGH  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GTE_HIGH )

#define AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH  AVM_DEBUG_ENDIF


/**
 * DEBUG  LEVEL > ULTRA
 */
#define AVM_DEBUG_LEVEL_GT_ULTRA         AVM_DEBUG_LEVEL_GT( ULTRA )

#define AVM_IF_DEBUG_LEVEL_GT_ULTRA  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GT_ULTRA )

#define AVM_ELSEIF_DEBUG_LEVEL_GT_ULTRA  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GT_ULTRA )

#define AVM_ENDIF_DEBUG_LEVEL_GT_ULTRA  AVM_DEBUG_ENDIF

/**
 * DEBUG  LEVEL >= ULTRA
 */
#define AVM_DEBUG_LEVEL_GTE_ULTRA        AVM_DEBUG_LEVEL_GTE( ULTRA )

#define AVM_IF_DEBUG_LEVEL_GTE_ULTRA  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GTE_ULTRA )

#define AVM_ELSEIF_DEBUG_LEVEL_GTE_ULTRA  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GTE_ULTRA )

#define AVM_ENDIF_DEBUG_LEVEL_GTE_ULTRA  AVM_DEBUG_ENDIF



/**
 * DEBUG  LEVEL < ?
 */
#define AVM_IF_DEBUG_LEVEL_LT( level )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_LT( level ) )

#define AVM_ELSEIF_DEBUG_LEVEL_LT( level )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_LT( level ) )

#define AVM_ENDIF_DEBUG_LEVEL_LT( level )  AVM_DEBUG_ENDIF


/**
 * DEBUG  LEVEL > ?
 */
#define AVM_IF_DEBUG_LEVEL_GT( level )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GT( level ) )

#define AVM_ELSEIF_DEBUG_LEVEL_GT( level )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GT( level ) )

#define AVM_ENDIF_DEBUG_LEVEL_GT( level )  AVM_DEBUG_ENDIF



/**
 * DEBUG  LEVEL <= ?
 */
#define AVM_IF_DEBUG_LEVEL_LTE( level )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_LTE( level ) )

#define AVM_ELSEIF_DEBUG_LEVEL_LTE( level )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_LTE( level ) )

#define AVM_ENDIF_DEBUG_LEVEL_LTE( level )  AVM_DEBUG_ENDIF


/**
 * DEBUG  LEVEL >= ?
 */
#define AVM_IF_DEBUG_LEVEL_GTE( level )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_GTE( level ) )

#define AVM_ELSEIF_DEBUG_LEVEL_GTE( level )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_GTE( level ) )

#define AVM_ENDIF_DEBUG_LEVEL_GTE( level )  AVM_DEBUG_ENDIF


/**
 * DEBUG TEST  LEVEL and CONDITION
 */
#define AVM_DEBUG_LEVEL_AND( level , condition )  \
	( AVM_DEBUG_LEVEL_GTE( level ) && (condition) )

#define AVM_IF_DEBUG_LEVEL_AND( level , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_AND( level , condition ) )

#define AVM_ELSEIF_DEBUG_LEVEL_AND( level , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_AND( level , condition ) )

#define AVM_ENDIF_DEBUG_LEVEL_AND( level )  AVM_DEBUG_ENDIF


/**
 * DEBUG TEST  LEVEL or CONDITION
 */
#define AVM_DEBUG_LEVEL_OR( level , condition )  \
	( AVM_DEBUG_LEVEL_GTE( level ) || (condition) )

#define AVM_IF_DEBUG_LEVEL_OR( level , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_OR( level , condition ) )

#define AVM_ELSEIF_DEBUG_LEVEL_OR( level , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_OR( level , condition ) )

#define AVM_ENDIF_DEBUG_LEVEL_OR( level )  AVM_DEBUG_ENDIF



/**
 *******************************************************************************
 * AVM DEBUG FLAG
 *******************************************************************************
 */

extern std::size_t  _AVM_DEBUG_FLAG_;


/**
 * DEBUG FLAG ENABLE
 * DEBUG FLAG DISABLE
 */
#define AVM_DEBUG_ENABLE_FLAG( flag )  \
	{ _AVM_DEBUG_FLAG_ |= (AVM_DEBUG_##flag##_FLAG); }

#define AVM_DEBUG_DISABLE_FLAG( flag )  \
	{ _AVM_DEBUG_FLAG_ &= (~ (AVM_DEBUG_##flag##_FLAG)); }



/**
 * DEBUG FLAG ENABLED
 * DEBUG FLAG DISABLED
 */
#define AVM_DEBUG_FLAG_ENABLED( flag )    \
	( (_AVM_DEBUG_FLAG_ & (AVM_DEBUG_##flag##_FLAG)) != 0 )

#define AVM_DEBUG_FLAG_GROUP_ENABLED( flag )  \
	( (_AVM_DEBUG_FLAG_ & (AVM_DEBUG_##flag##_FLAG)) ==  \
			(AVM_DEBUG_##flag##_FLAG) )


#define AVM_DEBUG_FLAG_ENABLED2( kind1 , kind2 )  \
	( AVM_DEBUG_FLAG_ENABLED( kind1 ) && AVM_DEBUG_FLAG_ENABLED( kind2 ) )

#define AVM_DEBUG_FLAG_DISABLED( flag )  \
	( (_AVM_DEBUG_FLAG_ & (AVM_DEBUG_##flag##_FLAG)) == 0 )



/**
 * DEBUG TEST  FLAG
 */
#define AVM_DEBUG_FLAG( flag )  \
	( AVM_DEBUG_ENABLED && AVM_DEBUG_FLAG_ENABLED( flag ) )

#define AVM_IF_DEBUG_FLAG( flag )  \
	AVM_DEBUG_IF( AVM_DEBUG_FLAG( flag ) )

#define AVM_ELSEIF_DEBUG_FLAG( flag )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_FLAG( flag ) )

#define AVM_ENDIF_DEBUG_FLAG( flag )  AVM_DEBUG_ENDIF



/**
 * DEBUG TEST  KIND1 and KIN2
 */
 #define AVM_DEBUG_FLAG2( kind1 , kind2 )  \
	( AVM_DEBUG_ENABLED && AVM_DEBUG_FLAG_ENABLED2( kind1 , kind2 ) )

 #define AVM_IF_DEBUG_FLAG2( kind1 , kind2 )  \
	AVM_DEBUG_IF( AVM_DEBUG_FLAG2( kind1 , kind2 ) )

 #define AVM_ELSEIF_DEBUG_FLAG2( kind1 , kind2 )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_FLAG2( kind1 , kind2 ) )

 #define AVM_ENDIF_DEBUG_FLAG2( kind1 , kind2 )  AVM_DEBUG_ENDIF


 /**
  * DEBUG TEST  KIND1 inhibit KIN2)
  */
 #define AVM_DEBUG_FLAG_AND_NOT_FLAG( kind1 , kind2 )  \
	( AVM_DEBUG_FLAG( kind1 ) && AVM_DEBUG_NOT_FLAG( kind2 ) )

 #define AVM_IF_DEBUG_FLAG_AND_NOT_FLAG( kind1 , kind2 )  \
	AVM_DEBUG_IF( AVM_DEBUG_FLAG_AND_NOT_FLAG( kind1 , kind2 ) )

 #define AVM_ELSEIF_DEBUG_FLAG_AND_NOT_FLAG( kind1 , kind2 )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_FLAG_AND_NOT_FLAG( kind1 , kind2 ) )

 #define AVM_ENDIF_DEBUG_FLAG_AND_NOT_FLAG( kind1 , kind2 )  AVM_DEBUG_ENDIF



/**
 * DEBUG TEST  FLAG and CONDITION
 */
#define AVM_DEBUG_FLAG_AND( flag , condition )  \
	( AVM_DEBUG_FLAG( flag ) && (condition) )

#define AVM_IF_DEBUG_FLAG_AND( flag , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_FLAG_AND( flag , condition ) )

#define AVM_ELSEIF_DEBUG_FLAG_AND( flag , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_FLAG_AND( flag , condition ) )

#define AVM_ENDIF_DEBUG_FLAG_AND( flag )  AVM_DEBUG_ENDIF



/**
 * DEBUG TEST  KIND1 and KIND2 and CONDITION
 */
 #define AVM_DEBUG_FLAG2_AND( kind1 , kind2 , condition )  \
	( AVM_DEBUG_FLAG2( kind1 , kind2 ) && (condition) )

 #define AVM_IF_DEBUG_FLAG2_AND( kind1 , kind2 , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_FLAG2_AND( kind1 , kind2 , condition ) )

 #define AVM_ELSEIF_DEBUG_FLAG2_AND( kind1 , kind2 , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_FLAG_AND( kind1 , kind2 , condition ) )

 #define AVM_ENDIF_DEBUG_FLAG2_AND( kind1 , kind2 )  AVM_DEBUG_ENDIF



/**
 * DEBUG TEST  FLAG or CONDITION
 */
#define AVM_DEBUG_FLAG_OR( flag , condition )  \
	( AVM_DEBUG_FLAG( flag ) || (condition) )

#define AVM_IF_DEBUG_FLAG_OR( flag , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_FLAG_OR( flag , condition ) )

#define AVM_ELSEIF_DEBUG_FLAG_OR( flag , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_FLAG_OR( flag , condition ) )

#define AVM_ENDIF_DEBUG_FLAG_OR( flag )  AVM_DEBUG_ENDIF




/**
 * DEBUG TEST  not FLAG
 */
#define AVM_DEBUG_NOT_FLAG( flag )       AVM_DEBUG_FLAG_DISABLED( flag )

#define AVM_IF_DEBUG_NOT_FLAG( flag )  \
	AVM_DEBUG_IF( AVM_DEBUG_NOT_FLAG( flag ) )

#define AVM_ELSEIF_DEBUG_NOT_FLAG( flag )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_NOT_FLAG( flag ) )

#define AVM_ENDIF_DEBUG_NOT_FLAG( flag )  AVM_DEBUG_ENDIF



/**
 * DEBUG TEST  ( not FLAG ) and CONDITION
 */
#define AVM_DEBUG_NOT_FLAG_AND( flag , condition )  \
	( AVM_DEBUG_NOT_FLAG( flag ) && (condition) )

#define AVM_IF_DEBUG_NOT_FLAG_AND( flag , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_NOT_FLAG_AND( flag , condition ) )

#define AVM_ELSEIF_DEBUG_NOT_FLAG_AND( flag , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_NOT_FLAG_AND( flag , condition ) )

#define AVM_ENDIF_DEBUG_NOT_FLAG_AND( flag )  AVM_DEBUG_ENDIF



/**
 * DEBUG TEST  LEVEL and FLAG
 */
#define AVM_DEBUG_LEVEL_FLAG( level , flag )  \
	( AVM_DEBUG_LEVEL_GTE( level ) && AVM_DEBUG_FLAG_ENABLED( flag ) )

#define AVM_IF_DEBUG_LEVEL_FLAG( level , flag )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_FLAG( level , flag ) )

#define AVM_ELSEIF_DEBUG_LEVEL_FLAG( level , flag )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_FLAG( level , flag ) )

#define AVM_ENDIF_DEBUG_LEVEL_FLAG( level , flag )  AVM_DEBUG_ENDIF


/**
 * DEBUG TEST  not ( LEVEL and FLAG )
 */
#define AVM_DEBUG_NOT2_LEVEL_FLAG( level , flag )  \
	( AVM_DEBUG_LEVEL_LT( level ) || AVM_DEBUG_FLAG_DISABLED( flag ) )

#define AVM_IF_DEBUG_NOT2_LEVEL_FLAG( level , flag )  \
	AVM_DEBUG_IF( AVM_DEBUG_NOT2_LEVEL_FLAG( level , flag ) )

#define AVM_ELSEIF_DEBUG_NOT2_LEVEL_FLAG( level , flag )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_NOT2_LEVEL_FLAG( level , flag ) )

#define AVM_ENDIF_DEBUG_NOT2_LEVEL_FLAG( level , flag )  AVM_DEBUG_ENDIF


/**
 * DEBUG TEST  LEVEL or FLAG
 */
#define AVM_DEBUG_LEVEL_OR_FLAG( level , flag )  \
	( AVM_DEBUG_LEVEL_GTE( level ) ||  \
			AVM_DEBUG_ENABLED_AND( AVM_DEBUG_FLAG_ENABLED( flag ) ) )

#define AVM_IF_DEBUG_LEVEL_OR_FLAG( level , flag )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_OR_FLAG( level , flag ) )

#define AVM_ELSEIF_DEBUG_LEVEL_OR_FLAG( level , flag )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_OR_FLAG( level , flag ) )

#define AVM_ENDIF_DEBUG_LEVEL_OR_FLAG( level , flag )  AVM_DEBUG_ENDIF



 /**
  * DEBUG TEST  LEVEL or FLAG
  */
 #define AVM_DEBUG_LEVEL_OR_FLAG2( level , kind1 , kind2 )  \
	( AVM_DEBUG_LEVEL_GTE( level ) ||  \
			AVM_DEBUG_ENABLED_AND( AVM_DEBUG_FLAG_ENABLED2( kind1 , kind2 ) ) )

 #define AVM_IF_DEBUG_LEVEL_OR_FLAG2( level , kind1 , kind2 )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_OR_FLAG2( level , kind1 , kind2 ) )

 #define AVM_ELSEIF_DEBUG_LEVEL_OR_FLAG2( level , kind1 , kind2 )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_OR_FLAG2( level , kind1 , kind2 ) )

 #define AVM_ENDIF_DEBUG_LEVEL_OR_FLAG2( level , kind1 , kind2 ) AVM_DEBUG_ENDIF



/**
 * DEBUG TEST  LEVEL and KIND1 and KIND2
 */
#define AVM_DEBUG_LEVEL_FLAG2( level , kind1 , kind2 )  \
	( AVM_DEBUG_LEVEL_GTE( level ) && AVM_DEBUG_FLAG_ENABLED2( kind1 , kind2 ) )

#define AVM_IF_DEBUG_LEVEL_FLAG2( level , kind1 , kind2 )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_FLAG2( level , kind1 , kind2 ) )

#define AVM_ELSEIF_DEBUG_LEVEL_FLAG2( level , kind1 , kind2 )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_FLAG2( level , kind1 , kind2 ) )

#define AVM_ENDIF_DEBUG_LEVEL_FLAG2( level , kind1 , kind2 )  AVM_DEBUG_ENDIF


 /**
  * DEBUG TEST  LEVEL and FLAG and CONDITION
  */
 #define AVM_DEBUG_LEVEL_FLAG_AND( level , flag , condition )  \
	( AVM_DEBUG_LEVEL_FLAG( level , flag ) && (condition) )

 #define AVM_IF_DEBUG_LEVEL_FLAG_AND( level , flag , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_FLAG_AND( level , flag , condition ) )

 #define AVM_ELSEIF_DEBUG_LEVEL_FLAG_AND( level , flag , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_FLAG_AND( level , flag , condition ) )

 #define AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( level , flag )  AVM_DEBUG_ENDIF


 /**
  * DEBUG TEST  LEVEL and KIND2 and CONDITION
  */
 #define AVM_DEBUG_LEVEL_FLAG2_AND( level , flag , kind2 , condition )  \
	( AVM_DEBUG_LEVEL_FLAG2( level , flag , kind2 ) && (condition) )

 #define AVM_IF_DEBUG_LEVEL_FLAG2_AND( level , flag , kind2 , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_FLAG2_AND( level , flag , kind2 , condition ) )

 #define AVM_ELSEIF_DEBUG_LEVEL_FLAG2_AND( level , flag , kind2 , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_FLAG2_AND( level , flag , kind2 , condition ) )

 #define AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND( level , flag , kind2 ) AVM_DEBUG_ENDIF


/**
 * DEBUG TEST  (LEVEL and FLAG) or CONDITION
 */
#define AVM_DEBUG_LEVEL_FLAG_OR( level , flag , condition )  \
	( AVM_DEBUG_LEVEL_FLAG( level , flag ) || (condition) )

#define AVM_IF_DEBUG_LEVEL_FLAG_OR( level , flag , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_FLAG_OR( level , flag , condition ) )

#define AVM_ELSEIF_DEBUG_LEVEL_FLAG_OR( level , flag , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_FLAG_OR( level , flag , condition ) )

#define AVM_ENDIF_DEBUG_LEVEL_FLAG_OR( level , flag )  AVM_DEBUG_ENDIF



 /**
  * DEBUG TEST  ( LEVEL or FLAG ) and CONDITION
  */
 #define AVM_DEBUG_LEVEL_OR_FLAG_AND( level , flag , condition )  \
	( ( AVM_DEBUG_LEVEL_GTE( level ) ||  \
		AVM_DEBUG_ENABLED_AND( AVM_DEBUG_FLAG_ENABLED( flag ) ) ) && \
	(condition) )

 #define AVM_IF_DEBUG_LEVEL_OR_FLAG_AND( level , flag , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_OR_FLAG_AND( level , flag , condition ) )

 #define AVM_ELSEIF_DEBUG_LEVEL_OR_FLAG_AND( level , flag , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_OR_FLAG_AND( level , flag , condition ) )

 #define AVM_ENDIF_DEBUG_LEVEL_OR_FLAG_AND( level , flag )  AVM_DEBUG_ENDIF


 /**
  * DEBUG TEST  ( LEVEL or FLAG ) or CONDITION
  */
 #define AVM_DEBUG_LEVEL_OR_FLAG_OR( level , flag , condition )  \
	( AVM_DEBUG_LEVEL_GTE( level ) ||  \
	AVM_DEBUG_ENABLED_AND( AVM_DEBUG_FLAG_ENABLED( flag ) ) || (condition) )

 #define AVM_IF_DEBUG_LEVEL_OR_FLAG_OR( level , flag , condition )  \
	AVM_DEBUG_IF( AVM_DEBUG_LEVEL_OR_FLAG_OR( level , flag , condition ) )

 #define AVM_ELSEIF_DEBUG_LEVEL_OR_FLAG_OR( level , flag , condition )  \
	AVM_DEBUG_ELSE_IF( AVM_DEBUG_LEVEL_OR_FLAG_OR( level , flag , condition ) )

 #define AVM_ENDIF_DEBUG_LEVEL_OR_FLAG_OR( level , flag )  AVM_DEBUG_ENDIF



/**
 * DEBUG FLAG ENUMERATION
 * on 64 bits max
 */

enum AVM_DEBUG_FLAG_T
{
	AVM_DEBUG_NOTHING_FLAG                  = 0x0000000000000000,

	// General Context
	AVM_DEBUG_CONFIGURING_FLAG              = 0x0000000000000001,
	AVM_DEBUG_PARSING_FLAG                  = 0x0000000000000002,
	AVM_DEBUG_COMPILING_FLAG                = 0x0000000000000004,
	AVM_DEBUG_LOADING_FLAG                  = 0x0000000000000008,

	AVM_DEBUG_COMPUTING_FLAG                = 0x0000000000000010,
	AVM_DEBUG_REPORTING_FLAG                = 0x0000000000000020,

	AVM_DEBUG_SOLVING_FLAG                  = 0x0000000000000040,
	AVM_DEBUG_SAT_SOLVING_FLAG              = AVM_DEBUG_SOLVING_FLAG,
	AVM_DEBUG_SMT_SOLVING_FLAG              = AVM_DEBUG_SOLVING_FLAG,

	AVM_DEBUG_PROFILING_FLAG                = 0x0000000000000080,

	// Process Stage: Processing, Filtering, ...
	AVM_DEBUG_PRE_PROCESSING_FLAG           = 0x0000000000000100,
	AVM_DEBUG_POST_PROCESSING_FLAG          = 0x0000000000000200,

	AVM_DEBUG_PROCESSING_FLAG               = AVM_DEBUG_PRE_PROCESSING_FLAG
	                                        | AVM_DEBUG_POST_PROCESSING_FLAG,

	AVM_DEBUG_PRE_FILTERING_FLAG            = 0x0000000000000400,
	AVM_DEBUG_POST_FILTERING_FLAG           = 0x0000000000000800,

	AVM_DEBUG_FILTERING_FLAG                = AVM_DEBUG_PRE_FILTERING_FLAG
	                                        | AVM_DEBUG_POST_FILTERING_FLAG,

	AVM_DEBUG_QUEUE_FLAG                    = 0x0000000000001000,
	AVM_DEBUG_QUEUING_FLAG                  = AVM_DEBUG_QUEUE_FLAG,

	AVM_DEBUG_ALL_PROCESS_STAGE_FLAG        = AVM_DEBUG_PROCESSING_FLAG
	                                        | AVM_DEBUG_FILTERING_FLAG,

	AVM_DEBUG_PROCESSOR_FLAG                = AVM_DEBUG_ALL_PROCESS_STAGE_FLAG,

	// Statement Evaluation
	AVM_DEBUG_PROGRAM_FLAG                  = 0x0000000000002000,
	AVM_DEBUG_STATEMENT_FLAG                = 0x0000000000010000,

	AVM_DEBUG_ASSIGNMENT_FLAG               = 0x0000000000020000,
	AVM_DEBUG_STATEMENT_ASSIGNMENT_FLAG     = AVM_DEBUG_ASSIGNMENT_FLAG,

	AVM_DEBUG_COMMUNICATION_FLAG            = 0x0000000000040000,
	AVM_DEBUG_STATEMENT_COMMUNICATION_FLAG  = AVM_DEBUG_COMMUNICATION_FLAG,

	AVM_DEBUG_STATEMENT_CONTROL_FLAG        = 0x0000000000080000,
	AVM_DEBUG_STATEMENT_SCHEDULING_FLAG     = 0x0000000000100000,

	AVM_DEBUG_TEST_DECISION_FLAG            = 0x0000000000200000,
	AVM_DEBUG_STATEMENT_TEST_DECISION_FLAG  = AVM_DEBUG_TEST_DECISION_FLAG,

	AVM_DEBUG_BYTECODE_FLAG                 = 0x0000000000800000,

	AVM_DEBUG_DATA_FLAG                     = 0x0000000001000000,

	AVM_DEBUG_TRACE_FLAG                    = 0x0000000002000000,

	// Element: Property, Signal...
	AVM_DEBUG_VARIABLE_FLAG                 = 0x0000000010000000,
	AVM_DEBUG_BUFFER_FLAG                   = 0x0000000020000000,
	AVM_DEBUG_PORT_FLAG                     = 0x0000000040000000,
	AVM_DEBUG_SIGNAL_FLAG                   = 0x0000000080000000,
	AVM_DEBUG_CONNEXION_FLAG                = 0x0000000100000000,

	AVM_DEBUG_TIME_FLAG                     = 0x0000000200000000,

	// Executable Component...
	AVM_DEBUG_EXECUTABLE_FLAG               = 0x0000001000000000,
	AVM_DEBUG_PRIMITIVE_FLAG                = 0x0000002000000000,
	AVM_DEBUG_ACTIVITY_FLAG                 = 0x0000004000000000,
	AVM_DEBUG_ROUTINE_FLAG                  = 0x0000008000000000,
	AVM_DEBUG_TRANSITION_FLAG               = 0x0000010000000000,
	AVM_DEBUG_MACHINE_FLAG                  = 0x0000020000000000,
	AVM_DEBUG_STATEMACHINE_FLAG             = 0x0000040000000000,

	// Others: [Qualified]NameID, RefCount, ...
	AVM_DEBUG_NAME_ID_FLAG                  = 0x0000100000000000,
	AVM_DEBUG_QUALIFIED_NAME_ID_FLAG        = 0x0000200000000000,
	AVM_DEBUG_FULLY_QUALIFIED_NAME_ID_FLAG  = 0x0000400000000000,

	AVM_DEBUG_CAS_FLAG                      = 0x0001000000000000,
	AVM_DEBUG_REDUNDANCE_FLAG               = 0x0002000000000000,

	AVM_DEBUG_REFERENCE_COUNTING_FLAG       = 0x0010000000000000,

	// God Mode
	AVM_DEBUG_ALL_FLAG                      = 0xFFFFFFFFFFFFFFFF,
	AVM_DEBUG_GOD_MODE_FLAG                 = 0xFFFFFFFFFFFFFFFF

};


/**
 *******************************************************************************
 * AVM DEBUG CONFIGURE
 *******************************************************************************
 */

void avm_setDebugLevel(std::string strDebugLevel);

void avm_unsetDebugLevel(std::string strDebugLevel);

std::string avm_strDebugLevel();


inline bool avm_hasDebugFlag()
{
	return( _AVM_DEBUG_FLAG_ != AVM_DEBUG_NOTHING_FLAG );
}

void avm_setDebugFlag(std::string strDebugFlag);

void avm_unsetDebugFlag(std::string strDebugFlag);

std::string avm_strDebugFlag(const std::string & sep = " ");



}


#endif /* AVM_DEBUG_H_ */

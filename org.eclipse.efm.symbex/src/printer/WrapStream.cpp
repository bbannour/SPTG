/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 juin 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#include "WrapStream.h"

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>


namespace sep {

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// WrapOstream
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

WrapData DEFAULT_WRAP_DATA( 80, 0, 4, "\n\t" );


bool WrapData::configure(const WObject * wfParameterObject)
{
	if( wfParameterObject != WObject::_NULL_ )
	{
		TAB_WIDTH = Query::getRegexWPropertyPosSizeT(wfParameterObject,
				CONS_WID3("char", "tab", "width"),
				DEFAULT_WRAP_DATA.TAB_WIDTH);

		LINE_WIDTH = Query::getRegexWPropertyPosSizeT(wfParameterObject,
				CONS_WID3("line", "wrap", "width"),
				DEFAULT_WRAP_DATA.LINE_WIDTH);

		SEPARATOR = Query::getRegexWPropertyString(wfParameterObject,
				CONS_WID3("line", "wrap", "separator"),
				DEFAULT_WRAP_DATA.SEPARATOR);

		StringTools::replaceAllEscapeSequences(DEFAULT_WRAP_DATA.SEPARATOR);
	}

	return( true );
}


// This is basically a line-buffering stream mBuffer.
// The algorithm is:
// - Explicit end of line ("\r" or "\n"): we flush our mBuffer
//   to the underlying stream's mBuffer, and set our record of
//   the line length to 0.
// - An "alert" character: sent to the underlying stream
//   without recording its length, since it doesn't normally
//   affect the a appearance of the output.
// - tab: treated as occupying `tab_width` characters, but is
//   passed through undisturbed (but if we wanted to expand it
//   to `tab_width` spaces, that would be pretty easy to do so
//   you could adjust the tab-width if you wanted.
// - Everything else: really basic buffering with word wrapping.
//   We try to add the character to the mBuffer, and if it exceeds
//   our line width, we search for the last space/tab in the
//   mBuffer and break the line there. If there is no space/tab,
//   we break the line at the limit.
WrapStreambuf::int_type WrapStreambuf::overflow(int_type c)
{
	if (traits_type::eq_int_type(traits_type::eof(), c))
	{
		return traits_type::not_eof(c);
	}
	switch (c)
	{
		case '\n':
		case '\r':
		{
			mBuffer += c;
			mCharCount = 0;

			int_type rc = mStreambuf->sputn(mBuffer.c_str(), mBuffer.size());

			mBuffer.clear();

			return rc;
		}

		case '\a':
		{
			return mStreambuf->sputc(c);
		}

		case '\t':
		{
			if( mCharCount > mWrapData.LINE_WIDTH )
			{
				mStreambuf->sputn(mWrapData.SEPARATOR.c_str(),
						mWrapData.SEPARATOR.size());

				mCharCount = mBuffer.size();
			}

			mBuffer += c;
			mCharCount += (mWrapData.TAB_WIDTH -
					mCharCount % mWrapData.TAB_WIDTH);

			mStreambuf->sputn(mBuffer.c_str(), mBuffer.size());
			mBuffer.clear();

			return c;
		}
		case ' ':
		case ')':
		case '}':
		case ']':
		case '/':
//		case '.':
		{
			if( mCharCount > mWrapData.LINE_WIDTH )
			{
				mStreambuf->sputn(mWrapData.SEPARATOR.c_str(),
						mWrapData.SEPARATOR.size());
				mCharCount = mBuffer.size();
			}

			mBuffer += c;
			++mCharCount;

			mStreambuf->sputn(mBuffer.c_str(), mBuffer.size());
			mBuffer.clear();

			return c;
		}


		default:
		{
			if( mBuffer.size() >= mWrapData.LINE_WIDTH )
			{
				mStreambuf->sputn(mBuffer.c_str(), mBuffer.size());
				mBuffer.clear();

				mStreambuf->sputn(mWrapData.SEPARATOR.c_str(),
						mWrapData.SEPARATOR.size());

				mCharCount = 0;
			}

//			if (mCharCount >= mWrapData.LINE_WIDTH)
//			{
//				string_type::size_type wpos = mBuffer.find_last_of(" \t");
//				if (wpos != string_type::npos)
//				{
//					mStreambuf->sputn(mBuffer.c_str(), wpos);
//					mCharCount = mBuffer.size()-wpos-1;
//					mBuffer = string_type(mBuffer, wpos+1);
//				}
//				else
//				{
//					mStreambuf->sputn(mBuffer.c_str(), mBuffer.size());
//					mBuffer.clear();
//					mCharCount = 0;
//				}
//				mStreambuf->sputc('\n');
//			}

			mBuffer += c;
			++mCharCount;

			return c;
		}
	}
}


} /* namespace sep */

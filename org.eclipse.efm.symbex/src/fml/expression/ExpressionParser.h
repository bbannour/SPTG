/*******************************************************************************
 * Copyright (c) 2019 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 03 avr. 2019
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
/**
 * Using The C++ Mathematical Expression Toolkit Library (ExprTk)
 * http://partow.net/programming/exprtk/index.html
 */

#ifndef EXPRESSIONPARSER_H_
#define EXPRESSIONPARSER_H_

#include <limits>
#include <sstream>
#include <string>
#include <vector>

#include <common/BF.h>
#include <fml/expression/AvmCode.h>


namespace sep
{

class Machine;
class Operator;

class ExpressionParser
{

protected:
	/**
	 * TYPEDEFS
	 */

	typedef unsigned char     uchar_t;
	typedef char               char_t;
	typedef uchar_t*        uchar_ptr;
	typedef char_t*          char_ptr;
	typedef uchar_t const* uchar_cptr;
	typedef char_t const*   char_cptr;


	////////////////////////////////////////////////////////////////////////////
	// TOKEN UTILS
	////////////////////////////////////////////////////////////////////////////

	struct Token
	{
		// TYPEDEF
		enum token_type
		{
			T_NONE         =   0 , T_ERROR        =   1 , T_ERROR_SYMBOL =   2,
			T_ERROR_NUMBER =   3 , T_ERROR_STRING =   4 , T_ERROR_SFUNC  =   5,
			T_SEMI         =   6 , T_NUMBER       =   7 , T_SYMBOL       =   8,
			T_STRING_DQ    =   9 , T_STRING_SQ    =  10 ,

			T_ADD_ASSIGN   =  11 , T_SUB_ASSIGN   =  12 , T_MULT_ASSIGN  =  13,
			T_DIV_ASSIGN   =  14 , T_MOD_ASSIGN   =  15 , T_POW_ASSIGN   =  16,
			T_RSHIFT       =  17 , T_LSHIFT       =  18 ,
			T_EQ           =  19 , T_NEQ          =  20 ,
			T_SEQ          =  21,  T_NSEQ         =  22 ,
			T_LTE          =  23 , T_GTE          =  24 ,

			T_LOR          =  25 , T_LAND         =  26 , T_LNOT         =  27,
			T_BOR          =  28 , T_BXOR         =  29 , T_BAND         =  230,
			T_BNOT         =  31 ,

			T_LT           = '<' , T_GT           = '>' , T_ASSIGN       = '=',
			T_RPAREN       = ')' , T_LPAREN       = '(' , T_RBRACKET     = ']',
			T_LBRACKET     = '[' , T_RCURLY       = '}' , T_LCURLY       = '{',
			T_COMMA        = ',' , T_ADD          = '+' , T_SUB          = '-',
			T_DIV          = '/' , T_MULT         = '*' , T_MOD          = '%',
			T_POW          = '^' , T_COLON        = ':' , T_TERNARY      = '?'
		};

		// ATTRIBUTES
		token_type type;
		std::string value;
		std::size_t position;

		// CONSTRUCTOR
		Token()
		: type(T_NONE),
		  value(""),
		  position(std::numeric_limits<std::size_t>::max())
		{
			//!! NOTHING
		}

		void clear()
		{
			type     = T_NONE;
			value    = "";
			position = std::numeric_limits<std::size_t>::max();
		}

		template <typename Iterator>
		inline Token& set_operator(const token_type tt,
				const Iterator begin, const Iterator end,
				const Iterator base_begin = Iterator(0))
		{
			type = tt;
			value.assign(begin,end);
			if (base_begin)
				position = static_cast<std::size_t>(std::distance(base_begin,begin));
			return (*this);
		}

		template <typename Iterator>
		inline Token& set_symbol(const Iterator begin, const Iterator end, const Iterator base_begin = Iterator(0))
		{
			type = T_SYMBOL;
			value.assign(begin,end);
			if (base_begin)
				position = static_cast<std::size_t>(std::distance(base_begin,begin));
			return (*this);
		}

		template <typename Iterator>
		inline Token& set_numeric(const Iterator begin, const Iterator end, const Iterator base_begin = Iterator(0))
		{
			type = T_NUMBER;
			value.assign(begin,end);
			if (base_begin)
				position = static_cast<std::size_t>(std::distance(base_begin,begin));
			return (*this);
		}

		template <typename Iterator>
		inline Token& set_string(char_t delimiter,
				const Iterator begin, const Iterator end, const Iterator base_begin = Iterator(0))
		{
			type = ('"' == delimiter) ? T_STRING_DQ : T_STRING_SQ;
			value.assign(begin,end);
			if (base_begin)
				position = static_cast<std::size_t>(std::distance(base_begin,begin));
			return (*this);
		}

		inline Token& set_string(char_t delimiter, const std::string& s, const std::size_t p)
		{
			type     = ('"' == delimiter) ? T_STRING_DQ : T_STRING_SQ;
			value    = s;
			position = p;
			return (*this);
		}

		template <typename Iterator>
		inline Token& set_error(const token_type et,
				const Iterator begin, const Iterator end,
				const Iterator base_begin = Iterator(0))
		{
			if (
					(T_ERROR        == et) ||
					(T_ERROR_SYMBOL == et) ||
					(T_ERROR_NUMBER == et) ||
					(T_ERROR_STRING == et) ||
					(T_ERROR_SFUNC  == et)
			)
			{
				type = et;
			}
			else
				type = T_ERROR;

			value.assign(begin,end);

			if (base_begin)
				position = static_cast<std::size_t>(std::distance(base_begin,begin));

			return (*this);
		}

		inline std::string str_type() const
		{
			switch (type)
			{
				case T_NONE         : return "NONE";
				case T_ERROR        : return "ERROR";
				case T_ERROR_SYMBOL : return "ERROR_SYMBOL";
				case T_ERROR_NUMBER : return "ERROR_NUMBER";
				case T_ERROR_STRING : return "ERROR_STRING";
				case T_ERROR_SFUNC  : return "ERROR_SFUNCTION";

				case T_SEMI          : return "SEMI";

				case T_NUMBER       : return "NUMBER";
				case T_SYMBOL       : return "SYMBOL";
				case T_STRING_DQ    : return "STRING";
				case T_STRING_SQ    : return "STRING";

				case T_ASSIGN       : return ":=";
				case T_ADD_ASSIGN   : return "+=";
				case T_SUB_ASSIGN   : return "-=";
				case T_MULT_ASSIGN  : return "*=";
				case T_DIV_ASSIGN   : return "/=";
				case T_MOD_ASSIGN   : return "%=";
				case T_POW_ASSIGN   : return "^=";

				case T_RSHIFT       : return ">>";
				case T_LSHIFT       : return "<<";

				case T_LOR          : return "||";
				case T_LAND         : return "&&";
				case T_LNOT         : return "!";

				case T_BOR          : return "|";
				case T_BXOR         : return "^";
				case T_BAND         : return "&";
				case T_BNOT         : return "~";

				case T_EQ           : return "==";
				case T_NEQ          : return "!=";
				case T_SEQ           : return "===";
				case T_NSEQ          : return "=!=";
				case T_LTE          : return "<=";
				case T_GTE          : return ">=";
				case T_LT           : return "<";
				case T_GT           : return ">";

				case T_RPAREN       : return ")";
				case T_LPAREN       : return "(";
				case T_RBRACKET     : return "]";
				case T_LBRACKET     : return "[";
				case T_RCURLY       : return "}";
				case T_LCURLY       : return "{";

				case T_COMMA        : return ",";
				case T_ADD          : return "+";
				case T_SUB          : return "-";
				case T_DIV          : return "/";
				case T_MULT         : return "*";
				case T_MOD          : return "%";
				case T_POW          : return "^";
				case T_COLON        : return ":";
				case T_TERNARY      : return "?:";
//				case T_SWAP         : return "<=>";
				default             : return "UNKNOWN";
			}
		}

		inline bool is_error() const
		{
			return (
					(T_ERROR        == type) ||
					(T_ERROR_SYMBOL == type) ||
					(T_ERROR_NUMBER == type) ||
					(T_ERROR_STRING == type) ||
					(T_ERROR_SFUNC  == type)
			);
		}

		inline void print(int index) const
		{
			std::string format;
			switch (type)
			{
				case T_NUMBER :
				case T_SYMBOL :
				{
					format = "Token[%02d] @ %03d  %6s  -->  %s\n";
					break;
				}
				case T_STRING_DQ :
				{
					format = "Token[%02d] @ %03d  %6s  -->  \"%s\"\n";
					break;
				}
				case T_STRING_SQ :
				{
					format = "Token[%02d] @ %03d  %6s  -->  '%s'\n";
					break;
				}

				default:
				{
					format = "Token[%02d] @ %03d  %6s  -->  '%s'\n";
					break;
				}
			}

			printf( format.c_str(),
					static_cast<int>(index),
					static_cast<int>(position),
					str_type().c_str(),
					value.c_str());
		}

		inline std::string str() const
		{
			std::ostringstream oss;

			oss << "Token< type: " << str_type()
				<< "  value: " << value << "  pos: " << position << " >";

			return oss.str();
		}

	};


	struct Lexer
	{

		/**
		 * ATTRIBUTES
		 */
		const std::string & rawExpression;

		std::vector<Token> tokens;

		std::string lastError;

		// LEXER VARS
		Token eof_token_;

		std::vector<Token>::iterator token_itr_;
		std::vector<Token>::iterator store_token_itr_;

		char_cptr base_itr_;
		char_cptr s_itr_;
		char_cptr s_end_;


		Lexer(const std::string & rawExpr)
		: rawExpression( rawExpr ),

		tokens( ),

		lastError( ),

		eof_token_( ),

		base_itr_(nullptr),
		s_itr_   (nullptr),
		s_end_   (nullptr)
		{
			//!! NOTHING
		}

		/**
		 * DESTRUCTOR
		 */
		~Lexer()
		{
			//!! NOTHING
		}


		/**
		 * GETTERS
		 */
		inline const std::string & error() const
		{
			return lastError;
		}

		/**
		 * TOKENS
		 */
		inline void printTokens()
		{
			for (std::size_t i = 0; i < tokens.size(); ++i)
			{
				tokens[i].print(i);
			}
		}


		////////////////////////////////////////////////////////////////////////
		// LEXER UTILS
		////////////////////////////////////////////////////////////////////////

		inline bool is_whitespace(const char_t c)
		{
			return  (' '  == c) || ('\n' == c) ||
					('\r' == c) || ('\t' == c) ||
					('\b' == c) || ('\v' == c) ||
					('\f' == c) ;
		}

		inline bool is_operator_char(const char_t c)
		{
			return  ('+' == c) || ('-' == c) ||
					('*' == c) || ('/' == c) ||
					('^' == c) || ('<' == c) ||
					('>' == c) || ('=' == c) ||
					(',' == c) || ('!' == c) ||
					('(' == c) || (')' == c) ||
					('[' == c) || (']' == c) ||
					('{' == c) || ('}' == c) ||
					('%' == c) || (':' == c) ||
					('?' == c) || ('&' == c) ||
					('|' == c) || ('~' == c) ||
					(';' == c) ;
		}

		inline bool is_letter(const char_t c)
		{
			return  (('a' <= c) && (c <= 'z')) ||
					(('A' <= c) && (c <= 'Z')) ||
					('_' == c);
		}

		inline bool is_xletter(const char_t c)
		{
			return is_letter(c) || ('#' == c) || ('$' == c);
		}

		inline bool is_digit(const char_t c)
		{
			return ('0' <= c) && (c <= '9');
		}

		inline bool is_xletter_or_digit(const char_t c)
		{
			return is_xletter(c) || is_digit(c);
		}

		inline bool is_left_bracket(const char_t c)
		{
			return ('(' == c) || ('[' == c) || ('{' == c);
		}

		inline bool is_right_bracket(const char_t c)
		{
			return (')' == c) || (']' == c) || ('}' == c);
		}

		inline bool is_bracket(const char_t c)
		{
			return is_left_bracket(c) || is_right_bracket(c);
		}

		inline bool is_sign(const char_t c)
		{
			return ('+' == c) || ('-' == c);
		}

		inline bool is_invalid(const char_t c)
		{
			return  !is_whitespace      (c) &&
					!is_operator_char   (c) &&
					!is_xletter_or_digit(c) &&
					('.'  != c)             &&
					('$'  != c)             &&
					('\'' != c);
		}


		inline void case_normalise(std::string&)
		{
			//!! NOTHING
		}

		inline bool imatch(const char_t c1, const char_t c2)
		{
			return c1 == c2;
		}

		inline bool imatch(const std::string& s1, const std::string& s2)
		{
			return s1 == s2;
		}

		struct ilesscompare
		{
			inline bool operator() (const std::string& s1, const std::string& s2) const
			{
				return s1 < s2;
			}
		};

		inline bool is_hex_digit(const std::string::value_type digit)
		{
			return  (('0' <= digit) && (digit <= '9')) ||
					(('A' <= digit) && (digit <= 'F')) ||
					(('a' <= digit) && (digit <= 'f')) ;
		}


		inline uchar_t hex_to_bin(uchar_t h)
		{
			if (('0' <= h) && (h <= '9'))
				return (h - '0');
			else
				return static_cast<unsigned char>(std::toupper(h) - 'A');
		}

		template <typename Iterator>
		inline void parse_hex(Iterator& itr, Iterator end, std::string::value_type& result)
		{
			if (
					(end !=  (itr    )) &&
					(end !=  (itr + 1)) &&
					(end !=  (itr + 2)) &&
					(end !=  (itr + 3)) &&
					('0' == *(itr    )) &&
					(
						('x' == *(itr + 1)) ||
						('X' == *(itr + 1))
					) &&
					(is_hex_digit(*(itr + 2))) &&
					(is_hex_digit(*(itr + 3)))
			)
			{
				result = hex_to_bin(static_cast<uchar_t>(*(itr + 2))) << 4 |
						hex_to_bin(static_cast<uchar_t>(*(itr + 3))) ;
				itr += 3;
			}
			else
				result = '\0';
		}

		inline void cleanup_escapes(std::string& s)
		{
			typedef std::string::iterator str_itr_t;

			str_itr_t itr1 = s.begin();
			str_itr_t itr2 = s.begin();
			str_itr_t end  = s.end  ();

			std::size_t removal_count  = 0;

			while (end != itr1)
			{
				if ('\\' == (*itr1))
				{
					++removal_count;

					if (end == ++itr1)
						break;
					else if ('\\' != (*itr1))
					{
						switch (*itr1)
						{
							case 'n' : (*itr1) = '\n'; break;
							case 'r' : (*itr1) = '\r'; break;
							case 't' : (*itr1) = '\t'; break;
							case '0' : parse_hex(itr1, end, (*itr1));
							removal_count += 3;
							break;
						}

						continue;
					}
				}

				if (itr1 != itr2)
				{
					(*itr2) = (*itr1);
				}

				++itr1;
				++itr2;
			}

			s.resize(s.size() - removal_count);
		}
		////////////////////////////////////////////////////////////////////////
		// SCAN TOKENS
		////////////////////////////////////////////////////////////////////////

		inline bool is_end(char_cptr itr)
		{
			return (s_end_ == itr);
		}

		inline bool is_comment_start(char_cptr itr)
		{
			const char_t c0 = *(itr + 0);
			const char_t c1 = *(itr + 1);

			if ('#' == c0)
				return true;
			else if (!is_end(itr + 1))
			{
				if (('/' == c0) && ('/' == c1)) return true;
				if (('/' == c0) && ('*' == c1)) return true;
			}
			return false;
		}

		inline void skip_whitespace()
		{
			while (!is_end(s_itr_) && is_whitespace(*s_itr_))
			{
				++s_itr_;
			}
		}

		inline void skip_comments()
		{
			// The following comment styles are supported:
			// 1. // .... \n
			// 2. #  .... \n
			// 3. /* .... */
			struct test
			{
				static inline bool comment_start(
						const char_t c0, const char_t c1, int& mode, int& incr)
				{
					mode = 0;
					if ('#' == c0)    { mode = 1; incr = 1; }
					else if ('/' == c0)
					{
						if ('/' == c1) { mode = 1; incr = 2; }
						else if ('*' == c1) { mode = 2; incr = 2; }
					}
					return (0 != mode);
				}

				static inline bool comment_end(
						const char_t c0, const char_t c1, int& mode)
				{
					if (
							((1 == mode) && ('\n' == c0)) ||
							((2 == mode) && ( '*' == c0) && ('/' == c1))
					)
					{
						mode = 0;
						return true;
					}
					else
						return false;
				}
			};

			int mode      = 0;
			int increment = 0;

			if (is_end(s_itr_))
				return;
			else if (!test::comment_start(*s_itr_, *(s_itr_ + 1), mode, increment))
				return;

			char_cptr cmt_start = s_itr_;

			s_itr_ += increment;

			while (!is_end(s_itr_))
			{
				if ((1 == mode) && test::comment_end(*s_itr_, 0, mode))
				{
					++s_itr_;
					return;
				}

				if ((2 == mode))
				{
					if (!is_end((s_itr_ + 1))
						&& test::comment_end(*s_itr_, *(s_itr_ + 1), mode))
					{
						s_itr_ += 2;
						return;
					}
				}

				++s_itr_;
			}

			if (2 == mode)
			{
				Token t;
				t.set_error(Token::T_ERROR, cmt_start, cmt_start + mode, base_itr_);
				tokens.push_back(t);
			}
		}


		inline void scan_token()
		{
			if (is_whitespace(*s_itr_))
			{
				skip_whitespace();
				return;
			}
			else if (is_comment_start(s_itr_))
			{
				skip_comments();
				return;
			}
			else if (is_operator_char(*s_itr_))
			{
				scan_operator();
				return;
			}
			else if (is_letter(*s_itr_))
			{
				scan_symbol();
				return;
			}
			else if (is_digit((*s_itr_)) || ('.' == (*s_itr_)))
			{
				scan_number();
				return;
			}
			else if ('$' == (*s_itr_))
			{
				scan_special_function();
				return;
			}
			else if (('"' == (*s_itr_)) || ('\'' == (*s_itr_)))
			{
				scan_string( *s_itr_);
				return;
			}
			else
			{
				Token t;
				t.set_error(Token::T_ERROR, s_itr_, s_itr_ + 2, base_itr_);
				tokens.push_back(t);
				++s_itr_;
			}
		}

		inline void scan_operator()
		{
			Token t;

			const char_t c0 = s_itr_[0];

			if (!is_end(s_itr_ + 1))
			{
				const char_t c1 = s_itr_[1];

				if (!is_end(s_itr_ + 2))
				{
					const char_t c2 = s_itr_[2];

					if (c2 == '=')
					{
						if (c0 == '=')
						{
							if (c1 == '=')
							{
								// ===
								t.set_operator(Token::T_SEQ, s_itr_, s_itr_ + 3, base_itr_);
								tokens.push_back(t);
								s_itr_ += 3;
								return;
							}
							else if ((c1 == '!') || (c1 == '/'))
							{
								// =!=  or  =/=
								t.set_operator(Token::T_NSEQ, s_itr_, s_itr_ + 3, base_itr_);
								tokens.push_back(t);
								s_itr_ += 3;
								return;
							}
						}
						else if ((c0 == '!') && (c1 == '='))
						{
							// !==
							t.set_operator(Token::T_NSEQ, s_itr_, s_itr_ + 3, base_itr_);
							tokens.push_back(t);
							s_itr_ += 3;
							return;
						}
					}
//					else if ((c0 == '<') && (c1 == '=') && (c2 == '>'))
//					{
//						t.set_operator(Token::T_SWAP, s_itr_, s_itr_ + 3, base_itr_);
//						tokens.push_back(t);
//						s_itr_ += 3;
//						return;
//					}
				}

				Token::token_type ttype = Token::T_NONE;

//					 if ((c0 == '<') && (c1 == '=')) ttype = Token::T_LTE;
//				else if ((c0 == '>') && (c1 == '=')) ttype = Token::T_GTE;
//				else if ((c0 == '<') && (c1 == '>')) ttype = Token::T_NEQ;
//				else if ((c0 == '!') && (c1 == '=')) ttype = Token::T_NEQ;
//				else if ((c0 == '=') && (c1 == '=')) ttype = Token::T_EQ;
//				else if ((c0 == ':') && (c1 == '=')) ttype = Token::T_ASSIGN;
//				else if ((c0 == '<') && (c1 == '<')) ttype = Token::T_LSHIFT;
//				else if ((c0 == '>') && (c1 == '>')) ttype = Token::T_RSHIFT;
//				else if ((c0 == '+') && (c1 == '=')) ttype = Token::T_ADD_ASSIGN;
//				else if ((c0 == '-') && (c1 == '=')) ttype = Token::T_SUB_ASSIGN;
//				else if ((c0 == '*') && (c1 == '=')) ttype = Token::T_MULT_ASSIGN;
//				else if ((c0 == '/') && (c1 == '=')) ttype = Token::T_DIV_ASSIGN;
//				else if ((c0 == '%') && (c1 == '=')) ttype = Token::T_MOD_ASSIGN;

				if (c1 == '=') {
					if (c0 == '<') ttype = Token::T_LTE;
					else if (c0 == '>') ttype = Token::T_GTE;
					else if (c0 == '=') ttype = Token::T_EQ;
					else if (c0 == '!') ttype = Token::T_NEQ;
					else if (c0 == ':') ttype = Token::T_ASSIGN;
					else if (c0 == '+') ttype = Token::T_ADD_ASSIGN;
					else if (c0 == '-') ttype = Token::T_SUB_ASSIGN;
					else if (c0 == '/') ttype = Token::T_DIV_ASSIGN;
					else if (c0 == '%') ttype = Token::T_MOD_ASSIGN;
					else if (c0 == '^') ttype = Token::T_POW_ASSIGN;
				}
				else if (c0 == '<') {
					if (c1 == '>') ttype = Token::T_NEQ;
					else if (c1 == '<') ttype = Token::T_LSHIFT;
				}
				else if (c0 == '*') {
					if (c1 == '=') ttype = Token::T_MULT_ASSIGN;
					else if (c1 == '*') ttype = Token::T_POW;
				}
				else if ((c0 == '&') && (c1 == '&')) ttype = Token::T_LAND;
				else if ((c0 == '|') && (c1 == '|')) ttype = Token::T_LOR;
				else if ((c0 == '>') && (c1 == '>')) ttype = Token::T_RSHIFT;

				if (Token::T_NONE != ttype)
				{
					t.set_operator(ttype, s_itr_, s_itr_ + 2, base_itr_);
					tokens.push_back(t);
					s_itr_ += 2;
					return;
				}
			}

			if (';' == c0)
			{
				t.set_operator(Token::T_SEMI, s_itr_, s_itr_ + 1, base_itr_);
			}
			else
			{
				t.set_operator(Token::token_type(c0), s_itr_, s_itr_ + 1, base_itr_);
			}

			tokens.push_back(t);
			++s_itr_;
		}

		inline void scan_symbol()
		{
			char_cptr initial_itr = s_itr_;

			while (!is_end(s_itr_))
			{
				if (!is_xletter_or_digit(*s_itr_))
				{
					if ('.' != (*s_itr_))
						break;
					/*
					Permit symbols that contain a 'dot'
					Allowed   : abc.xyz, a123.xyz, abc.123, abc_.xyz a123_.xyz abc._123
					Disallowed: .abc, abc.<white-space>, abc.<eof>, abc.<operator +,-,*,/...>
					 */
					if (
							(s_itr_ != initial_itr)             &&
							!is_end(s_itr_ + 1)                 &&
							!is_xletter_or_digit(*(s_itr_ + 1))
					)
						break;
				}

				++s_itr_;
			}

			Token t;
			t.set_symbol(initial_itr,s_itr_,base_itr_);
			tokens.push_back(t);
		}

		inline void scan_number()
		{
			/*
			  Attempt to match a valid numeric value in one of the following formats:
			  (01) 123456
			  (02) 123456.
			  (03) 123.456
			  (04) 123.456e3
			  (05) 123.456E3
			  (06) 123.456e+3
			  (07) 123.456E+3
			  (08) 123.456e-3
			  (09) 123.456E-3
			  (00) .1234
			  (11) .1234e3
			  (12) .1234E+3
			  (13) .1234e+3
			  (14) .1234E-3
			  (15) .1234e-3
			 */

			char_cptr initial_itr = s_itr_;
			bool dot_found                 = false;
			bool e_found                   = false;
			bool post_e_sign_found         = false;
			bool post_e_digit_found        = false;
			Token t;

			while (!is_end(s_itr_))
			{
				if ('.' == (*s_itr_))
				{
					if (dot_found)
					{
						t.set_error(Token::T_ERROR_NUMBER,
								initial_itr, s_itr_, base_itr_);

						tokens.push_back(t);

						return;
					}

					dot_found = true;
					++s_itr_;

					continue;
				}
				else if ('e' == std::tolower(*s_itr_))
				{
					const char_t& c = *(s_itr_ + 1);

					if (is_end(s_itr_ + 1))
					{
						t.set_error(Token::T_ERROR_NUMBER,
								initial_itr, s_itr_, base_itr_);

						tokens.push_back(t);

						return;
					}
					else if (
							('+' != c) &&
							('-' != c) &&
							!is_digit(c)
					)
					{
						t.set_error(Token::T_ERROR_NUMBER,
								initial_itr, s_itr_, base_itr_);

						tokens.push_back(t);

						return;
					}

					e_found = true;
					++s_itr_;

					continue;
				}
				else if (e_found && is_sign(*s_itr_) && !post_e_digit_found)
				{
					if (post_e_sign_found)
					{
						t.set_error(Token::T_ERROR_NUMBER,
								initial_itr, s_itr_, base_itr_);

						tokens.push_back(t);

						return;
					}

					post_e_sign_found = true;
					++s_itr_;

					continue;
				}
				else if (e_found && is_digit(*s_itr_))
				{
					post_e_digit_found = true;
					++s_itr_;

					continue;
				}
				else if (('.' != (*s_itr_)) && !is_digit(*s_itr_))
					break;
				else
					++s_itr_;
			}

			t.set_numeric(initial_itr, s_itr_, base_itr_);
			tokens.push_back(t);

			return;
		}

		inline void scan_special_function()
		{
			return;
		}

		inline void scan_string(char_t delimiter)
		{
			char_cptr initial_itr = s_itr_ + 1;
			Token t;

			if (std::distance(s_itr_,s_end_) < 2)
			{
				t.set_error(Token::T_ERROR_STRING, s_itr_, s_end_, base_itr_);
				tokens.push_back(t);
				return;
			}

			++s_itr_;

			bool escaped_found = false;
			bool escaped = false;

			while (!is_end(s_itr_))
			{
				if (!escaped && ('\\' == *s_itr_))
				{
					escaped_found = true;
					escaped = true;
					++s_itr_;

					continue;
				}
				else if (!escaped)
				{
					if (delimiter == *s_itr_)
						break;
				}
				else if (escaped)
				{
					if (!is_end(s_itr_) && ('0' == *(s_itr_)))
					{
						/*
					   Note: The following 'awkward' conditional is
							 due to various broken msvc compilers.
						 */
						const bool within_range = !is_end(s_itr_ + 1) &&
								!is_end(s_itr_ + 2) &&
								!is_end(s_itr_ + 3) ;

						const bool x_seperator  = ('x' == *(s_itr_ + 1)) ||
								('X' == *(s_itr_ + 1)) ;

						const bool both_digits  = is_hex_digit(*(s_itr_ + 2)) &&
								is_hex_digit(*(s_itr_ + 3)) ;

						if (!within_range || !x_seperator || !both_digits)
						{
							t.set_error(Token::T_ERROR_STRING,
									initial_itr, s_itr_, base_itr_);

							tokens.push_back(t);

							return;
						}
						else
							s_itr_ += 3;
					}

					escaped = false;
				}

				++s_itr_;
			}

			if (is_end(s_itr_))
			{
				t.set_error(Token::T_ERROR_STRING, initial_itr, s_itr_, base_itr_);
				tokens.push_back(t);

				return;
			}

			if (!escaped_found)
				t.set_string(delimiter, initial_itr, s_itr_, base_itr_);
			else
			{
				std::string parsed_string(initial_itr,s_itr_);

				cleanup_escapes(parsed_string);

				t.set_string(delimiter, parsed_string,
						static_cast<std::size_t>(std::distance(base_itr_,initial_itr)));
			}

			tokens.push_back(t);
			++s_itr_;

			return;
		}


		/**
		 * LEXER
		 */
		inline bool process()
		{
			if( rawExpression.empty() )
			{
				lastError = "Unexpected empty string expression !";

				return false;
			}
			else
			{
				base_itr_ = rawExpression.data();
				s_itr_    = rawExpression.data();
				s_end_    = rawExpression.data() + rawExpression.size();

				eof_token_.set_operator(Token::T_SEMI,s_end_,s_end_,base_itr_);
				tokens.clear();

				while (!is_end(s_itr_))
				{
					scan_token();

					if (!tokens.empty() && tokens.back().is_error())
					{
						return false;
					}
				}
			}

			return true;
		}


		/**
		 * PARSER UTILS
		 */
		inline bool empty() const
		{
			return tokens.empty();
		}

		inline std::size_t size() const
		{
			return tokens.size();
		}

		inline void begin()
		{
			token_itr_ = store_token_itr_ = tokens.begin();
		}

		inline void store()
		{
			store_token_itr_ = token_itr_;
		}

		inline void restore()
		{
			token_itr_ = store_token_itr_;
		}

		inline Token& next_token()
		{
			if (tokens.end() != token_itr_)
			{
				return *token_itr_++;
			}
			else
				return eof_token_;
		}

		inline Token& peek_next_token()
		{
			if (tokens.end() != token_itr_)
			{
				return *token_itr_;
			}
			else
				return eof_token_;
		}

		inline Token& operator[](const std::size_t& index)
		{
			if (index < tokens.size())
				return tokens[index];
			else
				return eof_token_;
		}

		inline Token operator[](const std::size_t& index) const
		{
			if (index < tokens.size())
				return tokens[index];
			else
				return eof_token_;
		}

		inline bool finished() const
		{
			return (tokens.end() == token_itr_);
		}



	};


protected:
	/**
	 * ATTRIBUTES
	 */
	const Machine & machineCtx;
	BF bfExpression;

	Lexer lexer;

	Token current_token_;
	Token store_current_token_;

	std::ostringstream OUT_ERR;

	/**
	 * CONTRUCTORS
	 */
	ExpressionParser(const Machine & machine, const std::string & rawExpression)
	: machineCtx( machine ),
	
	bfExpression( ),
	
	lexer( rawExpression ),

	current_token_( ),
	store_current_token_( ),

	OUT_ERR( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	~ExpressionParser()
	{
		//!! NOTHING
	}


	/**
	 * GETTERS
	 */
	inline const BF & result() const
	{
		return bfExpression;
	}


	/**
	 * GETTERS - SETTERS
	 * OUT_ERR
	 */
	inline std::ostringstream & err()
	{
		return OUT_ERR;
	}

	inline std::string error() const
	{
		return OUT_ERR.str();
	}

	inline bool hasError() const
	{
		return (! OUT_ERR.str().empty());
	}

	inline void setError(const std::string & errorMsg)
	{
		if( OUT_ERR.str().empty() )
		{
			OUT_ERR << errorMsg << std::endl 
					<< "\t\tFound " << current_token().str() << std::endl ;
		}
	}


	/**
	 * LEXER UTILS
	 */
	inline void store_token()
	{
		lexer.store();
		store_current_token_ = current_token_;
	}

	inline void restore_token()
	{
		lexer.restore();
		current_token_ = store_current_token_;
	}

	inline void next_token()
	{
		current_token_ = lexer.next_token();
	}


	inline const Token& current_token() const
	{
		return current_token_;
	}


	inline void advance_token(bool reqAdvance = true)
	{
		if (reqAdvance)
		{
			next_token();
		}
	}


	inline bool next_token_is(const Token::token_type& ttype)
	{
		if (current_token().type == ttype)
		{
			next_token();
			
			return true;
		}


		return false;
	}

	inline bool token_is(const Token::token_type& ttype)
	{
		return (current_token().type == ttype);
	}


	inline bool next_token_symbol_is(const std::string& value, bool reqAdvance = true)
	{
		if ((current_token().type == Token::T_SYMBOL)
			&& lexer.imatch(value,current_token().value))
		{
			next_token();

			return true;
		}

		return false;
	}

	inline bool token_symbol_is(const std::string& value, bool reqAdvance = true)
	{
		return ((current_token().type == Token::T_SYMBOL)
				&& lexer.imatch(value,current_token().value));
	}


	/**
	 * PARSER EXPRESSION RULES
	 */
	BF parseExpression();

	BF assignExpression();

	BF conditionalExpression();

	BF conditionalOrExpression();

	BF conditionalAndExpression();

	BF bitwiseOrExpression();

	BF bitwiseXorExpression();

	BF bitwiseAndExpression();


	BF equalityExpression();

	Operator * equalOp();


	BF relationalExpression();

	Operator * relationalOp();


	BF shiftExpression();

	Operator * shiftOp();


	BF additiveExpression();

	Operator * additiveOp();


	BF multiplicativeExpression();

	Operator * multiplicativeOp();


	BF powerExpression();


	BF unaryExpression();

	BF primaryExpression();

	BF literalExpression();


	/**
	 * COMPILER
	 */
	bool compile();


public:
	////////////////////////////////////////////////////////////////////////////
	// Parser
	////////////////////////////////////////////////////////////////////////////

	static BF parse(const Machine & machineCtx, const std::string & rawExpression);

	static const BF & parseVariable(
			const Machine & machineCtx, const std::string & varID);

};

}

#endif /* EXPRESSIONPARSER_H_ */

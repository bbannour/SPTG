/*
 * Py_Const.h
 *
 *  Created on: 16 avr. 2019
 *      Author: xavier
 */

#ifndef FML_INFRASTRUCTURE_FACADES_PY_CONST_H_
#define FML_INFRASTRUCTURE_FACADES_PY_CONST_H_

#include "fml/expression/ExpressionConstructor.h"
#include "fml/infrastructure/Variable.h"
#include "fml/infrastructure/Machine.h"
#include "fml/type/TypeManager.h"

namespace sep {

class Py_Const : public Variable {

public :
	Py_Const(Machine* m,const std::string & varName, const std::string & typeName):
		Variable(m, Modifier(Modifier::NATURE_VARIABLE_KIND,Modifier::FEATURE_CONST_KIND), TypeManager::getPrimitiveType(typeName), varName)
	{}

	Py_Const(const std::string & varName, const std::string & typeName):
		Variable(nullptr, Modifier(Modifier::NATURE_VARIABLE_KIND,Modifier::FEATURE_CONST_KIND), TypeManager::getPrimitiveType(typeName), varName)
	{}

	inline void setVal(int val) {setValue(ExpressionConstructor::newInteger(val));}
	inline void setVal(bool val) {setValue(ExpressionConstructor::newBoolean(val));}
	inline void setVal(float val) {setValue(ExpressionConstructor::newFloat(val));}
	inline void setVal(std::string val) {setValue(ExpressionConstructor::newString(val));}

   inline const std::string getName() const {return NamedElement::getNameID();}

   inline friend std::ostream& operator<<(std::ostream& o, const Py_Const& c) {
	   OutStream out(o);
	   c.strHeader(out);
	   return o;
	}
};

} // end of namespace
#endif /* FML_INFRASTRUCTURE_FACADES_PY_CONST_H_ */

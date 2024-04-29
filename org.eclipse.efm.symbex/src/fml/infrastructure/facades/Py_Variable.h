/*
 * Py_Variable.h
 *
 *  Created on: 4 avr. 2019
 *      Author: xavier
 */

#ifndef FML_INFRASTRUCTURE_FACADES_PY_VARIABLE_H_
#define FML_INFRASTRUCTURE_FACADES_PY_VARIABLE_H_

#include <string>

#include "fml/expression/ExpressionConstructor.h"
#include "fml/infrastructure/Variable.h"
#include "fml/infrastructure/Machine.h"
#include "fml/type/TypeManager.h"
#include "printer/OutStream.h"

namespace sep {


class Py_Variable : public Variable {

public :
	Py_Variable(Machine* m,std::string varName, std::string typeName):
	  Variable(m, Modifier::NATURE_VARIABLE_KIND, TypeManager::getPrimitiveType(typeName), varName)
	  {}

	Py_Variable(std::string varName, std::string typeName):
	  Variable(nullptr, Modifier::NATURE_VARIABLE_KIND, TypeManager::getPrimitiveType(typeName), varName)
	  {}

   inline void setInitVal(int val) {setValue(ExpressionConstructor::newInteger(val));}
   inline void setInitVal(bool val) {setValue(ExpressionConstructor::newBoolean(val));}
   inline void setInitVal(float val) {setValue(ExpressionConstructor::newFloat(val));}
   inline void setInitVal(std::string val) {setValue(ExpressionConstructor::newString(val));}

   //virtual void strHeader(OutStream & out) const override

   inline const std::string getName() const {return NamedElement::getNameID();}

   inline const std::string operator+(const Py_Variable& other) const {return getName() + " + " + other.getName();}
   inline const std::string operator-(const Py_Variable& other) const {return getName() + " - " + other.getName();}
   inline const std::string operator*(const Py_Variable& other) const {return getName() + " * " + other.getName();}
   inline const std::string operator/(const Py_Variable& other) const {return getName() + " / " + other.getName();}

   inline const std::string operator+(const std::string s) const {return getName() + " + " + s;}
   inline const std::string operator-(const std::string s) const {return getName() + " - " + s;}
   inline const std::string operator*(const std::string s) const {return getName() + " * " + s;}
   inline const std::string operator/(const std::string s) const {return getName() + " / " + s;}

   inline friend std::string operator+(const std::string s, const Py_Variable& v) {return s + " + " +  v.getName();}
   inline friend std::string operator-(const std::string s, const Py_Variable& v) {return s + " - " +  v.getName();}
   inline friend std::string operator*(const std::string s, const Py_Variable& v) {return s + " * " +  v.getName();}
   inline friend std::string operator/(const std::string s, const Py_Variable& v) {return s + " / " +  v.getName();}

   inline const std::string operator+(const int i) const {return getName() + " + " + std::to_string(i);}
   inline const std::string operator-(const int i) const {return getName() + " - " + std::to_string(i);}
   inline const std::string operator*(const int i) const {return getName() + " * " + std::to_string(i);}
   inline const std::string operator/(const int i) const {return getName() + " / " + std::to_string(i);}

   inline friend std::string operator+(const int i, const Py_Variable& v) {return std::to_string(i) + " + " +  v.getName();}
   inline friend std::string operator-(const int i, const Py_Variable& v) {return std::to_string(i) + " - " +  v.getName();}
   inline friend std::string operator*(const int i, const Py_Variable& v) {return std::to_string(i) + " * " +  v.getName();}
   inline friend std::string operator/(const int i, const Py_Variable& v) {return std::to_string(i) + " / " +  v.getName();}



   inline friend std::ostream& operator<<(std::ostream& o, const Py_Variable& v) {
	   OutStream out(o);
	   v.strHeader(out);
	   return o;
	}
};

}//endof namespace

#endif /* FML_INFRASTRUCTURE_FACADES_PY_VARIABLE_H_ */

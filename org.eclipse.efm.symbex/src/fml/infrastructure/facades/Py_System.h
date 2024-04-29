#ifndef FML_INFRASTRUCTURE_FACADES_PY_SYSTEM_H_
#define FML_INFRASTRUCTURE_FACADES_PY_SYSTEM_H_

#include <boost/python/suite/indexing/vector_indexing_suite.hpp>

#include "fml/infrastructure/System.h"
#include "fml/infrastructure/facades/Py_StateMachine.h"
#include "fml/common/SpecifierElement.h"

#include <string>

namespace sep{

class Py_Port;

class Py_System : public System{
    
public:
    
    Py_System (std::string name, std::string timed): System(name) {
    	if (timed == "discrete") {
    		getwSpecifier().addFeatureKind(Specifier::FEATURE_KIND::FEATURE_DISCRETE_TIMED_KIND);
    	} else if (timed == "continuous") {
    		getwSpecifier().addFeatureKind(Specifier::FEATURE_KIND::FEATURE_CONTINUOUS_TIMED_KIND);
    		//setSpecifier(Specifier(getSpecifier(), Specifier::FEATURE_CONTINUOUS_TIMED_KIND));
    	} else {
    	}
    }
    

    Py_StateMachine& addStateMachine(std::string);

    bool connect(boost::python::list, std::string);

	inline const std::string getName() const {return NamedElement::getNameID();}

	inline std::vector<std::string> getMachineNames() const {return Machine::getMachineNames();}


	friend std::ostream& operator<< (std::ostream& o, const Py_System& s) {
		return o << s.toString();
	}

};

} //end of namespace

#endif /* FML_INFRASTRUCTURE_FACADES_PY_SYSTEM_H_ */

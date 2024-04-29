#include <string>
#include <vector>
#include "fml/common/ModifierElement.h"
#include "fml/infrastructure/facades/Py_Port.h"
#include "fml/infrastructure/facades/Py_System.h"
#include "fml/infrastructure/ComProtocol.h"
#include "fml/infrastructure/Connector.h"
#include "fml/infrastructure/InteractionPart.h"

using namespace sep;


Py_StateMachine& Py_System::addStateMachine(std::string name) {
	    Py_StateMachine* sm = new Py_StateMachine(this, name);
		Machine::saveOwnedElement(sm);
		return *sm;
}



bool Py_System::connect(boost::python::list ports, std::string protocolName) {
	bool ok(true);

	InteractionPart * intPart = getUniqInteraction();
	Connector & conn = intPart->appendConnector();
	conn.setProtocol(ComProtocol::to_protocol(protocolName));

	conn.setCast(ComProtocol::to_cast(ComProtocol::to_protocol(protocolName)));

	ComRoute & inputRoute = conn.appendComRoute(sep::Modifier::PROPERTY_INPUT_DIRECTION);
	ComRoute & outputRoute = conn.appendComRoute(sep::Modifier::PROPERTY_OUTPUT_DIRECTION);

	Py_Port* p;
	while(boost::python::len(ports) > 0) {
		p = boost::python::extract<Py_Port*>(ports.pop(0));
		if (p->getModifier().isDirectionInput()) {
			inputRoute.appendComPoint(p);
		}
		else if (p->getModifier().isDirectionOutput()){
			outputRoute.appendComPoint(p);
		}
		else { /* Inout port non managed */
			ok = false; // throw std::exception(); //FIXME : define specific exception
		}
	}

	return ok;

}

//bool Py_System::connect(Py_Port& p1, Py_Port& p2, const std::string& protocolName) {
//	bool ok(true);
//
//	InteractionPart* intPart = getUniqInteraction();
//	Connector& conn = intPart->appendConnector();
//
//	ComRoute & inputRoute = conn.appendComRoute(sep::Modifier::PROPERTY_INPUT_DIRECTION);
//	ComRoute & outputRoute = conn.appendComRoute(sep::Modifier::PROPERTY_OUTPUT_DIRECTION);
//
//	//conn.setBuffer(this, "fifo", 42);
//    conn.setProtocol(ComProtocol::to_protocol(protocolName));
//
//		if (p1.getModifier().isDirectionInput()) {
//			inputRoute.appendComPoint(&p1);
//		}
//		else if (p1.getModifier().isDirectionOutput()){
//			outputRoute.appendComPoint(&p1);
//		}
//		else { /* Inout port non managed */
//			ok = false; // throw std::exception(); //FIXME : define specific exception
//		}
//
//		if (p2.getModifier().isDirectionInput()) {
//			inputRoute.appendComPoint(&p2);
//		}
//		else if (p2.getModifier().isDirectionOutput()){
//			outputRoute.appendComPoint(&p2);
//		}
//		else { /* Inout port non managed */
//			ok = false; // throw std::exception(); //FIXME : define specific exception
//		}
//
//	return ok;
//}

/*
 * CommunicationGraphSerializer.h
 *
 *  Created on: 2 mai 2019
 *      Author: xavier
 */

#ifndef FAM_SERIALIZER_COMMUNICATIONGRAPHSERIALIZER_H_
#define FAM_SERIALIZER_COMMUNICATIONGRAPHSERIALIZER_H_

#include <string>

namespace sep {

class OutStream;
class System;
class Connector;
class Machine;

class CommunicationGraphSerializer {


public :
	const std::string FILE_HEADER="@startuml\n";
	const std::string FILE_FOOTER="@enduml";

	CommunicationGraphSerializer(){};

	std::string format(const System & aSystem);
	std::string formatInteractions (const Machine& aMachine);
	std::string formatConnector(const Connector& aConnector );
	std::string formatComposition(const Machine& aMachine);

private :
	bool hasCommunicatingSubMachineaMachine(const Machine& aMachine);

};

} /* namespace sep */

#endif /* FAM_SERIALIZER_COMMUNICATIONGRAPHSERIALIZER_H_ */

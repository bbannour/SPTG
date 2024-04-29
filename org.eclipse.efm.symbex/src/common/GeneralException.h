#ifndef GENERALEXCEPTION_H_
#define GENERALEXCEPTION_H_

#include <exception>
#include <string>


namespace sep
{

class DiversityError: public std::exception {
	/* This class is an example to be expanded and generalized */
private:
	std::string message;
public:
	DiversityError(const std::string& msg) noexcept: message(msg) {}
    virtual ~DiversityError() noexcept {}

	inline virtual const char* what() const noexcept override {return message.c_str();}
};
}

#endif /* GENERALEXCEPTION_H_ */

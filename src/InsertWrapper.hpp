/*
 * Copyright 2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef INSERTWRAPPER_HPP_
#define INSERTWRAPPER_HPP_

#include <vector>
#include <string>
#include <sstream>
#include <map>
#include "flatzincsupport/FZDatastructs.hpp"

namespace FZ{

enum CONSTRAINT_TYPE {
	bool2int,

	booland, boolclause, booleq, booleqr, boolle, booller, boollt, boolltr, boolnot, boolor, boolxor,

	intabs, intdiv, inteq, inteqr, intle, intler, intlt, intltr, intmax, intmin, intmod, intne, intner, intplus, inttimes,
	intlineq, intlineqr, intlinle, intlinler, intlinne, intlinner,

	arraybooland, arrayboolor
};

enum ARG_TYPE { ARG_BOOL, ARG_INT, ARG_SET, ARG_ARRAY_OF_SET, ARG_ARRAY_OF_INT, ARG_ARRAY_OF_BOOL };

class InsertWrapper {
private:
	std::stringstream vars, theory;
	std::map<int, std::stringstream*> definitions;
	std::map<std::string, CONSTRAINT_TYPE> name2type;
	void addFunc(const std::string& func, const std::vector<Expression*>& origargs);
	void parseArgs(const std::vector<Expression*>& origargs, std::vector<int>& args, const std::vector<ARG_TYPE>& expectedtypes);

	void writeRule(int head, const std::vector<int>& body, bool conj, int definitionID);
	void writeEquiv(int head, const std::vector<int>& body, bool conj);

	int parseBool(const Expression& expr);
	int parseInt(const Expression& expr);
	int parseParInt(const Expression& expr);
	std::vector<int> parseArray(VAR_TYPE type, Expression& expr);
	std::vector<int> parseParIntArray(Expression& expr);

	template<class T>
	void addBinT(const T& boolvar, int intvar, const std::string& op, int intvar2);
	template<class T>
	void addBinI(const T& boolvar, int intvar, const std::string& op, int parint);

	void addLinear(const std::vector<Expression*>& arguments, const std::string& op, bool reif);

	void addOptim(Expression& expr, bool maxim);

public:
	InsertWrapper();
	virtual ~InsertWrapper();

	void start	();
	void finish	();

	void add	(Var* var);
	void add	(Constraint* var);
	void add	(Search* var);
};
}

#endif /* INSERTWRAPPER_HPP_ */

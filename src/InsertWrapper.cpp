/*
 * Copyright 2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "flatzincsupport/InsertWrapper.hpp"

#include <assert.h>
#include <string>
#include <iostream>
#include <algorithm>

#include "flatzincsupport/FZDatastructs.hpp"
#include "flatzincsupport/fzexception.hpp"

using namespace std;
using namespace FZ;

//TODO minisatid generates unsat on kakuro while it is sat (might be translation, might be gecode, but probably translation)

// Default ID is hardcoded
int defaultdefID = 0;

InsertWrapper::InsertWrapper(){
	name2type["bool2int"] = bool2int;
	name2type["bool_and"] = booland;
	name2type["bool_clause"] = boolclause;
	name2type["bool_eq"] = booleq;
	name2type["bool_eq_reif"] = booleqr;
	name2type["bool_le"] = boolle;
	name2type["bool_le_reif"] = booller;
	name2type["bool_lt"] = boollt;
	name2type["bool_lt_reif"] = boolltr;
	name2type["bool_not"] = boolnot;
	name2type["bool_or"] = boolor;
	name2type["bool_xor"] = boolxor;

	name2type["int_abs"] = intabs;
	name2type["int_div"] = intdiv;
	name2type["int_eq"] = inteq;
	name2type["int_eq_reif"] = inteqr;
	name2type["int_le"] = intle;
	name2type["int_le_reif"] = intler;
	name2type["int_lt"] = intlt;
	name2type["int_lt_reif"] = intltr;
	name2type["int_max"] = intmax;
	name2type["int_min"] = intmin;
	name2type["int_mod"] = intmod;
	name2type["int_ne"] = intne;
	name2type["int_ne_reif"] = intner;
	name2type["int_plus"] = intplus;
	name2type["int_times"] = inttimes;
	name2type["int_lin_eq"] = intlineq;
	name2type["int_lin_eq_reif"] = intlineqr;
	name2type["int_lin_le"] = intlinle;
	name2type["int_lin_le_reif"] = intlinler;
	name2type["int_lin_ne"] = intlinne;
	name2type["int_lin_ne_reif"] = intlinner;

	name2type["array_bool_and"] = arraybooland;
	name2type["array_bool_or"] = arrayboolor;
}

InsertWrapper::~InsertWrapper() {
	for(map<int, stringstream*>::iterator i=definitions.begin(); i!=definitions.end(); ++i){
		delete((*i).second);
	}
}

void InsertWrapper::start(){
	cout <<"c Automated transformation from a flatzinc model into ECNF.\n";
	cout <<"p ecnf\n";
}

void InsertWrapper::finish(){
	cout <<vars.str();
	cout <<theory.str();
}

void InsertWrapper::add(Var* var){
	var->add(vars, theory);
}

int InsertWrapper::parseBool(const Expression& expr){
	if(expr.type==EXPR_BOOL){
		return (expr.boollit?getTrue(vars):getFalse(vars));
	}else if(expr.type==EXPR_ARRAYACCESS){
		return getVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index, true);
	}else if(expr.type==EXPR_IDENT){
		return getVar(*expr.ident->name, true);
	}else{ throw fzexception("Unexpected type.\n"); }
}

int InsertWrapper::parseInt(const Expression& expr){
	if(expr.type==EXPR_INT){
		int varnb = createOneShotVar();
		vars <<"INTVAR " <<varnb <<" " <<expr.intlit <<" " <<expr.intlit <<" 0\n";
		return varnb;
	}else if(expr.type==EXPR_ARRAYACCESS){
		return getVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index, false);
	}else if(expr.type==EXPR_IDENT){
		return getVar(*expr.ident->name, false);
	}else{ throw fzexception("Unexpected type.\n"); }
}

int InsertWrapper::parseParInt(const Expression& expr){
	if(expr.type==EXPR_INT){
		return expr.intlit;
	}else if(expr.type==EXPR_ARRAYACCESS){
		return getVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index, false);
	}else if(expr.type==EXPR_IDENT){
		return getVar(*expr.ident->name, false);
	}else{ throw fzexception("Unexpected type.\n"); }
}

vector<int> InsertWrapper::parseArray(VAR_TYPE type, Expression& expr){
	if(expr.type!=EXPR_ARRAY){ throw fzexception("Unexpected type.\n"); }

	vector<int> elems;
	for(vector<Expression*>::const_iterator i=expr.arraylit->exprs->begin(); i<expr.arraylit->exprs->end(); ++i){
		if(type==VAR_BOOL){
			elems.push_back(parseBool(**i));
		}else{
			elems.push_back(parseInt(**i));
		}
	}
	return elems;
}

vector<int> InsertWrapper::parseParIntArray(Expression& expr){
	if(expr.type!=EXPR_ARRAY){ throw fzexception("Unexpected type.\n"); }

	vector<int> elems;
	for(vector<Expression*>::const_iterator i=expr.arraylit->exprs->begin(); i<expr.arraylit->exprs->end(); ++i){
		elems.push_back(parseParInt(**i));
	}
	return elems;
}

void InsertWrapper::parseArgs(const vector<Expression*>& origargs, vector<int>& args, const vector<ARG_TYPE>& expectedtypes){
	if(origargs.size()!=expectedtypes.size()){
		throw fzexception("Incorrect number of arguments.\n");
	}
	unsigned int itype=0;
	for(vector<Expression*>::const_reverse_iterator i=origargs.rbegin(); i<origargs.rend(); ++i, ++itype){
		ARG_TYPE expectedtype = expectedtypes[itype];
		Expression& expr = **i;
		switch(expectedtype){
		case ARG_BOOL: args.push_back(parseBool(expr)); break;
		case ARG_INT: args.push_back(parseInt(expr)); break;
		default:
			throw fzexception("Unexpected type.\n");
		}
	}
}

bool hasDefinitionAnnotation(const vector<Expression*>& args, int& definitionid){
	bool defined = false;
	for(vector<Expression*>::const_iterator i=args.begin(); i<args.end(); ++i){
		if((*i)->type==EXPR_IDENT && (*i)->ident->name->compare("inductivelydefined")==0){
			if((*i)->ident->arguments!=NULL){
				if((*i)->ident->arguments->size()==1 && (*(*i)->ident->arguments->begin())->type==EXPR_INT){
					definitionid = (*(*i)->ident->arguments->begin())->intlit;
				}else{ throw fzexception("Incorrect number of annotation arguments");}
			}else{
				definitionid = defaultdefID;
			}
			defined = true;
		}
	}
	return defined;
}

void InsertWrapper::writeRule(int head, const vector<int>& rhs, bool conj, int definitionID){
	theory <<(conj?"C":"D") <<" | " <<definitionID <<" " <<head <<" ";
	for(vector<int>::const_iterator i=rhs.begin(); i<rhs.end(); ++i){
		theory <<*i <<" ";
	}
	theory <<" 0\n";
}
void InsertWrapper::writeEquiv(int head, const vector<int>& rhs, bool conj){
	theory <<"EQUIV " <<(conj?"D":"C") <<" " <<head <<" ";
	for(vector<int>::const_iterator i=rhs.begin(); i<rhs.end(); ++i){
		theory <<*i <<" ";
	}
	theory <<" 0\n";
}

template<class T>
void InsertWrapper::addBinI(const T& boolvar, int intvar, const string& op, int intvar2){
	theory <<"BINTRI" <<" " <<boolvar <<" " <<intvar <<" " <<op <<" "<<intvar2 <<" 0\n";
}

template<class T>
void InsertWrapper::addBinT(const T& boolvar, int intvar, const string& op, int intvar2){
	theory <<"BINTRT" <<" " <<boolvar <<" " <<intvar <<" " <<op <<" "<<intvar2 <<" 0\n";
}

template<class T>
T getRevArg(const vector<T>& list, int index){
	return list[list.size()-index-1];
}

void InsertWrapper::addLinear(const vector<Expression*>& arguments, const string& op, bool reif){
	if(arguments.size()!=(reif?4:3)){ throw fzexception("Incorrect number of arguments.\n"); }
	vector<int> weights = parseParIntArray(*getRevArg(arguments, 0));
	vector<int> variables = parseArray(VAR_INT, *getRevArg(arguments, 1));
	int intvar = parseParInt(*getRevArg(arguments, 2));
	theory <<"SUMSTSIRI ";
	if(reif){
		theory <<parseBool(*getRevArg(arguments, 3)) <<" ";
	}else{
		theory <<getTrue(vars) <<" ";
	}
	for(unsigned int i=0; i<variables.size(); ++i){
		theory <<variables[i] <<" ";
	}
	theory <<" | ";
	for(unsigned int i=0; i<weights.size(); ++i){
		theory <<weights[i] <<" ";
	}
	theory <<" " <<op <<" " <<intvar <<" 0\n";
}

//VERY IMPORTANT: ALL PARSED VECTORS ARE REVERSED ORDER (TO HAVE FASTER PARSING)!!!!
void InsertWrapper::add(Constraint* var){
	const vector<Expression*>& arguments = *var->id->arguments;
	vector<int> args;
	vector<ARG_TYPE> types;

	map<string, CONSTRAINT_TYPE>::const_iterator it = name2type.find(*var->id->name);

	if(it==name2type.end()){
		stringstream ss;
		ss <<"Constraint " <<*var->id->name <<" is not a supported constraint.\n";
		throw fzexception(ss.str());
	}

	switch ((*it).second) {
	case bool2int:{
		types.push_back(ARG_BOOL); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		addBinI(args[0], args[1], "=", 1);
		break;}
	case booland:{
		types.push_back(ARG_BOOL); types.push_back(ARG_BOOL); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		vector<int> rhs;
		rhs.push_back(args[0]);
		rhs.push_back(args[1]);
		writeEquiv(args[2], rhs, true);
		break;}
	case boolclause:{
		if(arguments.size()!=2){ throw fzexception("Incorrect number of arguments.\n"); }
		vector<int> arg1 = parseArray(VAR_BOOL, *getRevArg(arguments, 0));
		vector<int> arg2 = parseArray(VAR_BOOL, *getRevArg(arguments, 1));
		for(vector<int>::const_iterator i=arg1.begin(); i<arg1.end(); ++i){
			theory <<*i <<" ";
		}
		for(vector<int>::const_iterator i=arg2.begin(); i<arg2.end(); ++i){
			theory <<"-" <<*i <<" ";
		}
		theory <<" 0\n";
		break;}
	case arraybooland:{
		if(arguments.size()!=2){ throw fzexception("Incorrect number of arguments.\n"); }
		vector<int> arg1 = parseArray(VAR_BOOL, *getRevArg(arguments, 0));
		int arg2 = parseBool(*getRevArg(arguments, 1));
		writeEquiv(arg2, arg1, true);
		break;}
	case arrayboolor:{
		if(arguments.size()!=2){ throw fzexception("Incorrect number of arguments.\n"); }
		vector<int> arg1 = parseArray(VAR_BOOL, *getRevArg(arguments, 0));
		int arg2 = parseBool(*getRevArg(arguments, 1));
		writeEquiv(arg2, arg1, false);
		break;}
	case booleq:{
		types.push_back(ARG_BOOL); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		vector<int> v; v.push_back(args[1]);
		writeEquiv(args[0], v, true);
		break;}
	case booleqr:{
		types.push_back(ARG_BOOL); types.push_back(ARG_BOOL); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		vector<int> bothttrue; bothttrue.push_back(args[0]); bothttrue.push_back(args[1]);
		vector<int> bothfalse; bothfalse.push_back(-args[0]); bothfalse.push_back(-args[1]);
		int bothtruereif = createOneShotVar();
		int bothfalsereif = createOneShotVar();
		writeEquiv(bothtruereif, bothttrue, true);
		writeEquiv(bothfalsereif, bothfalse, true);
		vector<int> oneofboth; oneofboth.push_back(bothfalsereif); oneofboth.push_back(bothtruereif);
		writeEquiv(args[2], oneofboth, false);
		break;}
	case boolle:{
		types.push_back(ARG_BOOL); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		theory <<"-" <<args[0] <<" " <<args[1] <<" 0\n";
		break;}
	case booller:{
		types.push_back(ARG_BOOL); types.push_back(ARG_BOOL); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		vector<int> rhs; rhs.push_back(-args[0]); rhs.push_back(args[1]);
		writeEquiv(args[2], rhs, false);
		break;}
	case boollt:{
		types.push_back(ARG_BOOL); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		theory <<"-" <<args[0] <<" 0\n";
		theory <<args[1] <<" 0\n";
		break;}
	case boolltr:{
		types.push_back(ARG_BOOL); types.push_back(ARG_BOOL); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		vector<int> rhs; rhs.push_back(-args[0]); rhs.push_back(args[1]);
		writeEquiv(args[2], rhs, true);
		break;}
	case boolnot:{
		types.push_back(ARG_BOOL); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		vector<int> rhs; rhs.push_back(-args[0]);
		writeEquiv(args[1], rhs, true);
		break;}
	case boolor:{
		types.push_back(ARG_BOOL); types.push_back(ARG_BOOL); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		vector<int> rhs; rhs.push_back(args[0]); rhs.push_back(args[1]);
		writeEquiv(args[2], rhs, false);
		break;}
	case boolxor:{
		types.push_back(ARG_BOOL); types.push_back(ARG_BOOL); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		vector<int> firstfalse; firstfalse.push_back(-args[0]); firstfalse.push_back(args[1]);
		vector<int> secondfalse; secondfalse.push_back(args[0]); secondfalse.push_back(-args[1]);
		int firstfalsereif = createOneShotVar();
		int secondfalsereif = createOneShotVar();
		writeEquiv(firstfalsereif, firstfalse, true);
		writeEquiv(secondfalsereif, secondfalse, true);
		vector<int> oneofboth; oneofboth.push_back(firstfalsereif); oneofboth.push_back(secondfalsereif);
		writeEquiv(args[2], oneofboth, false);
		break;}
	case inteq: {
		types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		addBinT(getTrue(vars), args[0], "=", args[1]);
		break;}
	case inteqr: {
		types.push_back(ARG_INT); types.push_back(ARG_INT); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		addBinT(args[2], args[0], "=", args[1]);
		break;}
	case intle: {
		types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		addBinT(getTrue(vars), args[0], "=<", args[1]);
		break;}
	case intler: {
		types.push_back(ARG_INT); types.push_back(ARG_INT); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		addBinT(args[2], args[0], "=<", args[1]);
		break;}
	case intlt: {
		types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		addBinT(getTrue(vars), args[0], "<", args[1]);
		break;}
	case intltr: {
		types.push_back(ARG_INT); types.push_back(ARG_INT); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		addBinT(args[2], args[0], "<", args[1]);
		break;}
	case intne: {
		types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		addBinT(getTrue(vars), args[0], "~=", args[1]);
		break;}
	case intner: {
		types.push_back(ARG_INT); types.push_back(ARG_INT); types.push_back(ARG_BOOL);
		parseArgs(arguments, args, types);
		addBinT(args[2], args[0], "~=", args[1]);
		break;}
	//TODO binary/ternary functions
/*	case intabs: {
		types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		//theory <<tab() <<"abs(" <<args[0] <<")= " <<args[1] <<endst();
		break;}
	case intdiv: {
		types.push_back(ARG_INT); types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		//theory <<tab() <<args[0] <<" / " <<args[1] <<" = " <<args[2] <<endst();
		break;}
	case intmax: {
		types.push_back(ARG_INT); types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		//theory <<tab() <<"max(" <<args[0] <<", " <<args[1] <<")= " <<args[2]<<endst();
		break;}
	case intmin: {
		types.push_back(ARG_INT); types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		//theory <<tab() <<"min(" <<args[0] <<", " <<args[1] <<")= " <<args[2] <<endst();
		break;}
	case intmod: {
		types.push_back(ARG_INT); types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		//theory <<tab() <<args[0] <<" mod " <<args[1] <<" = " <<args[2] <<endst();
		break;}
	case intplus: {
		types.push_back(ARG_INT); types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		//theory <<tab() <<args[0] <<" + " <<args[1] <<" = " <<args[2] <<endst();
		break;}
	case inttimes: {
		types.push_back(ARG_INT); types.push_back(ARG_INT); types.push_back(ARG_INT);
		parseArgs(arguments, args, types);
		//theory <<tab() <<args[0] <<" * " <<args[1] <<" = " <<args[2] <<endst();
		break;}*/
	case intlineq: {
		addLinear(arguments, "=", false);
		break;}
	case intlineqr: {
		addLinear(arguments, "=", true);
		break;}
	case intlinle: {
		addLinear(arguments, "=<", false);
		break;}
	case intlinler: {
		addLinear(arguments, "=<", true);
		break;}
	case intlinne: {
		addLinear(arguments, "~=", false);
		break;}
	case intlinner: {
		addLinear(arguments, "~=", true);
		break;}
	default:
		stringstream ss;
		ss <<"Constraint " <<*var->id->name <<" is not a supported constraint.\n";
		throw fzexception(ss.str());
	}
}

void InsertWrapper::addOptim(Expression& expr, bool maxim){
	MIntVar* intvar;
	if(expr.type==EXPR_ARRAYACCESS){
		intvar = getIntVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index);
	}else if(expr.type==EXPR_IDENT){
		intvar = getIntVar(*expr.ident->name);
	}else{ throw fzexception("Unexpected type.\n"); }

	vector<int> minorderedlist;
	if(intvar->range){
		for(int i=intvar->begin; i<=intvar->end; ++i){
			int tempvar = createOneShotVar();
			theory <<"BINTRI " <<tempvar <<" " <<intvar->var <<" " <<i <<" 0\n";
			minorderedlist.push_back(tempvar);
		}
	}else{
		sort(intvar->values.begin(), intvar->values.end());
		for(vector<int>::const_iterator i=intvar->values.begin(); i<=intvar->values.end(); ++i){
			int tempvar = createOneShotVar();
			theory <<"BINTRI " <<tempvar <<" " <<intvar->var <<" " <<*i <<" 0\n";
			minorderedlist.push_back(tempvar);
		}
	}


	theory <<"Mnmlist ";
	if(maxim){
		for(vector<int>::const_reverse_iterator i=minorderedlist.rbegin(); i<minorderedlist.rend(); ++i){
			theory <<*i <<" ";
		}
	}else{
		for(vector<int>::const_iterator i=minorderedlist.begin(); i<minorderedlist.end(); ++i){
			theory <<*i <<" ";
		}
	}
	theory <<" 0\n";
}

void InsertWrapper::add(Search* search){
	switch(search->type){
	case SOLVE_SATISFY:
		break;
	case SOLVE_MINIMIZE:
		addOptim(*search->expr, false);
		break;
	case SOLVE_MAXIMIZE:
		addOptim(*search->expr, true);
		break;
	}
}

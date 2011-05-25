/*
 * Copyright 2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "flatzincsupport/FZDatastructs.hpp"

#include <assert.h>

#include "flatzincsupport/fzexception.hpp"

using namespace std;
using namespace FZ;

int nextint = 1;
std::map<std::string, MBoolVar*> name2bool;
std::map<std::string, MIntVar*> name2int;
std::map<std::string, MBoolArrayVar*> name2boolarray;
std::map<std::string, MIntArrayVar*> name2intarray;

MBoolVar* createBoolVar(const string& name){
	MBoolVar* var = new MBoolVar();
	var->var = nextint++;
	var->hasmap = false;
	var->hasvalue = false;
	name2bool.insert(pair<string, MBoolVar*>(name, var));
	return var;
}

int FZ::createOneShotVar(){
	return nextint++;
}

MIntVar* createIntVar(const string& name){
	MIntVar* var = new MIntVar();
	var->var = nextint++;
	var->hasmap = false;
	var->hasvalue = false;
	name2int.insert(pair<string, MIntVar*>(name, var));
	return var;
}

MBoolArrayVar* createBoolArrayVar(const string& name, int nbelem){
	MBoolArrayVar* var = new MBoolArrayVar();
	var->nbelem = nbelem;
	name2boolarray.insert(pair<string, MBoolArrayVar*>(name, var));
	return var;
}

MIntArrayVar* createIntArrayVar(const string& name, int nbelem){
	MIntArrayVar* var = new MIntArrayVar();
	var->nbelem = nbelem;
	name2intarray.insert(pair<string, MIntArrayVar*>(name, var));
	return var;
}

MBoolVar* FZ::getBoolVar(const string& name){
	map<string, MBoolVar*>::iterator it = name2bool.find(name);
	if(it==name2bool.end()){
		throw fzexception("Variable was not declared.\n");
	}
	return (*it).second;
}

MIntVar* FZ::getIntVar(const string& name){
	map<string, MIntVar*>::iterator it = name2int.find(name);
	if(it==name2int.end()){
		throw fzexception("Variable was not declared.\n");
	}
	return (*it).second;
}

//IMPORTANT: index starts at ONE, so map to 0 based!
MBoolVar* FZ::getBoolVar(const string& name, int index){
	map<string, MBoolArrayVar*>::iterator it = name2boolarray.find(name);
	if(it==name2boolarray.end() || (*it).second->vars.size()<index){
		throw fzexception("Array was not declared or not initialized.\n");
	}
	return (*it).second->vars[index-1];
}

MIntVar* FZ::getIntVar(const string& name, int index){
	map<string, MIntArrayVar*>::iterator it = name2intarray.find(name);
	if(it==name2intarray.end() || (*it).second->vars.size()<index){
		throw fzexception("Array was not declared or not initialized.\n");
	}
	return (*it).second->vars[index-1];
}

int FZ::getVar(const string& name, bool expectbool){
	if(expectbool){
		return getBoolVar(name)->var;
	}else{
		return getIntVar(name)->var;
	}
}

int FZ::getVar(const string& name, int index, bool expectbool){
	if(expectbool){
		return getBoolVar(name, index)->var;
	}else{
		return getIntVar(name, index)->var;
	}
}

int FZ::getTrue(std::ostream& vars){
	int newvar = nextint++;
	vars <<newvar <<" 0\n";
	return newvar;
}

int FZ::getFalse(std::ostream& vars){
	int newvar = nextint++;
	vars <<-newvar <<" 0\n";
	return newvar;
}




void addBoolExpr(MBoolVar& var, const Expression& expr, std::stringstream& vars, std::stringstream& theory){
	if(expr.type==EXPR_BOOL){
		var.hasvalue = true;
		var.mappedvalue = expr.boollit;
		theory <<(expr.boollit?"":"-") <<var.var <<" 0\n";
	}else if(expr.type==EXPR_ARRAYACCESS){
		var.hasmap = true;
		var.mappedvar = getBoolVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index)->var;
		theory <<"EQUIV C " <<var.var <<" | " <<var.mappedvar <<" 0\n";
	}else if(expr.type==EXPR_IDENT){
		var.hasmap = true;
		var.mappedvar = getBoolVar(*expr.ident->name)->var;
		theory <<"EQUIV C " <<var.var <<" | " <<var.mappedvar <<" 0\n";
	}else{ throw fzexception("Unexpected type.\n"); }
}

void Var::add(std::stringstream& vars, std::stringstream& theory){
	if(type!=VAR_BOOL){ throw fzexception("Incorrect type.\n"); }

	MBoolVar* var = createBoolVar(getName());
	if(expr!=NULL){
		addBoolExpr(*var, *expr, vars, theory);
	}
}

void writeIntVar(const MIntVar& var, std::stringstream& vars){
	if(var.range){
		vars <<"INTVAR " <<var.var <<" " <<var.begin <<" " <<var.end <<" 0\n";
	}else{
		vars <<"INTVARDOM " <<var.var <<" ";
		for(vector<int>::const_iterator i=var.values.begin(); i<var.values.end(); ++i){
			vars <<*i <<" ";
		}
		vars <<" 0\n";
	}
}

//nobounds implies that it has not been written to output
void addIntExpr(MIntVar& var, bool nobounds, const Expression& expr, std::stringstream& vars, std::stringstream& theory){
	if(expr.type==EXPR_INT){
		var.hasvalue = true;
		var.mappedvalue = expr.intlit;
		if(nobounds){
			var.range = true;
			var.begin = var.mappedvalue;
			var.end = var.mappedvalue;
		}
	}else if(expr.type==EXPR_ARRAYACCESS){
		assert(hasnobounds);
		var.hasmap = true;
		MIntVar* map = getIntVar(*expr.arrayaccesslit->id, expr.arrayaccesslit->index);
		var.mappedvar = map->var;
		if(nobounds){
			var.range = map->range;
			var.begin = map->begin;
			var.end = map->end;
			var.values = map->values;
		}
	}else if(expr.type==EXPR_IDENT){
		var.hasmap = true;
		MIntVar* map = getIntVar(*expr.ident->name);
		var.mappedvar = map->var;
		if(nobounds){
			var.range = map->range;
			var.begin = map->begin;
			var.end = map->end;
			var.values = map->values;
		}
	}else{ throw fzexception("Unexpected type.\n"); }
	theory <<(var.hasvalue?"BINTRI ":"BINTRT ") <<getTrue(vars) <<" " <<var.var <<" = " <<(var.hasvalue?var.mappedvalue:var.mappedvar) <<" 0\n";
}

void IntVar::add(std::stringstream& vars, std::stringstream& theory){
	if(type!=VAR_INT){ throw fzexception("Incorrect type.\n"); }

	MIntVar* var = createIntVar(getName());

	//values
	bool nobounds = true;
	if(enumvalues){
		nobounds = false;
		var->range = false;
		var->values = *values;
	}else if(range){
		nobounds = false;
		var->range = true;
		var->begin = begin;
		var->end = end;
	}else if(expr==NULL){
		throw fzexception("Unbounded integer types are not supported by the backend.\n");
	}

	if(expr!=NULL){
		addIntExpr(*var, nobounds, *expr, vars, theory);
	}
	writeIntVar(*var, vars);
}

void ArrayVar::add(std::stringstream& vars, std::stringstream& theory){
	if(type!=VAR_ARRAY || begin!=1 || end<begin){ throw fzexception("Incorrect type.\n"); }

	VAR_TYPE mappedtype = rangetype;
	if(rangevar!=NULL){
		mappedtype = rangevar->type;
	}

	if(arraylit!=NULL && arraylit->exprs->size()!=0){
		if((int)arraylit->exprs->size() != end){
			throw fzexception("Incorrect nb of expressions.\n");
		}
	}

	if(mappedtype==VAR_BOOL){
		MBoolArrayVar* var = createBoolArrayVar(getName(), end);
		for(int i=1; i<=end; i++){
			MBoolVar* boolvar = new MBoolVar();
			boolvar->var = nextint++;
			boolvar->hasmap = false;
			boolvar->hasvalue = false;
			var->vars.push_back(boolvar);
		}
		// values
		if(arraylit!=NULL){
			int index = 1;
			for(vector<Expression*>::const_iterator i=arraylit->exprs->begin(); i<arraylit->exprs->end(); ++i, ++index){
				addBoolExpr(*var->vars[index], **i, vars, theory);
			}
		}
	}else{
		MIntArrayVar* var = createIntArrayVar(getName(), end);

		MIntVar* intvar = new MIntVar();
		intvar->var = nextint++;
		intvar->hasmap = false;
		intvar->hasvalue = false;
		bool nobounds = true;
		if(rangevar!=NULL){
			IntVar* rangedvar = dynamic_cast<IntVar*>(rangevar);
			if(rangedvar->enumvalues){
				nobounds = false;
				intvar->range = false;
				intvar->values = *rangedvar->values;
			}else if(rangedvar->range){
				nobounds = false;
				intvar->range = true;
				intvar->begin = rangedvar->begin;
				intvar->end = rangedvar->end;
			}
		}

		for(int i=1; i<=end; i++){
			MIntVar* tempvar = new MIntVar(*intvar);
			intvar->var = nextint++;
			var->vars.push_back(tempvar);
		}

		// values
		if(arraylit!=NULL){
			int index = 0;
			for(vector<Expression*>::const_iterator i=arraylit->exprs->begin(); i<arraylit->exprs->end(); ++i, ++index){
				addIntExpr(*var->vars[index], nobounds, **i, vars, theory);
			}
		}

		for(vector<MIntVar*>::const_iterator i=var->vars.begin(); i<var->vars.end(); ++i){
			writeIntVar(**i, vars);
		}
	}
}

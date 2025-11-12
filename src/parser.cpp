/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */
//
#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        std::vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); ++i) {
            parameters.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(stxs[0]->parse(env), parameters));
    }else{
    string op = id->s;
    if (find(op, env).get() != nullptr) {
        std::vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); ++i)
            args.push_back(stxs[i]->parse(env));
        return Expr(new Apply(Expr(new Var(op)), args));
    }
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); ++i) {
                parameters.push_back(stxs[i]->parse(env));
            }
        
        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            return Expr(new PlusVar(parameters));
        } else if (op_type == E_MINUS) {
            return Expr(new MinusVar(parameters));
        } else if (op_type == E_MUL) {
            return Expr(new MultVar(parameters));
        }  else if (op_type == E_DIV) {
            return Expr(new DivVar(parameters));
        }else if (op_type == E_EXPT) {
            return Expr(new Expt(stxs[1]->parse(env), stxs[2]->parse(env)));
        }else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_LT) {
            return Expr(new LessVar(parameters));
        } else if (op_type == E_LE) {
            return Expr(new LessEqVar(parameters));
        } else if (op_type == E_EQ) {
            return Expr(new EqualVar(parameters));
        } else if (op_type == E_GE) {
            return Expr(new GreaterEqVar(parameters));
        } else if (op_type == E_GT) {
            return Expr(new GreaterVar(parameters));
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else if(op_type == E_EXIT){
            if (stxs.size() != 1) throw RuntimeError("exit takes no arguments");
            return Expr(new Exit());
        }else if(op_type == E_CONS){
            if (stxs.size() != 3)
                throw RuntimeError("cons requires 2 arguments");
            Expr e1 = stxs[1]->parse(env);
            Expr e2 = stxs[2]->parse(env);
            return Expr(new Cons(e1, e2));
        }else if(op_type == E_CAR){
            if (stxs.size() != 2)
                throw RuntimeError("car requires 1 argument");
            Expr e = stxs[1]->parse(env);
            return Expr(new Car(e));
        }else if(op_type == E_CDR){
            if (stxs.size() != 2)
                throw RuntimeError("cdr requires 1 argument");
            Expr e = stxs[1]->parse(env);
            return Expr(new Cdr(e));
        }else if(op_type == E_VOID){
            return Expr(new MakeVoid());
        }else if(op_type == E_PAIRQ){
            if (stxs.size() != 2)
                throw RuntimeError("pair? requires 1 argument");
            Expr e = stxs[1]->parse(env);
            return Expr(new IsPair(e));
        }else if(op_type == E_BOOLQ){
            return Expr(new IsBoolean(stxs[1]->parse(env)));
        }else if(op_type == E_NULLQ){
            return Expr(new IsNull(stxs[1]->parse(env)));
        }else if(op_type == E_INTQ){
            return Expr(new IsFixnum(stxs[1]->parse(env)));
        }else if(op_type == E_PROCQ){
            return Expr(new IsProcedure(stxs[1]->parse(env)));
        }else if(op_type == E_SYMBOLQ){
            return Expr(new IsSymbol(stxs[1]->parse(env)));
        }else if(op_type == E_LISTQ){
            return Expr(new IsList(stxs[1]->parse(env)));
        }else if (op_type == E_STRINGQ) {
            return Expr(new IsString(stxs[1]->parse(env)));
        }else if (op_type == E_EQQ) {
            return Expr(new IsEq(stxs[1]->parse(env), stxs[2]->parse(env)));
        }
        else {
            throw RuntimeError("Unhandled primitive: " + op);
        }
    }

    if (reserved_words.count(op) != 0) {
        if (!op.empty() && reserved_words.count(op) != 0 && find(op, env).get() == nullptr){
    	switch (reserved_words[op]) {
			case E_IF:
            if (stxs.size() != 4) throw RuntimeError("if requires 3 arguments");
            return Expr(new If(stxs[1]->parse(env), stxs[2]->parse(env), stxs[3]->parse(env)));
        case E_BEGIN: {
            std::vector<Expr> es;
            for (size_t i = 1; i < stxs.size(); ++i)
                es.push_back(stxs[i]->parse(env));
            return Expr(new Begin(es));
        }
        case E_QUOTE:
            if (stxs.size() != 2) throw RuntimeError("quote requires 1 argument");
            return Expr(new Quote(stxs[1]));
        case E_DEFINE: {
            if (stxs.size() != 3) throw RuntimeError("define requires 2 arguments");
            SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[1].get());
            if (!id) throw RuntimeError("define first argument must be a symbol");
            return Expr(new Define(id->s, stxs[2]->parse(env)));
        }
        case E_LAMBDA: {
            


            
        }
        case E_SET: {
            if (stxs.size() != 3) throw RuntimeError("set requires 2 arguments");
            SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[1].get());
            if (!id) throw RuntimeError("set first argument must be a symbol");
            return Expr(new Set(id->s, stxs[2]->parse(env)));
        }
        case E_LET: {
            if (stxs.size() < 3) throw RuntimeError("let requires bindings and body");
            List *bindingList = dynamic_cast<List*>(stxs[1].get());
            if (!bindingList) throw RuntimeError("let bindings must be a list");
            std::vector<std::pair<std::string, Expr>> binds;
            for (auto &b : bindingList->stxs) {
                List *pairList = dynamic_cast<List*>(b.get());
                if (!pairList || pairList->stxs.size() != 2)
                    throw RuntimeError("each let binding must be a pair");
                SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(pairList->stxs[0].get());
                if (!sym) throw RuntimeError("let binding first element must be a symbol");
                binds.push_back({sym->s, pairList->stxs[1]->parse(env)});
            }
            std::vector<Expr> bodyEs;
            for (size_t i = 2; i < stxs.size(); ++i)
                bodyEs.push_back(stxs[i]->parse(env));
            Expr body = (bodyEs.size() == 1) ? bodyEs[0] : Expr(new Begin(bodyEs));
            return Expr(new Let(binds, body));
        }
        case E_LETREC: {
            if (stxs.size() < 3) throw RuntimeError("letrec requires bindings and body");
            List *bindingList = dynamic_cast<List*>(stxs[1].get());
            if (!bindingList) throw RuntimeError("letrec bindings must be a list");
            std::vector<std::pair<std::string, Expr>> binds;
            for (auto &b : bindingList->stxs) {
                List *pairList = dynamic_cast<List*>(b.get());
                if (!pairList || pairList->stxs.size() != 2)
                    throw RuntimeError("each letrec binding must be a pair");
                SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(pairList->stxs[0].get());
                if (!sym) throw RuntimeError("letrec binding first element must be a symbol");
                binds.push_back({sym->s, pairList->stxs[1]->parse(env)});
            }
            std::vector<Expr> bodyEs;
            for (size_t i = 2; i < stxs.size(); ++i)
                bodyEs.push_back(stxs[i]->parse(env));
            Expr body = (bodyEs.size() == 1) ? bodyEs[0] : Expr(new Begin(bodyEs));
            return Expr(new Letrec(binds, body));
        }
        case E_COND: {
            std::vector<std::vector<Expr>> clauses;
            for (size_t i = 1; i < stxs.size(); ++i) {
                List *clauseList = dynamic_cast<List*>(stxs[i].get());
                if (!clauseList || clauseList->stxs.size() < 2)
                    throw RuntimeError("each cond clause must have a test and at least one expression");
                std::vector<Expr> clauseEs;
                clauseEs.push_back(clauseList->stxs[0]->parse(env));
                for (size_t j = 1; j < clauseList->stxs.size(); ++j)
                    clauseEs.push_back(clauseList->stxs[j]->parse(env));
                clauses.push_back(clauseEs);
            }
            return Expr(new Cond(clauses));
        }
        	default:
            	throw RuntimeError("Unknown reserved word: " + op);
    	}
        }
    }

    Expr rator_expr = stxs[0]->parse(env);
    std::vector<Expr> parameters;
    for (size_t i = 1; i < stxs.size(); ++i) {
        parameters.push_back(stxs[i]->parse(env));
    }
    return Expr(new Apply(rator_expr, parameters));
}
}

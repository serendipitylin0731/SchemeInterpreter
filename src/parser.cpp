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
    //TODO: complete the rational parser
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

    //TODO: check if the first element is a symbol
    //If not, use Apply function to package to a closure;
    //If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        vector<Expr> args;
        for (size_t i = 0; i < stxs.size(); ++i) {
            args.push_back(stxs[i]->parse(env));
        }
    }else{
        string op = id->s;
        if (find(op, env).get() != nullptr) {
            vector<Expr> args;
                for (size_t i = 1; i < stxs.size(); ++i)
                    args.push_back(stxs[i]->parse(env));
                return Expr(new Apply(Expr(new Var(op)), args));
        }
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); ++i)
                parameters.push_back(stxs[i]->parse(env));
        
        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            if (parameters.size() == 2) {
                return Expr(new Plus(parameters[0], parameters[1])); 
            } else {
                throw RuntimeError("Wrong number of arguments for +");
            }
        } else if (op_type == E_MINUS) {
            if (parameters.size() != 2)
                throw RuntimeError("Wrong number of arguments for -");
            return Expr(new Minus(parameters[0], parameters[1]));
        } else if (op_type == E_MUL) {
            if (parameters.size() != 2)
                throw RuntimeError("Wrong number of arguments for *");
            return Expr(new Mult(parameters[0], parameters[1]));
        }  else if (op_type == E_DIV) {
            if (parameters.size() != 2)
                        throw RuntimeError("Wrong number of arguments for /");
                    return Expr(new Div(parameters[0], parameters[1]));
        } else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_LT) {
            if (parameters.size() == 2) {
                    return Expr(new Less(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for <");
            }
        } else if (op_type == E_LE) {
            if (parameters.size() == 2) {
                return Expr(new LessEq(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for <=");
            }
        } else if (op_type == E_EQ) {
            if (parameters.size() == 2) {
                return Expr(new Equal(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for =");
            }
        } else if (op_type == E_GE) {
            if (parameters.size() == 2) {
                return Expr(new GreaterEq(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for >=");
            }
        } else if (op_type == E_GT) {
            if (parameters.size() == 2) {
                return Expr(new Greater(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for >");
            }
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else {
            throw RuntimeError("Unknown primitive: " + op);
        }
    }

    if (reserved_words.count(op) != 0) {
    	switch (reserved_words[op]) {
case E_IF: {
                    if (stxs.size() != 4)
                        throw RuntimeError("if requires 3 arguments");
                    Expr cond = stxs[1]->parse(env);
                    Expr then_expr = stxs[2]->parse(env);
                    Expr else_expr = stxs[3]->parse(env);
                    return Expr(new If(cond, then_expr, else_expr));
                }
                case E_BEGIN: {
                    vector<Expr> body;
                    for (size_t i = 1; i < stxs.size(); ++i)
                        body.push_back(stxs[i]->parse(env));
                    return Expr(new Begin(body));
                }
                case E_QUOTE: {
                    if (stxs.size() != 2)
                        throw RuntimeError("quote requires 1 argument");
                    return Expr(new Quote(stxs[1]));
                }
                case E_DEFINE: {
                    if (stxs.size() != 3)
                        throw RuntimeError("define requires 2 arguments");
                    SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                    if (!sym) throw RuntimeError("first argument of define must be a symbol");
                    Expr body = stxs[2]->parse(env);
                    return Expr(new Define(sym->s, body));
                }
                case E_LAMBDA: {
                    if (stxs.size() < 3)
                        throw RuntimeError("lambda requires parameter list and body");
                    List *param_list = dynamic_cast<List*>(stxs[1].get());
                    if (!param_list)
                        throw RuntimeError("lambda parameter must be a list");
                    vector<string> params;
                    for (auto &sx : param_list->stxs) {
                        SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(sx.get());
                        if (!sym)
                            throw RuntimeError("lambda parameter must be a symbol");
                        params.push_back(sym->s);
                    }
                    // body 合并为 (begin ...) 形式
                    if (stxs.size() == 3)
                        return Expr(new Lambda(params, stxs[2]->parse(env)));
                    else {
                        vector<Expr> bodies;
                        for (size_t i = 2; i < stxs.size(); ++i)
                            bodies.push_back(stxs[i]->parse(env));
                        return Expr(new Lambda(params, Expr(new Begin(bodies))));
                    }
                }
                case E_LET: {
                    if (stxs.size() < 3)
                        throw RuntimeError("let requires bindings and body");
                    List *binds = dynamic_cast<List*>(stxs[1].get());
                    if (!binds)
                        throw RuntimeError("let bindings must be a list");
                    vector<pair<string, Expr>> bindings;
                    for (auto &b : binds->stxs) {
                        List *pair_list = dynamic_cast<List*>(b.get());
                        if (!pair_list || pair_list->stxs.size() != 2)
                            throw RuntimeError("let binding must be (var expr)");
                        SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(pair_list->stxs[0].get());
                        if (!sym)
                            throw RuntimeError("let binding variable must be symbol");
                        bindings.push_back(mp(sym->s, pair_list->stxs[1]->parse(env)));
                    }
                    // body 合并为 begin
                    vector<Expr> bodies;
                    for (size_t i = 2; i < stxs.size(); ++i)
                        bodies.push_back(stxs[i]->parse(env));
                    Expr body = Expr(new Begin(bodies));
                    return Expr(new Let(bindings, body));
                }
                case E_LETREC: {
                    if (stxs.size() < 3)
                        throw RuntimeError("letrec requires bindings and body");
                    List *binds = dynamic_cast<List*>(stxs[1].get());
                    if (!binds)
                        throw RuntimeError("letrec bindings must be a list");
                    vector<pair<string, Expr>> bindings;
                    for (auto &b : binds->stxs) {
                        List *pair_list = dynamic_cast<List*>(b.get());
                        if (!pair_list || pair_list->stxs.size() != 2)
                            throw RuntimeError("letrec binding must be (var expr)");
                        SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(pair_list->stxs[0].get());
                        if (!sym)
                            throw RuntimeError("letrec binding variable must be symbol");
                        bindings.push_back(mp(sym->s, pair_list->stxs[1]->parse(env)));
                    }
                    vector<Expr> bodies;
                    for (size_t i = 2; i < stxs.size(); ++i)
                        bodies.push_back(stxs[i]->parse(env));
                    Expr body = Expr(new Begin(bodies));
                    return Expr(new Letrec(bindings, body));
                }
                case E_SET: {
                    if (stxs.size() != 3)
                        throw RuntimeError("set! requires 2 arguments");
                    SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                    if (!sym) throw RuntimeError("first argument of set! must be a symbol");
                    Expr rhs = stxs[2]->parse(env);
                    return Expr(new Set(sym->s, rhs));
                }
                default:
                    throw RuntimeError("Unknown reserved word: " + op);
    	}
    }

    vector<Expr> args;  
    for (size_t i = 1; i < stxs.size(); ++i)
        args.push_back(stxs[i]->parse(env));
    return Expr(new Apply(Expr(new Var(op)), args));
}
}

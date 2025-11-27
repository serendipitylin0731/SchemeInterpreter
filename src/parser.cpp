/**
 * @file parser.cpp
 * @brief Syntax tree parsing and transformation implementation
 * @brief 语法树解析和转换实现
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>
#include <vector>
#include <utility>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Parse method not implemented");
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
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(stxs[0]->parse(env), parameters));
    } else {
        std::string op = id->s;
        if (find(op, env).get() != nullptr) {
            std::vector<Expr> parameters;
            for (size_t i = 1; i < stxs.size(); i++) {
                parameters.push_back(stxs[i].get()->parse(env));
            }
            return Expr(new Apply(stxs[0].get()->parse(env), parameters));
        }
        
        if (primitives.count(op) != 0) {
            std::vector<Expr> parameters;
            for (int i = 1; i < stxs.size(); i++) {
                parameters.push_back(stxs[i].get()->parse(env));
            }
            
            ExprType op_type = primitives[op];
            if (op_type == E_PLUS) {
                if (parameters.size() == 0) {
                    return Expr(new PlusVar(parameters));
                } else if (parameters.size() == 1) {
                    return parameters[0];
                } else if (parameters.size() == 2) {
                    return Expr(new Plus(parameters[0], parameters[1]));
                } else {
                    return Expr(new PlusVar(parameters));
                }
            } else if (op_type == E_MINUS) {
                if (parameters.size() == 0) {
                    throw RuntimeError("Insufficient arguments for subtraction");
                } else if (parameters.size() == 1) {
                    return Expr(new MinusVar(parameters));
                } else if (parameters.size() == 2) {
                    return Expr(new Minus(parameters[0], parameters[1]));
                } else {
                    return Expr(new MinusVar(parameters));
                }
            } else if (op_type == E_MUL) {
                if (parameters.size() == 0) {
                    return Expr(new MultVar(parameters));
                } else if (parameters.size() == 1) {
                    return parameters[0];
                } else if (parameters.size() == 2) {
                    return Expr(new Mult(parameters[0], parameters[1]));
                } else {
                    return Expr(new MultVar(parameters));
                }
            } else if (op_type == E_DIV) {
                if (parameters.size() == 0) {
                    throw RuntimeError("Insufficient arguments for division");
                } else if (parameters.size() == 1) {
                    return Expr(new DivVar(parameters));
                } else if (parameters.size() == 2) {
                    return Expr(new Div(parameters[0], parameters[1]));
                } else {
                    return Expr(new DivVar(parameters));
                }
            } else if (op_type == E_MODULO) {
                if (parameters.size() != 2) {
                    throw RuntimeError("Modulo requires exactly two arguments");
                }
                return Expr(new Modulo(parameters[0], parameters[1]));
            } else if (op_type == E_LIST) {
                return Expr(new ListFunc(parameters));
            } else if (op_type == E_LT) {
                if (parameters.size() < 2) {
                    throw RuntimeError("Less than requires at least two arguments");
                } else if (parameters.size() == 2) {
                    return Expr(new Less(parameters[0], parameters[1]));
                } else {
                    return Expr(new LessVar(parameters));
                }
            } else if (op_type == E_LE) {
                if (parameters.size() < 2) {
                    throw RuntimeError("Less equal requires at least two arguments");
                } else if (parameters.size() == 2) {
                    return Expr(new LessEq(parameters[0], parameters[1]));
                } else {
                    return Expr(new LessEqVar(parameters));
                }
            } else if (op_type == E_EQ) {
                if (parameters.size() < 2) {
                    throw RuntimeError("Equal requires at least two arguments");
                } else if (parameters.size() == 2) {
                    return Expr(new Equal(parameters[0], parameters[1]));
                } else {
                    return Expr(new EqualVar(parameters));
                }
            } else if (op_type == E_GE) {
                if (parameters.size() < 2) {
                    throw RuntimeError("Greater equal requires at least two arguments");
                } else if (parameters.size() == 2) {
                    return Expr(new GreaterEq(parameters[0], parameters[1]));
                } else {
                    return Expr(new GreaterEqVar(parameters));
                }
            } else if (op_type == E_GT) {
                if (parameters.size() < 2) {
                    throw RuntimeError("Greater than requires at least two arguments");
                } else if (parameters.size() == 2) {
                    return Expr(new Greater(parameters[0], parameters[1]));
                } else {
                    return Expr(new GreaterVar(parameters));
                }
            } else if (op_type == E_AND) {
                return Expr(new AndVar(parameters));
            } else if (op_type == E_OR) {
                return Expr(new OrVar(parameters));
            } else {
                return Expr(new Apply(stxs[0].get()->parse(env), parameters));
            }
        }

        if (reserved_words.count(op) != 0) {
            switch (reserved_words[op]) {
                case E_BEGIN: {
                    std::vector<Expr> passed_exprs;
                    for (size_t i = 1; i < stxs.size(); i++) {
                        passed_exprs.push_back(stxs[i]->parse(env));
                    }
                    return Expr(new Begin(passed_exprs));
                }
                case E_QUOTE: {
                    if (stxs.size() != 2) throw RuntimeError("Quote requires exactly one argument");
                    return Expr(new Quote(stxs[1]));
                }
                case E_IF: {
                    if (stxs.size() != 4) throw RuntimeError("If requires three arguments");
                    return Expr(new If(stxs[1]->parse(env), stxs[2]->parse(env), stxs[3]->parse(env)));
                }
                case E_COND: {
                    if (stxs.size() < 2) throw RuntimeError("Cond requires at least one clause");
                    std::vector<std::vector<Expr>> clauses;
                    for (size_t i = 1; i < stxs.size(); i++) {
                        List* clause_list = dynamic_cast<List*>(stxs[i].get());
                        if (clause_list == nullptr || clause_list->stxs.empty()) {
                            throw RuntimeError("Invalid cond clause structure");
                        }
                        std::vector<Expr> clause_exprs;
                        for (auto& clause_stx : clause_list->stxs) {
                            clause_exprs.push_back(clause_stx->parse(env));
                        }
                        clauses.push_back(clause_exprs);
                    }
                    return Expr(new Cond(clauses));
                }
                case E_LAMBDA: {
                    if (stxs.size() < 3) throw RuntimeError("Lambda requires parameters and body");
                    Assoc New_env = env;
                    std::vector<std::string> vars;
                    List* paras_ptr = dynamic_cast<List*>(stxs[1].get());
                    if (paras_ptr == nullptr) {
                        throw RuntimeError("Invalid lambda parameter list");
                    }
                    for (int i = 0; i < paras_ptr->stxs.size(); i++) {
                        if (auto tmp_var = dynamic_cast<Var*>(paras_ptr->stxs[i].get()->parse(env).get())) {
                            vars.push_back(tmp_var->x);
                            New_env = extend(tmp_var->x, NullV(), New_env);
                        } else {
                            throw RuntimeError("Invalid parameter in lambda");
                        }
                    }
                    
                    if (stxs.size() == 3) {
                        return Expr(new Lambda(vars, stxs[2].get()->parse(New_env)));
                    } else {
                        std::vector<Expr> body_exprs;
                        for (size_t i = 2; i < stxs.size(); i++) {
                            body_exprs.push_back(stxs[i]->parse(New_env));
                        }
                        return Expr(new Lambda(vars, Expr(new Begin(body_exprs))));
                    }
                }
                case E_DEFINE: {
                    if (stxs.size() < 3) throw RuntimeError("Define requires variable and expression");
                    
                    List *func_def_list = dynamic_cast<List*>(stxs[1].get());
                    if (func_def_list != nullptr) {
                        if (func_def_list->stxs.empty()) {
                            throw RuntimeError("Function definition requires name and parameters");
                        }
                        
                        SymbolSyntax *func_name = dynamic_cast<SymbolSyntax*>(func_def_list->stxs[0].get());
                        if (func_name == nullptr) {
                            throw RuntimeError("Invalid function name in define");
                        }
                        
                        std::vector<std::string> param_names;
                        for (size_t i = 1; i < func_def_list->stxs.size(); i++) {
                            SymbolSyntax *param = dynamic_cast<SymbolSyntax*>(func_def_list->stxs[i].get());
                            if (param == nullptr) {
                                throw RuntimeError("Invalid parameter in function definition");
                            }
                            param_names.push_back(param->s);
                        }
                        
                        if (stxs.size() == 3) {
                            Expr lambda_expr = Expr(new Lambda(param_names, stxs[2]->parse(env)));
                            return Expr(new Define(func_name->s, lambda_expr));
                        } else {
                            std::vector<Expr> body_exprs;
                            for (size_t i = 2; i < stxs.size(); i++) {
                                body_exprs.push_back(stxs[i]->parse(env));
                            }
                            Expr lambda_expr = Expr(new Lambda(param_names, Expr(new Begin(body_exprs))));
                            return Expr(new Define(func_name->s, lambda_expr));
                        }
                    } else {
                        if (stxs.size() != 3) throw RuntimeError("Variable define requires exactly two arguments");
                        SymbolSyntax *var_id = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                        if (var_id == nullptr) {
                            throw RuntimeError("Invalid variable name in define");
                        }
                        return Expr(new Define(var_id->s, stxs[2]->parse(env)));
                    }
                }
                case E_LET: {
                    if (stxs.size() != 3) throw RuntimeError("Let requires bindings and body");
                    std::vector<std::pair<std::string, Expr>> binded_vector;
                    List *binder_list_ptr = dynamic_cast<List*>(stxs[1].get());
                    if (binder_list_ptr == nullptr) {
                        throw RuntimeError("Invalid let binding list");
                    }

                    Assoc local_env = env;
                    for (int i = 0; i < binder_list_ptr->stxs.size(); i++) {
                        auto pair_it = dynamic_cast<List*>(binder_list_ptr->stxs[i].get());
                        if ((pair_it == nullptr) || (pair_it->stxs.size() != 2)) {
                            throw RuntimeError("Invalid let binding format");
                        }
                        auto Identifiers = dynamic_cast<SymbolSyntax*>(pair_it->stxs.front().get());
                        if (Identifiers == nullptr) {
                            throw RuntimeError("Invalid identifier in let binding");
                        }
                        Expr temp_expr = pair_it->stxs.back().get()->parse(env);
                        local_env = extend(Identifiers->s, NullV(), local_env);
                        std::pair<std::string, Expr> tmp_pair = std::make_pair(Identifiers->s, temp_expr);
                        binded_vector.push_back(tmp_pair);
                    }
                    return Expr(new Let(binded_vector, stxs[2]->parse(local_env)));
                }
                case E_LETREC: {
                    if (stxs.size() != 3) throw RuntimeError("Letrec requires bindings and body");
                    std::vector<std::pair<std::string, Expr>> binded_vector;
                    List *binder_list_ptr = dynamic_cast<List*>(stxs[1].get());
                    if (binder_list_ptr == nullptr) {
                        throw RuntimeError("Invalid letrec binding list");
                    }
                    
                    Assoc temp_env = env;
                    
                    for (auto &stx_tobind_raw : binder_list_ptr->stxs) {
                        List *stx_tobind = dynamic_cast<List*>(stx_tobind_raw.get());
                        if (stx_tobind == nullptr || stx_tobind->stxs.size() != 2) {
                            throw RuntimeError("Invalid letrec binding format");
                        }
                        SymbolSyntax *temp_id = dynamic_cast<SymbolSyntax*>(stx_tobind->stxs[0].get());
                        if (temp_id == nullptr) {
                            throw RuntimeError("Invalid identifier in letrec binding");
                        }
                        temp_env = extend(temp_id->s, NullV(), temp_env);
                    }
                    
                    for (auto &stx_tobind_raw : binder_list_ptr->stxs) {
                        List *stx_tobind = dynamic_cast<List*>(stx_tobind_raw.get());
                        SymbolSyntax *temp_id = dynamic_cast<SymbolSyntax*>(stx_tobind->stxs[0].get());
                        Expr temp_store = stx_tobind->stxs[1]->parse(temp_env);
                        binded_vector.push_back(std::make_pair(temp_id->s, temp_store));
                    }
                    
                    return Expr(new Letrec(binded_vector, stxs[2]->parse(temp_env)));
                }
                case E_SET: {
                    if (stxs.size() != 3) throw RuntimeError("Set requires variable and expression");
                    SymbolSyntax *var_id = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                    if (var_id == nullptr) {
                        throw RuntimeError("Invalid variable name in set");
                    }
                    return Expr(new Set(var_id->s, stxs[2]->parse(env)));
                }
                default:
                    throw RuntimeError("Unknown reserved word: " + op);
            }
        }

        Expr opexpr = stxs[0]->parse(env);
        std::vector<Expr> to_expr;
        for (size_t i = 1; i < stxs.size(); i++) {
            to_expr.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(opexpr, to_expr));
    }
}
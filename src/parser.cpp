#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <vector>

using std::string;
using std::vector;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/******************************
 * 基本语法节点 Parse
 ******************************/

Expr Syntax::parse(Assoc &env) {
    return ptr->parse(env);
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

/*********************************************
 * 核心：List::parse
 *********************************************/
Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    SyntaxBase *headPtr = stxs[0].ptr.get();
    SymbolSyntax *headSym = dynamic_cast<SymbolSyntax*>(headPtr);

    if (!headSym) {
        Expr rator = stxs[0].parse(env);
        vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); ++i)
            args.push_back(stxs[i].parse(env));
        return Expr(new Apply(rator, args));
    }

    string op = headSym->s;
    
    bool is_bound = false;
    Value bound_value = find(op, env);
    if (bound_value.get() != nullptr) {
        is_bound = true;
    }

    if (!is_bound && reserved_words.count(op)) {
        ExprType kw = reserved_words[op];
        switch (kw) {
            case E_IF:
                if (stxs.size() != 4) throw RuntimeError("if requires 3 args");
                return Expr(new If(
                    stxs[1].parse(env),
                    stxs[2].parse(env),
                    stxs[3].parse(env)
                ));
            case E_BEGIN: {
                vector<Expr> es;
                for (size_t i = 1; i < stxs.size(); ++i)
                    es.push_back(stxs[i].parse(env));
                return Expr(new Begin(es));
            }
            case E_QUOTE:
                if (stxs.size() != 2) throw RuntimeError("quote requires 1 arg");
                return Expr(new Quote(stxs[1]));
            case E_LAMBDA: {
                if (stxs.size() < 3) throw RuntimeError("lambda needs params & body");
                
                vector<string> params;
                bool is_variadic = false;
                
                List *plist = dynamic_cast<List*>(stxs[1].ptr.get());
                if (!plist) throw RuntimeError("lambda parameters must be list");

                for (size_t i = 0; i < plist->stxs.size(); ++i) {
                    if (auto sym = dynamic_cast<SymbolSyntax*>(plist->stxs[i].ptr.get())) {
                        if (sym->s == "..." && i == plist->stxs.size() - 1) {
                            is_variadic = true;
                        } else {
                            params.push_back(sym->s);
                        }
                    } else {
                        throw RuntimeError("lambda param must be symbol");
                    }
                }

                Expr body(nullptr);
                if (stxs.size() == 3)
                    body = stxs[2].parse(env);
                else {
                    vector<Expr> bs;
                    for (size_t i = 2; i < stxs.size(); ++i)
                        bs.push_back(stxs[i].parse(env));
                    body = Expr(new Begin(bs));
                }
                return Expr(new Lambda(params, body, is_variadic));
            }
            case E_DEFINE: {
                if (stxs.size() != 3) throw RuntimeError("define requires 2 args");
                SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(stxs[1].ptr.get());
                if (!sym) throw RuntimeError("define expects symbol");
                return Expr(new Define(sym->s, stxs[2].parse(env)));
            }
            case E_SET: {
                if (stxs.size() != 3) throw RuntimeError("set! requires 2 args");
                SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(stxs[1].ptr.get());
                if (!sym) throw RuntimeError("set! expects symbol");
                return Expr(new Set(sym->s, stxs[2].parse(env)));
            }
            case E_LET:
            case E_LETREC: {
                if (stxs.size() < 3) throw RuntimeError("let/letrec requires bindings & body");

                List *bl = dynamic_cast<List*>(stxs[1].ptr.get());
                if (!bl) throw RuntimeError("let/letrec bindings must be list");

                vector<std::pair<string, Expr>> binds;
                for (auto &b : bl->stxs) {
                    List *pairList = dynamic_cast<List*>(b.ptr.get());
                    if (!pairList || pairList->stxs.size() != 2)
                        throw RuntimeError("each let/letrec binding must be (id expr)");
                    SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(pairList->stxs[0].ptr.get());
                    if (!sym) throw RuntimeError("binding first element must be symbol");
                    
                    binds.push_back({sym->s, pairList->stxs[1].parse(env)});
                }

                vector<Expr> body;
                for (size_t i = 2; i < stxs.size(); ++i)
                    body.push_back(stxs[i].parse(env));
                Expr bodyExpr = (body.size() == 1 ? body[0] : Expr(new Begin(body)));

                if (kw == E_LET) return Expr(new Let(binds, bodyExpr));
                else return Expr(new Letrec(binds, bodyExpr));
            }
            case E_COND: {
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); ++i) {
                    List *cl = dynamic_cast<List*>(stxs[i].ptr.get());
                    if (!cl || cl->stxs.size() < 2) throw RuntimeError("malformed cond clause");
                    vector<Expr> ce;
                    for (auto &e : cl->stxs) ce.push_back(e.parse(env));
                    clauses.push_back(ce);
                }
                return Expr(new Cond(clauses));
            }
            case E_AND: {
                vector<Expr> es;
                for (size_t i = 1; i < stxs.size(); ++i)
                    es.push_back(stxs[i].parse(env));
                return Expr(new AndVar(es));
            }
            case E_OR: {
                vector<Expr> es;
                for (size_t i = 1; i < stxs.size(); ++i)
                    es.push_back(stxs[i].parse(env));
                return Expr(new OrVar(es));
            }
            default:
                throw RuntimeError("unknown keyword " + op);
        }
    }

    if (!is_bound && primitives.count(op)) {
        vector<Expr> ps;
        for (size_t i = 1; i < stxs.size(); ++i)
            ps.push_back(stxs[i].parse(env));

        ExprType t = primitives[op];
        switch (t) {
            case E_PLUS: return Expr(new PlusVar(ps));
            case E_MINUS: return Expr(new MinusVar(ps));
            case E_MUL: return Expr(new MultVar(ps));
            case E_DIV: return Expr(new DivVar(ps));
            case E_LT: return Expr(new LessVar(ps));
            case E_LE: return Expr(new LessEqVar(ps));
            case E_EQ: return Expr(new EqualVar(ps));
            case E_GE: return Expr(new GreaterEqVar(ps));
            case E_GT: return Expr(new GreaterVar(ps));
            case E_LIST: return Expr(new ListFunc(ps));
            case E_VOID: if (ps.size()!=0) throw RuntimeError("void requires 1");return Expr(new MakeVoid());
            case E_EXPT: if (ps.size()!=2) throw RuntimeError("expt requires 2"); return Expr(new Expt(ps[0], ps[1]));
            case E_MODULO: if (ps.size()!=2) throw RuntimeError("modulo requires 2"); return Expr(new Modulo(ps[0], ps[1]));
            case E_CONS: if (ps.size()!=2) throw RuntimeError("cons requires 2"); return Expr(new Cons(ps[0], ps[1]));
            case E_CAR: if (ps.size()!=1) throw RuntimeError("car requires 1"); return Expr(new Car(ps[0]));
            case E_CDR: if (ps.size()!=1) throw RuntimeError("cdr requires 1"); return Expr(new Cdr(ps[0]));
            case E_BOOLQ: if (ps.size()!=1) throw RuntimeError("boolean? requires 1"); return Expr(new IsBoolean(ps[0]));
            case E_INTQ: if (ps.size()!=1) throw RuntimeError("integer? requires 1"); return Expr(new IsFixnum(ps[0]));
            case E_STRINGQ: if (ps.size()!=1) throw RuntimeError("string? requires 1"); return Expr(new IsString(ps[0]));
            case E_SYMBOLQ: if (ps.size()!=1) throw RuntimeError("symbol? requires 1"); return Expr(new IsSymbol(ps[0]));
            case E_LISTQ: if (ps.size()!=1) throw RuntimeError("list? requires 1"); return Expr(new IsList(ps[0]));
            case E_EQQ: if (ps.size()!=2) throw RuntimeError("eq? requires 2"); return Expr(new IsEq(ps[0], ps[1]));
            case E_PAIRQ: if (ps.size()!=1) throw RuntimeError("pair? requires 1"); return Expr(new IsPair(ps[0]));
            case E_PROCQ: if (ps.size()!=1) throw RuntimeError("procedure? requires 1"); return Expr(new IsProcedure(ps[0]));
            case E_NULLQ: if (ps.size()!=1) throw RuntimeError("null? requires 1"); return Expr(new IsNull(ps[0]));
            case E_EXIT: if (stxs.size()!=1) throw RuntimeError("exit takes no args"); return Expr(new Exit());
            case E_DISPLAY: if (ps.size()!=1) throw RuntimeError("display requires 1"); return Expr(new Display(ps[0]));
            case E_NOT: if (ps.size()!=1) throw RuntimeError("not requires 1"); return Expr(new Not(ps[0]));
            default: throw RuntimeError("unknown primitive op " + op);
        }
    }

    {
        Expr rator = stxs[0].parse(env);
        vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); ++i)
            args.push_back(stxs[i].parse(env));
        return Expr(new Apply(rator, args));
    }
}
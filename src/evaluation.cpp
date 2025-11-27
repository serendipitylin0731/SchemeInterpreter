/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>
#include <memory>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> args;
    for (auto &expr : rands) {
        args.push_back(expr->eval(e));
    }
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    if (!x.empty()) {
        char first = x[0];
        if (isdigit(first) || first == '.' || first == '@')
            throw RuntimeError("Invalid variable name: starts with digit or {.@}");
    }

    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
             static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                    {E_VOID,     {new MakeVoid(), {}}},
                    {E_EXIT,     {new Exit(), {}}},
                    {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                    {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                    {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                    {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                    {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                    {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                    {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                    {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                    {E_PLUS,     {new PlusVar({}),  {}}},
                    {E_MINUS,    {new MinusVar({}), {}}},
                    {E_MUL,      {new MultVar({}),  {}}},
                    {E_DIV,      {new DivVar({}),   {}}},
                    {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EQ,       {new EqualVar({}), {}}},
                    {E_LT,       {new LessVar({}), {}}},
                    {E_LE,       {new LessEqVar({}), {}}},
                    {E_GT,       {new GreaterVar({}), {}}},
                    {E_GE,       {new GreaterEqVar({}), {}}},
                    {E_AND,      {new AndVar({}), {}}},
                    {E_OR,       {new OrVar({}), {}}},
                    {E_NOT,      {new Not(new Var("parm")), {"parm"}}},
                    {E_CONS,     {new Cons(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_CAR,      {new Car(new Var("parm")), {"parm"}}},
                    {E_CDR,      {new Cdr(new Var("parm")), {"parm"}}},
                    {E_LIST,     {new ListFunc({}), {}}},
                    {E_LISTQ,    {new IsList(new Var("parm")), {"parm"}}},
            };

            auto it = primitive_map.find(primitives[x]);
            if (it != primitive_map.end()) {
                const auto &pair = it->second;
                const Expr &expr = pair.first;
                const std::vector<std::string> &params = pair.second;
                bool is_variadic = false;
                if (dynamic_cast<PlusVar*>(expr.get()) || 
                    dynamic_cast<MinusVar*>(expr.get()) ||
                    dynamic_cast<MultVar*>(expr.get()) ||
                    dynamic_cast<DivVar*>(expr.get()) ||
                    dynamic_cast<EqualVar*>(expr.get()) ||
                    dynamic_cast<LessVar*>(expr.get()) ||
                    dynamic_cast<LessEqVar*>(expr.get()) ||
                    dynamic_cast<GreaterVar*>(expr.get()) ||
                    dynamic_cast<GreaterEqVar*>(expr.get()) ||
                    dynamic_cast<AndVar*>(expr.get()) ||
                    dynamic_cast<OrVar*>(expr.get()) ||
                    dynamic_cast<ListFunc*>(expr.get())) {
                    is_variadic = true;
                }
                
                return Value(new Procedure(params, expr, e, is_variadic));
            }
      }
      throw RuntimeError("Undefined variable: " + x);
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    auto p1 = rand1.ptr, p2 = rand2.ptr;
    if (p1->v_type == V_INT && p2->v_type == V_INT)
        return IntegerV(static_cast<Integer*>(p1.get())->n + static_cast<Integer*>(p2.get())->n);
    if (p1->v_type == V_RATIONAL && p2->v_type == V_RATIONAL) {
        int a = static_cast<Rational*>(p1.get())->numerator;
        int b = static_cast<Rational*>(p1.get())->denominator;
        int c = static_cast<Rational*>(p2.get())->numerator;
        int d = static_cast<Rational*>(p2.get())->denominator;
        return RationalV(a * d + b * c, b * d);
    }
    throw(RuntimeError("Wrong typename for +"));
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    auto p1 = rand1.ptr, p2 = rand2.ptr;
    if (p1->v_type == V_INT && p2->v_type == V_INT)
        return IntegerV(static_cast<Integer*>(p1.get())->n - static_cast<Integer*>(p2.get())->n);
    if (p1->v_type == V_RATIONAL && p2->v_type == V_RATIONAL) {
        int a = static_cast<Rational*>(p1.get())->numerator;
        int b = static_cast<Rational*>(p1.get())->denominator;
        int c = static_cast<Rational*>(p2.get())->numerator;
        int d = static_cast<Rational*>(p2.get())->denominator;
        return RationalV(a * d - b * c, b * d);
    }
    throw(RuntimeError("Wrong typename for -"));
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    auto p1 = rand1.ptr, p2 = rand2.ptr;
    if (p1->v_type == V_INT && p2->v_type == V_INT)
        return IntegerV(static_cast<Integer*>(p1.get())->n * static_cast<Integer*>(p2.get())->n);
    if (p1->v_type == V_RATIONAL && p2->v_type == V_RATIONAL) {
        int a = static_cast<Rational*>(p1.get())->numerator;
        int b = static_cast<Rational*>(p1.get())->denominator;
        int c = static_cast<Rational*>(p2.get())->numerator;
        int d = static_cast<Rational*>(p2.get())->denominator;
        return RationalV(a * c, b * d);
    }
    throw(RuntimeError("Wrong typename for *"));
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    auto p1 = rand1.ptr, p2 = rand2.ptr;
    if (p1->v_type == V_INT && p2->v_type == V_INT) {
        int n2 = static_cast<Integer*>(p2.get())->n;
        if (n2 == 0) throw(RuntimeError("Division by zero"));
        return RationalV(static_cast<Integer*>(p1.get())->n, n2);
    }
    if (p1->v_type == V_RATIONAL && p2->v_type == V_RATIONAL) {
        int a = static_cast<Rational*>(p1.get())->numerator;
        int b = static_cast<Rational*>(p1.get())->denominator;
        int c = static_cast<Rational*>(p2.get())->numerator;
        int d = static_cast<Rational*>(p2.get())->denominator;
        if (c == 0) throw(RuntimeError("Division by zero"));
        return RationalV(a * d, b * c);
    }
    throw(RuntimeError("Wrong typename for /"));
}


Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    if (args.empty()) return IntegerV(0);
    bool hasRational = false;
    for (auto &v : args) {
        if (v.ptr->v_type != V_INT && v.ptr->v_type != V_RATIONAL)
            throw(RuntimeError("Wrong typename for +"));
        if (v.ptr->v_type == V_RATIONAL) hasRational = true;
    }

    if (!hasRational) {
        int sum = 0;
        for (auto &v : args)
            sum += static_cast<Integer*>(v.ptr.get())->n;
        return IntegerV(sum);
    } else {
        int num = 0, den = 1;
        for (auto &v : args) {
            if (v.ptr->v_type == V_INT) {
                num = num * 1 + den * static_cast<Integer*>(v.ptr.get())->n;
            } else {
                int a = static_cast<Rational*>(v.ptr.get())->numerator;
                int b = static_cast<Rational*>(v.ptr.get())->denominator;
                num = num * b + den * a;
                den *= b;
            }
        }
        return RationalV(num, den);
    }
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.empty()) throw(RuntimeError("(-) requires at least one argument"));
    bool hasRational = false;
    for (auto &v : args) {
        if (v.ptr->v_type != V_INT && v.ptr->v_type != V_RATIONAL)
            throw(RuntimeError("Wrong typename for -"));
        if (v.ptr->v_type == V_RATIONAL) hasRational = true;
    }

    if (!hasRational) {
        int res = static_cast<Integer*>(args[0].ptr.get())->n;
        if (args.size() == 1)
            return IntegerV(-res);
        for (size_t i = 1; i < args.size(); ++i)
            res -= static_cast<Integer*>(args[i].ptr.get())->n;
        return IntegerV(res);
    } else {
        int num, den;
        if (args[0].ptr->v_type == V_INT) { num = static_cast<Integer*>(args[0].ptr.get())->n; den = 1; }
        else { num = static_cast<Rational*>(args[0].ptr.get())->numerator; den = static_cast<Rational*>(args[0].ptr.get())->denominator; }

        if (args.size() == 1) return RationalV(-num, den);

        for (size_t i = 1; i < args.size(); ++i) {
            int a, b;
            if (args[i].ptr->v_type == V_INT) { a = static_cast<Integer*>(args[i].ptr.get())->n; b = 1; }
            else { a = static_cast<Rational*>(args[i].ptr.get())->numerator; b = static_cast<Rational*>(args[i].ptr.get())->denominator; }
            num = num * b - den * a;
            den *= b;
        }
        return RationalV(num, den);
    }
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    if (args.empty()) return IntegerV(1);
    bool hasRational = false;
    for (auto &v : args) {
        if (v.ptr->v_type != V_INT && v.ptr->v_type != V_RATIONAL)
            throw(RuntimeError("Wrong typename for *"));
        if (v.ptr->v_type == V_RATIONAL) hasRational = true;
    }

    if (!hasRational) {
        int res = 1;
        for (auto &v : args)
            res *= static_cast<Integer*>(v.ptr.get())->n;
        return IntegerV(res);
    } else {
        int num = 1, den = 1;
        for (auto &v : args) {
            if (v.ptr->v_type == V_INT) {
                num *= static_cast<Integer*>(v.ptr.get())->n;
            } else {
                num *= static_cast<Rational*>(v.ptr.get())->numerator;
                den *= static_cast<Rational*>(v.ptr.get())->denominator;
            }
        }
        return RationalV(num, den);
    }
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.empty()) throw(RuntimeError("(/) requires at least one argument"));
    bool hasRational = false;
    for (auto &v : args) {
        if (v.ptr->v_type != V_INT && v.ptr->v_type != V_RATIONAL)
            throw(RuntimeError("Wrong typename for /"));
        if (v.ptr->v_type == V_RATIONAL) hasRational = true;
    }

    int num, den;
    if (args[0].ptr->v_type == V_INT) { num = static_cast<Integer*>(args[0].ptr.get())->n; den = 1; }
    else { num = static_cast<Rational*>(args[0].ptr.get())->numerator; den = static_cast<Rational*>(args[0].ptr.get())->denominator; }

    if (args.size() == 1) {
        if (num == 0) throw(RuntimeError("Division by zero"));
        return RationalV(den, num);
    }

    for (size_t i = 1; i < args.size(); ++i) {
        int a, b;
        if (args[i].ptr->v_type == V_INT) { a = static_cast<Integer*>(args[i].ptr.get())->n; b = 1; }
        else { a = static_cast<Rational*>(args[i].ptr.get())->numerator; b = static_cast<Rational*>(args[i].ptr.get())->denominator; }
        if (a == 0) throw(RuntimeError("Division by zero"));
        num *= b;
        den *= a;
    }
    return RationalV(num, den);
}


Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    int cmp = compareNumericValues(rand1, rand2);
    return BooleanV(cmp < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    int cmp = compareNumericValues(rand1, rand2);
    return BooleanV(cmp <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    int cmp = compareNumericValues(rand1, rand2);
    return BooleanV(cmp == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    int cmp = compareNumericValues(rand1, rand2);
    return BooleanV(cmp >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    int cmp = compareNumericValues(rand1, rand2);
    return BooleanV(cmp > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    if (args.size() < 2)
        throw RuntimeError("< expects at least two arguments");
    for (size_t i = 1; i < args.size(); ++i) {
        if (!(compareNumericValues(args[i - 1], args[i]) < 0))
            return BooleanV(false);
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    if (args.size() < 2)
        throw RuntimeError("<= expects at least two arguments");
    for (size_t i = 1; i < args.size(); ++i) {
        if (!(compareNumericValues(args[i - 1], args[i]) <= 0))
            return BooleanV(false);
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    if (args.size() < 2)
        throw RuntimeError("= expects at least two arguments");
    for (size_t i = 1; i < args.size(); ++i) {
        if (!(compareNumericValues(args[i - 1], args[i]) == 0))
            return BooleanV(false);
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    if (args.size() < 2)
        throw RuntimeError(">= expects at least two arguments");
    for (size_t i = 1; i < args.size(); ++i) {
        if (!(compareNumericValues(args[i - 1], args[i]) >= 0))
            return BooleanV(false);
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    if (args.size() < 2)
        throw RuntimeError("> expects at least two arguments");
    for (size_t i = 1; i < args.size(); ++i) {
        if (!(compareNumericValues(args[i - 1], args[i]) > 0))
            return BooleanV(false);
    }
    return BooleanV(true);
}


Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
     Value result = NullV();
    for (auto it = args.rbegin(); it != args.rend(); ++it) {
        result = PairV(*it, result);
    }
    return result;
}

Value IsList::evalRator(const Value &rand) { // list?
     Value current = rand;

    while (true) {
        if (dynamic_cast<Null*>(current.ptr.get()) != nullptr)
            return BooleanV(true);
        else if (dynamic_cast<Pair*>(current.ptr.get()) != nullptr)
            current = dynamic_cast<Pair*>(current.ptr.get())->cdr;
        else
            return BooleanV(false);
    }
}

Value Car::evalRator(const Value &rand) { // car
    auto p = dynamic_cast<Pair*>(rand.ptr.get());
    if (!p)
        throw RuntimeError("car: argument is not a pair");
    return p->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    auto p = dynamic_cast<Pair*>(rand.ptr.get());
    if (!p)
        throw RuntimeError("cdr: argument is not a pair");
    return p->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    auto p = dynamic_cast<Pair*>(rand1.ptr.get());
    if (!p)
        throw RuntimeError("set-car!: argument is not a pair");
    p->car = rand2;
    return VoidV(); 
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
   auto p = dynamic_cast<Pair*>(rand1.ptr.get());
    if (!p)
        throw RuntimeError("set-cdr!: argument is not a pair");
    p->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // 检查类型是否为 Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // 检查类型是否为 Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // 检查类型是否为 Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // 检查类型是否为 Null 或 Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}
//
Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    Value result = VoidV();
    for (auto &expr : es)
        result = expr->eval(e);
    return result;
}

static Value buildListFromSyntax(const std::vector<Syntax> &stxs, size_t start);

static Value syntaxToValue(const Syntax &syn) {
    SyntaxBase *base = syn.get();
    if (auto num = dynamic_cast<Number*>(base)) {
        return IntegerV(num->n);
    }
    if (auto rat = dynamic_cast<RationalSyntax*>(base)) {
        return RationalV(rat->numerator, rat->denominator);
    }
    if (dynamic_cast<TrueSyntax*>(base)) {
        return BooleanV(true);
    }
    if (dynamic_cast<FalseSyntax*>(base)) {
        return BooleanV(false);
    }
    if (auto str = dynamic_cast<StringSyntax*>(base)) {
        return StringV(str->s);
    }
    if (auto sym = dynamic_cast<SymbolSyntax*>(base)) {
        return SymbolV(sym->s);
    }
    if (auto list = dynamic_cast<List*>(base)) {
        if (list->stxs.empty())
            return NullV();
        
        // 递归构建列表，处理点对表示法
        return buildListFromSyntax(list->stxs, 0);
    }
    return VoidV();
}

// 辅助函数：递归构建列表，处理点对
static Value buildListFromSyntax(const std::vector<Syntax> &stxs, size_t start) {
    if (start >= stxs.size()) {
        return NullV();
    }
    
    // 只在特定的语法模式下检查点对表示法
    // 对于 quote 内部的列表，应该更保守地处理点对
    if (start + 2 < stxs.size()) {
        if (auto dotSym = dynamic_cast<SymbolSyntax*>(stxs[start + 1].ptr.get())) {
            if (dotSym->s == ".") {
                // 只有在明确的点对语法时才创建点对
                // 检查是否是有效的点对格式 (a . b)
                Value car = syntaxToValue(stxs[start]);
                Value cdr = syntaxToValue(stxs[start + 2]);
                
                // 如果后面没有更多元素，才是真正的点对
                if (start + 3 == stxs.size()) {
                    return PairV(car, cdr);
                }
            }
        }
    }
    
    // 普通列表：递归构建
    Value car = syntaxToValue(stxs[start]);
    Value cdr = buildListFromSyntax(stxs, start + 1);
    return PairV(car, cdr);
}


Value Quote::eval(Assoc& e) {
    return syntaxToValue(s);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    if (rands.empty()) return BooleanV(true);
    for (size_t i = 0; i < rands.size(); ++i) {
        Value v = rands[i]->eval(e);
        if (v->v_type == ValueType::V_BOOL && !((Boolean*)v.get())->b) {
            return BooleanV(false);  // 遇到 #f 立即返回
        }
    }
    return rands.back()->eval(e);  // 返回最后一个值
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    if (rands.empty()) return BooleanV(false);
    for (size_t i = 0; i < rands.size(); ++i) {
        Value v = rands[i]->eval(e);
        if (v->v_type != ValueType::V_BOOL || ((Boolean*)v.get())->b) {
            return v;  // 返回第一个真值
        }
    }
    return BooleanV(false);  // 所有值都是假值，返回 #f
}

Value Not::evalRator(const Value &rand) { // not
    if (rand->v_type == ValueType::V_BOOL)
        return BooleanV(!((Boolean*)rand.get())->b);
    return BooleanV(false);
}

Value If::eval(Assoc &e) {
    Value condVal = cond->eval(e);
    bool truthy = true;
    if (condVal->v_type == ValueType::V_BOOL)
        truthy = ((Boolean*)condVal.get())->b;
    return truthy ? conseq->eval(e) : alter->eval(e);
}

Value Cond::eval(Assoc &env) {
    for (auto &clause : clauses) {
        if (clause.empty()) continue;
        bool isElse = false;
        if (auto varNode = dynamic_cast<Var*>(clause[0].get())) {
            if (varNode->x == "else") {
                isElse = true;
            }
        }
        if (isElse ||
            (clause[0]->eval(env)->v_type == ValueType::V_BOOL &&
             ((Boolean*)clause[0]->eval(env).get())->b) ||
            (clause[0]->eval(env)->v_type != ValueType::V_BOOL)) {
            Value result = VoidV();
            for (size_t i = 1; i < clause.size(); ++i) {
                result = clause[i]->eval(env);
            }
            return result;
        }
    }
    return VoidV();
}

Value Lambda::eval(Assoc &env) { 
    return Value(new Procedure(x, e, env, is_variadic));
}

Value Apply::eval(Assoc &e) {
    Value proc_val = rator->eval(e);
    
    // 处理用户定义的过程
    if (proc_val->v_type == V_PROC) {
        Procedure* clos_ptr = dynamic_cast<Procedure*>(proc_val.get());
        if (!clos_ptr) throw RuntimeError("Invalid procedure closure");
        
        // 检查是否是原始过程包装的 Procedure
        if (auto prim_proc = dynamic_cast<Variadic*>(clos_ptr->e.get())) {
            std::vector<Value> args;
            for (auto &arg_expr : rand) {
                args.push_back(arg_expr->eval(e));
            }
            return prim_proc->evalRator(args);
        }
        
        if (auto bin_proc = dynamic_cast<Binary*>(clos_ptr->e.get())) {
            if (rand.size() != 2) {
                throw RuntimeError("Binary procedure expects 2 arguments, got " + std::to_string(rand.size()));
            }
            Value arg1 = rand[0]->eval(e);
            Value arg2 = rand[1]->eval(e);
            return bin_proc->evalRator(arg1, arg2);
        }
        
        if (auto unary_proc = dynamic_cast<Unary*>(clos_ptr->e.get())) {
            if (rand.size() != 1) {
                throw RuntimeError("Unary procedure expects 1 argument, got " + std::to_string(rand.size()));
            }
            Value arg = rand[0]->eval(e);
            return unary_proc->evalRator(arg);
        }
        
        // 处理普通用户定义过程
        std::vector<Value> args;
        for (auto &arg_expr : rand) {
            args.push_back(arg_expr->eval(e));
        }

        Assoc param_env = clos_ptr->env;
        size_t fixed_param_count = clos_ptr->parameters.size();
        bool is_variadic = clos_ptr->is_variadic;

        // 参数数量检查
        if (!is_variadic && args.size() != fixed_param_count) {
            throw RuntimeError("Argument count mismatch: expected " + 
                              std::to_string(fixed_param_count) + 
                              ", got " + std::to_string(args.size()));
        }
        if (is_variadic && args.size() < fixed_param_count) {
            throw RuntimeError("Argument count mismatch: expected at least " + 
                              std::to_string(fixed_param_count) + 
                              ", got " + std::to_string(args.size()));
        }

        // 绑定固定参数
        for (size_t i = 0; i < fixed_param_count; ++i) {
            param_env = extend(clos_ptr->parameters[i], args[i], param_env);
        }

        // 处理可变参数
        if (is_variadic) {
            std::vector<Value> var_args;
            for (size_t i = fixed_param_count; i < args.size(); ++i) {
                var_args.push_back(args[i]);
            }

            Value var_list = NullV();
            for (auto it = var_args.rbegin(); it != var_args.rend(); ++it) {
                var_list = PairV(*it, var_list);
            }

            if (!clos_ptr->parameters.empty()) {
                std::string var_param_name = clos_ptr->parameters.back();
                param_env = extend(var_param_name, var_list, param_env);
            }
        }
        
        return clos_ptr->e->eval(param_env);
    }
    
    throw RuntimeError("Attempt to apply a non-procedure");
}

Value Define::eval(Assoc &env) {
    Value val = e->eval(env);
    modify(var, val, env);
    return VoidV();
}

Value Let::eval(Assoc &env) {
    Assoc let_env = env;
    for (auto &binding : bind) {
        Value val = binding.second->eval(env);
        let_env = extend(binding.first, val, let_env);
    }
    return body->eval(let_env);
}

Value Letrec::eval(Assoc &env) {
    Assoc let_env = env;
    for (auto &binding : bind) {
        let_env = extend(binding.first, VoidV(), let_env);
    }
    for (auto &binding : bind) {
        Value val = binding.second->eval(let_env);
        modify(binding.first, val, let_env);
    }
    return body->eval(let_env);
}

Value Set::eval(Assoc &env) {
    Value val = e->eval(env);
    modify(var, val, env);
    return val;
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }

    return VoidV();
}
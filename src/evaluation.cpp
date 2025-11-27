/**
 * @file evaluation.cpp  
 * @brief Expression evaluation implementation for Scheme interpreter
 * @brief 实现Scheme解释器中所有表达式的求值逻辑
 */

#include "value.hpp"
#include "expr.hpp"
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) {
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) {
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) {
    return StringV(s);
}

Value True::eval(Assoc &e) {
    return BooleanV(true);
}

Value False::eval(Assoc &e) {
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) {
    return VoidV();
}

Value Exit::eval(Assoc &e) {
    return TerminateV();
}

Value Unary::eval(Assoc &e) {
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) {
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) {
    std::vector<Value> args;
    for (const auto& r : rands) {
        args.push_back(r->eval(e));
    }
    return evalRator(args);
}

Value Var::eval(Assoc &e) {
    if ((x.empty()) || (std::isdigit(x[0]) || x[0] == '.' || x[0] == '@')) 
        throw RuntimeError("Malformed variable identifier");
    
    for (int i = 0; i < x.size(); i++) {
        if (x[i] == '#') {
            throw(RuntimeError("unbound variable"));
        }
    }

    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
            Expr exp = nullptr;
            int type_name = primitives[x];
            switch (type_name) {
                case E_MUL: { exp = (new MultVar({})); break; }
                case E_MINUS: { exp = (new MinusVar({})); break; }
                case E_PLUS: { exp = (new PlusVar({})); break; }
                case E_DIV: { exp = (new DivVar({})); break; }
                case E_MODULO: { exp = (new Modulo(new Var("parm1"), new Var("parm2"))); break; }
                case E_LT: { exp = (new LessVar({})); break; }
                case E_LE: { exp = (new LessEqVar({})); break; }
                case E_EQ: { exp = (new EqualVar({})); break; }
                case E_GE: { exp = (new GreaterEqVar({})); break; }
                case E_GT: { exp = (new GreaterVar({})); break; }
                case E_VOID: { exp = (new MakeVoid()); break; }
                case E_EQQ: { exp = (new IsEq(new Var("parm1"), new Var("parm2"))); break; }
                case E_BOOLQ: { exp = (new IsBoolean(new Var("parm"))); break; }
                case E_INTQ: { exp = (new IsFixnum(new Var("parm"))); break; }
                case E_NULLQ: { exp = (new IsNull(new Var("parm"))); break; }
                case E_PAIRQ: { exp = (new IsPair(new Var("parm"))); break; }
                case E_PROCQ: { exp = (new IsProcedure(new Var("parm"))); break; }
                case E_LISTQ: { exp = (new IsList(new Var("parm"))); break; }
                case E_SYMBOLQ: { exp = (new IsSymbol(new Var("parm"))); break; }
                case E_STRINGQ: { exp = (new IsString(new Var("parm"))); break; }
                case E_CONS: { exp = (new Cons(new Var("parm1"), new Var("parm2"))); break; }
                case E_EXPT: { exp = (new Expt(new Var("parm1"), new Var("parm2"))); break; }
                case E_NOT: { exp = (new Not(new Var("parm"))); break; }
                case E_CAR: { exp = (new Car(new Var("parm"))); break; }
                case E_CDR: { exp = (new Cdr(new Var("parm"))); break; }
                case E_SETCAR: { exp = (new SetCar(new Var("parm1"), new Var("parm2"))); break; }
                case E_SETCDR: { exp = (new SetCdr(new Var("parm1"), new Var("parm2"))); break; }
                case E_DISPLAY: { exp = (new Display(new Var("parm"))); break; }
                case E_EXIT: { exp = (new Exit()); break; }
                case E_AND: { exp = (new AndVar({})); break; }
                case E_OR: { exp = (new OrVar({})); break; }
                case E_LIST: { exp = (new ListFunc({})); break; }
            }
            
            std::vector<std::string> parameters_;
            
            // 处理可变参数操作符
            if (dynamic_cast<PlusVar*>(exp.get()) != nullptr ||
                dynamic_cast<MinusVar*>(exp.get()) != nullptr ||
                dynamic_cast<MultVar*>(exp.get()) != nullptr ||
                dynamic_cast<DivVar*>(exp.get()) != nullptr ||
                dynamic_cast<LessVar*>(exp.get()) != nullptr ||
                dynamic_cast<LessEqVar*>(exp.get()) != nullptr ||
                dynamic_cast<EqualVar*>(exp.get()) != nullptr ||
                dynamic_cast<GreaterEqVar*>(exp.get()) != nullptr ||
                dynamic_cast<GreaterVar*>(exp.get()) != nullptr ||
                dynamic_cast<AndVar*>(exp.get()) != nullptr ||
                dynamic_cast<OrVar*>(exp.get()) != nullptr ||
                dynamic_cast<ListFunc*>(exp.get()) != nullptr) {
                // 可变参数操作符：使用单个参数名表示可变参数
                parameters_.push_back("args");
            }
            // 处理二元操作符
            else if (dynamic_cast<Binary*>(exp.get())) {
                parameters_.push_back("parm1");
                parameters_.push_back("parm2");
            } 
            // 处理一元操作符
            else if (dynamic_cast<Unary*>(exp.get())) {
                parameters_.push_back("parm");
            }
            // 处理无参数操作符（如 void, exit）
            else {
                // 无参数操作符
                parameters_ = std::vector<std::string>();
            }
            
            return ProcedureV(parameters_, exp, e);
        } else {
            throw(RuntimeError("unbound variable"));
        }
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return IntegerV((dynamic_cast<Integer*>(rand1.get())->n) + (dynamic_cast<Integer*>(rand2.get())->n));
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return RationalV(r1->numerator + n2 * r1->denominator, r1->denominator);
    }
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        return RationalV(n1 * r2->denominator + r2->numerator, r2->denominator);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int result_num = r1->numerator * r2->denominator + r2->numerator * r1->denominator;
        int result_den = r1->denominator * r2->denominator;
        if (result_den < 0) {
            result_num = -result_num;
            result_den = -result_den;
        }
        return RationalV(result_num, result_den);
    }
    throw(RuntimeError("Type mismatch in addition"));
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return IntegerV((dynamic_cast<Integer*>(rand1.get())->n) - (dynamic_cast<Integer*>(rand2.get())->n));
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return RationalV(r1->numerator - n2 * r1->denominator, r1->denominator);
    }
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        return RationalV(n1 * r2->denominator - r2->numerator, r2->denominator);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int result_num = r1->numerator * r2->denominator - r2->numerator * r1->denominator;
        int result_den = r1->denominator * r2->denominator;
        if (result_den < 0) {
            result_num = -result_num;
            result_den = -result_den;
        }
        return RationalV(result_num, result_den);
    }
    throw(RuntimeError("Type mismatch in subtraction"));
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return IntegerV((dynamic_cast<Integer*>(rand1.get())->n) * (dynamic_cast<Integer*>(rand2.get())->n));
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return RationalV(r1->numerator * n2, r1->denominator);
    }
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        return RationalV(n1 * r2->numerator, r2->denominator);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int result_num = r1->numerator * r2->numerator;
        int result_den = r1->denominator * r2->denominator;
        if (result_den < 0) {
            result_num = -result_num;
            result_den = -result_den;
        }
        return RationalV(result_num, result_den);
    }
    throw(RuntimeError("Type mismatch in multiplication"));
}

Value Div::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        if (divisor < 0) {
            dividend = -dividend;
            divisor = -divisor;
        }
        return RationalV(dividend, divisor);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        if (n2 == 0) {
            throw(RuntimeError("Division by zero"));
        }
        int result_num = r1->numerator;
        int result_den = r1->denominator * n2;
        if (result_den < 0) {
            result_num = -result_num;
            result_den = -result_den;
        }
        return RationalV(result_num, result_den);
    }
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->numerator == 0) {
            throw(RuntimeError("Division by zero"));
        }
        int result_num = n1 * r2->denominator;
        int result_den = r2->numerator;
        if (result_den < 0) {
            result_num = -result_num;
            result_den = -result_den;
        }
        return RationalV(result_num, result_den);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->numerator == 0) {
            throw(RuntimeError("Division by zero"));
        }
        int result_num = r1->numerator * r2->denominator;
        int result_den = r1->denominator * r2->numerator;
        if (result_den < 0) {
            result_num = -result_num;
            result_den = -result_den;
        }
        return RationalV(result_num, result_den);
    }
    throw(RuntimeError("Type mismatch in division"));
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) {
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

Value PlusVar::evalRator(const std::vector<Value> &args) {
    if (args.empty()) {
        return IntegerV(0);
    }
    
    bool has_rational = false;
    for (const auto& arg : args) {
        if (arg->v_type == V_RATIONAL) {
            has_rational = true;
            break;
        } else if (arg->v_type != V_INT) {
            throw(RuntimeError("Type error in variadic addition"));
        }
    }
    
    if (has_rational) {
        int total_num = 0, total_den = 1;
        for (const auto& arg : args) {
            if (arg->v_type == V_INT) {
                int n_val = dynamic_cast<Integer*>(arg.get())->n;
                total_num = total_num + n_val * total_den;
            } else if (arg->v_type == V_RATIONAL) {
                Rational* rat = dynamic_cast<Rational*>(arg.get());
                total_num = total_num * rat->denominator + rat->numerator * total_den;
                total_den = total_den * rat->denominator;
            }
        }
        return RationalV(total_num, total_den);
    } else {
        int sum_result = 0;
        for (const auto& arg : args) {
            sum_result += dynamic_cast<Integer*>(arg.get())->n;
        }
        return IntegerV(sum_result);
    }
}

Value MinusVar::evalRator(const std::vector<Value> &args) {
    if (args.empty()) {
        throw(RuntimeError("Wrong number of arguments for -"));
    }
    if (args.size() == 1) {
        if (args[0]->v_type == V_INT) {
            return IntegerV(-(dynamic_cast<Integer*>(args[0].get())->n));
        } else if (args[0]->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(args[0].get());
            return RationalV(-(r->numerator), r->denominator);
        } else {
            throw(RuntimeError("Type error in negation"));
        }
    }
    
    bool has_rational = false;
    for (const auto& arg : args) {
        if (arg->v_type == V_RATIONAL) {
            has_rational = true;
            break;
        } else if (arg->v_type != V_INT) {
            throw(RuntimeError("Type error in variadic subtraction"));
        }
    }
    
    if (has_rational) {
        int num, den;
        
        if (args[0]->v_type == V_INT) {
            num = dynamic_cast<Integer*>(args[0].get())->n;
            den = 1;
        } else {
            Rational* r = dynamic_cast<Rational*>(args[0].get());
            num = r->numerator;
            den = r->denominator;
        }
        
        for (size_t i = 1; i < args.size(); i++) {
            if (args[i]->v_type == V_INT) {
                int n = dynamic_cast<Integer*>(args[i].get())->n;
                num = num - n * den;
            } else if (args[i]->v_type == V_RATIONAL) {
                Rational* r = dynamic_cast<Rational*>(args[i].get());
                num = num * r->denominator - r->numerator * den;
                den = den * r->denominator;
            }
        }
        return RationalV(num, den);
    } else {
        int result = dynamic_cast<Integer*>(args[0].get())->n;
        for (size_t i = 1; i < args.size(); i++) {
            result -= dynamic_cast<Integer*>(args[i].get())->n;
        }
        return IntegerV(result);
    }
}

Value MultVar::evalRator(const std::vector<Value> &args) {
    if (args.empty()) {
        return IntegerV(1);
    }
    
    bool has_rational = false;
    for (const auto& arg : args) {
        if (arg->v_type == V_RATIONAL) {
            has_rational = true;
            break;
        } else if (arg->v_type != V_INT) {
            throw(RuntimeError("Type error in variadic multiplication"));
        }
    }
    
    if (has_rational) {
        int num = 1, den = 1;
        for (const auto& arg : args) {
            if (arg->v_type == V_INT) {
                num *= dynamic_cast<Integer*>(arg.get())->n;
            } else if (arg->v_type == V_RATIONAL) {
                Rational* r = dynamic_cast<Rational*>(arg.get());
                num *= r->numerator;
                den *= r->denominator;
            }
        }
        return RationalV(num, den);
    } else {
        int result = 1;
        for (const auto& arg : args) {
            result *= dynamic_cast<Integer*>(arg.get())->n;
        }
        return IntegerV(result);
    }
}

static int gcd_helper(int a, int b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        int temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

static Value multiply_rationals(int num1, int den1, int num2, int den2) {
    int new_num = num1 * num2;
    int new_den = den1 * den2;
    int g = gcd_helper(new_num, new_den);
    new_num /= g;
    new_den /= g;
    if (new_den < 0) {
        new_num = -new_num;
        new_den = -new_den;
    }
    return RationalV(new_num, new_den);
}

Value DivVar::evalRator(const std::vector<Value> &args) {
    if (args.empty()) {
        throw(RuntimeError("Wrong number of arguments for /"));
    }
    if (args.size() == 1) {
        if (args[0]->v_type == V_INT) {
            int n = dynamic_cast<Integer*>(args[0].get())->n;
            if (n == 0) throw(RuntimeError("Division by zero"));
            return RationalV(1, n);
        } else if (args[0]->v_type == V_RATIONAL) {
            auto rat = dynamic_cast<Rational*>(args[0].get());
            if (rat->numerator == 0) throw(RuntimeError("Division by zero"));
            return RationalV(rat->denominator, rat->numerator);
        } else {
            throw(RuntimeError("Type error in reciprocal"));
        }
    }
    
    int num, den;
    if (args[0]->v_type == V_INT) {
        num = dynamic_cast<Integer*>(args[0].get())->n;
        den = 1;
    } else if (args[0]->v_type == V_RATIONAL) {
        auto rat = dynamic_cast<Rational*>(args[0].get());
        num = rat->numerator;
        den = rat->denominator;
    } else {
        throw(RuntimeError("Type error in division"));
    }
    
    for (size_t i = 1; i < args.size(); i++) {
        if (args[i]->v_type == V_INT) {
            int divisor = dynamic_cast<Integer*>(args[i].get())->n;
            if (divisor == 0) throw(RuntimeError("Division by zero"));
            
            int g1 = gcd_helper(abs(num), abs(divisor));
            if (g1 > 1) {
                num /= g1;
                divisor /= g1;
            }
            den *= divisor;
        } else if (args[i]->v_type == V_RATIONAL) {
            auto rat = dynamic_cast<Rational*>(args[i].get());
            if (rat->numerator == 0) throw(RuntimeError("Division by zero"));
            
            int g1 = gcd_helper(abs(num), abs(rat->numerator));
            int g2 = gcd_helper(abs(den), abs(rat->denominator));
            
            if (g1 > 1) {
                num /= g1;
                int temp_rat_num = rat->numerator / g1;
                den *= temp_rat_num;
            } else {
                den *= rat->numerator;
            }
            
            if (g2 > 1) {
                den /= g2;
                int temp_rat_den = rat->denominator / g2;
                num *= temp_rat_den;
            } else {
                num *= rat->denominator;
            }
        } else {
            throw(RuntimeError("Type error in division"));
        }
    }
    
    int g = gcd_helper(abs(num), abs(den));
    if (g > 1) {
        num /= g;
        den /= g;
    }
    
    if (den < 0) {
        num = -num;
        den = -den;
    }
    
    if (den == 1) {
        return IntegerV(num);
    }
    
    return RationalV(num, den);
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type == V_INT and rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        int result = 1;
        int b = base;
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
    throw(RuntimeError("Type error in exponentiation"));
}

int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = (int)r1->numerator;
        int right = (int)n2 * r1->denominator;
        if (r1->denominator < 0) {
            left = -left;
            right = -right;
        }
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = (int)n1 * r2->denominator;
        int right = (int)r2->numerator;
        if (r2->denominator < 0) {
            left = -left;
            right = -right;
        }
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = (int)r1->numerator * r2->denominator;
        int right = (int)r2->numerator * r1->denominator;
        if (r1->denominator < 0) left = -left;
        if (r2->denominator < 0) right = -right;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Type error in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) {
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) <= (dynamic_cast<Integer*>(rand2.get())->n));
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        if (r1->denominator > 0) {
            return BooleanV(r1->numerator <= n2 * r1->denominator);
        } else {
            return BooleanV(r1->numerator >= n2 * r1->denominator);
        }
    }
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->denominator > 0) {
            return BooleanV(n1 * r2->denominator <= r2->numerator);
        } else {
            return BooleanV(n1 * r2->denominator >= r2->numerator);
        }
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        return BooleanV(compareNumericValues(rand1, rand2) <= 0);
    }
    throw(RuntimeError("Type error in less than or equal comparison"));
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) {
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) {
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) {
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) {
    if (args.size() < 2) {
        throw(RuntimeError("< requires at least 2 arguments"));
    }
    
    for (size_t i = 0; i < args.size() - 1; i++) {
        if ((args[i]->v_type != V_INT && args[i]->v_type != V_RATIONAL) || 
            (args[i+1]->v_type != V_INT && args[i+1]->v_type != V_RATIONAL)) {
            throw(RuntimeError("Type error in variadic less than"));
        }
        if (compareNumericValues(args[i], args[i+1]) >= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) {
    if (args.size() < 2) {
        throw(RuntimeError("<= requires at least 2 arguments"));
    }
    
    for (size_t i = 0; i < args.size() - 1; i++) {
        if ((args[i]->v_type != V_INT && args[i]->v_type != V_RATIONAL) || 
            (args[i+1]->v_type != V_INT && args[i+1]->v_type != V_RATIONAL)) {
            throw(RuntimeError("Type error in variadic less than or equal"));
        }
        if (compareNumericValues(args[i], args[i+1]) > 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) {
    if (args.size() < 2) {
        throw(RuntimeError("= requires at least 2 arguments"));
    }
    
    for (size_t i = 0; i < args.size() - 1; i++) {
        if ((args[i]->v_type != V_INT && args[i]->v_type != V_RATIONAL) || 
            (args[i+1]->v_type != V_INT && args[i+1]->v_type != V_RATIONAL)) {
            throw(RuntimeError("Type error in variadic equality"));
        }
        if (compareNumericValues(args[i], args[i+1]) != 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) {
    if (args.size() < 2) {
        throw(RuntimeError(">= requires at least 2 arguments"));
    }
    
    for (size_t i = 0; i < args.size() - 1; i++) {
        if ((args[i]->v_type != V_INT && args[i]->v_type != V_RATIONAL) || 
            (args[i+1]->v_type != V_INT && args[i+1]->v_type != V_RATIONAL)) {
            throw(RuntimeError("Type error in variadic greater than or equal"));
        }
        if (compareNumericValues(args[i], args[i+1]) < 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) {
    if (args.size() < 2) {
        throw(RuntimeError("> requires at least 2 arguments"));
    }
    
    for (size_t i = 0; i < args.size() - 1; i++) {
        if ((args[i]->v_type != V_INT && args[i]->v_type != V_RATIONAL) || 
            (args[i+1]->v_type != V_INT && args[i+1]->v_type != V_RATIONAL)) {
            throw(RuntimeError("Type error in variadic greater than"));
        }
        if (compareNumericValues(args[i], args[i+1]) <= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) {
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) {
    if (args.empty()) {
        return NullV();
    }
    
    Value result = NullV();
    for (int i = args.size() - 1; i >= 0; i--) {
        result = PairV(args[i], result);
    }
    
    return result;
}

Value IsList::evalRator(const Value &rand) {
    if (rand->v_type == V_NULL) {
        return BooleanV(true);
    }
    
    if (rand->v_type != V_PAIR) {
        return BooleanV(false);
    }
    
    Value slow = rand;
    Value fast = rand;
    
    while (true) {
        if (fast->v_type != V_PAIR) break;
        fast = dynamic_cast<Pair*>(fast.get())->cdr;
        if (fast->v_type != V_PAIR) break;
        fast = dynamic_cast<Pair*>(fast.get())->cdr;
        
        slow = dynamic_cast<Pair*>(slow.get())->cdr;
        
        if (slow.get() == fast.get()) {
            return BooleanV(false);
        }
    }
    
    return BooleanV(fast->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) {
    if (rand->v_type == V_PAIR)
        return dynamic_cast<Pair*>(rand.get())->car;
    else
        throw(RuntimeError("Type error: car requires a pair"));
}

Value Cdr::evalRator(const Value &rand) {
    if (rand->v_type == V_PAIR)
        return dynamic_cast<Pair*>(rand.get())->cdr;
    else
        throw(RuntimeError("Type error: cdr requires a pair"));
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-car!: argument must be a pair");
    }
    
    Pair* pair_ptr = dynamic_cast<Pair*>(rand1.get());
    pair_ptr->car = rand2;
    
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-cdr!: argument must be a pair");
    }
    
    Pair* pair_ptr = dynamic_cast<Pair*>(rand1.get());
    pair_ptr->cdr = rand2;
    
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) {
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) {
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) {
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) {
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) {
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) {
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) {
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    if (es.size() == 0) return VoidV();
    
    std::vector<std::pair<std::string, Expr>> internal_defs;
    int first_non_define = 0;
    
    for (int i = 0; i < es.size(); i++) {
        if (es[i]->e_type == E_DEFINE) {
            Define* def = dynamic_cast<Define*>(es[i].get());
            if (def) {
                internal_defs.push_back({def->var, def->e});
                first_non_define = i + 1;
            } else {
                break;
            }
        } else {
            break;
        }
    }
    
    if (!internal_defs.empty()) {
        Assoc new_env = e;
        for (const auto &def : internal_defs) {
            new_env = extend(def.first, Value(nullptr), new_env);
        }
        
        for (const auto &def : internal_defs) {
            Value val = def.second->eval(new_env);
            modify(def.first, val, new_env);
        }
        
        if (first_non_define >= es.size()) {
            return VoidV();
        }
        
        for (int i = first_non_define; i < es.size() - 1; i++) {
            es[i]->eval(new_env);
        }
        return es[es.size() - 1]->eval(new_env);
    }
    
    for (int i = 0; i < es.size() - 1; i++) {
        es[i]->eval(e);
    }
    return es[es.size() - 1]->eval(e);
}

Value Quote::eval(Assoc& e) {
    if (dynamic_cast<TrueSyntax*>(s.get())) 
        return BooleanV(true);
    else if (dynamic_cast<FalseSyntax*>(s.get())) 
        return BooleanV(false);
    else if (dynamic_cast<Number*>(s.get()))
        return IntegerV(dynamic_cast<Number*>(s.get())->n);
    else if (dynamic_cast<SymbolSyntax*>(s.get())) 
        return SymbolV(dynamic_cast<SymbolSyntax*>(s.get())->s);
    else if (dynamic_cast<StringSyntax*>(s.get())) 
        return StringV(dynamic_cast<StringSyntax*>(s.get())->s);
    else if (dynamic_cast<List*>(s.get())) {
        auto stxs_got = dynamic_cast<List*>(s.get())->stxs; 
        List* temp = new List;
        if (dynamic_cast<List*>(s.get())->stxs.empty()) {
            return NullV();
        } else if (stxs_got.size() == 1) {
            return PairV(Value(Quote(stxs_got[0]).eval(e)), NullV());
        } else {
            int pos = -1, cnt = 0, len = stxs_got.size();
            for (int i = 0; i < len; i++) {
                pos = (((dynamic_cast<SymbolSyntax*>(stxs_got[i].get())) && (dynamic_cast<SymbolSyntax*>(stxs_got[i].get())->s == ".")) ? (i) : (pos));
                cnt = (((dynamic_cast<SymbolSyntax*>(stxs_got[i].get())) && (dynamic_cast<SymbolSyntax*>(stxs_got[i].get())->s == ".")) ? (cnt + 1) : (cnt));
            }
            if ((cnt > 1 || ((pos != len - 2) && (cnt))) || (cnt == 1 && (len < 3))) {
                throw RuntimeError("Parm isn't fit");
            }
            if (len == 3) {
                if ((dynamic_cast<SymbolSyntax*>(stxs_got[1].get())) && (dynamic_cast<SymbolSyntax*>(stxs_got[1].get())->s == ".")) {
                    return PairV(Quote(stxs_got[0]).eval(e), Quote(stxs_got[2]).eval(e));
                }
            }
            (*temp).stxs = std::vector<Syntax>(stxs_got.begin() + 1, stxs_got.end());
            return PairV(Value(Quote(stxs_got.front()).eval(e)), Value(Quote(Syntax(temp)).eval(e)));
        }
    } else 
        throw(RuntimeError("Unknown quoted typename"));
}

Value AndVar::eval(Assoc &e) {
    if (rands.size() == 0) return BooleanV(true);
    
    for (int i = 0; i < rands.size(); i++) {
        Value val = rands[i]->eval(e);
        if (val->v_type == V_BOOL) {
            Boolean* b = dynamic_cast<Boolean*>(val.get());
            if (!b->b) {
                return BooleanV(false);
            }
        }
        if (i == rands.size() - 1) {
            return val;
        }
    }
    return BooleanV(true);
}

Value OrVar::eval(Assoc &e) {
    if (rands.size() == 0) return BooleanV(false);
    
    for (int i = 0; i < rands.size(); i++) {
        Value val = rands[i]->eval(e);
        bool is_false = false;
        if (val->v_type == V_BOOL) {
            Boolean* b = dynamic_cast<Boolean*>(val.get());
            is_false = !b->b;
        }
        
        if (!is_false) {
            return val;
        }
        
        if (i == rands.size() - 1) {
            return BooleanV(false);
        }
    }
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) {
    if (rand->v_type == V_BOOL and (dynamic_cast<Boolean*>(rand.get())->b == false))
        return BooleanV(true);
    else
        return BooleanV(false);
}

Value If::eval(Assoc &e) {
    Value valueof_condition = cond->eval(e);
    if (valueof_condition->v_type == V_BOOL && 
        dynamic_cast<Boolean*>(valueof_condition.get())->b == false) {
        return alter->eval(e);
    } else {
        return conseq->eval(e);
    }
}

Value Cond::eval(Assoc &env) {
    for (const auto &clause : clauses) {
        if (clause.empty()) continue;
        
        if (clause[0]->e_type == E_VAR) {
            Var* var_expr = dynamic_cast<Var*>(clause[0].get());
            if (var_expr && var_expr->x == "else") {
                if (clause.size() == 1) {
                    return VoidV();
                }
                Value result = VoidV();
                for (size_t i = 1; i < clause.size(); i++) {
                    result = clause[i]->eval(env);
                }
                return result;
            }
        }
        
        Value pred_value = clause[0]->eval(env);
        
        bool is_true = true;
        if (pred_value->v_type == V_BOOL) {
            Boolean* b = dynamic_cast<Boolean*>(pred_value.get());
            is_true = b->b;
        }
        
        if (is_true) {
            if (clause.size() == 1) {
                return pred_value;
            }
            Value result = VoidV();
            for (size_t i = 1; i < clause.size(); i++) {
                result = clause[i]->eval(env);
            }
            return result;
        }
    }
    
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    Assoc new_env = env;
    return ProcedureV(x, e, new_env);
}

Value Apply::eval(Assoc &e) {
    Value mid_fun = rator->eval(e);
    if (mid_fun->v_type != V_PROC) {throw RuntimeError("Attempt to apply a non-procedure");}

    Procedure* clos_ptr = dynamic_cast<Procedure*>(mid_fun.get());
    
    std::vector<Value> args;
    for (int i = 0; i < rand.size(); i++) {
        args.push_back(rand[i]->eval(e));
    }

    // 检查参数数量 - 对于可变参数操作符，允许任意数量的参数
    if (clos_ptr->parameters.size() == 1 && clos_ptr->parameters[0] == "args") {
        // 可变参数操作符，接受任意数量的参数
        // 不需要检查参数数量
    } else if (args.size() != clos_ptr->parameters.size()) {
        throw RuntimeError("Wrong number of arguments");
    }

    Assoc param_env = clos_ptr->env;
    
    // 对于可变参数操作符，直接调用 Variadic 的 eval 方法
    if (clos_ptr->parameters.size() == 1 && clos_ptr->parameters[0] == "args") {
        Variadic* variadic_op = dynamic_cast<Variadic*>(clos_ptr->e.get());
        if (variadic_op != nullptr) {
            return variadic_op->evalRator(args);
        } else {
            // 如果不是 Variadic 类型，回退到原来的环境扩展方式
            Value args_list = NullV();
            for (int i = args.size() - 1; i >= 0; i--) {
                args_list = PairV(args[i], args_list);
            }
            param_env = extend("args", args_list, param_env);
            return clos_ptr->e->eval(param_env);
        }
    } else {
        // 固定参数的情况
        for (int i = 0; i < clos_ptr->parameters.size(); i++) {
            param_env = extend(clos_ptr->parameters[i], args[i], param_env);
        }
        return clos_ptr->e->eval(param_env);
    }
}

Value Define::eval(Assoc &env) {
    if (primitives.count(var) || reserved_words.count(var)) {
        throw RuntimeError("Cannot redefine primitive: " + var);
    }
    
    env = extend(var, Value(nullptr), env);
    
    Value val = e->eval(env);
    
    modify(var, val, env);
    
    return VoidV();
}

Value Let::eval(Assoc &env) {
    Assoc cur_env = env;
    std::vector<std::pair<std::string, Value>> tobind;
    for (auto binded_pair : bind) {
        tobind.push_back({binded_pair.first, binded_pair.second->eval(env)});
    }
    for (auto binded_pair : tobind) {
        cur_env = extend(binded_pair.first, binded_pair.second, cur_env);
    }
    return body->eval(cur_env);
}

Value Letrec::eval(Assoc &env) {
    Assoc env1 = env;

    for (const auto &binding : bind) {
        env1 = extend(binding.first, Value(nullptr), env1);
    }

    std::vector<std::pair<std::string,Value>> bindings;

    for (const auto &binding : bind) {
        bindings.push_back(std::make_pair(binding.first, binding.second->eval(env1)));
    }

    Assoc env2 = env1;

    for (const auto &binding: bindings) {
        modify(binding.first, binding.second, env2);
    }

    return body->eval(env2);
}

Value Set::eval(Assoc &env) {
    Value var_value = find(var, env);
    if (var_value.get() == nullptr) {
        throw RuntimeError("Undefined variable in set!: " + var);
    }
    
    Value new_val = e->eval(env);
    
    modify(var, new_val, env);
    
    return VoidV();
}

Value Display::evalRator(const Value &rand) {
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    
    return VoidV();
}
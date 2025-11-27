#include "Def.hpp"
#include "syntax.hpp"
#include "expr.hpp"
#include "value.hpp"
#include "RE.hpp"
#include <sstream>
#include <iostream>
#include <map>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

bool isExplicitVoidCall(Expr expr) {
    MakeVoid* make_void_expr = dynamic_cast<MakeVoid*>(expr.get());
    if (make_void_expr != nullptr) {
        return true;
    }
    
    Apply* apply_expr = dynamic_cast<Apply*>(expr.get());
    if (apply_expr != nullptr) {
        Var* var_expr = dynamic_cast<Var*>(apply_expr->rator.get());
        if (var_expr != nullptr && var_expr->x == "void") {
            return true;
        }
    }
    
    Begin* begin_expr = dynamic_cast<Begin*>(expr.get());
    if (begin_expr != nullptr && !begin_expr->es.empty()) {
        return isExplicitVoidCall(begin_expr->es.back());
    }
    
    If* if_expr = dynamic_cast<If*>(expr.get());
    if (if_expr != nullptr) {
        return isExplicitVoidCall(if_expr->conseq) || isExplicitVoidCall(if_expr->alter);
    }
    
    Cond* cond_expr = dynamic_cast<Cond*>(expr.get());
    if (cond_expr != nullptr) {
        for (const auto& clause : cond_expr->clauses) {
            if (clause.size() > 1 && isExplicitVoidCall(clause.back())) {
                return true;
            }
        }
    }
    return false;
}

// 新增：检查是否是 display 调用
bool isDisplayCall(Expr expr) {
    // 检查直接调用 (display ...)
    Apply* apply_expr = dynamic_cast<Apply*>(expr.get());
    if (apply_expr != nullptr) {
        Var* var_expr = dynamic_cast<Var*>(apply_expr->rator.get());
        if (var_expr != nullptr && var_expr->x == "display") {
            return true;
        }
    }
    
    // 检查 begin 表达式中的最后一个子表达式
    Begin* begin_expr = dynamic_cast<Begin*>(expr.get());
    if (begin_expr != nullptr && !begin_expr->es.empty()) {
        return isDisplayCall(begin_expr->es.back());
    }
    
    // 检查 if 表达式的分支
    If* if_expr = dynamic_cast<If*>(expr.get());
    if (if_expr != nullptr) {
        return isDisplayCall(if_expr->conseq) || isDisplayCall(if_expr->alter);
    }
    
    // 检查 cond 表达式的分支
    Cond* cond_expr = dynamic_cast<Cond*>(expr.get());
    if (cond_expr != nullptr) {
        for (const auto& clause : cond_expr->clauses) {
            if (clause.size() > 1 && isDisplayCall(clause.back())) {
                return true;
            }
        }
    }
    
    return false;
}

void REPL(){
    Assoc global_env = empty();
    while (1){
        #ifndef ONLINE_JUDGE
            std::cout << "scm> ";
        #endif
        Syntax stx = readSyntax(std :: cin);
        try{
            Expr expr = stx -> parse(global_env);
            Value val = expr -> eval(global_env);
            if (val -> v_type == V_TERMINATE)
                break;
            
            // 统一的显示逻辑
            if (val->v_type == V_VOID) {
                // void 值：只有显式调用 void 时才显示
                if (isExplicitVoidCall(expr)) {
                    val -> show(std :: cout);
                    puts("");
                }
                // 其他 void 不显示（包括 display 的返回值）
            } else {
                // 非 void 值：只有非 display 调用才显示
                if (!isDisplayCall(expr)) {
                    val -> show(std :: cout);
                    puts("");
                }
            }
        }
        catch (const RuntimeError &RE){
            #ifndef ONLINE_JUDGE
                std :: cout << RE.message();
            #endif
            std :: cout << "RuntimeError";
            puts("");
        }
    }
}

int main(int argc, char *argv[]) {
    REPL();
    return 0;
}
/*
 * 声明：本代码为 2020 秋 中国科大编译原理（李诚）课程实验参考实现。
 * 请不要以任何方式，将本代码上传到可以公开访问的站点或仓库
 */

#include "cminusf_builder.hpp"

#define CONST_FP(num) ConstantFP::get((float)num, module.get())
#define CONST_INT(num) ConstantInt::get(num, module.get())


// TODO: Global Variable Declarations 
// You can define global variables here
// to store state. You can expand these
// definitions if you need to.
Value* factor_return_val;
Value* var_return_val;
Value* expression_return_val;
Value* additive_expression_return_val;
Value* term_return_val;
bool assignmentCallForVar;

// function that is being built
Function *cur_fun = nullptr;

// types
Type *VOID_T;
Type *INT1_T;
Type *INT32_T;
Type *INT32PTR_T;
Type *FLOAT_T;
Type *FLOATPTR_T;


std::string TypeOf(Value * val){
    if(val->get_type() == VOID_T)return "void";
    if(val->get_type() == INT1_T)return "bool";
    if(val->get_type() == INT32_T)return "int";
    if(val->get_type() == INT32PTR_T)return "int *";
    if(val->get_type() == FLOAT_T)return "float";
    if(val->get_type() == FLOATPTR_T)return "float *";
    return "unspecified";
}

/*
 * use CMinusfBuilder::Scope to construct scopes
 * scope.enter: enter a new scope
 * scope.exit: exit current scope
 * scope.push: add a new binding to current scope
 * scope.find: find and return the value bound to the name
 */

void CminusfBuilder::visit(ASTProgram &node) {
    VOID_T = Type::get_void_type(module.get());
    INT1_T = Type::get_int1_type(module.get());
    INT32_T = Type::get_int32_type(module.get());
    INT32PTR_T = Type::get_int32_ptr_type(module.get());
    FLOAT_T = Type::get_float_type(module.get());
    FLOATPTR_T = Type::get_float_ptr_type(module.get());

    for (auto decl : node.declarations) {
        decl->accept(*this);
    }
}

void CminusfBuilder::visit(ASTNum &node) {
    //!TODO: This function is empty now.
    // Add some code here.
    factor_return_val = node.type == TYPE_INT ? static_cast<Value*> (CONST_INT(node.i_val)) : static_cast<Value*>(CONST_FP(node.f_val));
}

void CminusfBuilder::visit(ASTVarDeclaration &node) {
    //!TODO: This function is empty now.
    // Add some code here.
    Type* elementType = node.type == TYPE_INT ? INT32_T : FLOAT_T;
    Type* varType = elementType;
    Value* variable;
    if(node.num){
        if(node.num->i_val) {
            varType = ArrayType::get(elementType, node.num->i_val);
        }
        else{
            //error
            std::cout << "[compiler error]: '" << node.id << "' is delcared as an array with a not positive size" << std::endl;
            exit(-1); 
        }
    }
    if(scope.in_global()){
        auto initializer = ConstantZero::get(elementType, module.get());
        variable = GlobalVariable::create(node.id, module.get(), varType, false, initializer);
    }
    else{
        variable = builder->create_alloca(varType);
    }
    if(!scope.push(node.id, variable)){
        std::cout << "[compiler error]: Redefinition of '" << node.id << "'" << std::endl; 
        exit(-1); 
    }
}

void CminusfBuilder::visit(ASTFunDeclaration &node) {

    FunctionType *fun_type;
    Type *ret_type;
    std::vector<Type *> param_types;
    if (node.type == TYPE_INT)
        ret_type = INT32_T;
    else if (node.type == TYPE_FLOAT)
        ret_type = FLOAT_T; 
    else
        ret_type = VOID_T;

    for (auto &param : node.params) {
        //!TODO: Please accomplish param_types.
        switch (param->type){
            case TYPE_INT:{
                Type* paramType = param->isarray ? INT32PTR_T : INT32_T;
                param_types.push_back(paramType);
            }break;
            case TYPE_FLOAT:{
                Type* paramType = param->isarray ? FLOATPTR_T : FLOAT_T;
                param_types.push_back(paramType);
            }break;
            default:;
        }
    }
    fun_type = FunctionType::get(ret_type, param_types);
    auto fun = Function::create(fun_type, node.id, module.get());
    scope.push(node.id, fun);
    cur_fun = fun;
    auto funBB = BasicBlock::create(module.get(), "entry", fun);
    builder->set_insert_point(funBB);
    scope.enter();
    std::vector<Value *> args;
    for (auto arg = fun->arg_begin(); arg != fun->arg_end(); arg++) {
        args.push_back(*arg);
    }
    for (int i = 0; i < node.params.size(); ++i) {
        //!TODO: You need to deal with params
        // and store them in the scope.
        auto paramAlloca = builder->create_alloca(param_types[i]);
        auto paramStore = builder->create_store(args[i], paramAlloca);
        scope.push(node.params[i]->id, paramAlloca);
    }
    node.compound_stmt->accept(*this);
    if (builder->get_insert_block()->get_terminator() == nullptr) 
    {
        if (cur_fun->get_return_type()->is_void_type())
            builder->create_void_ret();
        else if (cur_fun->get_return_type()->is_float_type())
            builder->create_ret(CONST_FP(0.));
        else
            builder->create_ret(CONST_INT(0));
    }
    scope.exit();

}

void CminusfBuilder::visit(ASTParam &node) {
    //!TODO: This function is empty now.
    // Add some code here.
    
}

void CminusfBuilder::visit(ASTCompoundStmt &node) {
    //!TODO: This function is not complete.
    // You may need to add some code here
    // to deal with complex statements. 

    static int layer = 0;
    if(layer){
        scope.enter();
    }
    layer++;
    for (auto &decl : node.local_declarations) {
        decl->accept(*this);
    }
    for (auto &stmt : node.statement_list) {
        stmt->accept(*this);
        if (builder->get_insert_block()->get_terminator() != nullptr)
            break;
    }
    layer--;
    if(layer){
        scope.exit();
    }

}

void CminusfBuilder::visit(ASTExpressionStmt &node) {
    //!TODO: This function is empty now.
    // Add some code here.
    if(node.expression){
        node.expression->accept(*this);
    }
}

void CminusfBuilder::visit(ASTSelectionStmt &node) {
    //!TODO: This function is empty now.
    // Add some code here.
  
    if(node.expression){
        node.expression->accept(*this);
    }

    //condition check
    if(expression_return_val->get_type() == INT32_T){
        expression_return_val = builder->create_icmp_gt(expression_return_val, CONST_INT(0));
    }
    else if(expression_return_val->get_type() == FLOAT_T){
        expression_return_val = builder->create_fcmp_gt(expression_return_val, CONST_FP(0));
    }
    else if(expression_return_val->get_type() != INT1_T){
        std::cout << "[compiler error]: Invalid expression type" << std::endl;
        exit(-1);
    }
    

    auto trueBlock = BasicBlock::create(module.get(), "", cur_fun);
    auto falseBlock = BasicBlock::create(module.get(), "", cur_fun);

    builder->create_cond_br(expression_return_val, trueBlock, falseBlock);
    
    //if true
    builder->set_insert_point(trueBlock);

    if(node.if_statement){
        node.if_statement->accept(*this);
    }


    //if false
    if(node.else_statement){
        auto endBlock = BasicBlock::create(module.get(), "", cur_fun);
        builder->create_br(endBlock);
        
        builder->set_insert_point(falseBlock);
        
        //else block
        node.else_statement->accept(*this);
        
        //end block
        builder->create_br(endBlock);
        builder->set_insert_point(endBlock);
    }
    else{
        //false block
        builder->create_br(falseBlock);
        builder->set_insert_point(falseBlock);
    }


}

void CminusfBuilder::visit(ASTIterationStmt &node) {
    //!TODO: This function is empty now.
    // Add some code here.

    auto whileStart = BasicBlock::create(module.get(), "", cur_fun);
    builder->create_br(whileStart);

    builder->set_insert_point(whileStart);

    if(node.expression){
        node.expression->accept(*this);
    }

    //condition check
    if(expression_return_val->get_type() == INT32_T){
        expression_return_val = builder->create_icmp_gt(expression_return_val, CONST_INT(0));
    }
    else if(expression_return_val->get_type() == FLOAT_T){
        expression_return_val = builder->create_fcmp_gt(expression_return_val, CONST_FP(0));
    }
    else if(expression_return_val->get_type() != INT1_T){
        std::cout << "[compiler error]: Invalid expression type" << std::endl;
        exit(-1);
    }
   
    auto whileTrue = BasicBlock::create(module.get(), "", cur_fun);
    auto whileFalse = BasicBlock::create(module.get(), "", cur_fun);

    builder->create_cond_br(expression_return_val, whileTrue, whileFalse);

    //if true
    builder->set_insert_point(whileTrue);

    if(node.statement){
        node.statement->accept(*this);
    }    

    builder->create_br(whileStart);

    //if false
    builder->set_insert_point(whileFalse);

}

void CminusfBuilder::visit(ASTReturnStmt &node) {

    if (node.expression == nullptr) {
        builder->create_void_ret();
    } else {
        //!TODO: The given code is incomplete.
        // You need to solve other return cases (e.g. return an integer).
        
        auto returnType = cur_fun->get_return_type();
        node.expression->accept(*this);

        //type conversion
        if(returnType == INT32_T){
            if(expression_return_val->get_type() == INT1_T){
                expression_return_val = builder->create_zext(expression_return_val, INT32_T);
            }
            else if(expression_return_val->get_type() == FLOAT_T){
                expression_return_val = builder->create_fptosi(expression_return_val, INT32_T);
            }
            else if(expression_return_val->get_type() != INT32_T){
                std::cout << "[compiler error]: Invalid return type" << std::endl;
                exit(-1);
            }
        }
        else if(returnType == FLOAT_T) {
            if(expression_return_val->get_type() == INT1_T){
                expression_return_val = builder->create_zext(expression_return_val, INT32_T);
            }
            if(expression_return_val->get_type() == INT32_T){
                expression_return_val = builder->create_sitofp(expression_return_val, FLOAT_T);
            }
            else if(expression_return_val->get_type() != FLOAT_T){
                std::cout << "[compiler error]: Invalid return type" << std::endl;
                std::cout << cur_fun->get_name() << ": return 'float'? type"<<std::endl;
                exit(-1);
            }
        }
        else {
            std::cout << "[compiler error]: Invalid return type" << std::endl;
        }
    
        //instruction insertion
        builder->create_ret(expression_return_val);
    }

}

void CminusfBuilder::visit(ASTVar &node) {
    //!TODO: This function is empty now.
    // Add some code here.


    bool calledFromFactor = !assignmentCallForVar;

    Value* variable = scope.find(node.id);
    if(variable){
        if(node.expression){
            node.expression->accept(*this);
            
            //type conversion
            Value* index = expression_return_val;
            if(expression_return_val->get_type() == INT1_T){
                index = builder->create_zext(expression_return_val, INT32_T);
            }
            else if(expression_return_val->get_type() == FLOAT_T){
                index = builder->create_fptosi(expression_return_val, INT32_T);
            }
            else if(expression_return_val->get_type() != INT32_T){
                std::cout << "[compiler error]: Array subscript is not an integer" << std::endl;
                exit(-1);
            }

            //boundry check
            auto false_block = BasicBlock::create(module.get(), "", cur_fun);
            auto true_block = BasicBlock::create(module.get(), "", cur_fun);

            auto icmp = builder->create_icmp_ge(index, CONST_INT(0));
            auto cond_br = builder->create_cond_br(icmp, true_block, false_block);

            //out of boundry
            builder->set_insert_point(false_block);
            builder->create_call(scope.find("neg_idx_except"), {});
            if(cur_fun->get_return_type() == INT32_T){
                builder->create_ret(CONST_INT(-1));
            }
            else if(cur_fun->get_return_type() == FLOAT_T){
                builder->create_ret(CONST_FP(-1.0));
            }
            else{
                builder->create_void_ret();
            }

            //valid boundry
            builder->set_insert_point(true_block);

            //variable is int pointer pointer type
            if(variable->get_type()->get_pointer_element_type()->is_pointer_type()){
                variable = builder->create_load(variable);
                variable = builder->create_gep(variable, {index});
            }
            else{
                variable = builder->create_gep(variable, {CONST_INT(0), index});
            }
        }
        if(calledFromFactor){
            if(variable->get_type()->get_pointer_element_type()->is_array_type()){
                factor_return_val = builder->create_gep(variable, {CONST_INT(0), CONST_INT(0)});
            }
            else{
                factor_return_val = builder->create_load(variable);
            }
        }
        var_return_val = variable;
    }
    else{
        std::cout << "[compiler error]: Use of undeclared identifier '" << node.id << "'" << std::endl;
        exit(-1);
    }

}

void CminusfBuilder::visit(ASTAssignExpression &node) {
    //!TODO: This function is empty now.
    // Add some code here.
    if(node.var){
        assignmentCallForVar = true;
        node.var->accept(*this);
    }
    Value* variable = var_return_val;

    if(node.expression){
        node.expression->accept(*this);
    }
    var_return_val = variable;

    if(expression_return_val->get_type() != INT1_T && expression_return_val->get_type() != INT32_T && expression_return_val->get_type() != FLOAT_T){
        std::cout << "[compiler error]: Assigning to '" << TypeOf(variable) << "' from incompatible type" << std::endl;
        exit(-1); 
    }
    
    if(var_return_val->get_type()->get_pointer_element_type() == INT32_T){
        if(expression_return_val->get_type() == INT1_T){
            expression_return_val = builder->create_zext(expression_return_val, INT32_T);
        }
        else if(expression_return_val->get_type() == FLOAT_T){
            expression_return_val = builder->create_fptosi(expression_return_val, INT32_T);
        }
    }
    else{
        if(expression_return_val->get_type() == INT1_T){
            expression_return_val = builder->create_zext(expression_return_val, INT32_T);
        }
        if(expression_return_val->get_type() == INT32_T){
            expression_return_val = builder->create_sitofp(expression_return_val, FLOAT_T);
        }
    }
    factor_return_val = expression_return_val;
    builder->create_store(expression_return_val, variable);

}

void CminusfBuilder::visit(ASTSimpleExpression &node) {
    //!TODO: This function is empty now.
    // Add some code here.


    if(node.additive_expression_l){
        node.additive_expression_l->accept(*this);      
    }
    Value* leftAdditiveExpression = expression_return_val = additive_expression_return_val;

    if(node.additive_expression_r){
        node.additive_expression_r->accept(*this);
        
        //invalid types
        if(leftAdditiveExpression->get_type() != INT1_T && leftAdditiveExpression->get_type() != INT32_T && leftAdditiveExpression->get_type() != FLOAT_T){
            std::cout << "[compiler error]: Invalid operands to binary expression ('" << TypeOf(leftAdditiveExpression)  << "' and '" << TypeOf(additive_expression_return_val) << "')" << std::endl;
            exit(-1); 
        }

        //type conversion
        if(leftAdditiveExpression->get_type() == INT1_T){
            leftAdditiveExpression = builder->create_zext(leftAdditiveExpression, INT32_T);
        }
        if(additive_expression_return_val->get_type() == INT1_T){
            additive_expression_return_val = builder->create_zext(additive_expression_return_val, INT32_T);
        }
        CminusType type = leftAdditiveExpression->get_type() == INT32_T ? TYPE_INT : TYPE_FLOAT;
        if(leftAdditiveExpression->get_type() != additive_expression_return_val->get_type()){
            if(leftAdditiveExpression->get_type() == INT32_T){
                leftAdditiveExpression = builder->create_sitofp(leftAdditiveExpression, FLOAT_T);
            }
            else{
                additive_expression_return_val = builder->create_sitofp(additive_expression_return_val, FLOAT_T);
            }
            type = TYPE_FLOAT;
        }

        //instruction insertion
        switch (type){
            case TYPE_INT : {
                switch (node.op){
                    case OP_LE : expression_return_val = builder->create_icmp_le(leftAdditiveExpression, additive_expression_return_val); break;
                    case OP_LT : expression_return_val = builder->create_icmp_lt(leftAdditiveExpression, additive_expression_return_val); break;
                    case OP_GT : expression_return_val = builder->create_icmp_gt(leftAdditiveExpression, additive_expression_return_val); break;
                    case OP_GE : expression_return_val = builder->create_icmp_ge(leftAdditiveExpression, additive_expression_return_val); break;
                    case OP_EQ : expression_return_val = builder->create_icmp_eq(leftAdditiveExpression, additive_expression_return_val); break;
                    case OP_NEQ : expression_return_val = builder->create_icmp_ne(leftAdditiveExpression, additive_expression_return_val); break;
                    default:;
                }
            }break;
            case TYPE_FLOAT : {
                switch (node.op){
                    case OP_LE : expression_return_val = builder->create_fcmp_le(leftAdditiveExpression, additive_expression_return_val); break;
                    case OP_LT : expression_return_val = builder->create_fcmp_lt(leftAdditiveExpression, additive_expression_return_val); break;
                    case OP_GT : expression_return_val = builder->create_fcmp_gt(leftAdditiveExpression, additive_expression_return_val); break;
                    case OP_GE : expression_return_val = builder->create_fcmp_ge(leftAdditiveExpression, additive_expression_return_val); break;
                    case OP_EQ : expression_return_val = builder->create_fcmp_eq(leftAdditiveExpression, additive_expression_return_val); break;
                    case OP_NEQ : expression_return_val = builder->create_fcmp_ne(leftAdditiveExpression, additive_expression_return_val); break;
                    default:;
                }
            }break;
            default:;
        };
    }
    factor_return_val = expression_return_val;
}

void CminusfBuilder::visit(ASTAdditiveExpression &node) {
    //!TODO: This function is empty now.
    // Add some code here.
    if(node.additive_expression){

        node.additive_expression->accept(*this);
        Value* additive_expression_val = additive_expression_return_val;

        if(node.term){
            node.term->accept(*this);
        }
        additive_expression_return_val = additive_expression_val;

        //invalid types
        if(term_return_val->get_type() != INT1_T && term_return_val->get_type() != INT32_T && term_return_val->get_type() != FLOAT_T){
            std::cout << "[compiler error]: Invalid operands to binary expression ('" << TypeOf(additive_expression_return_val)  << "' and '" << TypeOf(term_return_val) << "')" << std::endl;
            exit(-1);
        }

        //type conversion
        if(additive_expression_return_val->get_type() == INT1_T){
            additive_expression_return_val = builder->create_zext(additive_expression_return_val, INT32_T);
        }
        if(term_return_val->get_type() == INT1_T){
            term_return_val = builder->create_zext(term_return_val, INT32_T);
        }
        CminusType type = additive_expression_return_val->get_type() == INT32_T ? TYPE_INT : TYPE_FLOAT;
        if(additive_expression_return_val->get_type() != term_return_val->get_type()){
            if(term_return_val->get_type() == FLOAT_T){
                additive_expression_return_val = builder->create_sitofp(additive_expression_return_val, FLOAT_T);
            }
            else {
                term_return_val = builder->create_sitofp(term_return_val, FLOAT_T);
            }
            type = TYPE_FLOAT;
        }

        //instruction insertion
        switch (node.op){
            case OP_PLUS : {
                switch (type){
                    case TYPE_INT : additive_expression_return_val = builder->create_iadd(additive_expression_return_val, term_return_val); break;
                    case TYPE_FLOAT : additive_expression_return_val = builder->create_fadd(additive_expression_return_val, term_return_val); break;
                    default:;
                };
            }break;
            case OP_MINUS : {
                switch (type){
                    case TYPE_INT : additive_expression_return_val = builder->create_isub(additive_expression_return_val, term_return_val); break;
                    case TYPE_FLOAT : additive_expression_return_val = builder->create_fsub(additive_expression_return_val, term_return_val); break;
                    default:;
                };
            }break;
            default:;
        }
    }   
    else{
        if(node.term){
            node.term->accept(*this);
        }
        additive_expression_return_val = term_return_val;
    }
}

void CminusfBuilder::visit(ASTTerm &node) {
    //!TODO: This function is empty now.
    // Add some code here.

    if(node.term){
        
        node.term->accept(*this);
        Value* term_val = term_return_val;

        if(node.factor){
            assignmentCallForVar = false;
            node.factor->accept(*this);
        }
        term_return_val = term_val;
        
        //invalid types
        if(factor_return_val->get_type() != INT1_T && factor_return_val->get_type() != INT32_T && factor_return_val->get_type() != FLOAT_T){
            std::cout << "[compiler error]: Invalid operands to binary expression ('" << TypeOf(term_return_val)  << "' and '" << TypeOf(factor_return_val) << "')" << std::endl;
            exit(-1);
        }
        
        //type conversion
        if(term_return_val->get_type() == INT1_T){
            term_return_val = builder->create_zext(term_return_val, INT32_T);
        }
        if(factor_return_val->get_type() == INT1_T){
            factor_return_val = builder->create_zext(factor_return_val, INT32_T);
        }
        CminusType type = term_return_val->get_type() == INT32_T ? TYPE_INT : TYPE_FLOAT;
        if(term_return_val->get_type() != factor_return_val->get_type()){
            if(term_return_val->get_type() == FLOAT_T){
                factor_return_val = builder->create_sitofp(factor_return_val, FLOAT_T);
            }
            else {
                term_return_val = builder->create_sitofp(term_return_val, FLOAT_T);
            }
            type = TYPE_FLOAT;
        }

        //instruction insertion
        switch (node.op){
            case OP_MUL : {
                switch (type){
                    case TYPE_INT : term_return_val = builder->create_imul(term_return_val, factor_return_val); break;
                    case TYPE_FLOAT : term_return_val = builder->create_fmul(term_return_val, factor_return_val); break;
                    default:;
                };
            }break;
            case OP_DIV : {
                switch (type){
                    case TYPE_INT : term_return_val = builder->create_isdiv(term_return_val, factor_return_val); break;
                    case TYPE_FLOAT : term_return_val = builder->create_fdiv(term_return_val, factor_return_val); break;
                    default:;
                };
            }break;
            default:;
        }

    }
    else{
        if(node.factor){
            assignmentCallForVar = false;
            node.factor->accept(*this);
        }
        term_return_val = factor_return_val;
    }
}

void CminusfBuilder::visit(ASTCall &node) {
    //!TODO: This function is empty now.
    // Add some code here.

    Value* function = scope.find(node.id);
    if(function){
        std::vector<Value*> args;
        FunctionType* parameters = static_cast<FunctionType*>(function->get_type());
        auto parameter = parameters->param_begin();
        for(auto &arg : node.args){
            arg.get()->accept(*this);
            if(parameter == parameters->param_end()){
                std::cout << "[compiler error]: Invalid parameter in '" << node.id << "'" << std::endl;  
                exit(-1);
            }
            if(expression_return_val->get_type() != (*parameter)){
                if((expression_return_val->get_type() == INT1_T || expression_return_val->get_type() == INT32_T || expression_return_val->get_type() == FLOAT_T) && ((*parameter) == FLOAT_T || (*parameter) == INT32_T)){
                    if((*parameter) == FLOAT_T){
                        if(expression_return_val->get_type() == INT1_T){
                            expression_return_val = builder->create_zext(expression_return_val, INT32_T);
                        }
                        expression_return_val = builder->create_sitofp(expression_return_val, FLOAT_T);
                    }
                    else{
                        if(expression_return_val->get_type() == INT1_T){
                            expression_return_val = builder->create_zext(expression_return_val, INT32_T);
                        }
                        else{
                            expression_return_val = builder->create_fptosi(expression_return_val, INT32_T);
                        }
                    }
                }
                else{
                    std::cout << "[compiler error]: Invalid parameter in '" << node.id << "'" << std::endl;  
                    exit(-1);
                }
            }
            args.push_back(expression_return_val);
            parameter++;
        }
        if(parameter != parameters->param_end()){
            std::cout << "[compiler error]: Invalid parameter in '" << node.id << "'" << std::endl;  
            exit(-1);
        }
        factor_return_val = builder->create_call(function,args);
    }
    else {
        std::cout << "[compiler error]: Use of undeclared identifier '" << node.id << "'" << std::endl;
        exit(-1);
    }

}

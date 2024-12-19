#include "GVN.h"

#include "BasicBlock.h"
#include "Constant.h"
#include "DeadCode.h"
#include "FuncInfo.h"
#include "Function.h"
#include "Instruction.h"
#include "logging.hpp"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <memory>
#include <sstream>
#include <tuple>
#include <utility>
#include <vector>

using namespace GVNExpression;
using std::string_literals::operator""s;
using std::shared_ptr;

int I = 0;
bool Print;
void debug(std::string str, int checkPoint){
    if(I == checkPoint)
        std::cout << str << std::endl;
}
void debug(std::string str){
    if(Print)
        std::cout << str << std::endl;
}
static auto get_const_int_value = [](Value *v) { return dynamic_cast<ConstantInt *>(v)->get_value(); };
static auto get_const_fp_value = [](Value *v) { return dynamic_cast<ConstantFP *>(v)->get_value(); };
// Constant Propagation helper, folders are done for you
Constant *ConstFolder::compute(Instruction *instr, Constant *value1, Constant *value2) {
    auto op = instr->get_instr_type();
    switch (op) {
    case Instruction::add: return ConstantInt::get(get_const_int_value(value1) + get_const_int_value(value2), module_);
    case Instruction::sub: return ConstantInt::get(get_const_int_value(value1) - get_const_int_value(value2), module_);
    case Instruction::mul: return ConstantInt::get(get_const_int_value(value1) * get_const_int_value(value2), module_);
    case Instruction::sdiv: return ConstantInt::get(get_const_int_value(value1) / get_const_int_value(value2), module_);
    case Instruction::fadd: return ConstantFP::get(get_const_fp_value(value1) + get_const_fp_value(value2), module_);
    case Instruction::fsub: return ConstantFP::get(get_const_fp_value(value1) - get_const_fp_value(value2), module_);
    case Instruction::fmul: return ConstantFP::get(get_const_fp_value(value1) * get_const_fp_value(value2), module_);
    case Instruction::fdiv: return ConstantFP::get(get_const_fp_value(value1) / get_const_fp_value(value2), module_);

    case Instruction::cmp:
        switch (dynamic_cast<CmpInst *>(instr)->get_cmp_op()) {
        case CmpInst::EQ: return ConstantInt::get(get_const_int_value(value1) == get_const_int_value(value2), module_);
        case CmpInst::NE: return ConstantInt::get(get_const_int_value(value1) != get_const_int_value(value2), module_);
        case CmpInst::GT: return ConstantInt::get(get_const_int_value(value1) > get_const_int_value(value2), module_);
        case CmpInst::GE: return ConstantInt::get(get_const_int_value(value1) >= get_const_int_value(value2), module_);
        case CmpInst::LT: return ConstantInt::get(get_const_int_value(value1) < get_const_int_value(value2), module_);
        case CmpInst::LE: return ConstantInt::get(get_const_int_value(value1) <= get_const_int_value(value2), module_);
        }
    case Instruction::fcmp:
        switch (dynamic_cast<FCmpInst *>(instr)->get_cmp_op()) {
        case FCmpInst::EQ: return ConstantInt::get(get_const_fp_value(value1) == get_const_fp_value(value2), module_);
        case FCmpInst::NE: return ConstantInt::get(get_const_fp_value(value1) != get_const_fp_value(value2), module_);
        case FCmpInst::GT: return ConstantInt::get(get_const_fp_value(value1) > get_const_fp_value(value2), module_);
        case FCmpInst::GE: return ConstantInt::get(get_const_fp_value(value1) >= get_const_fp_value(value2), module_);
        case FCmpInst::LT: return ConstantInt::get(get_const_fp_value(value1) < get_const_fp_value(value2), module_);
        case FCmpInst::LE: return ConstantInt::get(get_const_fp_value(value1) <= get_const_fp_value(value2), module_);
        }
    default: return nullptr;
    }
}

Constant *ConstFolder::compute(Instruction *instr, Constant *value1) {
    auto op = instr->get_instr_type();
    switch (op) {
    case Instruction::sitofp: return ConstantFP::get((float)get_const_int_value(value1), module_);
    case Instruction::fptosi: return ConstantInt::get((int)get_const_fp_value(value1), module_);
    case Instruction::zext: return ConstantInt::get((int)get_const_int_value(value1), module_);
    default: return nullptr;
    }
}

Constant *ConstFolder::compute(Instruction::OpID op, Constant *value1, Constant *value2){
    switch (op) {
        case Instruction::add: return ConstantInt::get(get_const_int_value(value1) + get_const_int_value(value2), module_);
        case Instruction::sub: return ConstantInt::get(get_const_int_value(value1) - get_const_int_value(value2), module_);
        case Instruction::mul: return ConstantInt::get(get_const_int_value(value1) * get_const_int_value(value2), module_);
        case Instruction::sdiv: return ConstantInt::get(get_const_int_value(value1) / get_const_int_value(value2), module_);
        case Instruction::fadd: return ConstantFP::get(get_const_fp_value(value1) + get_const_fp_value(value2), module_);
        case Instruction::fsub: return ConstantFP::get(get_const_fp_value(value1) - get_const_fp_value(value2), module_);
        case Instruction::fmul: return ConstantFP::get(get_const_fp_value(value1) * get_const_fp_value(value2), module_);
        case Instruction::fdiv: return ConstantFP::get(get_const_fp_value(value1) / get_const_fp_value(value2), module_);
        default: return nullptr;
    }
}

namespace utils {
static std::string print_congruence_class(const CongruenceClass &cc) {
    std::stringstream ss;
    if (cc.index_ == 0) {
        ss << "top class\n";
        return ss.str();
    }
    ss << "\nindex: " << cc.index_ << "\nleader: " << cc.leader_->print()
       << "\nvalue phi: " << (cc.value_phi_ ? cc.value_phi_->print() : "nullptr"s)
       << "\nvalue expr: " << (cc.value_expr_  ? cc.value_expr_->print() : "nullptr"s)
       << "\nconstnant: " << (cc.constant_ ? cc.constant_->print() : "nullptr"s) << "\nmembers: {";
       
    for (auto &member : cc.members_)
        ss << member->print() << "; ";
    ss << "}\n";
    return ss.str();
}

static std::string dump_cc_json(const CongruenceClass &cc) {
    std::string json;
    json += "[";
    for (auto member : cc.members_) {
        if (auto c = dynamic_cast<Constant *>(member))
            json += member->print() + ", ";
        else
            json += "\"%" + member->get_name() + "\", ";
    }
    json += "]";
    return json;
}

static std::string dump_partition_json(const GVN::partitions &p) {
    std::string json;
    json += "[";
    for (auto cc : p)
        json += dump_cc_json(*cc) + ", ";
    json += "]";
    return json;
}

static std::string dump_bb2partition(const std::map<BasicBlock *, GVN::partitions> &map) {
    std::string json;
    json += "{";
    for (auto [bb, p] : map)
        json += "\"" + bb->get_name() + "\": " + dump_partition_json(p) + ",";
    json += "}";
    return json;
}

// logging utility for you
static void print_partitions(const GVN::partitions &p) {
    if (p.empty()) {
        LOG_DEBUG << "empty partitions\n";
        return;
    }
    std::string log;
    for (auto &cc : p)
        log += print_congruence_class(*cc);
    LOG_DEBUG << log; // please don't use std::cout
}
} // namespace utils

GVN::partitions GVN::join(const partitions &P1, const partitions &P2, BasicBlock *lbb, BasicBlock *rbb) {
    // TODO: do intersection pair-wise
    partitions P;
    for(auto ci : P1){
        for(auto cj : P2){
            auto Ck = intersect(ci, cj, lbb, rbb);
            if(Ck != nullptr)
                P.insert(Ck);
        }
    }
    return P;
}

std::shared_ptr<CongruenceClass> GVN::intersect(std::shared_ptr<CongruenceClass> Ci,
                                                std::shared_ptr<CongruenceClass> Cj,
                                                BasicBlock *lbb, BasicBlock *rbb) {
    if(Ci->index_ == 0) 
        return Cj;
    if(Cj->index_ == 0)
        return Ci;
    std::set<Value*> members;
    std::set_intersection(Ci->members_.begin(), Ci->members_.end(),
                        Cj->members_.begin(), Cj->members_.end(),
                        std::inserter(members, members.begin()));
    if(members.size() == 0){
        return nullptr;
    }

    size_t value_number;
    Value *leader;
    shared_ptr<Expression> value_expr = nullptr;
    shared_ptr<PhiExpression> value_phi = nullptr;
    Constant *constant = nullptr;

    if(Ci->leader_ == Cj->leader_){
        leader = Ci->leader_;
        if(basicBlockHasBeenReached[lbb]){
            value_number = Ci->index_;
            value_expr = Ci->value_expr_;
            value_phi = Ci->value_phi_;
            constant = Ci->constant_;
        }
        else{
            value_number = Cj->index_;
            value_expr = Cj->value_expr_;
            value_phi = Cj->value_phi_;
            constant = Cj->constant_;
        }
    }
    else {
        value_number = next_value_number_++;
        leader = *members.begin();
        //foo
        shared_ptr<Expression> lhs;
        shared_ptr<Expression> rhs;
        if(Ci->phiConstant_){
            lhs = ConstantExpression::create(Ci->constant_);
        }
        else{
           lhs = ValueNumber::create(Ci->index_);
        }
        if(Cj->phiConstant_){
            rhs = ConstantExpression::create(Cj->constant_);
        }
        else{
           rhs = ValueNumber::create(Cj->index_);
        }
        value_phi = PhiExpression::create(lhs, rhs, lbb, rbb);
        // if(Ci->constant_ == Cj->constant_){
        //     constant = Ci->constant_;
        // }
    }

    auto Ck = createCongruenceClass(value_number);
    Ck->leader_ = leader;
    Ck->value_expr_ = value_expr;
    Ck->value_phi_ = value_phi;
    Ck->members_ = members;
    Ck->constant_ = constant;
    return Ck;
}

void GVN::initializeReachedMap(){
    auto entryBlock = func_->get_entry_block(); 
    basicBlockHasBeenReached[entryBlock] = true;
    for(auto &bb : func_->get_basic_blocks()){
        if(&bb == entryBlock){
            continue;
        }
        basicBlockHasBeenReached[&bb] = false;
    }
}

void GVN::detectEquivalences() {
    bool changed = false;
    
    partitions temp;

    //add global variable to temp
    for(auto &g_var : m_->get_global_variable()){
        auto cc = createCongruenceClass(next_value_number_++);
        if(g_var.is_const()){
            cc->leader_ = g_var.get_init();
            cc->value_expr_ = ConstantExpression::create(g_var.get_init());
            cc->members_.insert(&g_var);
            cc->constant_ = g_var.get_init();
        }
        else{
            cc->leader_ = &g_var;
            cc->members_.insert(&g_var);
        }
        temp.insert(cc);
    }

    //add arguments to temp
    for(auto argument : func_->get_args()){
        auto cc = createCongruenceClass(next_value_number_++);
        cc->leader_ = argument;
        cc->members_.insert(argument);
        temp.insert(cc);
    }
    
    
    
    //PIN1 = {}
    auto entryBlock = func_->get_entry_block(); 
 


    //POUT1 = transferFunction(PIN1)
    for(auto &instruction : entryBlock->get_instructions()){
        if(not instruction.is_phi())
            temp = transferFunction(&instruction, &instruction, temp, *entryBlock);
    }
    for(auto successor : entryBlock->get_succ_basic_blocks()){
        for(auto &instruction : successor->get_instructions()){
            if(instruction.is_phi())
                temp = transferFunction(&instruction, &instruction, temp, *entryBlock);
        }
    }
    pout_[entryBlock] = std::move(temp);

    // std::cout << entryBlock->get_name() <<" ---------------entryBlock---------------" << I << std::endl;
    // for(auto cc : pout_[entryBlock])
    //     std::cout << utils::print_congruence_class(*cc); 
    
    for(auto &bb : func_->get_basic_blocks()){
        if(&bb == entryBlock)
            continue;
        pout_[&bb] = {createCongruenceClass()}; //POUTs = T
    }


    std::uint64_t value_number_start = next_value_number_;
    
    do {
        next_value_number_ = value_number_start;
        changed = false;
        initializeReachedMap();
        for (auto &bb : func_->get_basic_blocks()) { // you might need to visit the blocks in depth-first order
            // get PIN of bb by predecessor(s)
            // iterate through all instructions in the block
            // and the phi instruction in all the successors
            //if bb has more than two blocks join them
            if(&bb == entryBlock)
                continue;
            
            basicBlockHasBeenReached[&bb] = true;
            
            //get PINs
            auto predecessors = bb.get_pre_basic_blocks();
            auto it = predecessors.begin();
            if(predecessors.size() == 2){
                auto lbb = *(it++);
                auto rbb = *it;
                temp = join(pout_[lbb] ,pout_[rbb], lbb, rbb);
            }
            else if(predecessors.size() == 1){
                temp = pout_[*it];
            }
            else {
                continue;
            }
          
            
            //debug
            std::cout << bb.get_name() <<" ---------------join---------------" << I << std::endl;
            for(auto cc : temp)
                std::cout << utils::print_congruence_class(*cc); 
            
            //POUTs = transferFunction(PINs)
            for(auto &instruction : bb.get_instructions()){
                if(not instruction.is_phi()){
                    temp = transferFunction(&instruction, &instruction, temp, bb);
                }
            }
            for(auto successor : bb.get_succ_basic_blocks()){
                for(auto &instruction : successor->get_instructions()){
                    if(instruction.is_phi()){
                        temp = transferFunction(&instruction, &instruction, temp, bb);
                    }
                }
            }

            //debug
            std::cout << bb.get_name() <<" ---------------temp---------------" << I << std::endl;
            for(auto cc : temp)
                std::cout << utils::print_congruence_class(*cc);
            std::cout << bb.get_name() <<" ---------------pout---------------" << I++ << std::endl;                    
            for(auto cc : pout_[&bb])
                std::cout << utils::print_congruence_class(*cc);                        
            std::cout << "--------------result------------------" << std::endl;
            
            
            if(temp != pout_[&bb]){
                changed = true;
                std::cout << "changed\n";
            }
            else
                std::cout << "unchanged\n";
            std::cout << "\n\n\n\n\n\n\n";

            pout_[&bb] = std::move(temp);
        }
    } while (changed);  
}

shared_ptr<Expression> GVN::valueExpr(Instruction *instr, const partitions &PIN, Constant **constant) {
    // TODO
    if(instr->isBinary() or instr->is_cmp() or instr->is_fcmp()){
        Value *lhs = instr->get_operand(0);
        Value *rhs = instr->get_operand(1);
        Constant *lhs_is_constant = dynamic_cast<Constant *>(lhs);
        Constant *rhs_is_constant = dynamic_cast<Constant *>(rhs);
        shared_ptr<Expression> lhs_value_expr;
        shared_ptr<Expression> rhs_value_expr;

        if(lhs_is_constant and rhs_is_constant){
            *constant = folder_->compute(instr, lhs_is_constant, rhs_is_constant);
            return ConstantExpression::create(*constant);
        }
        
        if(lhs_is_constant){
            lhs_value_expr = ConstantExpression::create(lhs_is_constant);
        }
        else{
            bool found = false;
            for(auto cc : PIN){
                if(cc->members_.find(lhs) != cc->members_.end()){
                    lhs_is_constant = cc->constant_;
                    lhs_value_expr = ValueNumber::create(cc->index_);
                    found = true;
                    break;
                }
            }
            if(not found){
                for(auto &[_bb, pin] : pout_){
                    for(auto cc : pin){
                        if(cc->members_.find(lhs) != cc->members_.end()){
                            lhs_is_constant = cc->constant_;
                            lhs_value_expr = ValueNumber::create(cc->index_);
                            found = true;
                            break;
                        }
                    }
                    if(found)
                        break;
                } 
            }              
        }

        if(rhs_is_constant){
            rhs_value_expr = ConstantExpression::create(rhs_is_constant);
        }
        else{
            bool found = false;
            for(auto cc : PIN){
                if(cc->members_.find(rhs) != cc->members_.end()){
                    rhs_is_constant = cc->constant_;
                    rhs_value_expr = ValueNumber::create(cc->index_);
                    found = true;
                    break;
                }
            }
            if(not found){
                for(auto &[_bb, pin] : pout_){
                    for(auto cc : pin){
                        if(cc->members_.find(rhs) != cc->members_.end()){
                            rhs_is_constant = cc->constant_;
                            rhs_value_expr = ValueNumber::create(cc->index_);
                            found = true;
                            break;
                        }
                    }
                    if(found)
                        break;
                } 
            }              
        }

        if(lhs_is_constant and rhs_is_constant){
            *constant = folder_->compute(instr, lhs_is_constant, rhs_is_constant);
        }

        if(lhs_value_expr == nullptr or rhs_value_expr == nullptr) {
            return nullptr;
        }

        if(instr->isBinary()){
            return BinaryExpression::create(instr->get_instr_type(), lhs_value_expr, rhs_value_expr);
        }
        else {
            auto icmp = dynamic_cast<CmpInst *>(instr);
            auto fcmp = dynamic_cast<FCmpInst *>(instr);
            bool is_icmp;
            unsigned op;
            if(icmp){
                is_icmp = true;
                op = icmp->get_cmp_op();
            }
            else{
                is_icmp = false;
                op = fcmp->get_cmp_op();
            }
            return CompareExpression::create(is_icmp, op, lhs_value_expr, rhs_value_expr);
        }
    }
    else if(instr->is_gep() or instr->is_call()){
        if(instr->is_call()){
            auto func = static_cast<Function*> (instr->get_operand(0));
            if(not func_info_->is_pure_function(func)){
                return nullptr;
            }
        }
        Value *ptr_func = instr->get_operand(0);
        unsigned size = instr->get_num_operand();
        std::vector<shared_ptr<Expression>> indices_operands;
        //find operands in
        for(unsigned index = 1; index < size; index++){
            Constant *operand_is_constant = dynamic_cast<Constant *>(instr->get_operand(index));
            if(operand_is_constant){
                indices_operands.push_back(ConstantExpression::create(operand_is_constant));
                continue;
            }
            bool found = false;
            for(auto cc : PIN){
                if(cc->members_.find(instr->get_operand(index)) != cc->members_.end()){
                    indices_operands.push_back(ValueNumber::create(cc->index_));
                    found = true;
                    break;
                }
            }
            if(not found){
                for(auto &[_bb, pin] : pout_){
                    for(auto cc : pin){
                        if(cc->members_.find(instr->get_operand(index)) != cc->members_.end()){
                            indices_operands.push_back(ValueNumber::create(cc->index_));
                            found = true;
                            break;
                        }
                    }
                    if(found)
                        break;
                }
            }    
        }
        return Gep_CallExpression::create(ptr_func, indices_operands);
    }
    else if(instr->is_fp2si() or instr->is_si2fp() or instr->is_zext()) {
        Type *type;
        shared_ptr<Expression> value;
        if(instr->is_fp2si()){
            FpToSiInst *fp2si = dynamic_cast<FpToSiInst*>(instr);
            type = fp2si->get_dest_type();
        }
        else if(instr->is_si2fp()){
            SiToFpInst *si2fp = dynamic_cast<SiToFpInst*>(instr);
            type = si2fp->get_dest_type();
        }
        else{
            ZextInst *zext = dynamic_cast<ZextInst*>(instr);
            type = zext->get_dest_type();
        }
        bool found = false;
        Constant *c = nullptr;
        for(auto cc : PIN){
            if(cc->members_.find(instr->get_operand(0)) != cc->members_.end()){
                value = ValueNumber::create(cc->index_);
                c = cc->constant_;
                found = true;
                break;
            }
        }
        if(not found){
            for(auto &[_bb, pin] : pout_){
                for(auto cc : pin){
                    if(cc->members_.find(instr->get_operand(0)) != cc->members_.end()){
                        value = ValueNumber::create(cc->index_);
                        c = cc->constant_;
                        found = true;
                        break;
                    }
                }
                if(found)
                    break;
            }
        }
        if(value == nullptr){
            return nullptr;
        }
        if(c){
            *constant = folder_->compute(instr, c);
        }
        return TypeCastingExpression::create(value, type);
    }
    else {
        return nullptr;
    }
}

// instruction of the form `x = e`, mostly x is just e (SSA), but for copy stmt x is a phi instruction in the
// successor. Phi values (not copy stmt) should be handled in detectEquiv
/// \param bb basic block in which the transfer function is called
GVN::partitions GVN::transferFunction(Instruction *x, Value *e, partitions pin, BasicBlock &bb) {
    partitions pout = clone(pin);

    //don't care type
    if(x->is_void())
        return pout;

    //copy statement
    if(x->is_phi()){
        //find e
        Constant *constant = nullptr;
        auto operands = x->get_operands();
        for(int i = 0; i < operands.size(); i = i + 2){
            if(operands[i + 1] == static_cast<Value*>(&bb)){  //operands[i] is value and operands[i + 1] is the basic block in which operands[i] is 
                e = operands[i];
                constant = dynamic_cast<Constant*> (e);
                break;
            }
        }
        
        //erase all occurrence of x in pout except the one where e is in the same class 
        for(auto cc = pout.begin(); cc != pout.end();){
            bool erase_cc = false;
            if((*cc)->members_.find(e) == (*cc)->members_.end()){
                if((*cc)->members_.erase(x)){
                    if((*cc)->members_.empty())
                        erase_cc = true;
                    else if(static_cast<Value*>(x) == (*cc)->leader_)
                        (*cc)->leader_ = *((*cc)->members_.begin());
                }
            }
            if(erase_cc)
                cc = pout.erase(cc);
            else 
                cc++;
        }
        bool e_found = false;
        for(auto cc : pout){
            if(constant and (constant == cc->constant_)){
                e_found = true;
                cc->members_.insert(x);
                break;
            }
            if(cc->members_.find(e) != cc->members_.end()){
                e_found = true;
                cc->members_.insert(x);
                break;
            }
        }
        if(not e_found){
            auto cc = createCongruenceClass(next_value_number_++);
            cc->leader_ = e;
            cc->members_.insert(x);
            if(constant){
                cc->value_expr_ = ConstantExpression::create(constant);
                cc->constant_ = constant;
                cc->phiConstant_ = true;
            }
            else
                cc->members_.insert(e);
            pout.insert(cc); 
        }
        return pout;
    }

    //add only 
    //instruction: alloca , load, none pure call
    //ve == null (this includes phi function)
    Constant *constant = nullptr;
    shared_ptr<Expression> ve = valueExpr(x, pin, &constant);
    if(ve == nullptr or x->is_alloca() or x->is_load()){
        for(auto cc : pout){
            if(cc->members_.find(x) != cc->members_.end())
                return pout;
        }
        auto cc = createCongruenceClass(next_value_number_++);
        cc->leader_ = x;
        cc->members_.insert(x);
        pout.insert(cc);
        return pout;
    }

    shared_ptr<PhiExpression> vpf = valuePhiFunc(ve, pin);
     //erase all occurrence of x in pout except the one where ve or vpf is in the same class 
    // for(auto cc = pout.begin(); cc != pout.end();){
    //     bool erase_cc = false;
    //     if((not ((*cc)->value_expr_ == ve)) and 
    //         ( (vpf == nullptr) or 
    //           (not (std::static_pointer_cast<Expression>((*cc)->value_phi_) == std::static_pointer_cast<Expression>(vpf))))){
    //         if((*cc)->members_.erase(x)){
    //             if((*cc)->members_.empty())
    //                 erase_cc = true;
    //             else if(static_cast<Value*>(x) == (*cc)->leader_)
    //                 (*cc)->leader_ = *((*cc)->members_.begin());
    //         }
    //     }
    //     if(erase_cc)
    //         cc = pout.erase(cc);
    //     else 
    //         cc++;     
    // }
    bool ve_is_found = false;
    for(auto cc : pout){
        if(cc->value_expr_ == ve or 
           ( vpf and 
            (std::static_pointer_cast<Expression>((cc)->value_phi_) == std::static_pointer_cast<Expression>(vpf)))){
                ve_is_found = true;
                if(constant){
                    cc->leader_ = constant;
                }
                cc->members_.insert(x);
                cc->value_expr_ = ve;
                cc->constant_ = constant;
                break;
        }
    }
    if(not ve_is_found){
        if(constant){
            e = constant;
        }
        auto cc = createCongruenceClass(next_value_number_++);
        cc->leader_ = e;
        cc->value_expr_ = ve;
        cc->value_phi_= vpf;
        cc->members_.insert(x);
        cc->constant_ = constant;
        pout.insert(cc);
    }

    return pout;
}

//note : parameter P is not used
shared_ptr<PhiExpression> GVN::valuePhiFunc(shared_ptr<Expression> ve, const partitions &P) {
    // TODO
    shared_ptr<BinaryExpression> isBinaryExpression = std::dynamic_pointer_cast<BinaryExpression>(ve);
    if(not isBinaryExpression){
        return nullptr;
    }

    shared_ptr<PhiExpression> phiExpression;
    shared_ptr<Expression> vi, vj;
    shared_ptr<ValueNumber> lhs_value_number = std::dynamic_pointer_cast<ValueNumber>(isBinaryExpression->getLhs());
    shared_ptr<ValueNumber> rhs_value_number = std::dynamic_pointer_cast<ValueNumber>(isBinaryExpression->getRhs());
    shared_ptr<PhiExpression> lhsPhiExpression;
    shared_ptr<PhiExpression> rhsPhiExpression;


    if(lhs_value_number){
        bool found = false;
        for(auto cc : P){
            if(cc->index_ == lhs_value_number->getValueNumber()){
                lhsPhiExpression = cc->value_phi_;
                found = true;
                break;
            }
        }
        // if(not found){
        //     for(auto &[_bb, pin] : pout_){
        //         for(auto cc : pin){
        //             if(cc->index_ == lhs_value_number->getValueNumber()){
        //                 lhsPhiExpression = cc->value_phi_;
        //                 found = true;
        //                 break;
        //             }
        //         }
        //         if(found)
        //             break;
        //     } 
        // }        
    }

   if(rhs_value_number){
        bool found = false;
        for(auto cc : P){
            if(cc->index_ == rhs_value_number->getValueNumber()){
                rhsPhiExpression = cc->value_phi_;
                found = true;
                break;
            }
        }
        // if(not found){
        //     for(auto &[_bb, pin] : pout_){
        //         for(auto cc : pin){
        //             if(cc->index_ == rhs_value_number->getValueNumber()){
        //                 rhsPhiExpression = cc->value_phi_;
        //                 found = true;
        //                 break;
        //             }
        //         }
        //         if(found)
        //             break;
        //     } 
        // }        
    }

    if(lhsPhiExpression and rhsPhiExpression){
        //find corresponding predecessors(left and right predecessor)
        if(lhsPhiExpression->getLbb() != rhsPhiExpression->getLbb())
            return nullptr;
        if(lhsPhiExpression->getRbb() != rhsPhiExpression->getRbb())
            return nullptr;

        auto poutkl = pout_[lhsPhiExpression->getLbb()];
        auto poutkr = pout_[lhsPhiExpression->getRbb()];

        //process left edge
        shared_ptr<Expression> vi1_vi2 = v1_v2(isBinaryExpression->getOpID(), lhsPhiExpression->getLhs(), rhsPhiExpression->getLhs());
        if(vi1_vi2 == nullptr){
            return nullptr;
        }
        vi = getVN(poutkl, vi1_vi2);
        if(vi == nullptr){
            auto Vi = valuePhiFunc(vi1_vi2, poutkl);
            if(Vi){
                bool found = false;
                for(auto cc : poutkl){
                    if(cc->value_phi_ == Vi){
                        vi = ValueNumber::create(cc->index_);
                        found = true;
                        break;
                    }
                }
                // if(not found){
                //     for(auto &[_bb, pin] : pout_){
                //         for(auto cc : pin){
                //             if(cc->value_phi_ == Vi){
                //                 vi = ValueNumber::create(cc->index_);
                //                 found = true;
                //                 break;
                //             }
                //         }
                //         if(found)
                //             break;
                //     } 
                // }        
            }
        }
        //process right edge
        shared_ptr<Expression> vj1_vj2 = v1_v2(isBinaryExpression->getOpID(), lhsPhiExpression->getRhs(), rhsPhiExpression->getRhs());
        if(vj1_vj2 == nullptr){
            return nullptr;
        }
        vj = getVN(poutkr, vj1_vj2);
        if(vj == nullptr){
            auto Vj = valuePhiFunc(vj1_vj2, poutkr);
            if(Vj){
                bool found = false;
                for(auto cc : poutkr){
                    if(cc->value_phi_ == Vj){
                        vi = ValueNumber::create(cc->index_);
                        found = true;
                        break;
                    }
                }
                // if(not found){
                //     for(auto &[_bb, pin] : pout_){
                //         for(auto cc : pin){
                //             if(cc->value_phi_ == Vj){
                //                 vi = ValueNumber::create(cc->index_);
                //                 found = true;
                //                 break;
                //             }
                //         }
                //         if(found)
                //             break;
                //     } 
                // }        
            }
        }   
    }

    if(vi and vj){
        phiExpression = PhiExpression::create(vi, vj, lhsPhiExpression->getLbb(), lhsPhiExpression->getRbb());
    }

    return phiExpression;
}

shared_ptr<Expression> GVN::getVN(const partitions &pout, shared_ptr<Expression> ve) {
    // TODO: return what?
    // auto ve_is_constant = std::dynamic_pointer_cast<ConstantExpression> (ve);
    // if(ve_is_constant)
    //     return ve;
    
    for(auto cc : pout){
        if(ve and cc->value_expr_ == ve){
            return ValueNumber::create(cc->index_);
        }
    }

    return nullptr;
}

shared_ptr<Expression> GVN::v1_v2(Instruction::OpID op, std::shared_ptr<Expression> v1, std::shared_ptr<Expression> v2){
    auto v1_is_constant = std::dynamic_pointer_cast<ConstantExpression> (v1);
    auto v2_is_constant = std::dynamic_pointer_cast<ConstantExpression> (v2);
    // if(v1_is_constant and v2_is_constant)
    //     return ConstantExpression::create(folder_->compute(op, v1_is_constant->getC(), v2_is_constant->getC()));
    if(v1_is_constant or v2_is_constant)
        return nullptr;
    else
        return BinaryExpression::create(op, v1, v2);
}

void GVN::initPerFunction() {
    next_value_number_ = 1;
    pin_.clear();
    pout_.clear();
}

//using so called "leader" to replace any other value is the set
void GVN::replace_cc_members() {
    for (auto &[_bb, part] : pout_) {
        auto bb = _bb; // workaround: structured bindings can't be captured in C++17
        for (auto &cc : part) {
            if (cc->index_ == 0)
                continue;
            // if you are planning to do constant propagation, leaders should be set to constant at some point
            for (auto &member : cc->members_) {
                bool member_is_phi = dynamic_cast<PhiInst *>(member);
                bool value_phi = cc->value_phi_ != nullptr;
                if (member != cc->leader_ and (value_phi or !member_is_phi)) {
                    // only replace the members if users are in the same block as bb or the value is used by Phi instruction in the next block
                    member->replace_use_with_when(cc->leader_, [bb](User *user) {
                        if (auto instr = dynamic_cast<Instruction *>(user)) {
                            auto parent = instr->get_parent();
                            auto &bb_pre = parent->get_pre_basic_blocks();
                            if (instr->is_phi()) // as copy stmt, the phi belongs to this block
                                return std::find(bb_pre.begin(), bb_pre.end(), bb) != bb_pre.end();
                            else
                                return parent == bb;
                        }
                        return false;
                    });
                }
            }
        }
    }
    return;
}

// top-level function, done for you
void GVN::run() {
    std::ofstream gvn_json;
    if (dump_json_) {
        gvn_json.open("gvn.json", std::ios::out);
        gvn_json << "[";
    }

    folder_ = std::make_unique<ConstFolder>(m_);
    func_info_ = std::make_unique<FuncInfo>(m_);
    func_info_->run();
    dce_ = std::make_unique<DeadCode>(m_);
    dce_->run(); // let dce take care of some dead phis with undef

    for (auto &f : m_->get_functions()) {
        if (f.get_basic_blocks().empty())
            continue;
        func_ = &f;
        initPerFunction();
        LOG_INFO << "Processing " << f.get_name();
        detectEquivalences();
        LOG_INFO << "===============pin=========================\n";
        for (auto &[bb, part] : pin_) {
            LOG_INFO << "\n===============bb: " << bb->get_name() << "=========================\npartitionIn: ";
            for (auto &cc : part)
                LOG_INFO << utils::print_congruence_class(*cc);
        }
        LOG_INFO << "\n===============pout=========================\n";
        for (auto &[bb, part] : pout_) {
            LOG_INFO << "\n=====bb: " << bb->get_name() << "=====\npartitionOut: ";
            for (auto &cc : part)
                LOG_INFO << utils::print_congruence_class(*cc);
        }
        if (dump_json_) {
            gvn_json << "{\n\"function\": ";
            gvn_json << "\"" << f.get_name() << "\", ";
            gvn_json << "\n\"pout\": " << utils::dump_bb2partition(pout_);
            gvn_json << "},";
        }
        replace_cc_members(); // don't delete instructions, just replace them
    }
    dce_->run(); // let dce do that for us
    if (dump_json_)
        gvn_json << "]";
}

template <typename T>
static bool equiv_as(const Expression &lhs, const Expression &rhs) {
    // we use static_cast because we are very sure that both operands are actually T, not other types.
    return static_cast<const T *>(&lhs)->equiv(static_cast<const T *>(&rhs));
}

bool GVNExpression::operator==(const Expression &lhs, const Expression &rhs) {
    if (lhs.get_expr_type() != rhs.get_expr_type())
        return false;
    switch (lhs.get_expr_type()) {
    case Expression::e_constant: return equiv_as<ConstantExpression>(lhs, rhs);
    case Expression::e_bin: return equiv_as<BinaryExpression>(lhs, rhs);
    case Expression::e_cmp: return equiv_as<CompareExpression>(lhs, rhs);
    case Expression::e_phi: return equiv_as<PhiExpression>(lhs, rhs);
    case Expression::e_vn: return equiv_as<ValueNumber>(lhs, rhs);
    case Expression::e_gep_call: return equiv_as<Gep_CallExpression>(lhs, rhs);
    case Expression::e_typeCast: return equiv_as<TypeCastingExpression>(lhs, rhs);
    }
}

bool GVNExpression::operator==(const shared_ptr<Expression> &lhs, const shared_ptr<Expression> &rhs) {
    if (lhs == nullptr and rhs == nullptr) // is the nullptr check necessary here?
        return true;
    return lhs and rhs and *lhs == *rhs;
}

GVN::partitions GVN::clone(const partitions &p) {
    partitions data;
    for (auto &cc : p) {
        data.insert(std::make_shared<CongruenceClass>(*cc));
    }
    return data;
}

bool CongruenceClass::operator==(const CongruenceClass &other) const {
    if(not (value_expr_ == other.value_expr_)){
        std::cout << utils::print_congruence_class(*this);
        std::cout << utils::print_congruence_class(other);
        std::cout << "value_expr failed";
        return false;
    }
    if(not (std::static_pointer_cast<Expression> (value_phi_) == std::static_pointer_cast<Expression> (other.value_phi_))){
        std::cout << utils::print_congruence_class(*this);
        std::cout << utils::print_congruence_class(other);
        std::cout << "value_phi failed";
        return false;
    }
    if(not (constant_ == other.constant_)){
        std::cout << utils::print_congruence_class(*this);
        std::cout << utils::print_congruence_class(other);
        std::cout << "constant failed";
        return false;
    }
    if(members_ != other.members_){
        std::cout << utils::print_congruence_class(*this);
        std::cout << utils::print_congruence_class(other);
        std::cout << "members failed";
        return false;
    }
    return true;
}


bool operator==(const std::shared_ptr<CongruenceClass> &lhs, const std::shared_ptr<CongruenceClass> &rhs){
    if (lhs == nullptr and rhs == nullptr)
        return true;
    return lhs and rhs and *lhs == *rhs;
}


#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CFG.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include<vector>
#include<utility>
#include<algorithm>
#include<ctime>
#include<cstdlib>
#include<iostream>
#define RAW_INST 0
#define PUSH_ADDR 1
#define STORE_IMM 2
using namespace llvm;
namespace
{
    struct VMOpInfo
    {
        int opcode;
        int builtin_type=RAW_INST;
        std::vector<std::pair<int,Value*>> opnds;
        union
        {
            Instruction *instr=nullptr;
            int store_size;
        };
        
    };
	struct LLVMVM : public ModulePass
	{
    	static char ID;
        std::vector<Function*> vm_funcs;
        std::map<Function*,Function*> vm_mapping;
   		LLVMVM() : ModulePass(ID) {}
        void getAnalysisUsage(AnalysisUsage &AU) const override
		{
			errs()<<"Require LowerSwitchPass\n";
			AU.addRequiredID(LowerSwitchID);
			ModulePass::getAnalysisUsage(AU);
		}
        void demoteRegisters(Function *f);
        BasicBlock* handleAlloca(Function &f,std::map<Value*,int> &value_map,std::vector<std::pair<int,int>> &remap,int &space);
        Function* virtualization(Function &f);
        VMOpInfo *getOrCreateRawOp(Instruction &instr,std::vector<VMOpInfo*> &ops,int &cur_op);
        bool check(Function &f);
        void FixCallInst(Function *target,Function *orig);
        void createBuiltinOps(std::vector<VMOpInfo*> &ops,int &cur_op);
        std::string readAnnotate(Function *f);
        void buildVMFunction(Function &f,Function &vm,std::vector<VMOpInfo*> &ops,int mem_size,GlobalVariable *opcodes,int tmp_size,std::vector<std::pair<int,int>> &remap,std::map<Value*,int> &value_map);
        int generateOpcodes(std::vector<BasicBlock*> &code,std::map<Value*,int> &locals_addr_map,std::map<Instruction*,VMOpInfo*> &instr_map,std::vector<VMOpInfo*> &ops,int mem_size,std::vector<Constant *> &opcodes);
        int allocaMemory(BasicBlock &bb,std::map<Instruction*,int> &alloca_map,int mem_base);
   		bool runOnModule(Module &m) override
		{
            std::vector<Function*> removed;
            for(Function &f:m)
            {
                bool is_vm=false;
                for(Function *ff:vm_funcs)
                {
                    if(&f==ff)
                    {
                        is_vm=true;
                        break;
                    }
                        
                }
                if(!is_vm && f.hasExactDefinition() && !readAnnotate(&f).find("virtualization"))
                {
                    Function *vmfunc=virtualization(f);
                    if(vmfunc!=NULL)
                    {
                        vm_funcs.push_back(vmfunc);
                        FixCallInst(vmfunc,&f);
                    }
                        
                }
            }
			return false;
    	}
  	};
}
std::string LLVMVM::readAnnotate(Function *f)
{
    std::string annotation = "";
    /* Get annotation variable */
    GlobalVariable *glob=f->getParent()->getGlobalVariable( "llvm.global.annotations" );
    if ( glob != NULL )
    {
        /* Get the array */
        if ( ConstantArray * ca = dyn_cast<ConstantArray>( glob->getInitializer() ) )
        {
            for ( unsigned i = 0; i < ca->getNumOperands(); ++i )
            {
                /* Get the struct */
                if ( ConstantStruct * structAn = dyn_cast<ConstantStruct>( ca->getOperand( i ) ) )
                {
                    if ( ConstantExpr * expr = dyn_cast<ConstantExpr>( structAn->getOperand( 0 ) ) )
                    {
                        /*
                            * If it's a bitcast we can check if the annotation is concerning
                            * the current function
                            */
                        if ( expr->getOpcode() == Instruction::BitCast && expr->getOperand( 0 ) == f )
                        {
                            ConstantExpr *note = cast<ConstantExpr>( structAn->getOperand( 1 ) );
                            /*
                                * If it's a GetElementPtr, that means we found the variable
                                * containing the annotations
                                */
                            if ( note->getOpcode() == Instruction::GetElementPtr )
                            {
                                if ( GlobalVariable * annoteStr = dyn_cast<GlobalVariable>( note->getOperand( 0 ) ) )
                                {
                                    if ( ConstantDataSequential * data = dyn_cast<ConstantDataSequential>( annoteStr->getInitializer() ) )
                                    {
                                        if ( data->isString() )
                                        {
                                            annotation += data->getAsString().lower() + " ";
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    return(annotation);
}
void LLVMVM::demoteRegisters(Function *f)
{
    std::vector<PHINode *> tmpPhi;
    std::vector<Instruction *> tmpReg;
    BasicBlock *bbEntry = &*f->begin();
    do
    {
        tmpPhi.clear();
        tmpReg.clear();
        for(Function::iterator i=f->begin();i!=f->end();i++)
        {
            for(BasicBlock::iterator j=i->begin();j!=i->end();j++)
            {
                if(isa<PHINode>(j)) 
                {
                    PHINode *phi=cast<PHINode>(j);
                    tmpPhi.push_back(phi);
                    continue;
                }
                if (!(isa<AllocaInst>(j) && j->getParent()==bbEntry) && j->isUsedOutsideOfBlock(&*i))
                {
                    tmpReg.push_back(&*j);
                    continue;
                }
            }
        }
        for(unsigned int i=0;i<tmpReg.size();i++)
            DemoteRegToStack(*tmpReg.at(i),f->begin()->getTerminator());
        for(unsigned int i=0;i<tmpPhi.size();i++)
            DemotePHIToStack(tmpPhi.at(i),f->begin()->getTerminator());
    }
    while(tmpReg.size()!= 0 || tmpPhi.size()!= 0);
} 
BasicBlock* LLVMVM::handleAlloca(Function &f,std::map<Value*,int> &value_map,std::vector<std::pair<int,int>> &remap,int &space)
{
    std::vector<AllocaInst*> allocas;
    printf("    -collect allocainst\n");
    for(BasicBlock &bb:f)
        for(Instruction &i:bb)
        {
            if(isa<AllocaInst>(i))
                allocas.push_back((AllocaInst*)&i);
        }
    BasicBlock *alloca_block=&f.getEntryBlock();
    printf("    -move allocainst before\n");
    for(AllocaInst* a:allocas)
        a->moveBefore(&*alloca_block->getFirstInsertionPt());
    printf("    -split allocainst block\n");
    for(Instruction &i:*alloca_block)
    {
        if(!isa<AllocaInst>(i))
        {
            alloca_block->splitBasicBlock(&i);
            break;
        }
    }
    printf("    -calculate locals address\n");
    DataLayout data=f.getParent()->getDataLayout();
    for(AllocaInst* a:allocas)
    {
        int real_addr=space;
        printf("   [%4d] alloc size %d\n",real_addr,data.getTypeAllocSize(a->getAllocatedType()));
        space+=data.getTypeAllocSize(a->getAllocatedType());
        int ptr_addr=space;
        value_map[a]=space;
        printf("   [%4d] store ptr size %d\n",ptr_addr,data.getTypeAllocSize(a->getType()));
        space+=data.getTypeAllocSize(a->getType());
        remap.push_back(std::make_pair(ptr_addr,real_addr));
    }
    
    return alloca_block;
    
}
void findOperand(Instruction &instr,std::vector<std::pair<int,Value*>> &operand,std::vector<std::pair<int,Value*>> &unsupported)
{
    int i=0;
    for(Value *opnd:instr.operands())
    {
        if(isa<ConstantInt>(*opnd)/* || isa<ConstantFP>(*opnd)*/ || isa<Instruction>(*opnd) || isa<Argument>(*opnd))
            operand.push_back(std::make_pair(i,(GlobalVariable*)opnd));
        else
            unsupported.push_back(std::make_pair(i,(GlobalVariable*)opnd));
        i++;
    }
}
VMOpInfo *LLVMVM::getOrCreateRawOp(Instruction &instr,std::vector<VMOpInfo*> &ops,int &cur_op)
{
    if(instr.getOpcode()==Instruction::Br)
    {
        for(VMOpInfo *info:ops) 
        {
            if(info->instr->getOpcode()==Instruction::Br)
                return info;
        }
        VMOpInfo *news=new VMOpInfo();
        news->opcode=cur_op++;
        news->instr=&instr;
        ops.push_back(news);
        return news;
    }
    else
    {
        std::vector<std::pair<int,Value*>> operand1,un1;
        findOperand(instr,operand1,un1);
        for(VMOpInfo *info:ops) 
        {
            if(info->instr!=nullptr && info->instr->isSameOperationAs(&instr))
            {
                if(un1.size()==0)
                    return info;
                else
                {
                    std::vector<std::pair<int,Value*>> operand2,un2;
                    findOperand(*info->instr,operand2,un2);
                    if(un1.size()!=un2.size())
                        continue;
                    bool ok=true;
                    for(int i=0;i<un1.size();i++)
                    {
                        if(un1[i]!=un2[i])
                        {
                            ok=false;
                            break;
                        }
                    }
                    if(ok)
                        return info;
                }
            }
        }
        VMOpInfo *news=new VMOpInfo();
        news->opcode=cur_op++;
        news->instr=&instr;
        for(int i=0;i<operand1.size();i++)
            news->opnds.push_back(operand1.at(i));
        ops.push_back(news);
        return news;
    }
    
}
bool LLVMVM::check(Function &f)
{
    for(BasicBlock &bb:f)
        for(Instruction &i:bb)
        {
            if((i.isTerminator() && !isa<BranchInst>(i) && !isa<ReturnInst>(i)) || i.isFuncletPad())
            {
                printf("[!] Unsupported Instruction Type: %s\n",i.getOpcodeName());
                return false;
            }
        }
    return true;
}
void LLVMVM::createBuiltinOps(std::vector<VMOpInfo*> &ops,int &cur_op)
{
    VMOpInfo *push_addr=new VMOpInfo();
    push_addr->opcode=cur_op++;
    push_addr->builtin_type=PUSH_ADDR;
    VMOpInfo *store_1b=new VMOpInfo();
    store_1b->opcode=cur_op++;
    store_1b->builtin_type=STORE_IMM;
    store_1b->store_size=1;
    VMOpInfo *store_2b=new VMOpInfo();
    store_2b->opcode=cur_op++;
    store_2b->builtin_type=STORE_IMM;
    store_2b->store_size=2;
    VMOpInfo *store_4b=new VMOpInfo();
    store_4b->opcode=cur_op++;
    store_4b->builtin_type=STORE_IMM;
    store_4b->store_size=4;
    VMOpInfo *store_8b=new VMOpInfo();
    store_8b->opcode=cur_op++;
    store_8b->builtin_type=STORE_IMM;
    store_8b->store_size=8;
    ops.push_back(push_addr);
    ops.push_back(store_1b);
    ops.push_back(store_2b);
    ops.push_back(store_4b);
    ops.push_back(store_8b);
}
void LLVMVM::buildVMFunction(Function &f,Function &vm,std::vector<VMOpInfo*> &ops,int mem_size,GlobalVariable *opcodes,int addr_stack_size,std::vector<std::pair<int,int>> &remap,std::map<Value*,int> &value_map)
{
    assert(ops.size()<=255);
    BasicBlock *entry=BasicBlock::Create(vm.getContext(),"entry",&vm);
    BasicBlock *dispatch=BasicBlock::Create(vm.getContext(),"dispatch",&vm);
    BasicBlock *loop_end=BasicBlock::Create(vm.getContext(),"loopend",&vm);
    IRBuilder<> irb(entry);
    Value *pc=irb.CreateAlloca(irb.getInt32Ty());
    Value *memory=irb.CreateAlloca(ArrayType::get(irb.getInt8Ty(),mem_size));
    Value *addr_stack=irb.CreateAlloca(ArrayType::get(irb.getInt32Ty(),addr_stack_size));
    Value *ptr=irb.CreateAlloca(irb.getInt32Ty());
    
    //initial for locals
    printf("-  initial for locals\n");
    for(std::pair<int,int> p:remap)
    {
        int ptr_addr=p.first,real_addr=p.second;
        Value *ptr=irb.CreateGEP(memory,{irb.getInt32(0),irb.getInt32(real_addr)});
        Value *to_store=irb.CreateGEP(memory,{irb.getInt32(0),irb.getInt32(ptr_addr)});
        irb.CreateStore(ptr,irb.CreateBitCast(to_store,ptr->getType()->getPointerTo()));
    }
    //initial for arguments
    Function::arg_iterator real_iter=vm.arg_begin();
    for(Function::arg_iterator iter=f.arg_begin();iter!=f.arg_end();iter++)
    {
        Value *arg=&*iter;
        Value *real_arg=&*real_iter;
        assert(value_map.count(arg)!=0);
        int addr=value_map[arg];
        Value *to_store=irb.CreateGEP(memory,{irb.getInt32(0),irb.getInt32(addr)});
        irb.CreateStore(real_arg,irb.CreateBitCast(to_store,real_arg->getType()->getPointerTo()));
        real_iter++;
    }

    irb.CreateStore(irb.getInt32(0),pc);
    irb.CreateStore(irb.getInt32(0),ptr);
    BranchInst::Create(dispatch,entry);
    irb.SetInsertPoint(dispatch);
    Value *opvalue=irb.CreateLoad(irb.CreateGEP(opcodes,{irb.getInt32(0),irb.CreateLoad(pc)}));
    irb.CreateStore(irb.CreateAdd(irb.CreateLoad(pc),irb.getInt32(1)),pc);
    SwitchInst *dispatcher=SwitchInst::Create(opvalue,loop_end,0,dispatch);
    bool has_br=false;
    for(VMOpInfo* op:ops)
    {
        if(op->builtin_type)
        {
            if(op->builtin_type==PUSH_ADDR)
            {
                BasicBlock *handler=BasicBlock::Create(vm.getContext(),"push_addr",&vm);
                dispatcher->addCase(irb.getInt8(op->opcode),handler);
                irb.SetInsertPoint(handler);
                Value *vpc=irb.CreateLoad(pc);
                Value *vptr=irb.CreateLoad(ptr);
                Value *addr=irb.CreateLoad(irb.CreateBitCast(irb.CreateGEP(opcodes,{irb.getInt32(0),vpc}),irb.getInt32Ty()->getPointerTo()));
                irb.CreateStore(addr,irb.CreateGEP(addr_stack,{irb.getInt32(0),vptr}));
                irb.CreateStore(irb.CreateAdd(vptr,irb.getInt32(1)),ptr);
                irb.CreateStore(irb.CreateAdd(vpc,irb.getInt32(4)),pc);
                BranchInst::Create(loop_end,handler);
                handler->moveBefore(loop_end);
            }
            else if(op->builtin_type==STORE_IMM)
            {
                
                if(op->store_size==1)
                {
                    BasicBlock *handler=BasicBlock::Create(vm.getContext(),"store_imm1",&vm);
                    irb.SetInsertPoint(handler);
                    dispatcher->addCase(irb.getInt8(op->opcode),handler);
                    Value *vpc=irb.CreateLoad(pc);
                    Value *vptr=irb.CreateLoad(ptr);
                    Value *imm=irb.CreateLoad(irb.CreateGEP(opcodes,{irb.getInt32(0),vpc}));
                    Value *addr=irb.CreateLoad(irb.CreateGEP(addr_stack,{irb.getInt32(0),irb.CreateSub(vptr,irb.getInt32(1))}));
                    irb.CreateStore(imm,irb.CreateGEP(memory,{irb.getInt32(0),addr}));
                    
                    irb.CreateStore(irb.CreateSub(vptr,irb.getInt32(1)),ptr);
                    irb.CreateStore(irb.CreateAdd(vpc,irb.getInt32(1)),pc);
                    BranchInst::Create(loop_end,handler);
                    handler->moveBefore(loop_end);
                }
                else if(op->store_size==2)
                {
                    BasicBlock *handler=BasicBlock::Create(vm.getContext(),"store_imm2",&vm);
                    irb.SetInsertPoint(handler);
                    dispatcher->addCase(irb.getInt8(op->opcode),handler);
                    Value *vpc=irb.CreateLoad(pc);
                    Value *vptr=irb.CreateLoad(ptr);
                    Value *imm=irb.CreateLoad(irb.CreateBitCast(irb.CreateGEP(opcodes,{irb.getInt32(0),vpc}),irb.getInt16Ty()->getPointerTo()));

                    Value *addr=irb.CreateLoad(irb.CreateGEP(addr_stack,{irb.getInt32(0),irb.CreateSub(vptr,irb.getInt32(1))}));
                    irb.CreateStore(imm,irb.CreateBitCast(irb.CreateGEP(memory,{irb.getInt32(0),addr}),irb.getInt16Ty()->getPointerTo()));

                    irb.CreateStore(irb.CreateSub(vptr,irb.getInt32(1)),ptr);
                    irb.CreateStore(irb.CreateAdd(vpc,irb.getInt32(2)),pc);
                    BranchInst::Create(loop_end,handler);
                    handler->moveBefore(loop_end);
                }
                else if(op->store_size==4)
                {
                    BasicBlock *handler=BasicBlock::Create(vm.getContext(),"store_imm4",&vm);
                    irb.SetInsertPoint(handler);
                    dispatcher->addCase(irb.getInt8(op->opcode),handler);
                    Value *vpc=irb.CreateLoad(pc);
                    Value *vptr=irb.CreateLoad(ptr);
                    Value *imm=irb.CreateLoad(irb.CreateBitCast(irb.CreateGEP(opcodes,{irb.getInt32(0),vpc}),irb.getInt32Ty()->getPointerTo()));

                    Value *addr=irb.CreateLoad(irb.CreateGEP(addr_stack,{irb.getInt32(0),irb.CreateSub(vptr,irb.getInt32(1))}));
                    irb.CreateStore(imm,irb.CreateBitCast(irb.CreateGEP(memory,{irb.getInt32(0),addr}),irb.getInt32Ty()->getPointerTo()));

                    irb.CreateStore(irb.CreateSub(vptr,irb.getInt32(1)),ptr);
                    irb.CreateStore(irb.CreateAdd(vpc,irb.getInt32(4)),pc);
                    BranchInst::Create(loop_end,handler);
                    handler->moveBefore(loop_end);
                }
                else
                {
                    BasicBlock *handler=BasicBlock::Create(vm.getContext(),"store_imm8",&vm);
                    irb.SetInsertPoint(handler);
                    dispatcher->addCase(irb.getInt8(op->opcode),handler);
                    Value *vpc=irb.CreateLoad(pc);
                    Value *vptr=irb.CreateLoad(ptr);
                    Value *imm=irb.CreateLoad(irb.CreateBitCast(irb.CreateGEP(opcodes,{irb.getInt32(0),vpc}),irb.getInt64Ty()->getPointerTo()));

                    Value *addr=irb.CreateLoad(irb.CreateGEP(addr_stack,{irb.getInt32(0),irb.CreateSub(vptr,irb.getInt32(1))}));
                    irb.CreateStore(imm,irb.CreateBitCast(irb.CreateGEP(memory,{irb.getInt32(0),addr}),irb.getInt64Ty()->getPointerTo()));

                    irb.CreateStore(irb.CreateSub(vptr,irb.getInt32(1)),ptr);
                    irb.CreateStore(irb.CreateAdd(vpc,irb.getInt32(8)),pc);
                    BranchInst::Create(loop_end,handler);
                    handler->moveBefore(loop_end);
                }
            }
            else
                assert(false && "Unknow builtin op type!");
        }
        else
        {
            if(op->instr->getOpcode()==Instruction::Br)
            {
                if(!has_br)
                {
                    BasicBlock *handler=BasicBlock::Create(vm.getContext(),Twine("branch"),&vm);
                    irb.SetInsertPoint(handler);
                    dispatcher->addCase(irb.getInt8(op->opcode),handler);
                    Value *vpc=irb.CreateLoad(pc);
                    Value *vptr=irb.CreateLoad(ptr);
                    Value *cond_addr=irb.CreateLoad(irb.CreateGEP(addr_stack,{irb.getInt32(0),irb.CreateSub(vptr,irb.getInt32(1))}));
                    Value *cond=irb.CreateLoad(irb.CreateBitCast(irb.CreateGEP(memory,{irb.getInt32(0),cond_addr}),irb.getInt1Ty()->getPointerTo()));
                    Value *jmp_offset=irb.CreateLoad(irb.CreateBitCast(irb.CreateGEP(opcodes,{irb.getInt32(0),vpc}),irb.getInt32Ty()->getPointerTo()));
                    Value *final_offset=irb.CreateSelect(cond,jmp_offset,irb.getInt32(4));
                    irb.CreateStore(irb.CreateAdd(vpc,final_offset),pc);
                    irb.CreateStore(irb.CreateSub(vptr,irb.getInt32(1)),ptr);
                    BranchInst::Create(loop_end,handler);
                    handler->moveBefore(loop_end);
                    has_br=true;
                }
                
            }
            else
            {
                BasicBlock *handler=BasicBlock::Create(vm.getContext(),Twine("handler_")+op->instr->getOpcodeName(),&vm);
                irb.SetInsertPoint(handler);
                dispatcher->addCase(irb.getInt8(op->opcode),handler);
                Value *vpc=irb.CreateLoad(pc);
                Value *vptr=irb.CreateLoad(ptr);
                Instruction *target=op->instr->clone();
                Value *pos=vptr;
                int arg_num=op->opnds.size();
                for(int i=0;i<arg_num;i++)
                {
                    std::pair<int,Value*> p=op->opnds[i];
                    Value *arg_addr=irb.CreateLoad(irb.CreateGEP(addr_stack,{irb.getInt32(0),irb.CreateSub(vptr,irb.getInt32(arg_num-i))}));
                    Value *arg=irb.CreateLoad(irb.CreateBitCast(irb.CreateGEP(memory,{irb.getInt32(0),arg_addr}),p.second->getType()->getPointerTo()));
                    target->setOperand(p.first,arg);
                    pos=arg;
                }
                target->insertAfter((Instruction*)pos);
                if(target->getOpcode()==Instruction::Ret)
                {
                    handler->moveBefore(loop_end);
                    continue;
                }
                
                if(!target->getType()->isVoidTy())
                {
                    Value *to_store=irb.CreateLoad(irb.CreateBitCast(irb.CreateGEP(opcodes,{irb.getInt32(0),vpc}),irb.getInt32Ty()->getPointerTo()));
                    irb.CreateStore(target,irb.CreateBitCast(irb.CreateGEP(memory,{irb.getInt32(0),to_store}),target->getType()->getPointerTo()));
                    irb.CreateStore(irb.CreateAdd(vpc,irb.getInt32(4)),pc);
                }
                irb.CreateStore(irb.CreateSub(vptr,irb.getInt32(arg_num)),ptr);
                BranchInst::Create(loop_end,handler);
                handler->moveBefore(loop_end);
            }
        }
    }
    BranchInst::Create(dispatch,loop_end);
}
bool cmp(std::pair<Instruction*,int> &a, std::pair<Instruction*,int> &b)
{
    return a.second<b.second;
}
int LLVMVM::allocaMemory(BasicBlock &bb,std::map<Instruction*,int> &alloca_map,int mem_base)
{
    int max_space=0;
    DataLayout data=bb.getParent()->getParent()->getDataLayout();
    std::map<Instruction*,std::set<Instruction*>*> alive;
    for(Instruction &i:bb)
    {
        if(alive.count(&i)==0)
        {
            std::set<Instruction*> *instr_set=new std::set<Instruction*>;
            alive[&i]=instr_set;
        }
    }
    for(Instruction &i:bb)
    {
        if(i.isUsedOutsideOfBlock(&bb))
            assert(false && "Impossible: value escaped");
        for(Value *opnd:i.operands())
        {
            if(isa<Instruction>(*opnd) && !isa<AllocaInst>(*opnd))
            {
                Instruction* instr=(Instruction*)opnd;
                if(instr->getParent()!=&bb)
                    assert(false && "Impossible: value escaped");
                BasicBlock::iterator start=instr->getIterator(),end=i.getIterator();
                ++end;
                for(BasicBlock::iterator iter=++start;iter!=end;iter++)
                {
                    Instruction *ii=&*iter;
                    alive[ii]->insert(instr);
                }
            }
            
        }
    }
    /*for(Instruction &i:bb)
    {
        printf("current opname: %s\n\t",i.getOpcodeName());
        if(alive[&i]->size()==0)
            printf("null");
        for(std::set<Instruction*>::iterator iter=alive[&i]->begin();iter!=alive[&i]->end();iter++)
            printf("%s ",(*iter)->getOpcodeName());
        printf("\n");
    }*/
    //printf("value remain!\n");
    std::vector<std::pair<Instruction*,int>> current_alloc;
    for(Instruction &i:bb)
    {
        std::vector<std::pair<Instruction*,int>> freed;
        for(std::vector<std::pair<Instruction*,int>>::iterator iter=current_alloc.begin();iter!=current_alloc.end();iter++)
        {
            std::pair<Instruction*,int> p=*iter;
            bool find=false;
            for(std::set<Instruction*>::iterator iter=alive[&i]->begin();iter!=alive[&i]->end();iter++)
            {
                if(p.first==*iter)
                {
                    find=true;
                    break;
                }
            }
            if(!find)
            {
                //printf("    free value opcode: %s\n",p.first->getOpcodeName());
                freed.push_back(p);
            }
                
        }
        for(std::pair<Instruction*,int> pp:freed)
        {
            for(std::vector<std::pair<Instruction*,int>>::iterator iter=current_alloc.begin();iter!=current_alloc.end();iter++)
            {
                std::pair<Instruction*,int> p=*iter;
                if(p==pp)
                {
                    current_alloc.erase(iter);
                    break;
                }
            }
            
        }
            
        //printf("2 --------- %s\n",i.getOpcodeName());
        //printf("    allocated value num: %d\n",current_alloc.size());
        sort(current_alloc,cmp);
        for(std::vector<std::pair<Instruction*,int>>::iterator iter=current_alloc.begin();iter!=current_alloc.end();iter++)
        {
            std::pair<Instruction*,int> p=*iter;
            //printf("    > value %s at addr %d\n",p.first->getOpcodeName(),p.second+mem_base);
        }
        //printf("free ok %d!\n",freed.size());
        if(!i.getType()->isVoidTy())
        {
            //printf("    this instruction need space %d\n",data.getTypeAllocSize(i.getType()));
            std::vector<std::pair<Instruction*,int>>::iterator ptr=current_alloc.begin(),prev;
            while(ptr!=current_alloc.end())
            {
                int space,addr;
                std::pair<Instruction*,int> cur=*ptr;
                if(ptr!=current_alloc.begin())
                {
                    addr=prev->second+data.getTypeAllocSize(prev->first->getType());
                    space=cur.second-addr;
                }
                else
                {
                    addr=0;
                    space=cur.second;
                }
                if(space>=data.getTypeAllocSize(i.getType()))
                {
                    //printf("    find free space\n");
                    current_alloc.insert(ptr,std::make_pair(&i,addr));
                    alloca_map[&i]=addr+mem_base;
                    break;
                }
                prev=ptr;
                ptr++;
            }
            if(ptr==current_alloc.end())
            {
                //printf("    no free space,alloca new space\n");
                int addr;
                if(current_alloc.size()!=0)
                    addr=prev->second+data.getTypeAllocSize(prev->first->getType());
                else
                    addr=0;
                int bound=addr+data.getTypeAllocSize(i.getType());
                max_space=max_space>bound?max_space:bound;
                current_alloc.push_back(std::make_pair(&i,addr));
                alloca_map[&i]=addr+mem_base;
            }
        }
        //if(alloca_map.count(&i)>0)
            //printf("    [~] value addr: %d\n",alloca_map[&i]);
            
    }
    //printf("-----after alloca max_space %d\n",max_space+mem_base);
    for(Instruction &i:bb)
        delete alive[&i];
    return max_space+mem_base;
}
void pushBytes(unsigned char* ptr,int size,std::vector<unsigned char> &buffer)
{
    for(int i=0;i<size;i++)
        buffer.push_back(ptr[i]);
}
int queryAddr(Value *v,std::map<Value*,int> &locals_addr_map,std::map<Instruction*,int> &reg_addr_map)
{
    int addr;
    if(locals_addr_map.count(v)!=0)
        return locals_addr_map[v];
    else if(reg_addr_map.count((Instruction*)v)!=0)
        return reg_addr_map[(Instruction*)v];
    else
        assert(false && "Unknown value!");
}
unsigned char findStoreImmOp(std::vector<VMOpInfo*> &ops,int store_size)
{
    for(VMOpInfo *op:ops)
    {
        if(op->builtin_type==STORE_IMM && op->store_size==store_size)
            return op->opcode;
    }
    assert(false);
}
unsigned char findPushAddrOp(std::vector<VMOpInfo*> &ops)
{
    for(VMOpInfo *op:ops)
    {
        if(op->builtin_type==PUSH_ADDR)
            return op->opcode;
    }
    assert(false);
}
unsigned char findBranchOp(std::vector<VMOpInfo*> &ops)
{
    for(VMOpInfo *op:ops)
    {
        if(op->instr->getOpcode()==Instruction::Br)
            return op->opcode;
    }
    assert(false);
}
int LLVMVM::generateOpcodes(std::vector<BasicBlock*> &code,std::map<Value*,int> &locals_addr_map,std::map<Instruction*,VMOpInfo*> &instr_map,std::vector<VMOpInfo*> &ops,int mem_size,std::vector<Constant *> &opcodes)
{
    if(code.size()==0)
        return mem_size;
    std::vector<unsigned char> opcodes_raw;
    int new_mem_size=mem_size;
    LLVMContext *context=&code[0]->getContext();
    std::vector<std::pair<int,BasicBlock*>> br_to_fix;
    std::map<BasicBlock*,int> block_addr; 
    unsigned char store1_op=findStoreImmOp(ops,1);
    unsigned char store2_op=findStoreImmOp(ops,2);
    unsigned char store4_op=findStoreImmOp(ops,4);
    unsigned char store8_op=findStoreImmOp(ops,8);
    unsigned char push_addr_op=findPushAddrOp(ops);
    for(int i=0;i<code.size();i++)
    {
        BasicBlock *bb=code[i];
        DataLayout data=bb->getParent()->getParent()->getDataLayout();
        int cur_addr=opcodes_raw.size();
        block_addr[bb]=cur_addr;
        std::map<Instruction*,int> reg_addr_map;
        int allocated_space=allocaMemory(*bb,reg_addr_map,mem_size);
        int max_used_space=allocated_space;
        for(Instruction &instr:*bb)
        {
            assert(instr_map.count(&instr)!=0);
            VMOpInfo *op=instr_map[&instr];
            int used_space=allocated_space;
            if(isa<BranchInst>(instr))
            {

                BranchInst *br=(BranchInst*)&instr;
                unsigned char br_op=findBranchOp(ops);
                if(br->isConditional())
                {
                    Value *cond=br->getCondition();
                    assert(cond->getType()==Type::getInt1Ty(*context));
                    int addr=queryAddr(cond,locals_addr_map,reg_addr_map);
                    int empty=0xdeadbeef;
                    // push addr
                    printf("%-6d",opcodes_raw.size());
                    opcodes_raw.push_back(push_addr_op);
                    pushBytes((unsigned char*)&addr,4,opcodes_raw);
                    printf("push addr=[%d]\n",addr);
                    // br offset
                    printf("%-6d",opcodes_raw.size());
                    br_to_fix.push_back(std::make_pair(opcodes_raw.size(),br->getSuccessor(0)));     
                    opcodes_raw.push_back(br_op);
                    pushBytes((unsigned char*)&empty,4,opcodes_raw);
                    printf("branch offset=%d\n",empty);
                    
                    
                    if(i==code.size()-1 || code[i+1]!=br->getSuccessor(1))              
                    {
                        int true_value=1;
                        //push addr
                        printf("%-6d",opcodes_raw.size());
                        opcodes_raw.push_back(push_addr_op);
                        pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                        printf("push addr=[%d]\n",used_space);
                        //store 1
                        printf("%-6d",opcodes_raw.size());
                        opcodes_raw.push_back(store1_op);
                        pushBytes((unsigned char*)&true_value,1,opcodes_raw);
                        printf("store imm1=%d\n",1);
                        //push addr
                        printf("%-6d",opcodes_raw.size());
                        opcodes_raw.push_back(push_addr_op);
                        pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                        printf("push addr=[%d]\n",used_space);
                        //br offset
                        br_to_fix.push_back(std::make_pair(opcodes_raw.size(),br->getSuccessor(1)));
                        printf("%-6d",opcodes_raw.size());
                        opcodes_raw.push_back(br_op);
                        pushBytes((unsigned char*)&empty,4,opcodes_raw);
                        printf("branch offset=%d\n",empty);
                        used_space+=1;                          
                    }
                    
                }
                else                                                                        
                {
                    if(i==code.size()-1 || code[i+1]!=br->getSuccessor(0))
                    {
                        int true_value=1;
                        int empty=0xdeadbeef;
                        //push addr
                        printf("%-6d",opcodes_raw.size());
                        opcodes_raw.push_back(push_addr_op);
                        pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                        printf("push addr=[%d]\n",used_space);
                        //store 1
                        printf("%-6d",opcodes_raw.size());
                        opcodes_raw.push_back(store1_op);
                        pushBytes((unsigned char*)&true_value,1,opcodes_raw);
                        printf("store imm1=%d\n",1);
                        //push addr
                        printf("%-6d",opcodes_raw.size());
                        opcodes_raw.push_back(push_addr_op);
                        pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                        printf("push addr=[%d]\n",used_space);
                        //br offset
                        printf("%-6d",opcodes_raw.size());
                        br_to_fix.push_back(std::make_pair(opcodes_raw.size(),br->getSuccessor(0)));
                        opcodes_raw.push_back(br_op);
                        pushBytes((unsigned char*)&empty,4,opcodes_raw);
                        printf("branch offset=%d\n",empty);
                        used_space+=1;
                    }   
                    
                }
            }
            else
            {
                VMOpInfo *vmop=instr_map[&instr];
                for(std::pair<int,Value*> p:vmop->opnds)
                {
                    Value *op=instr.getOperand(p.first);
                    if(isa<ConstantInt>(*op)/* || isa<ConstantFP>(op)*/)
                    {
                        ConstantInt *val=(ConstantInt*)op;
                        int store_size=data.getTypeAllocSize(val->getType());
                        if(store_size==1)
                        {
                            //push addr
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(push_addr_op);
                            pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                            printf("push addr=[%d]\n",used_space);
                            
                            //store value
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(store1_op);
                            unsigned char r=val->getZExtValue()&0xff;
                            pushBytes((unsigned char*)&r,1,opcodes_raw);
                            printf("store imm1=%d\n",r);
                            
                            //push addr
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(push_addr_op);
                            pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                            printf("push addr=[%d]\n",used_space);
                            used_space+=1;
                            
                        }
                        else if(store_size==2)
                        {
                            //push addr
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(push_addr_op);
                            pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                            printf("push addr=[%d]\n",used_space);
                            
                            //store value
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(store2_op);
                            unsigned short r=val->getZExtValue()&0xff;
                            pushBytes((unsigned char*)&r,2,opcodes_raw);
                            printf("store imm2=%d\n",r);
                            
                            //push addr
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(push_addr_op);
                            pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                            printf("push addr=[%d]\n",used_space);
                            used_space+=2;
                        }
                        else if(store_size==4)
                        {
                            //push addr
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(push_addr_op);
                            pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                            printf("push addr=[%d]\n",used_space);
                            
                            //store value
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(store4_op);
                            unsigned int r=val->getZExtValue();
                            pushBytes((unsigned char*)&r,4,opcodes_raw);
                            printf("store imm4=%d\n",r);
                            
                            //push addr
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(push_addr_op);
                            pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                            printf("push addr=[%d]\n",used_space);
                            used_space+=4;
                        }
                        else if(store_size==8)
                        {
                            //push addr
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(push_addr_op);
                            pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                            printf("push addr=[%d]\n",used_space);
                            
                            //store value
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(store8_op);
                            unsigned long long r=val->getZExtValue();
                            pushBytes((unsigned char*)&r,8,opcodes_raw);
                            printf("store imm8=%lld\n",r);
                            
                            //push addr
                            printf("%-6d",opcodes_raw.size());
                            opcodes_raw.push_back(push_addr_op);
                            pushBytes((unsigned char*)&used_space,4,opcodes_raw);
                            printf("push addr=[%d]\n",used_space);
                            used_space+=8;
                        }
                        else
                            assert(false);
                    }
                    else
                    {
                        int addr=queryAddr(op,locals_addr_map,reg_addr_map);
                        //push addr
                        printf("%-6d",opcodes_raw.size());
                        opcodes_raw.push_back(push_addr_op);
                        pushBytes((unsigned char*)&addr,4,opcodes_raw);
                        printf("push addr=[%d]\n",addr);
                    }
                    
                }
                
                if(!instr.getType()->isVoidTy())
                {
                    //handler addr
                    
                    int addr=queryAddr(&instr,locals_addr_map,reg_addr_map);
                    printf("%-6d",opcodes_raw.size());
                    opcodes_raw.push_back(vmop->opcode);
                    pushBytes((unsigned char*)&addr,4,opcodes_raw);
                    printf("handler_%d st=[%d] name=%s\n",vmop->opcode,addr,vmop->instr->getOpcodeName());
                }
                else
                {
                    //handler
                    printf("%-6d",opcodes_raw.size());
                    opcodes_raw.push_back(vmop->opcode);
                    printf("handler_%d name=%s\n",vmop->opcode,vmop->instr->getOpcodeName());
                }
            }
            max_used_space=max_used_space>used_space?max_used_space:used_space;
            printf("\n");
        }
        printf("   block max used space: %d\n\n",max_used_space);
        new_mem_size=new_mem_size>max_used_space?new_mem_size:max_used_space;
    }
    for(std::pair<int,BasicBlock*> p:br_to_fix)
    {
        int pos=p.first+1;
        assert(opcodes_raw[pos]==0xEF && opcodes_raw[pos+1]==0xBE && opcodes_raw[pos+2]==0xAD && opcodes_raw[pos+3]==0xDE);
        BasicBlock *target=p.second;
        assert(block_addr.count(target)!=0);
        int delta=block_addr[target]-pos;
        unsigned char *ptr=(unsigned char*)&delta;
        for(int i=0;i<4;i++)
            opcodes_raw[pos+i]=ptr[i];
    }
    for(unsigned char op:opcodes_raw)
        opcodes.push_back(ConstantInt::get(Type::getInt8Ty(*context),op));
    return new_mem_size;
}
void LLVMVM::FixCallInst(Function *target,Function *orig)
{
    orig->dropAllReferences();
    BasicBlock *dummy=BasicBlock::Create(orig->getContext(),"dummy",orig);
    IRBuilder<> irb(dummy);
    std::vector<Value*> args;
    for(Function::arg_iterator iter=orig->arg_begin();iter!=orig->arg_end();iter++)
        args.push_back(&*iter);
    Value *call=irb.CreateCall(FunctionCallee(target),args);
    if(target->getReturnType()->isVoidTy())
        irb.CreateRetVoid();
    else
        irb.CreateRet(call);
    
    /*for(Function &func:*target->getParent())
        for(BasicBlock &bb:func)
            for(Instruction &ii:bb)
            {
                if(isa<CallInst>(ii))
                {
                    CallInst* callInst=&cast<CallInst>(ii);
                    if(callInst->getCalledFunction()==orig)
                        callInst->setCalledFunction(FunctionCallee(target));
                }
            }
    */
}
Function* LLVMVM::virtualization(Function &f)
{
    printf("\nFunction Name: %s\n",f.getName());
    if(!check(f))
        return NULL;
    printf("[1] start demote registers!\n");
    demoteRegisters(&f);
    std::map<Value*,int> alloca_map;
    std::vector<std::pair<int,int>> remap;
    int mem_size=0,cur_op=1;
    printf("[2] start alloca vm memory for arguments!\n");
    DataLayout data=f.getParent()->getDataLayout();
    for(Function::arg_iterator iter=f.arg_begin();iter!=f.arg_end();iter++)
    {
        Value *arg=&*iter;
        alloca_map[arg]=mem_size;
        mem_size+=data.getTypeAllocSize(arg->getType());
    }
    printf("    ----arguments space %d\n",mem_size);
    printf("[3] start alloca vm memory for locals!\n");
    BasicBlock* locals_block=handleAlloca(f,alloca_map,remap,mem_size);
    printf("    ----current allocated space %d\n",mem_size);
    std::vector<BasicBlock*> code_blocks;
    printf("[4] create mapping from instruction to opcode\n");
    std::map<Instruction*,VMOpInfo*> instr_map;
    std::vector<VMOpInfo*> ops;
    for(BasicBlock &bb:f)
    {
        if(&bb==&*locals_block)
            continue;
        code_blocks.push_back(&bb);
        for(Instruction &i:bb)
        {
            VMOpInfo *op=getOrCreateRawOp(i,ops,cur_op);
            instr_map[&i]=op;
        }
    }
    createBuiltinOps(ops,cur_op);
    printf("   -current number of raw op handlers: %d\n",ops.size());
    for(VMOpInfo *o:ops)
    {
        if(!o->builtin_type)
            printf("    -- %s\n",o->instr->getOpcodeName());
    }
    printf("[5] building vistualization function\n");
    std::vector<Constant *> opcodes;
    int new_mem_size=generateOpcodes(code_blocks,alloca_map,instr_map,ops,mem_size,opcodes);
    ArrayType *AT=ArrayType::get(Type::getInt8Ty(f.getContext()),opcodes.size());
	Constant *opcode_array=ConstantArray::get(AT,ArrayRef<Constant*>(opcodes));
    GlobalVariable *oparr_var=new GlobalVariable(*(f.getParent()),AT,false,GlobalValue::LinkageTypes::PrivateLinkage,opcode_array,"opcodes");
    Function *vm_func=Function::Create(f.getFunctionType(),f.getLinkage(),f.getName()+Twine("_VM"),f.getParent());
    buildVMFunction(f,*vm_func,ops,new_mem_size,oparr_var,256,remap,alloca_map);
    return vm_func;
}
char LLVMVM::ID=0;
static RegisterPass<LLVMVM> X("vm", "vm");

// Register for clang
static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible,
  [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
    PM.add(new LLVMVM());
  });

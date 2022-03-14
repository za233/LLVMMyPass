#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/CFG.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "assert.h"
#include<vector>
#include<algorithm>
#include<ctime>
#include<cstdlib>
#include<cstdio>
using namespace llvm;
namespace
{
	struct VariableRotation : public ModulePass
	{
    	static char ID;
        
   		VariableRotation() : ModulePass(ID) {}
        Function *createRotateFunc(Module *m,PointerType *ptrType,Twine &name);
        void processFunction(Function &f,SetVector<Function*> &shift);
        bool processVars(Function &f,SetVector<AllocaInst*> &vars,Function *rotateFunc);
        bool isUsedByInst(Instruction *inst,Value *var)
        {
            for(Value *ops:inst->operands())
                if(ops==var)
                    return true;
            return false;
        }
        
        bool runOnModule(Module &m) override
		{
            Twine fname1=Twine("shiftFuncitonI8");
            Function *shiftFunc=createRotateFunc(&m,Type::getInt8PtrTy(m.getContext()),fname1);
            SetVector<Function*> shifts;
            shifts.insert(shiftFunc);
            for(Function &f:m)
            {
                if(&f==shiftFunc)
                    continue;
                if(f.hasExactDefinition())
                    processFunction(f,shifts);
            }
			return true;
    	}
  	};
}

char VariableRotation::ID=0;
static RegisterPass<VariableRotation> X("varobfu", "varobfu");
bool VariableRotation::processVars(Function &f,SetVector<AllocaInst*> &vars,Function *rotateFunc)
{
    if(vars.size()<2)
        return false;
    IRBuilder<> irb(&*f.getEntryBlock().getFirstInsertionPt());
    Value *zero=ConstantInt::get(irb.getInt32Ty(),0);
    DataLayout data=f.getParent()->getDataLayout();
    int space=0;
    SetVector<int> value_map;
    printf("function: %s\n",f.getName());
    for(int i=0;i<vars.size();i++)
    {
        AllocaInst *a=vars[i];
        value_map.insert(space);
        printf("address:  %d\n",space);
        space+=data.getTypeAllocSize(a->getAllocatedType());
    }
    ArrayType *arrayType=ArrayType::get(irb.getInt8Ty(),space);
    AllocaInst *array=irb.CreateAlloca(arrayType);
    int prob=30;
    for(BasicBlock &bb:f)
    {
        int offset=0;
        BasicBlock::iterator iter=bb.getFirstInsertionPt();
        if(&bb==&f.getEntryBlock())
            iter++;
        while(iter!=bb.end())
        {
            Instruction *inst=&*iter;
            irb.SetInsertPoint(inst);
            for(int i=0;i<vars.size();i++)
                if(isUsedByInst(inst,vars[i]))
                {
                    if(rand()%100<prob)
                    {
                        int times=rand()%(vars.size()-1)+1;
                        int delta=(space+value_map[(offset+times)%vars.size()]-value_map[offset])%space;
                        irb.CreateCall(FunctionCallee(rotateFunc),{irb.CreateGEP(array,{zero,zero}),ConstantInt::get(irb.getInt32Ty(),space),ConstantInt::get(irb.getInt32Ty(),delta)});
                        offset=(offset+times)%vars.size();
                    }
                    int index=(space+value_map[i]-value_map[offset])%space;
                    Value *gep=irb.CreateGEP(array,{zero,ConstantInt::get(irb.getInt32Ty(),index)});
                    Value *cast=irb.CreateBitOrPointerCast(gep,vars[i]->getType());
                    int c=0;
                    for(Value *ops:inst->operands())
                    {
                        if(ops==vars[i])
                            inst->setOperand(c,cast);
                        c++;
                    }
                    break;
                }
            iter++;
        }
        if(offset!=0)
        {
            irb.SetInsertPoint(bb.getTerminator());
            irb.CreateCall(FunctionCallee(rotateFunc),{irb.CreateGEP(array,{zero,zero}),ConstantInt::get(irb.getInt32Ty(),space),ConstantInt::get(irb.getInt32Ty(),(space-value_map[offset])%space)});
        }
        
    }
    return true;
}
void VariableRotation::processFunction(Function &f,SetVector<Function*> &shift)
{
    SetVector<AllocaInst*> list;
    for(BasicBlock &bb:f)
        for(Instruction &instr:bb)
            if(isa<AllocaInst>(instr))
            {
                AllocaInst *a=(AllocaInst*)&instr;
                list.insert(a);
            }
    if(processVars(f,list,shift[0]))
    {
        for(AllocaInst *a:list)
            a->eraseFromParent();
    }
}
Function *VariableRotation::createRotateFunc(Module *m,PointerType *ptrType,Twine &name)
{
    std::vector<Type*> params;
    params.push_back(ptrType);
    params.push_back(Type::getInt32Ty(m->getContext()));
    params.push_back(Type::getInt32Ty(m->getContext()));
    Type *rawType=ptrType->getPointerElementType();
    FunctionType *funcType=FunctionType::get(Type::getVoidTy(m->getContext()),params,false);
    Function *func=Function::Create(funcType,GlobalValue::PrivateLinkage,name,m);
    BasicBlock *entry1=BasicBlock::Create(m->getContext(),"entry1",func);
    BasicBlock *cmp1=BasicBlock::Create(m->getContext(),"cmp1",func);
    BasicBlock *entry2=BasicBlock::Create(m->getContext(),"entry2",func);
    BasicBlock *cmp2=BasicBlock::Create(m->getContext(),"cmp2",func);
    BasicBlock *shift=BasicBlock::Create(m->getContext(),"shift",func);
    BasicBlock *end2=BasicBlock::Create(m->getContext(),"end2",func);
    BasicBlock *end1=BasicBlock::Create(m->getContext(),"end1",func);
    Function::arg_iterator iter=func->arg_begin();
    Value *ptr=iter;
    Value *len=++iter;
    Value *times=++iter;
    IRBuilder<> irb(entry1);
    Value *zero=ConstantInt::get(irb.getInt32Ty(),0);
    Value *one=ConstantInt::get(irb.getInt32Ty(),1);
    AllocaInst *i=irb.CreateAlloca(irb.getInt32Ty());
    AllocaInst *j=irb.CreateAlloca(irb.getInt32Ty());
    AllocaInst *tmp=irb.CreateAlloca(rawType);
    AllocaInst *array=irb.CreateAlloca(ptrType);
    irb.CreateStore(zero,j);
    irb.CreateStore(ptr,array);
    irb.CreateBr(cmp1);

    irb.SetInsertPoint(cmp1);
    irb.CreateCondBr(irb.CreateICmpSLT(irb.CreateLoad(j),times),entry2,end1);

    irb.SetInsertPoint(entry2);
    irb.CreateStore(zero,i);
    irb.CreateStore(irb.CreateLoad(irb.CreateInBoundsGEP(irb.CreateLoad(array),{zero})),tmp);
    irb.CreateBr(cmp2);

    irb.SetInsertPoint(cmp2);
    irb.CreateCondBr(irb.CreateICmpSLT(irb.CreateLoad(i),irb.CreateSub(len,one)),shift,end2);

    irb.SetInsertPoint(shift);
    Value *ival=irb.CreateLoad(i);
    Value *arr=irb.CreateLoad(array);
    irb.CreateStore(irb.CreateLoad(irb.CreateInBoundsGEP(arr,{irb.CreateAdd(ival,one)})),irb.CreateInBoundsGEP(rawType,arr,{ival}));
    irb.CreateStore(irb.CreateAdd(ival,one),i);
    irb.CreateBr(cmp2);

    irb.SetInsertPoint(end2);
    irb.CreateStore(irb.CreateAdd(irb.CreateLoad(j),one),j);
    irb.CreateStore(irb.CreateLoad(tmp),irb.CreateInBoundsGEP(irb.CreateLoad(array),{irb.CreateSub(len,one)}));
    irb.CreateBr(cmp1);

    irb.SetInsertPoint(end1);
    irb.CreateRetVoid();
    return func;
}
static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible,
  [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
    PM.add(new VariableRotation());
  });

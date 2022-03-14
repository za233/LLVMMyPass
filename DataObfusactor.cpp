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
	struct DataObfusactor : public FunctionPass
	{
		
    	static char ID;
   		DataObfusactor() : FunctionPass(ID) {}
		void collectAlloca(Function &f,SetVector<AllocaInst*> &allocaList);
		void dataFlowObfu(Function &f,SetVector<AllocaInst*> &allocaList);
		void doObfu(Function &f,SetVector<AllocaInst*> &varList,int size);
		void rubbishCode(IRBuilder<> &irb,SetVector<AllocaInst*> &array,SetVector<int> &vars,int prob);
   		bool runOnFunction(Function &f) override
		{
			SetVector<AllocaInst*> allocaInsts;
			collectAlloca(f,allocaInsts);
			dataFlowObfu(f,allocaInsts);
			return false;
    	}
  	};
}

char DataObfusactor::ID=0;
static RegisterPass<DataObfusactor> X("dataobfu", "dataobfu");
void DataObfusactor::collectAlloca(Function &f,SetVector<AllocaInst*> &allocaList)
{
	for(BasicBlock &bb:f)
		for(Instruction &instr:bb)
			if(isa<AllocaInst>(instr))
				allocaList.insert((AllocaInst*)&instr);
}
void choose(int range,SetVector<int> *selected,SetVector<int> *unselect,int count)
{
	bool *used=(bool*)malloc(sizeof(bool)*range);
	memset(used,0,sizeof(used));
	for(int i=0;i<count;i++)
	{
		int id=rand()%range;
		while(used[id])
			id=rand()%range;
		used[id]=true;
		selected->insert(id);
	}
	if(unselect!=nullptr)
	{
		for(int i=0;i<range;i++)
			if(!used[i])
				unselect->insert(i);
	}
	free(used);
}
void removeSet(SetVector<int> &all,SetVector<int> &remove,SetVector<int> &out)
{
	for(int v:all)
	{
		bool ok=true;
		for(int r:remove)
		{
			if(v==r)
			{
				ok=false;
				break;
			}
		}
		if(ok)
			out.insert(v);
	}
}
void DataObfusactor::rubbishCode(IRBuilder<> &irb,SetVector<AllocaInst*> &array,SetVector<int> &vars,int prob)
{
	if(rand()%100>prob)
		return;
	SetVector<int> idx;
	choose(vars.size(),&idx,nullptr,2);
	Value *l=(Value*)array[vars[idx[0]]];
	Value *r;
	int op=rand()%4;
	int o=rand()%2;
	if(o)
		r=ConstantInt::get(array[0]->getAllocatedType(),rand());
	else
		r=irb.CreateLoad(array[vars[idx[1]]]);
	if(op==0)
		irb.CreateStore(irb.CreateAdd(irb.CreateLoad(l),r),l);
	else if(op==1)
		irb.CreateStore(irb.CreateSub(irb.CreateLoad(l),r),l);
	else if(op==2)
		irb.CreateStore(irb.CreateMul(irb.CreateLoad(l),r),l);
	else
		irb.CreateStore(irb.CreateXor(irb.CreateLoad(l),r),l);
	
}
void DataObfusactor::doObfu(Function &f,SetVector<AllocaInst*> &varList,int size)
{
	int prob=10;
	MapVector<AllocaInst*,int> indexMap;
	if(varList.size()<=0)
		return;
	Type *type=varList[0]->getAllocatedType();
	SetVector<int> freeId,usedId;
	choose(size,&usedId,&freeId,varList.size());
	IRBuilder<> irb(&*f.getEntryBlock().getFirstInsertionPt());
	SetVector<AllocaInst*> array;
	for(int i=0;i<size;i++)
		array.insert(irb.CreateAlloca(type));
	BasicBlock::iterator entry=irb.GetInsertPoint();
	for(BasicBlock &bb:f)
	{
		BasicBlock::iterator iter=bb.begin();
		if(&bb==&f.getEntryBlock())
			iter=entry;
		while(iter!=bb.end())
		{
			irb.SetInsertPoint(&*iter);
			rubbishCode(irb,array,freeId,prob);
			iter++;
		}
	}
	int idx=0;
	for(AllocaInst *a:varList)
	{
		int id=usedId[idx++];
		Value *zero=ConstantInt::get(Type::getInt32Ty(f.getContext()),0);
		for(BasicBlock &bb:f)
			for(Instruction &inst:bb)
			{
				if(isa<LoadInst>(inst) && inst.getOperand(0)==a)
				{
					SetVector<int> used,unused;
					choose(freeId.size(),&used,&unused,3);
					SetVector<int> rubbishVars;
					for(int v:unused)
						rubbishVars.insert(freeId[v]);
					Value *vr=ConstantInt::get(type,rand());
					irb.SetInsertPoint(&inst);
					Value *ga=array[freeId[used[0]]];
					Value *gb=array[freeId[used[1]]];
					Value *gc=array[freeId[used[2]]];
					if(rand()%2)
					{
						irb.CreateStore(irb.CreateAdd(irb.CreateLoad(ga),vr),gb);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
						irb.CreateStore(irb.CreateAdd(irb.CreateLoad(ga),irb.CreateLoad(array[id])),ga);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
						irb.CreateStore(irb.CreateAdd(vr,irb.CreateSub(irb.CreateLoad(ga),irb.CreateLoad(gb))),gc);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
					}
					else
					{
						irb.CreateStore(irb.CreateXor(irb.CreateLoad(ga),vr),gb);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
						irb.CreateStore(irb.CreateXor(irb.CreateLoad(ga),irb.CreateLoad(array[id])),ga);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
						irb.CreateStore(irb.CreateXor(vr,irb.CreateXor(irb.CreateLoad(ga),irb.CreateLoad(gb))),gc);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
					}
					
					inst.setOperand(0,gc);
				}
				else if(isa<StoreInst>(inst) && inst.getOperand(1)==a)
				{
					Value *val=inst.getOperand(0);
					SetVector<int> used,unused;
					choose(freeId.size(),&used,&unused,3);
					SetVector<int> rubbishVars;
					for(int v:unused)
						rubbishVars.insert(freeId[v]);
					Value *vr=ConstantInt::get(type,rand());
					irb.SetInsertPoint(&inst);
					Value *ga=array[freeId[used[0]]];
					Value *gb=array[freeId[used[1]]];
					Value *gc=array[freeId[used[2]]];
					if(rand()%2)
					{
						irb.CreateStore(irb.CreateAdd(irb.CreateLoad(ga),vr),gb);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
						irb.CreateStore(irb.CreateAdd(irb.CreateLoad(ga),val),ga);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
						irb.CreateStore(irb.CreateAdd(vr,irb.CreateSub(irb.CreateLoad(ga),irb.CreateLoad(gb))),gc);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
					}
					else
					{
						irb.CreateStore(irb.CreateXor(irb.CreateLoad(ga),vr),gb);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
						irb.CreateStore(irb.CreateXor(irb.CreateLoad(ga),val),ga);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
						irb.CreateStore(irb.CreateXor(vr,irb.CreateXor(irb.CreateLoad(ga),irb.CreateLoad(gb))),gc);
						rubbishCode(irb,array,rubbishVars,prob);
						rubbishCode(irb,array,rubbishVars,prob);
					}
					inst.setOperand(0,irb.CreateLoad(gc));
					inst.setOperand(1,array[id]);
				}
				else
				{
					int c=0;
					for(Value *ops:inst.operands())
					{
						if(ops==a)
						{
							irb.SetInsertPoint(&inst);
							inst.setOperand(c,array[id]);
						}
							
						c++;
					}
				}
				
			}
	}
}
void DataObfusactor::dataFlowObfu(Function &f,SetVector<AllocaInst*> &allocaList)
{
	SetVector<AllocaInst*> charList,shortList,intList,longList;
	for(AllocaInst *a:allocaList)
	{
		Type *type=a->getAllocatedType();
		if(type->isIntegerTy())
		{
			IntegerType *intType=(IntegerType*)type;
			if(intType->getBitWidth()==8)
				charList.insert(a);
			else if(intType->getBitWidth()==16)
				shortList.insert(a);
			else if(intType->getBitWidth()==32)
				intList.insert(a);
			else if(intType->getBitWidth()==64)
				longList.insert(a);
		}
	}
	doObfu(f,charList,charList.size()+10);
	doObfu(f,shortList,shortList.size()+10);
	doObfu(f,intList,intList.size()+10);
	doObfu(f,longList,longList.size()+10);
	for(AllocaInst *a:charList)
		a->eraseFromParent();
	for(AllocaInst *a:shortList)
		a->eraseFromParent();
	for(AllocaInst *a:intList)
		a->eraseFromParent();
	for(AllocaInst *a:longList)
		a->eraseFromParent();
}
// Register for clang
static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible,
  [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
    PM.add(new DataObfusactor());
  });


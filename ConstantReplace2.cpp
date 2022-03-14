#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CFG.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include<vector>
#include<algorithm>
#include<ctime>
#include<cstdlib>
using namespace llvm;
namespace
{
	struct Pair
	{
		unsigned int pos;
		Value *val;
	};
	struct ConstantReplace : public ModulePass
	{
    	static char ID;
   		ConstantReplace() : ModulePass(ID) {}
   		void handleInstruction(Function *f,Instruction *ii,unsigned int &count)
   		{
   			int pos=0;
			BasicBlock *bb=&f->getEntryBlock();
			std::vector<Pair*> updates;
			IRBuilder<> irb(&*bb->getFirstInsertionPt());
			for(User::op_iterator opi=ii->op_begin();opi!=ii->op_end();opi++,pos++)
			{
				Value *v=*opi;
				if(isa<ConstantInt>(*v))
				{
					ConstantInt *consts=(ConstantInt*)v;
					Type *int8ty=Type::getInt8Ty(f->getContext());
					Type *int16ty=Type::getInt16Ty(f->getContext());
					Type *int32ty=Type::getInt32Ty(f->getContext());
					Type *int64ty=Type::getInt64Ty(f->getContext());
					std::string name="global_const"+std::to_string(count);
					if(consts->getType()==int8ty)
					{
						unsigned char data=(consts->getValue().getZExtValue())&0xFF;
						unsigned char rr=(rand()&0xFF);
						unsigned char tt=data^rr;
						Value *val1=ConstantInt::get(int8ty,tt);
						Value *val2=ConstantInt::get(int8ty,rr);
						AllocaInst *g=irb.CreateAlloca(int8ty);
						irb.CreateStore(val1,g);
						LoadInst *load=new LoadInst(g,"",ii);
						Value *vv=BinaryOperator::Create(Instruction::Xor,(Value *)load,(Value *)val2,"",ii);
						Pair *node=(Pair*)malloc(sizeof(Pair));
						node->pos=pos;
						node->val=vv;
						updates.push_back(node);
						count++;
					}
					else if(consts->getType()==int16ty)
					{
						unsigned short data=(consts->getValue().getZExtValue())&0xFFFF;
						unsigned short rr=(rand()&0xFFFF);
						unsigned short tt=data^rr;
						Value *val1=ConstantInt::get(int16ty,tt);
						Value *val2=ConstantInt::get(int16ty,rr);
						AllocaInst *g=irb.CreateAlloca(int16ty);
						irb.CreateStore(val1,g);
						LoadInst *load=new LoadInst(g,"",ii);
						Value *vv=BinaryOperator::Create(Instruction::Xor,(Value *)load,(Value *)val2,"",ii);
						Pair *node=(Pair*)malloc(sizeof(Pair));
						node->pos=pos;
						node->val=vv;
						updates.push_back(node);
						count++;
					}
					else if(consts->getType()==int32ty)
					{
						unsigned int data=(consts->getValue().getZExtValue())&0xFFFFFFFF;
						unsigned int rr=(rand()&0xFFFFFFFF);
						unsigned int tt=data^rr;
						Value *val1=ConstantInt::get(int32ty,tt);
						Value *val2=ConstantInt::get(int32ty,rr);
						AllocaInst *g=irb.CreateAlloca(int32ty);
						irb.CreateStore(val1,g);
						LoadInst *load=new LoadInst(g,"",ii);
						Value *vv=BinaryOperator::Create(Instruction::Xor,(Value *)load,(Value *)val2,"",ii);
						Pair *node=(Pair*)malloc(sizeof(Pair));
						node->pos=pos;
						node->val=vv;
						updates.push_back(node);
						count++;
					}
					else if(consts->getType()==int64ty)
					{
						unsigned long long data=(consts->getValue().getZExtValue())&0xFFFFFFFFFFFFFFFF;
						unsigned long long rr=(((((unsigned long long)rand())<<32)|rand())&0xFFFFFFFFFFFFFFFF);
						unsigned long long tt=data^rr; 
						Value *val1=ConstantInt::get(int64ty,tt);
						Value *val2=ConstantInt::get(int64ty,rr);
						AllocaInst *g=irb.CreateAlloca(int64ty);
						irb.CreateStore(val1,g);
						LoadInst *load=new LoadInst(g,"",ii);
						Value *vv=BinaryOperator::Create(Instruction::Xor,(Value *)load,(Value *)val2,"",ii);
						Pair *node=(Pair*)malloc(sizeof(Pair));
						node->pos=pos;
						node->val=vv;
						updates.push_back(node);
						count++;
					}
					else
						continue;
				}
			}
			for(std::vector<Pair*>::iterator iter=updates.begin();iter!=updates.end();iter++)
				ii->setOperand((*iter)->pos,(*iter)->val);
		}
   		void ReplaceConst(Module *M)
		{
			unsigned int count=0;
			
		   	for(Function &func:*M)
		   	{
		   		std::vector<Instruction*> instr_list;
		   		for(BasicBlock &bb:func)
					for(Instruction &ii:bb)
					{
						for(User::op_iterator opi=ii.op_begin();opi!=ii.op_end();opi++)
						{
							Value *v=*opi;
							if(isa<ConstantInt>(*v))
							{
								instr_list.push_back(&ii);
								break;
							}
						}
					}
				for(std::vector<Instruction*>::iterator iter=instr_list.begin();iter!=instr_list.end();iter++)
					handleInstruction(&func,*iter,count);
			}
				
			
		} 
		
   		bool runOnModule(Module &M) override
		{
			ReplaceConst(&M);
			return false;
    	}
  	};
}

char ConstantReplace::ID=0;
static RegisterPass<ConstantReplace> X("replaceconst", "Const");

// Register for clang
static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible,
  [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
    PM.add(new ConstantReplace());
  });


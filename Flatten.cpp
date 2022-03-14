#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CFG.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <sstream>
#include "llvm/IR/Module.h"
#include<vector>
#include<algorithm>
#include<queue>
#include<ctime>
#include<cstdlib>
using namespace llvm;
namespace
{
	struct MyFlatten : public FunctionPass
	{
    	static char ID;
   		MyFlatten() : FunctionPass(ID) {}
      	std::vector<BasicBlock*> *getBlocks(Function *function,std::vector<BasicBlock*> *lists)
      	{
      		lists->clear();
      		for(BasicBlock &basicBlock:*function)
      			lists->push_back(&basicBlock);
      		return lists;
      	}
      	void getAnalysisUsage(AnalysisUsage &AU) const override
		{
			errs()<<"Require LowerSwitchPass\n";
			AU.addRequiredID(LowerSwitchID);
			FunctionPass::getAnalysisUsage(AU);
		}
		unsigned int getUniqueNumber(std::vector<unsigned int> *rand_list)
		{
				unsigned int num=rand();
				while(true)
				{
					bool state=true;
					for(std::vector<unsigned int>::iterator n=rand_list->begin();n!=rand_list->end();n++)
						if(*n==num)
						{
							state=false;
							break;
						}
					if(state)
						break;
					num=rand();
				}
				return num;
		}
		void DoSplit(Function *f,int align)
		{
			std::vector<BasicBlock*> origBB;
			getBlocks(f,&origBB);
			for(std::vector<BasicBlock *>::iterator b=origBB.begin();b!=origBB.end();b++)
			{
				BasicBlock *basicBlock=*b;
				int pos=0;
				while(true)
				{
					int len=basicBlock->getInstList().size(),idx=0;
					if(len<=align || pos==len)
						break;
					BasicBlock *tmp;
					for(Instruction &ii:*basicBlock)
					{
						idx++,pos++;
						errs()<<"        pos: "<<pos;
						if(idx%align==0 && idx!=len)
						{
							errs()<<"\tsplit!"<<"\n";
							tmp=basicBlock->splitBasicBlock((BasicBlock::iterator)ii,Twine("block"));
							break;
						}
						errs()<<"\n";
					}
					basicBlock=tmp;
				}

			}
		}
		static bool valueEscapes(Instruction *Inst)
		{
			const BasicBlock *BB=Inst->getParent();
			for(const User *U:Inst->users())
			{
				const Instruction *UI=cast<Instruction>(U);
				if (UI->getParent()!=BB || isa<PHINode>(UI))
					return true;
			}
			return false;
		}
      	void DoFlatten(Function *f,int seed)
      	{
			srand(seed);
			std::vector<BasicBlock*> origBB;
			getBlocks(f,&origBB);
			if(origBB.size()<=1)
				return ;
			unsigned int rand_val=seed;
			Function::iterator  tmp=f->begin();
			BasicBlock *oldEntry=&*tmp;
			origBB.erase(origBB.begin());
			BranchInst *firstBr=NULL;
			if(isa<BranchInst>(oldEntry->getTerminator()))
				firstBr=cast<BranchInst>(oldEntry->getTerminator());
			BasicBlock *firstbb=oldEntry->getTerminator()->getSuccessor(0);
			if((firstBr!=NULL && firstBr->isConditional()) || oldEntry->getTerminator()->getNumSuccessors()>2)		//Split the first basic block
			{
				BasicBlock::iterator iter=oldEntry->end();
				iter--;
				if(oldEntry->size()>1)
					iter--;
				BasicBlock *splited=oldEntry->splitBasicBlock(iter,Twine("FirstBB"));
				firstbb=splited;
				origBB.insert(origBB.begin(),splited);
			}
			BasicBlock *newEntry=oldEntry;												//Prepare basic block
			BasicBlock *loopBegin=BasicBlock::Create(f->getContext(),"LoopBegin",f,newEntry);
			BasicBlock *defaultCase=BasicBlock::Create(f->getContext(),"DefaultCase",f,newEntry);
			BasicBlock *loopEnd=BasicBlock::Create(f->getContext(),"LoopEnd",f,newEntry);
			newEntry->moveBefore(loopBegin);
			BranchInst::Create(loopEnd,defaultCase);					//Create branch instruction,link basic blocks
			BranchInst::Create(loopBegin,loopEnd);
		    newEntry->getTerminator()->eraseFromParent();
		    BranchInst::Create(loopBegin,newEntry);
		    AllocaInst *switchVar=new AllocaInst(Type::getInt32Ty(f->getContext()),0,Twine("switchVar"),newEntry->getTerminator());		//Create switch variable
		    LoadInst *value=new LoadInst(switchVar,"cmd",loopBegin);
			SwitchInst *sw=SwitchInst::Create(value,defaultCase,0,loopBegin);
			std::vector<unsigned int> rand_list;
			unsigned int startNum=0;
			for(std::vector<BasicBlock *>::iterator b=origBB.begin();b!=origBB.end();b++)							//Put basic blocks into switch structure
			{
				BasicBlock *block=*b;
				block->moveBefore(loopEnd);
				unsigned int num=getUniqueNumber(&rand_list);
				rand_list.push_back(num);
				if(block==firstbb)
					startNum=num;
				ConstantInt *numCase=cast<ConstantInt>(ConstantInt::get(sw->getCondition()->getType(),num));
				sw->addCase(numCase,block);
			}
			ConstantInt *startVal=cast<ConstantInt>(ConstantInt::get(sw->getCondition()->getType(),startNum));		//Set the entry value
			new StoreInst(startVal,switchVar,newEntry->getTerminator());
			errs()<<"Put Block Into Switch\n";
			for(std::vector<BasicBlock *>::iterator b=origBB.begin();b!=origBB.end();b++)							//Handle successors
			{
				BasicBlock *block=*b;
				if(block->getTerminator()->getNumSuccessors()==1)
				{
					errs()<<"This block has 1 successor\n";
					BasicBlock *succ=block->getTerminator()->getSuccessor(0);
					ConstantInt *caseNum=sw->findCaseDest(succ);
					if(caseNum==NULL)
					{
						unsigned int num=getUniqueNumber(&rand_list);
						rand_list.push_back(num);
						caseNum=cast<ConstantInt>(ConstantInt::get(sw->getCondition()->getType(),num));
					}
					block->getTerminator()->eraseFromParent();
					new StoreInst(caseNum,switchVar,block);
					BranchInst::Create(loopEnd,block);
				}
				else if(block->getTerminator()->getNumSuccessors()==2)
				{
					errs()<<"This block has 2 successors\n";
					BasicBlock *succTrue=block->getTerminator()->getSuccessor(0);
					BasicBlock *succFalse=block->getTerminator()->getSuccessor(1);
					ConstantInt *numTrue=sw->findCaseDest(succTrue);
					ConstantInt *numFalse=sw->findCaseDest(succFalse);
					if(numTrue==NULL)
					{
						unsigned int num=getUniqueNumber(&rand_list);
						rand_list.push_back(num);
						numTrue=cast<ConstantInt>(ConstantInt::get(sw->getCondition()->getType(),num));
					}
					if(numFalse==NULL)
					{
						unsigned int num=getUniqueNumber(&rand_list);
						rand_list.push_back(num);
						numFalse=cast<ConstantInt>(ConstantInt::get(sw->getCondition()->getType(),num));
					}
					BranchInst *oldBr=cast<BranchInst>(block->getTerminator());
					SelectInst *select=SelectInst::Create(oldBr->getCondition(),numTrue,numFalse,Twine("choice"),block->getTerminator());
					block->getTerminator()->eraseFromParent();
					new StoreInst(select,switchVar,block);
					BranchInst::Create(loopEnd,block);
				}
				else
					continue;
			}
			std::vector<PHINode *> tmpPhi;
		    std::vector<Instruction *> tmpReg;
			BasicBlock *bbEntry = &*f->begin();
			do
			{
				tmpPhi.clear();
				tmpReg.clear();
				for(Function::iterator i = f->begin();i!=f->end();i++)
				{
					for( BasicBlock::iterator j=i->begin();j!=i->end();j++)
					{
						if(isa<PHINode>(j))
						{
							PHINode *phi=cast<PHINode>(j);
							tmpPhi.push_back(phi);
							continue;
						}
						if (!(isa<AllocaInst>(j) && j->getParent()==bbEntry) && (valueEscapes(&*j) || j->isUsedOutsideOfBlock(&*i)))
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
			errs()<<"Finish\n";
      	}
   		bool runOnFunction(Function &function) override
		{
			DoFlatten(&function,0);
			DoSplit(&function,4);
      		return false;
    	}
  	};
}

char MyFlatten::ID=0;
static RegisterPass<MyFlatten> X("myfla", "MyFlatten");

// Register for clang
static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible,
  [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
    PM.add(new MyFlatten());
  });


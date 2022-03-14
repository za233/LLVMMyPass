#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/Local.h"

#include<assert.h>
#include<vector>
#include<algorithm>
#include<queue>
#include<ctime>
#include<cstdlib>
#include"ObfuTerm.h"
using namespace llvm;
namespace
{
	struct MyBCF : public FunctionPass
	{
    	static char ID;
    	bool flag=false;
    	unsigned int seed;
   		MyBCF() : FunctionPass(ID) {}
   		BasicBlock *getOriginalBlock(BasicBlock *basicBlock,const Twine name)
   		{
   	        BasicBlock::iterator i1=basicBlock->begin();
      		if(basicBlock->getFirstNonPHIOrDbgOrLifetime())
        		i1=(BasicBlock::iterator)basicBlock->getFirstNonPHIOrDbgOrLifetime();
      		BasicBlock *originalBB=basicBlock->splitBasicBlock(i1,name);
      		return originalBB;
   		}
      	std::vector<BasicBlock*> *getBlocks(Function *function,std::vector<BasicBlock*> *lists)
      	{
      		lists->clear();
      		for(BasicBlock &basicBlock:*function)
      			lists->push_back(&basicBlock);
      		return lists;
      	}
      	void splitBlocks(Function &function,int align)
		{
		  	BasicBlock *basicBlock,*entry=&function.getEntryBlock();
			std::vector<BasicBlock *> bbList,origs;
			getBlocks(&function,&bbList);
			errs()<<"Splitting the blocks"<<'\n';
			for(int i=0;i<bbList.size();i++)
			{
				basicBlock=bbList[i];
			  	//errs()<<basicBlock->getInstList().size()<<'\n';
				BasicBlock *orig=getOriginalBlock(basicBlock,Twine("original_block_"));
			  	origs.push_back(orig);
			}
			for(int i=0;i<origs.size();i++)
			{
			  	errs()<<"    block "<<i<<"\n";
			  	basicBlock=origs[i];
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
			errs()<<"Split finished! "<<"\n";
		}
		Value *buildExpr(Function &f,Node *node,IRBuilder<> &irb,Value *var)
		{
			Token *token=node->token;
			if(node->left==NULL && node->right==NULL)
			{
				if(token->type==VAR) 
					return irb.CreateLoad(Type::getInt32Ty(f.getContext()),var,"x");
				if(token->type==NUM)
					return irb.getInt32(token->num); 
				assert(false);
			} 
			if(token->type==OP)
			{
				if(token->data[0]=='+')
					return irb.CreateAdd(buildExpr(f,node->left,irb,var),buildExpr(f,node->right,irb,var));
				else if(token->data[0]=='*')
					return irb.CreateMul(buildExpr(f,node->left,irb,var),buildExpr(f,node->right,irb,var));
				else
					assert(false);
			} 
			else
				assert(false);
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
   		bool runOnFunction(Function &function) override
		{
			if(!flag)
			{
				srand(time(0));
				flag=true;
			}
			else
				srand(seed);

      		errs() << "Reach Function ->";
      		errs().write_escaped(function.getName()) << '\n';
      		BasicBlock *entry=&(function.getEntryBlock());
      		IRBuilder<> IRB(entry);
      		splitBlocks(function,4); 
			errs()<<'\n'; 
			std::vector<BasicBlock*> bbList;
			getBlocks(&function,&bbList);
			int len=bbList.size();
			for(int i=0;i<len;i++)
			{
				BasicBlock *basicBlock=bbList[i];
				if(basicBlock==entry)
					continue;
				if(isa<BranchInst>(basicBlock->getTerminator()))
				{
					BranchInst *end=(BranchInst*)basicBlock->getTerminator();
					if(end->isUnconditional())
					{

						BasicBlock *target=end->getSuccessor(0);
      					MyParser *parser=new MyParser();
      					std::vector<Token*> rightTokens,leftTokens;
      					IRB.SetInsertPoint(&(*entry->getFirstInsertionPt()));
      					Value *var=IRB.CreateAlloca(Type::getInt32Ty(function.getContext())); 
      					int f=rand()%2;
      					generate_obfu_eq(rightTokens,leftTokens,3,f);
      					IRB.SetInsertPoint(end);
      					Node *root=parser->parse(rightTokens);
      					assert(root!=NULL);
      					Value *right=buildExpr(function,root,IRB,var);
      					parser->destory(root);
      					IRB.SetInsertPoint(end);
      					root=parser->parse(leftTokens);
      					assert(root!=NULL);
						Value *left=buildExpr(function,root,IRB,var);
						parser->destory(root); 
						IRB.SetInsertPoint(end);
						BasicBlock *bb=bbList.at(rand()%bbList.size());
						while(bb==&(function.getEntryBlock()) || bb==target)
							bb=bbList.at(rand()%bbList.size());
						if(!f)
							IRB.CreateCondBr(IRB.CreateICmpEQ(right,left),target,bb); 
						else
							IRB.CreateCondBr(IRB.CreateICmpEQ(right,left),bb,target); 
      					end->eraseFromParent();

					}

				}

			}
			std::vector<PHINode *> tmpPhi;
			std::vector<Instruction *> tmpReg;
			BasicBlock *bbEntry=&function.getEntryBlock();
			do
			{
				tmpPhi.clear();
				tmpReg.clear();
				for(Function::iterator i=function.begin();i!=function.end();i++)
				{
					for(BasicBlock::iterator j=i->begin();j!=i->end();j++)
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
					DemoteRegToStack(*tmpReg.at(i),function.begin()->getTerminator());
				for(unsigned int i=0;i<tmpPhi.size();i++)
					DemotePHIToStack(tmpPhi.at(i),function.begin()->getTerminator());
			}
			while(tmpReg.size()!= 0 || tmpPhi.size()!= 0);
      		return false;
    	}
  	};
}

char MyBCF::ID=0;
static RegisterPass<MyBCF> X("mybcf", "My First BCF!");

// Register for clang
static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible,
  [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
    PM.add(new MyBCF());
  });

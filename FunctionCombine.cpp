#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include<vector>
#include<algorithm>
#include<map>
#include<ctime>
#include<cstdlib>
using namespace llvm;
namespace
{
	struct CombineFunction : public ModulePass
	{
    	static char ID;
   		CombineFunction() : ModulePass(ID) {}
      	std::vector<BasicBlock*> *getBlocks(Function *function,std::vector<BasicBlock*> *lists)
      	{
      		lists->clear();
      		for(BasicBlock &basicBlock:*function)
      			lists->push_back(&basicBlock);
      		return lists;
      	}
      	std::vector<Function*> *getFunctions(Module *module,std::vector<Function*> *lists)
      	{
      		lists->clear();
      		for(Function &func:*module)
      			lists->push_back(&func);
      		return lists;
      	}
		std::string readAnnotate(Function *f)
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
		Function *Combine(std::vector<Function*> *func_list,ValueToValueMapTy* VMap,Twine name,std::vector<unsigned int> *argPosList)
		{
			if(func_list->size()<1)
				return NULL;
			errs()<<"Check Function Type\n";
			for(std::vector<Function *>::iterator f=func_list->begin();f!=func_list->end();f++)
			{
				Function *func=*f;
				if(func->isDeclaration() || func->hasAvailableExternallyLinkage()!=0 || func->getFunctionType()->isVarArg()!=false)
					return NULL;
			}
			errs()<<"	Done\n";
			errs()<<"Prepare Function Type\n";
			std::vector<Type*> ArgTypes;
			for(std::vector<Function *>::iterator f=func_list->begin();f!=func_list->end();f++)
			{
				Function *func=*f;
				for(Argument &I:func->args())
					ArgTypes.push_back(I.getType());
			}
			errs()<<"	Done\n";
			errs()<<"Check Function Return Type\n";
			Function *first=*func_list->begin();
			ArgTypes.push_back(Type::getInt32Ty(first->getParent()->getContext()));
			for(std::vector<Function *>::iterator f=func_list->begin();f!=func_list->end();f++)
			{
				Function *func=*f;
				if(func->getFunctionType()->getReturnType()!=first->getFunctionType()->getReturnType())
					return NULL;
				if(func->getParent()!=first->getParent())
					return NULL;
				if(func->getLinkage()!=first->getLinkage())
					return NULL;
			}
			FunctionType *fty=FunctionType::get(first->getFunctionType()->getReturnType(),ArgTypes,false);
			Function *result=Function::Create(fty,first->getLinkage(),first->getAddressSpace(),name,first->getParent());
			Function ::arg_iterator iter=result->arg_begin();
			errs()<<"	Done\n";
			errs()<<"Start Working\n";
			unsigned int index=0;
			for(std::vector<Function *>::iterator f=func_list->begin();f!=func_list->end();f++)
			{
				Function *func=*f;
				argPosList->push_back(index);
				for(Argument &I:func->args())
					(*VMap)[&I]=&*iter++,index++;
			}
			SmallVector<ReturnInst*,8> returns;
			ClonedCodeInfo CodeInfo;
			for(std::vector<Function *>::iterator f=func_list->begin();f!=func_list->end();f++)
			{
				Function *func=*f;
				CloneFunctionInto(result,func,*VMap,func->getSubprogram()!= nullptr,returns,"",&CodeInfo);
			}
			errs()<<"	Done\n";
			return result;
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
		bool FixFunction(Function *target,std::vector<Function*> *orig_list,ValueToValueMapTy *VMap,std::vector<unsigned int> *valueList)
		{
			std::vector<BasicBlock*> entryBlocks;
			std::vector<BasicBlock*> bodyBlock;
			errs()<<"Get all entry blocks\n";
			for(std::vector<Function *>::iterator f=orig_list->begin();f!=orig_list->end();f++)
			{
				Function *func=*f;
				BasicBlock *entry=&*func->begin();
				Value *ptr=(Value*)VMap->lookup(entry);
				if(isa<BasicBlock>(*ptr))
					entryBlocks.push_back((BasicBlock*)ptr);
				else
					return false;
			}
			getBlocks(target,&bodyBlock);
			errs()<<"	Done\n";
			errs()<<"Build switch\n";
			BasicBlock *entry=BasicBlock::Create(target->getContext(),"Entry",target);
			BasicBlock *selector=BasicBlock::Create(target->getContext(),"Selector",target);
			entry->moveBefore(*entryBlocks.begin());
			selector->moveBefore(*entryBlocks.begin());
			AllocaInst *var=new AllocaInst(Type::getInt32Ty(target->getContext()),0,Twine("switchVar"),entry);
			Function::arg_iterator iter=target->arg_end();
			Value *controlArg=--iter;
			new StoreInst(controlArg,var,entry);
			BranchInst::Create(selector,entry);
			LoadInst *load=new LoadInst(var,Twine(""),selector);
			BasicBlock *endBlock=BasicBlock::Create(target->getContext(),"DefaultEnd",target);
			ReturnInst *ret=ReturnInst::Create(target->getContext(),Constant::getNullValue(target->getFunctionType()->getReturnType()),endBlock);
			SwitchInst *sw=SwitchInst::Create(load,endBlock,0,selector);
			std::vector<unsigned int> rand_list;
			std::vector<BasicBlock*>::iterator bblist_iter=entryBlocks.begin();
			for(std::vector<Function *>::iterator f=orig_list->begin();f!=orig_list->end();f++)
			{
				unsigned int val=getUniqueNumber(&rand_list);
				errs()<<val<<'\n';
				rand_list.push_back(val);
				ConstantInt *numCase=cast<ConstantInt>(ConstantInt::get(sw->getCondition()->getType(),val));
				valueList->push_back(val);
				sw->addCase(numCase,*bblist_iter);
				
				bblist_iter++;
			}
			errs()<<"	Done\n";
			errs()<<"Add useless code\n";
			for(std::vector<BasicBlock *>::iterator b=bodyBlock.begin();b!=bodyBlock.end();b++)
			{
				BasicBlock *basicBlock=*b;
				BranchInst *br=NULL;
				if(isa<BranchInst>(*basicBlock->getTerminator()))
				{
					br=(BranchInst*)basicBlock->getTerminator();
					if(br->isUnconditional())
					{
						BasicBlock *rand_target=entryBlocks.at(rand()%entryBlocks.size());
						BasicBlock *right=basicBlock->getTerminator()->getSuccessor(0);
						basicBlock->getTerminator()->eraseFromParent();
						unsigned int val=getUniqueNumber(&rand_list);
						rand_list.push_back(val);
						LoadInst *cmpValA=new LoadInst(var,Twine(""),basicBlock);
						ConstantInt *cmpValB=ConstantInt::get(Type::getInt32Ty(target->getContext()),val);
						ICmpInst *condition=new ICmpInst(*basicBlock,ICmpInst::ICMP_EQ,cmpValA,cmpValB);
						BranchInst::Create(rand_target,right,condition,basicBlock);
					}
				}

			}

			errs()<<"	Done\n";
			return true;
		}
		bool FixCallInst(Function *target,std::vector<Function*> *orig_list,ValueToValueMapTy *VMap,std::vector<unsigned int> *valueList,std::vector<unsigned int> *argPosList)
		{
			std::vector<unsigned int>::iterator  v=valueList->begin(),a=argPosList->begin();
			std::vector<CallInst*> remove_list;
			for(std::vector<Function *>::iterator f=orig_list->begin();f!=orig_list->end();f++,v++,a++)
			{
				unsigned int val=*v,argPos=*a;
				Function *ff=*f;
				for(Function &func:*ff->getParent())
					for(BasicBlock &bb:func)
						for(Instruction &ii:bb)
						{
							if(isa<CallInst>(ii))
							{
								CallInst* callInst=&cast<CallInst>(ii);
								if(callInst->getCalledFunction()==ff)
								{
									std::vector<Value *> arg_list;
									Function ::arg_iterator itera=target->arg_begin();
									User::op_iterator iterb=callInst->arg_begin();
									for(size_t i=0;i<target->arg_size()-1;i++,itera++)
									{
										if(i>=argPos && i<argPos+callInst->arg_size())
										{
											arg_list.push_back(*iterb);
											iterb++;
										}
										else
											arg_list.push_back(Constant::getNullValue((*itera).getType()));
									}
									arg_list.push_back(ConstantInt::get(Type::getInt32Ty(target->getContext()),val));
									CallInst *newCall=CallInst::Create(target,arg_list,Twine(""),callInst);
									remove_list.push_back(callInst);
									callInst->replaceAllUsesWith(newCall);
								}
							}
						}

			}
			for(std::vector<CallInst *>::iterator c=remove_list.begin();c!=remove_list.end();c++)
				(*c)->eraseFromParent();
			return true;
		}
   		bool runOnModule(Module &module) override
		{
			std::vector<Function*>  func_list;
			getFunctions(&module,&func_list);
			std::vector<Function*>  work_list;
			errs()<<"Function List:\n";
			for(std::vector<Function *>::iterator f=func_list.begin();f!=func_list.end();f++)
			{
				Function *func=*f;
				errs()<<"	";
				errs().write_escaped(func->getName()) << '\n';
				if(!readAnnotate(func).find("combine"))
				{
					errs()<<"		-Add to work list\n";
					work_list.push_back(func);
				}
			}
			ValueToValueMapTy VMap;
			std::vector<unsigned int> values,argPos;
			Function *target=Combine(&work_list,&VMap,"MixFunction",&argPos);
			if(target==NULL)
			{
				errs()<<"Combine Fail\n";
				return false;
			}

			if(!FixFunction(target,&work_list,&VMap,&values))
			{
				errs()<<"FixFunction Fail\n";
				return false;
			}
			if(!FixCallInst(target,&work_list,&VMap,&values,&argPos))
			{
				errs()<<"FixCallInst Fail\n";
				return false;
			}
			module.getGlobalVariable("llvm.global.annotations")->eraseFromParent();
			for(std::vector<Function *>::iterator f=work_list.begin();f!=work_list.end();f++)
			{
				Function *func=*f;
				func->eraseFromParent();
			}
      		return false;
    	}
  	};
}

char CombineFunction ::ID=0;
static RegisterPass<CombineFunction > X("combine", "MyCombine");

// Register for clang
static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible,
  [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
    PM.add(new CombineFunction ());
  });

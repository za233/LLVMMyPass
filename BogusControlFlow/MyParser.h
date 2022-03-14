#ifndef __MYPARSER_H__
#define __MYPARSER_H__
#include<vector>
#include<stack>
#include<cstdio>
#include<cstdlib>
#define VAR 1
#define NUM 2
#define OP 3
#define END 4
struct Token
{
	int type;
	union
	{
		char data[8];
		int num;
	};
	
};
struct Node
{
	Node *left,*right;
	Token *token;
};

class MyParser 
{
	public:
		~MyParser()
		{
			this->destory_pool(this->allocaPool);
		}
		void destory(Node *root);
		Node* parse(std::vector<Token*> &tokens);
	private:
		bool error=false;
		std::stack<Node*> tokenStack;
		std::vector<Node*> allocaPool; 
		std::vector<Node*> tmpPool;
		void expression(std::vector<Token*> &eles,std::vector<Token*>::iterator &iter);
		void _expression(std::vector<Token*> &eles,std::vector<Token*>::iterator &iter);
		void term(std::vector<Token*> &eles,std::vector<Token*>::iterator &iter);
		void _term(std::vector<Token*> &eles,std::vector<Token*>::iterator &iter);
		void factor(std::vector<Token*> &eles,std::vector<Token*>::iterator &iter);
		void panic(int id);
		Node *alloca_tmp_node(Token *token);
		void free_node(Node *node);
		void combine_node(Token *op);
		void push_node(Token *op);
		void destory_pool(std::vector<Node*> &pool);
};
#endif

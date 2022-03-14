#include"MyParser.h"

void MyParser::panic(int id)
{
	printf("Error! %d\n",id);
	this->error=true;
}
extern void MyParser::destory(Node *root)
{
	if(root==NULL)
		return;
	if(root->left!=NULL)
		this->destory(root->left);
	if(root->right!=NULL)
		this->destory(root->right);
	this->free_node(root);
}	
extern Node* MyParser::parse(std::vector<Token*> &tokens)
{
		
	this->error=false;
	while(!this->tokenStack.empty())
		this->tokenStack.pop();
	this->tmpPool.clear();
	std::vector<Token*>::iterator iter=tokens.begin();
	this->expression(tokens,iter);
	if(this->error || iter!=tokens.end())
	{
		this->destory_pool(this->tmpPool);
		this->tmpPool.clear();
		return NULL;
	}
	else
	{
		for(std::vector<Node*>::iterator iter=this->tmpPool.begin();iter!=this->tmpPool.end();iter++)
			this->allocaPool.push_back(*iter);
		this->tmpPool.clear();
		//printf("%d\n",this->tokenStack.size());
		return this->tokenStack.top();	
	}
	//	return true;
} 
void MyParser::destory_pool(std::vector<Node*> &pool)
{
	std::vector<Node*>::iterator iter=pool.begin();
	while(iter!=pool.end())
	{
		free(*iter);
		iter++;
	}
	this->allocaPool.clear();
}

Node *MyParser::alloca_tmp_node(Token *token)
{
	Node *node=(Node*)malloc(sizeof(Node));
	this->tmpPool.push_back(node);
	node->left=node->right=NULL;
	node->token=token;
	return node;
} 
void MyParser::free_node(Node *node)
{
	std::vector<Node*>::iterator iter=this->allocaPool.begin();
	while(iter!=this->allocaPool.end())
	{
		if(*iter==node)
		{
			free(node);
			break;
		}
		iter++;
	}
	this->allocaPool.erase(iter);
}
void MyParser::push_node(Token *op)
{
	//printf("push %c\n",op->data[0]);
	this->tokenStack.push(this->alloca_tmp_node(op));
}
void MyParser::combine_node(Token *op)
{
	Node *a=this->tokenStack.top();
	this->tokenStack.pop();
	Node *b=this->tokenStack.top();
	this->tokenStack.pop();
	Node *c=alloca_tmp_node(op);
	c->left=a;
	c->right=b;
	//printf("combine %c\n",c->token->data[0]);
	this->tokenStack.push(c);
}
void MyParser::expression(std::vector<Token*> &tokens,std::vector<Token*>::iterator &iter)
{
	if(this->error)
		return;
	this->term(tokens,iter);
	this->_expression(tokens,iter);
}
void MyParser::_expression(std::vector<Token*> &tokens,std::vector<Token*>::iterator &iter)
{
	if(this->error)
		return; 
	if(iter==tokens.end())
		return;
	else if((*iter)->type==OP && ((*iter)->data[0]=='+' || (*iter)->data[0]=='-'))
	{
		Token *op=*iter;
		iter++;
		this->term(tokens,iter);
		this->combine_node(op);
		this->_expression(tokens,iter);
	}
		
}
void MyParser::term(std::vector<Token*> &tokens,std::vector<Token*>::iterator &iter)
{
	if(this->error)
		return;
	this->factor(tokens,iter);
	this->_term(tokens,iter);
} 
void MyParser::_term(std::vector<Token*> &tokens,std::vector<Token*>::iterator &iter)
{
	if(this->error)
		return;
	if(iter==tokens.end())
		return;
	else if((*iter)->type==OP && (*iter)->data[0]=='*')
	{
		Token *op=*iter;
		iter++;
		this->factor(tokens,iter);
		this->combine_node(op);
		this->_term(tokens,iter);
	}
		
}
void MyParser::factor(std::vector<Token*> &tokens,std::vector<Token*>::iterator &iter)
{
	if(this->error)
		return;
	if(iter==tokens.end())
		this->panic(1);
	else if((*iter)->type==VAR || (*iter)->type==NUM) 
	{
		this->push_node(*iter);
		iter++;
	}
	else if((*iter)->type==OP && (*iter)->data[0]=='(')
	{
		iter++;
		this->expression(tokens,iter);
		if(iter==tokens.end() || (*iter)->type!=OP || (*iter)->data[0]!=')')
			this->panic(2); 
		else
			iter++; 
			
	}
	else
		this->panic(3);
		
}

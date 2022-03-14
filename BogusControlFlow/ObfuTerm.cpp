#include"ObfuTerm.h"

#include<algorithm>
#include<cstdio>
#include<ctime>
#include<cstring>
void push_term(std::vector<Term*> &poly,int coeff,int index)
{
	Term *tm=(Term*)malloc(sizeof(Term));
	tm->coeff=coeff;
	tm->index=index;
	poly.push_back(tm);
}
bool term_cmp(Term *a,Term *b)
{
	return a->index>b->index;
}
void simplify(std::vector<Term*> &poly)
{
	sort(poly.begin(),poly.end(),term_cmp);
	std::vector<Term*>::iterator iter=poly.begin();
	std::vector<Term*> tmp;
	Term *front=*iter;
	tmp.push_back(front);
	iter++;
	while(iter!=poly.end())
	{
		Term *ptr=*iter;
		if(ptr->index!=front->index)
		{
			front=ptr;	
			tmp.push_back(ptr);
		}
		else
			front->coeff+=ptr->coeff;
		iter++;
	}
	poly.clear();
	for(std::vector<Term*>::iterator iter=tmp.begin();iter!=tmp.end();iter++)
	{
		if((*iter)->coeff!=0)
			poly.push_back(*iter);
	}
	tmp.clear();
}
void multipy(std::vector<Term*> &polya,std::vector<Term*> &polyb,std::vector<Term*> &out)
{
	for(std::vector<Term*>::iterator a=polya.begin();a!=polya.end();a++)
		for(std::vector<Term*>::iterator b=polyb.begin();b!=polyb.end();b++)
			push_term(out,(*a)->coeff*(*b)->coeff,(*a)->index+(*b)->index);
	simplify(out);
}



void generate_random_poly(std::vector<Term*> &out,int coeff_range,int index_range,int term_num)
{
	for(int i=0;i<term_num;i++)
		push_term(out,(rand()%coeff_range)-coeff_range/2,rand()%index_range);
	simplify(out);
}
void push_num(std::vector<Token*> &out,int num)
{
	Token *t=(Token*)malloc(sizeof(Token));
	t->type=NUM;
	t->num=num;
	out.push_back(t);
}
void push_others(std::vector<Token*> &out,int type,const char *d)
{
	Token *t=(Token*)malloc(sizeof(Token));
	memset(t,0,sizeof(Token));
	t->type=type;
	memcpy(t->data,d,strlen(d));
	out.push_back(t);
}
void one_to_tokens(Term* in,std::vector<Token*> &out)
{
	push_num(out,in->coeff);
	push_others(out,OP,"*");
	if(in->index>0)
	{
		for(int j=0;j<in->index-1;j++)
		{
			push_others(out,VAR,"x");
			push_others(out,OP,"*");
		}	
		push_others(out,VAR,"x");
	}
	else
		push_num(out,1);
}
void all_to_tokens(std::vector<Term*> &in,std::vector<Token*> &out)
{
	for(size_t i=0LL;i<in.size();i++)
	{
		one_to_tokens(in[i],out); 
		if(i!=in.size()-1)
			push_others(out,OP,"+");
	}
	
}
void dump_tokens(std::vector<Token*> left)
{
	for(std::vector<Token*>::iterator iter=left.begin();iter!=left.end();iter++)
	{
		Token *t=*iter;
		if(t->type!=NUM)
			printf("%s",t->data);
		else
			printf("%d",t->num);
	}
	puts("");
}
void generate_obfu_eq(std::vector<Token*> &left,std::vector<Token*> &right,int factor_num,bool noteq)
{
	std::vector<Term*> poly,result,tmp;
	std::vector<Token*> o;
	int coeff_range=65535,index_range=3;
	for(int i=0;i<factor_num;i++)
	{
		push_others(left,OP,"(");
		generate_random_poly(poly,coeff_range,index_range,3);
		all_to_tokens(poly,o);
		for(std::vector<Token*>::iterator iter=o.begin();iter!=o.end();iter++)
			left.push_back(*iter);
		push_others(left,OP,")");
		if(i!=factor_num-1)
			push_others(left,OP,"*");
		if(i==0)
		{
			for(std::vector<Term*>::iterator iter=poly.begin();iter!=poly.end();iter++)
				result.push_back(*iter);
		}
		else
		{
			tmp.clear();
			multipy(result,poly,tmp);
			result.clear();
			for(std::vector<Term*>::iterator iter=tmp.begin();iter!=tmp.end();iter++)
				result.push_back(*iter);
		}
		poly.clear(); 
		o.clear();
	}
	for(int i=0;i<factor_num;i++)
	{
		Term t;
		t.coeff=rand()%coeff_range-coeff_range/2;
		t.index=rand()%((index_range-1)*factor_num); 
		o.clear();
		one_to_tokens(&t,o);
		push_term(result,t.coeff,t.index);
		push_others(left,OP,"+");
		for(std::vector<Token*>::iterator iter=o.begin();iter!=o.end();iter++)
			left.push_back(*iter);
		
	}
	if(noteq)
		push_term(result,rand()%100,0);
	simplify(result);
	all_to_tokens(result,right);
}
void dbg(Node *node)
{
	Token *t=node->token; 
	if(t->type!=NUM)
		printf("%s",t->data);
	else
		printf("%d",t->num);
}
void dump_tree(Node *node)
{
	if(node->left==NULL && node->right==NULL)
		return;
	dump_tree(node->left);
	dump_tree(node->right);
	printf("Opnd1-> ");
	dbg(node->left);
	putchar(' ');
	printf("Opnd2-> ");
	dbg(node->right);
	putchar(' ');
	printf("Op->");
	dbg(node);
	putchar('\n'); 
}
int main()
{
	/*
	std::vector<Term*> a,b,p;
	generate_random_poly(a,10,4,5);
	generate_random_poly(b,10,4,5);
	multipy(a,b,p);
	for(std::vector<Term*>::iterator iter=p.begin();iter!=p.end();iter++)
	{
		
		if((*iter)->coeff!=1)
			printf("%d",(*iter)->coeff);
		if((*iter)->index!=0)
			printf("x^%d",(*iter)->index);
		if(iter+1!=p.end())
			printf("+");
	}
	puts("");
	std::vector<Token*> out;
	all_to_tokens(p,out);
	MyParser *parser=new MyParser();
	Node *root=parser->parse(out);
	if(root!=NULL)
		dump_tree(root);
	parser->destory(root);*/
	srand(time(0));
	std::vector<Token*> left,right;
	generate_obfu_eq(left,right,3,true);
	dump_tokens(left); 
	dump_tokens(right); 
	MyParser *parser=new MyParser();
	Node *root=parser->parse(right);
	if(root!=NULL)
		dump_tree(root);
	int x=100000;
	int l=(2*x*x+23*x)*(-46*x*x+26*x+-44*1)*(-28*x*x+-9*x+5*1)+21*x*x*x*x*x*x+-27*x*x*x*x*x+22*1;
	int r=2597*x*x*x*x*x*x+28969*x*x*x*x*x+-5686*x*x*x*x+18716*x*x*x+11658*x*x+-5060*x+22*1;
	if(l==r)
		printf("equal\n");
	return 0;
	
}

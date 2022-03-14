#include<vector>
#include"MyParser.h"
struct Term			//coeff+x^index
{
	int index;
	int coeff;
};
void generate_obfu_eq(std::vector<Token*> &left,std::vector<Token*> &right,int factor_num,bool noteq);

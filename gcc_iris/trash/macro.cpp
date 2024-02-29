#include<iostream>
#include <stdlib.h>

typedef struct Lel* nig;
int a = 3;
  /* The nodes in the splay tree.  */
  struct Lel {
    int a;
    nig left;
    nig right;
  };

int main(){

  nig o;

  
  o = (nig)malloc(sizeof(Lel *));

  std::cout << o->a;
  
  return 0;
  
}

/*
  Last Modified: July 30, 2012
 
  SF-Tree.c 
  
  To compile: gcc -Wall SF-Tree.c -o prog -lm
  To run: ./prog inputFile utilityTable outputFile minShare

  Example Friend Database:
  
  L1 = Tom: {Ken(30), Pat(20), Sam(40)}
  L2 = Sam: {Jill(10), Joe(40), Ken(20), Tom(50)}
  L3 = Don: {Bob(10), Jill(10), Joe(10), Ken(30), Tom(20)}
  L4 = Pat: {Jill(30), Joe(50), Ken(30)}
  L5 = Ken: {Bob(10), Joe(20), Sam(10), Tom(20)}
  L6 = Jill: {Joe(10), Pat(30)}
  L7 = Joe: {Don(20), Ken(20), Sam(30)}
  
  (Bob is 8)
  
  Corresponding input file should look like this:
  The first line (7) is the number of transactions
  
  7
  1	3	5 30 4 20 2 40
  2	4	6 10 7 40 5 20 1 50
  3	5	8 10 6 10 7 10 5 30 1 20
  4	3	6 30 7 50 5 30
  5	4	8 10 7 20 2 10 1 20
  6	2	7 10 4 30
  7	3	3 20 5 20 2 30
  
  Utility table should look like this:
  
  8
  7 0.40
  3 0.50
  5 0.70
  6 0.90
  2 0.70
  4 0.60
  8 0.20
  1 0.50

  Note: To get the correct results set SORT_TREE to 1, everything else 0, to see the results set PRF_FP to 1
  When SORT_TREE is set to 0, not getting the right results.
  
  ****IMPORTANT:
  If not getting consistent results, might have to increase MAXITEMSETS if run out of
  room in FP array.
  May need to increase MAXITEMSETS if minSig really small
  
  There is a function called countMem that counts the memory when doing the FP-Growth.
  This was included in FP-Growth algorithm.
  
*/

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <math.h>
#include <sys/time.h>
#include "SF-Tree.h"

#define DEBUG     0
#define CNT_FP    0 /* default: 1; use CNT_FP=1 with SING_PATH=1 */
#define PRT_FP    1
//#define CNT_CCC   0 /* use CNT_CCC=1 with CNT_MEM=1 */
#define CNT_MEM   0
#define PRT_MEM   0
#define PRT_FALSE_POS  0	//print number of false positives
#define SORT_TREE 1 /* default: 1 */ //don't set this to 0
#define SING_PATH 0 /* default: 1 */ //set this to 1

int setTransNum;
Itemset FP[MAXITEMSETS + 1]; //keep a list of frequent patterns found
int sizeFP;

int initial_number;

void init_itemset(Itemset *I){
	
	int i;
	for(i = 1; i <= MAXITEMS; i ++){
		I->items[i] = 0;
	}
	I->climp = 0;
	I->dgimp = 0;
	I->info = NULL;
}

void init_transaction(Transaction *T){
	
	int i;
	for(i = 1; i <= MAXITEMS; i ++){
		T->itemset[i] = 0;
	}
}

void print_itemset(Itemset *I, FILE *fpRev){
	
	int i;
	printf("\n{ ");
	fprintf(fpRev, "\n{ ");
	for(i = 1; i <= MAXITEMS; i ++){
		if(I->items[i] == 1){
			printf("%d ", i);
			fprintf(fpRev, "%d ", i);
		}
	}
	printf("}");
	fprintf(fpRev, "}");	
}

/* sort desc key, asc datum1 */
int compU1( longList *A, int x, int y ){
  int diff;

  diff = A->key[x] - A->key[y];
  if( diff == 0 )
    diff = A->datum1[y] - A->datum1[x];
  return (diff < 0 ? -1 : 1);
}

int compU2( longList *A, int x, int key, int datum ){
  int diff;

  diff = A->key[x] - key;
  if( diff == 0 )
    diff = datum - A->datum1[x];
  return (diff < 0 ? -1 : 1);
}

void heapifyMaxUQ( longList *A, int i ){
  int l, r, largest;
  int temp;

  l = LEFT(i);
  r = RIGHT(i);
  if( l <= A->size && (compU1(A,l,i) > 0) )
    largest = l;
  else
    largest = i;
  if( r <= A->size && (compU1(A,r,largest) > 0) )
    largest = r;
  if( largest != i ){
    temp = A->key[i];
    A->key[i] = A->key[largest];
    A->key[largest] = temp;
    temp = A->datum1[i];
    A->datum1[i] = A->datum1[largest];
    A->datum1[largest] = temp;
    heapifyMaxUQ( A, largest );
  }
}

int extractMaxUQ( longList *A, int *datum1 ){
  int max;

  if( A->size < 1 ){
    fprintf( stderr, "ERROR[extractMaxUQ]: Heap underflow\n" );
    exit( 0 );
  }

  max = A->key[1];
  *datum1 = A->datum1[1];
  A->key[1] = A->key[A->size];
  A->datum1[1] = A->datum1[A->size];
  (A->size)--;
  heapifyMaxUQ( A, 1 );
  return max;
}

void insMaxUQ( longList *A, int keyVal, int datum1 ){
  int i;

  if( A->size >= MAXQITEM ){
    fprintf( stderr, "ERROR[insMaxUQ]: Heap overflow\n" );
    exit( 0 );
  }

  (A->size)++;
  i = A->size;
  while( (i > 1) && (compU2(A,PARENT(i),keyVal,datum1) < 0) ){
    A->key[i] = A->key[PARENT(i)];
    A->datum1[i] = A->datum1[PARENT(i)];
    i = PARENT(i);
  }
  A->key[i] = keyVal;
  A->datum1[i] = datum1;
}

void heapifyMinUQ( longList *A, int i ){
  int l, r, smallest;
  int temp;

  l = LEFT(i);
  r = RIGHT(i);
  if( l <= A->size && (compU1(A,l,i) < 0) )
    smallest = l;
  else
    smallest = i;
  if( r <= A->size && (compU1(A,r,smallest) < 0) )
    smallest = r;
  if( smallest != i ){
    temp = A->key[i];
    A->key[i] = A->key[smallest];
    A->key[smallest] = temp;
    temp = A->datum1[i];
    A->datum1[i] = A->datum1[smallest];
    A->datum1[smallest] = temp;
    heapifyMinUQ( A, smallest );
  }
}

int extractMinUQ( longList *A, int *datum1 ){
  int min;

  if( A->size < 1 ){
    fprintf( stderr, "ERROR[extractMinUQ]: Heap underflow\n" );
    exit( 0 );
  }

  min = A->key[1];
  *datum1 = A->datum1[1];
  A->key[1] = A->key[A->size];
  A->datum1[1] = A->datum1[A->size];
  (A->size)--;
  heapifyMinUQ( A, 1 );
  return min;
}

//keyVal is the lgwt and datum1 is the item
void insMinUQ( longList *A, int keyVal, int datum1 ){
  int i;

  if( A->size >= MAXQITEM ){
    fprintf( stderr, "ERROR[insMinUQ]: Heap overflow\n" );
    exit( 0 );
  }

  (A->size)++;
  i = A->size;
  while( (i > 1) && (compU2(A,PARENT(i),keyVal,datum1) > 0) ){
    A->key[i] = A->key[PARENT(i)];
    A->datum1[i] = A->datum1[PARENT(i)];
    i = PARENT(i);
  }
  A->key[i] = keyVal;
  A->datum1[i] = datum1;
}

void heapSortAscUQ( longList *A ){
  int i, temp;
  int heapSize;

  heapSize = A->size;
  for( i = A->size; i >= 2; i-- ){
    temp = A->key[1];
    A->key[1] = A->key[i];
    A->key[i] = temp;
    temp = A->datum1[1];
    A->datum1[1] = A->datum1[i];
    A->datum1[i] = temp;
    (A->size)--;
    heapifyMaxUQ( A, 1 );
  }
  A->size = heapSize;
}

void heapSortDescUQ( longList *A ){
  int i, temp;
  int heapSize;

  heapSize = A->size;
  for( i = A->size; i >= 2; i-- ){
    temp = A->key[1];
    A->key[1] = A->key[i];
    A->key[i] = temp;
    temp = A->datum1[1];
    A->datum1[1] = A->datum1[i];
    A->datum1[i] = temp;
    (A->size)--;
    heapifyMinUQ( A, 1 );
  }
  A->size = heapSize;
}

void showHeapUQ( longList *A ){
  int i, maxNode;

  printf( "Heap(size=%d):\n\t", A->size );
  for( i=1, maxNode=2; i <= A->size; i++ ){
    printf( "%d <%d> ", A->key[i], A->datum1[i] );
    if( (i+1) % maxNode == 0 ){
      printf( "\n\t" );
      maxNode *= 2;
    }
  }
  printf( "\n" );
}

void showList( longList *A ){
  int i;

  printf( "longList(size=%d):\n\t", A->size );
  for( i=1; i <= A->size; i++ )
    printf( "%d <%d> ", A->key[i], A->datum1[i] );
  printf( "\n" );
}

/* ======================================================================= */

/* sort desc key, asc datum1 */

int compSU1( shortList *A, int x, int y ){
  int diff;

  diff = A->key[x] - A->key[y];
  if( diff == 0 )
    diff = A->datum1[y] - A->datum1[x];
  return (diff < 0 ? -1 : 1);
}

int compSU2( shortList *A, int x, int key, int datum ){
  int diff;

  diff = A->key[x] - key;
  if( diff == 0 )
    diff = datum - A->datum1[x];
  return (diff < 0 ? -1 : 1);
}

void heapifyMaxUList( shortList *A, int i ){
  int l, r, largest;
  int temp;

  l = LEFT(i);
  r = RIGHT(i);
  if( l <= A->size && (compSU1(A,l,i) > 0) )
    largest = l;
  else
    largest = i;
  if( r <= A->size && (compSU1(A,r,largest) > 0) )
    largest = r;
  if( largest != i ){
    temp = A->key[i];
    A->key[i] = A->key[largest];
    A->key[largest] = temp;
    temp = A->datum1[i];
    A->datum1[i] = A->datum1[largest];
    A->datum1[largest] = temp;
    heapifyMaxUList( A, largest );
  }
}

int extractMaxUList( shortList *A, int *datum1 ){
  int max;

  if( A->size < 1 ){
    fprintf( stderr, "ERROR[extractMaxUList]: Heap underflow\n" );
    exit( 0 );
  }

  max = A->key[1];
  *datum1 = A->datum1[1];
  A->key[1] = A->key[A->size];
  A->datum1[1] = A->datum1[A->size];
  (A->size)--;
  heapifyMaxUList( A, 1 );
  return max;
}

void insMaxUList( shortList *A, int keyVal, int datum1 ){
  int i;

  if( A->size >= MAXQITEM ){
    fprintf( stderr, "ERROR[insMaxUList]: Heap overflow\n" );
    exit( 0 );
  }

  (A->size)++;
  i = A->size;
  while( (i > 1) && (compSU2(A,PARENT(i),keyVal,datum1) < 0) ){
    A->key[i] = A->key[PARENT(i)];
    A->datum1[i] = A->datum1[PARENT(i)];
    i = PARENT(i);
  }
  A->key[i] = keyVal;
  A->datum1[i] = datum1;
}

void heapifyMinUList( shortList *A, int i ){
  int l, r, smallest;
  int temp;

  l = LEFT(i);
  r = RIGHT(i);
  if( l <= A->size && (compSU1(A,l,i) < 0) )
    smallest = l;
  else
    smallest = i;
  if( r <= A->size && (compSU1(A,r,smallest) < 0) )
    smallest = r;
  if( smallest != i ){
    temp = A->key[i];
    A->key[i] = A->key[smallest];
    A->key[smallest] = temp;
    temp = A->datum1[i];
    A->datum1[i] = A->datum1[smallest];
    A->datum1[smallest] = temp;
    heapifyMinUList( A, smallest );
  }
}

int extractMinUList( shortList *A, int *datum1 ){
  int min;

  if( A->size < 1 ){
    fprintf( stderr, "ERROR[extractMinUList]: Heap underflow\n" );
    exit( 0 );
  }

  min = A->key[1];
  *datum1 = A->datum1[1];
  A->key[1] = A->key[A->size];
  A->datum1[1] = A->datum1[A->size];
  (A->size)--;
  heapifyMinUList( A, 1 );
  return min;
}

void insMinUList( shortList *A, int keyVal, int datum1 ){
  int i;

  if( A->size >= MAXQITEM ){
    fprintf( stderr, "ERROR[insMinUList]: Heap overflow\n" );
    exit( 0 );
  }

  (A->size)++;
  i = A->size;
  while( (i > 1) && (compSU2(A,PARENT(i),keyVal,datum1) > 0) ){
    A->key[i] = A->key[PARENT(i)];
    A->datum1[i] = A->datum1[PARENT(i)];
    i = PARENT(i);
  }
  A->key[i] = keyVal;
  A->datum1[i] = datum1;
}

void heapSortAscUList( shortList *A ){
  int i, temp;
  int heapSize;

  heapSize = A->size;
  for( i = A->size; i >= 2; i-- ){
    temp = A->key[1];
    A->key[1] = A->key[i];
    A->key[i] = temp;
    temp = A->datum1[1];
    A->datum1[1] = A->datum1[i];
    A->datum1[i] = temp;
    (A->size)--;
    heapifyMaxUList( A, 1 );
  }
  A->size = heapSize;
}

void heapSortDescUList( shortList *A ){
  int i, temp;
  int heapSize;

  heapSize = A->size;
  for( i = A->size; i >= 2; i-- ){
    temp = A->key[1];
    A->key[1] = A->key[i];
    A->key[i] = temp;
    temp = A->datum1[1];
    A->datum1[1] = A->datum1[i];
    A->datum1[i] = temp;
    (A->size)--;
    heapifyMinUList( A, 1 );
  }
  A->size = heapSize;
}

void showHeapUList( shortList *A ){
  int i, maxNode;

  printf( "Heap(size=%d):\n\t", A->size );
  for( i=1, maxNode=2; i <= A->size; i++ ){
    printf( "%d <%d> ", A->key[i], A->datum1[i] );
    if( (i+1) % maxNode == 0 ){
      printf( "\n\t" );
      maxNode *= 2;
    }
  }
  printf( "\n" );
}

void showSList( shortList *A ){
  int i;

  printf( "shortList(size=%d):\n\t", A->size );
  for( i=1; i <= A->size; i++ )
    printf( "%d <%d> ", A->key[i], A->datum1[i] );
  printf( "\n" );
}

/* ======================================================================= */

/*
  Items are arranged according to descending frequency order.
  Only frequent and valid items are in the tree.
*/
/* #define constrOk(i) ((i <= 1000)) */
//#define constrOk(i) ((TRUE))

int countL[MAXLEVEL+1];
int maxMemSpc;

//int numConstrChk;
int numSupCnt;
int numNodesGT, numNodesAllT;
int isGlobal;

void cleanHdr( Header *hdr ){
  int i;

  hdr->hdrLen = 0;
  for( i=1; i <= MAXITEMS; i++ ){
    hdr->item[i] = 0;
    hdr->lgwt[i] = 0;
    hdr->nodeCnt[i] = 0;
    hdr->head[i] = NULL;
    hdr->tail[i] = NULL;
    hdr->mapHdr[i] = 0;
  }
}

TreeNode *createNewNode( int item, int count ){
  TreeNode *N;

  N = (TreeNode *)malloc( sizeof(TreeNode) );
  if( N == NULL ){
    fprintf( stderr, "ERROR[createNode]\n" );
    exit( 0 );
  }
  N->item = item;
  N->count = count;
  N->info = NULL;
  N->nodeLink = NULL;
  N->parent = NULL;
  N->firstChild = NULL;
  N->lastChild = NULL;
  N->sibling = NULL;

  return N;
}

PersonalInfo *create_info(int item){
	PersonalInfo *P;
	
	P = (PersonalInfo *)malloc(sizeof(PersonalInfo));
	if(P == NULL){
		fprintf(stderr, "ERROR[create_info]\n");
		exit(0);
	}
	int i;
	for(i = 1; i <= MAXITEMS; i ++){
		P->friends[i] = 0;
	}
	P->friends[item] = 1;
	return P;
}

PersonalInfo *create_info_copy(PersonalInfo *child){
	PersonalInfo *P;
	
	P = (PersonalInfo *)malloc(sizeof(PersonalInfo));
	if(P == NULL){
		fprintf(stderr, "ERROR[create_info_copy]\n");
		exit(0);
	}
	int i;
	for(i = 1; i <= MAXITEMS; i ++){
		if(child->friends[i] == 1){
			P->friends[i] = 1;
		}
		else{
			P->friends[i] = 0;
		}
	}

	return P;
}

void insert_friend(PersonalInfo *P, int friend){
	
	P->friends[friend] = 1;
}

void combine_info(PersonalInfo *child, PersonalInfo *parent){
	
	int i;
	for(i = 1; i <= MAXITEMS; i ++){
		if(child->friends[i] == 1){
			parent->friends[i] = 1;
		}
	}
}

void showFP( int headItem, shortList *tail, int count, TreeNode *head ){
  int i;

  printf( "FP%d: ", 1 + tail->size );
  printf( "%d ", headItem );
  for( i=1; i <= tail->size; i++ ){
    printf( "%d ", tail->datum1[i] );
  }
  /*
  printf( "(%d)  ", count );
  
  TreeNode *node = head;
  while(node != NULL && node->info != NULL){
  	PersonalInfo *P = node->info;
  	for(i = 1; i <= MAXITEMS; i ++){
  		if(P->friends[i] == 1){
  			printf("%d ", i);
  		}
  	}
  	node = node->nodeLink;
  }
  */
  printf("\n");
}

void storeFP(int headItem, shortList *tail, int count, TreeNode *head){

  int i;
  init_itemset(&FP[sizeFP]);
  FP[sizeFP].items[headItem] = 1;
  for( i=1; i <= tail->size; i++ ){
    FP[sizeFP].items[tail->datum1[i]] = 1;
  }
  FP[sizeFP].climp = count;
  TreeNode *node = head;
  while(node != NULL && node->info != NULL){
  	if(FP[sizeFP].info == NULL){
  		PersonalInfo *P = create_info_copy(node->info);
  		FP[sizeFP].info = P;
  	}
  	else{
  		combine_info(node->info, FP[sizeFP].info);
  	}
  	node = node->nodeLink;
  }
  sizeFP ++;
  if(sizeFP == MAXITEMSETS){
  	printf("\nNEED TO INCREASE MAXITEMSETS");
  	exit(-1);
  }

}

double get_dgimp(int items[], Transaction *T){
	
	int i;
	double dgimp = 0;
	for(i = 1; i <= MAXITEMS; i ++){
		if(T->itemset[i] > 0 && items[i] == 1){
			dgimp += T->itemset[i];
		}	
	}
	return dgimp;
}

boolean in_transaction(int items[], Transaction *T){
	
	boolean result = true;
	int i;
	for(i = 1; i <= MAXITEMS && result == true; i ++){
		if(items[i] == 1 && T->itemset[i] == 0){
			result = false;
		}
	}
	return result;
}

void sortList( shortList *oList, shortList *sList, Counter *c ){
  int i;
  longList Q;

  Q.size = 0;
  for( i=1; i <= oList->size; i++ )
    insMinUQ( &Q, c->cnt[oList->datum1[i]], oList->datum1[i] );
  heapSortDescUQ( &Q );

  sList->size = oList->size;
  for( i=1; i <= Q.size; i++ )
    sList->datum1[i] = Q.datum1[i];
}

int countMem( int prevMemSpc, Header *hdr ){
  int tNode, hNode, currMemSpc;
  int h;

  if( ! CNT_MEM ) return 0;

  tNode = 0;
  hNode = 0;

  for( h=1; h <= hdr->hdrLen; h++ ){
    hNode++;
    tNode += hdr->nodeCnt[h];
  }
  currMemSpc = prevMemSpc + (1 + 3*tNode + 2*hNode);
  if( currMemSpc > maxMemSpc )
    maxMemSpc = currMemSpc;

  numNodesAllT += tNode;
  if( isGlobal ){
    numNodesGT = tNode;
    isGlobal = FALSE;
  }

  if( PRT_MEM )
    printf( "prevMemSpc = %d\tcurrMemSpc = %d\tmaxMemSpc = %d\n",
	   prevMemSpc, currMemSpc, maxMemSpc );

  return currMemSpc;
}

void showMem( void ){
  printf( "Total memory space required = %d bytes\n", 2 * maxMemSpc );
}

void countNode(Header *hdr )
{
	int tNode, hNode;
	int h;
	tNode = 0;
	hNode = 0;

	for( h=1; h <= hdr->hdrLen; h++ ){
		hNode++;
		tNode += hdr->nodeCnt[h];
	}
  	printf("Node Count = [%d]\n", tNode);
	printf("Node size DSS= [%ld]\n", sizeof(TreeNode));
	printf("Memory space required for tree = %ld bytes\n\n", tNode * sizeof(TreeNode));
}

void insertHdr( Header *H, int item, int lgwt ){
  (H->hdrLen)++;
  H->item[H->hdrLen] = item;
  H->lgwt[H->hdrLen] = 0;
  H->nodeCnt[H->hdrLen] = 0;
  H->head[H->hdrLen] = NULL;
  H->tail[H->hdrLen] = NULL;
  H->mapHdr[item] = H->hdrLen;
}

void showHdr( Header *H ){
  int i;

  printf( "Header (len=%d):\n", H->hdrLen );
  for( i=1; i <= H->hdrLen; i++ )
    printf( "\t[%d]\t%d %d %ld %ld lgwt: %d\n", i, H->item[i], H->nodeCnt[i], (intptr_t)(H->head[i]), (intptr_t)(H->tail[i]), H->lgwt[i] );
}

void showFullHdr( Header *H ){
  int i;
  TreeNode *temp;

  printf( "Header %ld (len=%d):\n", (intptr_t)H, H->hdrLen );
  for( i=1; i <= H->hdrLen; i++ ){
    printf( "\t[%d]\t%d %d %ld %ld:", i,
	   H->item[i], H->nodeCnt[i], (intptr_t)(H->head[i]), (intptr_t)(H->tail[i]) );
    temp = H->head[i];
    while( temp != NULL ){
      printf( " %d", temp->item );
      temp = temp->nodeLink;
    }
    printf( "\n" );
  }
}

TreeNode *matchChild( int item, TreeNode *tree ){
  TreeNode *X = tree->firstChild;

  while( (X != NULL) && (X->item != item) )
    X = X->sibling;
  return X;
}

void showTree2helper(TreeNode *tree, int depth ){
  TreeNode *temp;
  int i;

  temp = tree;
  while( temp != NULL ){
    for( i=1; i <= depth; i++ )
      printf( "     " );
    printf( "%d (%d)\n", temp->item, temp->count );
    temp = temp->firstChild;
    showTree2helper( temp, depth+1 );
    while( temp != NULL ){
      temp = temp->sibling;
      showTree2helper( temp, depth+1 );
    }
  }
}

void showTree2( TreeNode *tree ){
  printf( "Tree %ld:\n", (intptr_t)tree );
  showTree2helper( tree, 0 );
}

void showTree( TreeNode *tree ){
  TreeNode *temp;
  printf("\n");
  temp = tree;
  while( temp != NULL ){
    printf( "tree: %d (%d)\n", temp->item, temp->count );
    temp = temp->firstChild;
  }

}

void insertTree( Header *H, shortList *list, PersonalInfo *P, int count, int ind, int indMax, TreeNode *tree ){

  TreeNode *N;
  int item, mappedItem;

  if( list->size == 0 ){
    return;
  }
  item = list->datum1[ind];
  mappedItem = H->mapHdr[item];

  if( tree->firstChild == NULL ){
     // IF FIRST CHILD NULL
  	//printf("\nInsert item (%d) First child null", item);
    N = createNewNode( item, count );
    N->parent = tree;
    tree->firstChild = N;
    tree->lastChild = N;
    if( H->tail[mappedItem] == NULL ){
		// IF HEADER TABLE POINTS TO NULL
      H->head[mappedItem] = N;
      H->tail[mappedItem] = N;
    }else{
		// IF HEADER TABLE HAS LINKS
      (H->tail[mappedItem])->nodeLink = N;
      H->tail[mappedItem] = N;
    }
    (H->nodeCnt[mappedItem])++;
    (H->lgwt[mappedItem]) += count;
  }else{
	// HAS CHILD
	
    N = matchChild( item, tree );
    if( N != NULL ){
          //printf("\nInsert item (%d) Match found with child", item);
          //MATCH FOUND WITH ON OF THE CHILD
		N->count += count;
		//node count doesn't increase because not adding a node here
		(H->lgwt[mappedItem]) += count;
    }
    else{
   // printf("\nInsert item (%d) No match found with child", item);
		// NO MATCH FOUND WITH THE CHILDREN
      N = createNewNode( item, count );
      N->parent = tree;
      (tree->lastChild)->sibling = N;
      tree->lastChild = N;
      if( H->tail[mappedItem] == NULL ){
		H->head[mappedItem] = N;
		H->tail[mappedItem] = N;
      }else{
		(H->tail[mappedItem])->nodeLink = N;
		H->tail[mappedItem] = N;
      }
      (H->nodeCnt[mappedItem])++;
      (H->lgwt[mappedItem]) += count;
    }
  }
  //if we are the last child in the list
  //add personal information
  if(ind == indMax && N->info == NULL && P != NULL){
  	N->info = P;
  }
  else if(ind == indMax && N->info != NULL && P != NULL){
  	combine_info(P, N->info);
  }
  
  if( DEBUG ){
    showTree( tree );
    showHdr( H );
  }
  if( ind < indMax ) // INSERT THE NEXT ITEM IN THE TRANSACTION
    insertTree( H, list, P, count, ind+1, indMax, N );
}

void insertTreeRev( Header *H, shortList *list, PersonalInfo *P, int count, int ind,
		   int indMin, TreeNode *tree ){
  TreeNode *N;
  int item, mappedItem;

  if( list->size == 0 ) return;

  item = list->datum1[ind];
  mappedItem = H->mapHdr[item];

  if( tree->firstChild == NULL ){
    N = createNewNode( item, count );
    N->parent = tree;
    tree->firstChild = N;
    tree->lastChild = N;
    if( H->tail[mappedItem] == NULL ){
      H->head[mappedItem] = N;
      H->tail[mappedItem] = N;
    }else{
      (H->tail[mappedItem])->nodeLink = N;
      H->tail[mappedItem] = N;
    }
    (H->nodeCnt[mappedItem])++;
    (H->lgwt[mappedItem]) += count;
  }else{
    N = matchChild( item, tree );
    if( N != NULL )
      N->count += count;
    else{
      N = createNewNode( item, count );
      N->parent = tree;
      (tree->lastChild)->sibling = N;
      tree->lastChild = N;
      if( H->tail[mappedItem] == NULL ){
	H->head[mappedItem] = N;
	H->tail[mappedItem] = N;
      }else{
	(H->tail[mappedItem])->nodeLink = N;
	H->tail[mappedItem] = N;
      }
      (H->nodeCnt[mappedItem])++;
      (H->lgwt[mappedItem]) += count;
    }
  }
  if(ind == indMin && N->info == NULL && P != NULL){
  	N->info = P;
  }
  else if(ind == indMin && N->info != NULL && P != NULL){
  	combine_info(P, N->info);
  }
  if( DEBUG ){
    showTree( tree );
    showHdr( H );
  }
  if( ind > indMin )
    insertTreeRev( H, list, P, count, ind-1, indMin, N );
}

int isSinglePath( TreeNode *tree ){
  TreeNode *temp = tree;

  while( temp != NULL ){
    if( temp->firstChild != temp->lastChild )
      return FALSE;
    temp = temp->firstChild;
  }
  return TRUE;
}

/* path to list Top-Down */
void pathToListTD( TreeNode *tree, shortList *list ){
  TreeNode *t;

  list->size = 0;
  t = tree->firstChild;
  while( t != NULL ){
    (list->size)++;
    list->key[list->size] = t->count;
    list->datum1[list->size] = t->item;
    t = t->firstChild;
  }
}

/* choose(n,k) = n! / k! (n-k)! = prod_{i=k+1}^{n} i / (n-k)! */
int choose( int n, int k ){
  int i, prod;
  int L, S;

  L = MAX(k, n-k);
  S = MIN(k, n-k);

  prod = 1;
  for( i=n; i >= L+1; i-- )
    prod *= i;
  for( i=S; i >= 2; i-- )
    prod /= i;
  return prod;
}

/* mine( head | tail ) */
void mine( shortList *head, shortList *tail ){
  int j, k;
  shortList head2;
  shortList tail2;

  if( head->size == 0 ){
    fprintf( stderr, "ERROR[mine]: Infrequent (0H)\n" );
    exit( -1 );
  }

  if( CNT_FP ){
    for( k = 1; k <= head->size; k++ )
      countL[MIN(k + tail->size,MAXLEVEL)] += choose(head->size,k);
    return;
  }

  if( head->size == 1 ){
    (countL[MIN(1 + tail->size,MAXLEVEL)])++;
    //if( PRT_FP ){
    //  if( head->key[1] >= minsup ){
	//	showFP( head->datum1[1], tail, head->key[1] );
    // }else{
	//	fprintf( stderr, "ERROR[mine]: Infrequent (1H)\n" );
	//	exit( -1 );
    // }
    //}
  }else{
    for( k = tail->size; k >= 1; k-- ){
      tail2.datum1[k+1] = tail->datum1[k];
      tail2.key[k+1] = tail->key[k];
    }
    tail2.size = tail->size + 1;

    for( k = 1; k < head->size; k++ ){
      head2.datum1[k] = head->datum1[k];
      head2.key[k] = head->key[k];
    }

    for( j = head->size; j >= 1; j-- ){
      #if CNT_FP
	    (countL[MIN(tail2.size,MAXLEVEL)])++;
	  #endif
//      if( PRT_FP ){
//		if( head->key[j] >= minsup ){
//		  showFP( head->datum1[j], tail, head->key[1] );
//		}else{
//		  fprintf( stderr, "ERROR[mine]: Infrequent (mH)\n" );
//		  exit( -1 );
//		}
//      }
      if( j >= 2 ){
	head2.size = j - 1;
	tail2.datum1[1] = head->datum1[j];
	tail2.key[1] = head->key[j];
	mine( &head2, &tail2 );
      }
    }
  }
}

void countFreq( TreeNode *leaf, Counter *c, int count ){
  TreeNode *X;

  X = leaf;
  while( (X != NULL) && (X->item != ROOT) ){
    c->cnt[X->item] += count;
    X = X->parent;
  }
}

void getRevList( Counter *c, TreeNode *N, shortList *list, int minSig ){
  TreeNode *X;

  list->size = 0;
  X = N;
  while( X != NULL ){
    if( (c->cnt[X->item] >= minSig) && (X->item != ROOT) ){
      (list->size)++;
      list->datum1[list->size] = X->item;
      list->key[list->size] = X->count;
    }
    X = X->parent;
  }
}

void freeTree( TreeNode *tree, Header *hdr ){
  int i;
  TreeNode *head, *temp;

  for( i=1; i <= hdr->hdrLen; i++ ){
    head = hdr->head[i];
    while( head != NULL ){
      temp = head;
      head = head->nodeLink;
      if(temp->info != NULL){
      	//free(temp->info); //how to free the info?
      }
      free( temp );
    }
  }
  free( tree );
}

void FPgrowth( Header *H, TreeNode *tree, shortList *alpha, int memSpc, int minSig){
  int h, i, k;
  Counter c;
  TreeNode *leaf;
  shortList list, RList;
  Header LH;
  TreeNode *bTree;
  shortList alpha2;
  longList Q;

  if( SING_PATH && isSinglePath(tree) ){
    /* SINGLE-PATH TREE: extract items into a list in top-down fashion */
    if( DEBUG ) printf( "single path\n" );
    pathToListTD( tree, &list );		// COPY THE PATH TO THE LIST
    if( DEBUG ) showSList( &list );
    mine( &list, alpha );				// MINE THE ITEMS IN THE LIST
  }else{
	  // IF NOT SINGLE PATH TREE I.E. MULTI-PART TREE
    if( DEBUG ) printf( "multi path\n" );
    // printf("[%d]", H->hdrLen);
    for( h = H->hdrLen; h >= 1; h-- ){
	      if( DEBUG ) printf( "multi path: %d\n", H->item[h] );
	      /* NOTE: H->head[h]->item == H->item[h] */

	      leaf = H->head[h];
	      for( i=1; i <= MAXITEMS; i++ )
			c.cnt[i] = 0;
	      while( leaf != NULL ){
			// CALC THE FREQ OF THE NODES IN THE CURRENT PATH
			countFreq( leaf, &c, leaf->count );
			leaf = leaf->nodeLink;
	      }

	      //if( CNT_CCC ){
		/* Upper bound: numSupCnt += H->hdrLen; */
		/* Reasonable bound (impl): numSupCnt += h; */
		/* Tighter bound: */
			//for( i=1; i < h; i++ )
				//if( c.cnt[H->item[i]] > 0 ) numSupCnt++;
	      //}
		#if CNT_FP
	      (countL[MIN(1 + alpha->size,MAXLEVEL)])++;
	    #endif
//here print out the frequent patterns
		  if( PRT_FP ){
			if( c.cnt[H->item[h]] >= minSig ){
			  showFP( H->item[h], alpha, c.cnt[H->item[h]], H->head[h] );
			  storeFP( H->item[h], alpha, c.cnt[H->item[h]], H->head[h] );
			  if(PRT_FALSE_POS){
			  	initial_number ++;
			  }
			}
	      }

	      if( SORT_TREE ){	// WHY??
			Q.size = 0;
			for( i=1; i < h; i++ )
			  if( c.cnt[H->item[i]] >= minSig ){
				insMinUQ( &Q, c.cnt[H->item[i]], H->item[i] );
			  }
			heapSortDescUQ( &Q );
			if( DEBUG ) showHeapUQ( &Q );

			cleanHdr( &LH );		// CREATE THE HEADER OF PROJECTED-DB
			for( i=1; i <= Q.size; i++ )
			  insertHdr( &LH, Q.datum1[i], 0 ); //CHANGE THIS 0
		  }else{ /* NO SORT_TREE */
			cleanHdr( &LH );
			for( i=1; i < h; i++ )
			  if( c.cnt[H->item[i]] >= minSig )
				insertHdr( &LH, H->item[i] , 0); //CHANGE THIS 0
	      }
		if(LH.hdrLen <= 0){
			leaf = H->head[h];
			while(leaf != NULL){
		
				if(leaf->info != NULL && leaf->parent->info == NULL){
					PersonalInfo *P = create_info_copy(leaf->info);
					leaf->parent->info = P;
				}
				else if(leaf->parent->info != NULL && leaf->info != NULL){
					combine_info(leaf->info, leaf->parent->info);
				}
				leaf = leaf->nodeLink;
			}
		}
	      if( LH.hdrLen > 0 ){
			bTree = createNewNode( ROOT, 1 ); // PROJ-TREE ROOT NODE
			leaf = H->head[h];
			while( leaf != NULL ){			// BUILD THE PROJ-TREE
			  if(leaf->info != NULL && leaf->parent->info == NULL){
				PersonalInfo *P = create_info_copy(leaf->info);
				leaf->parent->info = P;
			  }
			  else if(leaf->parent->info != NULL && leaf->info != NULL){
				combine_info(leaf->info, leaf->parent->info);
			  }
			  getRevList( &c, leaf->parent, &list, minSig );
			  if( list.size > 0 ){
				if( SORT_TREE ){
				  sortList( &list, &RList, &c );
				  insertTree( &LH, &RList, leaf->info, leaf->count, 1, RList.size, bTree );
				}else{
				  insertTreeRev( &LH, &list, leaf->info, leaf->count, 1, list.size, bTree );
				}
			  }
			  leaf = leaf->nodeLink;
			}

			if( DEBUG ){
			  showFullHdr( &LH );
			  showTree2( bTree );
			}
			for( k = alpha->size; k >= 1; k-- ){
			  alpha2.datum1[k+1] = alpha->datum1[k];
			  alpha2.key[k+1] = alpha->key[k];
			}
			alpha2.datum1[1] = H->item[h];
			alpha2.key[1] = c.cnt[H->item[h]];
			alpha2.size = alpha->size + 1;
			FPgrowth( &LH, bTree, &alpha2, countMem(memSpc,&LH), minSig );
			freeTree( bTree, &LH );
	      }
	  }
  }
  if( DEBUG ) printf( "FP growth: Completed\n" );
}

/* ======================================================================= */

int main( int argc, char *argv[] ){

  int items[MAXITEMS+1];
  int i, j;
  FILE *fpOrg, *fpConf, *fpRev;
  int numTrans, transInd, pid, numItems, item, weight;
  float conf;
  double minSig;
  int sizeDB;
  double weight_DB = 0;
  longList Q;
  TreeNode *root;
  Header H;
  shortList nullList;
  shortList SQ;
  sizeFP = 0;
  
  float confidence[MAXITEMS + 1];
  double limp[MAXTRANSACTIONS + 1];
  double dlimp_DB = 0;
  double climp[MAXITEMS + 1];
  double dgimp[MAXITEMS + 1];
  double sig[MAXITEMS + 1];

  struct timeval  start_time, end_time; /* structs for timer     */
  struct timezone zone;
  long int sec = 0, usec = 0; /* sec & microsec for the timer    */
  
  long int time_total_sec = 0;
  double time_total_msec = 0;
  long int time_total_usec = 0;
  
  initial_number = 0;

   if( argc != 5 ){
     fprintf( stderr, "Usage: %s database confidenceTable outFile minSig\n", argv[0] );
     exit( 0 );
   }

   fpOrg = fopen( argv[1], "r" );
   fpConf = fopen(argv[2], "r" );
   fpRev = fopen( argv[3], "w" );
   minSig = atof( argv[4] );

   //setTransNum = atoi(argv[4]);	// to change the size of the data set
  printf( "===== %s %s %s %f =====\n\n", argv[0], argv[1], argv[2], minSig );

  if( (fpOrg == NULL) || (fpConf == NULL) || (fpRev == NULL) ){
    fprintf( stdout, "ERROR[%s]: Can't open %s or %s or %s\n", argv[0], argv[1], argv[2], argv[3] );
    fprintf( stderr, "ERROR[%s]: Can't open %s or %s or %s\n", argv[0], argv[1], argv[2], argv[3] );
    fprintf( stderr, "ERROR[%s]: Can't open %s or %s or %s\n", argv[0], argv[1], argv[2], argv[3] );
    exit( 0 );
  }

  //numConstrChk = 0;
  numSupCnt = 0;
  numNodesGT = 0;
  numNodesAllT = 0;
  isGlobal = TRUE;

  /* Construct FP-tree */
  for( i = 1; i <= MAXITEMS; i++ ){
    items[i] = 0;
    confidence[i] = 0;
    climp[i] = -1;
    dgimp[i] = 0;
    sig[i] = 0;
  }
  for( i = 1; i <= MAXTRANSACTIONS; i ++){
  	limp[i] = 0;
  }
  
  //record the time for the first db scan
  if(gettimeofday(&start_time, &zone) == -1){
    fprintf(stderr, "gettimeofday error\n");
  }
  
	fscanf(fpConf, "%d ", &numItems); 
	for(i = 1; i <= numItems; i ++){
	
		fscanf(fpConf, "%d %f ", &item, &conf);
		confidence[item] = conf;
	}

  fscanf( fpOrg, "%d ", &numTrans );
  sizeDB = numTrans;
	for(i = 1; i <= numTrans; i ++){
	
		fscanf(fpOrg, "%d ", &pid);
		fscanf(fpOrg, "%d ", &numItems);

		for(j = 1; j <= numItems; j ++){
			fscanf(fpOrg, "%d %d ", &item, &weight);

			items[item] = 1;
			limp[i] += (weight * confidence[item]);
			dgimp[item] += (weight * confidence[item]);
		}
		dlimp_DB += limp[i];
		
		for(j = 1; j <= MAXITEMS; j ++){
			if(items[j] == 1){
				if(climp[j] == -1){
					climp[j] = 0;
				}
				climp[j] += limp[i];
				items[j] = 0;
			}
		}
		weight_DB += limp[i];
	}
	
	if(gettimeofday(&end_time, &zone) == 0){
      	if(end_time.tv_usec >= start_time.tv_usec){
      		sec  = end_time.tv_sec - start_time.tv_sec;
      		usec = end_time.tv_usec - start_time.tv_usec;
      	}else{
      		sec  = end_time.tv_sec - start_time.tv_sec - 1;
      		usec = end_time.tv_usec - start_time.tv_usec + 1000000;
      	}
      	time_total_sec += sec;
      	time_total_usec += usec;
      	
      	fprintf(stdout, "\n[SF-Tree] Total runtime for first db scan is %ld sec. %.3f msec\n", sec, usec/1000.0);
      	fpRev = fopen( argv[3], "a" );
      	fprintf(fpRev, "\n[SF-Tree] Total runtime for first db scan is %ld sec. %.3f msec\n", sec, usec/1000.0);
      	fclose( fpRev );
      }
      
	for(i = 1; i <= MAXITEMS; i ++){
		sig[i] = dgimp[i] / dlimp_DB;
	}

	if(DEBUG){
		printf("\n");
		for(i = 1; i <= MAXITEMS; i ++){
			printf("\nitem (%d) has conf: %f", i, confidence[i]);
		}
		printf("\n");
		for(i = 1; i <= MAXTRANSACTIONS; i ++){
			printf("\nL%d has limp: %f", i, limp[i]);
		}
		printf("\n");
		printf("\nlimp(DB): %f", dlimp_DB);
		printf("\n");
		for(i = 1; i <= MAXITEMS; i ++){
			printf("\nitem (%d) has climp: %f", i, climp[i]);
		
		}
		printf("\n");
		for(i = 1; i <= MAXITEMS; i ++){
			printf("\nitem (%d) has dgimp: %f", i, dgimp[i]);
		
		}
		printf("\n");
		for(i = 1; i <= MAXITEMS; i ++){
			printf("\nitem (%d) has sig: %f", i, sig[i]);
		
		}
	}
	
  //if( CNT_CCC ){
    /* Upper bound: numSupCnt += "domItems" */
    /* Tigher bound: */
    //for( i=1; i <= MAXITEMS; i++ )
      //if( L1[i] > 0 ){ numConstrChk++; numSupCnt++; }
  //}

  /* sort the valid domain items in descending order of support count */
  
  Q.size = 0;
  for( i = 1; i <= MAXITEMS; i++ ){

    if(climp[i] >= MIN_CLIMP(dlimp_DB, minSig)){
      insMinUQ(&Q, climp[i], i);
    }
  }
    
  heapSortDescUQ( &Q );
  if( DEBUG ) showHeapUQ( &Q );

  cleanHdr( &H );
  for( i=1; i <= Q.size; i++ )
    insertHdr( &H, Q.datum1[i], Q.key[i]);

  if( DEBUG ) showHdr( &H );
 
  //printf("msg1a\n");
  if( H.hdrLen > 0 ){ 
    root = createNewNode( ROOT, 1 );

    rewind( fpOrg );
    fscanf( fpOrg, "%d ", &numTrans );

    //record the time for creating the tree
    if(gettimeofday(&start_time, &zone) == -1){
    	 fprintf(stderr, "gettimeofday error\n");
    }
    
    for( transInd = 1; transInd <= numTrans; transInd++ ){

      SQ.size = 0;
      fscanf( fpOrg, "%d ", &pid );
      fscanf( fpOrg, "%d ", &numItems );
      for( i = 1; i <= numItems; i++ ){
		fscanf( fpOrg, "%d %d ", &item, &weight );
		
		if(climp[item] < MIN_CLIMP(dlimp_DB, minSig)){
			
			limp[transInd] -= (weight * confidence[item]);
		}
		items[item] = 1;
		
      }
      //insert each transaction one by one into the tree ie. insert L1 then L2, then L3 separately
      for(i = 1; i <= MAXITEMS; i ++){
      	if(items[i] == 1){
      		if(climp[i] >= MIN_CLIMP(dlimp_DB, minSig)){
      		
				insMinUList( &SQ, climp[i], i ); 
			}
			items[i] = 0;
      	}
      }
      heapSortDescUList( &SQ );

     // if( DEBUG ) showHeapUList( &SQ );
     PersonalInfo *P = create_info(transInd);
      insertTree( &H, &SQ, P, limp[transInd], 1, SQ.size, root );
    }
    
    	if(gettimeofday(&end_time, &zone) == 0){
	 	if(end_time.tv_usec >= start_time.tv_usec){
	 		sec  = end_time.tv_sec - start_time.tv_sec;
	 		usec = end_time.tv_usec - start_time.tv_usec;
	 	}else{
	 		sec  = end_time.tv_sec - start_time.tv_sec - 1;
	 		usec = end_time.tv_usec - start_time.tv_usec + 1000000;
	 	}
	 	time_total_sec += sec;
      	time_total_usec += usec;
      	
	 	fprintf(stdout, "\n[SF-Tree] Total runtime for creating tree is %ld sec. %.3f msec\n", sec, usec/1000.0);
	 	fpRev = fopen( argv[3], "a" );
	 	fprintf(fpRev, "\n[SF-Tree] Total runtime for creating tree is %ld sec. %.3f msec\n", sec, usec/1000.0);
	 	fclose( fpRev );
 	}
 	
     if(DEBUG){
		printf("\n");
		for(i = 1; i <= MAXITEMS; i ++){
			printf("\nL%d has limp: %f", i, limp[i]);
	
		}
	}
  
  if(PRT_MEM){
  	printf("\nMemory usage for initial tree:\n");
  	countNode(&H);
  }
  //return 0;
    //if( DEBUG ){
    //  showTree2( root );
    //  showFullHdr( &H );
    //}

	nullList.size = 0;
	
	//record the time for the FP-Growth
	if(gettimeofday(&start_time, &zone) == -1){
		fprintf(stderr, "gettimeofday error\n");
	}
	
	FPgrowth( &H, root, &nullList, countMem(0,&H), MIN_CLIMP(dlimp_DB, minSig) );
	
	if(gettimeofday(&end_time, &zone) == 0){
	 	if(end_time.tv_usec >= start_time.tv_usec){
	 		sec  = end_time.tv_sec - start_time.tv_sec;
	 		usec = end_time.tv_usec - start_time.tv_usec;
	 	}else{
	 		sec  = end_time.tv_sec - start_time.tv_sec - 1;
	 		usec = end_time.tv_usec - start_time.tv_usec + 1000000;
	 	}
      	time_total_sec += sec;
      	time_total_usec += usec;
      	
	 	fprintf(stdout, "\n[SF-Tree] Total runtime for FP-Growth is %ld sec. %.3f msec\n", sec, usec/1000.0);
	 	fpRev = fopen( argv[3], "a" );
	 	fprintf(fpRev, "\n[SF-Tree] Total runtime for FP-Growth is %ld sec. %.3f msec\n", sec, usec/1000.0);
	 	fclose( fpRev );
 	}
	freeTree( root, &H );
  }

 // showMem();
#if CNT_FP
  for( i=1; i <= MAXLEVEL; i++ )
 	if(countL[i]!=0)
 	    printf( "|L%d| = %d\n", i, countL[i] );
#endif
//  if( CNT_CCC ){
//    printf( "numConstrChk = |F1| = %d;\n", numConstrChk );
//    printf( "numSupCnt = %d;\n", numSupCnt );
//    printf( "numNodes = %d (in global tree), %d (in all trees)\n",
//	   numNodesGT, numNodesAllT );
//  }
  
	//read the db a 3rd time to get strong group of friends
	rewind(fpOrg);
	
	//record the time for the last db scan
	if(gettimeofday(&start_time, &zone) == -1){
		fprintf(stderr, "gettimeofday error\n");
	}
	
  	fscanf( fpOrg, "%d ", &numTrans );
	for(i = 1; i <= numTrans; i ++){
	
		fscanf(fpOrg, "%d %d ", &pid, &numItems);
		
		Transaction T;
		init_transaction(&T);
		for(j = 1; j <= numItems; j ++){
			fscanf(fpOrg, "%d %d ", &item, &weight);
			(T.itemset[item]) += (weight * confidence[item]);
		}
		for(j = 0; j < sizeFP; j ++){
			if(in_transaction(FP[j].items, &T) == true){
				FP[j].dgimp += get_dgimp(FP[j].items, &T);
			}
		}
	}
	
	if(gettimeofday(&end_time, &zone) == 0){
	 	if(end_time.tv_usec >= start_time.tv_usec){
	 		sec  = end_time.tv_sec - start_time.tv_sec;
	 		usec = end_time.tv_usec - start_time.tv_usec;
	 	}else{
	 		sec  = end_time.tv_sec - start_time.tv_sec - 1;
	 		usec = end_time.tv_usec - start_time.tv_usec + 1000000;
	 	}
     	time_total_sec += sec;
      	time_total_usec += usec;
      	
	 	fprintf(stdout, "\n[SF-Tree] Total runtime for last db scan is %ld sec. %.3f msec\n", sec, usec/1000.0);
	 	fpRev = fopen( argv[3], "a" );
	 	fprintf(fpRev, "\n[SF-Tree] Total runtime for last db scan is %ld sec. %.3f msec\n", sec, usec/1000.0);
	 	fclose( fpRev );
 	}
	
  fpRev = fopen( argv[3], "a" );
  if(PRT_FP){
     
	printf("\nFound ShFrequent Itemsets:");
	fprintf(fpRev, "\nFound ShFrequent Itemsets:");
	//printf("\nsig: [%f] weightdb: [%f] dlimpdb: [%f] minclimp: [%f]\n", minSig, weight_DB, dlimp_DB, MIN_CLIMP(dlimp_DB, minSig) );
	int counter = 0;
	for(i = 0; i < sizeFP; i ++){
		double ratio = FP[i].dgimp / weight_DB;
		//don't round
		//double sig = (floor(ratio * 100 + 0.5)) / 100;
		if(ratio >= minSig){
			print_itemset(&FP[i], fpRev);
			//printf(" climp [%d] dgimp [%f] str [%f]", FP[i].climp, FP[i].dgimp, ratio);
			counter ++;
		}
	}
	printf("\n\nFound (%d) ShFrequent Itemsets\n", counter);
	if(PRT_FALSE_POS){
		printf("\nFalse Positives: %d\n", initial_number - counter);
  	}
  }
  
    	time_total_msec = time_total_usec / 1000.0;
  	if(time_total_msec >= 1000){
  		time_total_sec += floor(time_total_msec/1000);
  		time_total_msec = time_total_usec % 1000;
  	}
  	
  	//printf("\ntime sec: %ld time msec: %.3lf time usec: %ld", time_total_sec, time_total_msec, time_total_usec);

	fprintf(stdout, "\n[SF-Tree] Total (aggregate) runtime is %ld sec. %.3lf msec\n", time_total_sec, time_total_msec);
	fprintf(fpRev, "\n[SF-Tree] Total (aggregate) runtime is %ld sec. %.3lf msec\n", time_total_sec, time_total_msec);

  fclose(fpOrg);
  fclose(fpConf);
  fclose(fpRev);
  printf( "\n===== %s %s %s %f: Completed =====\n\n", argv[0], argv[1], argv[2], minSig );

  return 0;
}

/* ======================================================================= */

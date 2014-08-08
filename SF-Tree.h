/*
  Last Modified: July 30, 2012
 
  SF-Tree.h
  
  (C) 2003-2011 U Manitoba Database & Data Mining Lab

  Header file of FP-tree based algorithm

  *** For U Manitoba CS DB Lab (Dr. Carson K. Leung) only ***
  *** Please do NOT re-distribute this code without permission from DBLab ***
*/

#ifndef _FPGROWTH_H
#define _FPGROWTH_H

#define MAXLEVEL       	10
#define MAXITEMS     	10 /* 100, 1000, 10000 */
#define MAXQITEM     	10000 /* 100, 1000, 10000 */
#define MAXLISTITEMS  	100 /* 64 */
#define MAXTRANSACTIONS 	20
#define MAXITEMSETS  	5000
#define ROOT            	0

#define TRUE      		1
#define FALSE     		0
#define INVALID 		-10

#define PARENT(x) ((int)(floor((x)/2))) 
#define LEFT(x)   ((2*(x)))
#define RIGHT(x)  ((2*(x) + 1))

#define MIN(x,y) ((x) < (y) ? (x) : (y))
#define MAX(x,y) ((x) >= (y) ? (x) : (y))

#define MIN_CLIMP(x,y) ((x)*(y))

typedef enum BOOL{
	false = 0,
	true = 1
} boolean;

typedef struct{
	int friends[MAXITEMS + 1];
	//int friends;
} PersonalInfo;

typedef struct{
	int items[MAXITEMS + 1];
	int climp;
	double dgimp;
	PersonalInfo *info;
} Itemset;

typedef struct{
	double itemset[MAXITEMS + 1]; //stores the support of each item ie. support of item X = itemset[X]
} Transaction;

typedef struct tN{
  int item;
  int count;
  PersonalInfo *info;
  struct tN *parent;
  struct tN *firstChild;
  struct tN *lastChild;
  struct tN *sibling;
  struct tN *nodeLink;
} TreeNode;
  
typedef struct{
  int hdrLen;
  int item[MAXITEMS+1];
  int lgwt[MAXITEMS+1];	//added this, may not actually need it
  int nodeCnt[MAXITEMS+1];
  TreeNode *head[MAXITEMS+1];
  TreeNode *tail[MAXITEMS+1];
  int mapHdr[MAXITEMS+1];
} Header;

typedef struct{
  int size;
  int key[MAXITEMS+1];
  int datum1[MAXITEMS+1];
} longList;

typedef struct{
  int size;
  int key[MAXITEMS+1];
  int datum0[MAXITEMS+1];
  int datum1[MAXITEMS+1];
} longBList;

typedef struct{
  int size;
  int key[MAXLISTITEMS+1];
  int datum1[MAXLISTITEMS+1]; //stores FP
} shortList;

typedef struct{
  int size;
  int key[MAXLISTITEMS+1];
  int datum0[MAXLISTITEMS+1];
  int datum1[MAXLISTITEMS+1];
} shortBList;

typedef struct{
  int cnt[MAXITEMS+1];
} Counter;

void heapifyMaxUQ( longList *A, int i );
int extractMaxUQ( longList *A, int *datum1 );
void insMaxUQ( longList *A, int keyVal, int datum1 );
void heapifyMinUQ( longList *A, int i );
int extractMinUQ( longList *A, int *datum1 );
void insMinUQ( longList *A, int keyVal, int datum1 );
void heapSortAscUQ( longList *A );
void heapSortDescUQ( longList *A );
void showHeapUQ( longList *A );
void showList( longList *A );

void heapifyMaxUList( shortList *A, int i );
int extractMaxUList( shortList *A, int *datum1 );
void insMaxUList( shortList *A, int keyVal, int datum1 );
void heapifyMinUList( shortList *A, int i );
int extractMinUList( shortList *A, int *datum1 );
void insMinUList( shortList *A, int keyVal, int datum1 );
void heapSortAscUList( shortList *A );
void heapSortDescUList( shortList *A );
void showHeapUList( shortList *A );
void showSList( shortList *A );

#endif

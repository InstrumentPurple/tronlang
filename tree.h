#pragma once
/* Sept. 26, 2019 */
#include <stdbool.h>
#include <stdint.h>



/*
 * LIST DECLARATIONS
 */

#ifdef __cplusplus  
extern "C" { 
#endif 



typedef void (*effect)(void*);

typedef struct list_node{
  struct list_node *next;
  void *data;
} list_node;

typedef struct list{
  struct list_node *head;
  struct list_node **tail;
} list;

/* list_init must be called before a list is used */
static inline
void list_init(list *subject)
{
  subject->head = 0;
  subject->tail = &(subject->head);
}


/* assigns data to new tail and advances tail to new tail */
void list_insert(list *collection, void *data);


/* functional style of list iteration.
 * fun is given the data pointer of a previously
 * inserted element. */
void list_apply(list *collection, effect fun);


/* frees all data and nodes inserted and calls list_init
 * incase the list is reused */
void list_destruct_all(list *collection);

/* frees all data but not the nodes */
void list_destruct_data(list *collection);

/* frees all nodes but not the pointer inserted */
void list_destruct(list *collection);


/* the **tail isn't actually a pointer to the tail node;
 * however sometimes we might want that pointer. */
list_node * list_tail(list *collection);


/* function adhering to the declartion of effect.
 * you might use with list_apply thusly:
 * list_apply(L, print_voidstar); */
void print_voidstar(void *string);


/* converts a unix style directory to a list so
 * it might be iterated through easier */
void dir_to_list_alloc(const char *dir, list *collection);

void list_str(const char *dir, list *collection, char delim);

/* output list to stdout */
void list_print(list *lst);

/* output the data element of a single node */
void list_print_data(void *lst_node);




/* 
 * QUEUE  DECLARATIONS
 */



list_node * dequeue(list *collection);

static inline
void enqueue(list *collection, void *data)
{ list_insert(collection, data); }





/*
 * STACK DECLARATIONS
 */



list_node* stack_push(list *coconut, void *rock);

static inline
list_node* stack_pop(list *coconut)
{ if(coconut != 0) return dequeue(coconut); return 0; }





/*
 * BINARY SEARCH TREE DECLARATIONS
 */



/* sept. 19, 2019 */

typedef struct bst_node {
  const char *key;
  void *data;
  struct bst_node *left;
  struct bst_node *right;
} bst_node;

/* initializes and allocations a new bst_node */
bst_node * bst_node_init(const char* key, void *data);

/* inserts data into a bst by it's key */
bool bst_insert(const char* key, void *data, bst_node **cur);

/* Is tollerant of existing nodes. If it is not found then it is inserted.
 * returns a pointer to the existing node or the one that was inserted. */
bst_node * bst_insert_get(const char* key, void *data, bst_node **cur);

/* finds an existing node and returns the data
 * that is associated with key */
void * bst_find(const char* key, bst_node **root);

/* removes an existing node by it's associated key */
bool bst_delete(const char* key, bst_node **root);

void bst_destroy(bst_node *cur);

/* destroys an existing bst and sets root to null */
void bst_destruct(bst_node **root);

void bst_destroy_all(bst_node *cur);

/* same as bst_destruct but frees both key and data
 * if they were both dynamically alloc'd */
void bst_destruct_all(bst_node **root);

/* prints a bst. Only works if data is a string */
void bst_print(bst_node *cur);

/* apply the function to the data member with
 * in-order traversal */
void bst_in_order(bst_node *cur, effect fun);

/* Do a inorder and bop steck*/
void bst_to_stack(bst_node *root, list *dest);


/*
 * TREE DECLARATIONS
 */



/* If the node being considered has a null key then
 * it is a terminal node / a file. */


typedef bst_node tree;

/* inserts data into a general tree into a location
 * specified by path */
void tree_insert(tree **root, list *path, void *data);

void tree_insert_str(tree **root, char *path, void *data);


/* create a path but don't insert data / a file
 * similar to mkdir UNIX command.
 * returns a pointer to the last node created
 * along the path. */
tree* tree_make_path(tree **root, list *path);

/* same as tree_make_path but uses a UNIX style dir
 * instead of a linked list */
tree* tree_make_path_str(tree **root, const char *path);

/* prints an existing tree to stdout */
void tree_print(tree *cur);

/* find node associated with the path.
 * The node or path could be a directory or file.
 * You can tell if a returned node is a directory
 * or file whether the key is set to null. Null
 * means the node is a file. */
tree * tree_find(tree **root, list *path);

tree * tree_find_str(tree **root, char *path);

void tree_destruct(tree **root);

static inline
bool is_file(tree *subTree)
{  return subTree->key == 0;  }



void sortToList(list *containerDest, bst_node **containerSrc );


#ifdef __cplusplus 
} 
#endif 
/* Sept. 26, 2019 */

/* Permission is hereby granted, free of charge,
*  to any person obtaining a copy of this software
*  and associated documentation files (the "Software"),
*  to deal in the Software without restriction, including
*  without limitation the rights to use, copy, modify,
*  merge, publish, distribute, sublicense, and/or sell
*  copies of the Software, and to permit persons to whom the 
*  Software is furnished to do so, subject 
*  to the following conditions:
*
*  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
*  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
*  OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
*  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
*  HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
*  WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
*  ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE 
*  OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

#ifdef __cplusplus  
extern "C" { 
#endif

#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>
#include "tree.h"





/* 
 * LIST IMPLEMENTATIONS
 */



void list_insert(list *collection, void *data)
{
  list_node *new_node = (list_node *)malloc(sizeof(list_node));
  new_node->next = 0;
  new_node->data = data;
  *(collection->tail) = new_node;
  collection->tail = &(new_node->next);
}


static
void list_apply_(list_node *cur, effect fun)
{
  if(0 == cur) return;
  fun(cur->data);
  list_apply_(cur->next, fun);
}


void list_apply(list *collection, effect fun)
{  list_apply_(collection->head, fun);  }


static
void list_destroy(list_node *cur)
{
  if(0 == cur) return;
  list_destroy(cur->next);
  free(cur);
}


void list_destruct(list *collection)
{
  list_destroy(collection->head);
  list_init(collection); /* setup so it can be reused */
}


static
void list_destroy_all(list_node *cur)
{
  if(0 == cur) return;
  list_destroy_all(cur->next);
  free(cur->data);
  free(cur);
}


void list_destruct_data_(list_node *n)
{
	if(0 == n) return;
	free(n->data);
	list_destruct_data_(n->next);
}


void list_destruct_data(list *collection)
{
	if(0 == collection) return;
	list_destruct_data_(collection->head);
}


void list_destruct_all(list *collection)
{
  list_destroy_all(collection->head);
  list_init(collection); /* setup so it can be reused */
}

/* find out if this actually can be optimized */
list_node * list_tail_(list_node *cur)
{
	if(0==cur->next) return cur;
	list_tail_(cur->next);
}


list_node * list_tail(list *collection)
{
	return list_tail_(collection->head);
}


void list_print(list *lst)
{ 
  list_node *cur = lst->head;
  while(0!=cur){
    list_print_data(cur);
    if(0 != cur->next) putchar(',');
	cur = cur->next;
  }
  putchar('\n');
}

void list_print_data(void *lst_node)
{ printf("%s", (char*)((list_node*)lst_node)->data); }

void print_voidstar(void *string)
{ if(0 != string)printf("%s\n", (const char *)string); }


void print_voidstar_int(void *i)
{ if(0 != i)printf("%d\n", *((int *)i)); }


void list_str(const char *dir, list *collection, char delim)
{
  char *dir_pos = (char*)dir,
       *allocd;
  size_t offset = 0,
         prev = 0,
         max = strlen(dir);
  for(size_t pos = 1;pos < max; ++pos)
    if(delim == dir[pos]
          /* exploiting short-circut eval */
         || ('\0' == dir[pos+1] && ++pos)){
      offset = pos - prev;
      allocd = (char*)malloc(offset);
      allocd[offset-1] = '\0';
      /* Adjust by +1 because we don't want to include the delim.
       * -1 to adjust for the adjustment */
      strncpy(allocd, dir_pos+1, offset-1);
      list_insert(collection, allocd);
      dir_pos += offset;
      prev = pos;
    }
}


/* this function is practically redundant. fucko move. */
void dir_to_list_alloc(const char *dir, list *collection)
{
  static const char delim = '/';
  if(dir[0] != delim) return;

  char *dir_pos = (char*)dir,
       *allocd;
  size_t offset = 0,
         prev = 0,
         max = strlen(dir);
  for(size_t pos = 1;pos < max; ++pos)
    if(delim == dir[pos]
          /* exploiting short-circut eval */
         || ('\0' == dir[pos+1] && ++pos)){
      offset = pos - prev;
      allocd = (char*)malloc(offset);
      allocd[offset-1] = '\0';
      /* Adjust by +1 because we don't want to include the delim.
       * -1 to adjust for the adjustment */
      strncpy(allocd, dir_pos+1, offset-1);
      list_insert(collection, allocd);
      dir_pos += offset;
      prev = pos;
    }
}





/* 
 * QUEUE  IMPLEMENTATIONS
 */



list_node * dequeue(list *collection)
{
  if(collection == 0) return 0;
  list_node *front = collection->head;
  if(front == 0) return 0;
  collection->head = front->next;
  return front;
}





/*
 * STACK IMPLEMENTATIONS
 */



list_node* stack_push(list *coconut, void *rock)
{
  list_node *milk = (list_node *)malloc(sizeof(list_node));
  milk->next = coconut->head;
  milk->data = rock;
  coconut->head = milk;
  return milk;
}





/*
 * BINARY SEARCH TREE IMPLEMENTATIONS
 */



/* Working with BSTs in terms of their links instead of their nodes
 * drastically simplilfies many of the routines.
*/
static inline
bst_node ** llink(bst_node **n)
{ return &((*n)->left); }


static inline
bst_node ** rlink(bst_node **n)
{ return &((*n)->right); }

/* alloc */
bst_node * bst_node_init(const char* key, void *data)
{
  bst_node *new_node = (bst_node *)malloc(sizeof(bst_node));
  new_node->key = key;
  new_node->data = data;
  new_node->left = 0;
  new_node->right = 0;
  return new_node;
}


/* Find the link where a new node might go. */
static
bst_node ** bst_find_placement(const char* key, bst_node **cur)
{
  if(0 == *cur) return cur;
  int path = strcmp(key, (*cur)->key);
  if(-1 == path)
    return bst_find_placement(key, llink(cur));
  else if(1 == path)
    return bst_find_placement(key, rlink(cur));
  return 0;
}


/* This routine is exruciatingly similar to bst_find_placement
 * but alas they cannot be merged because bst_insert
 * is always expecting a pointer to a null link but bst_find_link
 * fails if this condition is met.
 */
static
bst_node ** bst_find_link(const char* key, bst_node **cur)
{
  if(0 == *cur) return cur;
  int path = strcmp(key, (*cur)->key);
  if(-1 == path)
    return bst_find_link(key, llink(cur));
  else if(1 == path)
    return bst_find_link(key, rlink(cur));
  return cur;
}


void * bst_find(const char*  key, bst_node **root)
{
  bst_node **found = bst_find_link(key, root);
  if(0 == *found) return 0;
  return (*found)->data;
}


bool bst_insert(const char* key, void *data, bst_node **cur)
{
  cur = bst_find_link(key, cur);
  if(0 == cur) return 0;
  *cur = bst_node_init(key, data);
  return 1;
}


bst_node * bst_insert_get(const char* key, void *data, bst_node **cur)
{
  cur = bst_find_link(key, cur);
  if(0 == *cur)
    *cur = bst_node_init(key, data);
  return *cur;
}


/* it is used only once. it will get optimized away */
static
void bst_absorb(bst_node *dest, bst_node *src)
{
  dest->key = src->key;
  dest->data = src->data;
}


bst_node ** bst_min_link(bst_node **cur)
{
  if(0 == (*cur)->left) return cur;
  return bst_min_link(llink(cur));
}


bool bst_delete(const char* key, bst_node **root)
{
  bst_node **mourning_father = bst_find_link(key, root);
  if(0 == *mourning_father) return 0;
  bst_node *dead = *mourning_father;
  bst_node *chopping_block = dead;

  if( 0 == dead->right && 0 == dead->left )
    *mourning_father = 0;
  else if(0 == dead->right && 0 != dead->left)
    *mourning_father = dead->left;
  /* todo: do we really need to check both of them at this point in the logic ? */
  else if(0 != dead->right && 0 == dead->left)
    *mourning_father = dead->right;
  else {
    mourning_father = bst_min_link( &(dead->right) );
    bst_absorb(dead, *mourning_father);
    return bst_delete( (*mourning_father)->key, mourning_father);
  }

  /* the executioner approaches */
  free(chopping_block);
  return 1;
}


void bst_destroy(bst_node *cur)
{
  if(0 == cur) return;
  bst_destroy(cur->left);
  bst_destroy(cur->right);
  free(cur);
}


void bst_destruct(bst_node **root)
{
  bst_destroy(*root);
  *root = 0;
}


void bst_destroy_all(bst_node *cur)
{
  if(0 == cur) return;
  bst_destroy(cur->left);
  bst_destroy(cur->right);
  free((void*)cur->key);
  free(cur->data);
  free(cur);
}

void bst_destruct_all(bst_node **root)
{
  bst_destroy_all(*root);
  *root = 0;
}


void bst_in_order(bst_node *cur, effect fun)
{
  if(0 == cur) return;
  bst_in_order(cur->left, fun);
  fun(cur->data);
  bst_in_order(cur->right, fun);
}


void bst_print(bst_node *cur)
{
  if(0 == cur) return;
  bst_print(cur->left);
  printf("%s : %s\n", cur->key, ((char*)cur->data));
  bst_print(cur->right);
}


void bst_to_stack(bst_node *root, list *dest)
{
  if(0 == root) return;
  bst_to_stack(root->left, dest);
  stack_push(dest, root);
  bst_to_stack(root->right, dest);
}


/* 
 * TREE IMPLEMENTATIONS 
*/

tree * tree_find(tree **root, list *path)
{
  list_node *cur_dir = path->head;
  bst_node *cur_node = *root;

  while(0 != cur_dir){
    cur_node = (bst_node*)bst_find((char *)cur_dir->data, &cur_node);
	if(cur_node == 0) return 0;
	if(cur_node->key == 0) return cur_node;
    cur_dir = cur_dir->next;
  }

  return cur_node;
}


void tree_insert(tree **root, list *path, void *data)
{
  tree *exists = tree_find(root, path);
  tree *cur_node = 0;
  if(exists == 0)
    cur_node = tree_make_path(root, path);
  else
    cur_node = exists;
  /* a file has the key of null */
  cur_node->data = bst_node_init(0,data);
}

void tree_insert_str(tree **root, char *path, void *data)
{
  list dirs;
  list_init(&dirs);
  dir_to_list_alloc(path, &dirs);
  tree_insert(root, &dirs, data);
  list_destruct_data(&dirs);
}


tree* tree_make_path(tree **root, list *path)
{
  list_node *cur_dir = path->head;
  tree **cur_link = root;
  tree *cur_node = 0;

  while(0 != cur_dir){
    cur_node = bst_insert_get((char *)cur_dir->data, 0, cur_link);
    cur_link = (tree **)&( cur_node->data );
    cur_dir = cur_dir->next;
  }
  
  return cur_node;
}


tree* tree_make_path_str(tree **root, const char *path)
{
  list dirs;
  list_init(&dirs);
  dir_to_list_alloc(path, &dirs);
  tree *last = tree_make_path(root, &dirs);
  list_destruct(&dirs); /* should be list_destroy_all */
  return last;
}





tree * tree_find_str(tree **root, char *path){
  list dirs;
  list_init(&dirs);
  dir_to_list_alloc(path, &dirs);
  tree *last = tree_find(root, &dirs);
  list_destruct(&dirs);
  return last;
}



static
void tree_print_(tree *cur, unsigned depth)
{
  if(0 == cur) return;
  tree_print_(cur->left,depth);
  tree_print_(cur->right,depth);
  if(0 == cur->key) return;
  for(int i = 0; i < depth; ++i) printf("  ");
  puts(cur->key);
  tree_print_((tree*)cur->data,depth+1);
}


void tree_print(tree *root)
{ tree_print_(root, 0); }


static
void tree_destroy(tree *cur)
{
  if(0 == cur) return;
  tree_destroy(cur->left);
  tree_destroy(cur->right);
  tree_destroy((tree*)cur->data);
  free(cur);
}


void tree_destruct(tree **root)
{
  tree_destroy(*root);
  *root = 0;
}



/* todo: tree_destruct_all */



static
void sortToList_(list *containerDest, bst_node **containerSrc )
{
	sortToList_(containerDest, &((*containerSrc)->left));
	list_insert(containerDest, (*containerSrc)->data);
	sortToList_(containerDest, &((*containerSrc)->right));
}
void sortToList(list *containerDest, bst_node **containerSrc ){
	containerSrc = 0;
	sortToList_(containerDest, containerSrc);
}



 
 
#ifdef __cplusplus 
} 
#endif 
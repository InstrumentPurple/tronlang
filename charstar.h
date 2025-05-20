/* Sept. 26, 2019 */
#pragma once
#include <stdbool.h>
#include <stdint.h>
#define CMD_STR_SIZE 256
#define DEFAULT_PAGE_SIZE 4096
#define INT_PAGE_SIZE DEFAULT_PAGE_SIZE/sizeof(int64_t)


#ifdef __cplusplus  
extern "C" { 
#endif

/* Checks if yin and yang are eqivaltent.
 * Aside from being more syntatically verbose
 * sometimes strcmp is more feature rich than
 * we need and that comes at a cost. */
bool eq(const char *yin, const char *yang);

/* check if str entirely constists of letters of the alphabet.
 * Case insensitive. */
bool is_word(const char *str);

/* check if we have balanced parens in str */
bool balanced_parens(const char *str);

/* check if str contains post from it's right side. */
bool postfix(const char *str, const char *post);

/* check if a string has a prefix of pre */
bool prefix(const char *str, const char *pre);

/* returns ending posision of pre string if it in fact is a substring. Otherwise returns 0. */
size_t prefixs(const char *str, const char *pre);


/* it's naive because it isn't kmp or anything fancier.
 * find a substrin sub in string str */
int substr_naive(const char *str, const char *sub);


bool get_between(char *buf,const int lim, const char *src,
                 const char *left, const char *right);

void chomp(char *str);

void super_chomp(char *str);



bool is_whitespace(char c);

/* the first character includingly bounded by offset */
void skip_spaces(char *src, size_t *offset);

bool char_is_digit(char c);

/* returns 0 if an error condition happens and returns the number of bytes coppied.
 * len determines how many bytes is copied and should be less then the len of buffer dest.
 * offset is less then len and would return false if not so.*/
size_t copy_range_prefixs(char *dest, char *src, size_t len, size_t offset);



/* size_t digit_sequence_prefix(char *str) */
static inline
size_t digit_sequence_prefix(char *str)
{
	size_t i = 0;
	for(; str[i] != '\0' && char_is_digit( str[i] ); i++);
	return i;
}

bool char_is_alpha(char c);

static inline
size_t word_sequence_prefix(char *str)
{
	size_t count = 0;
	
	for(; str[count] != '\0' && char_is_alpha(str[count]); count++);
	
	return count;
}
/* size_t word_sequence_prefix(char *str); */


/*
bool has_whitespace(char *str)
bool has_digit(char *str)
bool has_many
*/

void column(char *dest, char *str, int bufMax, int col);


long long binsearch(char **data, const char *item, long long upperBound);

#ifdef __cplusplus  
}
#endif 
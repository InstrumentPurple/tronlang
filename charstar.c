/* Sept. 27, 2019 */

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

#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include "charstar.h"


bool eq(const char *yin, const char *yang)
{
  register unsigned pos = 0;
  for(;;){
    if(yin[pos] != yang[pos])
      return 0;
    else if('\0' == yang[pos])
      break;
    ++pos;
  }
  return 1;
}


bool is_word(const char *str)
{
  static const char alphabet[] 
  = "etaoinsrhdlucmfywgpbvkxqjz"
    "ETAOINSRHDLUCMFYWGPBVKXQJZ";
  static const int alpha_len = sizeof(alphabet);

  if(str[0] == '\0') return 0;

  bool found_one = 0;
  for(int i = 0; str[i] != '\0'; ++i){
    for(int j = 0; j < alpha_len; ++j){
      if(str[i] == alphabet[j]){
        found_one = 1;
        break;
      }
    }
    if(!found_one) return 0;
    found_one = 0;
  }

  return 1;
}


bool balanced_parens(const char *str)
{
  int count = 0;
  for(size_t i = 0; str[i] != '\0'; i++){
     if('(' == str[i]) count += 1;
     else if(')' == str[i]) count -= 1;
  }
  return count == 0;
}


bool postfix(const char *str, const char *post)
{
  int len_str = 0,
      len_post = 0;
  for(;str[len_str] != '\0'; ++len_str);
  for(;post[len_post] != '\0'; ++len_post);
  
  if(len_post > len_str) return 0;
  return eq(str+(len_str-len_post), post);
}


bool prefix(const char *str, const char *pre)
{
  int pre_len = 0, str_len = 0;
  for(;pre[pre_len] != '\0'; pre_len++);
  for(;str[str_len] != '\0'; str_len++);
  
  if(str_len < pre_len) return 0;
  
  for(int i = 0; i < pre_len; ++i)
    if(str[i] != pre[i]) return 0;
  
  return 1;
}



int substr_naive_likely(const char *str, const char *sub){
  int firstOptm = 0;
  
  for(;str[firstOptm] != '\0' && sub[firstOptm] != '\0' && str[firstOptm] == sub[firstOptm]; firstOptm++);
  
  register int str_len = 0,
               sub_len = 0;
			   
  for(;sub[sub_len] != '\0'; ++sub_len);
  
  if(firstOptm == sub_len) return 0;
  
  for(;str[str_len] != '\0'; ++str_len);
  
  if(str_len < sub_len) return -1;
  
  
  register int j = 0;
  register int max = str_len - sub_len;
  for(int i = 0 /* already checked */; i <= max; ++i){
    for(; j < sub_len; ++j)
      if(str[i + j] != sub[j]) break;
    if(j == sub_len) return i;
	j = 0;
  }
  return -1;
}



int substr_naive(const char *str, const char *sub){
  register int str_len = 0,
               sub_len = 0;
  for(;str[str_len] != '\0'; ++str_len);
  for(;sub[sub_len] != '\0'; ++sub_len);
	  
  if(str_len < sub_len) return -1;
  
  register int j = 0;
  register int max = str_len - sub_len;
  for(int i = 0; i <= max; ++i){
    for(; j < sub_len; ++j)
      if(str[i + j] != sub[j]) break;
    if(j == sub_len) return i;
	j = 0;
  }
  return -1;
}


size_t prefixs(const char *str, const char *pre)
{
  size_t i = 1;
  if(pre[0] == '*')
	for(i = 1; str[i] != '\0' && !prefix(str+i, pre+1); ++i);
  else 
	for(i = 0; str[i] != '\0' && str[i] != '\0' && str[i] == pre[i]; ++i);
  return i;
}


bool get_between(char *buf,const int lim, const char *src,
                 const char *left, const char *right){
  int skip = 0;
  for(; left[skip] != '\0'; skip++);
  /* we add j because we don't want to include left
   * within the slice */
  int left_pos = substr_naive_likely(src, left) + skip; /* We do not include the delim, left, in the region we are copying to in the following lines. */
  int right_pos = substr_naive_likely(src, right);
  
  if(left_pos >= right_pos){ 
	buf[0] = '\0';
	return 0;
  }
  
  int slice_size = right_pos - left_pos;
  if(slice_size > lim) return 0;
  
  if(!(slice_size + 1 < lim)) return 0;
  
  int i = 0;
  for(; i < slice_size ; ++i)
    buf[i] = src[left_pos + i];
  buf[i] = '\0';
  return 1;
}

void chomp(char *str){
  int i = 0;
  for(; str[i] != '\0'; ++i);
  --i; /* for zero-indexing */
  for(int pos = i; str[pos] == '\n' || str[pos] == '\r'; --pos)
    str[pos] = '\0';
}

void super_chomp(char *str){
  int i = 0;
  for(; str[i] != '\0'; ++i);
  --i; /* for zero-indexing */
  for(int pos = i; str[pos] == '\n' || str[pos] == '\r' ||
                   str[pos] == ' ' || str[pos] == '\t'; --pos)
    str[pos] = '\0';
}

bool is_whitespace(char c)
{
	const char whiteSpace[] = " \n\r\t";
	static int whiteSpaceLen = 3;

	bool isSpace = 0;
	for(int i = 0; i < whiteSpaceLen; i++)
		isSpace = isSpace | (whiteSpace[i] == c);
	if(!isSpace) return 0;
	return isSpace;
}

void skip_spaces(char *src, size_t *offset)
{
	if(offset == 0) return;
	if(!is_whitespace(src[*offset])) return;

	const int srcLen = strlen(src);
	for(int j = 0; j < srcLen; j++)
		if( is_whitespace(src[*offset]) )
			(*offset)++;
}


/* true when float or int*/
bool char_is_digit(char c)
{
	static char digits[12] = "0123456789";
	for(int i = 0; i < 12; i++)
		if(c == digits[i]) return 1;
	return 0;
}

size_t copy_range_prefixs(char *dest, char *src, size_t len, size_t offset)
{
	if(offset >= len) return 0;
	size_t i = 0;
	for(; i < len && (offset + i) < len && src[i] != '\0'; i++)
		dest[i] = src[i + offset];
	dest[i] = '\0';
	return i;
}


/*
size_t digit_sequence_prefix(char *str)
{
	size_t i = 0;
	for(; str[i] != '\0' && char_is_digit( str[i] ); i++);
	return i;
}
*/


bool char_is_alpha(char c)
{
	static char alphaSet[] = "qwertyuiopasdfghjklzxcvbnm";
	size_t alphaLen = strlen(alphaSet);
	
	size_t i = 0;
	for(; i < alphaLen; ++i)
		if(alphaSet[i] == c) return 1;
	
	return 0;
}

/*
size_t word_sequence_prefix(char *str)
{
	size_t count = 0;
	
	for(; str[count] != '\0' && char_is_alpha(str[count]); count++);
	
	return count;
}

*/

/*
size_t csv_split(char *line)
{
	return char_split(',', line);
}

*/




/* col is zero-indexed */
void column(char *dest, char *str, int bufMax, int col)
{
	int bufPos = 0;
	memset(dest, '\0', bufMax);
	
	/* skip over col + 1 spaces */
	int strPos = 0;
	for(int spaces = 0; str[strPos] != '\0' && spaces < col; strPos++){
		if(str[strPos] == ' ') spaces++;
	}
	
	for(; str[strPos] != ' ' &&
		!(str[strPos] == '\r' ||
		str[strPos] == '\n'); strPos++, bufPos++){
			
		dest[bufPos] = str[strPos];
	}
	dest[bufPos] = '\0';
}

/* Binary search on a table of strings. */
long long binsearch(char **data, const char *item, long long upperBound)
{
	long long lowerBound = 0;
	long long middleSpan = 2; /* 2 to enter the loop. could be any number larger */
	if(strcmp(data[0], item) == 0) return 0;
	
	while( middleSpan > 1 ){
		middleSpan = (upperBound - lowerBound) / 2;
		if(strcmp(data[lowerBound+middleSpan], item) == -1)
			lowerBound += middleSpan;
		else if(strcmp(data[lowerBound+middleSpan], item) == 1)
			upperBound -= middleSpan;
		else
			return lowerBound+middleSpan;
	}
	
	return -1;
}
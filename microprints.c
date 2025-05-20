/* aug 25, 2021 */
/* modified May 12, 2025 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include <math.h>


#include "./hakkerbase/tree.h"

typedef struct ajgraph {
    int **graph;
    int y;
    int x;
} ajgraph;


typedef struct graphStrTbl {
    ajgraph g;
    char **tbl;
    unsigned tbllen;
} graphStrTbl;


typedef struct fileInfo {
    int lineMaxLen;
    int lineCount;
}fileInfo;


typedef struct profile {
    char *dataPath;
    char *name;
    char *freq;
    graphStrTbl gst;
} profile;

char specialChars[] = ",.<>;':\"[]{}/?`~!@#$%^&*()_=+|\\";


#define LINE_SIZE 4026
#define PATH_SIZE 4096
#define GRAPH_LINE_SIZE 1024 * 1024 * 32


bool is_special_char(char c)
{
    const int spchrLen = strlen(specialChars);
    for(int i = 0; i < spchrLen; i++){
        if(c == specialChars[i]) return 1;
    }
    return 0;
}


void remove_appended_special_chars(char *str)
{
    int len = strlen(str)-1;
    for(int i = len; i >= 0; i--)
        if(is_special_char(str[i]))
            str[i] = '\0';
}


void ajgraph_insert(ajgraph *g, int y, int x, int weight)
{
    g->graph[y][x] = weight;
}


/* col is zero-indexed */
void column_(char *dest, char *str, int bufMax, int col)
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


/* TODO: test */
void ajgraph_from_file(ajgraph *g, const char *file_path)
{
    FILE *fh;
    char line[LINE_SIZE];

    /* edge buffers */
    int w=0,v=0;
    char left[LINE_SIZE];
    char right[LINE_SIZE];
    memset(left, '\0', LINE_SIZE);
    memset(right, '\0', LINE_SIZE);


    memset(line, '\0', LINE_SIZE);
    fh = fopen(file_path, "r");
    int cur = 0,j = 0,i = 0;
    while(1){
        fgets(line, 4096, fh);
        /* feof seemed to not be working for me. */
        if(strcmp(line, "end") == 0 ||
            /* you can add a comment after the
             * end statement*/
            strcmp(line, "end\n") == 0 || /* linux */
            strcmp(line, "end\r\n") == 0 || /* windows */
            feof(fh) == 1) break;

        j = 0;
        /* parse and proc line data */
        for(; line[cur] != ' ' &&
            !(line[cur] == '\n' ||
            line[cur] == '\r'); cur++, j++){

            left[j] = line[cur];
            }
            left[j] = '\0';
        w = atoi(left);

        cur++; /* skip delimiter */
        i = 0;
        for(; line[cur] != ' ' &&
            !(line[cur] == '\n' ||
            line[cur] == '\r'); cur++, i++){

            right[i] = line[cur];
            }
            right[i] = '\0';
        v = atoi(right);


        /* TODO: parse edge and insert into datastructure */

        cur = 0;
    }

    fclose(fh);
}


void ajgraph_init(ajgraph *g, int y, int x)
{
    g->graph = (int **)malloc(sizeof(int*) * y);

    for(int i = 0; i < y; i++)
        g->graph[i] = (int *)malloc(sizeof(int) * x);

    //for(int i = 0; i < y; i++)
    //	memset(g->graph[i], 0, sizeof(int) * x);
    g->y = y;
    g->x = x;

    for(int i = 0; i < y; i++){
        for(int j = 0; j < x; j++){
            g->graph[i][j] = 0;
        }
    }

}


void ajgraph_print(ajgraph *g)
{
    for(int i = 0; i < g->y; i++){
        for(int j = 0; j < g->x; j++)
            printf("%d ", g->graph[i][j]);
        puts("");
    }
}


void ajgraph_save(const char *path, ajgraph *g)
{
    FILE *gTextFile = fopen(path, "w");

    //if( 0 == gTextFile ) puts("file error");

    for(int i = 0; i < g->y; i++){
        for(int j = 0; j < g->x; j++){
            fprintf(gTextFile,"%d ", g->graph[i][j]);
        }
        fprintf(gTextFile, "%s", "\n");
    }


    fclose(gTextFile);
}


void ajgraph_destroy(ajgraph *g)
{
    for(int i = 0; i < g->y; i++)
        free(g->graph[i]);
}


const char vowels[] = "euioa";

bool is_vowel(char c)
{
    static int vllen = strlen(vowels);
    for(int i = 0; i < vllen; i++)
        if(c == vowels[i])
            return 1;

    return 0;
}


bool not_newline(const char *line)
{ return line[0] != '\r' && line[0] != '\n'; }


bool end_of_file(const char *line)
{
    static const char endDelim[] = "end";
    int linePos = 0;
    for(; line[linePos] != '\0' && endDelim[linePos] != '\0' && not_newline(line); linePos++){
        if(line[linePos] != endDelim[linePos]) return 0;
    }

    return 1;
}

/* TODO: check buffer possitions */
void chumbawamba_prep(const char *srcPath, const char *edgesPath)
{
    FILE *src = fopen(srcPath, "r");
    FILE *cons = fopen(edgesPath, "w");
    if( 0 == cons ) return;

    int chkpos = 0;
    char chunk[LINE_SIZE];
    memset(chunk, '\0', LINE_SIZE);

    char words[LINE_SIZE];
    memset(words, '\0', LINE_SIZE);
    char prev = '\0';
    while(1){
        fgets( words, LINE_SIZE, src );
        if(end_of_file(words)) break;
        for(int i = 0; words[i] != '\0'; ++i){
            if(is_vowel(words[i])){
                prev = words[i];
                i++; /* skip vowel because it is a delimiter */
                for(; words[i] != '\0' && words[i] != '\r' && words[i] != '\n'
                    && words[i] != ' ' && !is_vowel(words[i]);chkpos++, i++){
                    chunk[chkpos] = words[i];
                    }
                    //chunk[++chkpos] = '\0';
                    chunk[chkpos] = '\0';

                if(chunk[0] != '\0')
                    fprintf(cons, "%c %s\n",prev,chunk);
                chkpos = 0;
                memset(chunk, '\0', LINE_SIZE);
            }
        }
    }

    fprintf(cons, "%s", "end");

    fclose(src);
    fclose(cons);
}


void bst_write_keys_(FILE *k, bst_node *n)
{
    if(0==n) return;
    bst_write_keys_(k, n->left);
    fprintf(k, "%s\n", n->key);
    bst_write_keys_(k, n->right);
}


void bst_write_keys(FILE *k, bst_node *n)
{
    bst_write_keys_(k,n);
    fprintf(k,"%s", "end");
}


void chumbawamba_vertexs(const char *edgesPath, const char *strtblPath)
{
    FILE *edgesFile = fopen(edgesPath, "r");

    char line[LINE_SIZE];
    memset(line, '\0', LINE_SIZE);

    char col[LINE_SIZE];
    memset(col, '\0', LINE_SIZE);

    char *strAlloc = 0;

    bst_node *root = 0;

    /* TODO: free buffers */
    while(1){
        fgets(line, LINE_SIZE, edgesFile);
        if(end_of_file(line)) break;
        column_(col,line,LINE_SIZE,1);
        /*TODO: is the +1 needed? */
        strAlloc = (char *)malloc(strlen(col)+1);
        memset(strAlloc, '\0', strlen(col)+1);
        memcpy(strAlloc, col, strlen(col) + 1);
        if(strAlloc[0] != '\0') /* hack. */
            bst_insert(strAlloc,0,&root);
    }

    fclose(edgesFile);

    FILE *f = fopen(strtblPath, "w");
    bst_write_keys(f, root);
    fclose(f);
}


void file_info_init(FILE *f, fileInfo *fi)
{
    fi->lineMaxLen = 0;
    fi->lineCount = 0;
    int curCharCount = 0;

    char line[LINE_SIZE];
    memset(line, '\0', LINE_SIZE);

    while(1){
        fgets(line, LINE_SIZE, f);
        if(end_of_file(line)) break;
        if(strlen(line) > curCharCount)
            curCharCount = strlen(line);
        fi->lineCount++;
    }
    fi->lineMaxLen = curCharCount;
    rewind(f);
}


void super_chomp_(char *str){
    int i = 0;
    for(; str[i] != '\0'; ++i);
    --i; /* for zero-indexing */
    for(int pos = i; str[pos] == '\n' || str[pos] == '\r' ||
        str[pos] == ' ' || str[pos] == '\t'; --pos)
        str[pos] = '\0';

}


void str_tbl_init(const char *vertPath, graphStrTbl *gst)
{
    FILE *f = fopen(vertPath, "r");
    fileInfo fi;
    file_info_init(f, &fi);

    ajgraph_init(&(gst->g),strlen(vowels),fi.lineCount);
    gst->tbllen = fi.lineCount;

    gst->tbl = (char **)malloc(sizeof(char*)*fi.lineCount + 1);

    for(int i = 0; i < fi.lineCount; i++){
        gst->tbl[i] = (char *)malloc(fi.lineMaxLen+1);
        memset(gst->tbl[i], '\0', sizeof(char)*fi.lineMaxLen+1);
    }


    char line[LINE_SIZE];
    memset(line, '\0', LINE_SIZE);

    int cur = 0;
    while(1){
        fgets(line,LINE_SIZE,f);
        if(end_of_file(line)) break;
        memcpy(gst->tbl[cur],line, fi.lineMaxLen+1);
        cur++;
    }

    fclose(f);

    for(int i = 0; i < gst->tbllen-1; i++)
        super_chomp_(gst->tbl[i]);
}


int str_tbl_lookup(graphStrTbl *gst, const char *item)
{
    /*
     * for(int i = 0; i < gst->tbllen; i++){
     *	if(strcmp(gst->tbl[i], item) == 0)
     *		return i;
}
return -1;
*/

    /* binary search */
    char **data = gst->tbl;
    int upperBound = gst->tbllen-1;
    int lowerBound = 0;
    int middleSpan = 2; /* 2 to enter the loop. could be any number larger */
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


int str_tbl_lookup_vowel(char v)
{
    int res;
    switch(v){
        case 'e': res = 0;
        break;
        case 'u': res = 1;
        break;
        case 'i': res = 2;
        break;
        case 'o': res = 3;
        break;
        case 'a': res = 4;
        break;
        default:
            res = -1;
            break;
    }
    return res;
}


char str_tbl_lookup_vowel_reverse(int index)
{
    char res;
    switch(index){
        case 0: res = 'e';
        break;
        case 1: res = 'u';
        break;
        case 2: res = 'i';
        break;
        case 3: res = 'o';
        break;
        case 4: res = 'a';
        break;
        default:
            res = '\0';
            break;
    }
    return res;
}

//void column(char *dest, char *str, int bufMax, int col)


void graph_str_tbl_init(const char *epath, const char *vpath, graphStrTbl *gst)
{
    str_tbl_init(vpath, gst);

    FILE *edgesFile = fopen(epath, "r");

    char line[LINE_SIZE];
    memset(line, '\0', LINE_SIZE);

    char vowelBuf[LINE_SIZE];
    memset(vowelBuf, '\0', LINE_SIZE);

    char constanantBuf[LINE_SIZE];
    memset(constanantBuf, '\0', LINE_SIZE);
    int res1, res2;
    while(1){
        fgets(line,LINE_SIZE, edgesFile);
        if(end_of_file(line)) break;
        column_(vowelBuf, line, LINE_SIZE, 0);
        column_(constanantBuf, line, LINE_SIZE, 1);

        res1 = str_tbl_lookup_vowel(vowelBuf[0]);
        res2 = str_tbl_lookup(gst, constanantBuf);

        gst->g.graph[res1][res2]++;
    }

    fclose(edgesFile);
}


/* currently crashes the whole program if called */
void graph_str_tbl_destroy(graphStrTbl *gst)
{
    ajgraph_destroy(&(gst->g));
    for(int i = 0; i < gst->tbllen-1; i++){
        free(gst->tbl[i]);
    }
}


void profile_init(const char *proPath, profile *dest)
{
    FILE *pro = fopen(proPath, "r");

    char line[LINE_SIZE];
    memset(line, '\0', LINE_SIZE);

    char lhs[LINE_SIZE];
    memset(lhs,'\0',LINE_SIZE);

    char rhs[LINE_SIZE];
    memset(rhs, '\0', LINE_SIZE);

    int curLine = 0;
    int cur = 0;
    char *destSliceR = 0;
    while(1){
        fgets(line, LINE_SIZE, pro);
        super_chomp_(line);
        if(end_of_file(line)) break;

        curLine = 0;
        for(cur = 0;line[curLine] != '=' && line[curLine] != '\0'; cur++,curLine++){
            lhs[cur] = line[curLine];
        }
        lhs[cur] = '\0';
        curLine++; /* skip delimiter */

        for(cur = 0;line[curLine] != '\0'; cur++,curLine++){
            rhs[cur] = line[curLine];
        }
        rhs[cur] = '\0';

        destSliceR = (char *)malloc(strlen(rhs)+1);
        memset(destSliceR, '\0', strlen(rhs)+1);
        memcpy(destSliceR, rhs, strlen(rhs));

        if(strcmp(lhs, "name") == 0){
            dest->name = destSliceR;
        } else if(strcmp(lhs,"data") == 0){
            dest->dataPath = destSliceR;
        } else if(strcmp(lhs,"freq") == 0){
            dest->freq = destSliceR;
        }

    }
    fclose(pro);
}


void proc_profile(profile *pr)
{
    char tmpEdgePath[PATH_SIZE] = "./tmp_edge.";
    char vertTblPath[PATH_SIZE] = "./vert_tbl.";
    char graphPath[PATH_SIZE] = "./graph.";

    strncat(tmpEdgePath, pr->name, PATH_SIZE-1);
    strncat(vertTblPath, pr->name, PATH_SIZE-1);
    strncat(graphPath, pr->name, PATH_SIZE-1);


    chumbawamba_prep(pr->dataPath, tmpEdgePath);
    chumbawamba_vertexs(tmpEdgePath, vertTblPath);

    graph_str_tbl_init(tmpEdgePath, vertTblPath, &(pr->gst));

    //ajgraph_print(&(gst.g));

    ajgraph_save(graphPath,&(pr->gst.g));
}


void post_proc_profile(profile *pr)
{
    char tmpEdgePath[PATH_SIZE] = "./tmp_edge.";
    char vertTblPath[PATH_SIZE] = "./vert_tbl.";
    char graphPath[PATH_SIZE] = "./graph.";

    strncat(tmpEdgePath, pr->name, PATH_SIZE-1);
    strncat(vertTblPath, pr->name, PATH_SIZE-1);
    strncat(graphPath, pr->name, PATH_SIZE-1);

    graph_str_tbl_init(tmpEdgePath, vertTblPath, &(pr->gst));
}


int maximum_edge_y(graphStrTbl *g, char *vertY)
{
    int maximum = 0;
    int pos = 0;

    int res = str_tbl_lookup(g, vertY);
    int vlen = strlen(vowels);
    for(int i = 0; i < vlen; i++){
        if(maximum < g->g.graph[i][res]){
            pos = i;
            maximum = g->g.graph[i][res];
        }
    }

    return pos;
}


int maximum_edge_x(graphStrTbl *gst, char vertX)
{
    int maximum = 0;
    int pos = 0;

    int res = str_tbl_lookup_vowel(vertX);
    int vlen = gst->tbllen-1;
    for(int i = 0; i < vlen; i++){
        if(maximum < gst->g.graph[res][i]){
            pos = i;
            maximum = gst->g.graph[res][i];
        }
    }

    return pos;
}


void dual(profile *a, profile *b)
{
    char start[LINE_SIZE];
    memset(start, '\0', LINE_SIZE);

    int res = 0;
    bool cur = 1;
    char curVowel;
    char *curCnst = "";
    int curSomething = 0;
    profile *tmp;
    while(1){
        scanf("%s", start);
        if(end_of_file(start)) break;
        curCnst = start;
        for(int i = 0; i < 20; i++){
            if(cur){
                res = maximum_edge_y(&(a->gst), curCnst);
                curVowel = str_tbl_lookup_vowel_reverse(res);
                printf("%c", curVowel);
            } else {
                res = maximum_edge_x(&(b->gst), curVowel);
                curCnst = b->gst.tbl[res];
                printf("%s", curCnst);
            }

            if(curSomething % 3 == 0){
                tmp = a;
                a = b;
                b = tmp;
            }

            curSomething++;
            cur = !cur;
        }
        puts("");
    }
}


void random_select(profile *pf)
{
    srand(time(NULL));
    int r1, r2;
    for(int i = 0; i < 20; i++){
        r1 = rand() % strlen(vowels);
        r2 = rand() % pf->gst.tbllen;
        printf("%c%s", str_tbl_lookup_vowel_reverse(r1), pf->gst.tbl[r2]);
    }
}


void fprint_td(FILE *htmlFile, char *contents)
{
    static char tdStart[] = "<td>";
    static char tdEnd[] = "</td>";
    fprintf(htmlFile, "%s%s%s", tdStart, contents, tdEnd);
}


void fprint_global_style(FILE *htmlFile)
{
    static const char css[] =
    "table{"
    "font-size:18pt; font-family: arial,verdana;"
    "text-align:right;}"
    "#break{padding-top:50px;}"
    ;

    fprintf(htmlFile, "<style>%s</style>", css);
}


float density(ajgraph *g)
{
    float zeros = 0.0;
    float nonZeros = 0.0;

    for(int i = 0; i < g->y; i++)
        for(int j = 0; j < g->x; j++)
            if(g->graph[i][j] == 0.0)
                zeros++;
    else
        nonZeros++;

    return nonZeros / zeros;
}


float average(ajgraph *g)
{
    float card = 0.0;
    float sum = 0.0;

    for(int i = 0; i < g->y; i++)
        for(int j = 0; j < g->x; j++){
            if(g->graph[i][j] != 0){
                sum += g->graph[i][j];
                card++;
            }
        }

        return sum / card;
}


void report(char *reportFilePath, profile *pro)
{
    char item[100];
    memset(item, '\0', 100);
    FILE *htmlFile = fopen(reportFilePath, "w");

    fprint_global_style(htmlFile);

    fprintf(htmlFile, "%s\n", "<table>");
    fprintf(htmlFile, "%s\n", "<th>");
    for(int i = 0; i < pro->gst.tbllen-1; i++){
        fprint_td(htmlFile, pro->gst.tbl[i]);
    }
    fprintf(htmlFile, "%s\n", "</th>");

    for(int i = 0; i < strlen(vowels); i++){
        fprintf(htmlFile, "<tr><th>%c", vowels[i]);
        fprintf(htmlFile, "%s", "</th>");

        for(int j = 0; j < pro->gst.tbllen-1; j++){
            sprintf(item, "%d", pro->gst.g.graph[i][j]);
            fprint_td(htmlFile, item);
            fflush(htmlFile);
        }


        fprintf(htmlFile, "</tr>\n");
    }

    fprintf(htmlFile, "%s\n", "</table>");

    fprintf(htmlFile, "%s\n", "<div id=\"break\"></div>");

    fprintf(htmlFile, "%s\n", "<table>");
    fprintf(htmlFile, "<tr><th>%s</th><td>%f</td></tr>\n",
            "Density", density(&(pro->gst.g)));
    fprintf(htmlFile, "<tr><th>%s</th><td>%f</td></tr>\n",
            "Average", average(&(pro->gst.g)));
    fprintf(htmlFile, "%s\n", "</table>");

    fflush(htmlFile);
    fclose(htmlFile);
}


void similarity(profile *a, profile *b)
{
    list L;
    list_init(&L);

    int res;
    for(int i = 0; i < a->gst.tbllen - 1; i++){
        res = str_tbl_lookup(&(b->gst), a->gst.tbl[i]);
        if(res != -1)
            list_insert(&L, a->gst.tbl[i]);
    }

    puts("similarity of edges (a/b)");
    list L2;
    list_init(&L2);
    float *resPtr = 0;
    int vlen = strlen(vowels);
    int res2;
    list_node *ln;
    float sumA = 0.0;
    int cardA = 0;
    float curA = 0.0;

    float sumNS = 0.0;
    int cardNS = 0;


    for(ln = L.head; ln != 0; ln = ln->next){
        res = str_tbl_lookup(&(a->gst),ln->data);
        res2 = str_tbl_lookup(&(b->gst),ln->data);
        for(int i = 0; i < vlen; i++){
            curA = (float)a->gst.g.graph[i][res] / (float)b->gst.g.graph[i][res2];
            if(a->gst.g.graph[i][res] != 0 && b->gst.g.graph[i][res2] != 0
                && curA < 10000.0){ /* hack. mysteriously has larger than expected values */
                    sumA += curA;
                    cardA++;

                    if(!(curA > 0.5 && curA < 1.5)){
                        sumNS += curA;
                        cardNS++;
                    }

                    printf("%s -> %c at %f\n", (char*)ln->data,vowels[i], curA);
                }
        }
    }

    printf("Average similarity = %f\n", sumA / (float)cardA);
    printf("Non-similar average = %f\n", sumNS / (float)cardNS);
}


void clear(profile *pro)
{
    char tmpEdgeCmd[PATH_SIZE] = "del .\\tmp_edge.";
    char vertTblCmd[PATH_SIZE] = "del .\\vert_tbl.";
    char graphCmd[PATH_SIZE] = "del .\\graph.";


    strncat(tmpEdgeCmd, pro->name, PATH_SIZE-1);
    strncat(vertTblCmd, pro->name, PATH_SIZE-1);
    strncat(graphCmd, pro->name, PATH_SIZE-1);

    system(tmpEdgeCmd);
    system(vertTblCmd);
    system(graphCmd);
}



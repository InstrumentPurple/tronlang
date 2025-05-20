package main

/*
 #include "./charstar.h"
 #include "./charstar.c"

 #include "./tree.h"
 #include "./tree.c"
 #include <stdio.h>
 #include <stdlib.h>

 #include "./csv.h"
 #include "./csv.c"

 #include "./microprints.c"

 void printarray(char **data){
	for(int i=0; data[i] != 0; i++){
		puts(data[i]);
	}
 }

 char* get_single(char **data, int i){
	return data[i];
 }
//parse_csv null terminates but be carful with data from elsewhere
 int count_items(char **data){
	int i=0;
	for(; data[i] != 0;i++);
	return i;
 }

 */
// #cgo CFLAGS: -O2 -w
import "C"
//April 30, 2025
import "fmt"
import "regexp"
import "os"
import "unsafe"
import "strings"
import "bufio"
import "math"
import(
"math/big"
"strconv"
)

var DEBUG bool = true

type stackItem struct{
	callerFnName string
	stptr int64
	args []string
	kvargs map[string]string
}


type chainNode struct{
	theKey string
	theData string
	del bool
	empty bool
}

type hashTbl struct{
	tbl []chainNode
	size int64
	count int64
	reallocs int
}

type kvargPair struct {
	ks []string
	es []string
}

const(INFINITY=math.MaxFloat64)

type gEdge struct {
	dest *gVertex
	cost float64
}

type gVertex struct {
	name string
	adj []gEdge
	dist float64
	prev *gVertex
	scratch int
}

type Graph struct {
	vertexs map[string]*gVertex
}

type csvEntity struct {
	head []string
	hasHead bool
	data [][]string
}


func (vrt *gVertex) reset(){
	vrt.dist = INFINITY
	vrt.prev = nil
	vrt.scratch = 0
}

func (g *Graph) clearAll(){
	for _, vert := range g.vertexs{
		vert.reset()
	}
}

func (g *Graph) getVertex(name string) *gVertex {
	got, inset := g.vertexs[name]
	if !inset {
		newvert := &gVertex{name:name} // listen here. this is malloc
		g.vertexs[name] = newvert
		return newvert

	}
	return got
}

func (g *Graph) addEdge(source, destination string, ncost float64){
	v := g.getVertex(source)
	w := g.getVertex(destination)
	v.adj = append(v.adj, gEdge{dest: w, cost: ncost})
}

func (g *Graph) printPath_(dest *gVertex){
	if dest.prev != nil{
		g.printPath_(dest.prev)
	}
	fmt.Print(dest.name + " ")
}

func (g *Graph) printPath(dest string){
	foundItem,okay := g.vertexs[dest]

	if okay{
		g.printPath_(foundItem)
		fmt.Println("cost:", foundItem.dist)
	}

	fmt.Println()
}


// a Go translation of Belman-Ford Algorithm for graph containing negative edge costs
// from it's original C++ (Data Structures and Problem Solving Using C++ by Mark Allen Weiss)
// currently broken
func (g *Graph) negative(start string){
	g.clearAll()
	startV, su := g.vertexs[start]
	if DEBUG{
		fmt.Println("starting vertex",start)
	}
	if su{
		q := []*gVertex{startV}
		startV.dist = 0.0
		startV.scratch++
		if DEBUG{
		fmt.Println("starting vertex scratch variable value =",startV.scratch)
		}
		for len(q) > 0 {
			if DEBUG{
				fmt.Println("in for loop")
				fmt.Println("len of q ", len(q))
			}
			v := q[0]
			q=q[1:]


			//c++ rules on the ++ operator are strange. still never detects the negative cycle
			if v.scratch > 2 * len(g.vertexs){
				if DEBUG{
				fmt.Println("negative cycle detected")
				}
				v.scratch++ // idk
				return // negative cycle detected. crashes i think
			} else {
				if DEBUG{
					fmt.Println("not a negative cycle. still increaing v.scratch frist off queue")
				}
				v.scratch++ // idk
			}

			for i := 0; i < len(v.adj); i++{
				e := v.adj[i]
				w := e.dest
				cvw := e.cost

				if w.dist > (v.dist + cvw){
					w.dist = v.dist + cvw
					w.prev = v

					if w.scratch % 2 == 0 {
						w.scratch++
						if DEBUG{
						fmt.Println("pushing w ", w.name)
						}
						q = append(q, w)
					} else {
						w.scratch++
					}
				}
			}
		}
	}
}


var builtIns  map[string](func ([]string) ) = map[string](func ([]string) ){}

const(VERSION="v0.2 (public test)")
var sc *bufio.Scanner = bufio.NewScanner(os.Stdin)

var callStack []stackItem = []stackItem{}
var worldTree *C.tree = nil
var worldGraph Graph = Graph{vertexs: map[string]*gVertex{}}

var shortTbls map[string]*hashTbl = map[string]*hashTbl{}
var strTbl map[string]string = map[string]string{}
var rootBeer map[string]float64 = map[string]float64{
	"e":2.7182818284590452353602874713526624977572470936999596,
	"pi":3.1415926535897932384626433832795028841971693993751058,
}
var boole map[string]bool = map[string]bool{}
var csvTbl map[string]csvEntity = map[string]csvEntity{}

var observerTbl map[string]([]string) = map[string]([]string){} // func id to slice of strings (in strTbl)

var definedFunctions map[string]([]string) = map[string]([]string){"test":[]string{"!mathSet:\"j\",\"j 1 +\"" ,"!setBoole:\"now\",\"j 10 gt\"","!ifstop:\"now\"","!showRb:","!test:"}}
var definedFunKvargs map[string]kvargPair = map[string]kvargPair{}

func reCompile(s string) *regexp.Regexp{
	rc,_ := regexp.Compile(s)
	return rc
}

var re map[string]*regexp.Regexp = map[string]*regexp.Regexp{
	"begWhiteSpace": reCompile("^( |\t|\r|\n|\r\n)*"),
	"trailWhiteSpace":reCompile("( |\t|\r|\n|\r\n)*$"),
	"validCall":reCompile("![a-zA-Z]*:"),
	"remFunBeg":reCompile("^!"),
	"remFunTrail":reCompile(":(| )$"),
	"defFunc":reCompile("(\t| |)*def "),
	"sourceLoop":reCompile(".*\\(src .*\\)"),
}



var ONE *big.Int = big.NewInt(1)
var ZERO *big.Int = big.NewInt(0)


//factorial
func fact_cancel(at, n *big.Int)*big.Int{

	result := big.NewInt(1.0)

	for n.Cmp(at) != 0 {
		result.Mul(result, n)
		n.Sub(n, ONE)
	}

	return result
}


func bicoef(n, r *big.Int) *big.Int{

	g := big.NewInt(1.0)
	if n == r {
		return ONE
	}
	g.Sub(n, r)
	divdr := big.NewInt(1.0)

	cancelded := fact_cancel(ONE, g)
	if cancelded == ZERO{
		return ONE
	}
	divdr.Quo(fact_cancel(r,n),cancelded)
	return divdr
}


// this funtion was vibed then slightly modified manually
// (RPN) reverse polish notation
func evaluateRPN(expression string) (float64, error) {
	tokens := strings.Split(expression, " ")
	stack := []float64{}

	for _, token := range tokens {
		if num, err := strconv.ParseFloat(token, 64); err == nil {
			stack = append(stack, num)
		} else {
			rb,okay := rootBeer[token]
			if okay {
				stack = append(stack,rb)
				continue;
			} else if strings.Contains(token, "args:"){
				id := (strings.Split(token, "args:"))[1]
				stack = append(stack, stackGetFloat64(id))
				continue;
			}

			if len(stack) < 2 {
				return 0, fmt.Errorf("invalid expression: not enough operands for operator %s", token)
			}
			operand2 := stack[len(stack)-1]
			stack = stack[:len(stack)-1]
			operand1 := stack[len(stack)-1]
			stack = stack[:len(stack)-1]

			var result float64
			switch token {
				case "+":

					result = operand1 + operand2
				case "-":
					result = operand1 - operand2
				case "*":
					result = operand1 * operand2
				case "C":
					n := big.NewInt(int64(operand1))
					r := big.NewInt(int64(operand2))
					if n.Cmp(r) == 0 { //this is a hack to fix broken bicoef
						result = 1.0
					} else {
						result,_ = (bicoef(n,r)).Float64()
					}
				case "/":
					if operand2 == 0.0 {
						return 0, fmt.Errorf("division by zero")
					}
					result = operand1 / operand2
				case "**":
					result = math.Pow(operand1, operand2)
				case "sin":
					if operand2 == 0.0 {
						return 0, fmt.Errorf("division by zero")
					}
					result = math.Sin(operand1 / operand2)
				case "cos":
					if operand2 == 0.0 {
						return 0, fmt.Errorf("division by zero")
					}
					result = math.Cos(operand1 / operand2)
				case "acos":
					if operand2 == 0.0 {
						return 0, fmt.Errorf("division by zero")
					}
					result = math.Acos(operand1 / operand2)
				case "asin":
					if operand2 == 0.0 {
						return 0, fmt.Errorf("division by zero")
					}
					result = math.Asin(operand1 / operand2)
				default:
					return 0, fmt.Errorf("invalid operator: %s", token)
			}
			stack = append(stack, result)
		}
	}

	if len(stack) != 1 {
		return 0, fmt.Errorf("invalid expression: too many operands")
	}

	return stack[0], nil
}


func hash(s string)big.Float{

	sum := big.NewInt(0)
	for _, c := range s{
		sum.Add(sum, big.NewInt(int64(c)))
	}
	//sum.Mul(sum, big.NewInt(15))
	got,_,_ := big.ParseFloat(sum.String(), 10, 0, big.AwayFromZero)
	pri := big.NewFloat(152623.0*60)
	return mod(*got, *pri)
}

func (h *hashTbl) Init(s int64)*hashTbl{
	h.size = s
	cns := make([]chainNode,s)
	for i, _ := range cns{
		cns[i].empty = true
		cns[i].del = false
	}
	h.tbl = cns
	return h
}

func (h *hashTbl) Insert(key, data string)bool{
	hsh_ := hash(key)
	hsh__,_ := strconv.Atoi(hsh_.String())
	hsh := int64(hsh__)
	retn := !( h.tbl[hsh].empty)
	x := int64(1)

	for ;hsh < h.size && !(h.tbl[hsh].empty) ; x++{
		hsh = int64(hsh__) + x * x //quadratic probing
	}

	if hsh >= h.size{
		h.size = hsh
		ntbl := make([]chainNode, h.size)
		copy(ntbl, h.tbl)
		h.tbl = ntbl
		h.reallocs++
		hsh = x
	}
	h.tbl[hsh].del = false
	h.tbl[hsh].empty = false
	h.tbl[hsh].theKey = key
	h.tbl[hsh].theData = data
	h.count++
	return retn
}

func (h *hashTbl) Find(key string)string{
	hsh_ := hash(key)
	hsh__,_ := strconv.Atoi(hsh_.String())
	hsh := int64(hsh__)
	retn := !( h.tbl[hsh].empty)

	if retn && h.tbl[hsh].theKey == key{
		return h.tbl[hsh].theData
	} else if(retn){

		for x := int64(1);!(h.tbl[hsh].empty) && h.tbl[hsh].theKey != key && int64(hsh__) + x * x < h.size; x++{
			hsh = int64(hsh__) + x * x //quadratic probing
		}
		if h.tbl[hsh].theKey == key && !(h.tbl[hsh].del){
			return h.tbl[hsh].theData
		}
	}

	return ""
}

func mod(a,b big.Float)big.Float{
	tmp := a

	for tmp.Cmp(&b) > 0{
		tmp_ := tmp
		tmp.Sub(&tmp_, &b)
	}
	return tmp
}


func convertToStringSlice(data  **C.char) []string {
	args_ := []string{}
	count := int(C.count_items(data))
	for i := 0; i < count; i++{
		args_ = append(args_, C.GoString(C.get_single(data, C.int(i))))
	}
	return args_
}

func unwrap(subj string) string{
	subj = re["remFunBeg"].ReplaceAllString(subj, "")
	subj = re["remFunTrail"].ReplaceAllString(subj, "")
	return subj
}

func getArgs(content string)[]string{
	got:=strings.Replace( content, ":","[seperator]", 1) //needs to be unique

	sep := strings.Split(got,"[seperator]")

	if len(sep) < 2 {
		return []string{}
	}
	argPart := sep[1]

	csvDataC := C.CString(argPart)
	parsedArgDataC := C.parse_csv(csvDataC)
	var args []string

	if argPart != ""{ // get it into golang better
		args = convertToStringSlice(parsedArgDataC)
	} else {
		args = []string{}
	}

	return args
}

// the callstack take 2
func run(blank []string){
	startLoop:
	for len(callStack) > 1{ //we don't care about main yet. Set to 0 eventually
		topItem := callStack[len(callStack)-1]

		if DEBUG{
			fmt.Println("top of stack for ", topItem.callerFnName)
		}
		//todo this is stupid. Put it in scope
		kv,hasKv := definedFunKvargs[topItem.callerFnName]
		if hasKv{
			if DEBUG{
			fmt.Println("has kvargs")
			}
			expns := kv.es
			if len(expns) > 0 {
				for trail, id := range kv.ks{
					if DEBUG{
					fmt.Println("evaluating expression ", expns[trail])
					}
					val,err := evaluateRPN(expns[trail])
					if err != nil {
						fmt.Println(err)
					} else {
						rootBeer[topItem.callerFnName+"."+id] = val
					}
				}
			}
		}

		fnlist, inside := definedFunctions[topItem.callerFnName]
		iptr := topItem.stptr
		if iptr != 0 {
			if (iptr > int64(len(fnlist))){
				if DEBUG{
				fmt.Println("wonder bread fix")
				}
				callStack = callStack[0:(len(callStack)-2)]
				return //all finished
			}
			if DEBUG{
			fmt.Println("resuming at ", iptr)
			}
		}
		if inside{
			for int64(len(fnlist)) > iptr{
				line := fnlist[iptr]


				fnname := getName(line)
				args := getArgs(line)
				if fnname != "math" && fnname != "mathSet"{ // handled in RPN
					for i, arg := range args{

						if strings.Contains(arg, "args:") && !strings.Contains(arg, " "){
							id := (strings.Split(arg, "args:"))[1]
							id_,_ :=strconv.Atoi(id)
							args[i] = callStack[len(callStack)-1].args[id_]
							fmt.Println("args[i]", args[i])
						}
					}
				}

				if(fnname == "ifstop"){
					if boole[args[0]]{
						if DEBUG{
						fmt.Println("poping stack from ifstop")
						}
						callStack = callStack[0:(len(callStack)-2)]
						goto startLoop
						//run([]string{})
						return // idk
					}
				}

				builtin, inblin := builtIns[fnname]
				if inblin{
					if DEBUG{
					fmt.Println("saw builtin", fnname)
					}
					builtin(args)
				}

				_, indefn := definedFunctions[fnname]
				if indefn{
					if DEBUG{
					fmt.Println("pushing to stack")
					}
					callStack[len(callStack)-1].stptr = iptr + 1
					callStack = append(callStack, stackItem{callerFnName: fnname ,stptr:0, args: args})
					goto startLoop
					//run([]string{})
				}
				if DEBUG{
				fmt.Println("iptr",iptr)
				}
				iptr++
			}
			//automatically return when the function is completed
			if iptr >= int64(len(fnlist)) && len(callStack) > 1{
				callStack = callStack[0:(len(callStack)-2)]
				if DEBUG{
				fmt.Println("pop stack reached")
				}
			}
		}
	}
}

func parseAndCall(content string, useless int64) bool{
	//remove whitespace from entity
	content = re["begWhiteSpace"].ReplaceAllString(content, "")
	content = re["trailWhiteSpace"].ReplaceAllString(content, "")

	if re["validCall"].MatchString(content){
		got:=strings.Replace( content, ":","[seperator]", 1) //needs to be unique

		sep := strings.Split(got,"[seperator]")

		if len(sep) >= 2{
			callPart, argPart := sep[0], sep[1]

			if re["sourceLoop"].MatchString(argPart){
				path := strings.Trim(argPart, "(src ")
				path = strings.Trim(path, ")")
				fmt.Println(path)
				file,_ := os.Open(path)
				defer file.Close()

				fsc := bufio.NewScanner(file)

				args := ""
				for fsc.Scan(){
					args = fsc.Text()

					cmd := callPart+":"+args
					fmt.Println(cmd)
					parseAndCall(cmd, 0)

				}

				return true
			}

			//fmt.Println(callPart, argPart)
			//parse arguments as they are csv encoded
			csvDataC := C.CString(argPart)
			parsedArgDataC := C.parse_csv(csvDataC)
			var args []string

			if argPart != ""{ // get it into golang better
				args = convertToStringSlice(parsedArgDataC)
			} else {
				 args = []string{}
			}

			name := unwrap(callPart)

			//C.free_csv_line(parsedArgDataC)
			//C.free(unsafe.Pointer(csvDataC))
			fn,insidebif := builtIns[name]
			if insidebif {
				fn(args)
			}

		}

		return true
	}
	return false
}

func insertWt(args []string){
	var data unsafe.Pointer

	var path, line string

	if len(args) < 2{
		fmt.Print("path=")
		sc.Scan()
		path = sc.Text()
		fmt.Print("data=")
		sc.Scan()
		line = sc.Text()
	} else if(len(args) >= 2) {
		path, line = args[0], args[1]
	}

	data = unsafe.Pointer(C.CString(line))
	strpath := C.CString(path)

	C.tree_make_path_str(&worldTree, strpath)
	C.tree_insert_str(&worldTree, strpath, data)

	C.free(data)
	C.free(unsafe.Pointer(strpath))
}

func showWt(useless []string){
	C.tree_print(worldTree)
}

func findWt(args []string){
	var txt string = ""
	if len(args)==0{
		fmt.Print("path=")
		sc.Scan()
		txt = sc.Text()
	}else if(len(args) >= 1){
		txt = args[0]
	}

	ctxt := C.CString(txt)

	got := C.tree_find_str(&worldTree, ctxt)
	C.puts((*C.char)(got.data))

	C.free(unsafe.Pointer(ctxt))
}


func newShort(args []string){
	var name string
	if len(args)==0{
		fmt.Print("name=")
		sc.Scan()
		name = sc.Text()
	} else {
		name=args[0]
	}
	shortTbls[name] = &hashTbl{}
	shortTbls[name].Init(152623*60)
}


func findShort(args []string){
	var name, key string
	if len(args)==0{
		fmt.Print("name=")
		sc.Scan()
		name = sc.Text()

		fmt.Print("key=")
		sc.Scan()
		key = sc.Text()
	} else if(len(args) >= 2){
		name,key=args[0],args[1]
	}
	got := shortTbls[name].Find(key)
	for _,strId := range observerTbl["findShort"]{ //emit
		strTbl[strId] = got
	}

	fmt.Println(got)
}


func emit(args []string){
	var fn, value string ="",""
	if len(args)==0{
		fmt.Print("function=")
		sc.Scan()
		fn=sc.Text()
		fmt.Print("value=")
		sc.Scan()
		value=sc.Text()

	} else if(len(args)>=2){
		fn,value=args[0],args[1]
	}
	//todo: add rootBeers
	for _,strId := range observerTbl[fn]{
		strTbl[strId] = value
	}
}


func insertShort(args []string){
	var name, key, data string
	if len(args)==0 {
		fmt.Print("name=")
		sc.Scan()
		name = sc.Text()

		fmt.Print("key=")
		sc.Scan()
		key = sc.Text()

		fmt.Print("data=")
		sc.Scan()
		data = sc.Text()
	} else if(len(args)>= 3){
		name,key,data = args[0],args[1],args[2]
	}
	shortTbls[name].Insert(key, data)
}

func newString(args []string){
	for _,val := range args{
		strTbl[val]=""
	}
}

func connect(args []string){
	funcId, strId := args[0], args[1]

	_,okay := observerTbl[funcId]
	if !okay{
		observerTbl[funcId] = []string{strId}
	} else {
		observerTbl[funcId] = append(observerTbl[funcId], strId)
	}
}

func showStrings(useless []string){
	for k,v := range strTbl{
		fmt.Println(k, "=", v)
	}
}

func getVar(args []string){
	if len(args)==1{
		fmt.Println(strTbl[args[0]])
		fmt.Println(rootBeer[args[0]])
		fmt.Println(boole[args[0]])
	}
}

func disconnect(args []string){
	got := observerTbl[args[0]]
	working := []string{}
	for _,val := range got{
		if val != args[1]{
			working = append(working, val)
		}
	}
	observerTbl[args[0]] = working
}

func math_(args []string){
	for _,exp := range args{
		num, _ := evaluateRPN(exp)
		fmt.Println(num)
	}
}

func newRootBeer(args []string){
	rootBeer[args[0]],_ = strconv.ParseFloat(args[1],64)
}

func mathSet(args []string){
	num, err := evaluateRPN(args[1])
	if err != nil{
		fmt.Println(err)
	}
	rootBeer[args[0]] = num
}


func showRb(args []string){
	for k,val := range rootBeer{
		fmt.Println(k,val)
	}
}

func newBoole(args []string){
	for _,id := range args{
		boole[id] = false
	}
}

func boolToFloat64(subj bool)float64{
	if subj{
		return 1.0
	} else {
		return 0.0
	}
}

func float64ToBool(subj float64)bool{
	var ret bool = false
	if int(subj) < 1{
		ret = false
	} else {
		ret = true
	}
	return ret
}

//copy of evaluateRPN with some modifications
func evalBooleExpr(expression string)(bool,error) {
	tokens := strings.Split(expression, " ")
	stack := []float64{}

	for _, token := range tokens {
		if num, err := strconv.ParseFloat(token, 64); err == nil {
			stack = append(stack, num)
		} else {
			rb,okay := rootBeer[token]
			bl,okay2 := boole[token]
			if okay {
				stack = append(stack,rb)
				continue;
			} else if(okay2){
				stack = append(stack, boolToFloat64(bl) )
				continue;
			}else if strings.Contains(token, "args:"){
				id := (strings.Split(token, "args:"))[1]
				stack = append(stack, stackGetFloat64(id))
				continue;
			}

			if len(stack) < 2 {
				return false, fmt.Errorf("invalid expression: not enough operands for operator %s", token)
			}

			operand2 := stack[len(stack)-1]
			stack = stack[:len(stack)-1]
			operand1 := stack[len(stack)-1]
			stack = stack[:len(stack)-1]

			var result float64
			switch token {
				case "gt":
					result = boolToFloat64(operand1 > operand2)
				case "eq":
					result = boolToFloat64(operand1 == operand2)
				case "and":
					result = boolToFloat64(float64ToBool(operand1) && float64ToBool(operand2))
				case "or":
					result = boolToFloat64( float64ToBool(operand1) || float64ToBool(operand2) )
				default:
					return false, fmt.Errorf("invalid operator: %s", token)
			}
			stack = append(stack, result)
		}
	}

	if len(stack) != 1 {
		return false, fmt.Errorf("invalid expression: too many operands")
	}

	return float64ToBool(stack[0]), nil
}

func setBoole(args []string){
	var vr,val string
	if len(args) < 2 {
		fmt.Print("name=")
		sc.Scan()
		vr = sc.Text()
		fmt.Print("value=") //value or expression
		sc.Scan()
		val = sc.Text()
	} else {
		vr,val = args[0],args[1]
	}


	if val == "0"{
		boole[vr] = false
		return
	} else {
		b,_ := evalBooleExpr(val)
		boole[vr] = b
	}
}

func showBoole(args []string){
	for v, b := range boole{
		fmt.Println(v,b)
	}
}


func addEdge_(args []string){
	var src,dest string
	src,dest = args[0], args[1]
	c := args[2]
	nc,_ := strconv.ParseFloat(c, 64)

	worldGraph.addEdge(src, dest, nc)
}

func shortestPath(args []string){
	src := args[0]
	worldGraph.negative(src)
	worldGraph.printPath(args[1])
}

func getName(subj string)string{
	got:=strings.Replace( subj, ":","[seperator]", 1) //needs to be unique

	sep := strings.Split(got,"[seperator]")
	return unwrap(sep[0])
}


func debug(args []string){
	parseAndCall("!addEdge:\"a\",\"b\",\"1.0\"",0)
	parseAndCall("!addEdge:\"b\",\"c\",\"2.0\"",1)
	parseAndCall("!addEdge:\"a\",\"c\",\"1.0\"",2)
	parseAndCall("!shortestPath:\"a\",\"c\"",3)

}

func push(args []string){
	var name string
	if len(args) < 1{
		fmt.Print("name = ")
		sc.Scan()
		name = sc.Text()
	} else {
		name = args[0]
	}

	if len(args) < 2 {
		callStack = append(callStack, stackItem{stptr:0, callerFnName:name})
	} else {
		callStack = append(callStack, stackItem{stptr:0, callerFnName:name, args: args[1:]})
	}
}

func call(args []string){
	push(args)
	run([]string{})
}

//i guess sometimes you don't want to pass strings
func stackGetFloat64(i string)float64{
	j,_ := strconv.Atoi(i)
	got, _ := strconv.ParseFloat( callStack[len(callStack)-1].args[j], 64)
	return got
}

func flip(args []string){
	//if len(args) <
	boole[args[0]] = !boole[args[0]]
}

func main(){
	fmt.Println("Tronlang " + VERSION)

	command := ""

	if len(os.Args) > 1{
		callStack = append(callStack, stackItem{stptr:0, callerFnName:"main", args: os.Args[1:]})
	} else {
		callStack = append(callStack, stackItem{stptr:0, callerFnName:"main"})
	}

	//functions := map[string]int64{}
	//initialize built in functions
	builtIns["insertWt"] = insertWt
	builtIns["showWt"] = showWt
	builtIns["findWt"] = findWt
	builtIns["newShort"] = newShort
	builtIns["findShort"] = findShort
	builtIns["insertShort"] = insertShort
	builtIns["newString"] = newString
	builtIns["connect"] = connect
	builtIns["getVar"] = getVar
	builtIns["showStrings"] = showStrings
	builtIns["emit"] = emit
	builtIns["disconnect"] = disconnect
	builtIns["math"] = math_
	builtIns["mathSet"] = mathSet
	builtIns["newRootBeer"] = newRootBeer
	builtIns["newRb"] = newRootBeer
	builtIns["showRb"] = showRb
	builtIns["newBoole"] = newBoole
	builtIns["setBoole"] = setBoole
	builtIns["showBoole"] = showBoole
	builtIns["addEdge"] = addEdge_
	builtIns["shortestPath"] = shortestPath
	builtIns["debug"] = debug
	builtIns["call"] = call //the only way to call a user defined function from the commandline
	builtIns["flip"] = flip

	var recentDefName string = "main"
	iGuessIptr := int64(0)
	for command != "quit"{
		sc.Scan()
		command=sc.Text()

		if re["remFunBeg"].MatchString(command){
			parseAndCall(command, iGuessIptr)
			iGuessIptr++
		} else if(re["defFunc"].MatchString(command)){

			instructions := []string{}

			name := strings.Trim(command, "def ")
			name = strings.Trim(name, ":")
			recentDefName = name

			for {
				fmt.Print("... ")
				sc.Scan()
				if sc.Text() == "enddef"{
					break;
				} else {

					if sc.Text() == "defkv"{
						k := []string{}
						exprs := []string{}
						for {
							fmt.Print("k=")
							sc.Scan()
							if sc.Text() == "endkv"{
								definedFunKvargs[recentDefName] = kvargPair{ks:k, es:exprs}
								break;
							} else {
								k=append(k, sc.Text())
								fmt.Print("v=")
								sc.Scan()
								exprs=append(exprs, sc.Text())
							}
						}
					} else {
						instructions = append(instructions, sc.Text())
					}
				}
			}

			definedFunctions[name] = instructions
		}
	}
}

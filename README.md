# tronlang
Tronlang script interpreter written in Golang and C

CURRENTLY EXPERIMENTAL

initial created to facilitate access to datastructures. Includes a general tree call the world tree because it's gobal. Hash tables are supported through short tables (which have limited capacity.). A global graph is implemented as a digraph and can find shortest paths with the Belman-ford algorithm

May in fact leak memory somewhere. Have fun building up memory. tron.exe should be FAT

simply build with this command:
```
go build tron.go
```

Tronlang uses CGo which means you need a C compiler. What simply worked for me was gcc. I don't know about other compilers but you'd probably have to configure something to get this to compile with anything else. 

A modern version of Go might be needed. I build this myself with 1.24.2

If you need a C compiler that works with windows you can install gcc provided by strawberry perl (https://strawberryperl.com/)

project uses https://github.com/semitrivial/csv_parser/tree/master for csv parsing

this will give you a list of availible builtIn functions. ifstop and return are only availible within user defined functions.

```
!help:
```

arguments are CSV

function names must be alpha-numeric

set rootbeer variable j to 0
```
!setMath:"j","0.0"
```

expressions are reverse polish notation
```
!setMath:"m","j 1 +"
```

```
!setBoole:"now","0"
```
boolean expressions are also reversion polish notation

```
!setBoole:"now","1 0 and"
```
we are now ready to call the test function and watch it count

```
!call:"test"
```

reset the interpreter's state

```
!nuke:
```

if statement is achieved with ifcall and function definitions

```
!ifcall:"1 1 and","fn","some argument"
```

start a function definition. Not needed when using loadFn (previously loadfn)
```
def a:
```

use arguments

```
!mathSet:"k","args:0 1 +"
```

return string

```
!return:"a string"
```

return value of variable

```
!return:"deref:k"
```

end a function definition

```
enddef
```

get most previous return value

```
!storeRet:"varhere"
```

do a source loop

```
!addEdge:(src ./edges.csv)
```

add a function from disk

```
!loadFn:./function.tron,test2
!test2:
```

confused about what arguments go to which builtIns? Simply call the builtin without arguments and you will start the builtIn's options in the order they are passed.

The following are all the availible reverse polish operators within rootbeer expressions like you can do with math or setMath and they all require two arguments. With the trig functions the operands are divided before they are passed to the trig function.

/

\+

\-

\*

C

\*\*

mod

sin

cos

acos

asin

 ```
!pristineRb:
!math:pi 2 sin
```


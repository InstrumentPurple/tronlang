# tronlang
Tronlang interpreter written in Golang and C

CURRENTLY EXPERIMENTAL

initial created to facilitate access to datastructures. Includes a general tree call the world tree because it's gobal. Hash tables are supported through short tables (which has limited capacity.). A global graph is implemented as a digraph and can find shortest paths with the Belman-ford algorithm

May in fact leak memory somewhere. Have fun building up memory. tron.exe should be FAT

simply go build tron.go

If you need a C compiler that works with windows you can install gcc provided by strawberry perl (https://strawberryperl.com/)

project uses https://github.com/semitrivial/csv_parser/tree/master for csv parsing

check out tron.go for a list of the built in's in main

arguments are CSV

set rootbeer variable j to 0

!setMath:"j","0.0"


expressions are reverse polish notation

!setMath:"m","j 1 +"


!setBoole:"now","0"

boolean expressions are also reversion polish notation

!setBoole:"now","1 0 and"

we are now ready to call the test function and watch it count

!call:"test"

reset the interpreter's state

!nuke:

if statement is achieved with ifcall and function definitions

!ifcall:"1 1 and","fn","some argument"

start a function definition. Not needed when using loadFn (previously loadfn)

def a:

use arguments

!mathSet:"k","args:0 1 +"

return string

!return:"a string"

return value of variable

!return:"deref:k"

end a function definition

enddef

get most previous return value

!storeRet:"varhere"

do a source loop

!addEdge:(src ./edges.csv)

add a function from disk

!loadFn:

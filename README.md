# OCamlStackInspection

First Homework of the Language-based Technology for Security exam.

It is an interpreter of a simple functional language which ncludes a dynamic mechanism for enforcing access control checks, 
along the line of the so-called stack inspection algorithm.

## Permits and Operations
The permissions concern the reading, writing and execution of a file. 
Two permissions are the same if they refer to the same file. 
Two operations are the same if they require the same file to be written / read / executed.

The permission type was defined as:
type permission =
| ReadPerm of string
| WritePerm of string
| ExecutePerm of string


## Stack Inspection simulation
The ieval function has been modified, so that the stack and the permissions table can also be taken into account when evaluating an expression.
During the declaration, each function is associated with a list of permissions, which are those that the function has. The Closure contains the list of permissions, which will then be checked before carrying out a read / write / execute operation.

With each function call, the stack and the permissions table are modified, as follows:

• the called function is added at the top of the stack, in order to keep track of all the called functions. For simplicity the functions are uniquely identified with their parameter. If the function contains another function in the Body, the same thing will be recursively done, the last function called will therefore be at the top of the stack.

• a pair containing the name of the called function and the list of its permissions is added to the table of permissions, as in the previous case, if the Body contains a function, the permissions of that function will also be added, thanks to recursion. 

Before the evaluation of a privileged expression, Read or Execute or Write, the check function (of type: stack -> permissionTable -> permission -> bool) is called, which checks that all the functions present in the stack (starting from head of the list, therefore from the last function called) possess the permission required by the operation. To do this, it builds a list of all the permission lists of the functions in the stack, then checks that all the lists contain the permission required by the operation; if yes, it returns true, otherwise false, denying the execution of the requested operation.

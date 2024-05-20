My first TLA+ spec. It formalizes the classical linked-list reversal algorithm.

A node is simply a number, and the list is a function from a number to another, or NIL.
In the initial state, every node with the number n points to n+1, or NIL for the last node.
In the final state, every node should point to n-1, except the node 1, which points to nil.

The empty list case isn't handled.

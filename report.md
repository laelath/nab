We created a lazy version of the 430 language Neerdowell, which was chosen
because it was the latest langauge whose implementation did not crash when
running the test suite.

The language is a variation of Neerdowell we called Nab.
It is fully lazy in function arguments, let-bindings, and match expressions.
The language additionally has `box` and `cons` as lazy data structures.
Vectors and strings are still strict as might not be expected.
This was done mainly for simplicity of implementation, since `make-vector` and
`make-string` would both require strictness in their first argument so the
actual memory for the string/vector can be allocated (this could also be
deferred at the cost of complex semantics), and implementing `vector-set!` with
thunks would require making the semantics only lazy in the final argument.
These design complications would have been considered if there
were more operations that mutated data structures.

Thunks are implemented by adding a layer of indirection into the heap.
The structure of evaluated thunks in the heap is just the value itself.
The structure of unevaluated thunks is a new constant `val-thunk`, followed by
a closure (a code label followed by the variables it closes over).

Expressions that are arguments to applications, let-bound to variables, and
scrutinized by matches are thunked.

We also implemented `letrec` to enable further exploitation of the laziness of
lists.

The classic infinite list example:
```
(define (take n lst)
  (if (zero? n)
      '()
      (cons (car lst) (take (sub1 n) (cdr lst)))))
(letrec ([ones (cons 1 ones)])
  (take 5 ones))
```

One of the harder parts about implementing laziness turned out to be the
interface between the lazy data structures and the different program runtimes.
For the C runtime, the evaluation can be implemented by having the C code call
back into the code while printing to compute unevaluated thunks. This was done
by including an `eval_thunk` trampoline in the generated a86.
However, when producing values for Racket, there is no (reasonable) way of
calling back into the compiled x86.
Instead we elected to implement an a86 function `strictify` that converts the
lazy data structures into strict ones, allowing the same `unload/free` to be
used, at the cost of now requiring a compile-time switch between generating code
that is compatible with the C runtime and the `asm-interp` runtime.

The only optimization that is implemented by the compiler is to avoid the
creation of 'trivial' thunks.
These are thunks where the only operation they perform is either a variable
lookup or returning a literal value.
The former case can be optimized by just performing the variable lookup without
forcing the thunk, i.e. just copying the thunk's address.
For literal values we still need to create a thunk, but instead of creating a
full closure, we can create an "evaluated" thunk, saving the creation of a
defunctionalized lambda.

We did not get to implementing any form of strictness analysis.
Actually implementing a strictness analysis that does not change the behavior
of the programs is complicated by the fact that Nab has side effecting
operations that can occur in any arbitrary expressions.
This means that any strictness analysis would also need to consider whether it
could be reordering the evaluation of thunks that produce side effects when
forced.

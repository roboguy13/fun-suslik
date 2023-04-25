Setup
---

To install the necessary GHC executable and the dependencies, run

    stack setup

To build the project, run

    stack build

To run the compiler, run

    ./fun-suslik.sh filename.fsus

where `filename.fsus` is the source file you want to compile.

Running Tests
---

To run every test:

    ./run-tests.sh

To run an individual test, in this case `filterLt9`:

    ./run-tests.sh --test-options='-p "/filterLt9/"'

Compiler Stages
---

Demonstrated by showing how an example transforms in each stage.

The running example is:

```
%generate filterLt7 [Sll[readonly]] Sll

Sll : List -> layout[x];
Sll Nil := emp;
Sll (Cons head tail) := x :-> head, (x+1) :-> tail, Sll tail

filterLt7 : List -> List;
filterLt7 := filter (\v. v < 7)

filter : (Int -> Bool) -> List -> List;
filter p Nil      := Nil;
filter p (Cons head tail)
  | p head       := Cons head (filter p tail);
  | not (p head) := filter p tail;
```

1. Parsing

Self-explanatory


2. Defunctionalization/lambda lifting

```
filterLt7 : List -> List;
filterLt7 Nil      := Nil;
filterLt7 (Cons head tail)
  | head < 7       := Cons head (filterLt7 tail);
  | not (head < 7) := filterLt7 tail;
```

3. Elaboration

This stage performs simple inference of layouts (and elaborates by inserting
`lower` and `instantiate` for the inferred layouts). Also generates SuSLik names for
the layout parameters. In this example, the generated names are `y` and `r`.

The pattern matches are also decorated with the layouts and corresponding layout
parameters are generated (in this case, the parameter is `x`).

```
filterLt7 (Sll[readonly ; x] Nil) := lower Sll[readonly ; r] Nil;
filterLt7 (Sll[readonly ; x] (Cons head tail))
  | head < 7       := lower Sll[readonly ; r] (Cons head (instantiate [Sll[readonly ; tail]] Sll[y] filterLt7 tail));
  | not (head < 7) := instantiate [Sll[readonly ; tail]] Sll[r] filter tail;
```

4. Unfold layout for pattern matching

```
filterLt7 Nil      :=
    layout{ emp } & lower Sll[readonly ; r] Nil;
filterLt7 (Cons head tail)
  | head < 7       :=
        layout{ x :=> head, (x+1) :=> tail } & lower Sll[readonly ; r] (Cons head (instantiate [Sll[readonly ; tail]] Sll[y] filterLt7 tail));
  | not (head < 7) :=
        layout{ x :=> head, (x+1) :=> tail } & instantiate [Sll[readonly ; tail]] Sll[r] filter tail;
```


5. Unfold lowered constructor applications

In "pseudo-code":

```
filterLt7 Nil      := layout{ emp };
filterLt7 (Cons head tail)
  | head < 7       := layout{ x :=> head, (x+1) :=> tail, r :-> head, (r+1) :-> y, filterLt7__Sll_Sll[tail | y] tail));
  | not (head < 7) := layout{ x :=> head, (x+1) :=> tail, filterLt7__Sll_Sll[tail | r] tail));
```

6. Generation

Final step into SuSLik.

By the time it reaches this stage, every
application in a `layout` should be of the form `f[arg1, arg2, ..., argN | result] v1 v2 ... vM`, where
`v1`, ..., `vM` are fun-SuSLik variables. `arg1`, ... `argN` and `result` are SuSLik names.
Only the SuSLik names of an application will be needed for this final stage, and
the fun-SuSLik variables `v1`, ..., `vM` will not be used.

The main work this stage performs is turning pattern
matches into the corresponding SuSLik branch condition.

```
inductive ro_Sll(loc x) {
| x == 0 => { emp }
| not (x == 0) => { x :=> head ** (x+1) :=> tail ** ro_Sll(tail) }
}

inductive Sll(loc x) {
| x == 0 => { emp }
| not (x == 0) => { x :-> head ** (x+1) :-> tail ** Sll(tail) }
}

inductive filterLt7__Sll_Sll(loc x, loc r) {
| x == 0 => { emp }
| not (x == 0) && head < 7 => {
    x :=> head ** (x+1) :=> tail ** r :-> head ** (r+1) :-> y ** filterLt7__Sll_Sll(tail, y)
  }
| not (x == 0) && not (head < 7) => {
    x :=> head ** (x+1) :=> tail ** filterLt7__Sll_Sll(tail, r)
  }
}
```


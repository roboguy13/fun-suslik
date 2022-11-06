Compiler Stages
---

Demonstrated by showing how an example transforms in each stage.

1. Parsing

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
the layout parameters. In this example, the generated names are `x` and `r`.

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

Uses temporary variables to connect nested function applications and generates SuSLik

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
    x :=> head ** (x+1) :=> tail ** r :-> head ** (r+1) :-> nxt ** filterLt7__Sll_Sll(tail, nxt)
  }
| not (x == 0) && not (head < 7) => {
    x :=> head ** (x+1) :=> tail ** filterLt7__Sll_Sll(tail, r)
  }
}
```


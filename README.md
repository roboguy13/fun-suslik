Compiler Stages
---

1. Parsing

```
%generate filterLt7 [Sll] Sll

filterLt7 : List -> List;
filterLt7 Nil      := Nil;
filterLt7 (Cons head tail)
  | head < 7       := Cons head (filterLt7 tail);
  | not (head < 7) := filterLt7 tail;
```

2. Elaboration

This stage performs simple inference of layouts and generates SuSLik names for
them.

```
filterLt7 Nil      := lower Sll[readonly ; x] Nil;
filterLt7 (Cons head tail)
  | head < 7       := lower Sll[readonly ; x] (Cons head (instantiate [Sll[readonly ; x]] Sll[r] filterLt7 tail));
  | not (head < 7) := instantiate [Sll[readonly ; x]] Sll[r] filter tail;
```

3. Generation

This unfolds layout definitions (where applicable) and uses temporary variables
to connect nested function applications.

```
inductive ro_Sll(loc x) {
| x == 0 => { emp }
| not (x == 0) => { x :=> head ** (x+1) :=> tail ** ro_Sll(tail) }
}

inductive Sll() {
| x == 0 => { emp }
| not (x == 0) => { x :-> head ** (x+1) :-> tail ** Sll(tail) }
}

inductive filterLt7(loc x, loc r) {
| x == 0 => { emp }
| not (x == 0) && head < 7 => {
    x :=> head ** (x+1) :=> tail ** r :-> head ** (r+1) :-> nxt ** filterLt7(tail, nxt)
  }
| not (x == 0) && not (head < 7) => {
    x :=> head ** (x+1) :=> tail ** filterLt7(tail, r)
  }
}
```


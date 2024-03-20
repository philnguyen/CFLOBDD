This is a re-implementation of the [CFLOBDD](https://dl.acm.org/doi/10.1145/3651157) work (by Sistla, Chaudhuri, and Reps) in Idris,
to help my understanding.

Differences from the original paper:
* The `Internal` grouping drops the `AReturnTuple` field (which seems to be always identity).
* The `Internal` grouping "zips" the parallel arrays of `BConnections` and `BReturnTuples` into
  one array of `CFLOBDD`s.
* The paper's `ValueTuple` and `ReturnTuple` are both represented as `Vect n t`
  (a vector whose type tracks size and element).
* `CFLOBDD k t` and `Grouping k n` are defined as a mutual induction:
  (1) a `Grouping` is some wiring waiting on a list of "continuations" to select,
  and (2) a `CFLOBDD` is a `Grouping` paired with the "continuation" list.
  The type index `k` tracking height makes it obvious that the data cannot be cyclic,
  and structurally recursion on it must terminate.
  This also allows a nicer implementation of the operational semantics as mutual induction
  on the data.
* The `DontCare` grouping is "height-polymorphic", instead of strictly 0 as in the paper.
  This obviates the need for the `No-Distinction-Proto-CFLOBDD` family.
* The `level` and `exits` properties aren't stored as data at runtime.
  They're just static type indices to convince the type-checker that things match up
  and terminate.

Code tested with Idris 2 `0.7.0`:
```
idris2 Main.idr
```

### Project structure:

* [`CFLOBDD.idr`](https://github.com/philnguyen/CFLOBDD/blob/main/src/CFLOBDD.idr) defines the datastructure and its operational semantics
* [`Construction1.idr`](https://github.com/philnguyen/CFLOBDD/blob/main/src/Construction.idr) implements "Construction 1" in Appendix C
* [`Tests.idr`](https://github.com/philnguyen/CFLOBDD/blob/main/src/Tests.idr) transcribes and tests some examples from the paper
* [`Main.idr`](https://github.com/philnguyen/CFLOBDD/blob/main/src/Main.idr) runs the residual tests I couldn't express as theorems

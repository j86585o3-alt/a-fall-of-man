# llm-acl2-books: 102-book certified checkpoint

This portable archive contains 102 ordinary ACL2 source books and the complete
fresh `.cert.out` transcript for every source.  The sources were copied into an
empty workspace and certified serially under ACL2 8.7/SBCL 2.6.5.  A second
certification invocation rebuilt zero books.

The rational-pair amendment adds
`zcx2-total-rational-pair-wfta.lisp`, exposing the compiler's native
rational-pair vector type for both forward and inverse transforms.  ACL2 proves
compiled/direct equality in both directions.  The older scalar interfaces are
proved to be exact restrictions through `QCX-REALIFY`.

The object-stream front end now accepts both legacy scalar requests and native
pair requests.  A pair request is exactly two ACL2 objects, for example:

```lisp
(:wfta-pairs :inverse 3 1/10)
((1 . 1/2) (2 . -1) (3 . 0))
```

The stateful entry points are `ZCZ-MAIN` for standard object input/output and
`ZCZ-RUN-FILE` for a named object file.  Successful requests print one
ACL2-readable list of rational pairs.  The order must be an odd prime greater
than two, epsilon a positive rational, and the input vector must have exactly
the stated length.

`release-metadata/RATIONAL-PAIR-WFTA-AND-WATERFALL-ROADMAP-2026-06-29.md`
records the next proposed research line: theory capsules, proof-plan semantics,
ADP/ranked plan optimization, untrusted plan execution, final ordinary ACL2
checking, and benchmarked waterfall robustness.

No `.cert` binaries are included; those are Lisp-implementation-specific.

# llm-acl2-books: 101-book certified checkpoint

This portable archive contains 101 ordinary ACL2 source books and the complete
fresh `.cert.out` transcript for every source. The sources were copied into an
empty workspace and certified serially under ACL2 8.7/SBCL 2.6.5. A second
certification invocation rebuilt zero books.

The WFTA epilogue adds:

- `zcx-total-rational-inverse-wfta.lisp`, an inverse-form WFTA obtained by
  conjugating the generated rational twiddle table and scaling by exact
  rational `1/p`; and
- `zcz-rational-wfta-object-io.lisp`, a logical request validator plus a small
  program-mode shell using ACL2's built-in `state` stobj, object channels,
  `read-object`, and `fmt`.

A request is exactly two ACL2 objects, for example:

```lisp
(:wfta :inverse 3 1/10)
(1 2 3)
```

The stateful entry points are `ZCZ-MAIN` for standard object input/output and
`ZCZ-RUN-FILE` for a named object file. Successful requests print one
ACL2-readable list of rational pairs. The order must be an odd prime greater
than two, epsilon a positive rational, and the input vector a rational list of
that order.

`ZCX-TOTAL-RATIONAL-INVERSE-WFTA-CORRECT` proves exact equality between the
compiled inverse-form WFTA and the corresponding direct inverse-form DFT over
the same conjugated generated rational table. Since the generated twiddle has
approximate closure, it does not assert exact forward/inverse round-trip
recovery.

No `.cert` binaries are included; those are Lisp-implementation-specific.

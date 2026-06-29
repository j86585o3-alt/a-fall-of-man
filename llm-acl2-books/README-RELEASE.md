# llm-acl2-books: fully searched rational WFTA checkpoint

This portable source release contains 95 ordinary ACL2 books.  Five books
extend the rational Winograd/DFT line from a certificate-driven compiler to a
resource-bounded, witness-free public generator interface:

* `zco-dyadic-sign-bracket-search.lisp` certifies finite dyadic polynomial
  sign-bracket search, including soundness, exact grid width, and completeness
  relative to the searched finite grid.
* `zcp-stereographic-sector-bracket.lisp` specializes that search to the
  nonzero stereographic sector used for rational twiddle construction.
* `zcq-generated-rational-wfta-interface.lisp` searches the bisection precision
  and composes the resulting rational twiddle certificate with the universal
  Rader/Toom-Cook compiler.
* `zcr-primitive-root-certificate-search.lisp` searches finite-field elements
  and proves that every successful result has multiplicative order `p-1`.
* `zcs-fully-generated-rational-wfta.lisp` exposes the complete generated
  object and proves execution equality with the direct rational DFT whenever
  its executable certificate predicate succeeds.

The public construction takes only `p`, rational `epsilon`, finite grid depth,
finite precision fuel, and rational input data.  It does not require a supplied
primitive root, sign bracket, bisection depth, twiddle table, Rader table, or
Toom-Cook plan.

The theorem is intentionally conditional on executable search success.  This
release does not claim that particular finite resource bounds succeed for all
primes and all positive rational epsilons.

All 95 books were certified in one empty source-only workspace under ACL2 8.7.
The archive contains sources, fresh `.cert.out` transcripts, hashes, smoke-test
transcripts, and audit records.  Implementation-specific `.cert` products are
not included in this portable archive.

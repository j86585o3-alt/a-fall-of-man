# llm-acl2-books: 84-book spline and rational-bisection checkpoint

Release date: 2026-06-29

This archive is a source release of 84 ordinary ACL2 books.  It retains the
82-book universal generated Rader/Toom--Cook WFTA closure, adds a small
arbitrary-dimensional rational not-a-knot spline certificate kernel, and
promotes a repaired rational polynomial sign-bisection engine for the next
WFTA twiddle-seed construction.

The release was built with ACL2 8.7 under the recovered SBCL image and the
verified basic community-books cache.  It contains no ACL2(r) books,
nonstandard analysis, real-number semantics, or Lisp complex-number
assumptions.  Complex quantities are represented as pairs of ACL2 rationals.

## Fresh certification

The exact 84 `.lisp` files in this archive were copied to an empty workspace
and certified serially with:

```sh
export ACL2=/mnt/data/acl2-8.7-recovery/sbcl-saved_acl2
export ACL2_SYSTEM_BOOKS=/mnt/data/acl2-8.7-recovery/books
export ACL2_CUSTOMIZATION=NONE
/mnt/data/acl2-8.7-recovery/books/build/cert.pl -j1 *.lisp
```

The cold-run and idempotence logs, source/certificate hashes, source identity
audit, and trust audit are under `release-metadata/`.  Complete `.cert.out`
transcripts are retained.  Implementation-specific `.cert`, `.fasl`, and
`.port` products are represented by hashes rather than vendored.

## New books

`zcg-rational-not-a-knot-spline-kernel.lisp` checks finite rational scalar and
coordinate-major vector cubic spline certificates with approximate endpoint
interpolation, exact C2 joins, and both endpoint not-a-knot conditions.
Evaluation is proved to produce an ACL2-rational vector of the certified
arbitrary dimension.

`zch-rational-polynomial-sign-bisection.lisp` certifies exact rational
midpoint refinement of polynomial sign brackets, including sign preservation,
interval containment, exact dyadic width, and an executable positive-rational
epsilon selector.

See `release-metadata/SPLINE-AND-BISECTION-CHECKPOINT-2026-06-29.md` for the
mathematical and recovery details.

## WFTA status

The universal generated Rader/Toom--Cook compiler remains closed by
`zcf-rader-index-implies-compact.lisp`.  The next substantial seam is the
finite rational construction of stereographic twiddle parameters.  The new
`zch` book supplies its certified sign-refinement kernel.

## Verification

From the extracted `llm-acl2-books` directory:

```sh
sha256sum -c SHA256SUMS
```

Then run the serial certification command above.  `-j1` is recommended on
memory-constrained machines.

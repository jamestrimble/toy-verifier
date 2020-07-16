# toy-verifier: A simple verifier for PB proofs

## Don't use this verifier for anything serious!!!

Use [VeriPB](https://github.com/StephanGocht/VeriPB) instead.  It's faster and
more thoroughly tested.

## Input format

The input format is the same as that of
[VeriPB](https://github.com/StephanGocht/VeriPB).

## Usage

```
python3 toy-verifier.py model.opb proof.proof [--verbose|--canonical]
```

## Notes on design and limitations

toy-verifier was written in a hurry, so I am sure the design is suboptimal.  I
borrowed a few ideas from the code of VeriPB, but if you're wondering how to
write a good verifier, the VeriPB code is a much better place to look.

Variable numbers are positive integers.  Literals are stored as integers, with
a positive integer representing the variable of that number, and a negative
integer `lit` representing the negation of the variable whose number is `~lit`.

Each `Constraint` is a >= constraint.  The left-hand side is represented as a
map from variable number to coefficent.  Constraints are stored with only
positive literals and possibly-negative coefficients.  Each `Constraint` also
stores its canonical form (with only positive coefficients and a non-negative
right-hand side) in the `canonical_form` field.  This is a 2-tuple, with the
first element being a list of `(coef, literal)` pairs, and the second element
being the right-hand side.

Unit propagation is done in a very simple way without watched literals, which
is why it is so slow!

The parser does not check carefully for syntax errors in the OPB and proof
files.

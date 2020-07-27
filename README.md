# toy-verifier: A simple verifier for PB proofs

## Don't use this verifier for anything serious!!!

Use [VeriPB](https://github.com/StephanGocht/VeriPB) instead.  It's faster and
more thoroughly tested.

## Input format

The input format is the same as that of
[VeriPB](https://github.com/StephanGocht/VeriPB).

## Usage

```
python3 toy-verifier.py model.opb proof.proof [--verbose]
```

## Notes on design and limitations

toy-verifier was written in a hurry, so I am sure the design is suboptimal.  I
borrowed a few ideas from the code of VeriPB, but if you're wondering how to
write a good verifier, the VeriPB code is a much better place to look.

Literals are stored as strings using the original variable names, with a
leading tilde (~) indicating a negated variable.

Each `Constraint` is a >= constraint.  The left-hand side is represented as a
map from literal to coefficent, in canonical form (with only positive
coefficients and a non-negative right-hand side).

Unit propagation is done in a very simple way without watched literals, which
is why it is so slow!

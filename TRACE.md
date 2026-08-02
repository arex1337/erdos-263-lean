# Erdős 263 reasoning trace

## Claim

`Erdos263.formalConjectures_folklore` proves the literal existing folklore
variant in `google-deepmind/formal-conjectures`, as present in PR #4679's
head:

```lean
theorem formalConjectures_folklore (a : ℕ → ℕ)
    (ha : Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (2 ^ n : ℝ)))
      atTop atTop) :
    Irrational (∑' n, 1 / (a n : ℝ))
```

This is a partial result for Erdős problem 263. It does not settle either
headline question on the problem page.

## Production chain

1. AI proof workers formalized Erdős's 1975 monotone argument.
2. A sorting argument removed the monotonicity hypothesis for positive
   integer sequences.
3. The Formal Conjectures adapter replaced zero entries by one. Root growth
   proves that only finitely many entries change.
4. The positive no-monotonicity theorem was applied to the normalized
   sequence.
5. The original and normalized reciprocal sums differ by a rational finite
   prefix, so irrationality transfers back to the original sum.
6. Lean checked the adapter and its dependencies. The adapter contains no
   `sorry`, `admit`, or custom axioms.

## Evidence

- Exact adapter: `Erdos263/FormalConjecturesAdapter.lean`
- No-monotonicity proof: `Erdos263/Erdos1975F.lean`
- Human-readable proof companion: `PROOF-1975.md`
- Axiom command: `CheckFormalConjecturesAdapterAxioms.lean`

## Production disclosure

The Lean proofs and analysis were produced by AI agents under human direction.
The human repository owner directed the work and publication. Lean's kernel,
rather than agent prose, is the proof-verification authority.

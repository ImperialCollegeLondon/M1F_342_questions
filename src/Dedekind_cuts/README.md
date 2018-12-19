# M1F Week 7 Problems class question

Part of the question this week described the construction of the reals as Dedekind cuts. This is not in Lean -- Lean's definition of the reals is as Cauchy sequences modulo null sequences.

So here are some things one could do in Lean:

1) (see framework.lean) Construct the Dedekind reals as Dedekind cuts, and prove that they are a complete archimedean totally ordered field.

2) (see challenge.lean) Prove that any complete archimedean totally ordered field is uniquely isomorphic to Lean's real numbers.

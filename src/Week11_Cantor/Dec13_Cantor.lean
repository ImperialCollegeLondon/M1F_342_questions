-- Cantor's theorem in Lean

import tactic.interactive

open function

/- Theorem: If X is any type, then there is no bijective function
   f from X to the power set of X.
-/
theorem no_bijection_to_power_set (X : Type) :
∀ f : X → set X, ¬ (bijective f) :=
begin
  -- Proof by Kevin Buzzard
  -- let f be a function from X to the power set of X
  intro f,
  -- Assume, for a contradiction, that f is bijective
  intro Hf,
  -- f is bijective, so it's surjective.
  cases Hf with Hi Hs,
  -- it's also injective, but I don't even care
  clear Hi,
  -- Let S be the usual cunning set
  let S : set X := {x : X | x ∉ f x},
  -- What does surjectivity of f say when applied to S?
  have HCantor := Hs S,
  -- It tells us that there's x in X with f x = S!
  cases HCantor with x Hx,
  -- That means x is in f x if and only if x has is in S.
  have Hconclusion_so_far : x ∈ f x ↔ x ∈ S := by rw [Hx],
  -- but this means (x ∈ f x) ↔ ¬ (x ∈ f x)
  have Hlogical_nonsense : (x ∈ f x) ↔ ¬ (x ∈ f x) := Hconclusion_so_far,
  -- automation can now take over.
  tauto!,
  -- Other proofs welcome. Get in touch. Write a function. 
  -- xenaproject.wordpress.com
end

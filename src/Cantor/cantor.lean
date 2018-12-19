-- Cantor's theorem in Lean

import tactic.interactive

open function

/- Theorem: If X is any type, then there is no bijective function f
   from X to the power set of X.
-/

theorem no_bijection_to_power_set (X : Type) :
∀ f : X → set X, ¬ (bijective f) :=
begin
  -- Proof by Kevin Buzzard

  -- let f be an arbitrary function from X to the power set of X
  intro f,
  -- Assume, for a contradiction, that f is bijective
  intro Hf,
  -- f is bijective, so it's surjective.
  cases Hf with Hi Hs,
  -- it's also injective, but I don't even care
  clear Hi,
  -- Let S be the usual cunning set
  let S : set X := {x : X | x ∉ f x},
  -- what is the definition of surjective?
  unfold surjective at Hs,
  -- What does surjectivity of f say when applied to S?
  have HCantor := Hs S,
  -- It tells us that there's x in X with f x = S!
  cases HCantor with x Hx,
  -- That means x is in f x if and only if x has is in S.
  have Hconclusion_so_far : x ∈ f x ↔ x ∈ S := by rw [Hx],
  -- but this means (x ∈ f x) ↔ ¬ (x ∈ f x)
  have Hlogical_nonsense : (x ∈ f x) ↔ ¬ (x ∈ f x) := Hconclusion_so_far,
  -- automation can now take over.
  revert Hlogical_nonsense,
  simp,
  -- Other proofs welcome. Get in touch. Write a function. 
  -- xenaproject.wordpress.com
end

-- folding up the proof gives this
theorem no_bijection_to_power_set'
  (X : Type)
  (f : X → set X) :
bijective f → false :=
λ ⟨Hi, Hs⟩,
let ⟨x,Hx⟩ := Hs {x : X | x ∉ f x} in
have Hconclusion_so_far : x ∈ f x ↔ x ∈ _ := by rw [Hx],
begin clear _fun_match,clear _let_match,tauto! end

-- NB this function is in mathlib already, it's called
-- cantor_surjective. The proof is quite compressed: two lines!
theorem cantor_surjective
  (α : Type)
  (f : α → α → Prop)
  (h : function.surjective f) :
false :=
let ⟨D, e⟩ := h (λ a, ¬ f a a) in
(iff_not_self (f D D)).1 $ iff_of_eq (congr_fun e D)


-- When unravelled, the mathlib proof looks like this:
theorem cantor_surjective'
  (X : Type)
  (f : X → set X)
  (Hs : surjective f) :
false :=
begin
have Hcantor := Hs {x : X | x ∉ f x},
cases Hcantor with x Hx,
  apply (iff_not_self (x ∈ f x)).1,
  apply iff_of_eq,
  apply congr_fun Hx x,
end 

/-
  NB I renamed the variables in the mathlib proof
  α → X
  h → Hf
  D → x
  e → Hx,
-/
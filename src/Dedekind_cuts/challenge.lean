import algebra.archimedean
import data.real.basic

definition completeness_axiom (k : Type*) [preorder k] : Prop :=
∀ (S : set k), (∃ x, x ∈ S) → (∃ x, ∀ y ∈ S, y ≤ x) →
  ∃ x, ∀ y, x ≤ y ↔ ∀ z ∈ S, z ≤ y

open function

theorem characterisation_of_reals (k : Type*) [discrete_linear_ordered_field k] [archimedean k] :
completeness_axiom k → ∃ f : k → ℝ, is_ring_hom f ∧ bijective f ∧ ∀ x y : k, x < y → f x < f y := sorry

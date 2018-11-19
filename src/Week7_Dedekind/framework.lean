import data.rat

structure Dedekind_real :=
(carrier : set ℚ)
(nonemp : ∃ a, a ∈ carrier)
(nonrat : ∃ a, a ∉ carrier)
(down : ∀ p ∈ carrier, ∀ q, q < p → q ∈ carrier)
(nomax : ∀ p ∈ carrier, ∃ q ∈ carrier, p < q)

notation `ℝ` := Dedekind_real

instance : has_coe ℝ (set ℚ) := ⟨λ r, r.carrier⟩

namespace Dedekind_real

protected def lt (α β : ℝ) : Prop := (α : set ℚ) ⊂ β

-- notation typeclass
instance : has_lt ℝ := ⟨Dedekind_real.lt⟩

#check λ a b : ℝ, a < b -- I can use "<" notation now.

-- more definitions of stuff like addition go here in the namespace

end Dedekind_real

open Dedekind_real

-- questions about reals go here, outside the namespace

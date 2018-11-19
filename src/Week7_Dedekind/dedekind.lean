import data.rat data.set.basic order.bounds

structure dedekind_real :=
(carrier: set ℚ)
(nonemp: ∃ a, a ∈ carrier)
(nonrat: ∃ a, a ∉ carrier)
(down: ∀ p ∈ carrier, ∀ q, q < p → q ∈ carrier)
(init: ∀ p ∈ carrier, ∀ q ∉ carrier, p < q)


notation `ℝ` := dedekind_real
instance: has_coe ℝ (set ℚ) := ⟨λ r, r.carrier⟩

namespace dedekind_real

theorem eq_of_carrier_eq:
  ∀ {α β: dedekind_real}, α.carrier = β.carrier → α = β
| ⟨a, _, _, _, _⟩ ⟨b, _, _, _, _⟩ rfl := rfl

theorem carrier_inj {α β: dedekind_real}:
  α.carrier = β.carrier ↔ α = β :=
⟨eq_of_carrier_eq, λ h, congr_arg carrier h⟩

protected def le (α β: ℝ): Prop := (α: set ℚ) ⊆ β
instance: has_le ℝ := ⟨dedekind_real.le⟩

end dedekind_real

open dedekind_real

theorem Q_1a (α: ℝ) (r s: ℚ):
  r ∉ (α: set ℚ) → r < s → s ∉ (α: set ℚ) :=
λ hna hlt hsa, hna (α.down s hsa r hlt)

theorem Q_1b: linear_order ℝ := {
  le := dedekind_real.le,
  le_total :=
  λ α β, classical.or_iff_not_imp_left.2
    (λ h b hb, exists.elim (set.not_subset.1 h)
    (λ a ⟨ha, hnb⟩, or.elim (le_or_gt a b)
      (λ hle, false.elim (not_le_of_gt (β.init b hb a hnb) hle))
      (λ hgt, α.down a ha b hgt))),
  le_antisymm := λ α β h1 h2, eq_of_carrier_eq (set.subset.antisymm h1 h2),
  le_trans := λ α β γ h1 h2 c ha, h2 (h1 ha),
  le_refl := λ a c h, h
}

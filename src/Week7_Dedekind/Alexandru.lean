import data.rat
import data.set.basic
import order.bounds

open classical
/-import order.bounds
import data.rat

class linear_order (α : Type)

is a structure (in fact a class) which looks like this:

There's a function
le : α → α → Prop

with notation ≤ ( type with \le )

There is also lt : α → α → Prop with notation <
satisfying a < b ↔ (a ≤ b ∧ ¬ b ≤ a)

Axioms:

(le_refl : ∀ a : α, a ≤ a)
(le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
(le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)
(le_total : ∀ a b : α, a ≤ b ∨ b ≤ a)

And here are some definitions from order.bounds, valid
for α a total order:

def upper_bounds (s : set α) : set α := { x | ∀a ∈ s, a ≤ x }
def lower_bounds (s : set α) : set α := { x | ∀a ∈ s, x ≤ a }
def is_least (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ lower_bounds s
def is_greatest (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ upper_bounds s
def is_lub (s : set α) : α → Prop := is_least (upper_bounds s)
def is_glb (s : set α) : α → Prop := is_greatest (lower_bounds s)
-/

structure Dedekind_real :=
(carrier : set ℚ)
(nonemp : ∃ a, a ∈ carrier)
(nonrat : ∃ a, a ∉ carrier)
(down : ∀ p ∈ carrier, ∀ q, q ≤ p → q ∈ carrier)
(nomax : ∀ p ∈ carrier, ∃ q, q ∈ carrier ∧ p ≤ q ∧ p ≠ q)

notation `ℝ` := Dedekind_real

instance : has_coe ℝ (set ℚ) := ⟨λ r, r.carrier⟩

namespace Dedekind_real

protected def le (α β : ℝ) : Prop := (α : set ℚ) ⊆ β
protected def lt (α β : ℝ) : Prop := (α : set ℚ) ⊂ β

-- notation typeclass
instance : has_le ℝ := ⟨Dedekind_real.le⟩
instance : has_lt ℝ := ⟨Dedekind_real.lt⟩

def union_of_ne_b_r_set (S : set ℝ) (hne : ∃ s, s ∈ S) (hb : ∃ (b : ℝ), ∀ (s ∈ S), s ≤ b) : ℝ :=
⟨{x : ℚ | ∃ (s : ℝ), s ∈ S ∧ x ∈ (s : ℝ).carrier},
exists.elim hne (λ s hs, exists.elim s.nonemp (λ q hq, ⟨q, ⟨s, hs, hq⟩ ⟩ ) ),
exists.elim hb (λ b h, exists.elim b.nonrat (λ q hnq, ⟨q, (λ h0, hnq
(exists.elim h0 (λ s H, ( (h s) H.left ) H.right ) ) ) ⟩ )),
(λ p hp q hqp, exists.elim hp (λ s H, ⟨s, H.left, s.down p H.right q hqp⟩ ) ),
(λ p hp, exists.elim hp (λ s H, exists.elim (s.nomax p H.right) (λ r H0, ⟨r, ⟨s, H.left, H0.left ⟩,
H0.right.left, H0.right.right ⟩ ) ) ) ⟩

def arthm_mean (a b : ℚ) : ℚ := (a + b)/2

end Dedekind_real

open Dedekind_real

lemma bounded_by_non_elements : ∀ (α : ℝ) (x : ℚ),
x ∉ α.carrier ↔ (∀ (q ∈ α.carrier), q < x) := λ α x,
⟨(λ h q hq, classical.by_contradiction (λ hn, h (α.down q hq x (le_of_not_lt hn)))),
(λ h hx, (λ (h0 : x < x), not_lt_of_le (le_refl x) h0) (h x hx))⟩

lemma real_intro : ∀ {a b : ℝ}, a.carrier = b.carrier → a = b
| ⟨a, _, _, _, _⟩ ⟨b, _, _, _, _⟩ rfl := rfl

lemma le_intro : ∀ {a b : ℝ}, a.carrier ⊆ b.carrier → a ≤ b := λ a b h x hb, h hb

theorem eq_reals (a b : ℝ) : a = b ↔ a.carrier = b.carrier := ⟨λ hab, by rw hab,
real_intro⟩

theorem arthm_mean_bounded_q : ∀ (a b : ℚ), a < b → (a < arthm_mean a b ∧ arthm_mean a b < b) := λ a b hab,
⟨by calc a = a/2*2 : eq.symm (@div_mul_cancel _ _ a 2 (dec_trivial) )
... = a/2 + a/2 : mul_two (a/2)
... < a/2 + b/2 : (λ (h1 : (0 : ℚ) < 2), add_lt_add_left
( (div_lt_div_right h1).2 hab) (a/2) ) dec_trivial
... = (a + b)/2 : eq.symm (add_div a b 2),
by calc (a + b)/2 = a/2 + b/2 : add_div a b 2
... < b/2 + b/2 : (λ (h1 : (0 : ℚ) < 2), add_lt_add_right
( (div_lt_div_right h1).2 hab) (b/2) ) dec_trivial
... = b/2*2 : eq.symm (mul_two (b/2) )
... = b : (@div_mul_cancel _ _ b 2 (dec_trivial) ) ⟩

namespace Dedekind_real

def lt_rat_r (p : ℚ) : ℝ := ⟨{q | q < p}, ⟨p-1, trans_rel_left rat.has_lt.lt (lt_add_one (p-1) )
(sub_add_cancel p 1) ⟩, ⟨p+1, (λ h, (not_lt_of_lt (lt_add_one p) ) h) ⟩, (λ q hq r hrq, lt_of_le_of_lt hrq hq),
(λ q hq, ⟨ (q+p)/2, (arthm_mean_bounded_q q p hq).right, le_of_lt ( (arthm_mean_bounded_q q p hq).left),
ne_of_lt ( (arthm_mean_bounded_q q p hq).left) ⟩ ) ⟩

protected def add (α β : ℝ) : ℝ := ⟨{x | ∃ (a b : ℚ), a ∈ α.carrier ∧ b ∈ β.carrier ∧ x = a + b},
(exists.elim α.nonemp (λ a haα, exists.elim β.nonemp (λ b hbβ, ⟨a + b, ⟨a, b, haα, hbβ, rfl ⟩ ⟩ ) ) ), --nonemp
exists.elim α.nonrat (exists.elim β.nonrat (λ b hbβ a haα, ⟨a+b, not_exists.2 (λ a0,
not_exists.2 (λ b0 h, absurd (eq.symm h.right.right) (ne_of_lt (add_lt_add_of_lt_of_le
( ( bounded_by_non_elements α a ).1 haα a0 h.left )
( le_of_lt ( ( bounded_by_non_elements β b ).1 hbβ b0 h.right.left ) ) ) ) ) ) ⟩ ) ), --nonrat
(λ p padd q hqp, exists.elim padd (λ a hb, exists.elim hb (λ b h, ⟨ q-b, b,
(α.down a h.left (q-b) (trans_rel_left rat.le (add_le_add_right (trans_rel_left rat.le hqp h.right.right)
(-b) ) (add_sub_cancel a b) ) ),
h.right.left, eq.symm (sub_add_cancel q b) ⟩ ) ) ), --down
(λ p padd, exists.elim padd (λ a H, exists.elim H (λ b h, exists.elim (α.nomax a h.left)
(λ c hc, ⟨c + b, ⟨c, b, hc.left, h.right.left, rfl⟩, (trans_rel_right rat.le h.right.right
(add_le_add_right hc.right.left b) ), (λ hn, hc.right.right ( (add_right_inj b).1
(eq.trans (eq.symm h.right.right) hn) ) ) ⟩ ) ) ) ) ⟩ --nomax

protected def zero : ℝ := lt_rat_r 0

/-
protected def neg (α : ℝ) : ℝ := ⟨{p : ℚ | ∀ (q : ℚ), q ∈ α.carrier → p < -q},
exists.elim α.nonrat (λ r hr, ⟨-r, (λ q hq, neg_lt_neg_iff.2 ( (bounded_by_non_elements α r).1 hr q hq) ) ⟩ ),
(classical.by_contradiction (λ h, exists.elim α.nonemp (λ q0 hq0, (not_lt_of_lt (lt_add_one (-q0) ) )
(classical.not_exists_not.1 h (-q0 + 1) q0 hq0 ) ) ) ), _, _⟩
-/
instance : has_add ℝ := ⟨Dedekind_real.add⟩
instance : has_zero ℝ := ⟨Dedekind_real.zero⟩

end Dedekind_real



variables (a b : ℝ)
variable (h : ¬∃ (x : ℚ), x ∈ a.carrier ∧ x ∉ b.carrier)
variable (x : ℚ)
variable (hxa : x ∈ (↑a : set ℚ))

--#check (not_exists.1 h x : ¬(x ∈ ↑a ∧ x ∉ ↑b))

--⊢ ¬(x ∈ ↑a ∧ x ∉ ↑b)

lemma le_total_r : ∀ a b : ℝ, a ≤ b ∨ b ≤ a := λ a b, (em (∃ x, x ∈ a.carrier ∧ x ∉ b.carrier)).elim
(λ h, exists.elim h (λ x H, or.inr (λ y hyb, (a.down x H.left y
(le_of_lt ( (bounded_by_non_elements b x).1 H.right y hyb) ) ) ) ) )
(λ h, or.inl (λ x hxa, classical.not_not.1 (not_and.1 ((@not_exists ℚ _).1 h x) hxa) ) )

instance linear_order_r : linear_order ℝ := ⟨Dedekind_real.le, Dedekind_real.lt, (λ a x h, h),
(λ a b c hab hbc x hxa, hbc (hab hxa) ), ((λ a b, ⟨(λ hab, ⟨hab.left,(λ hba, hab.right (antisymm hab.left hba))⟩),
(λ h, ⟨h.left,(λ hab, h.right (((@set.subset.antisymm_iff _ ↑a ↑b).1) hab).right)⟩)⟩)), λ a b hab hba,
(eq_reals a b).2 ((set.ext_iff a.carrier b.carrier).2 (λ x, ⟨(λ hxa, hab hxa),(λ hxb, hba hxb)⟩)), le_total_r⟩

lemma union_is_bound (S : set ℝ) (hne : ∃ s, s ∈ S) (hb : ∃ (b : ℝ), ∀ (s ∈ S), s ≤ b) :
(union_of_ne_b_r_set S hne hb) ∈ upper_bounds S := λ s hs x hxs, ⟨s, hs, hxs⟩

theorem has_lub_property (S : set ℝ) (hne : ∃ s, s ∈ S) (hb : ∃ (b : ℝ), ∀ (s ∈ S), s ≤ b) :
(∃ (b : ℝ), is_lub S b) := ⟨union_of_ne_b_r_set S hne hb, ⟨(λ s hs x hxs, ⟨s, hs, hxs⟩),
(λ s hs x hx, exists.elim hx (λ sx hsx, hs sx hsx.left hsx.right ) ) ⟩ ⟩

theorem add_assoc_r (a b c : ℝ) : a + b + c = a + (b + c) := real_intro (set.ext (λ x,
⟨ (λ hx, exists.elim hx (λ ab hc, exists.elim hc (λ c hab, exists.elim hab.left (λ a hb, exists.elim hb
(λ b h, ⟨a, b+c, h.left, ⟨b, c, h.right.left, hab.right.left, rfl⟩, eq.trans hab.right.right (eq.trans
( (add_right_inj c).2 h.right.right) (add_assoc a b c) ) ⟩ ) ) ) ) ), -- left inclusion
(λ hx, exists.elim hx (λ a hbc, exists.elim hbc (λ bc hbc, exists.elim hbc.right.left (λ b hc, exists.elim hc
(λ c h, ⟨ a + b, c, ⟨a, b, hbc.left, h.left, rfl⟩ , h.right.left, eq.trans hbc.right.right (eq.trans
( (add_left_inj a).2 h.right.right) (eq.symm (add_assoc a b c) ) ) ⟩ ) ) ) ) ) ⟩ ) ) --right inclusion

theorem add_comm_r (a b : ℝ) : a + b = b + a := real_intro (set.ext (λ x,
⟨λ hx, exists.elim hx (λ a hb, exists.elim hb (λ b h, ⟨b, a, h.right.left, h.left,
eq.trans h.right.right (add_comm a b) ⟩ ) ),
λ hx, exists.elim hx (λ b ha, exists.elim ha (λ a h, ⟨a, b, h.right.left, h.left,
eq.trans h.right.right (add_comm b a)⟩  ) ) ⟩ ) )

theorem zero_add_r (α : ℝ) : α + 0 = α := real_intro (set.ext (λ x, ⟨ (λ hx, exists.elim hx (λ a h0,
exists.elim h0 (λ b h, α.down a h.left x (le_of_lt (by calc x = a + b : h.right.right
... < a + 0 : add_lt_add_of_le_of_lt (le_refl a) h.right.left
... = a : add_zero a) ) ) ) ), (λ hx, exists.elim (α.nomax x hx) (λ a h, ⟨a, x-a, h.left,
sub_lt_zero.2 (lt_of_le_of_ne h.right.left h.right.right), eq.symm (add_sub_cancel'_right a x) ⟩ ) ) ⟩ ) )

theorem add_zero_r (α : ℝ) : 0 + α = α := eq.trans (add_comm_r 0 α) (zero_add_r α)
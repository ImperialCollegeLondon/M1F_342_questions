import algebra.archimedean data.set.intervals order.conditionally_complete_lattice

namespace set

protected def dite (c : Prop) {α : Type*} (pos : c → set α) (neg : ¬c → set α) : set α :=
{ x | (∃ hc, x ∈ pos hc) ∨ (∃ hnc, x ∈ neg hnc) }

protected def ite (c : Prop) {α : Type*} (pos neg : set α) : set α :=
set.dite c (λ _, pos) (λ _, neg)

protected theorem dif_pos {c : Prop} (hc : c) {α : Type*} {pos neg} : (set.dite c pos neg : set α) = pos hc :=
ext $ λ z, ⟨λ hz, or.cases_on hz Exists.snd $ λ ⟨hnc, _⟩, absurd hc hnc,
λ hz, or.inl ⟨hc, hz⟩⟩

protected theorem dif_neg {c : Prop} (hnc : ¬c) {α : Type*} {pos neg} : (set.dite c pos neg : set α) = neg hnc :=
ext $ λ z, ⟨λ hz, or.cases_on hz (λ ⟨hc, _⟩, absurd hc hnc) Exists.snd,
λ hz, or.inr ⟨hnc, hz⟩⟩

protected theorem if_pos {c : Prop} (hc : c) {α : Type*} {t e} : (set.ite c t e : set α) = t :=
set.dif_pos hc

protected theorem if_neg {c : Prop} (hnc : ¬c) {α : Type*} {t e} : (set.ite c t e : set α) = e :=
set.dif_neg hnc

end set

open set lattice

structure real : Type :=
(carrier : set ℚ)
(exists_carrier : ∃ x, x ∈ carrier)
(exists_not_carrier : ∃ x, x ∉ carrier)
(mem_of_mem_of_le : ∀ q ∈ carrier, ∀ p ≤ q, p ∈ carrier)
(exists_lt_of_mem : ∀ q ∈ carrier, ∃ M ∈ carrier, q < M)

notation `ℝ` := real

namespace real

@[extensionality]
theorem ext : ∀ {c₁ c₂ : ℝ}, c₁.carrier = c₂.carrier → c₁ = c₂
| ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ rfl := rfl

protected def dite (c : Prop) (pos : c → ℝ) (neg : ¬c → ℝ) : ℝ :=
{ carrier := set.dite c (λ hc, (pos hc).1) (λ hnc, (neg hnc).1),
  exists_carrier := classical.by_cases
    (λ hc : c, by rw set.dif_pos hc; exact (pos hc).2)
    (λ hnc : ¬c, by rw set.dif_neg hnc; exact (neg hnc).2),
  exists_not_carrier := classical.by_cases
    (λ hc : c, by rw set.dif_pos hc; exact (pos hc).3)
    (λ hnc : ¬c, by rw set.dif_neg hnc; exact (neg hnc).3),
  mem_of_mem_of_le := classical.by_cases
    (λ hc : c, by rw set.dif_pos hc; exact (pos hc).4)
    (λ hnc : ¬c, by rw set.dif_neg hnc; exact (neg hnc).4),
  exists_lt_of_mem := classical.by_cases
    (λ hc : c, by rw set.dif_pos hc; exact (pos hc).5)
    (λ hnc : ¬c, by rw set.dif_neg hnc; exact (neg hnc).5) }

protected def ite (c : Prop) (pos neg : ℝ) : ℝ :=
real.dite c (λ _, pos) (λ _, neg)

protected theorem dif_pos {c : Prop} (hc : c) {pos neg} : real.dite c pos neg = pos hc :=
ext $ set.dif_pos hc

protected theorem dif_neg {c : Prop} (hnc : ¬c) {pos neg} : real.dite c pos neg = neg hnc :=
ext $ set.dif_neg hnc

protected theorem if_pos {c : Prop} (hc : c) {t e} : real.ite c t e = t :=
real.dif_pos hc

protected theorem if_neg {c : Prop} (hnc : ¬c) {t e} : real.ite c t e = e :=
real.dif_neg hnc

def of_rat (r : ℚ) : ℝ :=
⟨Iio r, ⟨r-1, sub_one_lt r⟩, ⟨r, lt_irrefl r⟩,
λ q hqr p hpq, lt_of_le_of_lt hpq hqr,
λ q hqr, ⟨q/2+r/2,
calc  q/2+r/2 < r/2+r/2 : add_lt_add_right (div_lt_div_of_lt_of_pos hqr two_pos) _
... = r : add_halves r,
calc  q = q/2+q/2 : (add_halves q).symm
... < q/2+r/2 : add_lt_add_left (div_lt_div_of_lt_of_pos hqr two_pos) _⟩⟩

instance : has_mem ℚ ℝ :=
⟨λ r c, r ∈ c.carrier⟩

theorem lt_of_mem_of_not_mem (c : ℝ) {p q : ℚ}
  (H1 : p ∈ c) (H2 : q ∉ c) : p < q :=
lt_of_not_ge $ mt (c.4 _ H1 _) H2

protected theorem le_total (c₁ c₂ : ℝ) : c₁.1 ⊆ c₂.1 ∨ c₂.1 ⊆ c₁.1 :=
classical.or_iff_not_imp_left.2 $ λ hc q hq2,
  let ⟨r, hr1, hr2⟩ := not_subset.1 hc in
  c₁.4 r hr1 _ $ le_of_lt $ lt_of_mem_of_not_mem c₂ hq2 hr2

protected def max (r₁ r₂ : ℝ) : ℝ :=
real.ite (r₁.1 ⊆ r₂.1) r₂ r₁

protected def min (r₁ r₂ : ℝ) : ℝ :=
real.ite (r₁.1 ⊆ r₂.1) r₁ r₂

protected def Sup (S : set ℝ) : ℝ :=
real.dite ((∃ r, r ∈ S) ∧ (∃ M : ℝ, ∀ r ∈ S, carrier r ⊆ M.1))
(λ hc, { carrier :=  ⋃ r ∈ S, carrier r,
  exists_carrier := let ⟨⟨r, hrs⟩, _⟩ := hc, ⟨q, hqr⟩ := r.2 in
    ⟨q, mem_bUnion hrs hqr⟩,
  exists_not_carrier := let ⟨_, M, HM⟩ := hc, ⟨q, hqM⟩ := M.3 in
    ⟨q, mt (λ H, bUnion_subset HM H) hqM⟩,
  mem_of_mem_of_le := λ q hq p hpq, let ⟨r, hrs, hqr⟩ := mem_bUnion_iff.1 hq in
    mem_bUnion hrs (r.4 q hqr _ hpq),
  exists_lt_of_mem := λ q hq, let ⟨r, hrs, hqr⟩ := mem_bUnion_iff.1 hq,
    ⟨M, HMr, hqM⟩ := r.5 q hqr in ⟨M, mem_bUnion hrs HMr, hqM⟩ })
(λ _, of_rat 0)

protected def Inf (S : set ℝ) : ℝ :=
real.Sup $ { m | ∀ r ∈ S, m.1 ⊆ carrier r }

instance conditionally_complete_linear_order : conditionally_complete_linear_order ℝ :=
{ le_total := real.le_total,
  sup := real.max,
  le_sup_left := λ r₁ r₂, show r₁.1 ⊆ (real.ite (r₁.1 ⊆ r₂.1) r₂ r₁).1, from classical.by_cases
    (λ h : r₁.1 ⊆ r₂.1, by rwa real.if_pos h) (λ h, by rw real.if_neg h),
  le_sup_right := λ r₁ r₂, show r₂.1 ⊆ (real.ite (r₁.1 ⊆ r₂.1) r₂ r₁).1, from classical.by_cases
    (λ h : r₁.1 ⊆ r₂.1, by rw real.if_pos h) (λ h, by rwa real.if_neg h; exact (real.le_total r₁ r₂).resolve_left h),
  sup_le := λ r₁ r₂ r hr1 hr2, show (real.ite (r₁.1 ⊆ r₂.1) r₂ r₁).1 ⊆ r.1, from classical.by_cases
    (λ h : r₁.1 ⊆ r₂.1, by rwa real.if_pos h) (λ h, by rwa real.if_neg h),
  inf := real.min,
  inf_le_left := λ r₁ r₂, show (real.ite (r₁.1 ⊆ r₂.1) r₁ r₂).1 ⊆ r₁.1, from classical.by_cases
    (λ h : r₁.1 ⊆ r₂.1, by rw real.if_pos h) (λ h, by rw real.if_neg h; exact (real.le_total r₁ r₂).resolve_left h),
  inf_le_right := λ r₁ r₂, show (real.ite (r₁.1 ⊆ r₂.1) r₁ r₂).1 ⊆ r₂.1, from classical.by_cases
    (λ h : r₁.1 ⊆ r₂.1, by rwa real.if_pos h) (λ h, by rw real.if_neg h),
  le_inf := λ r r₁ r₂ hr1 hr2, show r.1 ⊆ (real.ite (r₁.1 ⊆ r₂.1) r₁ r₂).1, from classical.by_cases
    (λ h : r₁.1 ⊆ r₂.1, by rwa real.if_pos h) (λ h, by rwa real.if_neg h),
  Sup := real.Sup,
  le_cSup := λ S r hS hrS, show r.1 ⊆ set.dite _ _ _,
    by rw set.dif_pos; [exact subset_bUnion_of_mem hrS, exact ⟨⟨r, hrS⟩, hS⟩],
  cSup_le := λ S r HS hr, show set.dite _ _ _ ⊆ r.1,
    by rw set.dif_pos; [exact bUnion_subset hr, exact ⟨exists_mem_of_ne_empty HS, r, hr⟩],
  cInf_le := λ S r HS hrS, show set.dite _ _ _ ⊆ _,
    by rw set.dif_pos; [exact bUnion_subset (λ m hm, hm r hrS), exact ⟨HS, r, λ m hm, hm r hrS⟩],
  le_cInf := λ S r HS hr, let ⟨s, hs⟩ := exists_mem_of_ne_empty HS in show r.1 ⊆ set.dite _ _ _,
    by rw set.dif_pos; [exact subset_bUnion_of_mem hr, exact ⟨⟨r, hr⟩, s, λ m hm, hm s hs⟩],
  Inf := real.Inf,
  .. partial_order.lift _ $ λ _ _, real.ext}

theorem of_rat_lt_iff (q : ℚ) (r : ℝ) : of_rat q < r ↔ q ∈ r :=
⟨λ hqr, let ⟨p, hpr, hpq⟩ := not_subset.1 hqr.2 in mem_of_mem_of_le _ p hpr _ (le_of_not_lt hpq),
λ hqr, ⟨λ p hpq, mem_of_mem_of_le _ q hqr _ (le_of_lt hpq),
λ hrq, lt_irrefl q $ hrq hqr⟩⟩

theorem le_of_rat_iff (q : ℚ) (r : ℝ) : r ≤ of_rat q ↔ q ∉ r :=
⟨λ hrq, mt (of_rat_lt_iff _ _).2 (not_lt_of_le hrq), λ hqr, le_of_not_lt $ mt (of_rat_lt_iff _ _).1 hqr⟩

def of_rat_embed : ((≤) : ℚ → ℚ → Prop) ≼o ((≤) : ℝ → ℝ → Prop) :=
{ to_fun := of_rat,
  inj := λ q₁ q₂ hq, le_antisymm
    (le_of_not_lt $ λ hq21 : q₂ ∈ of_rat q₁, lt_irrefl q₂ $ by rwa hq at hq21)
    (le_of_not_lt $ λ hq12 : q₁ ∈ of_rat q₂, lt_irrefl q₁ $ by rwa ← hq at hq12),
  ord := λ q₁ q₂, ⟨λ hq12, le_of_not_lt $ λ hq21, not_lt_of_le hq12 ((of_rat_lt_iff _ _).1 hq21),
    λ hq21, le_of_not_lt $ λ hq12, not_lt_of_le hq21 ((of_rat_lt_iff _ _).2 hq12)⟩ }

theorem of_rat_le_of_rat (q₁ q₂) : of_rat q₁ ≤ of_rat q₂ ↔ q₁ ≤ q₂ :=
(@order_embedding.ord _ _ _ _ of_rat_embed q₁ q₂).symm

theorem of_rat_lt_of_rat (q₁ q₂) : of_rat q₁ < of_rat q₂ ↔ q₁ < q₂ :=
of_rat_lt_iff _ _

theorem exists_rat_btwn_add (q : ℚ) (r) (hq : 0 < q) : ∃ m, of_rat m < r ∧ r < of_rat (m + q) :=
suffices ∀ (q:ℚ) (r:ℝ) (hq:q>0), ∃ m, m ∈ r ∧ m+q ∉ r,
from let ⟨m, hmr, hmqr⟩ := this (q/2) r (half_pos hq) in ⟨m, (of_rat_lt_iff _ _).2 hmr,
  lt_of_le_of_lt ((le_of_rat_iff _ _).2 hmqr) ((of_rat_lt_of_rat _ _).2 (add_lt_add_left (half_lt_self hq) _))⟩,
λ q r hq, let ⟨lo, hlo⟩ := r.2, ⟨hi, hhi⟩ := r.3 in
have ∀ n : ℕ, ∃ m, m ∈ r ∧ m + (hi - lo) / 2^n ∉ r,
  from λ n, nat.rec_on n ⟨lo, hlo, by rwa [pow_zero, div_one, add_sub_cancel'_right]⟩ $ λ n ⟨m, hmr, hmnr⟩,
  classical.by_cases (assume h : m + (hi - lo) / 2 ^ n.succ ∈ r,
    ⟨_, h, by rwa [add_assoc, pow_succ', ← div_div_eq_div_mul, add_halves]⟩)
  (λ h, ⟨m, hmr, h⟩),
let ⟨n, hn⟩ := pow_unbounded_of_gt_one ((hi - lo) / q) two_gt_one,
  ⟨m, hmr, hmnr⟩ := this n in
⟨m, hmr, mt (λ hmqr, r.4 _ hmqr (m + (hi-lo)/2^n) $ add_le_add_left
  (mul_div_cancel' q (ne_of_gt (pow_pos two_pos n)) ▸
    div_mul_div_cancel (hi-lo) (ne_of_gt (pow_pos two_pos n)) (ne_of_gt hq) ▸
    mul_le_mul_of_nonneg_right (le_of_lt hn) (div_nonneg (le_of_lt hq) (pow_pos two_pos n)))
  m) hmnr⟩

protected theorem exists_rat_btwn {r₁ r₂ : ℝ} (H : r₁ < r₂) :
  ∃ q, r₁ < of_rat q ∧ of_rat q < r₂ :=
let ⟨q, hq2, hq1⟩ := not_subset.1 H.2, ⟨q', hq2', hqq'⟩ := r₂.5 q hq2 in
⟨q', lt_of_le_of_lt ((le_of_rat_iff _ _).2 hq1) ((of_rat_lt_of_rat _ _).2 hqq'), (of_rat_lt_iff _ _).2 hq2'⟩

protected def add (r₁ r₂ : ℝ) : ℝ :=
{ carrier := (λ p:ℚ×ℚ, p.1+p.2) '' r₁.1.prod r₂.1,
  exists_carrier := let ⟨q₁, hq₁⟩ := r₁.2, ⟨q₂, hq₂⟩ := r₂.2 in
    ⟨q₁+q₂, @mem_image_of_mem _ _ (λ p:ℚ×ℚ, p.1+p.2) (q₁, q₂) (r₁.1.prod r₂.1) ⟨hq₁, hq₂⟩⟩,
  exists_not_carrier := let ⟨q₁, hq₁⟩ := r₁.3, ⟨q₂, hq₂⟩ := r₂.3 in
    ⟨q₁+q₂, λ ⟨⟨p₁,p₂⟩,⟨⟨hp₁,hp₂⟩,hp⟩⟩, absurd hp $ ne_of_lt $
      add_lt_add (lt_of_mem_of_not_mem r₁ hp₁ hq₁) (lt_of_mem_of_not_mem r₂ hp₂ hq₂)⟩,
  mem_of_mem_of_le := λ q ⟨⟨p₁,p₂⟩,⟨⟨hp₁,hp₂⟩,hp⟩⟩ p hpq,
    ⟨(p₁,p₂-(q-p)), ⟨hp₁, r₂.4 p₂ hp₂ _ (sub_le_self _ $ sub_nonneg_of_le hpq)⟩,
      by simp only [add_sub, (show p₁ + p₂ = q, from hp), sub_sub_cancel]⟩,
  exists_lt_of_mem := λ q ⟨⟨p₁,p₂⟩,⟨⟨hp₁,hp₂⟩,hp⟩⟩,
    let ⟨M₁,HM₁,hpM₁⟩ := r₁.5 p₁ hp₁, ⟨M₂,HM₂,hpM₂⟩ := r₂.5 p₂ hp₂ in
    ⟨M₁+M₂, @mem_image_of_mem _ _ (λ p:ℚ×ℚ, p.1+p.2) (M₁, M₂) (r₁.1.prod r₂.1) ⟨HM₁, HM₂⟩,
      hp ▸ add_lt_add hpM₁ hpM₂⟩ }

theorem rat_dense {r₁ r₂ : ℝ} (h : ∀ q, of_rat q < r₁ ↔ of_rat q < r₂) : r₁ = r₂ :=
ext $ set.ext $ λ q, (of_rat_lt_iff _ _).symm.trans $ (h q).trans $ of_rat_lt_iff _ _

theorem of_rat_lt_add_iff (q) (r₁ r₂) : of_rat q < real.add r₁ r₂ ↔
  ∃ q₁ ∈ r₁, ∃ q₂ ∈ r₂, q₁ + q₂ = q :=
(of_rat_lt_iff _ _).trans ⟨λ ⟨⟨x,y⟩,⟨hx,hy⟩,hxy⟩, ⟨x,hx,y,hy,hxy⟩, λ ⟨x,hx,y,hy,hxy⟩, ⟨⟨x,y⟩,⟨hx,hy⟩,hxy⟩⟩

protected def neg (r : ℝ) : ℝ :=
{ carrier := { q | r < of_rat (-q) },
  exists_carrier := let ⟨q, hqr⟩ := r.3 in ⟨-(q+1), show r < of_rat (- -(q+1)),
    from lt_of_not_ge $ mt (by rw _root_.neg_neg; exact λ hq1r,
      (of_rat_lt_iff _ _).1 (lt_of_lt_of_le ((of_rat_lt_of_rat _ _).2 (lt_add_one q)) hq1r)) hqr⟩,
  exists_not_carrier := let ⟨q, hqr⟩ := r.2 in ⟨-q,
    show ¬ r < of_rat (- -q), from (neg_neg q).symm ▸ not_lt_of_lt ((of_rat_lt_iff _ _).2 hqr)⟩,
  mem_of_mem_of_le := λ q hrq p hpq, lt_of_lt_of_le hrq $ (of_rat_le_of_rat _ _).2 (neg_le_neg hpq),
  exists_lt_of_mem := λ q hrq, let ⟨x, hrx, hxq⟩ := real.exists_rat_btwn hrq in
    ⟨-x, show r < of_rat (- -x), from (neg_neg x).symm ▸ hrx, lt_neg_of_lt_neg $ (of_rat_lt_of_rat _ _).1 hxq⟩ }

instance : add_comm_group ℝ :=
{ add := real.add,
  zero := of_rat 0,
  neg := real.neg,
  add_assoc := λ _ _ _, ext $ le_antisymm
    (image_subset_iff.2 $ λ ⟨xy,z⟩ ⟨⟨⟨x,y⟩,⟨hx,hy⟩,hxy⟩,hz⟩, ⟨(x,y+z),⟨hx,⟨(y,z),⟨hy,hz⟩,rfl⟩⟩,
      by simp only at hxy; exact hxy ▸ (add_assoc _ _ _).symm⟩)
    (image_subset_iff.2 $ λ ⟨x,yz⟩ ⟨hx,⟨⟨y,z⟩,⟨hy,hz⟩,hyz⟩⟩, ⟨(x+y,z),⟨⟨(x,y),⟨hx,hy⟩,rfl⟩,hz⟩,
      by simp only at hyz; exact hyz ▸ add_assoc _ _ _⟩),
  zero_add := λ r, rat_dense $ λ q, (of_rat_lt_add_iff _ _ _).trans
    ⟨λ ⟨q₁,hq₁,q₂,hq₂,hq⟩, hq ▸ (of_rat_lt_iff _ _).2 (r.4 q₂ hq₂ _ $ add_le_of_nonpos_of_le (le_of_lt hq₁) (le_refl _)),
    λ hqr, let ⟨M, HMr, hqM⟩ := r.5 q ((of_rat_lt_iff _ _).1 hqr) in ⟨q-M, sub_neg_of_lt hqM, M, HMr, sub_add_cancel _ _⟩⟩,
  add_zero := λ r, rat_dense $ λ q, (of_rat_lt_add_iff _ _ _).trans
    ⟨λ ⟨q₁,hq₁,q₂,hq₂,hq⟩, hq ▸ (of_rat_lt_iff _ _).2 (r.4 q₁ hq₁ _ $ add_le_of_le_of_nonpos (le_refl _) (le_of_lt hq₂)),
    λ hqr, let ⟨M, HMr, hqM⟩ := r.5 q ((of_rat_lt_iff _ _).1 hqr) in ⟨M, HMr, q-M, sub_neg_of_lt hqM, add_sub_cancel'_right _ _⟩⟩,
  add_left_neg := λ r, rat_dense $ λ q, (of_rat_lt_add_iff _ _ _).trans
    ⟨λ ⟨q₁,hq₁,q₂,hq₂,hq⟩, hq ▸ (of_rat_lt_iff _ _).2 (show q₁ + q₂ < 0,
      from add_comm q₂ q₁ ▸ (sub_neg_eq_add q₂ q₁) ▸ sub_neg_of_lt ((of_rat_lt_of_rat _ _).1 $
        lt_trans ((of_rat_lt_iff _ _).2 hq₂) hq₁)),
    λ hq, let ⟨m, hmr, hrmq⟩ := exists_rat_btwn_add (-q) r (neg_pos.2 ((of_rat_lt_of_rat _ _).1 hq)) in
    ⟨-(m-q), show r < of_rat (- -(m-q)), from (neg_neg (m-q)).symm ▸ hrmq,
    m, ((of_rat_lt_iff _ _).1 hmr), by rw [neg_sub, sub_add_cancel]⟩⟩,
  add_comm := λ _ _, ext $ le_antisymm
    (image_subset_iff.2 $ λ ⟨x,y⟩ ⟨hx,hy⟩, ⟨(y,x), ⟨hy,hx⟩, add_comm y x⟩)
    (image_subset_iff.2 $ λ ⟨x,y⟩ ⟨hx,hy⟩, ⟨(y,x), ⟨hy,hx⟩, add_comm y x⟩),
  .. real.conditionally_complete_linear_order }

def sign (r : ℝ) : ℝ :=
real.ite (r < of_rat 0) (of_rat (-1))
  (real.ite (of_rat 0 < r) (of_rat 1) (of_rat 0))

protected def abs (r : ℝ) : ℝ :=
r ⊔ -r

end real 

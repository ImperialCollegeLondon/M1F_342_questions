--Rohan and Enrico
import data.set
namespace prop_logic

inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)
open fml

infixr ` →' `:50 := imp
local notation ` ¬' ` := fml.not

--CAN I MAKE THIS A FUNCTION INTO PROP INSTEAD OF TYPE????
inductive thm : fml → Prop
| axk (p q) : thm (p →' q →' p)
| axs (p q r) : thm $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axn (p q) : thm $ (¬'q →' ¬'p) →' p →' q
| mp (p q) : thm p → thm (p →' q) → thm q

lemma p_of_p_of_p_of_p_of_p (p : fml) : thm ((p →' (p →' p)) →' (p →' p)) :=
thm.mp (p →' ((p →' p) →' p)) ((p →' (p →' p)) →' (p →' p)) (thm.axk p (p →' p)) (thm.axs p (p →' p) p)

lemma p_of_p (p : fml) : thm (p →' p) := 
thm.mp (p →' p →' p) (p →' p) (thm.axk p p) (p_of_p_of_p_of_p_of_p p)

lemma p_of_p' (p : fml) : thm (p →' p) := 
begin
    have lemma1 := p_of_p_of_p_of_p_of_p p,
    have lemma2 := thm.axk p p,
    exact thm.mp _ _ lemma2 lemma1,
end

inductive consequence (G : set fml) : fml → Prop
| axk (p q) : consequence (p →' q →' p)
| axs (p q r) : consequence $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axn (p q) : consequence $ (¬'q →' ¬'p) →' p →' q
| mp (p q) : consequence p → consequence (p →' q) → consequence q
| of_G (g ∈ G) : consequence g 

lemma consequence_of_thm (f : fml) (H : thm f) (G : set fml) : consequence G f :=
begin
  induction H,
  exact consequence.axk G H_p H_q,
  exact consequence.axs G H_p H_q H_r,
  exact consequence.axn G H_p H_q,
  exact consequence.mp H_p H_q H_ih_a H_ih_a_1,
end

lemma thm_of_consequence_null (f : fml) (H : consequence ∅ f) : thm f :=
begin
  induction H,
  exact thm.axk H_p H_q,
  exact thm.axs H_p H_q H_r,
  exact thm.axn H_p H_q,
  exact thm.mp H_p H_q H_ih_a H_ih_a_1,
  rw set.mem_empty_eq at H_H,
  contradiction,
end

theorem deduction (G : set fml) (p q : fml) (H : consequence (G ∪ {p}) q) : consequence G (p →' q) :=
begin
  induction H,
  have H1 := consequence.axk G H_p H_q,
  have H2 := consequence.axk G (H_p →' H_q →' H_p) p,
  exact consequence.mp _ _ H1 H2,
  have H6 := consequence.axs G H_p H_q H_r,
  have H7 := consequence.axk G ((H_p →' H_q →' H_r) →' (H_p →' H_q) →' H_p →' H_r) p,
  exact consequence.mp _ _ H6 H7,
  have H8 := consequence.axn G H_p H_q,
  have H9 := consequence.axk G ((¬' H_q →' ¬' H_p) →' H_p →' H_q) p,
  exact consequence.mp _ _ H8 H9,
  have H3 := consequence.axs G p H_p H_q,
  have H4 := consequence.mp _ _ H_ih_a_1 H3,
  exact consequence.mp _ _ H_ih_a H4,
  rw set.mem_union at H_H,
  cases H_H,
    have H51 := consequence.of_G H_g H_H,
    have H52 := consequence.axk G H_g p,
    exact consequence.mp _ _ H51 H52,
  rw set.mem_singleton_iff at H_H,
  rw H_H,
  exact consequence_of_thm _ (p_of_p p) G,
end

lemma part1 (p : fml) : consequence {¬' (¬' p)} p :=
begin
  have H1 := consequence.axk {¬' (¬' p)} p p,
  have H2 := consequence.axk {¬' (¬' p)} (¬' (¬' p)) (¬' (¬' (p →' p →' p))),
  have H3 := consequence.of_G (¬' (¬' p))(set.mem_singleton (¬' (¬' p))),
  have H4 := consequence.mp _ _ H3 H2,
  have H5 := consequence.axn {¬' (¬' p)} (¬' p) (¬' (p →' p →' p)),
  have H6 := consequence.mp _ _ H4 H5,
  have H7 := consequence.axn {¬' (¬' p)} (p →' p →' p) p,
  have H8 := consequence.mp _ _ H6 H7,
  exact consequence.mp _ _ H1 H8,
end

lemma p_of_not_not_p (p : fml) : thm ((¬' (¬' p)) →' p) :=
begin
  have H1 := deduction ∅ (¬' (¬' p)) p,
  rw set.empty_union at H1,
  have H2 := H1 (part1 p),
  exact thm_of_consequence_null (¬' (¬' p) →' p) H2,
end

theorem not_not_p_of_p (p : fml) : thm (p →' (¬' (¬' p))) :=
begin
  have H1 := thm.axn p (¬' (¬' p)),
  have H2 := p_of_not_not_p (¬' p),
  exact thm.mp _ _ H2 H1,
end

end prop_logic
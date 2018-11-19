inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := imp -- right associative

notation `¬' ` := fml.not


inductive prf : fml → Type
| axk {p q} : prf (p →' q →' p)
| axs {p q r} : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX {p q} : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

open prf

lemma p_of_p_of_p_of_q (p q : fml) : prf $ (p →' q) →' (p →' p) :=
begin
  apply mp (p →' q →' p) ((p →' q) →' p →' p) (axk p q),
  exact axs p q p
end

lemma p_of_p_of_p_of_q' (p q : fml) : prf $ (p →' q) →' (p →' p) :=
mp (p →' q →' p) ((p →' q) →' p →' p) (axk p q) (axs p q p)

lemma p_of_p_of_p_of_q'' (p q : fml) : prf $ (p →' q) →' (p →' p) :=
mp axk axs
-- question 6a on Britnell sheet
theorem p_of_p (p : fml) : prf $ p →' p :=
begin
  exact mp (p →' p →' p) (p →' p) (axk p p) (p_of_p_of_p_of_q p (p →' p)), 
end
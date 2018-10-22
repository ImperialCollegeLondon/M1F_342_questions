inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:40 := fml.not

inductive prf : fml → Type
| axk (p q) : prf (p →' q →' p)
| axs (p q r) : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX (p q) : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf (p →' q) → prf p → prf q -- bracket change

open prf

-- example usage:
/-
lemma p_of_p_of_p_of_q (p q : fml) : prf $ (p →' q) →' (p →' p) :=
begin
  apply mp (axs p q p),
  exact (axk p q)
end
-/

lemma Q6a (p : fml) : prf $ p →' p := sorry

theorem Q6b (p : fml) : prf $ p →' ¬' ¬' p := sorry
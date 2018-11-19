/- Question 6 on John Britnell's handout
   for M1F group project on 18/10/18.
   Formalised by Kevin Buzzard, with many
   thanks to Gabriel Ebner for showing him
   how to do it. 
-/

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

/-
-- example usage:

lemma p_of_p_of_p_of_q (p q : fml) : prf $ (p →' q) →' (p →' p) :=
begin
  apply mp (axs p q p),
  exact (axk p q)
end

-- or just

lemma p_of_p_of_p_of_q' (p q : fml) : prf $ (p →' q) →' (p →' p) :=
mp (axs p q p) (axk p q)
-/

theorem transitivity {p q r : fml} (HPQ : prf $ p →' q) (HQR : prf $ q →' r) : prf $ p →' r :=
begin
  have HQRPQR := axk (q →' r) p,
  have HPQR := mp HQRPQR HQR,
  have HPQPR := mp (axs p q r ) HPQR,
  exact mp HPQPR HPQ,
end

lemma Q6a (p : fml) : prf $ p →' p :=
begin
  have r : fml, exact p,
  have q := r →' p,
  have HPQP := axk p (r →' p),
  have HPQPP := mp (axs p (r →' p) p) HPQP,
  apply mp HPQPP,
  have HPRP := axk p r,
  -- How do I change (p →' q) into (p →' r →' p)?
  exact HPRP,
end

lemma contra_twice (p : fml) : prf $ ((¬' ¬' ¬' ¬' p) →' (¬' ¬' p)) →' ((¬' ¬' p) →' p) :=
begin
  have H1 := axX (¬' p) (¬' ¬' ¬' p),
  have H2 := axX (¬' ¬' p) p,
  exact transitivity H1 H2,
end

lemma PPQPQ (p q : fml) (HPPQ : prf (p →' (p →' q))) : prf $ (p →' q) :=
begin
  apply mp (mp (axs p p q) HPPQ),
  exact Q6a p,
end

lemma nnPP (p : fml) : prf $ (¬' ¬' p) →' p :=
begin
  have H1 := axk (¬' ¬' p) (¬' ¬' ¬' ¬' p),
  have H2 := transitivity H1 (contra_twice p),
  exact PPQPQ (¬' ¬' p) p H2,
end

theorem Q6b (p : fml) : prf $ p →' ¬' ¬' p :=
begin
  have H1 := nnPP (¬' p),
  exact mp (axX p (¬' ¬' p)) H1,
end

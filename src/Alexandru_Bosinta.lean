inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := fml.imp -- right associative

prefix `¬' `:40 := fml.not

inductive prf : fml → Type
| axk (p q) : prf (p →' q →' p)
| axs (p q r) : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX (p q) : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf (p →' q) → prf p → prf q -- bracket change

open prf

-- example usage:
--lemma p_of_p_of_p_of_q (p q : fml) : prf $ (p →' q) →' (p →' p) :=
--begin
 -- apply mp (axs p q p),
  --exact (axk p q)
--end

lemma Q6a (p : fml) : prf $ p →' p := 
begin
  have H1 : (prf $ (p →' (p →' p) →' p)) := by exact axk p (p →' p),
  have H2 : (prf $ (p →' (p →' p) →' p) →' (p →' p →' p) →' p →' p) := by exact axs p (p →' p) p,
  have H3 : (prf $ ((p →' p →' p) →' p →' p)) := by exact mp H2 H1,
  exact mp H3 (axk p p)
end

-- Proof of transitivity of implication sign (→'):

lemma transit (p q r : fml) (hpq : prf $ p →' q) (hqr : prf $ q →' r) : prf $ p →' r :=
begin
  have H1 : (prf $ (q →' r) →' p →' (q →' r)) := by exact axk (q →' r) p,
  have H2 : (prf $ p →' q →' r) := by exact mp H1 hqr,
  have H3 : (prf $ (p →' q) →' p →' r) := by exact mp (axs p q r) H2, 
  exact mp H3 hpq
end 

-- proof of Q6b starts here: Lemmas L1 to L16 are in the logical order. 

lemma L1 (p q : fml) : prf $ (¬' p) →' (¬' q) →' (¬' p) :=  
begin
  exact axk (¬' p) (¬' q)
end

lemma L2 (p q : fml) : prf $ (¬' p) →' p →' q :=
begin
  exact transit (¬' p) ((¬' q) →' (¬' p)) (p →' q) (L1 p q) (axX p q) 
end

lemma L3 (p q : fml) : prf $ (¬' p) →' p →' (¬' q) :=
begin
  exact L2 p (¬' q)
end

lemma L4 (p q : fml) : prf $ ((¬' p) →' p →' (¬' q)) →' ((¬' p) →' p) →' (¬' p) →' (¬' q) :=
begin
  exact axs (¬' p) p (¬' q)
end

lemma L5 (p q : fml) : prf $ ((¬' p) →' p) →' (¬' p) →' (¬' q) :=
begin
  exact mp (L4 p q) (L3 p q) 
end

lemma L6 (p q : fml) : prf $ ((¬' p) →' p) →' q →' p :=
begin
  exact transit ((¬' p) →' p) ((¬' p) →' (¬' q)) (q →' p) (L5 p q) (axX q p)
end

lemma L7 (p : fml) : prf $ ((¬' p) →' p) →' ((¬' p) →' p) →' p :=
begin
  exact L6 p ((¬' p) →' p)
end

lemma L8 (p : fml) : prf $ (((¬' p) →' p) →' ((¬' p) →' p) →' p) →' (((¬' p) →' p) →' ((¬' p) →' p)) →' ((¬' p) →' p) →' p :=
begin
  exact (axs ((¬' p) →' p) ((¬' p) →' p) p)
end

lemma L9 (p : fml) : prf $ (((¬' p) →' p) →' ((¬' p) →' p)) →' ((¬' p) →' p) →' p := 
begin
  exact mp (L8 p) (L7 p)
end

lemma L10 (p : fml) : prf $ ((¬' p) →' p) →' p := 
begin
  exact mp (L9 p) (Q6a ((¬' p) →' p))
end

lemma L11 (p : fml) : prf $ (¬' ¬' p) →' ((¬' p) →' (¬' ¬' p)) := 
begin
  exact axk (¬' ¬' p) (¬' p)
end

lemma L12 (p : fml) : prf $ ((¬' p) →' (¬' ¬' p)) →' ((¬' p) →' p) :=
begin
  exact axX (¬' p) p,
end

lemma L13 (p : fml) : prf $ (¬' ¬' p) →' (¬' p) →' p :=
begin
  exact transit (¬' ¬' p) ((¬' p) →' (¬' ¬' p)) ((¬' p) →' p) (L11 p) (L12 p)
end

lemma L14 (p : fml) : prf $ (¬' ¬' p) →' p :=
begin
  exact transit (¬' ¬' p) ((¬' p) →' p) p (L13 p) (L10 p)
end

lemma L15 (p : fml) : prf $ (¬' ¬' ¬'p) →' (¬' p) :=
begin
  exact L14 (¬' p)
end

lemma L16 (p : fml) : prf $ ((¬' ¬' ¬'p) →' (¬' p)) →' p →' (¬' ¬' p) :=
begin
  exact axX p (¬' ¬' p)
end

theorem Q6b (p : fml) : prf $ p →' (¬' ¬' p) := 
begin
  exact mp (L16 p) (L15 p),
end
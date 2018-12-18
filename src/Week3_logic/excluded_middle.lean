-- TODO -- post this on M1F blackboard and on Xena blackboard
-- No -- put it on M1F example class questions github site
/-
   Equivalent formulations of the law of the excluded middle.

   Dr Britnell's axioms were:

   1) P → (Q → P)
   2) (¬ Q → ¬ P) → (P → Q) 
   3) (P → (Q → R)) → ((P → Q) → (P → R))

   Here I formalise the assertion that the second axiom is
   equivalent to the so-called "law of the excluded middle", that
   not not P implies P.
-/

inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

-- namespace fml -- haven't defined things like and and iff

open fml

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:40 := fml.not

inductive prf : fml → Type
| axk (p q) : prf (p →' q →' p)
| axs (p q r) : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| mp {q r} : prf (q →' r) → prf q → prf r

open prf

-- contrapositive
definition contra (p q : fml) : fml := ((¬' q) →' (¬' p)) →' p →' q

-- excluded middle
definition lem (p : fml) : fml := (¬' (¬' p)) →' p

-- those definitions can be used to create extra
-- constructors for `fml`, equivalent to extra axioms.

-- Here is what I hope is a correct formalisation of the
-- assertion that the law of the excluded middle is equivalent
-- to Dr Britnell's choice (which is also Prof Evans' choice, I
-- think someone told me, in his P65 course)
-- of the contrapositive.

-- Solving these lemmas is the challenge then.

lemma lem_of_contra (p q : fml) :
(∀ r, prf (lem r)) → ∀ p q, prf (contra p q) :=
begin
  intro Hlem,
  intros p q,
  -- example usage
  have H : prf ((¬' (¬' q)) →' q) := Hlem q,
  have H2 : prf ((¬' q) →' ¬' p) → prf ¬' q → prf ¬' p := mp,
  sorry
end


lemma contra_of_lem (p q : fml) :
(∀ p q, prf (contra p q)) → (∀ r, prf (lem r)) :=
sorry 

import tactic.interactive

theorem cantor_surjective {α} (f : α → α → Prop) : ¬ function.surjective f | h :=
let ⟨D, e⟩ := h (λ a, ¬ f a a) in
(iff_not_self (f D D)).1 $ iff_of_eq (congr_fun e D)

-- me trying to translate it

-- change spacing, unravel fancy computer science `$` and `|` stuff,
-- completely changing notation, simplifying brackets, removing
-- universes and switching to tactic mode!

theorem cantor_surjective'
-- if X is a set
  (X : Type)
-- and if f is a surjective function from X to its power set  
  (f : X → set X)
  (Hsurj : function.surjective f) :
-- then we get a contradiction.
false :=
begin
  -- Proof.
  -- By surjectivity, there must then be an element t of X such that
  -- f t is that weird set {a : X | a ∉ f a}.
  -- So let Ht be the hypothesis that f t = {a : X | a ∉ f a}
  have H := Hsurj {a : X | a ∉ f a},
  cases H with t Ht,
  -- We're looking for a contradiction, so it suffices to
  -- prove that (t ∈ f t) ↔ (t ∉ f t) because this is logical nonsense
  -- [this is computer scientists going backwards like they like to do]
  apply (iff_not_self (t ∈ f t)).1,
  -- but the statement (t ∈ f t) ↔ (t ∉ f t) follows easily from
  -- our hypothesis Ht.
  exact (iff_of_eq (congr_fun Ht t))
end

--import logic.basic
import tactic.interactive

theorem cantor_surjective {α} (f : α → α → Prop) : ¬ function.surjective f | h :=
let ⟨D, e⟩ := h (λ a, ¬ f a a) in
(iff_not_self (f D D)).1 $ iff_of_eq (congr_fun e D)

-- me trying to translate it

-- change spacing, unravel fancy computer science `$` and `|` stuff,
-- completely changing notation, simplifying brackets, removing
-- universes and switching to tactic mode!

theorem cantor_surjective' (X : Type)
  (f : X → set X)
  (Hsurj : function.surjective f) :
false :=
begin
  -- there must then be an element t of X such that f t
  -- is that weird set {a : X | a ∉ f a}
  have H := Hsurj (λ a, ¬ f a a),
  cases H with t Ht,
  -- It suffices to prove that (t ∈ f t) ↔ (t ∉ f t)
  apply (iff_not_self (t ∈ f t)).1,
  -- but this follows easily from our assumptions
  exact (iff_of_eq (congr_fun Ht t))
end


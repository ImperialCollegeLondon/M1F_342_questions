/- (Quoting from Mario on the chat, talking about metamath.)

You should look at the derivations of some basic theorems - this is where metamath is most readable. 
Your theorem is notnot1

http://us.metamath.org/mpeuni/notnot1.html

Here is a moderately inlined version of the metamath proof. The key to making this readable is to
break it into bite sized pieces of no more than five steps. Almost all of the intermediate steps are
independently useful, even more than I'm showing here. Hilbert style axiomatizations are not meant
to be used directly; you should prove as lemmas all the basic facts and use them as scaffolding to
manage the complexity.

-/

inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:max := fml.not

inductive prf : fml → Type
| axk {p q} : prf (p →' q →' p)
| axs {p q r} : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX {p q} : prf $ (¬' q →' ¬' p) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

namespace prf
prefix `⊢ `:30 := prf

def mp' {p q} (h1 : ⊢ p →' q) (h2 : ⊢ p) : ⊢ q := mp h2 h1
def a1i {p q} : ⊢ p → ⊢ q →' p := mp' axk
def a2i {p q r} : ⊢ p →' q →' r → ⊢ (p →' q) →' p →' r := mp' axs
def con4i {p q} : ⊢ ¬' p →' ¬' q → ⊢ q →' p := mp' axX
def mpd {p q r} (h : ⊢ p →' q →' r) : ⊢ p →' q → ⊢ p →' r := mp' (a2i h)
def syl {p q r} (h1 : ⊢ p →' q) (h2 : ⊢ q →' r) : ⊢ p →' r := mpd (a1i h2) h1
def id {p} : ⊢ p →' p := mpd axk (@axk p p)
def a1d {p q r} (h : ⊢ p →' q) : ⊢ p →' r →' q := syl h axk
def com12 {p q r} (h : ⊢ p →' q →' r) : ⊢ q →' p →' r := syl (a1d id) (a2i h)
def con4d {p q r} (h : ⊢ p →' ¬' q →' ¬' r) : ⊢ p →' r →' q := syl h axX
def absurd {p q} : ⊢ ¬' p →' p →' q := con4d axk
def imidm {p q} (h : ⊢ p →' p →' q) : ⊢ p →' q := mpd h id
def contra {p} : ⊢ (¬' p →' p) →' p := imidm (con4d (a2i absurd))
def notnot2 {p} : ⊢ ¬' ¬' p →' p := syl absurd contra
def mpdd {p q r s} (h : ⊢ p →' q →' r →' s) : ⊢ p →' q →' r → ⊢ p →' q →' s := mpd (syl h axs)
def syld {p q r s} (h1 : ⊢ p →' q →' r) (h2 : ⊢ p →' r →' s) : ⊢ p →' q →' s := mpdd (a1d h2) h1
def con2d {p q r} (h1 : ⊢ p →' q →' ¬' r) : ⊢ p →' r →' ¬' q := con4d (syld (a1i notnot2) h1)
def con2i {p q} (h1 : ⊢ p →' ¬' q) : ⊢ q →' ¬' p := con4i (syl notnot2 h1)
def notnot1 {p} : ⊢ p →' ¬' ¬' p := con2i id

end prf

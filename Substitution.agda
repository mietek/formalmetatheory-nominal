module Substitution where

open import Atom
open import Alpha
open import ListProperties
open import Term hiding (fv)
open import TermRecursion
open import TermInduction
open import TermAcc
open import NaturalProperties
open import Equivariant
open import Permutation
open import FreeVariables

open import Data.Bool hiding (_∨_)
open import Data.Nat hiding (_*_)
open import Data.Nat.Properties
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.List
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Relation.Binary.PreorderReasoning as PreR
open PreR ≈-preorder

hvar : Atom → Λ → Atom → Λ
hvar x N y with x ≟ₐ y
... | yes _ = N
... | no  _ = v y

_[_≔_] : Λ → Atom → Λ → Λ
M [ a ≔ N ] = ΛIt Λ (hvar a N) _·_ (a ∷ fv N , ƛ) M


-- Substitution behaviour under ƛ term constructor
lemmaSubstƛ : ∀ a b M P → (ƛ b M) [ a ≔ P ] ≡ ƛ (χ (a ∷ fv P) (ƛ b M)) ( ( （ b ∙ (χ (a ∷ fv P) (ƛ b M)) ） M) [ a ≔ P ] )
lemmaSubstƛ a b M P = ΛItƛ Λ (hvar a P) _·_ (a ∷ fv P)  ƛ b M

lemmahvar : {a b : Atom}{M : Λ} → a ≡ b × (v b) [ a ≔ M ] ≡ M ∨ a ≢ b × (v b) [ a ≔ M ] ≡ v b
lemmahvar {a} {b} {M} with a ≟ₐ b
lemmahvar {a} {.a}  {M}  | yes  refl  = inj₁ (refl , refl)
lemmahvar {a} {b}   {M}  | no   a≢b   = inj₂ (a≢b , refl)

lemmahvar≡ : {a : Atom}{M : Λ} → hvar a M a ≡ M
lemmahvar≡ {a} {M} with lemmahvar {a} {a} {M}
... | inj₁ (_    , hvaraMa≡a)  = hvaraMa≡a
... | inj₂ (a≢a  , _      )    = ⊥-elim (a≢a refl)


lemmahvar≢ : {a b : Atom}{M : Λ} → a ≢ b → hvar a M b ≡ v b
lemmahvar≢ {a} {b} {M} a≢b with lemmahvar {a} {b} {M}
... | inj₁ (a≡b    , _)       = ⊥-elim (a≢b a≡b)
... | inj₂ (_  , hvaraMb≡b )  = hvaraMb≡b

lemmaSubst1 : {M N : Λ}(P : Λ)(a : Atom)
  → M ∼α N → M [ a ≔ P ] ≡ N [ a ≔ P ]

lemmaSubst1 {M} {N} P a = lemmaΛItStrongαCompatible Λ (hvar a P) _·_  (a ∷ fv P) ƛ M N

Ps : Λ → Λ → Atom → Λ → Set
Ps N P x M = N ∼α P → M [ x ≔ N ] ∼α M [ x ≔ P ]

lemmaSubst2 : ∀ {N} {P} M x
  → N ∼α P → M [ x ≔ N ] ∼α M [ x ≔ P ]

lemmaSubst2 {N} {P} M x = TermIndPerm (Ps N P x) lemmav lemma· lemmaƛ M
  where
  lemmav : (a : Atom) → Ps N P x (v a)
  lemmav a N∼αP with x ≟ₐ a
  ... | yes _ = N∼αP
  ... | no  _ = ∼αv
  lemma· : (M M' : Λ) → (Ps N P x) M → Ps N P x M' → Ps N P x (M · M')
  lemma· M M' PsM PsM' N∼αP
    = ∼α· (PsM N∼αP) (PsM' N∼αP)
  lemmaƛ :  (M : Λ) (b : Atom) → (∀ π → Ps N P x (π ∙ M)) → Ps N P x (ƛ b M)
  lemmaƛ M b f N∼P
    = begin
        ƛ b M [ x ≔ N ]
      ≈⟨ lemmaSubstƛ x b M N ⟩
        ƛ c ((（ b ∙ c ） M) [ x ≔ N ])
      ∼⟨ lemma∼αƛ (f [(b , c)] N∼P) ⟩
        ƛ c ((（ b ∙ c ） M) [ x ≔ P ])
      ≈⟨ cong (λ y → ƛ y ((（ b ∙ y ） M) [ x ≔ P ])) c≡d ⟩
        ƛ d ((（ b ∙ d ） M) [ x ≔ P ])
      ≈⟨ sym (lemmaSubstƛ x b M P) ⟩
        ƛ b M [ x ≔ P ]
      ∎
    where
    c = χ (x ∷ fv N) (ƛ b M)
    c#ƛbM = χ# (x ∷ fv N) (ƛ b M)
    d = χ (x ∷ fv P) (ƛ b M)
    c≡d : c ≡ d
    c≡d rewrite lemma∼αfv N∼P = refl

lemmaSubst : {M N P Q : Λ}(a : Atom)
  → M ∼α N → P ∼α Q
  → M [ a ≔ P ] ∼α N [ a ≔ Q ]
lemmaSubst {M} {N} {P} {Q} a M∼N P∼Q
  =  begin
       M [ a ≔ P ]
     ≈⟨ lemmaSubst1 P a M∼N ⟩
       N [ a ≔ P ]
     ∼⟨ lemmaSubst2 N a P∼Q  ⟩
       N [ a ≔ Q ]
     ∎


-- Substitution behaviour under swapping

lemma∙cancel∼α1 : ∀ {a b c d x g N M} → g ∉ (（ a ∙ b ）ₐ c ∷ fv (（ a ∙ b ） N) ++ fv (（ a ∙ b ） M)) → x # （ a ∙ b ） (ƛ d M)
        → （ x ∙ g ） （ （ a ∙ b ）ₐ d ∙ x ） （ a ∙ b ） M ∼α （ （ a ∙ b ）ₐ d ∙ g ） （ a ∙ b ） M
lemma∙cancel∼α1 {a} {b} {c} {d} .{（ a ∙ b ）ₐ d} {g} {N} {M} g∉ #ƛ≡
  rewrite lemma（aa）M≡M {（ a ∙ b ）ₐ d} {（ a ∙ b ） M} = ρ
lemma∙cancel∼α1 {a} {b} {c} {d} {x} {g} {N} {M} g∉ (#ƛ x#（ab）M) = lemma∙cancel∼α g#（ab）M x#（ab）M
  where
  g#（ab）M : g # （ a ∙ b ） M
  g#（ab）M = lemma∉fv→# (c∉xs++ys→c∉ys {xs = fv (（ a ∙ b ） N)} (b∉a∷xs→b∉xs g∉))

Ps[] :  Λ → Set
Ps[] M = ∀ a b c N → （ a ∙ b ） (M [ c ≔ N ]) ∼α (（ a ∙ b ） M) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ]

lemmaSw[] : ∀ M → Ps[] M
lemmaSw[]
  = TermIndPerm  Ps[] --αCompPs[]
                 lemmav
                 (λ _ _ Ps[]M Ps[]N a b c N → ∼α· (Ps[]M a b c N) (Ps[]N a b c N))
                 lemmaƛ
  where
  lemmav : (d : ℕ) → Ps[] (v d)
  lemmav d   a b c N  with (v d) [ c ≔ N ] | lemmahvar {c} {d} {N}
  lemmav .c  a b c N | .N | inj₁ (refl , refl) with  （ a ∙ b ）ₐ c | lemma∙ₐ a b c
  lemmav .c  a b c N | .N | inj₁ (refl , refl) | .b | inj₁ (a≡c , refl)
    rewrite lemmahvar≡ {b} {(（ a ∙ b ） N)} = ρ
  lemmav .c  a b c N | .N | inj₁ (refl , refl) | .a | inj₂ (inj₁ (b≡c , d≢a , refl))
    rewrite lemmahvar≡ {a} {(（ a ∙ b ） N)} = ρ
  lemmav .c a b c N | .N | inj₁ (refl , refl) | .c | inj₂ (inj₂ (d≢a , d≢b , refl))
    rewrite lemmahvar≡ {c} {(（ a ∙ b ） N)} = ρ
  lemmav d a b c N | .(v d) | inj₂ (c≢d , refl)
    rewrite lemmahvar≢ {（ a ∙ b ）ₐ c} {（ a ∙ b ）ₐ d} {（ a ∙ b ） N} (lemma∙ₐinj c≢d) = ρ
  lemmaƛ : (M : Λ) (d : ℕ)
         → ((π : List (Atom × Atom)) → Ps[] (π ∙ M))
         → Ps[] (ƛ d M)
  lemmaƛ M d Ps[]M a b c N
    = begin
        （ a ∙ b ） ƛ d M [ c ≔ N ]
      ≈⟨ cong (λ x → （ a ∙ b ） x) (lemmaSubstƛ c d M N) ⟩
        （ a ∙ b ） ƛ e ((（ d ∙ e ） M) [ c ≔ N ])
      ≈⟨ refl ⟩
        ƛ (（ a ∙ b ）ₐ e) (（ a ∙ b ） ((（ d ∙ e ） M) [ c ≔ N ]))
      ∼⟨  lemma∼αƛ (Ps[]M [(d , e)] a b c N) ⟩
        ƛ (（ a ∙ b ）ₐ e) ((（ a ∙ b ） （ d ∙ e ） M) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ])
      ≈⟨ cong (λ x → ƛ (（ a ∙ b ）ₐ e)  (x [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ])) (lemma∙distributive {a} {b} {d} {e} {M}) ⟩
        ƛ (（ a ∙ b ）ₐ e)  ((（ （ a ∙ b ）ₐ d ∙ （ a ∙ b ）ₐ e ） （ a ∙ b ） M) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ])
      ∼⟨ ∼αƛ (（ a ∙ b ）ₐ c ∷ fv (（ a ∙ b ） N) ++ fv (（ a ∙ b ） M))
         (λ g g∉vs →
         begin
           （ （ a ∙ b ）ₐ e ∙ g ） ((（ （ a ∙ b ）ₐ d ∙ （ a ∙ b ）ₐ e ） （ a ∙ b ） M) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ])
         ∼⟨ Ps[]M ((（ a ∙ b ）ₐ d , （ a ∙ b ）ₐ e)  ∷ ( a , b ) ∷ []) (（ a ∙ b ）ₐ e) g (（ a ∙ b ）ₐ c) (（ a ∙ b ） N) ⟩
            ((（ （ a ∙ b ）ₐ e ∙ g ） （ （ a ∙ b ）ₐ d ∙ （ a ∙ b ）ₐ e ） （ a ∙ b ） M) [ （ （ a ∙ b ）ₐ e ∙ g ）ₐ （ a ∙ b ）ₐ c ≔ （ （ a ∙ b ）ₐ e ∙ g ） （ a ∙ b ） N ])
         ≈⟨ cong (λ x → (（ （ a ∙ b ）ₐ e ∙ g ） （ （ a ∙ b ）ₐ d ∙ （ a ∙ b ）ₐ e ） （ a ∙ b ） M) [ x ≔ （ （ a ∙ b ）ₐ e ∙ g ） （ a ∙ b ） N ]) (lemma∙ₐc≢a∧c≢b (lemma∙ₐinj (sym≢ e≢c)) (sym≢ (g≢（ab）c g∉vs))) ⟩
            (（ （ a ∙ b ）ₐ e ∙ g ） （ （ a ∙ b ）ₐ d ∙ （ a ∙ b ）ₐ e ） （ a ∙ b ） M) [ （ a ∙ b ）ₐ c ≔ （ （ a ∙ b ）ₐ e ∙ g ） （ a ∙ b ） N ]
         ∼⟨ lemmaSubst2 (（ （ a ∙ b ）ₐ e ∙ g ） （ （ a ∙ b ）ₐ d ∙ （ a ∙ b ）ₐ e ） （ a ∙ b ） M) (（ a ∙ b ）ₐ c) (σ (lemma#∼α （ab）e#（ab）N (g#（ab）N g∉vs))) ⟩
            (（ （ a ∙ b ）ₐ e ∙ g ） （ （ a ∙ b ）ₐ d ∙ （ a ∙ b ）ₐ e ） （ a ∙ b ） M) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ]
         ≈⟨ lemmaSubst1 (（ a ∙ b ） N) (（ a ∙ b ）ₐ c) (∼α1 g∉vs e#ƛdM) ⟩
            (（ （ a ∙ b ）ₐ d ∙ g ） （ a ∙ b ） M) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ]
         ≈⟨ lemmaSubst1 (（ a ∙ b ） N) (（ a ∙ b ）ₐ c) (∼α2 g∉vs f#ƛ（ab）d（ab）M) ⟩
            (（ f ∙ g ） （ （ a ∙ b ）ₐ d ∙ f ） （ a ∙ b ） M) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ]
         ∼⟨ lemmaSubst2 (（ f ∙ g ） （ （ a ∙ b ）ₐ d ∙ f ） （ a ∙ b ） M) (（ a ∙ b ）ₐ c) (lemma#∼α f#（ab）N (g#（ab）N g∉vs)) ⟩
            (（ f ∙ g ） （ （ a ∙ b ）ₐ d ∙ f ） （ a ∙ b ） M) [ （ a ∙ b ）ₐ c ≔ （ f ∙ g ） （ a ∙ b ） N ]
         ≈⟨ cong (λ x → (（ f ∙ g ） （ （ a ∙ b ）ₐ d ∙ f ） （ a ∙ b ） M) [ x ≔ （ f ∙ g ） （ a ∙ b ） N ]) ( sym (lemma∙ₐc≢a∧c≢b (sym≢ f≢（ab）c) (sym≢ (g≢（ab）c g∉vs))))  ⟩
            (（ f ∙ g ） （ （ a ∙ b ）ₐ d ∙ f ） （ a ∙ b ） M) [ （ f ∙ g ）ₐ （ a ∙ b ）ₐ c ≔ （ f ∙ g ） （ a ∙ b ） N ]
         ∼⟨ σ (Ps[]M ((（ a ∙ b ）ₐ d , f) ∷ (a , b) ∷ []) f g (（ a ∙ b ）ₐ c) (（ a ∙ b ） N)) ⟩
           （  f            ∙ g ） ((（ （ a ∙ b ）ₐ d ∙         f      ） （ a ∙ b ） M) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ])
         ∎ )⟩
        ƛ f               ((（ （ a ∙ b ）ₐ d ∙ f ） （ a ∙ b ） M) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ])
      ≈⟨ sym (lemmaSubstƛ (（ a ∙ b ）ₐ c) (（ a ∙ b ）ₐ d) (（ a ∙ b ） M) (（ a ∙ b ） N)) ⟩
        (ƛ (（ a ∙ b ）ₐ d) (（ a ∙ b ） M)) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ]
     ≈⟨ refl  ⟩
        (（ a ∙ b ） ƛ d M) [ （ a ∙ b ）ₐ c ≔ （ a ∙ b ） N ]
      ∎
    where
    e = χ (c ∷ fv N) (ƛ d M)
    f = χ (（ a ∙ b ）ₐ c ∷ fv (（ a ∙ b ） N)) (（ a ∙ b ） ƛ d M)
    e#ƛdM : e # ƛ d M
    e#ƛdM = χ# (c ∷ fv N) (ƛ d M)
    e∉c∷fvN : e ∉ c ∷ fv N
    e∉c∷fvN = χ∉ (c ∷ fv N) (ƛ d M)
    e≢c : e ≢ c
    e≢c = b∉a∷xs→b≢a e∉c∷fvN
    g≢（ab）c : {g : Atom} → g ∉ (（ a ∙ b ）ₐ c ∷ fv (（ a ∙ b ） N) ++ fv (（ a ∙ b ） M)) →  g ≢ （ a ∙ b ）ₐ c
    g≢（ab）c g∉ = b∉a∷xs→b≢a g∉
    e#N : e # N
    e#N = lemma∉fv→# (b∉a∷xs→b∉xs e∉c∷fvN)
    g#（ab）N : {g : Atom} → g ∉ (（ a ∙ b ）ₐ c ∷ fv (（ a ∙ b ） N) ++ fv (（ a ∙ b ） M)) →  g # （ a ∙ b ） N
    g#（ab）N g∉ = lemma∉fv→# (c∉xs++ys→c∉xs (b∉a∷xs→b∉xs g∉))
    （ab）e#（ab）N : （ a ∙ b ）ₐ e # （ a ∙ b ） N
    （ab）e#（ab）N = lemma#Equiv [(a , b)] e#N
    f#ƛ（ab）d（ab）M : f # ƛ (（ a ∙ b ）ₐ d) (（ a ∙ b ） M)
    f#ƛ（ab）d（ab）M = χ# (（ a ∙ b ）ₐ c ∷ fv (（ a ∙ b ） N)) (ƛ (（ a ∙ b ）ₐ d) (（ a ∙ b ） M))
    f∉（ab）c∷fv（ab）N : f ∉ （ a ∙ b ）ₐ c ∷ fv (（ a ∙ b ） N)
    f∉（ab）c∷fv（ab）N = χ∉ (（ a ∙ b ）ₐ c ∷ fv (（ a ∙ b ） N)) (ƛ (（ a ∙ b ）ₐ d) (（ a ∙ b ） M))
    f≢（ab）c : f ≢ （ a ∙ b ）ₐ c
    f≢（ab）c = b∉a∷xs→b≢a f∉（ab）c∷fv（ab）N
    f#（ab）N : f # （ a ∙ b ） N
    f#（ab）N = lemma∉fv→# (b∉a∷xs→b∉xs f∉（ab）c∷fv（ab）N)
    ∼α1 : ∀ {g e} → g ∉ (（ a ∙ b ）ₐ c ∷ fv (（ a ∙ b ） N) ++ fv (（ a ∙ b ） M)) → e # ƛ d M
        → （ （ a ∙ b ）ₐ e ∙ g ） （ （ a ∙ b ）ₐ d ∙ （ a ∙ b ）ₐ e ） （ a ∙ b ） M ∼α （ （ a ∙ b ）ₐ d ∙ g ） （ a ∙ b ） M
    ∼α1 {g} {e} g∉ e# = lemma∙cancel∼α1 {a} {b} {c} {d} {（ a ∙ b ）ₐ e} {g} {N} {M} g∉ (lemma#Equiv [(a , b)] e#)
    ∼α2 : ∀ {g f} → g ∉ (（ a ∙ b ）ₐ c ∷ fv (（ a ∙ b ） N) ++ fv (（ a ∙ b ） M)) → f # ƛ (（ a ∙ b ）ₐ d) (（ a ∙ b ） M)
        → （ （ a ∙ b ）ₐ d ∙ g ） （ a ∙ b ） M ∼α （ f ∙ g ） （ （ a ∙ b ）ₐ d ∙ f ） （ a ∙ b ） M
    ∼α2 {g} {f} g∉ f# = σ (lemma∙cancel∼α1 {a} {b} {c} {d} {f} {g} {N} {M} g∉ f#)


-- The result of substitution is alpha-equivalent to a naive substitution when there not exists variable capture.

lemmaƛ∼[] : ∀ {a b P} M → b ∉ a ∷ fv P
  → ƛ b M [ a ≔ P ] ∼α  ƛ b (M [ a ≔ P ])

lemmaƛ∼[] {a} {b} {P} M b∉a∷fvP
  = begin
       ƛ b M [ a ≔ P ]
    ≈⟨ lemmaSubstƛ a b M P ⟩
       ƛ c ((（ b ∙ c ） M) [ a ≔ P ])
    ∼⟨ ∼αƛ  (a ∷ fv P ++ fv M)
            (λ d d∉ →  begin
                         （ c ∙ d ） (（ b ∙ c ） M) [ a ≔ P ]
                       ∼⟨ lemmaSw[] (（ b ∙ c ） M) c d a P  ⟩
                         (（ c ∙ d ） （ b ∙ c ） M) [ （ c ∙ d ）ₐ  a ≔ （ c ∙ d ） P ]
                       ≈⟨ lemmaSubst1 (（ c ∙ d ） P) (（ c ∙ d ）ₐ  a) (lemma∙cancel∼α‴ (d#M d∉) c#ƛbM) ⟩
                         (（ b ∙ d ） M) [ （ c ∙ d ）ₐ a ≔ （ c ∙ d ） P ]
                       ≈⟨ cong (λ x → (（ b ∙ d ） M) [ x ≔ （ c ∙ d ） P ]) (lemma∙ₐc≢a∧c≢b a≢c (a≢d d∉)) ⟩
                         (（ b ∙ d ） M) [ a ≔ （ c ∙ d ） P ]
                       ∼⟨ lemmaSubst2 (（ b ∙ d ） M) a (σ (lemma#∼α c#P (d#P d∉))) ⟩
                         (（ b ∙ d ） M) [ a ≔ P ]
                       ∼⟨ lemmaSubst2 (（ b ∙ d ） M) a ((lemma#∼α b#P (d#P d∉))) ⟩
                         (（ b ∙ d ） M) [ a ≔ （ b ∙ d ） P ]
                       ≈⟨ sym (cong (λ x → (（ b ∙ d ） M) [ x ≔ （ b ∙ d ） P ]) (lemma∙ₐc≢a∧c≢b a≢b (a≢d d∉))) ⟩
                         (（ b ∙ d ） M) [ （ b ∙ d ）ₐ a ≔ （ b ∙ d ） P ]
                       ∼⟨ σ (lemmaSw[] M b d a P)  ⟩
                         （ b ∙ d ） (M [ a ≔ P ])
                       ∎)⟩
      ƛ b (M [ a ≔ P ])
    ∎
  where
  a≢b : a ≢ b
  a≢b = sym≢ (b∉a∷xs→b≢a b∉a∷fvP)
  a≢d : ∀ {d} → d ∉ (a ∷ fv P ++ fv M) → a ≢ d
  a≢d d∉ = sym≢ (b∉a∷xs→b≢a d∉)
  d#M : ∀ {d} → d ∉ (a ∷ fv P ++ fv M) → d # M
  d#M d∉ = lemma∉fv→# (c∉xs++ys→c∉ys {xs = fv P} (b∉a∷xs→b∉xs d∉))
  d#P : ∀ {d} → d ∉ (a ∷ fv P ++ fv M) → d # P
  d#P d∉ = lemma∉fv→# (c∉xs++ys→c∉xs (b∉a∷xs→b∉xs d∉))
  c = χ (a ∷ fv P) (ƛ b M)
  c#ƛbM = χ# (a ∷ fv P) (ƛ b M)
  c∉a∷fvP = χ∉ (a ∷ fv P) (ƛ b M)
  c#P : c # P
  c#P = lemma∉fv→# (b∉a∷xs→b∉xs c∉a∷fvP)
  b#P : b # P
  b#P = lemma∉fv→# (b∉a∷xs→b∉xs b∉a∷fvP)
  a≢c : a ≢ c
  a≢c = sym≢ (b∉a∷xs→b≢a c∉a∷fvP)

Pfv[] : Atom → Λ → Λ → Set
Pfv[] x N M = x ∉ fv M → M ∼α M [ x ≔ N ]

αCompatiblePfv[] : ∀ x N → αCompatiblePred (Pfv[] x N)
αCompatiblePfv[] x N {M} {P} M∼P Pfv[]M x∉fvP rewrite lemma∼αfv (σ M∼P)
  =  begin
       P
     ∼⟨ σ (M∼P) ⟩
       M
     ∼⟨ Pfv[]M x∉fvP ⟩
       M [ x ≔ N ]
     ≈⟨ lemmaSubst1 N x M∼P  ⟩
       P [ x ≔ N ]
     ∎

lemmafv[] : ∀ {x N M} → Pfv[] x N M
lemmafv[] {x} {N} {M}
  = TermαPrimInd  (Pfv[] x N) (αCompatiblePfv[] x N)
                  lemmav
                  lemma·
                  (x ∷ fv N , lemmaƛ)
                  M
  where
  lemmav : (a : ℕ) → Pfv[] x N (v a)
  lemmav a x∉fva with (v a) [ x ≔ N ] | lemmahvar {x} {a} {N}
  ... | .N | inj₁ (x≡a , refl)    = ⊥-elim (x∉fva (here x≡a))
  ... | .(v a) | inj₂ (_ , refl)  = ∼αv
  lemma· : (M P : Λ) → Pfv[] x N M → Pfv[] x N P → Pfv[] x N (M · P)
  lemma· M P Pfv[]M Pfv[]N x∉fvM++fvN
    = ∼α· (Pfv[]M (c∉xs++ys→c∉xs x∉fvM++fvN)) (Pfv[]N (c∉xs++ys→c∉ys {xs = fv M} x∉fvM++fvN))
  lemmaƛ : (M : Λ) (b : ℕ) → b ∉ x ∷ fv N → Pfv[] x N M → Pfv[] x N (ƛ b M)
  lemmaƛ M b b∉ Pfv[]M x∉ƛbM
    =  begin
         ƛ b M
       ∼⟨ lemma∼αƛ (Pfv[]M x∉fvM) ⟩
         ƛ b (M [ x ≔ N ])
       ∼⟨ σ (lemmaƛ∼[] M b∉) ⟩
         ƛ b M [ x ≔ N ]
       ∎
    where
    x≢b : x ≢ b
    x≢b = λ x≡b → b∉ (here (sym x≡b))
    x∉fvM : x ∉ fv M
    x∉fvM x∈fvM = x∉ƛbM (lemma∈fvM→a∈fvƛbM {b = b} {M} x≢b x∈fvM)

PSC : ∀ {x y L} N → Λ → Set
PSC {x} {y} {L} N M = x ≢ y → x ∉ fv L
  → (M [ x ≔ N ]) [ y ≔ L ] ∼α (M [ y ≔ L ])[ x ≔ N [ y ≔ L ] ]

αCompatiblePSC : ∀ {x y L} N → αCompatiblePred (PSC {x} {y} {L} N)
αCompatiblePSC {x} {y} {L} N {M} {P} M∼P PM x≢y x∉fvL
  =  begin
       (P [ x ≔ N ]) [ y ≔ L ]
     -- Strong α compability of inner substitution operation
     ≈⟨ cong (λ z → z [ y ≔ L ]) (lemmaSubst1 N x (σ M∼P)) ⟩
       (M [ x ≔ N ]) [ y ≔ L ]
     -- We apply that we know the predicate holds for M
     ∼⟨ PM x≢y x∉fvL ⟩
       (M [ y ≔ L ]) [ x ≔ N [ y ≔ L ] ]
     -- Strong α compability of inner substitution operation
     ≈⟨ cong (λ z → z [ x ≔ N [ y ≔ L ] ]) (lemmaSubst1 L y (M∼P))  ⟩
       (P [ y ≔ L ]) [ x ≔ N [ y ≔ L ] ]
     ∎

lemmav[] : ∀ a x y N L → x ≢ y → x ∉ fv L
  → ((v a) [ x ≔ N ]) [ y ≔ L ] ∼α ((v a) [ y ≔ L ]) [ x ≔ (N [ y ≔ L ]) ]
lemmav[] a x y N L  x≢y x∉fvL with (v a) [ x ≔ N ] | lemmahvar {x} {a} {N}
lemmav[] a x y N L x≢y x∉fvL | .N      | inj₁ (x≡a , refl)
  with (v a) [ y ≔ L ] | lemmahvar {y} {a} {L}
... | .L      | inj₁ (y≡a , refl) = ⊥-elim (x≢y (trans x≡a (sym y≡a)))
... | .(v a)  | inj₂ (y≢a , refl)
  with (v a) [ x ≔ (N [ y ≔ L ]) ] | lemmahvar {x} {a} {N [ y ≔ L ]}
... | .(N [ y ≔ L ])  | inj₁ (_    , refl) = ρ
... | .(v a)           | inj₂ (x≢a  , refl) = ⊥-elim (x≢a x≡a)
lemmav[] a x y N L x≢y x∉fvL | .(v a)  | inj₂ (x≢a , refl)
  with (v a) [ y ≔ L ] | lemmahvar {y} {a} {L}
... | .L      | inj₁ (y≡a , refl) = lemmafv[] x∉fvL
... | .(v a)  | inj₂ (y≢a , refl)
  with (v a) [ x ≔ N [ y ≔ L ] ] | lemmahvar {x} {a} {N [ y ≔ L ]}
... | .(N [ y ≔ L ])  | inj₁ (x≡a    , refl)  = ⊥-elim (x≢a x≡a)
... | .(v a)           | inj₂ (_  , refl)      = ∼αv

lemmaSubstComposition : ∀ {x y L} N M → PSC {x} {y} {L} N M
lemmaSubstComposition {x} {y} {L} N M
  = TermαPrimInd  (PSC {x} {y} {L} N)
                  (αCompatiblePSC {x} {y} {L} N)
                  lemmav
                  lemma·
                  (y ∷ fv L ++ x ∷ fv N ++ fv (N [ y ≔ L ]) , lemmaƛ)
                  M
  where
  lemmav : (a : ℕ) → PSC {x} {y} {L} N (v a)
  lemmav a x≢y x∉fvL = lemmav[] a x y N L x≢y x∉fvL
  lemma· : (M P : Λ) → PSC {x} {y} {L} N M → PSC {x} {y} {L} N P → PSC {x} {y} {L} N (M · P)
  lemma· M P PscNM PscNP x≢y x∉fvL
    = ∼α· (PscNM x≢y x∉fvL) (PscNP x≢y x∉fvL)
  lemmaƛ : (M : Λ) (b : ℕ) → b ∉ y ∷ fv L ++ x ∷ fv N ++ fv (N [ y ≔ L ])
         → PSC N M → PSC N (ƛ b M)
  lemmaƛ M b b∉ IndHip x≢y x∉fvL
    =
       begin
         (ƛ b M [ x ≔ N ])   [ y ≔ L ]
       -- Inner substitution is α equivalent
       -- to a naive one because b ∉ x ∷ fv N
       ≈⟨ lemmaSubst1 L y (lemmaƛ∼[] M b∉x∷fvN)  ⟩
         (ƛ b (M [ x ≔ N ])) [ y ≔ L ]
       -- Outer substitution is α equivalent
       -- to a naive one because b ∉ y ∷ fv L
       ∼⟨ lemmaƛ∼[] (M [ x ≔ N ]) b∉y∷fvL ⟩
         ƛ b ((M [ x ≔ N ])  [ y ≔ L ])
       -- We can now apply our inductive hypothesis
       ∼⟨ lemma∼αƛ (IndHip x≢y x∉fvL) ⟩
         ƛ b ((M [ y ≔ L ])  [ x ≔ N [ y ≔ L ] ])
       -- Outer substitution is α equivalent
       -- to a naive one because b ∉ x ∷ fv N [y ≔ L]
       ∼⟨ σ (lemmaƛ∼[] (M [ y ≔ L ]) b∉x∷fvN[y≔L]) ⟩
         (ƛ b (M [ y ≔ L ])) [ x ≔ N [ y ≔ L ] ]
       -- Inner substitution is α equivalent
       -- to a naive one because b ∉ y ∷ fv L
       ≈⟨ sym (lemmaSubst1 (N [ y ≔ L ])  x (lemmaƛ∼[] M b∉y∷fvL))  ⟩
         (ƛ b M [ y ≔ L ])   [ x ≔ N [ y ≔ L ] ]
       ∎
      where
      b∉x∷fvN : b ∉ x ∷ fv N
      b∉x∷fvN = c∉xs++ys→c∉xs (c∉xs++ys→c∉ys {xs = y ∷ fv L} b∉)
      b≢x : b ≢ x
      b≢x = λ b≡x → b∉x∷fvN (here b≡x)
      b∉y∷fvL : b ∉ y ∷ fv L
      b∉y∷fvL = c∉xs++ys→c∉xs b∉
      b∉fvN[y≔L] : b ∉ fv (N [ y ≔ L ])
      b∉fvN[y≔L] = c∉xs++ys→c∉ys {xs = x ∷ fv N} (c∉xs++ys→c∉ys {xs = y ∷ fv L} b∉)
      b∉x∷fvN[y≔L] : b ∉ x ∷ fv (N [ y ≔ L ])
      b∉x∷fvN[y≔L] (here b≡x) = ⊥-elim (b≢x b≡x)
      b∉x∷fvN[y≔L] (there b∈) = ⊥-elim (b∉fvN[y≔L] b∈)

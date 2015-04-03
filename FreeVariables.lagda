\begin{code}
module FreeVariables where

open import Level
open import Function
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

\end{code}

%<*freeVariables>
\begin{code}
fv : Λ → List Atom
fv = ΛIt (List Atom) [_] _++_ ([] , λ v r → r - v)
\end{code}
%</freeVariables>

\begin{code}
lemmafvƛ : ∀ b M → fv (ƛ b M) ≡ fv (（ b ∙ χ [] (ƛ b M) ） M) - χ [] (ƛ b M)
lemmafvƛ b M = ΛItƛ (List Atom) [_] _++_ []  (λ v r → r - v) b M
--
lemma∼αfv : {M N : Λ} → M ∼α N → fv M ≡ fv N
lemma∼αfv {M} {N} = lemmaΛItStrongαCompatible (List Atom) [_] _++_ [] (λ v r → r - v) M N 
\end{code}


Define free predicate using term iterator


\begin{code}
free : Atom → Λ → Set
free a = ΛIt Set (λ b → a ≡ b) _∨_ ([ a ] , const id) 
--
freeλ : ∀ a b M → free a (ƛ b M) ≡ free a (（ b ∙ χ [ a ] (ƛ b M) ） M)
freeλ a b M = ΛItƛ Set (λ b → a ≡ b) _∨_ [ a ] (const id) b M 
--
freeStrongCompatible : ∀ a M → strong∼αCompatible (free a) M
freeStrongCompatible a M N M∼N 
  = lemmaΛItStrongαCompatible Set (λ b → a ≡ b) _∨_ [ a ]  (const id) M N M∼N
--
lemmavfree : ∀ {a b} → a ≡ b → free a (v b)
lemmavfree {a} .{a} refl  = refl
--
lemma·rfree : ∀ {a M} N → free a M → free a (M · N)
lemma·rfree {a} {M} N afreeM = inj₁ afreeM
--
lemma·lfree : ∀ {a} M {N} → free a N → free a (M · N)
lemma·lfree {a} M {N} afreeN = inj₂ afreeN
--
Pfs : Atom → Λ → Set
Pfs a M = ∀ b c → a ≢ b → a ≢ c → free a M → free a (（ b ∙ c ） M)
--
lemmaFreeSwap : ∀ M a → Pfs a M
lemmaFreeSwap M a
  = TermαIndPerm  
                 (Pfs a) 
                 αCompatiblePfsa
                 lemmav 
                 lemma· 
                 ([ a ] , lemmaƛ)
                 M 
  where
  αCompatiblePfsa : αCompatiblePred (Pfs a)
  αCompatiblePfsa {M} {N} M∼N PfsaM b c a≢b a≢c afreeN 
    rewrite  
       freeStrongCompatible a N M (σ M∼N) 
    |  freeStrongCompatible a (（ b ∙ c ） N) (（ b ∙ c ） M) (lemma∼αEquiv [(b , c)] (σ M∼N)) 
    = PfsaM b c a≢b a≢c afreeN
  lemmav : (d : ℕ) → Pfs a (v d)
  lemmav .a b c a≢b a≢c refl = sym (lemma∙ₐc≢a∧c≢b a≢b a≢c)
  lemma· : (M N : Λ) → Pfs a M → Pfs a N → Pfs a (M · N)
  lemma· M₁ N PfsaM PfsaN b c a≢b a≢c (inj₁ afreeM) = inj₁ (PfsaM b c a≢b a≢c afreeM)
  lemma· M₁ N PfsaM PfsaN b c a≢b a≢c (inj₂ afreeN) = inj₂ (PfsaN b c a≢b a≢c afreeN)
  lemmaƛ : (M : Λ) (d : ℕ) → d ∉ [ a ] → ((π : List (Atom × Atom)) → Pfs a (π ∙ M)) → Pfs a (ƛ d M)
  lemmaƛ M d d∉[a] Hi b c a≢b a≢c afree（de）M rewrite freeλ a d M | freeλ a (（ b ∙ c ）ₐ d) (（ b ∙ c ） M)
    with χ [ a ] (ƛ d M) | χ∉ [ a ] (ƛ d M) | χ [ a ] (（ b ∙ c ） (ƛ d M)) | χ∉ [ a ] (（ b ∙ c ） (ƛ d M))
  ... | e | e∉[a] | f | f∉[a] = afree（（bc）df）（bc）M
    where 
    a≢d : a ≢ d
    a≢d = λ a≡d → d∉[a] (here (sym a≡d))
    a≢e : a ≢ e
    a≢e = λ a≡e → (e∉[a] (here (sym a≡e)))
    afreeM :  free a M
    afreeM  with （ d ∙ e ） (（ d ∙ e ） M) | Hi [( d , e)] d e a≢d a≢e afree（de）M | lemma（ab）（ab）M≡M {d} {e} {M}
    ... | .M | afreeM | refl = afreeM
    afree（bc）M : free a (（ b ∙ c ） M)
    afree（bc）M = Hi [] b c a≢b a≢c afreeM
    a≢（bc）d : a ≢ （ b ∙ c ）ₐ d
    a≢（bc）d = lemma∙ₐa≢b∧a≢c∧a≢d→a≢（bc）d a≢b a≢c a≢d
    a≢f : a ≢ f
    a≢f = λ a≡f → (f∉[a] (here (sym a≡f)))
    afree（（bc）df）（bc）M : free a (（ （ b ∙ c ）ₐ d ∙ f ） （ b ∙ c ） M)
    afree（（bc）df）（bc）M = Hi [(b , c)] (（ b ∙ c ）ₐ d) f a≢（bc）d a≢f afree（bc）M
--
lemmaƛfree : ∀ {b a M} → free a M → a ≢ b → free a (ƛ b M)
lemmaƛfree {b} {a} {M} freeaM a≢b rewrite freeλ a b M = lemmaFreeSwap M a b c a≢b a≢c freeaM
  where
  c = χ [ a ] (ƛ b M)
  c∉[a] = χ∉ [ a ] (ƛ b M)
  a≢c = λ a≡c → c∉[a] (here (sym a≡c))
--
lemma*→free : ∀ {a M} → a * M → free a M
lemma*→free *v                        = lemmavfree refl
lemma*→free {a} {M · N} (*·l a*M)     = lemma·rfree {a} {M} N (lemma*→free a*M)
lemma*→free {a} {M · N} (*·r a*N)     = lemma·lfree {a} M {N} (lemma*→free a*N)
lemma*→free {a} {ƛ b M} (*ƛ a*M a≢b)  = lemmaƛfree {b} {a} {M} (lemma*→free a*M) (sym≢ a≢b)
--
Pfs2 : Atom → Λ → Set
Pfs2 a M = ∀ b c → a ≢ b → a ≢ c → free a (（ b ∙ c ） M) → free a M
--
lemmaFreeSwap2 : ∀ M a → Pfs2 a M
lemmaFreeSwap2 M a b c a≢b a≢c afree（bc）M 
  with lemmaFreeSwap (（ b ∙ c ） M) a b c a≢b a≢c afree（bc）M 
... | p rewrite lemma（ab）（ab）M≡M {b} {c} {M}  = p
--
Pf* : Atom → Λ → Set
Pf* a M = free a M → a * M
--
lemmafree→* : ∀ {a M} → Pf* a M
lemmafree→* {a} {M} 
  = TermαIndPerm (Pf* a) αCompatiblePf*a (λ {.a refl → *v}) lemma· ([ a ] , lemmaƛ) M
  where
  αCompatiblePf*a :  αCompatiblePred (Pf* a)
  αCompatiblePf*a {M} {N} M∼N Pf*aM afreeN 
    rewrite freeStrongCompatible a N M (σ M∼N) 
    = lemma∼α* M∼N (Pf*aM afreeN)
  lemma· : (M N : Λ) → Pf* a M → Pf* a N → Pf* a (M · N)
  lemma· M N Pf*aM Pf*aN (inj₁ a*M) = *·l (Pf*aM a*M)
  lemma· M N Pf*aM Pf*aN (inj₂ a*N) = *·r (Pf*aN a*N)
  lemmaƛ : (M : Λ) (b : ℕ) → b ∉ [ a ] 
         → ((π : List (Atom × Atom)) → Pf* a (π ∙ M)) 
         → Pf* a (ƛ b M)
  lemmaƛ M b b∉[a] Hi afree（bc）M rewrite freeλ a b M with χ [ a ] (ƛ b M) | χ∉ [ a ] (ƛ b M) 
  ... | c | c∉[a] = *ƛ (lemma*swap←≢ (sym≢ b≢a) a≢c (Hi [( b , c)] afree（bc）M)) b≢a
    where 
    b≢a = λ b≡a → b∉[a] (here b≡a)
    a≢c = λ a≡c → c∉[a] (here (sym a≡c))
--
Pfvf : Atom → Λ → Set
Pfvf a M = a ∈ fv M → free a M
--
αCompatiblePfvfa : ∀ a → αCompatiblePred (Pfvf a)
αCompatiblePfvfa a {M} {N} M∼N PfvfM a∈fvN 
  rewrite 
    lemma∼αfv M∼N 
  | freeStrongCompatible a N M (σ M∼N) = PfvfM a∈fvN
--
lemmafvf : ∀ {a} {M} → Pfvf a M
lemmafvf {a} {M} 
  = TermαIndPerm (Pfvf a) (αCompatiblePfvfa a) lemmav lemma· ([ a ] , lemmaƛ) M   
  where
  lemmav : (b : ℕ) → Pfvf a (v b)
  lemmav .a  (here refl) = refl
  lemmav _   (there ())
  lemma· : (M N : Λ) → Pfvf a M → Pfvf a N → Pfvf a (M · N)
  lemma· M N PfvfaM PfvfaN a∈fvM++fvN with c∈xs++ys→c∈xs∨c∈ys {a} {fv M} a∈fvM++fvN 
  ... | inj₁ a∈fvM = inj₁ (PfvfaM a∈fvM)
  ... | inj₂ a∈fvN = inj₂ (PfvfaN a∈fvN)
  lemmaƛ : (M : Λ) (b : ℕ) → b ∉ [ a ] 
         → ((π : List (Atom × Atom)) 
         → Pfvf a (π ∙ M)) 
         → Pfvf a (ƛ b M)
  lemmaƛ M b b∉[a] f a∈fvƛbM 
    rewrite lemmafvƛ b M
    with χ [] (ƛ b M) | lemmafilter→ a (fv (（ b ∙ χ [] (ƛ b M) ） M)) (λ y → not (⌊ χ [] (ƛ b M) ≟ₐ y ⌋)) a∈fvƛbM  
  ... | c | ¬a≟c=true , a∈fv（bc）M with a ≟ₐ c
  lemmaƛ M b b∉[a] f a∈fvƛbM | .a | ¬a≟a=true , a∈fv（ba）M  | yes refl with a ≟ₐ a
  lemmaƛ M b b∉[a] f a∈fvƛbM | .a | () , a∈fv（ba）M  | yes refl | yes _
  lemmaƛ M b b∉[a] f a∈fvƛbM | .a | _ , a∈fv（ba）M  | yes refl | no a≢a = ⊥-elim (a≢a refl)
  lemmaƛ M b b∉[a] f a∈fvƛbM | c  | _ , a∈fv（bc）M  | no a≢c 
    = lemmaƛfree {b} {a} {M} (lemmaFreeSwap2 M a b c a≢b a≢c (f [(b , c)] a∈fv（bc）M)) a≢b 
    where
    a≢b : a ≢ b
    a≢b = λ a≡b → (⊥-elim (b∉[a] (here (sym a≡b))))
\end{code}

Other way using free data relation *.

%<*fvPred>
\begin{code}
Pfv* : Atom → Λ → Set
Pfv* a M = a ∈ fv M → a * M
\end{code}
%</fvPred>

\begin{code}
αCompatiblePfv* : ∀ a → αCompatiblePred (Pfv* a)
αCompatiblePfv* a M∼N a∈fvM→a*M a∈fvN 
  rewrite lemma∼αfv M∼N = lemma∼α* M∼N (a∈fvM→a*M a∈fvN)
--
lemmafv* : ∀ {a} {M} → Pfv* a M
lemmafv* {a} {M} = TermαIndPerm (Pfv* a) (αCompatiblePfv* a) lemmav lemma· ([ a ] , lemmaƛ) M
  where
  lemmav : (b : Atom) → Pfv* a (v b)
  lemmav .a  (here refl) = *v
  lemmav b   (there ()) 
  lemma· : (M N : Λ) → Pfv* a M → Pfv* a N → Pfv* a (M · N)
  lemma· M N PM PN a∈fvM·N
    with c∈xs++ys→c∈xs∨c∈ys {a} {fv M} {fv N} a∈fvM·N 
  ... | inj₁ a∈fvM = *·l (PM a∈fvM)
  ... | inj₂ a∈fvN = *·r (PN a∈fvN)
  lemmaƛ : (M : Λ) (b : ℕ) → b ∉ [ a ] → (∀ π → Pfv* a (π ∙ M)) → Pfv* a (ƛ b M)
  lemmaƛ M b b∉[a] f a∈fvƛbM 
    rewrite lemmafvƛ b M
    with χ [] (ƛ b M) | lemmafilter→ a (fv (（ b ∙ χ [] (ƛ b M) ） M)) (λ y → not (⌊ χ [] (ƛ b M) ≟ₐ y ⌋)) a∈fvƛbM  
  ... | c | ¬a≟c=true , a∈fv（bc）M with a ≟ₐ c
  lemmaƛ M b b∉[a] f a∈fvƛbM | .a | ¬a≟a=true , a∈fv（ba）M  | yes refl with a ≟ₐ a
  lemmaƛ M b b∉[a] f a∈fvƛbM | .a | () , a∈fv（ba）M  | yes refl | yes _
  lemmaƛ M b b∉[a] f a∈fvƛbM | .a | _ , a∈fv（ba）M  | yes refl | no a≢a = ⊥-elim (a≢a refl)
  lemmaƛ M b b∉[a] f a∈fvƛbM | c  | _ , a∈fv（bc）M  | no a≢c 
    = *ƛ (lemma*swap←≢ (sym≢ b≢a) a≢c  (f [(b , c)] a∈fv（bc）M)) b≢a
    where
    b≢a : b ≢ a
    b≢a = λ b≡a → (⊥-elim (b∉[a] (here b≡a)))
\end{code}

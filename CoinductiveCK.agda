
module CoinductiveCK where

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat
open import Data.Bool using (Bool; if_then_else_; true; false)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; subst)
open PropEq.≡-Reasoning
open import Relation.Nullary
open import Relation.Nullary.Negation using (¬∃⟶∀¬; Excluded-Middle)
open import Function using (_$_; _∘_)
open import Relation.Binary.Core using (IsEquivalence) renaming (Rel to RelL)
open import Level as L using () renaming (_⊔_ to _⊔L_)

-- to be classical, we need the law of excluded middle
-- the following defns. were adapted from:
-- http://stackoverflow.com/questions/36669072/law-of-excluded-middle-in-agda

postulate LEM : ∀ {ℓ} (A : Set ℓ) → Dec A

¬¬A⇒A : ∀ {ℓ} {A : Set ℓ} → ¬ (¬ A) → A
¬¬A⇒A {_} {A} ¬¬p with LEM A
... | yes p = p
... | no ¬p = ⊥-elim (¬¬p ¬p)


¬∀⟶∃¬ :  ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} → ¬ (∀ a → B a) → ∃ λ a → ¬ (B a)
¬∀⟶∃¬ {A = A} {B} ¬∀ with LEM (∃ λ a → ¬ B a)
... | (yes p) = p
... | (no ¬p) = ⊥-elim $ ¬∀ (¬¬A⇒A ∘ ¬∃⟶∀¬ ¬p)


postulate State : Set

Event : ∀ {ℓ} → Set (L.suc ℓ)
Event {ℓ} = State → Set ℓ

_∧_ : ∀ {ℓ ℓ'} → Event {ℓ} → Event {ℓ'} → Event
e1 ∧ e2 = λ w → e1 w × e2 w

_∨_ : ∀ {ℓ ℓ'} → Event {ℓ} → Event {ℓ'} → Event
e1 ∨ e2 = λ w → e1 w ⊎ e2 w

_⟶_ : ∀ {ℓ ℓ'} → Event {ℓ} → Event {ℓ'} → Event
e1 ⟶ e2 = λ w → e1 w → e2 w

_⇒_ : ∀ {ℓ ℓ'} → Event {ℓ} → Event {ℓ'} → Set _
e1 ⇒ e2 = ∀ w → e1 w → e2 w

~_ : ∀ {ℓ} → Event {ℓ} → Event
~ e = λ w → e w → ⊥

All : ∀ {ℓ} → Event {ℓ} → Set _
All e = ∀ w → e w

⇒All⟶ : ∀ {ℓ ℓ'} (e1 : Event {ℓ}) (e2 : Event {ℓ'}) → e1 ⇒ e2 → All (e1 ⟶ e2)
⇒All⟶ e1 e2 e1⇒e2 w e1w = e1⇒e2 w e1w

mapE : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} → (Event {ℓ'} → Event {ℓ''}) → (X → Event) → X → Event {ℓ''}
mapE K E = λ n → K (E n)

_⊂_ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} → (X → Event {ℓ'}) → Event {ℓ''} → Set (ℓ ⊔L ℓ' ⊔L ℓ'')
_⊂_ {X = X} E e = ∀ w → (∀ (x : X) → E x w) → e w

⇒Trans : ∀ {ℓ ℓ' ℓ''} {e1 : Event {ℓ}} {e2 : Event {ℓ'}} {e3 : Event {ℓ''}} → e1 ⇒ e2 → e2 ⇒ e3 → e1 ⇒ e3
⇒Trans e1⇒e2 e2⇒e3 w e1w = e2⇒e3 w (e1⇒e2 w e1w)

⊂Trans : ∀ {ℓ ℓ' ℓ'' ℓ'''} {X : Set ℓ} {E : X → Event {ℓ'}} {e1 : Event {ℓ''}} {e2 : Event {ℓ'''}} →
  E ⊂ e1 → e1 ⇒ e2 → E ⊂ e2
⊂Trans E⊂e1 e1⇒e2 w ∀xExw = e1⇒e2 w (E⊂e1 w ∀xExw)

-- Definition of preservation of semantic implication.
Sem⊂ : ∀ {ℓ ℓ' ℓ''} → (Event {ℓ'} → Event {ℓ''}) → Set (L.suc (ℓ ⊔L ℓ') ⊔L ℓ'')
Sem⊂ {ℓ} {ℓ'} {ℓ''} K = ∀ {X : Set ℓ} {E : X → Event {ℓ'}} {e : Event {ℓ'}} → _⊂_ {ℓ} {ℓ'} {ℓ'} E e → (mapE K E) ⊂ K e

-- Knowledge Operators
record KOp {ℓ ℓ'} (K : Event {ℓ} → Event {ℓ}) : Set (L.suc (ℓ ⊔L ℓ')) where
  field
    axiomN : ∀ {e} → All e → All (K e)
    axiomK : ∀ {e1 e2} → K (e1 ⟶ e2) ⇒ (K e1 ⟶ K e2)
    axiomT : ∀ {e} → K e ⇒ e
    axiom4 : ∀ {e} → K e ⇒ K (K e)
    axiom5 : ∀ {e} → (~ K e) ⇒ K (~ K e)
    -- Infinitary deduction
    axiomInf : Sem⊂ {ℓ'} K


-- axiomN follows from axiomInf, using the empty family
emptyFam : ∀ {ℓ} → ⊥ → Event {ℓ}
emptyFam ()

All_emptyFam : ∀ {ℓ ℓ'} (e : Event {ℓ}) → All e → (emptyFam {ℓ'}) ⊂ e
All_emptyFam e Alle w ∀xExw = Alle w

emptyFam_All : ∀ {ℓ ℓ'} (e : Event {ℓ}) → (emptyFam {ℓ'}) ⊂ e → All e
emptyFam_All e emptyFam⊂e w = emptyFam⊂e w (λ x → ⊥-elim x)

infN : ∀ {ℓ ℓ'} → (K : Event {ℓ} → Event {ℓ'}) → Sem⊂ K → ∀ e → All e → All (K e)
infN {ℓ} K Sem⊂K e Alle = emptyFam_All (K e) aux
  where
    aux : (emptyFam {ℓ}) ⊂ (K e)
    aux w _ = Sem⊂K (All_emptyFam e Alle) w (λ x → ⊥-elim x)

-- Similarly, axiomK follows from axiomInf using a family with two members:
-- A "modus ponens" family.
mpFam : ∀ {ℓ ℓ'} (e1 : Event {ℓ ⊔L ℓ'}) (e2 : Event {ℓ'}) → Bool → Event {ℓ ⊔L ℓ'}
mpFam e1 e2 = λ b → if b then (e1 ⟶ e2) else e1

infK : ∀ {ℓ} → (K : Event {ℓ} → Event {ℓ}) → Sem⊂ K →
  ∀ (e1 : Event {ℓ}) (e2 : Event {ℓ}) → K (e1 ⟶ e2) ⇒ (K e1 ⟶ K e2)
infK {ℓ} K Sem⊂K e1 e2 w Ke1⟶e2w Ke1w = Sem⊂K {E = mpFam {ℓ} e1 e2} aux₁ w aux₂
  where
    aux₁ : mpFam {ℓ} e1 e2 ⊂ e2
    aux₁ w ∀x⦃e1⟶e2,e1⦄xw = ∀x⦃e1⟶e2,e1⦄xw true (∀x⦃e1⟶e2,e1⦄xw false)

    aux₂ : (x : Bool) → mapE K (mpFam {ℓ} e1 e2) x w
    aux₂ true = Ke1⟶e2w
    aux₂ false = Ke1w

natK : ∀ {ℓ ℓ'} {X : Set ℓ'} {K : Event {ℓ} → Event {ℓ}} → KOp {ℓ} {ℓ'} K →
  ∀ {E : X → Event} {e} → E ⊂ e → (mapE K E) ⊂ (K e)
natK KOpK E⊂e = KOp.axiomInf KOpK E⊂e

K⇒ : ∀ {ℓ ℓ'} {K : Event {ℓ} → Event {ℓ}} → KOp {ℓ} {ℓ'} K →
  ∀ {e1 e2} → e1 ⇒ e2 → (K e1) ⇒ (K e2)
K⇒ KOpK {e1} {e2} e1⇒e2 w Ke1w = KOp.axiomK KOpK {e1} {e2} w (KOp.axiomN KOpK e1⇒e2 w) Ke1w

~e⇒K~Ke : ∀ {ℓ ℓ'} {K : Event {ℓ} → Event {ℓ}} → KOp {ℓ} {ℓ'} K →
  ∀ {e} → (~ e) ⇒ K (~ K e)
~e⇒K~Ke KOpK {e} w ~ew = KOp.axiom5 KOpK w (λ Kew → ~ew (KOp.axiomT KOpK {e} w Kew))


-- COINDUCTIVE DEFINITION OF COMMON KNOWLEDGE
postulate Agent : Set
postulate an_agent : Agent

postulate 𝕂 : ∀ {ℓ} → Agent → Event {ℓ} → Event {ℓ}
postulate 𝕂KOp : ∀ {ℓ ℓ'} a → KOp {ℓ} {ℓ'} (𝕂 a)

𝕂⇒ : ∀ {ℓ} {e1 : Event {ℓ}} {e2 : Event {ℓ}} {i : Agent} → e1 ⇒ e2 → 𝕂 i e1 ⇒ 𝕂 i e2
𝕂⇒ {ℓ} {e1} {e2} {i} e1⇒e2 w 𝕂ie1w =
  KOp.axiomK (𝕂KOp {ℓ} {ℓ} i) {e1} {e2} w (KOp.axiomN (𝕂KOp {ℓ} {ℓ} i) e1⇒e2 w) 𝕂ie1w

-- Everybody Knows
EK : ∀ {ℓ ℓ'} {K : Agent → Event {ℓ} → Event {ℓ'}} → Event → Event
EK {ℓ} {ℓ'} {K} e = λ w → ∀ {i : Agent} → K i e w

E𝕂 : ∀ {ℓ} → Event {ℓ} → Event {ℓ}
E𝕂 = EK {K = 𝕂}

-- Common Knowledge
-- Coinductive Definition

record cCK {ℓ} {K : Agent → Event {ℓ} → Event {ℓ}} (e : Event {ℓ}) (w : State) : Set ℓ where
  coinductive
  field
    intro : (EK {ℓ} {ℓ} {K} e ∧ cCK {ℓ} {K} (EK {ℓ} {ℓ} {K} e)) w

cC𝕂 : ∀ {ℓ} → Event {ℓ} → Event {ℓ}
cC𝕂 = cCK {K = 𝕂}

cCK⇒EK : ∀ {ℓ} {e : Event {ℓ}} {K : Agent → Event {ℓ} → Event {ℓ}} →
  cCK {K = K} e ⇒ EK {K = K} e
cCK⇒EK w cCKe = proj₁ (cCK.intro cCKe)

cCK⇒cCKEK : ∀ {ℓ} {e : Event {ℓ}} {K : Agent → Event {ℓ} → Event {ℓ}} →
  cCK {K = K} e ⇒ cCK {K = K} (EK {K = K} e)
cCK⇒cCKEK w cCKe = proj₂ (cCK.intro cCKe)

-- knowledge operator properties of E𝕂
E𝕂axiomInf : ∀ {ℓ ℓ'} → Sem⊂ {ℓ'} (E𝕂 {ℓ})
E𝕂axiomInf {X = X} {E} {e} E⊂e w ∀xEKExw {i} =
  KOp.axiomInf (𝕂KOp i) {X} {E} {e} E⊂e w (λ x → ∀xEKExw x)

E𝕂axiomN : ∀ {ℓ} {e : Event {ℓ}} →
  All e → All (E𝕂 e)
E𝕂axiomN {ℓ} Alle w {i} = KOp.axiomN (𝕂KOp {ℓ} {ℓ} i) Alle w

E𝕂axiomK : ∀ {ℓ} {e1 e2 : Event {ℓ}} →
  E𝕂 (e1 ⟶ e2) ⇒ (E𝕂 e1 ⟶ E𝕂 e2)
E𝕂axiomK {ℓ} {e1 = e1} {e2} w E𝕂e1⟶e2w E𝕂e1w {i} =
  KOp.axiomK (𝕂KOp {ℓ} {ℓ} i) {e1} w E𝕂e1⟶e2w E𝕂e1w

E𝕂axiomT : ∀ {ℓ} {e : Event {ℓ}} → E𝕂 e ⇒ e
E𝕂axiomT {ℓ} w E𝕂ew = KOp.axiomT (𝕂KOp {ℓ} {ℓ} an_agent) w E𝕂ew

E𝕂⇒ : ∀ {ℓ} {e1 e2 : Event {ℓ}} → e1 ⇒ e2 → E𝕂 e1 ⇒ E𝕂 e2
E𝕂⇒ e1⇒e2 w E𝕂e1w = 𝕂⇒ e1⇒e2 w E𝕂e1w

-- EK_axiom4 doesn't hold - if it did, (EK e) would imply (EK (EK e)),
-- and applying this ad infinitum would imply (cCK e)

E𝕂cC𝕂 : ∀ {ℓ} {e : Event {ℓ}} → e ⇒ E𝕂 e → e ⇒ cC𝕂 e
cCK.intro (E𝕂cC𝕂 {e} e⇒E𝕂e w ew) = e⇒E𝕂e w ew , E𝕂cC𝕂 (E𝕂⇒ e⇒E𝕂e) w (e⇒E𝕂e w ew)

~K⇒~EK : ∀ {ℓ} {e : Event {ℓ}} {K : Agent → Event {ℓ} → Event {ℓ}} {a} →
  (~ K a e) ⇒ (~ EK {K = K} e)
~K⇒~EK w ~Kae EKew = ~Kae EKew

𝕂~𝕂⇒𝕂~E𝕂 : ∀ {ℓ} {e : Event {ℓ}} {a} → 𝕂 a (~ 𝕂 a e) ⇒ 𝕂 a (~ E𝕂 e)
𝕂~𝕂⇒𝕂~E𝕂 = 𝕂⇒ (~K⇒~EK {K = 𝕂})

~e⇒E𝕂~E𝕂 : ∀ {ℓ} {e : Event {ℓ}} → (~ e) ⇒ E𝕂 (~ E𝕂 e)
~e⇒E𝕂~E𝕂 {ℓ} w ~ew {i} = 𝕂~𝕂⇒𝕂~E𝕂 w (~e⇒K~Ke (𝕂KOp {ℓ} {ℓ} i) w ~ew)

-- cCK equivalent of recursive EK

recEK : ∀ {ℓ} {K : Agent → Event {ℓ} → Event {ℓ}} → Event {ℓ} → ℕ → Event {ℓ}
recEK {K = K} e zero = EK {K = K} e
recEK {K = K} e (suc n) = EK {K = K} (recEK {K = K} e n)

recE𝕂 : ∀ {ℓ} → Event {ℓ} → ℕ → Event {ℓ}
recE𝕂 = recEK {K = 𝕂}

recEK-EK≡EK-recEK : ∀ {ℓ} {K : Agent → Event {ℓ} → Event {ℓ}} (e : Event {ℓ}) n →
  recEK {K = K} (EK {K = K} e) n ≡ EK {K = K} (recEK {K = K} e n)
recEK-EK≡EK-recEK _ zero = refl
recEK-EK≡EK-recEK {K = K} e (suc n) = cong (EK {K = K}) (recEK-EK≡EK-recEK {K = K} e n)

cCK⇒recEK : ∀ {ℓ} {K : Agent → Event {ℓ} → Event {ℓ}} (e : Event {ℓ}) n →
  cCK {K = K} e ⇒ recEK {K = K} e n
cCK⇒recEK e zero w cCKew {i} = proj₁ (cCK.intro cCKew)
cCK⇒recEK {K = K} e (suc n) =
  ⇒Trans {e2 = cCK {K = K} (EK {K = K} e)} cCK⇒cCKEK
    (⇒Trans {e2 = recEK {K = K} (EK {K = K} e) n} ih aux)
  where
    ih : cCK {K = K} (EK {K = K} e) ⇒ recEK {K = K} (EK {K = K} e) n
    ih = cCK⇒recEK (EK {K = K} e) n

    aux : recEK {K = K} (EK {K = K} e) n ⇒ recEK {K = K} e (suc n)
    aux rewrite recEK-EK≡EK-recEK {K = K} e n = λ w EKrecEKenw {i} → EKrecEKenw

recEK⊂cCK : ∀ {ℓ} {K : Agent → Event {ℓ} → Event {ℓ}} (e : Event {ℓ}) →
  (recEK {K = K} e) ⊂ (cCK {K = K} e)
cCK.intro (recEK⊂cCK {K = K} e w ∀xrecEKexw) =
  ∀xrecEKexw zero , ih w (λ n → subst (λ P → P) (aux n) (∀xrecEKexw (suc n)))
  where
    ih : (recEK {K = K} (EK {K = K} e)) ⊂ (cCK {K = K} (EK {K = K} e))
    ih = recEK⊂cCK (EK {K = K} e)

    aux : ∀ n → (EK {K = K} (recEK {K = K} e n)) w ≡ (recEK {K = K} (EK {K = K} e) n) w
    aux n = cong (λ P → P w) {EK {K = K} (recEK {K = K} e n)} {recEK {K = K} (EK {K = K} e) n}
      (sym (recEK-EK≡EK-recEK e n))

-- knowledge operator properties of cCK

E𝕂cC𝕂⇒cC𝕂E𝕂 : ∀ {ℓ} (e : Event {ℓ}) → E𝕂 (cC𝕂 e) ⇒ cC𝕂 (E𝕂 e)
E𝕂cC𝕂⇒cC𝕂E𝕂 e w E𝕂cC𝕂ew = cCK⇒cCKEK w (E𝕂axiomT w E𝕂cC𝕂ew)

cCKEK⇒EKcCK : ∀ {ℓ} {K : Agent → Event {ℓ} → Event {ℓ}} {KOpK : ∀ a -> KOp {ℓ} {L.zero} (K a)} (e : Event {ℓ}) →
  cCK {K = K} (EK {K = K} e) ⇒ EK {K = K} (cCK {K = K} e)
cCKEK⇒EKcCK {K = K} {KOpK} e w cCKEKew {i} =
  natK {X = ℕ} (KOpK i) (recEK⊂cCK e) w
    (λ n → aux n w (subst (λ P → P w)
      {recEK {K = K} (EK {K = K} e) n}
      {EK {K = K} (recEK {K = K} e n)}
      (recEK-EK≡EK-recEK e n)
      (cCK⇒recEK (EK {K = K} e) n w cCKEKew)))
  where
    aux : ∀ n → EK {K = K} (recEK {K = K} e n) ⇒ mapE (K i) (recEK {K = K} e) n
    aux n w EKrecEKen = EKrecEKen

cCK⇒EKcCK : ∀ {ℓ} {K : Agent → Event {ℓ} → Event {ℓ}} (KOpK : ∀ a -> KOp {ℓ} {L.zero} (K a)) (e : Event {ℓ}) →
  cCK {K = K} e ⇒ EK {K = K} (cCK {K = K} e)
cCK⇒EKcCK {K = K} KOpK e = ⇒Trans {e2 = cCK {K = K} (EK {K = K} e)} cCK⇒cCKEK (cCKEK⇒EKcCK {K = K} {KOpK} e)

E𝕂recE𝕂 : ∀ {ℓ} (e1 e2 : Event {ℓ}) n → e1 ⇒ E𝕂 e2 → recE𝕂 e1 n ⇒ recE𝕂 e2 (suc n)
E𝕂recE𝕂 e1 e2 zero    e1⇒E𝕂e2 w recE𝕂e1nw {i} = E𝕂⇒ {e1 = e1} e1⇒E𝕂e2 w recE𝕂e1nw
E𝕂recE𝕂 e1 e2 (suc n) e1⇒E𝕂e2 w recE𝕂e1nw {i} = E𝕂⇒ {e1 = recEK e1 n} ih w recE𝕂e1nw
  where
    ih : recE𝕂 e1 n ⇒ recE𝕂 e2 (suc n)
    ih = E𝕂recE𝕂 e1 e2 n e1⇒E𝕂e2

cC𝕂⇒recE𝕂cC𝕂 : ∀ {ℓ} (e : Event {ℓ}) n → cC𝕂 e ⇒ recE𝕂 (cC𝕂 e) n
cC𝕂⇒recE𝕂cC𝕂 e zero = cCK⇒EKcCK 𝕂KOp e
cC𝕂⇒recE𝕂cC𝕂 e (suc n) = ⇒Trans {e2 = E𝕂 (cC𝕂 e)} (cCK⇒EKcCK 𝕂KOp e) ih
  where
    ih : E𝕂 (cC𝕂 e) ⇒ E𝕂 (recE𝕂 (cC𝕂 e) n)
    ih = E𝕂⇒ (cC𝕂⇒recE𝕂cC𝕂 e n)

cC𝕂axiomInf : ∀ {ℓ ℓ'} → Sem⊂ {ℓ} {ℓ'} {ℓ'} cC𝕂
cCK.intro (cC𝕂axiomInf {X = X} {E} {e} E⊂e w mapEcC𝕂E) =
  E𝕂axiomInf {X = X} {E} E⊂e w (λ x → cCK⇒EK w (mapEcC𝕂E x)) ,
  cC𝕂axiomInf {E = λ x → E𝕂 (E x)} (E𝕂axiomInf {X = X} {E} E⊂e) w (λ x → cCK⇒cCKEK w (mapEcC𝕂E x))

cC𝕂axiom4 : ∀ {ℓ} {e : Event {ℓ}} → cC𝕂 e ⇒ cC𝕂 (cC𝕂 e)
cC𝕂axiom4 {e = e} w cC𝕂e = recEK⊂cCK (cC𝕂 e) w ((λ n → cC𝕂⇒recE𝕂cC𝕂 e n w cC𝕂e))

cC𝕂axiomN : ∀ {ℓ} {e : Event {ℓ}} → All e → All (cC𝕂 e)
cC𝕂axiomN {e = e} = infN cC𝕂 cC𝕂axiomInf e

cC𝕂axiomT : ∀ {ℓ} {e : Event {ℓ}} → cC𝕂 e ⇒ e
cC𝕂axiomT w cC𝕂ew = E𝕂axiomT w (proj₁ (cCK.intro cC𝕂ew))

cC𝕂axiomK : ∀ {ℓ} {e1 e2 : Event {ℓ}} → cC𝕂 (e1 ⟶ e2) ⇒ (cC𝕂 e1 ⟶ cC𝕂 e2)
cC𝕂axiomK {_} {e1} {e2} = infK cC𝕂 cC𝕂axiomInf e1 e2


~cC𝕂⇒E𝕂~cC𝕂 : ∀ {ℓ} {e : Event {ℓ}} → (~ cC𝕂 e) ⇒ E𝕂 (~ cC𝕂 e)
~cC𝕂⇒E𝕂~cC𝕂 {e = e} w ~cC𝕂ew = cut (λ ∀nrecE𝕂enw → ~cC𝕂ew (recEK⊂cCK e w ∀nrecE𝕂enw))
  where
    cut : (¬(∀ n → recE𝕂 e n w)) → E𝕂 (~ cC𝕂 e) w
    cut ¬∀nrecE𝕂enw = E𝕂⇒ {e1 = ~ recE𝕂 e (suc n)}
      (λ w ~recE𝕂eSn cC𝕂ew → ~recE𝕂eSn (cCK⇒recEK e (suc n) w cC𝕂ew))
      w
      (~e⇒E𝕂~E𝕂 w ¬recE𝕂enw)
      where
        neg : ∃ (λ n → ¬ (recE𝕂 e n w))
        neg = ¬∀⟶∃¬ ¬∀nrecE𝕂enw

        n = proj₁ neg
        ¬recE𝕂enw = proj₂ neg

cC𝕂axiom5 : ∀ {ℓ} {e : Event {ℓ}} → (~ cC𝕂 e) ⇒ cC𝕂 (~ cC𝕂 e)
cC𝕂axiom5 = E𝕂cC𝕂 ~cC𝕂⇒E𝕂~cC𝕂


cC𝕂KOp : ∀ {ℓ ℓ'} → KOp {ℓ} {ℓ'} cC𝕂
cC𝕂KOp = record {
    axiomN = cC𝕂axiomN
  ; axiomK = cC𝕂axiomK
  ; axiomT = cC𝕂axiomT
  ; axiom4 = cC𝕂axiom4
  ; axiom5 = cC𝕂axiom5
  ; axiomInf = cC𝕂axiomInf
  }

-- Equivalence Relations

RelToK : ∀ {ℓ ℓ'} → RelL State ℓ → Event {ℓ'} → Event {ℓ ⊔L ℓ'}
RelToK R e w = ∀ v → R w v → e v

KtoRel : ∀ {ℓ} → (Event → Event {ℓ}) → RelL State (L.suc ℓ)
KtoRel K w v = ∀ e → K e w → K e v

-- Proof that RelToK on an equivalence relation yields a K satisfying S5 *)

axiomN' : ∀ {ℓ ℓ'} → (R : RelL State ℓ) → IsEquivalence R →
  ∀ {e : Event {ℓ'}} → All e → All ((RelToK R) e)
axiomN' _ _ Alle _ v _ = Alle v

axiomK' : ∀ {ℓ ℓ' ℓ''} → (R : RelL State ℓ) → IsEquivalence R →
  ∀ {e1 : Event {ℓ'}} {e2 : Event {ℓ''}} → (RelToK R) (e1 ⟶ e2) ⇒ ((RelToK R) e1 ⟶ (RelToK R) e2)
axiomK' R _ {e1} {e2} w Ke1⟶e2 Ke1w = λ v Rwv → Ke1⟶e2 v Rwv (Ke1w v Rwv)

axiomT' : ∀ {ℓ ℓ'} → (R : RelL State ℓ) → IsEquivalence R →
  ∀ {e : Event {ℓ'}} → (RelToK R) e ⇒ e
axiomT' R IsEqR {e} w Kew = Kew w (IsEquivalence.refl IsEqR)

axiom4' : ∀ {ℓ ℓ'} → (R : RelL State ℓ) → IsEquivalence R →
  ∀ {e : Event {ℓ'}} → (RelToK R) e ⇒ (RelToK R) ((RelToK R) e)
axiom4' R IsEqR {e} w Kew v Rwv u Rvu = Kew u (IsEquivalence.trans IsEqR Rwv Rvu)

axiom5' : ∀ {ℓ ℓ'} → (R : RelL State ℓ) → IsEquivalence R →
  ∀ {e : Event {ℓ'}} → (~ (RelToK R) e) ⇒ (RelToK R) (~ ((RelToK R) e))
axiom5' R IsEqR {e} w ~Kew v Rwv Kev =
  ~Kew (λ u Rwu → Kev u (IsEquivalence.trans IsEqR (IsEquivalence.sym IsEqR Rwv) Rwu))

axiomInf' : ∀ {ℓ ℓ'} → (R : RelL State ℓ) → IsEquivalence R → Sem⊂ {ℓ'} {ℓ} (RelToK R)
axiomInf' R IsEqR E⊂e w ∀x v Rwv = E⊂e v (λ x → ∀x x v Rwv)


KOpRelToK : ∀ {ℓ ℓ'} → (R : RelL State ℓ) → IsEquivalence R → KOp {ℓ} {ℓ'} (RelToK R)
KOpRelToK R IsEqR = record {
    axiomN = axiomN' R IsEqR
  ; axiomK = axiomK' R IsEqR
  ; axiomT = axiomT' R IsEqR
  ; axiom4 = axiom4' R IsEqR
  ; axiom5 = axiom5' R IsEqR
  ; axiomInf = axiomInf' R IsEqR
  }

-- Proof that K_to_Rel on a K satisfying S5 yields an equivalence relation

eqRefl' : ∀ {ℓ ℓ'} → (K : Event {ℓ} → Event) → KOp {ℓ} {ℓ'} K →
  ∀ {w : State} → (KtoRel K) w w
eqRefl' K KopK = λ e Kew → Kew


eqSym' : ∀ {ℓ ℓ'} → (K : Event {ℓ} → Event) → KOp {ℓ} {ℓ'} K →
  ∀ {w v : State} → (KtoRel K) w v → (KtoRel K) v w
eqSym' K KOpK {w} {v} Rwv e Kev = ¬¬A⇒A (λ ¬Kew →
  KOp.axiomT KOpK {~ K e} v (Rwv (~ K e) (KOp.axiom5 KOpK {e} w ¬Kew)) Kev)

eqTrans' : ∀ {ℓ ℓ'} → (K : Event {ℓ} → Event) → KOp {ℓ} {ℓ'} K →
  ∀ {w v u : State} →  (KtoRel K) w v → (KtoRel K) v u → (KtoRel K) w u
eqTrans' K _ {w} {v} {u} Rwv Rvu e Kew = Rvu e (Rwv e Kew)


EqRelKtoRel : ∀ {ℓ ℓ'} → (K : Event {ℓ} → Event) → KOp {ℓ} {ℓ'} K → IsEquivalence (KtoRel K)
EqRelKtoRel K KOpK = record { refl = eqRefl' K KOpK ; sym = eqSym' K KOpK ; trans = eqTrans' K KOpK }

-- The two transformations are an isomorphism

EqRelKIso1 : ∀ {ℓ ℓ'} → {K : Event → Event {ℓ}} → KOp {ℓ} {ℓ'} K →
    ∀ (e : Event {ℓ}) → (K e) ⇒ (RelToK (KtoRel K) e)
EqRelKIso1 {K = K} KOpK e w Kew v Rwv = KOp.axiomT KOpK v (Rwv e Kew)

data Indexed {ℓ ℓ'} (K : Event {ℓ} → Event {ℓ'}) (w : State) : Set (L.suc (ℓ ⊔L ℓ')) where
  index : ∀ (e : Event) → K e w → Indexed K w

KFam : ∀ {ℓ} {K : Event {ℓ} → Event {ℓ}} {w : State} → Indexed K w → Event {ℓ}
KFam {K = K} (index e Kew) = K e



Rew→KFam⊂e : ∀ {ℓ} → {K : Event → Event {ℓ}} →
  ∀ (e : Event {ℓ}) w → RelToK (KtoRel K) e w → (KFam {K = K} {w}) ⊂ e
Rew→KFam⊂e {ℓ} {K} e w R2K-K2Rew v ∀xKFamxv =
  R2K-K2Rew v (λ e' Ke'w → ∀xKFamxv (index e' Ke'w))


EqRelKIso2 : ∀ {ℓ} → {K : Event → Event {ℓ}} → KOp {ℓ} {L.suc ℓ} K →
    ∀ (e : Event {ℓ}) → (RelToK (KtoRel K) e) ⇒ (K e)
EqRelKIso2 {ℓ} {K} KOpK e w R2K-K2Rew = KOp.axiomInf KOpK aux w aux₁
  where
    aux : _⊂_ {L.suc ℓ} {ℓ} {ℓ} (KFam {ℓ} {K} {w}) e
    aux = Rew→KFam⊂e e w R2K-K2Rew

    aux₁ : (x : Indexed K w) → K (KFam x) w
    aux₁ (index e Kew) = KOp.axiom4 KOpK w Kew


KeqRelIso1 : ∀ {ℓ} → (R : RelL State ℓ) → IsEquivalence R →
  ∀ w v → R w v → KtoRel {ℓ} (RelToK R) w v
KeqRelIso1 R IsEqR w v Rwv e R2Kew u Rvu = R2Kew u (IsEquivalence.trans IsEqR Rwv Rvu)

KeqRelIso2 : ∀ {ℓ} → (R : RelL State ℓ) → IsEquivalence R →
  ∀ w v → KtoRel {ℓ} (RelToK R) w v → R w v
KeqRelIso2 R IsEqR w v K2R-R2Kwv = K2R-R2Kwv (R w) (λ v₁ z → z) v (IsEquivalence.refl IsEqR)

-- RELATIONAL DEFINITION OF COMMON KNOWLEDGE

postulate 𝕂R : ∀ {ℓ} → Agent → RelL State ℓ
postulate IsEq𝕂R : ∀ {ℓ} a → IsEquivalence (𝕂R {ℓ} a)

𝕂ᵣ : ∀ {ℓ} (i : Agent) → Event {ℓ} → Event {ℓ}
𝕂ᵣ {ℓ} i = RelToK (𝕂R {ℓ} i)

𝕂ᵣKOp : ∀ {ℓ ℓ'} i -> KOp {ℓ} {ℓ'} (𝕂ᵣ i)
𝕂ᵣKOp i = KOpRelToK (𝕂R i) (IsEq𝕂R i)

𝕂ᵣe→e : ∀ {ℓ} i (e : Event {ℓ}) w → 𝕂ᵣ i e w → e w
𝕂ᵣe→e i e w 𝕂ᵣiew = 𝕂ᵣiew w (IsEquivalence.refl (IsEq𝕂R i))

𝕂ᵣe→𝕂ᵣ𝕂ᵣe : ∀ {ℓ} i (e : Event {ℓ}) w → 𝕂ᵣ i e w → 𝕂ᵣ i (𝕂ᵣ i e) w
𝕂ᵣe→𝕂ᵣ𝕂ᵣe i e w 𝕂ᵣiew v 𝕂Riwv u 𝕂Rivu =
  𝕂ᵣiew u (IsEquivalence.trans (IsEq𝕂R i) 𝕂Riwv 𝕂Rivu)


E𝕂ᵣ : ∀ {ℓ} → Event {ℓ} → Event {ℓ}
E𝕂ᵣ = EK {K = 𝕂ᵣ}

cC𝕂ᵣ : ∀ {ℓ} → Event {ℓ} → Event {ℓ}
cC𝕂ᵣ = cCK {K = 𝕂ᵣ}

cC𝕂ᵣ→E𝕂ᵣcC𝕂ᵣ : ∀ {ℓ} {e : Event {ℓ}} {w : State} → cC𝕂ᵣ e w -> E𝕂ᵣ (cC𝕂ᵣ e) w
cC𝕂ᵣ→E𝕂ᵣcC𝕂ᵣ {ℓ} {e} {w} = cCK⇒EKcCK {K = 𝕂ᵣ} 𝕂ᵣKOp e w

data C𝕂R {ℓ} : RelL State ℓ where
  base : ∀ i w v -> 𝕂R {ℓ} i w v -> C𝕂R w v
  trans : ∀ {w v u} -> C𝕂R {ℓ} w v -> C𝕂R {ℓ} v u -> C𝕂R {ℓ} w u

C𝕂Rrefl : ∀ {ℓ} → Relation.Binary.Core.Reflexive (C𝕂R {ℓ})
C𝕂Rrefl {x = w} = base an_agent w w (IsEquivalence.refl (IsEq𝕂R an_agent))

C𝕂Rsym : ∀ {ℓ} → Relation.Binary.Core.Symmetric (C𝕂R {ℓ})
C𝕂Rsym (base i w v 𝕂Riwv) = base i v w (IsEquivalence.sym (IsEq𝕂R i) 𝕂Riwv)
C𝕂Rsym (trans C𝕂Rwv C𝕂Rvu) = trans (C𝕂Rsym C𝕂Rvu) (C𝕂Rsym C𝕂Rwv)

EqRelC𝕂R : ∀ {ℓ} → IsEquivalence (C𝕂R {ℓ})
EqRelC𝕂R = record { refl = C𝕂Rrefl ; sym = C𝕂Rsym ; trans = trans }

C𝕂ᵣ : ∀ {ℓ} → Event {ℓ} → Event {ℓ}
C𝕂ᵣ {ℓ} = RelToK (C𝕂R {ℓ})

C𝕂ᵣ→E𝕂ᵣ : ∀ {ℓ} {e : Event {ℓ}} {w : State} → C𝕂ᵣ e w -> E𝕂ᵣ e w
C𝕂ᵣ→E𝕂ᵣ {_} {e} {w} C𝕂ᵣew {i} v 𝕂Riwv = C𝕂ᵣew v (base i w v 𝕂Riwv)

C𝕂ᵣ→E𝕂ᵣC𝕂ᵣ : ∀ {ℓ} {e : Event {ℓ}} {w : State} → C𝕂ᵣ e w -> E𝕂ᵣ (C𝕂ᵣ e) w
C𝕂ᵣ→E𝕂ᵣC𝕂ᵣ {_} {e} {w} C𝕂ᵣew {i} v 𝕂Riwv u C𝕂Rvu =
  C𝕂ᵣew u (trans (base i w v 𝕂Riwv) C𝕂Rvu)

C𝕂ᵣ→C𝕂ᵣE𝕂ᵣ : ∀ {ℓ} {e : Event {ℓ}} {w : State} → C𝕂ᵣ e w -> C𝕂ᵣ (E𝕂ᵣ e) w
C𝕂ᵣ→C𝕂ᵣE𝕂ᵣ {_} {e} {w} C𝕂ᵣew v C𝕂Rwv {i} u 𝕂Rivu =
  C𝕂ᵣew u (trans C𝕂Rwv (base i v u 𝕂Rivu))


C𝕂ᵣ→cC𝕂ᵣ : ∀ {ℓ} {e : Event {ℓ}} {w : State} → C𝕂ᵣ e w -> cC𝕂ᵣ e w
cCK.intro (C𝕂ᵣ→cC𝕂ᵣ {ℓ} {e} {w} C𝕂ᵣew) = C𝕂ᵣ→E𝕂ᵣ C𝕂ᵣew , C𝕂ᵣ→cC𝕂ᵣ (C𝕂ᵣ→C𝕂ᵣE𝕂ᵣ C𝕂ᵣew)

C𝕂transport : ∀ {ℓ} {e : Event {ℓ}} {w v : State} → cC𝕂ᵣ e w -> C𝕂R {ℓ} w v -> cC𝕂ᵣ e v
C𝕂transport {_} {e} cC𝕂ᵣew (base i w v 𝕂Riwv) = record { intro =
    proj₁ (cCK.intro (proj₂ (cCK.intro cC𝕂ᵣew))) v 𝕂Riwv ,
    aux v 𝕂Riwv
  }
  where
    aux : E𝕂ᵣ (cC𝕂ᵣ (E𝕂ᵣ e)) w
    aux = cC𝕂ᵣ→E𝕂ᵣcC𝕂ᵣ (record { intro = cCK.intro (proj₂ (cCK.intro cC𝕂ᵣew)) })
C𝕂transport cC𝕂ᵣew (trans C𝕂Rwv C𝕂Rvu) =
  C𝕂transport (C𝕂transport cC𝕂ᵣew C𝕂Rwv) C𝕂Rvu

cC𝕂ᵣ→C𝕂ᵣ : ∀ {ℓ} {e : Event {ℓ}} {w : State} → cC𝕂ᵣ e w -> C𝕂ᵣ e w
cC𝕂ᵣ→C𝕂ᵣ {ℓ} {e} cC𝕂ᵣew v (base i w .v x) = proj₁ (cCK.intro cC𝕂ᵣew) v x
cC𝕂ᵣ→C𝕂ᵣ {ℓ} {e} {w} cC𝕂ᵣew v (trans {v = v'} C𝕂Rwv' C𝕂Rv'v) =
  cC𝕂ᵣ→C𝕂ᵣ (C𝕂transport cC𝕂ᵣew C𝕂Rwv') v C𝕂Rv'v

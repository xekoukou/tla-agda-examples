module DIE_HARD where

open import TLA.Def


open import Data.Nat
open import Relation.Nullary
open import Data.Vec hiding ([_])
open import Data.Unit using (⊤ ; tt)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (case_of_)
open import Level renaming (zero to lzero ; suc to lsuc ; Lift to ℓ↑)

open import LTL.Core
open import LTL.Stateless

DHVars = ℕ ∷ ℕ ∷ []

fillSmall : Action ⊤ DHVars
cond fillSmall e sys = ⊤
resp fillSmall e (small , big) (small' , big') = (small' ≡ 3) × (big' ≡ big)

fillBig : Action ⊤ DHVars
cond fillBig e sys = ⊤
resp fillBig e (small , big , _) (small' , big' , _) = (small' ≡ small) × (big' ≡ 5)

emptySmall : Action ⊤ DHVars
cond emptySmall e sys = ⊤
resp emptySmall e (small , big) (small' , big') = (small' ≡ 0) × (big' ≡ big)

emptyBig : Action ⊤ DHVars
cond emptyBig e sys = ⊤
resp emptyBig e (small , big , _) (small' , big' , _ ) = (small' ≡ small) × (big' ≡ 0)

smallToBig : Action ⊤ DHVars
cond smallToBig e sys = ⊤
resp smallToBig e (small , big , _) (small' , big' , _)
  = case (small + big ≤? 5) of
      λ { (yes _) → big' ≡ big + small × small' ≡ 0
        ; (no _) → big' ≡ 5 × small' ≡ small ∸ (5 ∸ big)}


bigToSmall : Action ⊤ DHVars
cond bigToSmall e sys = ⊤
resp bigToSmall e (small , big , _) (small' , big' , _)
  = case (small + big ≤? 3) of
      λ { (yes _) → small' ≡ big + small × big' ≡ 0
        ; (no _) → small' ≡ 3 × big' ≡ big ∸ (3 ∸ small)}


DHE = V⊤ 7

DHSpec : Spec DHVars DHE
DHSpec = fillSmall ∷ₛₚ fillBig ∷ₛₚ emptySmall ∷ₛₚ emptyBig
         ∷ₛₚ smallToBig ∷ₛₚ bigToSmall ∷ₛₚ stAction ∷ₛₚ []ₛₚ

TypeOK : System DHVars → Set
TypeOK (fst , snd , _) 
  =   fst ≥ 0 × fst ≤ 3
    × snd ≥ 0 × snd ≤ 5



TypeOKInd : (beh : (System DHVars) ʷ) → (pe : (DHE toUS) ʷ)
            → [ (DHSpec $ₛₚₜ pe) beh ⇒ ⟨ TypeOK ⟩ $ beh ⇒ ⟨ TypeOK ⟩ $ (○ beh) ]
TypeOKInd beh pe n rst ptok with pe n | beh n | beh (suc n)
TypeOKInd beh pe n (_ , refl , refl) (a , b , c , d) | e ←u | sys | .3 , .(snd sys)
  = {!!} , ({!!} , (c , d))
TypeOKInd beh pe n rst ptok | u→ (e ←u) | sys | nsys = {!!}
TypeOKInd beh pe n rst ptok | u→ (u→ pen) | sys | nsys = {!!}

TypeOK! : (beh : (System DHVars) ʷ)
          → (init : fst (! beh) ≡ 0 × fst (snd (! beh)) ≡ 0 ) → ! ( ⟨ TypeOK ⟩ $ beh )
TypeOK! beh (fst , snd) = {!!} , {!!}


TypeOKProof : (beh : (System DHVars) ʷ) → (pe : (DHE toUS) ʷ)
         → (init : fst (! beh) ≡ 0 × fst (snd (! beh)) ≡ 0 ) → [ (DHSpec $ₛₚₜ pe) beh ] → [ ⟨ TypeOK ⟩ $ beh ]
TypeOKProof beh pe init rst = indn (TypeOKInd beh pe $ rst) (TypeOK! beh init)

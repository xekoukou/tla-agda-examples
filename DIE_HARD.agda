module DIE_HARD where

open import TLA.Def


open import Prelude.Nat
open import Prelude.Bool
open import Prelude.Ord
open import Prelude.Semiring
open import Prelude.Function using (case_of_)


open import LTL.Stateless

DHVars = Nat ∷ Nat ∷ []

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
      λ { true → big' ≡ big + small × small' ≡ 0
        ; false → big' ≡ 5 × small' ≡ small - (5 - big)}


bigToSmall : Action ⊤ DHVars
cond bigToSmall e sys = ⊤
resp bigToSmall e (small , big , _) (small' , big' , _)
  = case (small + big ≤? 3) of
      λ { true → small' ≡ big + small × big' ≡ 0
        ; false → small' ≡ 3 × big' ≡ big - (3 - small)}


DHE = V⊤ 6

DHSpec : Spec DHVars DHE
DHSpec = fillSmall ∷ₛₚ fillBig ∷ₛₚ emptySmall ∷ₛₚ emptyBig
         ∷ₛₚ smallToBig ∷ₛₚ bigToSmall ∷ₛₚ []ₛₚ

TypeOK : System DHVars → Set
TypeOK (fst , snd , _) 
  =   fst ≥ 0 × fst ≤ 3
    × snd ≥ 0 × snd ≤ 5



TypeOKInd : (beh : (System DHVars) ʷ) → (pe : (DHE toUS) ʷ)
            → [ Restr DHSpec beh pe ⇒ ⟨ TypeOK ⟩ $ʷ beh ⇒ ⟨ TypeOK ⟩ $ʷ (○ beh) ]
TypeOKInd beh pe n rst ptok with pe n | beh n | beh (suc n)
TypeOKInd beh pe n (u→ refl) ptok | pen | sys | .sys = ptok
TypeOKInd beh pe n ((_ , refl , refl) ←u) (a , b , c , d) | e ←u | sys | .3 , .(snd sys)
  = {!!} , ({!!} , (c , d))
TypeOKInd beh pe n (rst ←u) ptok | u→ (e ←u) | sys | nsys = {!!}
TypeOKInd beh pe n (rst ←u) ptok | u→ (u→ pen) | sys | nsys = {!!}

TypeOK! : (beh : (System DHVars) ʷ)
          → (init : fst (! beh) ≡ 0 × fst (snd (! beh)) ≡ 0 ) → ! ( ⟨ TypeOK ⟩ $ʷ beh )
TypeOK! beh (fst , snd) = {!!} , {!!}


TypeOKProof : (beh : (System DHVars) ʷ) → (pe : (DHE toUS) ʷ)
         → (init : fst (! beh) ≡ 0 × fst (snd (! beh)) ≡ 0 ) → [ Restr DHSpec beh pe ] → [ ⟨ TypeOK ⟩ $ʷ beh ]
TypeOKProof beh pe init rst = indn (TypeOKInd beh pe $ʷ rst) (TypeOK! beh init)

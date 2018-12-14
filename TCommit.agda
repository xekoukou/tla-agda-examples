module TCommit where

open import Data.Nat
open import Data.Fin
open import Data.Sum
open import Relation.Nullary
open import Data.Empty
open import Data.Vec hiding ([_])
open import Data.Unit using (⊤ ; tt)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (case_of_)
open import Data.Product.Relation.Pointwise.NonDependent

open import TLA.Def
open import TLA.Utils

variable
  RM : ℕ
  
data RMState : Set where
  working prepared committed aborted : RMState


rmDec : (a b : RMState) → Dec (a ≡ b)
rmDec working working = yes refl
rmDec working prepared = no (λ ())
rmDec working committed = no (λ ())
rmDec working aborted = no (λ ())
rmDec prepared working = no (λ ())
rmDec prepared prepared = yes refl
rmDec prepared committed = no (λ ())
rmDec prepared aborted = no (λ ())
rmDec committed working = no (λ ())
rmDec committed prepared = no (λ ())
rmDec committed committed = yes refl
rmDec committed aborted = no (λ ())
rmDec aborted working = no (λ ())
rmDec aborted prepared = no (λ ())
rmDec aborted committed = no (λ ())
rmDec aborted aborted = yes refl


TCVars : (RM : ℕ) → VSet RM
TCVars RM = VS RMState RM

rmDecV : {RM : ℕ} → (a b : System (TCVars RM)) → Dec (a ≡ b)
rmDecV {zero} a b = yes refl
rmDecV {suc RM} a b
  = case rmDecV (snd a) (snd b) of
      λ { (yes p) → case rmDec (fst a) (fst b)
                      of λ { (yes q) → yes (≡×≡⇒≡ (q , p))
                           ; (no ¬q) → no λ { refl → ⊥-elim (¬q refl)}}
        ; (no ¬p) → no (λ {refl → ⊥-elim (¬p refl)})}


TCInit : System (TCVars RM) → Set
TCInit {zero} sys = ⊤
TCInit {suc RM} sys = fst sys ≡ working × TCInit (snd sys)


canCommit : System (TCVars RM) → Set
canCommit {RM} sys = (e : Fin RM) → (sys at e ≡ prepared) ⊎ (sys at e ≡ committed)

canCommit′ : System (TCVars RM) → (e : Fin RM) →  Set
canCommit′ sys e = (sys at e ≡ prepared) ⊎ (sys at e ≡ committed)


notCommitted : System (TCVars RM) → Set
notCommitted {RM} sys = (e : Fin RM) → ¬ (sys at e ≡ committed)


Prepare : Action (Fin RM) (TCVars RM)
cond (Prepare {zero}) ()
cond (Prepare {suc RM}) e sys = sys at e ≡ working
resp (Prepare {zero}) ()
resp (Prepare {suc RM}) e sys nsys = nsys ≡ sys Except e != λ v nv → nv ≡ prepared


Decide : Action (Fin RM) (TCVars RM)
cond (Decide {zero}) ()
cond (Decide {suc RM}) e sys
  =   (sys at e ≡ prepared × canCommit sys)
    ⊎ notCommitted sys
resp (Decide {zero}) ()
resp (Decide {suc RM}) e sys nsys
  =  nsys ≡ sys Except e != λ v nv →   v ≡ prepared × canCommit sys × nv ≡ committed
                                     ⊎ notCommitted sys × nv ≡ aborted 



TCE : ℕ → (k : ℕ) → VSet k
TCE RM k = VS (Fin RM) k

tcspec : Spec (TCVars RM) (⊤ ∷ TCE RM 2)
tcspec = stAction ∷ₛₚ Prepare ∷ₛₚ Decide ∷ₛₚ []ₛₚ

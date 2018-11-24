module TCommit where

open import Data.Nat
open import Data.Fin
open import Data.Sum
open import Relation.Nullary
open import Data.Vec hiding ([_])
open import Data.Unit using (⊤ ; tt)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (case_of_)


open import TLA.Def
open import TLA.Utils

variable
  RM : ℕ
  
data RMState : Set where
  working prepared committed aborted : RMState

TCVars : (RM : ℕ) → VSet RM
TCVars RM = VS RMState RM


-- Should I use Heterogeneous Equality here ?

TCInit : System (TCVars RM) → Set
TCInit {zero} sys = ⊤
TCInit {suc RM} sys = fst sys ≡ working × TCInit (snd sys)


canCommit : System (TCVars RM) → Set
canCommit {zero} sys = ⊤
canCommit {suc RM} sys = ((fst sys ≡ prepared) ⊎ (fst sys ≡ committed)) × canCommit (snd sys)

notCommitted : System (TCVars RM) → Set
notCommitted {zero} sys = ⊤
notCommitted {suc RM} sys = (¬ (fst sys ≡ committed)) × canCommit (snd sys)



Prepare : Action (Fin RM) (TCVars RM)
cond (Prepare {zero}) ()
cond (Prepare {suc RM}) zero sys = fst sys ≡ working
cond (Prepare {suc RM}) (suc e) sys = cond Prepare e (snd sys)
resp (Prepare {zero}) ()
resp (Prepare {suc RM}) zero sys nsys = fst nsys ≡ prepared
resp (Prepare {suc RM}) (suc e) sys nsys = resp Prepare e (snd sys) (snd nsys)


Decide : Action (Fin RM) (TCVars RM)
cond (Decide {zero}) ()
cond (Decide {suc RM}) zero sys
  =   (fst sys ≡ prepared
      × canCommit sys)
    ⊎ (((fst sys ≡ prepared) ⊎ (fst sys ≡ working))
      × notCommitted sys)
cond (Decide {suc RM}) (suc e) sys = cond Decide e (snd sys)
resp (Decide {zero}) ()
resp (Decide {suc RM}) zero sys nsys
  =   (fst sys ≡ prepared
      × canCommit sys
      × fst nsys ≡ committed)
    ⊎ (((fst sys ≡ prepared) ⊎ (fst sys ≡ working))
      × notCommitted sys
      × fst nsys ≡ aborted)
resp (Decide {suc RM}) (suc e) sys nsys = fst sys ≡ fst nsys × resp Decide e (snd sys) (snd nsys)

TCE : ℕ → VSet 2
TCE RM = VS (Fin RM) 2

TCSpec : Spec (TCVars RM) (TCE RM)
TCSpec = Prepare ∷ₛₚ Decide ∷ₛₚ []ₛₚ

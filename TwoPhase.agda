module TwoPhase where

open import Data.List
open import Relation.Binary
open import Data.Nat hiding (_≟_)
open import Data.Fin hiding (_+_ )
open import Data.Sum
open import Relation.Nullary
open import Data.Vec hiding ([_] ; init)
open import Data.Unit using (⊤ ; tt)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (case_of_)

open import TLA.Def
open import TLA.Utils
open import TLA.Refine

open import TCommit


data Message (RM : ℕ) : Set where
  _isPrepared : (r : Fin RM) → Message RM
  doCommit : Message RM
  doAbort : Message RM


decMsg : (RM : ℕ) → Decidable {A = Message RM} _≡_
decMsg RM (x isPrepared) (y isPrepared) with (x ≟ y)
decMsg RM (x isPrepared) (y isPrepared) | yes p = yes (cong _isPrepared p)
decMsg RM (x isPrepared) (y isPrepared) | no ¬p = no λ { refl → ¬p refl}
decMsg RM (x isPrepared) doCommit = no (λ ())
decMsg RM (x isPrepared) doAbort = no (λ ())
decMsg RM doCommit (x isPrepared) = no (λ ())
decMsg RM doCommit doCommit = yes refl
decMsg RM doCommit doAbort = no (λ ())
decMsg RM doAbort (x isPrepared) = no (λ ())
decMsg RM doAbort doCommit = no (λ ())
decMsg RM doAbort doAbort = yes refl

module _ {RM : ℕ} where
  open import Data.List.Membership.DecPropositional (decMsg RM)
  _∈?ₘ_ = _∈?_
  _∈ₘ_ = _∈_

module _ {RM : ℕ} where
  open import Data.List.Membership.DecPropositional (_≟_ {n = RM})
  _∈?ᶠ_ = _∈?_
  _∈ᶠ_ = _∈_


data TMState : Set where
  init done : TMState

TMPrepared : (RM : ℕ) → Set
TMPrepared RM = List (Fin RM)

Msgs : (RM : ℕ) → Set
Msgs RM = List (Message RM)

TPVars : (RM : ℕ) → VSet (3 + RM)
TPVars RM = TMState ∷ TMPrepared RM ∷ Msgs RM ∷ TCVars RM

TPInit : System (TPVars RM) → Set
TPInit {RM} (tmState , tmPrepared , msgs , rmState) = tmState ≡ init × tmPrepared ≡ [] × msgs ≡ [] × TCInit rmState


TPtoTCrefm : System (TPVars RM) → System (TCVars RM)
TPtoTCrefm (_ , _ , _ , rmState) = rmState



foo : (e : Fin RM) → (tmpr tmpr' : List (Fin RM)) → Dec (e ∈ᶠ tmpr) → Set
foo e tmpr tmpr' (yes p) = tmpr' ≡ tmpr
foo e tmpr tmpr' (no ¬p) = tmpr' ≡ e ∷ tmpr

refTMRcvPrepared : RefStAction {varsA = TCVars RM} TPtoTCrefm
RE (refTMRcvPrepared {RM}) = Fin RM
cond (ract refTMRcvPrepared) e (tmState , tmPrepared , msgs , rmState)
  = tmState ≡ init × ((e isPrepared) ∈ₘ msgs)
resp (ract refTMRcvPrepared) e sys nsys
 = let fn-tmprepared = suc zero
       tmprepared' = proj nsys fn-tmprepared
       tmprepared  = proj sys fn-tmprepared
   in   sys ≡ nsys except fn-tmprepared
      × (Σ (Dec (e ∈ᶠ tmprepared)) (foo e tmprepared tmprepared'))
isConst refTMRcvPrepared e (_ , _ , _ , rmState) (_ , _ , _ , rmState') (_ , (_ , _ , eq) , _) = eq


refTMCommit : RefStAction {varsA = TCVars RM} TPtoTCrefm
RE refTMCommit = ⊤
cond (ract refTMCommit) e (tmState , tmPrepared , msgs , rmState)
  = tmState ≡ init × {!!}
resp (ract refTMCommit) e sys nsys = {!!}
isConst refTMCommit e (_ , _ , _ , rmState) (_ , _ , _ , rmState') (cnd , rsp) = {!!}


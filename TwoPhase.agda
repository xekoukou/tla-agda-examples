module TwoPhase where

open import Relation.Binary hiding (_⇒_)
open import Data.Nat hiding (_≟_)
-- open import Data.Nat.Properties hiding (_≟_)
open import Data.Fin hiding (_+_ ; lift ; pred)
open import Data.Fin.Subset renaming (_∈_ to _∈ᶠ_ ; ⊤ to ⊤ᶠ ; ⊥ to ⊥ᶠ)
open import Data.Fin.Subset.Properties renaming (_∈?_ to _∈?ᶠ_)
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
open import LTL.Core
open import LTL.Stateless
open import LTL.PastGlobally
-- open import LTL.Past
open import LTL.Utils

open import TCommit
open import Level renaming (zero to lzero ; suc to lsuc ; Lift to ℓ↑ ; lift to lift)


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


_toFin : Message RM → Fin (2 + RM)
(r isPrepared) toFin = raise 2 r
_toFin {RM} doCommit = raise 1 (fromℕ RM)
_toFin {RM} doAbort = fromℕ (suc RM)


data TMState : Set where
  init done : TMState

TMPrepared : (RM : ℕ) → Set
TMPrepared RM = Subset RM

-- This is not quite Type-Safe. Is there an easy and better way?
Msgs : (RM : ℕ) → Set
Msgs RM = Subset (2 + RM)

TPVars : (RM : ℕ) → VSet (3 + RM)
TPVars RM = TMState ∷ TMPrepared RM ∷ Msgs RM ∷ TCVars RM


TPInit : System (TPVars RM) → Set
TPInit {RM} (tmState , tmPrepared , msgs , rmState) = tmState ≡ init × tmPrepared ≡ ⊥ᶠ × msgs ≡ ⊥ᶠ × TCInit rmState


TPtoTCrefm : (RM : ℕ) → System (TPVars RM) → System (TCVars RM)
TPtoTCrefm RM (_ , _ , _ , rmState) = rmState

_toTCV : {RM : ℕ} → System (TPVars RM) → System (TCVars RM)
_toTCV {RM} = TPtoTCrefm RM


_toTCVʷ : {RM : ℕ} → (System (TPVars RM)) ʷ → (System (TCVars RM)) ʷ
_toTCVʷ {RM} beh = ⟨ TPtoTCrefm RM ⟩ $ beh

--------------------------------------------------

refTMRcvPrepared : {RM : ℕ} → RefAction (TPtoTCrefm RM) stAction


RE (refTMRcvPrepared {RM}) = Fin RM
cond (ract refTMRcvPrepared) e (tmState , tmPrepared , msgs , rmState)
  = tmState ≡ init × ((e isPrepared) toFin) ∈ᶠ msgs
resp (ract refTMRcvPrepared) e sys@(tmState , tmPrepared , msgs , rmState)
                               nsys@(tmState' , tmPrepared' , msgs' , rmState')
 =      sys ≡ nsys except (suc zero)
      × tmPrepared' ≡ ⁅ e ⁆ ∪ tmPrepared


par (refTMRcvPrepared {RM}) e sys = tt
gcond (refTMRcvPrepared {RM}) e sys = ⊤
embed refTMRcvPrepared e (_ , _ , _ , rmState) gcnd (_ , _ , _ , rmState') (_ , (_ , _ , eq) , _) = tt , eq


-----------------------------------------------------------

refTMCommit : {RM : ℕ} → RefAction (TPtoTCrefm RM) stAction


RE refTMCommit = ⊤
cond (ract (refTMCommit {RM = RM})) e (tmState , tmPrepared , msgs , rmState)
  = tmState ≡ init × tmPrepared ≡ ⊤ᶠ
resp (ract refTMCommit) e sys@(tmState , tmPrepared , msgs , rmState)
                          nsys@(tmState' , tmPrepared' , msgs' , rmState')
  =   tmPrepared' ≡ tmPrepared × (rmState ≡ rmState' all)
    × tmState' ≡ done × msgs' ≡ ⁅ doCommit toFin ⁆ ∪ msgs


par refTMCommit e sys = tt
gcond refTMCommit e sys = ⊤
embed refTMCommit e (_ , _ , _ , rmState) gcnd (_ , _ , _ , rmState') (cnd , (_ , eq , _ , _)) = tt , eq


-----------------------------------------------------------

refTMAbort : {RM : ℕ} → RefAction (TPtoTCrefm RM) stAction


RE refTMAbort = ⊤
cond (ract refTMAbort) e sys@(tmState , tmPrepared , msgs , rmState)
  = tmState ≡ init
resp (ract refTMAbort) e sys@(tmState , tmPrepared , msgs , rmState)
                         nsys@(tmState' , tmPrepared' , msgs' , rmState')
  =   tmPrepared' ≡ tmPrepared × (rmState ≡ rmState' all)
    × tmState' ≡ done × msgs' ≡ ⁅ doAbort toFin ⁆ ∪ msgs
gcond refTMAbort e sys = ⊤


par refTMAbort e sys = tt
embed refTMAbort e sys gcnd nsys (_ , (_ , eq , _ , _)) = tt , eq


-----------------------------------------------------------

refRMPrepare : {RM : ℕ} → RefAction (TPtoTCrefm RM) Prepare


RE (refRMPrepare {RM}) = Fin RM
gcond (refRMPrepare) e sys = ⊤
cond (ract (refRMPrepare {zero})) () sys
resp (ract (refRMPrepare {zero})) () sys nsys
cond (ract (refRMPrepare {suc RM})) e sys@(tmState , tmPrepared , msgs , rmState)
  = rmState at e ≡ working
resp (ract (refRMPrepare {suc RM})) e sys@(tmState , tmPrepared , msgs , rmState)
                                      nsys@(tmState' , tmPrepared' , msgs' , rmState')
  =   (rmState' at e ≡ prepared)
    × rmState ≡ rmState' except e
    × msgs' ≡ ⁅ e isPrepared toFin ⁆ ∪ msgs
    × tmState ≡ tmState'
    × tmPrepared ≡ tmPrepared'



par refRMPrepare x _ = x
embed (refRMPrepare {zero}) () sys nsys rst
embed (refRMPrepare {suc RM}) e sys@(tmState , tmPrepared , msgs , rmState) gcnd
                                nsys@(tmState' , tmPrepared' , msgs' , rmState') (cnd , (a , b , _)) = cnd , a , b



-----------------------------------------------------------


refRMChooseToAbort : {RM : ℕ} → RefAction (TPtoTCrefm RM) Decide



RE (refRMChooseToAbort {RM}) = Fin RM
gcond (refRMChooseToAbort) e (tmState , tmPrepared , msgs , rmState) = notCommitted rmState
cond (ract (refRMChooseToAbort {zero})) ()
cond (ract (refRMChooseToAbort {suc RM})) e (tmState , tmPrepared , msgs , rmState)
  = rmState at e ≡ working
resp (ract (refRMChooseToAbort {zero})) () sys nsys
resp (ract (refRMChooseToAbort {suc RM})) e sys@(tmState , tmPrepared , msgs , rmState)
                                            nsys@(tmState' , tmPrepared' , msgs' , rmState')
  =   (rmState' at e ≡ aborted)
    × rmState ≡ rmState' except e
    × msgs ≡ msgs
    × tmState ≡ tmState'
    × tmPrepared ≡ tmPrepared'



par refRMChooseToAbort e sys = e
embed (refRMChooseToAbort {zero}) ()
embed (refRMChooseToAbort {suc RM}) e sys@(tmState , tmPrepared , msgs , rmState) gcnd
                                      nsys@(tmState' , tmPrepared' , msgs' , rmState') (cnd , (resp , oeq , _))
  = u→ ((u→ cnd , gcnd)) , (u→ ((u→ cnd) , gcnd , resp)) , oeq



-----------------------------------------------------------


-- The commit msg is sent to all, but some might be lost.
-- This action might not be triggerred at all.
refRMReceiveCommitMsg : {RM : ℕ} → RefAction (TPtoTCrefm RM) Decide


-- There is a problem here because we also have stuttering here, if this specific client has already committed.
RE (refRMReceiveCommitMsg {RM}) = Fin RM
gcond (refRMReceiveCommitMsg) e (tmState , tmPrepared , msgs , rmState) = rmState at e ≡ prepared × canCommit rmState
cond (ract (refRMReceiveCommitMsg {zero})) () sys
resp (ract (refRMReceiveCommitMsg {zero})) () sys nsys
cond (ract (refRMReceiveCommitMsg {suc RM})) e sys@(tmState , tmPrepared , msgs , rmState)
  = doCommit toFin ∈ᶠ msgs
resp (ract (refRMReceiveCommitMsg {suc RM})) e sys@(tmState , tmPrepared , msgs , rmState)
                                               nsys@(tmState' , tmPrepared' , msgs' , rmState')
  =   (rmState' at e ≡ committed)
    × rmState ≡ rmState' except e
    × msgs ≡ msgs
    × tmState ≡ tmState'
    × tmPrepared ≡ tmPrepared'



par refRMReceiveCommitMsg e sys = e
embed (refRMReceiveCommitMsg {zero}) () sys nsys x
embed (refRMReceiveCommitMsg {suc RM}) e sys@(tmState , tmPrepared , msgs , rmState) gcnd
                                         nsys@(tmState' , tmPrepared' , msgs' , rmState') (cnd , (resp , oeq , _))
  = (gcnd ←u) , ((fst gcnd , (snd gcnd , resp)) ←u) , oeq



-----------------------------------------------------------



refRMReceiveAbortMsg : {RM : ℕ} → RefAction (TPtoTCrefm RM) Decide



RE (refRMReceiveAbortMsg {RM}) = Fin RM
gcond (refRMReceiveAbortMsg) e sys@(tmState , tmPrepared , msgs , rmState)
  = (rmState at e ≡ prepared ⊎ rmState at e ≡ working) × notCommitted rmState
cond (ract (refRMReceiveAbortMsg {zero})) () sys
cond (ract (refRMReceiveAbortMsg {suc RM})) e sys@(tmState , tmPrepared , msgs , rmState)
  = doAbort toFin ∈ᶠ msgs
resp (ract (refRMReceiveAbortMsg {zero})) () sys nsys
resp (ract (refRMReceiveAbortMsg {suc RM})) e  sys@(tmState , tmPrepared , msgs , rmState)
                                               nsys@(tmState' , tmPrepared' , msgs' , rmState')
  =   (rmState' at e ≡ aborted)
    × rmState ≡ rmState' except e
    × msgs ≡ msgs
    × tmState ≡ tmState'
    × tmPrepared ≡ tmPrepared'



par (refRMReceiveAbortMsg {RM}) e sys = e
embed (refRMReceiveAbortMsg {zero}) ()
embed (refRMReceiveAbortMsg {suc RM}) e sys@(tmState , tmPrepared , msgs , rmState) gcnd
                                        nsys@(tmState' , tmPrepared' , msgs' , rmState') (cnd , (resp , oeq , _))
  = (u→ gcnd) , ((u→ (fst gcnd , (snd gcnd , resp))) , oeq)

tprspec : {RM : ℕ} → RSpec (TPtoTCrefm RM) (V⊤ 3 ++ TCE RM 5) tcspec
tprspec {RM} = refStAction (TPtoTCrefm RM) m∷ᵣₛₚ refTMCommit m∷ᵣₛₚ refTMAbort m∷ᵣₛₚ refTMRcvPrepared ∷ᵣₛₚ refRMPrepare ∷ᵣₛₚ refRMChooseToAbort m∷ᵣₛₚ
          refRMReceiveCommitMsg m∷ᵣₛₚ refRMReceiveAbortMsg ∷ᵣₛₚ []ᵣₛₚ



-----------------------------------------------------------



-- □ₚworkinglm : (beh : (System (TPVars RM)) ʷ) → (pe : ((V⊤ 3 ++ TCE RM 5) toUS) ʷ) → TPInit (! beh)
--       → [ (exSpec tprspec $ₛₚₜ pe) beh ] → (r : Fin RM)
--       → [ ⟨ (λ z → (z at r) ≡ working) ⟩ $ (beh toTCVʷ) ⇒ (◇ₚ ( ⟨ (λ z → ¬ ((z at r) ≡ working)) ⟩ $ (beh toTCVʷ))) ]
-- □ₚworkinglm beh pe tpinit rst r n workingNow = {!!}
-- 

□ₚworking : (beh : (System (TPVars RM)) ʷ) → (pe : ((V⊤ 3 ++ TCE RM 5) toUS) ʷ)
      → [ (exSpec tprspec $ₛₚₜ pe) beh ] → (r : Fin RM)
      → [ ⟨ (λ z → (z at r) ≡ working) ⟩ $ (beh toTCVʷ) ⇒ (□ₚ ( ⟨ (λ z → (z at r) ≡ working) ⟩ $ (beh toTCVʷ))) ]
□ₚworking beh pe rst r zero workingNow .0 z≤n = workingNow
□ₚworking beh pe rst r (suc n) workingNow zero m≤n with rmDec (((beh 0) toTCV) at r) working
□ₚworking beh pe rst r (suc n) workingNow zero m≤n | yes p = p
□ₚworking beh pe rst r (suc n) workingNow zero m≤n | no ¬p with [a→b]⇒[b←b] rmDec (⟨ (λ z → z at r) ⟩ $ (beh toTCVʷ)) (s≤s z≤n) ¬p refl workingNow
□ₚworking beh pe rst r (suc n) workingNow zero m≤n | no ¬p | h , 1≤h , h≤sn , intv , negeq with beh (pred h) | pe (pred h) | rst (pred h)
□ₚworking beh pe rst r (suc n) workingNow zero m≤n | no ¬p | h , 1≤h , h≤sn , intv , negeq | behn | en ←u | rstn = {!!}
□ₚworking beh pe rst r (suc n) workingNow zero m≤n | no ¬p | h , 1≤h , h≤sn , intv , negeq | behn | u→ pen | rstn = {!!}
□ₚworking beh pe rst r (suc n) workingNow (suc m) m≤n = {!!}




gcndNC : System (TPVars RM) → Fin RM → Set
gcndNC sys@(tmState , tmPrepared , msgs , rmState) e
  = rmState at e ≡ working → notCommitted rmState

tcinit⇒notCommitted : ∀{RM} → (sys : System (TCVars RM)) → TCInit sys → notCommitted sys
tcinit⇒notCommitted {zero} sys tcinit = tt
tcinit⇒notCommitted {suc RM} sys (refl , tcinit) = (λ {()}) , tcinit⇒notCommitted (snd sys) tcinit

!gcndNCP : (beh : (System (TPVars RM)) ʷ)
           → TPInit (! beh)
           → ! (⟨ Fin RM ⟩ ⇒ᵈ ⟨ gcndNC ⟩ $ beh)
!gcndNCP beh (_ , _ , _ , tcinit) a x = tcinit⇒notCommitted (snd (snd ( snd (beh 0)))) tcinit


gcndNCPExcept : (sys nsys : System (TCVars RM)) → (e : Fin RM) → ¬ (nsys at e ≡ committed)
      → sys ≡ nsys except e → notCommitted sys → notCommitted nsys
gcndNCPExcept {zero} sys nsys e atE ao pcnd = tt
gcndNCPExcept {suc RM} (v , sys) (nv , nsys) zero atE ao pcnd = atE , (subst notCommitted (pEq⇒Eq ao) (snd pcnd))
gcndNCPExcept {suc RM} (v , sys) (nv , nsys) (suc e) atE (refl , ao) pcnd = (fst pcnd) , gcndNCPExcept sys nsys e atE ao (snd pcnd)

prepared¬≡committed : ¬ (prepared ≡ committed)
prepared¬≡committed ()

aborted¬≡committed : ¬ (aborted ≡ committed)
aborted¬≡committed ()


gcndNCPInd : (beh : (System (TPVars RM)) ʷ) → (pe : ((V⊤ 3 ++ TCE RM 5) toUS) ʷ)
      → [ (exSpec tprspec $ₛₚₜ pe) beh ⇒ (⟨ Fin RM ⟩ ⇒ᵈ ⟨ gcndNC ⟩ $ beh) ⇒ (⟨ Fin RM ⟩ ⇒ᵈ ⟨ gcndNC ⟩ $ (○ beh)) ]
gcndNCPInd {zero} beh pe n rst ind r = λ x → tt
gcndNCPInd {suc RM} beh pe n rst ind r with beh n | beh (suc n) | pe n
gcndNCPInd {suc RM} beh pe n (_ , _ , _ , _ , eq) ind r | behn | behsn | en ←u
  = subst (λ z → z at r ≡ working → notCommitted z) (pEq⇒Eq eq) (ind r)
gcndNCPInd {suc RM} beh pe n (_ , _ , eq , _ , _) ind r | behn | behsn | u→ (e ←u)
  = subst (λ z → z at r ≡ working → notCommitted z) (pEq⇒Eq eq) (ind r)
gcndNCPInd {suc RM} beh pe n (_ , _ , eq , _ , _) ind r | behn | behsn | u→ (u→ (e ←u))
  = subst (λ z → z at r ≡ working → notCommitted z) (pEq⇒Eq eq) (ind r)
gcndNCPInd {suc RM} beh pe n (_ , (_ , _ , eq) , _) ind r | behn | behsn | u→ (u→ (u→ (e ←u))) 
  = subst (λ z → z at r ≡ working → notCommitted z) (pEq⇒Eq eq) (ind r)
gcndNCPInd {suc RM} beh pe n (cnd , npr , eq , _) ind r | behn | behsn | u→ (u→ (u→ (u→ (e ←u))))
  = λ _ → gcndNCPExcept (snd (snd (snd behn))) ((snd (snd (snd behsn)))) e (λ x → prepared¬≡committed (trans (sym npr) x)) eq (ind e cnd)
gcndNCPInd {suc RM} beh pe n (cnd , npr , eq , _) ind r | behn | behsn | u→ (u→ (u→ (u→ (u→ (e ←u)))))
  = λ _ → gcndNCPExcept (snd (snd (snd behn))) ((snd (snd (snd behsn)))) e (λ x → aborted¬≡committed (trans (sym npr) x)) eq (ind e cnd)
gcndNCPInd {suc RM} beh pe n rst ind r | behn | behsn | u→ (u→ (u→ (u→ (u→ (u→ (e ←u)))))) = {!!}
gcndNCPInd {suc RM} beh pe n rst ind r | behn | behsn | u→ (u→ (u→ (u→ (u→ (u→ (u→ pen)))))) = {!!}


gcndNCP : (beh : (System (TPVars RM)) ʷ) → (pe : ((V⊤ 3 ++ TCE RM 5) toUS) ʷ) → TPInit (! beh)
      → [ (exSpec tprspec $ₛₚₜ pe) beh ] → [ (⟨ Fin RM ⟩ ⇒ᵈ ⟨ gcndNC ⟩ $ beh) ]
gcndNCP beh pe tpinit rst = indn (gcndNCPInd beh pe $ rst) (!gcndNCP beh tpinit)



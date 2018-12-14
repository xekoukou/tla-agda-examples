module TwoPhase where


open import Level renaming (Lift to ℓ↑ ; lift to lift ; suc to lsuc ; zero to lzero)
open import Data.Nat
open import Data.Fin hiding (_+_ ; lift ; pred) renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Subset renaming (_∈_ to _∈ᶠ_ ; _∉_ to _∉ᶠ_ ; ⊤ to ⊤ᶠ ; ⊥ to ⊥ᶠ ; _⊆_ to _⊆ᶠ_)
open import Data.Fin.Subset.Properties renaming (_∈?_ to _∈?ᶠ_)
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
open import TLA.Refine
open import TLA.Utils


open import TCommit


data LeaderMsg : Set where
  doCommit : LeaderMsg
  doAbort : LeaderMsg

llm : ℕ
llm = suc (suc zero)

_toFinₗ : LeaderMsg → Fin (llm)
_toFinₗ doCommit = zero
_toFinₗ doAbort = suc zero


LMsgs = Subset llm

_∈ˡ_ : LeaderMsg → LMsgs → Set
m ∈ˡ lmsgs = _∈ᶠ_ (m toFinₗ) lmsgs

_∉ˡ_ : LeaderMsg → LMsgs → Set
m ∉ˡ lmsgs = _∉ᶠ_ (m toFinₗ) lmsgs


TPrepared : ∀ RM → Set
TPrepared RM =  Subset RM

RMsgs : ∀ RM → Set
RMsgs RM =  Subset RM

TPVars : (RM : ℕ) → VSet (suc (suc (suc (suc zero))))
TPVars RM = TCVars RM toPS ∷ LMsgs ∷ TPrepared RM ∷ RMsgs RM ∷ []

TPtoTCrefm : (RM : ℕ) → System (TPVars RM) → System (TCVars RM)
TPtoTCrefm RM (rmState , rm) = rmState

TPInit : System (TPVars RM) → Set
TPInit (rmState , lmsgs , tprepared , rmsgs , rm) = TCInit rmState × lmsgs ≡ ⊥ᶠ × tprepared ≡ ⊥ᶠ × rmsgs ≡ ⊥ᶠ


gcondv : ∀{RM} → GCondV (TPVars RM)
         (suc (suc (suc (suc (suc (suc zero))))))
gcondv {RM} (rmState , lmsgs , tprepared , rmsgs , rm)
  = (doCommit ∈ˡ lmsgs → canCommit rmState)
  ∷ (doAbort ∈ˡ lmsgs → notCommitted rmState)
  ∷ (doCommit ∈ˡ lmsgs → doAbort ∉ˡ lmsgs)
  ∷ ((e : Fin RM) → lmsgs ≡ ⊥ᶠ → e ∈ᶠ tprepared → (canCommit′ rmState) e)
  ∷ (lmsgs ≡ ⊥ᶠ → notCommitted rmState)
  ∷ (lmsgs ≡ ⊥ᶠ → (e : Fin RM) → e ∈ᶠ rmsgs → (canCommit′ rmState) e)
  ∷ []

gcond : ∀{RM} → GCond (TPVars RM)
gcond {RM} sys = (gcondv {RM} sys) toPS


dd : ¬ (committed ≡ prepared)
dd ()

{-# TERMINATING #-}
refRMPrepare : {RM : ℕ} → RefAction {varsB = TPVars RM} ( TPtoTCrefm RM ) gcond Prepare
RE (refRMPrepare {RM}) = Fin RM
cond (ract (refRMPrepare {RM})) e (rmState , rm)
  = (rmState at e) ≡ working
resp (ract (refRMPrepare {RM})) e (rmState , lmsgs , tprepared , rmsgs , rm) (rmState' , lmsgs' , tprepared' , rmsgs' , rm')
  = rmState' ≡ rmState Except e != (λ v nv → nv ≡ prepared)
  × lmsgs' ≡ lmsgs
  × tprepared' ≡ tprepared
  × rmsgs' ≡ rmsgs
par (refRMPrepare {RM}) e sys = e
gcondInd (refRMPrepare {RM}) e (rmState , lmsgs , tprepared , rmsgs , rm) (rmState' , lmsgs' , tprepared' , rmsgs' , rml')
         (cnd , (rmSteq , refl , tpreq , refl)) (a , b , c , d , f , g , irm)
  = (λ dc∈lmsgs oe → let bf = a dc∈lmsgs
                     in case (e ≟ᶠ oe) of
                         λ { (yes p) → let wq = exceptEq e oe p rmSteq
                                       in wq ←u
                           ; (no ¬p) → let wq = exceptNEq e oe ¬p rmSteq 
                                       in subst (λ z → z ≡ prepared ⊎ z ≡ committed) (sym wq) (bf oe) })
  , (λ da∈lmsgs oe → let bf = b da∈lmsgs
                     in case (e ≟ᶠ oe) of
                         λ { (yes p) → let wq = exceptEq e oe p rmSteq
                                       in λ x → dd (trans (sym x) wq)
                           ; (no ¬p) → let wq = exceptNEq e oe ¬p rmSteq 
                                       in λ x → bf oe (subst (λ z → z ≡ committed) wq x)})
  , c
  , (λ oe y x → case (e ≟ᶠ oe) of
                         λ { (yes p) → exceptEq e oe p rmSteq ←u
                           ; (no ¬p) → let wq = exceptNEq e oe ¬p rmSteq
                                           bf = d oe y (subst _ tpreq x)
                                       in subst (λ z → z ≡ prepared ⊎ z ≡ committed) (sym wq) bf }) 
  , (λ x oe →  case (e ≟ᶠ oe) of
                         λ { (yes p) → λ z → dd ( trans (sym z) (exceptEq e oe p rmSteq))
                           ; (no ¬p) → let wq = exceptNEq e oe ¬p rmSteq
                                       in subst (λ z → ¬ z ≡ committed) (sym wq) (f x oe) })
  , (λ w oe y → case (e ≟ᶠ oe) of
                λ { (yes p) → let wq = exceptEq e oe p rmSteq
                              in wq ←u
                  ; (no ¬p) → let wq = exceptNEq e oe ¬p rmSteq
                              in subst (λ z → z ≡ prepared ⊎ z ≡ committed) (sym wq) (g w oe y) })
  , lift tt
embed (refRMPrepare {zero}) () (rmState , rm) (nrm , rmState') gcnd rst
embed (refRMPrepare {suc RM}) e (rmState , rm) (rmState' , rm') gcnd (cnd , (resp , rmresp)) = cnd , resp


{-# TERMINATING #-}
refRMRcCommit : {RM : ℕ} → RefAction {varsB = TPVars RM} (TPtoTCrefm RM) gcond Decide
RE (refRMRcCommit {RM}) = Fin RM
cond (ract (refRMRcCommit {RM})) e (rmState , lmsgs , rm)
  =   rmState at e ≡ prepared
    × (doCommit ∈ˡ lmsgs)
resp (ract (refRMRcCommit {RM})) e (rmState , lmsgs , tprepared , rmsgs , rm) (rmState' , lmsgs' , tprepared' , rmsgs' , rm')
  = (rmState' ≡ rmState Except e != λ v nv → nv ≡ committed)
  × lmsgs' ≡ lmsgs
  × tprepared' ≡ tprepared
  × rmsgs' ≡ rmsgs
par (refRMRcCommit {RM}) e sys = e
gcondInd (refRMRcCommit {RM}) e (rmState , lmsgs , tprepared , rmsgs , rm) (rmState' , lmsgs' , tprepared' , rmsgs' , rm')
         ((cnd1 , cnd2) , (rmSteq , refl , tpreq , refl)) (a , b , c , d , f , g , irm)
  = (λ dc∈lmsgs oe → let bf = a dc∈lmsgs
                     in case (e ≟ᶠ oe) of
                         λ { (yes p) → let wq = exceptEq e oe p rmSteq
                                           in u→ wq
                           ; (no ¬p) → let wq = exceptNEq e oe ¬p rmSteq 
                                       in subst (λ z → z ≡ prepared ⊎ z ≡ committed) (sym wq) (bf oe) })
  , (λ da∈lmsgs → let wq = da∈lmsgs in ⊥-elim (c cnd2 wq))
  , c
  , (λ oe y x → case (e ≟ᶠ oe) of
                         λ { (yes p) → u→ exceptEq e oe p rmSteq
                           ; (no ¬p) → let wq = exceptNEq e oe ¬p rmSteq
                                           bf = d oe y (subst _ tpreq x)
                                       in subst (λ z → z ≡ prepared ⊎ z ≡ committed) (sym wq) bf })
  , (λ x → ⊥-elim (∉⊥ (subst (λ z → zero ∈ᶠ z) x cnd2)))
  , ((λ w oe y → case (e ≟ᶠ oe) of
                λ { (yes p) → let wq = exceptEq e oe p rmSteq
                              in u→ wq
                  ; (no ¬p) → let wq = exceptNEq e oe ¬p rmSteq
                              in subst (λ z → z ≡ prepared ⊎ z ≡ committed) (sym wq) (g w oe y) }))
  , lift tt
embed (refRMRcCommit {zero}) () sys nsys gcnd rst
embed (refRMRcCommit {suc RM}) e (rmState , lmsgs , rm) (rmState' , rm') (a , _) ((cnd1 , cnd2) , (rmSteq , rmeq))
  = ((cnd1 , a cnd2) ←u) , let wq = except&at {Q = λ v nv → v ≡ prepared} cnd1 rmSteq
                           in exceptP⇒Q (λ {v nv (q , w) → (w , a cnd2 , q) ←u}) wq



ww : ¬ committed ≡ aborted
ww ()

{-# TERMINATING #-}
refRMRcAbort : {RM : ℕ} → RefAction {varsB = TPVars RM} (TPtoTCrefm RM) gcond Decide
RE (refRMRcAbort {RM}) = Fin RM
cond (ract (refRMRcAbort {RM})) e (rmState , lmsgs , rm)
  = (doAbort ∈ˡ lmsgs)
resp (ract (refRMRcAbort {RM})) e (rmState , lmsgs , tprepared , rmsgs , rm) (rmState' , lmsgs' , tprepared' , rmsgs' , rm')
  = (rmState' ≡ rmState Except e != λ v nv → nv ≡ aborted)
  × lmsgs' ≡ lmsgs
  × tprepared' ≡ tprepared
  × rmsgs' ≡ rmsgs
par (refRMRcAbort {RM}) e sys = e
gcondInd (refRMRcAbort {RM}) e (rmState , lmsgs , tprepared , rmsgs , rm) (rmState' , lmsgs' , tprepared' , rmsgs' , rm')
         (cnd1 , (rmSteq , refl , rmeq)) (a , b , c , irm)
  = (λ x → let wq = x in ⊥-elim (c wq cnd1))
  , (λ da∈lmsgs oe → let bf = b da∈lmsgs
                     in case (e ≟ᶠ oe) of
                         λ { (yes p) → let wq = exceptEq e oe p rmSteq
                                           in λ x → ww (trans (sym x) wq)
                           ; (no ¬p) → let wq = exceptNEq e oe ¬p rmSteq 
                                       in λ x → bf oe (subst (λ z → z ≡ committed) wq x)  })
  , c
  , (λ oe y x → ⊥-elim (∉⊥ (subst (λ z → (doAbort ∈ˡ z)) y cnd1)))
  , (λ x → ⊥-elim (∉⊥ (subst (λ z → (suc zero) ∈ᶠ z) x cnd1)))
  , (λ x → ⊥-elim (∉⊥ (subst (λ z → (suc zero) ∈ᶠ z) x cnd1)))
  , lift tt
embed (refRMRcAbort {zero}) () sys nsys gcnd rst
embed (refRMRcAbort {suc RM}) e (rmState , lmsgs , rm) nsys (a , b , _) (cnd1 , (rmSteq , rmeq))
  = (u→ b cnd1) , exceptP⇒Q (λ v nv x → u→ (b cnd1 , x)) rmSteq




refLSndCommit : {RM : ℕ} → RefAction {varsB = TPVars RM} (TPtoTCrefm RM) gcond stAction
RE (refLSndCommit {RM}) = ⊤
cond (ract (refLSndCommit {RM})) e (rmState , lmsgs , tprepared , rm)
  = lmsgs ≡ ⊥ᶠ
  × tprepared ≡ ⊤ᶠ
resp (ract (refLSndCommit {RM})) e (rmState , lmsgs , tprepared , rmsgs) (rmState' , lmsgs' , tprepared' , rmsgs')
  = rmState' ≡ rmState
  × lmsgs' ≡ ⁅ doCommit toFinₗ ⁆ ∪ lmsgs
  × tprepared' ≡ tprepared
  × rmsgs' ≡ rmsgs
par (refLSndCommit {RM}) e sys = tt
gcondInd (refLSndCommit {RM}) e (rmState , lmsgs , tprepared , rm) (rmState' , lmsgs' , tprepared' , rm')
         ((refl , refl) , (rmSteq , refl , tpreq , rmeq)) (a , b , c , d , irm)
  = (λ x oe → subst _ (sym rmSteq) (d oe refl ∈⊤) )
  , (λ { (there ())})
  , (λ { x (there ())})
  , (λ oe x → ⊥-elim (∉⊥ (subst (λ z → zero ∈ᶠ z) x here)))
  , (λ y → ⊥-elim (∉⊥ (subst (λ z → (doCommit ∈ˡ z)) y here)))
  , ((λ y → ⊥-elim (∉⊥ (subst (λ z → (doCommit ∈ˡ z)) y here))))
  , lift tt
embed (refLSndCommit {RM}) e sys nsys gcnd ((cnd) , (rmSteq , rmeq)) = tt , rmSteq


refLSndAbort : {RM : ℕ} → RefAction {varsB = TPVars RM} (TPtoTCrefm RM) gcond stAction
RE (refLSndAbort {RM}) = ⊤
cond (ract (refLSndAbort {RM})) e (rmState , lmsgs , tprepared , rm)
  = lmsgs ≡ ⊥ᶠ
resp (ract (refLSndAbort {RM})) e (rmState , lmsgs , tprepared , rmsgs) (rmState' , lmsgs' , tprepared' , rmsgs')
  = rmState' ≡ rmState
  × lmsgs' ≡ ⁅ doAbort toFinₗ ⁆ ∪ lmsgs
  × tprepared' ≡ tprepared
  × rmsgs' ≡ rmsgs
par (refLSndAbort {RM}) e sys = tt
gcondInd (refLSndAbort {RM}) e (rmState , lmsgs , tprepared , rm) (rmState' , lmsgs' , tprepared' , rm')
         (refl , (refl , refl , tpreq , rmeq)) (a , b , c , d , f , irm)
  = (λ {()})
  , (λ x → f refl)
  , (λ {()})
  , (λ oe x →  ⊥-elim (∉⊥ (subst (λ z → (suc zero) ∈ᶠ z) x (there here))))
  , ((λ x →  ⊥-elim (∉⊥ (subst (λ z → (suc zero) ∈ᶠ z) x (there here)))))
  , (((λ x →  ⊥-elim (∉⊥ (subst (λ z → (suc zero) ∈ᶠ z) x (there here))))))
  , lift tt
embed (refLSndAbort {RM}) e sys nsys gcnd (cnd , (rmSteq , rmeq)) = tt , rmSteq



refRMSndPrepared : {RM : ℕ} → RefAction {varsB = TPVars RM} (TPtoTCrefm RM) gcond stAction
RE (refRMSndPrepared {RM}) = Fin RM
cond (ract (refRMSndPrepared {RM})) e (rmState , lmsgs , tprepared , rmsgs , rm)
  = rmState at e ≡ prepared
resp (ract (refRMSndPrepared {RM})) e (rmState , lmsgs , tprepared , rmsgs , rm) (rmState' , lmsgs' , tprepared' , rmsgs' , rm')
  = rmState' ≡ rmState
  × lmsgs' ≡ lmsgs
  × tprepared' ≡ tprepared
  × rmsgs' ≡ ⁅ e ⁆ ∪ rmsgs
par (refRMSndPrepared {RM}) e sys = tt
gcondInd (refRMSndPrepared {RM}) e (rmState , lmsgs , tprepared , rmsgs , rm) (rmState' , lmsgs' , tprepared' , rmsgs' , rm')
         (cnd , (refl , refl , refl , refl)) (a , b , c , d , f , g , irm)
  = a
  , b
  , c
  , d
  , f
  , (λ w oe x → case (x∈p∪q⁻ _ _ x) of
                  λ { (x ←u) → let wq = x∈⁅y⁆⇒x≡y e x
                               in (subst _ (sym wq) cnd ←u)
                    ; (u→ y) → g w oe y })
  , lift tt
embed (refRMSndPrepared {RM}) e sys nsys gcnd (cnd , (rmeq , rm)) = tt , rmeq



refLRcPrepared : {RM : ℕ} → RefAction {varsB = TPVars RM} (TPtoTCrefm RM) gcond stAction
RE (refLRcPrepared {RM}) = Fin RM
cond (ract (refLRcPrepared {RM})) e (rmState , lmsgs , tprepared , rmsgs , rm)
  = e ∈ᶠ rmsgs
resp (ract (refLRcPrepared {RM})) e (rmState , lmsgs , tprepared , rmsgs , rm) (rmState' , lmsgs' , tprepared' , rmsgs' , rm')
  = rmState' ≡ rmState
  × lmsgs' ≡ lmsgs
  × tprepared' ≡ ⁅ e ⁆ ∪ tprepared
  × rmsgs' ≡ rmsgs
par (refLRcPrepared {RM}) e sys = tt
gcondInd (refLRcPrepared {RM}) e (rmState , lmsgs , tprepared , rmsgs , rm)
                                 (rmState' , lmsgs' , tprepared' , rmsgs' , rm')
         (cnd , (refl , refl , refl , refl)) (a , b , c , d , f , g , irm)
  = a
  , b
  , c
  , (λ oe q x → case (x∈p∪q⁻ _ _ x) of
                  λ { (x ←u) → let wq = x∈⁅y⁆⇒x≡y e x
                               in g q oe (subst _ (sym wq) cnd)
                    ; (u→ y) → d oe q y })
  , f
  , g
  , lift tt
embed (refLRcPrepared {RM}) e sys nsys gcnd (cnd , (rmeq , rm)) = tt , rmeq

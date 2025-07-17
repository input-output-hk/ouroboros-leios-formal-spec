open import Leios.Prelude hiding (id; _>>=_; return)
open import Leios.Config

open import Prelude.Monad
open import Prelude.Result

open import CategoricalCrypto hiding (id; _∘_)

-- TODO: SpecStructure as parameter
module Leios.Short.Trace.Verifier (params : Params) (let open Params params) where

open import Leios.Defaults params
  using (isb; hpe; hhs; htx; SendIB; FFDBuffers; Dec-SimpleFFD; sortition)
  renaming (d-SpecStructure to traceSpecStructure) public

open import Leios.SpecStructure using (SpecStructure)
open SpecStructure traceSpecStructure hiding (Hashable-IBHeader; Hashable-EndorserBlock; isVoteCertified) public

open import Leios.Short traceSpecStructure params public
open GenFFD

open Types params

data FFDUpdate : Type where
  IB-Recv-Update : InputBlock → FFDUpdate
  EB-Recv-Update : EndorserBlock → FFDUpdate
  VT-Recv-Update : List Vote → FFDUpdate

data Action : Type where
  IB-Role-Action    : ℕ → Action
  EB-Role-Action    : ℕ → List IBRef → List EndorserBlock → Action
  VT-Role-Action    : ℕ → Action
  No-IB-Role-Action : ℕ → Action
  No-EB-Role-Action : ℕ → Action
  No-VT-Role-Action : ℕ → Action
  Ftch-Action       : ℕ → Action
  Slot-Action       : ℕ → Action
  Base₁-Action      : ℕ → Action
  Base₂a-Action     : ℕ → EndorserBlock → Action
  Base₂b-Action     : ℕ → Action

TestTrace = List (Action × FFDT Out)

private variable
  s s′ : LeiosState
  α    : Action
  αs   : TestTrace
  μ    : FFDUpdate
  μs   : List FFDUpdate
  ib   : InputBlock
  eb   : EndorserBlock
  ebs  : List EndorserBlock
  vt   : List Vote

data ValidUpdate : FFDUpdate → LeiosState → Type where
{-
  IB-Recv : ValidUpdate (IB-Recv-Update ib) s
  EB-Recv : ValidUpdate (EB-Recv-Update eb) s
  VT-Recv : ValidUpdate (VT-Recv-Update vt) s
-}
{-
data ValidAction₁ : Action → LeiosState → FFDT Out → Type where

  IB-Role : let open LeiosState s
            in
            ∙ canProduceIB slot sk-IB (stake s) tt
            ─────────────────────────────────────────────────────────────────────────
            ValidAction₁ (IB-Role-Action slot) s SLOT

  EB-Role : let open LeiosState s
                ibs = L.filter (IBSelection? s Late-IB-Inclusion) IBs
                LI  = map getIBRef ibs
                LE = map getEBRef ebs
                h  = mkEB slot id tt sk-EB LI LE
                P  = λ x → isVoteCertified s x
                         × x ∈ˡ EBs
                         × x ∈ᴮ slices L slot 2 (3 * η / L)
                slots = map slotNumber
            in
            ∙ needsUpkeep EB-Role
            ∙ canProduceEB slot sk-EB (stake s) tt
            ∙ All.All P ebs
            ∙ Unique (slots ebs) × fromList (slots ebs) ≡ᵉ fromList (slots (filter P EBs))
            ─────────────────────────────────────────────────────────────────────────
            ValidAction₁ (EB-Role-Action slot LI ebs) s SLOT

  VT-Role : let open LeiosState s
                EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
                votes = map (vote sk-VT ∘ hash) EBs'
            in
            ∙ needsUpkeep-Stage VT-Role
            ∙ canProduceV slot sk-VT (stake s)
            ─────────────────────────────────────────────────────────────────────────
            ValidAction₁ (VT-Role-Action slot) s SLOT

  No-IB-Role : let open LeiosState s
               in
               ∙ needsUpkeep IB-Role
               ∙ (∀ π → ¬ canProduceIB slot sk-IB (stake s) π)
               ───────────────────────────────────────────────
               ValidAction₁ (No-IB-Role-Action slot) s SLOT

  No-EB-Role : let open LeiosState s
               in
               ∙ needsUpkeep EB-Role
               ∙ (∀ π → ¬ canProduceEB slot sk-EB (stake s) π)
               ───────────────────────────────────────────────
               ValidAction₁ (No-EB-Role-Action slot) s SLOT

  No-VT-Role : let open LeiosState s
               in
               ∙ needsUpkeep-Stage VT-Role →
               ∙ (¬ canProduceV slot sk-VT (stake s))
               ───────────────────────────────────────────────
               ValidAction₁ (No-VT-Role-Action slot) s SLOT

  Slot : let open LeiosState s
         in
         ∙ allDone s
         ─────────────────────────────────────────────────────────────────────────
         ValidAction₁ (Slot-Action slot) s SLOT

  Ftch : ValidAction₁ (Ftch-Action (LeiosState.slot s)) s FTCH

  Base₂a : ∀ {eb} → let open LeiosState s renaming (BaseState to bs)
           in
           ∙ needsUpkeep Base
           ∙ eb ∈ filter (λ x → isVoteCertified s x × x ∈ᴮ slice L slot 2) EBs
           ∙ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ tt
           ─────────────────────────────────────────────────────────────────────────
           ValidAction₁ (Base₂a-Action slot eb) s SLOT

  Base₂b : let open LeiosState s renaming (BaseState to bs)
           in
           ∙ needsUpkeep Base
           ∙ [] ≡ filter (λ x → isVoteCertified s x × x ∈ᴮ slice L slot 2) EBs
           ∙ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ tt
           ─────────────────────────────────────────────────────────────────────────
           ValidAction₁ (Base₂b-Action slot) s SLOT

data ValidAction₂ : Action → LeiosState → BaseT In → Type where

  Base₁ : ∀ {txs} → ValidAction₂ (Base₁-Action (LeiosState.slot s)) s (SUBMIT (this txs))


data ValidAction₃ : Action → LeiosState → BaseT Out → Type where

  Slot : ∀ {rbs} → let open LeiosState s
         in
         ─────────────────────────────────────────────────────────────────────────
         ValidAction₃ (Slot-Action slot) s (BASE-LDG rbs)

-}
private variable
  i : FFDT Out -- LeiosInput
  o : FFDT In -- LeiosOutput

{-
⟦_⟧ : ValidAction₁ α s i → LeiosState × FFDT In
⟦ IB-Role {s} _ ⟧       = addUpkeep s IB-Role , EMPTY
⟦ EB-Role {s} _ _ _ _ ⟧ = addUpkeep s EB-Role , EMPTY
⟦ VT-Role {s} _ _ ⟧     = addUpkeep-Stage s VT-Role , EMPTY
⟦ No-IB-Role {s} _ _ ⟧  = addUpkeep s IB-Role , EMPTY
⟦ No-EB-Role {s} _ _ ⟧  = addUpkeep s EB-Role , EMPTY
⟦ No-VT-Role {s} _ _ ⟧  = addUpkeep-Stage s VT-Role , EMPTY
⟦ Slot {s} _ ⟧          =
  let open LeiosState s
  in
  (record s
     { Ledger       = constructLedger {!!}
     ; slot         = suc slot
     ; Upkeep       = ∅
     ; Upkeep-Stage = ifᵈ (endOfStage slot) then ∅ else Upkeep-Stage
     } ↑ L.filter (isValid? s) {!!}
  , EMPTY)

-}
{-
⟦ Ftch {s} ⟧ = s , FTCH-LDG (LeiosState.Ledger s)
⟦ Base₁ {s} {txs} ⟧ = record s { ToPropose = txs } , EMPTY
⟦ Base₂a {s} {eb} _ _ _ ⟧ =
  let (bs' , _) = B.SUBMIT-total {LeiosState.BaseState s} {this eb}
  in addUpkeep record s { BaseState = bs' } Base , EMPTY
⟦ Base₂b {s} _ _ _ ⟧ =
  let (bs' , _) = B.SUBMIT-total {LeiosState.BaseState s} {that (LeiosState.ToPropose s)}
  in addUpkeep record s { BaseState = bs' } Base , EMPTY
-}
open LeiosState
open FFDBuffers

{-
ValidAction₁→Eq-Slot : ∀ {s sl} → ValidAction₁ (Slot-Action sl) s SLOT → sl ≡ slot s
ValidAction₁→Eq-Slot (Slot _) = refl

ValidAction₁→Eq-IB : ∀ {s sl} → ValidAction₁ (IB-Role-Action sl) s SLOT → sl ≡ slot s
ValidAction₁→Eq-IB (IB-Role _) = refl

ValidAction₁→Eq-EB : ∀ {s sl ibs ebs} → ValidAction₁ (EB-Role-Action sl ibs ebs) s SLOT → sl ≡ slot s × ibs ≡ map getIBRef (L.filter (IBSelection? s Late-IB-Inclusion) (IBs s))
ValidAction₁→Eq-EB (EB-Role _ _ _ _) = refl , refl

ValidAction₁→Eq-VT : ∀ {s sl} → ValidAction₁ (VT-Role-Action sl) s SLOT → sl ≡ slot s
ValidAction₁→Eq-VT (VT-Role _ _) = refl
-}

getLabel : ∀ {i o} → s -⟦ i / o ⟧⇀ s′ → Action
getLabel (Slot₁ {s} _)                        = Slot-Action (slot s)
getLabel (Slot₂ {s})                          = Slot-Action (slot s)
getLabel (Ftch {s})                           = Ftch-Action (slot s)
getLabel (Base₁ {s})                          = Base₁-Action (slot s)
getLabel (Base₂a {s} {eb} _ _)                = Base₂a-Action (slot s) eb
getLabel (Base₂b {s} _ _)                     = Base₂b-Action (slot s)
getLabel (Roles₁ (IB-Role {s} _))             = IB-Role-Action (slot s)
getLabel (Roles₁ (EB-Role {s} {ebs} _ _ _ _)) =
  let ibs = L.filter (IBSelection? s Late-IB-Inclusion) (IBs s)
      LI  = map getIBRef ibs
  in EB-Role-Action (slot s) LI ebs
getLabel (Roles₁ (VT-Role {s} _ _))           = VT-Role-Action (slot s)
getLabel (Roles₂ (No-IB-Role {s} _ _))        = No-IB-Role-Action (slot s)
getLabel (Roles₂ (No-EB-Role {s} _ _))        = No-EB-Role-Action (slot s)
getLabel (Roles₂ (No-VT-Role {s} _ _))        = No-VT-Role-Action (slot s)


--- ValidAction₁-sound : ∀ {i o} → (vα : ValidAction₁ α s i) → let (s′ , o) = ⟦ vα ⟧ in s -⟦ rcvˡ (-, i) / {!!} ⟧⇀ s′
{-
ValidAction₁-sound : ∀ {i o} → (ValidAction₁ α s i) → s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′
ValidAction₁-sound = {!!}

ValidAction₁-sound (Slot x)          = Slot₁ x
--ValidAction₁-sound Ftch                    = Ftch
--ValidAction₁-sound Base₁                   = Base₁
ValidAction₁-sound (Base₂a x x₁)        = Base₂a x x₁
ValidAction₁-sound (Base₂b x x₁)        = Base₂b x x₁
ValidAction₁-sound (IB-Role x₁)         = Roles₁ (IB-Role x₁)
ValidAction₁-sound (EB-Role x x₁ x₂ x₃) = Roles₁ (EB-Role x x₁ x₂ x₃)
ValidAction₁-sound (VT-Role x x₁)       = Roles₁ (VT-Role x x₁)
ValidAction₁-sound (No-IB-Role x x₁)       = Roles₂ (No-IB-Role x x₁)
ValidAction₁-sound (No-EB-Role x x₁)       = Roles₂ (No-EB-Role x x₁)
ValidAction₁-sound (No-VT-Role x x₁)       = Roles₂ (No-VT-Role x x₁)
-}



{-
ValidAction-complete : (st : s -⟦ rcvˡ (-, i) / {!!} ⟧⇀ s′) → ValidAction (getLabel st) s i
ValidAction-complete {s} {s′} (Roles₁ (IB-Role {s} {π} {ffds'} x₁ _)) =
  let b  = record { txs = ToPropose s }
      h  = mkIBHeader (slot s) id tt sk-IB (ToPropose s)
  in IB-Role {s} x₁
ValidAction-complete {s} (Roles₁ (EB-Role {ebs = ebs} x x₁ x₂ x₃ _)) =
  let ibs = L.filter (IBSelection? s Late-IB-Inclusion) (IBs s)
      LI  = map getIBRef ibs
      LE  = (map getEBRef ebs)
      h   = mkEB (slot s) id tt sk-EB LI LE
  in EB-Role {s} x x₁ x₂ x₃
ValidAction-complete {s} (Roles₁ (VT-Role x x₁ _))  =
  let EBs'  = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L (slot s) 1) (EBs s)
      votes = map (vote sk-VT ∘ hash) EBs'
  in VT-Role {s} x x₁
ValidAction-complete (Roles₂ (No-IB-Role x x₁)) = No-IB-Role x x₁
ValidAction-complete (Roles₂ (No-EB-Role x x₁)) = No-EB-Role x x₁
ValidAction-complete (Roles₂ (No-VT-Role x x₁)) = No-VT-Role x x₁
ValidAction-complete Ftch                      = Ftch
ValidAction-complete Base₁                     = Base₁
ValidAction-complete (Base₂a x x₁ x₂)          = Base₂a x x₁ x₂
ValidAction-complete (Base₂b x x₁ x₂)          = Base₂b x x₁ x₂
ValidAction-complete {s} (Slot x x₁ _)         = Slot x x₁
-}

data Err-verifyAction (α : Action) (i : FFDT Out) (s : LeiosState) : Type where
--  E-Err : ¬ ValidAction α s i → Err-verifyAction α i s

{-
verifyAction : ∀ (α : Action) → (i : FFDT Out) → (s : LeiosState) → Result (Err-verifyAction α i s) (ValidAction₁ α s i)
verifyAction = {!!}

verifyAction (IB-Role-Action _) (INIT _) _ = Err (E-Err λ ())
verifyAction (IB-Role-Action _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (IB-Role-Action sl) SLOT s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (ValidAction→Eq-IB x)))
... | yes p rewrite p
  with dec | dec
... | yes x | yes y = Ok (IB-Role x y)
... | no ¬p | _  = Err (E-Err λ where (IB-Role p _) → ⊥-elim (¬p p))
... | _ | no ¬p  = Err (E-Err λ where (IB-Role _ p) → ⊥-elim (¬p p))
verifyAction (IB-Role-Action _) FTCH-LDG _ = Err (E-Err λ ())
verifyAction (EB-Role-Action _ _ _) (INIT _) _ = Err (E-Err λ ())
verifyAction (EB-Role-Action _ _ _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (EB-Role-Action sl ibs ebs) SLOT s
  with sl ≟ slot s | ibs ≟  map getIBRef (L.filter (IBSelection? s Late-IB-Inclusion) (IBs s))
... | no ¬p | _ = Err (E-Err λ x → ⊥-elim (¬p (proj₁ $ ValidAction→Eq-EB x)))
... | _ | no ¬q = Err (E-Err λ x → ⊥-elim (¬q (proj₂ $ ValidAction→Eq-EB x)))
... | yes p | yes q rewrite p rewrite q
  with dec | dec | dec | dec | dec
... | yes x | yes y | yes z | yes w | yes v = Ok (EB-Role x y z w v)
... | no ¬p | _ | _ | _ | _ = Err (E-Err λ where (EB-Role p _ _ _ _) → ⊥-elim (¬p p))
... | _ | no ¬p | _ | _ | _ = Err (E-Err λ where (EB-Role _ p _ _ _) → ⊥-elim (¬p p))
... | _ | _ | no ¬p | _ | _ = Err (E-Err λ where (EB-Role _ _ p _ _) → ⊥-elim (¬p p))
... | _ | _ | _ | no ¬p | _ = Err (E-Err λ where (EB-Role _ _ _ p _) → ⊥-elim (¬p p))
... | _ | _ | _ | _ | no ¬p = Err (E-Err λ where (EB-Role _ _ _ _ p) → ⊥-elim (¬p p))
verifyAction (EB-Role-Action _ _ _) FTCH-LDG _ = Err (E-Err λ ())
verifyAction (VT-Role-Action _) (INIT _) _ = Err (E-Err λ ())
verifyAction (VT-Role-Action _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (VT-Role-Action sl) SLOT s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (ValidAction→Eq-VT x)))
... | yes p rewrite p
  with dec | dec | dec
... | yes x | yes y | yes z = Ok (VT-Role x y z)
... | no ¬p | _ | _ = Err (E-Err λ where (VT-Role p _ _) → ⊥-elim (¬p p))
... | _ | no ¬p | _ = Err (E-Err λ where (VT-Role _ p _) → ⊥-elim (¬p p))
... | _ | _ | no ¬p = Err (E-Err λ where (VT-Role _ _ p) → ⊥-elim (¬p p))
verifyAction (VT-Role-Action _) FTCH-LDG _ = Err (E-Err λ ())
verifyAction (No-IB-Role-Action _) (INIT _) _ = Err (E-Err λ ())
verifyAction (No-IB-Role-Action _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (No-IB-Role-Action sl) SLOT s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (sl≡slot x)))
  where
    sl≡slot : ∀ {s sl} → ValidAction (No-IB-Role-Action sl) s SLOT → sl ≡ slot s
    sl≡slot (No-IB-Role _ _) = refl
... | yes p rewrite p
  with dec | dec
... | yes p | yes q = Ok (No-IB-Role p q)
... | no ¬p | _ = Err (E-Err λ where (No-IB-Role p _) → ⊥-elim (¬p p))
... | _ | no ¬q = Err (E-Err λ where (No-IB-Role _ q) → ⊥-elim (¬q q))
verifyAction (No-IB-Role-Action _) FTCH-LDG _ = Err (E-Err λ ())
verifyAction (No-EB-Role-Action _) (INIT _) _ = Err (E-Err λ ())
verifyAction (No-EB-Role-Action _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (No-EB-Role-Action sl) SLOT s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (sl≡slot x)))
  where
    sl≡slot : ∀ {s sl} → ValidAction (No-EB-Role-Action sl) s SLOT → sl ≡ slot s
    sl≡slot (No-EB-Role _ _) = refl
... | yes p rewrite p
  with dec | dec
... | yes p | yes q = Ok (No-EB-Role p q)
... | no ¬p | _ = Err (E-Err λ where (No-EB-Role p _) → ⊥-elim (¬p p))
... | _ | no ¬q = Err (E-Err λ where (No-EB-Role _ q) → ⊥-elim (¬q q))
verifyAction (No-EB-Role-Action _) FTCH-LDG _ = Err (E-Err λ ())
verifyAction (No-VT-Role-Action _) (INIT _) _ = Err (E-Err λ ())
verifyAction (No-VT-Role-Action _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (No-VT-Role-Action sl) SLOT s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (sl≡slot x)))
  where
    sl≡slot : ∀ {s sl} → ValidAction (No-VT-Role-Action sl) s SLOT → sl ≡ slot s
    sl≡slot (No-VT-Role _ _) = refl
... | yes p rewrite p
  with dec | dec
... | yes p | yes q = Ok (No-VT-Role p q)
... | no ¬p | _ = Err (E-Err λ where (No-VT-Role p _) → ⊥-elim (¬p p))
... | _ | no ¬q = Err (E-Err λ where (No-VT-Role _ q) → ⊥-elim (¬q q))
verifyAction (No-VT-Role-Action _) FTCH-LDG _ = Err (E-Err λ ())
verifyAction (Ftch-Action _) (INIT _) _ = Err (E-Err λ ())
verifyAction (Ftch-Action _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (Ftch-Action _) SLOT _ = Err (E-Err λ ())
verifyAction (Ftch-Action sl) FTCH-LDG s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (sl≡slot x)))
  where
    sl≡slot : ∀ {s sl} → ValidAction (Ftch-Action sl) s FTCH-LDG → sl ≡ slot s
    sl≡slot Ftch = refl
... | yes p rewrite p = Ok Ftch
verifyAction (Slot-Action _) (INIT _) _ = Err (E-Err λ ())
verifyAction (Slot-Action _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (Slot-Action sl) SLOT s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (ValidAction→Eq-Slot x)))
... | yes p rewrite p
  with dec | dec | dec
... | yes x | yes y | yes z = Ok (Slot x y z)
... | no ¬p | _ | _ = Err (E-Err λ where (Slot p _ _) → ⊥-elim (¬p p))
... | _ | no ¬p | _ = Err (E-Err λ where (Slot _ p _) → ⊥-elim (¬p p))
... | _ | _ | no ¬p = Err (E-Err λ where (Slot _ _ p) → ⊥-elim (¬p p))
verifyAction (Slot-Action _) FTCH-LDG _ = Err (E-Err λ ())
verifyAction (Base₁-Action _) (INIT _) _ = Err (E-Err λ ())
verifyAction (Base₁-Action _) (SUBMIT (inj₁ _)) _ = Err (E-Err λ ())
verifyAction (Base₁-Action sl) (SUBMIT (inj₂ _)) s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (sl≡slot x)))
  where
    sl≡slot : ∀ {s sl} → ValidAction (Base₁-Action sl) s (SUBMIT (inj₂ _)) → sl ≡ slot s
    sl≡slot Base₁ = refl
... | yes p rewrite p = Ok Base₁
verifyAction (Base₁-Action _) SLOT _ = Err (E-Err λ ())
verifyAction (Base₁-Action _) FTCH-LDG _ = Err (E-Err λ ())
verifyAction (Base₂a-Action _ _) (INIT _) _ = Err (E-Err λ ())
verifyAction (Base₂a-Action _ _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (Base₂a-Action sl _) SLOT s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (sl≡slot x)))
  where
    sl≡slot : ∀ {s sl} → ValidAction (Base₂a-Action sl _) s SLOT → sl ≡ slot s
    sl≡slot (Base₂a _ _ _) = refl
... | yes p rewrite p
  with dec | dec | dec
... | yes x | yes y | yes z = Ok (Base₂a x y z)
... | no ¬p | _ | _ = Err (E-Err λ where (Base₂a p _ _) → ⊥-elim (¬p p))
... | _ | no ¬p | _ = Err (E-Err λ where (Base₂a _ p _) → ⊥-elim (¬p p))
... | _ | _ | no ¬p = Err (E-Err λ where (Base₂a _ _ p) → ⊥-elim (¬p p))
verifyAction (Base₂a-Action _ _) FTCH-LDG _ = Err (E-Err λ ())
verifyAction (Base₂b-Action _) (INIT _) _ = Err (E-Err λ ())
verifyAction (Base₂b-Action _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (Base₂b-Action sl) SLOT s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (sl≡slot x)))
  where
    sl≡slot : ∀ {s sl} → ValidAction (Base₂b-Action sl) s SLOT → sl ≡ slot s
    sl≡slot (Base₂b _ _ _) = refl
... | yes p rewrite p
  with dec | dec | dec
... | yes x | yes y | yes z = Ok (Base₂b x y z)
... | no ¬p | _ | _ = Err (E-Err λ where (Base₂b p _ _) → ⊥-elim (¬p p))
... | _ | no ¬p | _ = Err (E-Err λ where (Base₂b _ p _) → ⊥-elim (¬p p))
... | _ | _ | no ¬p = Err (E-Err λ where (Base₂b _ _ p) → ⊥-elim (¬p p))
verifyAction (Base₂b-Action _) FTCH-LDG _ = Err (E-Err λ ())
-}

data Err-verifyUpdate (μ : FFDUpdate) (s : LeiosState) : Type where
  E-Err : ¬ ValidUpdate μ s → Err-verifyUpdate μ s

{-
verifyUpdate : ∀ (μ : FFDUpdate) → (s : LeiosState) → Result (Err-verifyUpdate μ s) (ValidUpdate μ s)
verifyUpdate (IB-Recv-Update _) _ = Ok IB-Recv
verifyUpdate (EB-Recv-Update _) _ = Ok EB-Recv
verifyUpdate (VT-Recv-Update _) _ = Ok VT-Recv
-}
{-
data _⇑_ : LeiosState → LeiosState → Type where

  UpdateIB : ∀ {s ib} → let open LeiosState s renaming (FFDState to ffds) in
    s ⇑ record s { FFDState = record ffds { inIBs = ib ∷ inIBs ffds } }

  UpdateEB : ∀ {s eb} → let open LeiosState s renaming (FFDState to ffds) in
    s ⇑ record s { FFDState = record ffds { inEBs = eb ∷ inEBs ffds } }

  UpdateVT : ∀ {s vt} → let open LeiosState s renaming (FFDState to ffds) in
    s ⇑ record s { FFDState = record ffds { inVTs = vt ∷ inVTs ffds } }
-}

-- NOTE: this goes backwards, from the current state to the initial state
data _—→_ : LeiosState → LeiosState → Type where

  ActionStep : ∀ {s i o s′} →
    ∙ s -⟦ i / o ⟧⇀ s′
      ───────────────────
      s′ —→ s

{-
  UpdateStep : ∀ {s s′} →
    ∙ s ⇑ s′
      ───────────────────
      s′ —→ s
-}

  -- TODO: add base layer update

{-
ValidUpdate-sound : ∀ {μ} → ValidUpdate μ s → ∃[ s′ ](s ⇑ s′)
ValidUpdate-sound {s} (IB-Recv {ib = ib}) = record s { FFDState = record (FFDState s) { inIBs = ib ∷ inIBs (FFDState s)}} , UpdateIB
ValidUpdate-sound {s} (EB-Recv {eb = eb}) = record s { FFDState = record (FFDState s) { inEBs = eb ∷ inEBs (FFDState s)}} , UpdateEB
ValidUpdate-sound {s} (VT-Recv {vt = vt}) = record s { FFDState = record (FFDState s) { inVTs = vt ∷ inVTs (FFDState s)}} , UpdateVT
-}

open import Prelude.Closures _—→_

infix 0 _≈_

data _≈_ : TestTrace → s′ —↠ s → Type where

{-
  FromAction :
    ∀ α i {αs s₁} {tr : s₁ —↠ s}
      → αs ≈ tr
      → (vα : ValidAction₁ α s₁ i)
      → (α , i) ∷ αs ≈ _ —→⟨ ActionStep (ValidAction₁-sound vα) ⟩ tr
-}

  FromAction :
    ∀ i {αs s′ s₀ o} {tr : s —↠ s₀}
      → αs ≈ tr
      → (α : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
      → (getLabel α , i) ∷ αs ≈ s′ —→⟨ ActionStep α ⟩ tr

{-
  FromUpdate :
    ∀ {s} μ {αs s₁} {tr : s₁ —↠ s}
      → αs ≈ tr
      → (vμ : ValidUpdate μ s₁)
      → inj₂ μ ∷ αs ≈ ValidUpdate-sound vμ .proj₁ —→⟨ UpdateStep (proj₂ (ValidUpdate-sound vμ)) ⟩ tr
-}

  Done : [] ≈ s ∎


data ValidTrace (es : TestTrace) (s : LeiosState) : Type where
  Valid : (tr : s′ —↠ s) → es ≈ tr → ValidTrace es s

data Err-verifyTrace : TestTrace → LeiosState → Type where
  Err-StepOk   : Err-verifyTrace αs s → Err-verifyTrace ((α , i) ∷ αs) s
--  Err-UpdateOk : Err-verifyTrace αs s → Err-verifyTrace (inj₂ μ ∷ αs) s
  Err-Action   : Err-verifyAction α i s′ → Err-verifyTrace ((α , i) ∷ αs) s
--  Err-Update   : Err-verifyUpdate μ s′ → Err-verifyTrace (inj₂ μ ∷ αs) s

verifyTrace : ∀ (αs : TestTrace) → (s : LeiosState) → Result (Err-verifyTrace αs s) (ValidTrace αs s)
verifyTrace [] s = Ok (Valid (s ∎) Done)
verifyTrace ((IB-Role-Action n , FFDT.SLOT) ∷ αs) _
  with verifyTrace αs _
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with n ≟ slot s′ | sortition IB (slot s′) <? stake s′
--  with n ≟ slot s′ | dec
... | yes p | yes q rewrite p = do
  let
    step = IB-Role {s = s′} (q , refl) -- q
    b = ibBody (record { txs = (ToPropose s′) })
    h = ibHeader (mkIBHeader (slot s′) id tt sk-IB (ToPropose s′))
  let trace = (addUpkeep s′ IB-Role) —→⟨ ActionStep (Roles₁ {i = FFD.Send h (just b)} step ) ⟩ tr
  let act = FromAction FFDT.SLOT eq (Roles₁ step)
  return $ Valid trace act

{-
verifyTrace ((α , i) ∷ αs) s
  with verifyTrace αs s
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with verifyAction α i s′
... | Err e = mapErr Err-Action (Err e)
... | Ok p = Ok (Valid (_ —→⟨ ActionStep (ValidAction₁-sound p) ⟩ tr ) (FromAction α i eq p))
-}
{-
verifyTrace (inj₂ μ ∷ αs) s
  with verifyTrace αs s
... | Err e = mapErr Err-UpdateOk (Err e)
... | Ok (Valid {s′} tr eq)
  with verifyUpdate μ s′
... | Err e = mapErr Err-Update (Err e)
... | Ok p = Ok (Valid (ValidUpdate-sound p .proj₁ —→⟨ UpdateStep (ValidUpdate-sound p .proj₂) ⟩ tr) (FromUpdate μ eq p)) -}

open import Leios.Prelude hiding (id)
open import Leios.Config

import Data.List.Relation.Unary.All as A
open import Data.List.Relation.Unary.Unique.DecPropositional N._≟_

-- TODO: SpecStructure as parameter
module Leios.Short.Trace.Verifier (params : Params) (let open Params params) where

open import Leios.Defaults params
  using (LeiosState; initLeiosState; isb; hpe; hhs; htx; SendIB; FFDBuffers; Dec-SimpleFFD)
  renaming (d-SpecStructure to traceSpecStructure) public

open import Leios.SpecStructure using (SpecStructure)
open SpecStructure traceSpecStructure hiding (Hashable-IBHeader; Hashable-EndorserBlock; isVoteCertified) public

open import Leios.Short traceSpecStructure hiding (LeiosState; initLeiosState) public
open GenFFD

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

TestTrace = List ((Action × LeiosInput) ⊎ FFDUpdate)

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
  IB-Recv : ValidUpdate (IB-Recv-Update ib) s
  EB-Recv : ValidUpdate (EB-Recv-Update eb) s
  VT-Recv : ValidUpdate (VT-Recv-Update vt) s

data ValidAction : Action → LeiosState → LeiosInput → Type where

  IB-Role : let open LeiosState s renaming (FFDState to ffds)
                b = record { txs = ToPropose }
                h = mkIBHeader slot id tt sk-IB ToPropose
                ffds' = proj₁ (FFD.Send-total {ffds} {ibHeader h} {just (ibBody b)})
            in
            ∙ canProduceIB slot sk-IB (stake s) tt
            ∙ ffds FFD.-⟦ FFD.Send (ibHeader h) (just (ibBody b)) / FFD.SendRes ⟧⇀ ffds'
            ─────────────────────────────────────────────────────────────────────────
            ValidAction (IB-Role-Action slot) s SLOT

  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
                h = mkEB slot id tt sk-EB LI (L.map getEBRef ebs)
                ffds' = proj₁ (FFD.Send-total {ffds} {ebHeader h} {nothing})
                P = λ eb' → eb' ∈ˡ EBs
                          × isVoteCertified s eb'
                          × eb' ∈ᴮ slices L slot (3 * η / L) 2
                slots = map slotNumber
            in
            ∙ canProduceEB slot sk-EB (stake s) tt
            ∙ A.All P ebs
            ∙ Unique (slots ebs) × fromList (slots ebs) ≡ᵉ fromList (slots (filter P EBs))
            ∙ ffds FFD.-⟦ FFD.Send (ebHeader h) nothing / FFD.SendRes ⟧⇀ ffds'
            ─────────────────────────────────────────────────────────────────────────
            ValidAction (EB-Role-Action slot LI ebs) s SLOT

  VT-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
                votes = map (vote sk-VT ∘ hash) EBs'
                ffds' = proj₁ (FFD.Send-total {ffds} {vtHeader votes} {nothing})
            in
            ∙ canProduceV slot sk-VT (stake s)
            ∙ ffds FFD.-⟦ FFD.Send (vtHeader votes) nothing / FFD.SendRes ⟧⇀ ffds'
            ─────────────────────────────────────────────────────────────────────────
            ValidAction (VT-Role-Action slot) s SLOT

  No-IB-Role : let open LeiosState s
               in
               ∙ needsUpkeep IB-Role
               ∙ (∀ π → ¬ canProduceIB slot sk-IB (stake s) π)
               ───────────────────────────────────────────────
               ValidAction (No-IB-Role-Action slot) s SLOT

  No-EB-Role : let open LeiosState s
               in
               ∙ needsUpkeep EB-Role
               ∙ (∀ π → ¬ canProduceEB slot sk-EB (stake s) π)
               ───────────────────────────────────────────────
               ValidAction (No-EB-Role-Action slot) s SLOT

  No-VT-Role : let open LeiosState s
               in
               ∙ needsUpkeep-Stage VT-Role →
               ∙ (¬ canProduceV slot sk-VT (stake s))
               ───────────────────────────────────────────────
               ValidAction (No-VT-Role-Action slot) s SLOT

  Slot : let open LeiosState s renaming (FFDState to ffds; BaseState to bs)
             (res , (bs' , _))    = B.FTCH-total {bs}
             (msgs , (ffds' , _)) = FFD.Fetch-total {ffds}
         in
         ∙ allDone s
         ∙ bs B.-⟦ B.FTCH-LDG / B.BASE-LDG res ⟧⇀ bs'
         ∙ ffds FFD.-⟦ FFD.Fetch / FFD.FetchRes msgs ⟧⇀ ffds'
         ─────────────────────────────────────────────────────────────────────────
         ValidAction (Slot-Action slot) s SLOT

  Ftch : ValidAction (Ftch-Action (LeiosState.slot s)) s FTCH-LDG

  Base₁ : ∀ {txs} → ValidAction (Base₁-Action (LeiosState.slot s)) s (SUBMIT (inj₂ txs))

  Base₂a : ∀ {eb} → let open LeiosState s renaming (BaseState to bs)
           in
           ∙ needsUpkeep Base
           ∙ eb ∈ filter (λ eb' → isVoteCertified s eb' × eb' ∈ᴮ slice L slot 2) EBs
           ∙ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ tt
           ─────────────────────────────────────────────────────────────────────────
           ValidAction (Base₂a-Action slot eb) s SLOT

  Base₂b : let open LeiosState s renaming (BaseState to bs)
           in
           ∙ needsUpkeep Base
           ∙ [] ≡ filter (λ eb' → isVoteCertified s eb' × eb' ∈ᴮ slice L slot 2) EBs
           ∙ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ tt
           ─────────────────────────────────────────────────────────────────────────
           ValidAction (Base₂b-Action slot) s SLOT

private variable
  i : LeiosInput
  o : LeiosOutput

⟦_⟧ : ValidAction α s i → LeiosState × LeiosOutput
⟦ IB-Role {s} _ _ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      b = record { txs = ToPropose }
      h = mkIBHeader slot id tt sk-IB ToPropose
      ffds' = proj₁ (FFD.Send-total {ffds} {ibHeader h} {just (ibBody b)})
  in addUpkeep record s { FFDState = ffds' } IB-Role , EMPTY
⟦ EB-Role {s} {ebs} _ _ _ _ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
      h = mkEB slot id tt sk-EB LI (L.map getEBRef ebs)
      ffds' = proj₁ (FFD.Send-total {ffds} {ebHeader h} {nothing})
  in addUpkeep record s { FFDState = ffds' } EB-Role , EMPTY
⟦ VT-Role {s} _ _ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
      votes = map (vote sk-VT ∘ hash) EBs'
      ffds' = proj₁ (FFD.Send-total {ffds} {vtHeader votes} {nothing})
  in addUpkeep-Stage record s { FFDState = ffds' } VT-Role , EMPTY
⟦ No-IB-Role {s} _ _ ⟧ = addUpkeep s IB-Role , EMPTY
⟦ No-EB-Role {s} _ _ ⟧ = addUpkeep s EB-Role , EMPTY
⟦ No-VT-Role {s} _ _ ⟧ = addUpkeep-Stage s VT-Role , EMPTY
⟦ Slot {s} _ _ _ ⟧ =
  let open LeiosState s renaming (FFDState to ffds; BaseState to bs)
      (res , (bs' , _))    = B.FTCH-total {bs}
      (msgs , (ffds' , _)) = FFD.Fetch-total {ffds}
  in
  (record s
     { FFDState     = ffds'
     ; BaseState    = bs'
     ; Ledger       = constructLedger res
     ; slot         = suc slot
     ; Upkeep       = ∅
     ; Upkeep-Stage = ifᵈ (endOfStage slot) then ∅ else Upkeep-Stage
     } ↑ L.filter (isValid? s) msgs
  , EMPTY)
⟦ Ftch {s} ⟧ = s , FTCH-LDG (LeiosState.Ledger s)
⟦ Base₁ {s} {txs} ⟧ = record s { ToPropose = txs } , EMPTY
⟦ Base₂a {s} {eb} _ _ _ ⟧ =
  let (bs' , _) = B.SUBMIT-total {LeiosState.BaseState s} {this eb}
  in addUpkeep record s { BaseState = bs' } Base , EMPTY
⟦ Base₂b {s} _ _ _ ⟧ =
  let (bs' , _) = B.SUBMIT-total {LeiosState.BaseState s} {that (LeiosState.ToPropose s)}
  in addUpkeep record s { BaseState = bs' } Base , EMPTY

open LeiosState
open FFDBuffers

ValidAction→Eq-Slot : ∀ {s sl} → ValidAction (Slot-Action sl) s SLOT → sl ≡ slot s
ValidAction→Eq-Slot (Slot _ _ _) = refl

ValidAction→Eq-IB : ∀ {s sl} → ValidAction (IB-Role-Action sl) s SLOT → sl ≡ slot s
ValidAction→Eq-IB (IB-Role _ _) = refl

ValidAction→Eq-EB : ∀ {s sl ibs ebs} → ValidAction (EB-Role-Action sl ibs ebs) s SLOT → sl ≡ slot s × ibs ≡ (map getIBRef $ filter (_∈ᴮ slice L (slot s) 3) (IBs s))
ValidAction→Eq-EB (EB-Role _ _ _ _) = refl , refl

ValidAction→Eq-VT : ∀ {s sl} → ValidAction (VT-Role-Action sl) s SLOT → sl ≡ slot s
ValidAction→Eq-VT (VT-Role _ _) = refl

getLabel : just s -⟦ i / o ⟧⇀ s′ → Action
getLabel (Slot {s} _ _ _)                        = Slot-Action (slot s)
getLabel (Ftch {s})                              = Ftch-Action (slot s)
getLabel (Base₁ {s})                             = Base₁-Action (slot s)
getLabel (Base₂a {s} {eb} _ _ _)                 = Base₂a-Action (slot s) eb
getLabel (Base₂b {s} _ _ _)                      = Base₂b-Action (slot s)
getLabel (Roles (IB-Role {s} _ _))               = IB-Role-Action (slot s)
getLabel (Roles (EB-Role {s} {_} {ebs} _ _ _ _)) = EB-Role-Action (slot s) (map getIBRef $ filter (_∈ᴮ slice L (slot s) 3) (IBs s)) ebs
getLabel (Roles (VT-Role {s} _ _))               = VT-Role-Action (slot s)
getLabel (Roles (No-IB-Role {s} _ _))            = No-IB-Role-Action (slot s)
getLabel (Roles (No-EB-Role {s} _ _))            = No-EB-Role-Action (slot s)
getLabel (Roles (No-VT-Role {s} _ _))            = No-VT-Role-Action (slot s)

ValidAction-sound : (vα : ValidAction α s i) → let (s′ , o) = ⟦ vα ⟧ in just s -⟦ i / o ⟧⇀ s′
ValidAction-sound (Slot x x₁ x₂)       = Slot {rbs = []} x x₁ x₂
ValidAction-sound Ftch                 = Ftch
ValidAction-sound Base₁                = Base₁
ValidAction-sound (Base₂a x x₁ x₂)     = Base₂a x x₁ x₂
ValidAction-sound (Base₂b x x₁ x₂)     = Base₂b x x₁ x₂
ValidAction-sound (IB-Role x₁ x₂)      = Roles (IB-Role x₁ x₂)
ValidAction-sound (EB-Role x x₁ x₂ x₃) = Roles (EB-Role x x₁ x₂ x₃)
ValidAction-sound (VT-Role x₁ x₂)      = Roles (VT-Role x₁ x₂)
ValidAction-sound (No-IB-Role x x₁)    = Roles (No-IB-Role x x₁)
ValidAction-sound (No-EB-Role x x₁)    = Roles (No-EB-Role x x₁)
ValidAction-sound (No-VT-Role x x₁)    = Roles (No-VT-Role x x₁)

ValidAction-complete : (st : just s -⟦ i / o ⟧⇀ s′) → ValidAction (getLabel st) s i
ValidAction-complete {s} {s′} (Roles (IB-Role {s} {π} {ffds'} x₁ _)) =
  let b  = record { txs = ToPropose s }
      h  = mkIBHeader (slot s) id tt sk-IB (ToPropose s)
      pr = proj₂ (FFD.Send-total {FFDState s} {ibHeader h} {just (ibBody b)})
  in IB-Role {s} x₁ pr
ValidAction-complete {s} (Roles (EB-Role {ebs = ebs} x₁ x₂ x₃ _)) =
  let LI = map getIBRef $ filter (_∈ᴮ slice L (slot s) 3) (IBs s)
      h  = mkEB (slot s) id tt sk-EB LI (map getEBRef ebs)
      pr = proj₂ (FFD.Send-total {FFDState s} {ebHeader h} {nothing})
  in EB-Role {s} x₁ x₂ x₃ pr
ValidAction-complete {s} (Roles (VT-Role x₁ _))  =
  let EBs'  = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L (slot s) 1) (EBs s)
      votes = map (vote sk-VT ∘ hash) EBs'
      pr    = proj₂ (FFD.Send-total {FFDState s} {vtHeader votes} {nothing})
  in VT-Role {s} x₁ pr
ValidAction-complete (Roles (No-IB-Role x x₁)) = No-IB-Role x x₁
ValidAction-complete (Roles (No-EB-Role x x₁)) = No-EB-Role x x₁
ValidAction-complete (Roles (No-VT-Role x x₁)) = No-VT-Role x x₁
ValidAction-complete Ftch                      = Ftch
ValidAction-complete Base₁                     = Base₁
ValidAction-complete (Base₂a x x₁ x₂)          = Base₂a x x₁ x₂
ValidAction-complete (Base₂b x x₁ x₂)          = Base₂b x x₁ x₂
ValidAction-complete {s} (Slot x x₁ _)         = Slot x x₁ (proj₂ (proj₂ (FFD.Fetch-total {FFDState s})))

-- TODO: Use Result type from Prelude
private variable
  A B E E₁ : Type

data Result (E A : Type) : Type where
  Ok  : A → Result E A
  Err : E → Result E A

mapErr : (E → E₁) → Result E A → Result E₁ A
mapErr f (Ok x)  = Ok x
mapErr f (Err e) = Err (f e)

IsOk : Result E A → Type
IsOk (Ok _)  = ⊤
IsOk (Err _) = ⊥

data Err-verifyAction (α : Action) (i : LeiosInput) (s : LeiosState) : Type where
  E-Err : ¬ ValidAction α s i → Err-verifyAction α i s

verifyAction : ∀ (α : Action) → (i : LeiosInput) → (s : LeiosState) → Result (Err-verifyAction α i s) (ValidAction α s i)
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
  with sl ≟ slot s | ibs ≟ (map getIBRef $ filter (_∈ᴮ slice L (slot s) 3) (IBs s))
... | no ¬p | _ = Err (E-Err λ x → ⊥-elim (¬p (proj₁ $ ValidAction→Eq-EB x)))
... | _ | no ¬q = Err (E-Err λ x → ⊥-elim (¬q (proj₂ $ ValidAction→Eq-EB x)))
... | yes p | yes q rewrite p rewrite q
  with dec | dec | dec | dec
... | yes x | yes y | yes z | yes w = Ok (EB-Role x y z w)
... | no ¬p | _ | _ | _ = Err (E-Err λ where (EB-Role p _ _ _) → ⊥-elim (¬p p))
... | _ | no ¬p | _ | _ = Err (E-Err λ where (EB-Role _ p _ _) → ⊥-elim (¬p p))
... | _ | _ | no ¬p | _ = Err (E-Err λ where (EB-Role _ _ p _) → ⊥-elim (¬p p))
... | _ | _ | _ | no ¬p = Err (E-Err λ where (EB-Role _ _ _ p) → ⊥-elim (¬p p))
verifyAction (EB-Role-Action _ _ _) FTCH-LDG _ = Err (E-Err λ ())
verifyAction (VT-Role-Action _) (INIT _) _ = Err (E-Err λ ())
verifyAction (VT-Role-Action _) (SUBMIT _) _ = Err (E-Err λ ())
verifyAction (VT-Role-Action sl) SLOT s
  with sl ≟ slot s
... | no ¬p = Err (E-Err λ x → ⊥-elim (¬p (ValidAction→Eq-VT x)))
... | yes p rewrite p
  with dec | dec
... | yes x | yes y = Ok (VT-Role x y)
... | no ¬p | _ = Err (E-Err λ where (VT-Role p _) → ⊥-elim (¬p p))
... | _ | no ¬p = Err (E-Err λ where (VT-Role _ p) → ⊥-elim (¬p p))
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

data Err-verifyUpdate (μ : FFDUpdate) (s : LeiosState) : Type where
  E-Err : ¬ ValidUpdate μ s → Err-verifyUpdate μ s

verifyUpdate : ∀ (μ : FFDUpdate) → (s : LeiosState) → Result (Err-verifyUpdate μ s) (ValidUpdate μ s)
verifyUpdate (IB-Recv-Update _) _ = Ok IB-Recv
verifyUpdate (EB-Recv-Update _) _ = Ok EB-Recv
verifyUpdate (VT-Recv-Update _) _ = Ok VT-Recv

data _⇑_ : LeiosState → LeiosState → Type where

  UpdateIB : ∀ {s ib} → let open LeiosState s renaming (FFDState to ffds) in
    s ⇑ record s { FFDState = record ffds { inIBs = ib ∷ inIBs ffds } }

  UpdateEB : ∀ {s eb} → let open LeiosState s renaming (FFDState to ffds) in
    s ⇑ record s { FFDState = record ffds { inEBs = eb ∷ inEBs ffds } }

  UpdateVT : ∀ {s vt} → let open LeiosState s renaming (FFDState to ffds) in
    s ⇑ record s { FFDState = record ffds { inVTs = vt ∷ inVTs ffds } }

-- NOTE: this goes backwards, from the current state to the initial state
data _—→_ : LeiosState → LeiosState → Type where

  ActionStep : ∀ {s i o s′} →
    ∙ just s -⟦ i / o ⟧⇀ s′
      ───────────────────
      s′ —→ s

  UpdateStep : ∀ {s s′} →
    ∙ s ⇑ s′
      ───────────────────
      s′ —→ s

  -- TODO: add base layer update

ValidUpdate-sound : ∀ {μ} → ValidUpdate μ s → ∃[ s′ ](s ⇑ s′)
ValidUpdate-sound {s} (IB-Recv {ib = ib}) = record s { FFDState = record (FFDState s) { inIBs = ib ∷ inIBs (FFDState s)}} , UpdateIB
ValidUpdate-sound {s} (EB-Recv {eb = eb}) = record s { FFDState = record (FFDState s) { inEBs = eb ∷ inEBs (FFDState s)}} , UpdateEB
ValidUpdate-sound {s} (VT-Recv {vt = vt}) = record s { FFDState = record (FFDState s) { inVTs = vt ∷ inVTs (FFDState s)}} , UpdateVT

open import Prelude.Closures _—→_

infix 0 _≈_

data _≈_ : TestTrace → s′ —↠ s → Type where

  FromAction :
    ∀ α i {αs s₁} {tr : s₁ —↠ s}
      → αs ≈ tr
      → (vα : ValidAction α s₁ i)
      → inj₁ (α , i) ∷ αs ≈ ⟦ vα ⟧ .proj₁ —→⟨ ActionStep (ValidAction-sound vα) ⟩ tr

  FromUpdate :
    ∀ {s} μ {αs s₁} {tr : s₁ —↠ s}
      → αs ≈ tr
      → (vμ : ValidUpdate μ s₁)
      → inj₂ μ ∷ αs ≈ ValidUpdate-sound vμ .proj₁ —→⟨ UpdateStep (proj₂ (ValidUpdate-sound vμ)) ⟩ tr

  Done : [] ≈ s ∎

data ValidTrace (es : TestTrace) (s : LeiosState) : Type where
  Valid : (tr : s′ —↠ s) → es ≈ tr → ValidTrace es s

data Err-verifyTrace : TestTrace → LeiosState → Type where
  Err-StepOk   : Err-verifyTrace αs s → Err-verifyTrace (inj₁ (α , i) ∷ αs) s
  Err-UpdateOk : Err-verifyTrace αs s → Err-verifyTrace (inj₂ μ ∷ αs) s
  Err-Action   : Err-verifyAction α i s′ → Err-verifyTrace (inj₁ (α , i) ∷ αs) s
  Err-Update   : Err-verifyUpdate μ s′ → Err-verifyTrace (inj₂ μ ∷ αs) s

verifyTrace : ∀ (αs : TestTrace) → (s : LeiosState) → Result (Err-verifyTrace αs s) (ValidTrace αs s)
verifyTrace [] s = Ok (Valid (s ∎) Done)
verifyTrace (inj₁ (α , i) ∷ αs) s
  with verifyTrace αs s
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with verifyAction α i s′
... | Err e = mapErr Err-Action (Err e)
... | Ok p = Ok (Valid {s′ = ⟦ p ⟧ .proj₁} (⟦ p ⟧ .proj₁ —→⟨ ActionStep (ValidAction-sound p) ⟩ tr ) (FromAction α i eq p))
verifyTrace (inj₂ μ ∷ αs) s
  with verifyTrace αs s
... | Err e = mapErr Err-UpdateOk (Err e)
... | Ok (Valid {s′} tr eq)
  with verifyUpdate μ s′
... | Err e = mapErr Err-Update (Err e)
... | Ok p = Ok (Valid (ValidUpdate-sound p .proj₁ —→⟨ UpdateStep (ValidUpdate-sound p .proj₂) ⟩ tr) (FromUpdate μ eq p))

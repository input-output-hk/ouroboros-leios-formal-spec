open import Leios.Prelude hiding (id)
open import Leios.Config

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
  i    : FFDT Out
  o    : FFDT In

open LeiosState
open FFDBuffers

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

data Err-verifyAction (α : Action) (i : FFDT Out) (s : LeiosState) : Type where
--  E-Err : ¬ ValidAction α s i → Err-verifyAction α i s

-- NOTE: this goes backwards, from the current state to the initial state
data _—→_ : LeiosState → LeiosState → Type where

  ActionStep : ∀ {s i o s′} →
    ∙ s -⟦ i / o ⟧⇀ s′
      ───────────────────
      s′ —→ s

open import Prelude.Closures _—→_

infix 0 _≈_

data _≈_ : TestTrace → s′ —↠ s → Type where

  FromAction :
    ∀ i {αs s′ s₀ o} {tr : s —↠ s₀}
      → αs ≈ tr
      → (α : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
      → (getLabel α , i) ∷ αs ≈ s′ —→⟨ ActionStep α ⟩ tr

  Done : [] ≈ s ∎

data ValidTrace (es : TestTrace) (s : LeiosState) : Type where
  Valid : (tr : s′ —↠ s) → es ≈ tr → ValidTrace es s

data Err-verifyTrace : TestTrace → LeiosState → Type where
  Err-StepOk   : Err-verifyTrace αs s → Err-verifyTrace ((α , i) ∷ αs) s
  Err-Action   : Err-verifyAction α i s′ → Err-verifyTrace ((α , i) ∷ αs) s

verifyTrace : ∀ (αs : TestTrace) → (s : LeiosState) → Result (Err-verifyTrace αs s) (ValidTrace αs s)
verifyTrace [] s = Ok (Valid (s ∎) Done)
verifyTrace ((IB-Role-Action n , FFDT.SLOT) ∷ αs) _
  with verifyTrace αs _
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with n ≟ slot s′ | ¿ canProduceIB (slot s′) sk-IB (stake s′) tt ¿
... | yes p | yes q rewrite p =
  let
    st = IB-Role {s = s′} q
    b  = ibBody (record { txs = (ToPropose s′) })
    h  = ibHeader (mkIBHeader (slot s′) id tt sk-IB (ToPropose s′))
    ex = _ —→⟨ ActionStep (Roles₁ {i = FFD.Send h (just b)} st ) ⟩ tr
    ac = FromAction FFDT.SLOT eq (Roles₁ st)
  in Ok (Valid ex ac)
... | no ¬p | _ = {!!}
... | _ | no ¬q = {!!}
verifyTrace ((IB-Role-Action n , _) ∷ αs) _ = {!!}

verifyTrace ((EB-Role-Action n ibs ebs , FFDT.SLOT) ∷ αs) _
  with verifyTrace αs _
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with n ≟ slot s′
    | ¿ needsUpkeep s′ EB-Role ¿
    | ¿ canProduceEB (slot s′) sk-EB (stake s′) tt ¿
    | ¿ All.All (λ x → isVoteCertified s′ x × x ∈ˡ (EBs s′) × x ∈ᴮ slices L (slot s′) 2 (3 * η / L)) ebs ¿
    | ¿ Unique (map slotNumber ebs) × fromList (map slotNumber ebs) ≡ᵉ fromList (map slotNumber (filter (λ x → isVoteCertified s′ x × x ∈ˡ (EBs s′) × x ∈ᴮ slices L (slot s′) 2 (3 * η / L)) (EBs s′))) ¿
    | ibs ≟  map getIBRef (L.filter (IBSelection? s′ Late-IB-Inclusion) (IBs s′))
... | yes p | yes x₁ | yes x₂ | yes x₃ | yes x₄ | yes q rewrite p rewrite q =
  let
    ibs = L.filter (IBSelection? s′ Late-IB-Inclusion) (IBs s′)
    LI  = map getIBRef ibs
    LE  = map getEBRef ebs
    h   = mkEB (slot s′) id tt sk-EB LI LE
    st = EB-Role {s = s′} x₁ x₂ x₃ x₄
    ex = _ —→⟨ ActionStep (Roles₁ {i = FFD.Send (ebHeader h) nothing} st ) ⟩ tr
    ac = FromAction FFDT.SLOT eq (Roles₁ st)
  in Ok (Valid ex ac)

verifyTrace ((EB-Role-Action n ibs ebs , _) ∷ αs) _ = {!!}

verifyTrace ((VT-Role-Action n , FFDT.SLOT) ∷ αs) _
  with verifyTrace αs _
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with n ≟ slot s′
    | ¿ needsUpkeep-Stage s′ VT-Role ¿
    | ¿ canProduceV (slot s′) sk-VT (stake s′) ¿
... | yes p | yes x₁ | yes x₂ rewrite p =
  let
    st = VT-Role x₁ x₂
    EBs' = filter (allIBRefsKnown s′) $ filter (_∈ᴮ slice L (slot s′) 1) (EBs s′)
    votes = map (vote sk-VT ∘ hash) EBs'
    ex = _ —→⟨ ActionStep (Roles₁ {i = FFD.Send (vtHeader votes) nothing} st ) ⟩ tr
    ac = FromAction FFDT.SLOT eq (Roles₁ st)
  in Ok (Valid ex ac)
... | no ¬p | _ | _ = {!!}
... | _ | no ¬q | _ = {!!}
verifyTrace ((VT-Role-Action n , _) ∷ αs) _ = {!!}

verifyTrace ((No-IB-Role-Action n , FFDT.SLOT) ∷ αs) _
  with verifyTrace αs _
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with n ≟ slot s′
... | no ¬p = Err {!!} -- (E-Err λ x → ⊥-elim (¬p ?)) -- (sl≡slot x)))
... | yes p rewrite p
  with ¿ needsUpkeep s′ IB-Role ¿ | ¿ (∀ π → ¬ canProduceIB (slot s′) (IB , tt) (stake s′) π) ¿
... | yes p | yes q =
  let
    st = Roles₂ (No-IB-Role p q)
    ex = _ —→⟨ ActionStep st ⟩ tr
    ac = FromAction FFDT.SLOT eq st
  in Ok (Valid ex ac)
... | no ¬p | _ = Err {!!} -- (E-Err λ where (No-IB-Role p _) → ⊥-elim (¬p p))
... | _ | no ¬q = Err {!!} -- (E-Err λ where (No-IB-Role _ q) → ⊥-elim (¬q q))
verifyTrace ((No-IB-Role-Action n , _) ∷ αs) _ = {!!}
verifyTrace ((No-EB-Role-Action n , _) ∷ αs) _ = {!!}
verifyTrace ((No-VT-Role-Action n , _) ∷ αs) _ = {!!}

verifyTrace ((Ftch-Action n , FFDT.FTCH) ∷ αs) _
  with verifyTrace αs _
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with n ≟ slot s′
... | yes p rewrite p =
  let
    st = Ftch
    ex = _ —→⟨ ActionStep st ⟩ tr
    ac = FromAction FFDT.FTCH eq {!st!}
  in Ok (Valid ex {!ac!})

--verifyTrace ((Ftch-Action n , _) ∷ αs) _ = {!!}

verifyTrace ((Slot-Action n , FFDT.SLOT) ∷ αs) _
  with verifyTrace αs _
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with n ≟ slot s′
... | no ¬p = Err {!!} -- (E-Err λ x → ⊥-elim (¬p (ValidAction→Eq-Slot x)))
... | yes p rewrite p
  with ¿ allDone s′ ¿
... | yes x =
  let
    st = Slot₁ x
    ex = _ —→⟨ ActionStep st ⟩ tr
    ac = FromAction FFDT.SLOT eq st
  in Ok (Valid ex ac)
... | no ¬p = Err {!!} -- (E-Err λ where (Slot p _ _) → ⊥-elim (¬p p))
verifyTrace ((Slot-Action n , _) ∷ αs) _ = {!!}

verifyTrace ((Base₁-Action n , _) ∷ αs) _
  with verifyTrace αs _
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with n ≟ slot s′
... | no ¬p = Err {!!} -- (E-Err λ x → ⊥-elim (¬p (ValidAction→Eq-Slot x)))
... | yes p rewrite p =
  let
    st = Base₁
    ex = _ —→⟨ ActionStep st ⟩ tr
    ac = FromAction {!!} eq {!!} -- st
  in Ok (Valid ex {!!}) -- ac)

verifyTrace ((Base₂a-Action n eb , FFDT.SLOT) ∷ αs) _
  with verifyTrace αs _
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with n ≟ slot s′
... | no ¬p = Err {!!} -- (E-Err λ x → ⊥-elim (¬p (ValidAction→Eq-Slot x)))
... | yes p rewrite p
  with ¿ needsUpkeep s′ Base ¿
    | ¿ eb ∈ filter (λ x → isVoteCertified s′ x × x ∈ᴮ slice L (slot s′) 2) (EBs s′) ¿
... | yes x₁ | yes x₂ =
  let
    st = Base₂a x₁ x₂
    ex = _ —→⟨ ActionStep st ⟩ tr
    ac = FromAction FFDT.SLOT eq st
  in Ok (Valid ex ac)
... | no ¬p | _ = Err {!!} -- (E-Err λ where (Slot p _ _) → ⊥-elim (¬p p))
verifyTrace ((Base₂a-Action n eb , _) ∷ αs) _ = {!!}

verifyTrace ((Base₂b-Action n , FFDT.SLOT) ∷ αs) _
  with verifyTrace αs _
... | Err e = mapErr Err-StepOk (Err e)
... | Ok (Valid {s′} tr eq)
  with n ≟ slot s′
... | no ¬p = Err {!!} -- (E-Err λ x → ⊥-elim (¬p (ValidAction→Eq-Slot x)))
... | yes p rewrite p
  with ¿ needsUpkeep s′ Base ¿
    | ¿ [] ≡ filter (λ x → isVoteCertified s′ x × x ∈ᴮ slice L (slot s′) 2) (EBs s′) ¿
... | yes x₁ | yes x₂ =
  let
    st = Base₂b x₁ x₂
    ex = _ —→⟨ ActionStep st ⟩ tr
    ac = FromAction FFDT.SLOT eq st
  in Ok (Valid ex ac)
... | no ¬p | _ = Err {!!} -- (E-Err λ where (Slot p _ _) → ⊥-elim (¬p p))
verifyTrace ((Base₂b-Action n , _) ∷ αs) _ = {!!}

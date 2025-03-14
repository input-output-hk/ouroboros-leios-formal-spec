open import Leios.Prelude hiding (id)

module Leios.Trace.TraceVerifier where

open import Leios.SpecStructure using (SpecStructure)
open import Leios.Defaults 2 fzero using (st; sd; LeiosState; initLeiosState; isb; hpe; hhs; htx; SendIB; FFDState; Dec-SimpleFFD; send-total; fetch-total)
open import Leios.Trace.Verifier st
open SpecStructure st hiding (Hashable-IBHeader; Hashable-EndorserBlock; isVoteCertified)

open import Leios.Short st hiding (LeiosState; initLeiosState)
open import Prelude.Closures _↝_
open GenFFD

data Action : Type where
  IB-Role-Action EB-Role-Action V-Role-Action : Action
  No-IB-Role-Action No-EB-Role-Action No-V-Role-Action : Action
  Ftch-Action Slot-Action : Action
  -- Base₁-Action Base₂a-Action Base₂b-Action : Action

Actions = List (Action × LeiosInput)

private variable
  s s′ : LeiosState
  α : Action

data ValidAction : Action → LeiosState → LeiosInput → Type where

  IB-Role : let open LeiosState s renaming (FFDState to ffds)
                b = record { txs = ToPropose }
                h = mkIBHeader slot id tt sk-IB ToPropose
                ffds' = proj₁ (send-total {ffds} {ibHeader h} {just (ibBody b)})
            in .(needsUpkeep IB-Role) →
               .(canProduceIB slot sk-IB (stake s) tt) →
               .(ffds FFD.-⟦ FFD.Send (ibHeader h) (just (ibBody b)) / FFD.SendRes ⟧⇀ ffds') →
               ValidAction IB-Role-Action s SLOT

  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
                h = mkEB slot id tt sk-EB LI []
                ffds' = proj₁ (send-total {ffds} {ebHeader h} {nothing})
            in .(needsUpkeep EB-Role) →
               .(canProduceEB slot sk-EB (stake s) tt) →
               .(ffds FFD.-⟦ FFD.Send (ebHeader h) nothing / FFD.SendRes ⟧⇀ ffds') →
               ValidAction EB-Role-Action s SLOT

  V-Role  : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
                votes = map (vote sk-V ∘ hash) EBs'
                ffds' = proj₁ (send-total {ffds} {vHeader votes} {nothing})
            in .(needsUpkeep V-Role) →
               .(canProduceV slot sk-V (stake s)) →
               .(ffds FFD.-⟦ FFD.Send (vHeader votes) nothing / FFD.SendRes ⟧⇀ ffds') →
               ValidAction V-Role-Action s SLOT

  No-IB-Role : let open LeiosState s
               in needsUpkeep IB-Role →
                  (∀ π → ¬ canProduceIB slot sk-IB (stake s) π) →
                  ValidAction No-IB-Role-Action s SLOT

  No-EB-Role : let open LeiosState s
               in needsUpkeep EB-Role →
                  (∀ π → ¬ canProduceEB slot sk-EB (stake s) π) →
                  ValidAction No-EB-Role-Action s SLOT

  No-V-Role : let open LeiosState s
              in needsUpkeep V-Role →
                 (¬ canProduceV slot sk-V (stake s)) →
                 ValidAction No-V-Role-Action s SLOT

  Slot : let open LeiosState s renaming (FFDState to ffds; BaseState to bs)
             (msgs , (ffds' , _)) = fetch-total {ffds}
         in .(Upkeep ≡ᵉ allUpkeep) →
            .(bs B.-⟦ B.FTCH-LDG / B.BASE-LDG [] ⟧⇀ tt) → -- TODO: rbs ≠ []
            .(ffds FFD.-⟦ FFD.Fetch / FFD.FetchRes msgs ⟧⇀ ffds') →
            ValidAction Slot-Action s SLOT

  Ftch : ValidAction Ftch-Action s FTCH-LDG

{-
  Base₁ : ∀ {txs} → ValidAction Base₁-Action s (SUBMIT (inj₂ txs))

  Base₂a : ∀ {eb} → let open LeiosState s renaming (BaseState to bs)
           in .(needsUpkeep Base) →
              .(eb ∈ filter (λ eb → isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs) →
              .(bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ tt) →
              ValidAction Base₂a-Action s SLOT

  Base₂b : let open LeiosState s renaming (BaseState to bs)
           in .(needsUpkeep Base) →
              .([] ≡ filter (λ eb → isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs) →
              .(bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ tt) →
              ValidAction Base₂b-Action s SLOT
-}

private variable
  i : LeiosInput
  o : LeiosOutput

⟦_⟧ : ValidAction α s i → LeiosState × LeiosOutput
⟦ IB-Role {s} x x₁ x₂ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      b = record { txs = ToPropose }
      h = mkIBHeader slot id tt sk-IB ToPropose
      ffds' = proj₁ (send-total {ffds} {ibHeader h} {just (ibBody b)})
  in addUpkeep record s { FFDState = ffds' } IB-Role , EMPTY
⟦ EB-Role {s} x x₁ x₂ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
      h = mkEB slot id tt sk-EB LI []
      ffds' = proj₁ (send-total {ffds} {ebHeader h} {nothing})
  in addUpkeep record s { FFDState = ffds' } EB-Role , EMPTY
⟦ V-Role {s} x x₁ x₂ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
      votes = map (vote sk-V ∘ hash) EBs'
      ffds' = proj₁ (send-total {ffds} {vHeader votes} {nothing})
  in addUpkeep record s { FFDState = ffds' } V-Role , EMPTY
⟦ No-IB-Role {s} x x₁ ⟧ = addUpkeep s IB-Role , EMPTY
⟦ No-EB-Role {s} x x₁ ⟧ = addUpkeep s EB-Role , EMPTY
⟦ No-V-Role {s} x x₁ ⟧ = addUpkeep s V-Role , EMPTY
⟦ Slot {s} x x₁ x₂ ⟧ =
  let open LeiosState s renaming (FFDState to ffds; BaseState to bs)
      (msgs , (ffds' , _)) = fetch-total {ffds}
  in
  (record s
     { FFDState  = ffds'
     ; BaseState = tt -- bs'
     ; Ledger    = constructLedger [] -- rbs
     ; slot      = suc slot
     ; Upkeep    = ∅
     } ↑ L.filter isValid? msgs
  , EMPTY)
⟦ Ftch {s} ⟧ = s , FTCH-LDG (LeiosState.Ledger s)
-- ⟦ Base₁ {s} {txs} ⟧ = record s { ToPropose = txs } , EMPTY
-- ⟦ Base₂a {s} x x₁ x₂ ⟧ = addUpkeep record s { BaseState = tt } Base , EMPTY
-- ⟦ Base₂b {s} x x₁ x₂ ⟧ = addUpkeep record s { BaseState = tt } Base , EMPTY

instance
  Dec-ValidAction : ValidAction ⁇³
  Dec-ValidAction {IB-Role-Action} {s} {SLOT} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (IB-Role x y z)
  ... | no ¬p | _ | _ = no λ where (IB-Role p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (IB-Role _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (IB-Role _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {IB-Role-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {IB-Role-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {IB-Role-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {EB-Role-Action} {s} {SLOT} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (EB-Role x y z)
  ... | no ¬p | _ | _ = no λ where (EB-Role p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (EB-Role _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (EB-Role _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {EB-Role-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {EB-Role-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {EB-Role-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {V-Role-Action} {s} {SLOT} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (V-Role x y z)
  ... | no ¬p | _ | _ = no λ where (V-Role p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (V-Role _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (V-Role _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {V-Role-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {V-Role-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {V-Role-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {No-IB-Role-Action} {s} {SLOT} .dec
    with dec | dec
  ... | yes p | yes q = yes (No-IB-Role p q)
  ... | no ¬p | _ = no λ where (No-IB-Role p _) → ⊥-elim (¬p p)
  ... | _ | no ¬q = no λ where (No-IB-Role _ q) → ⊥-elim (¬q q)
  Dec-ValidAction {No-IB-Role-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {No-IB-Role-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {No-IB-Role-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {No-EB-Role-Action} {s} {SLOT} .dec
    with dec | dec
  ... | yes p | yes q = yes (No-EB-Role p q)
  ... | no ¬p | _ = no λ where (No-EB-Role p _) → ⊥-elim (¬p p)
  ... | _ | no ¬q = no λ where (No-EB-Role _ q) → ⊥-elim (¬q q)
  Dec-ValidAction {No-EB-Role-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {No-EB-Role-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {No-EB-Role-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {No-V-Role-Action} {s} {SLOT} .dec
    with dec | dec
  ... | yes p | yes q = yes (No-V-Role p q)
  ... | no ¬p | _ = no λ where (No-V-Role p _) → ⊥-elim (¬p p)
  ... | _ | no ¬q = no λ where (No-V-Role _ q) → ⊥-elim (¬q q)
  Dec-ValidAction {No-V-Role-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {No-V-Role-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {No-V-Role-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {Slot-Action} {s} {SLOT} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (Slot x y z)
  ... | no ¬p | _ | _ = no λ where (Slot p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (Slot _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (Slot _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {Slot-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {Slot-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {Slot-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {Ftch-Action} {s} {FTCH-LDG} .dec = yes Ftch
  Dec-ValidAction {Ftch-Action} {s} {SLOT} .dec = no λ ()
  Dec-ValidAction {Ftch-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {Ftch-Action} {s} {SUBMIT _} .dec = no λ ()
{-
  Dec-ValidAction {Base₁-Action} {s} {SUBMIT (inj₁ ebs)} .dec = no λ ()
  Dec-ValidAction {Base₁-Action} {s} {SUBMIT (inj₂ txs)} .dec = yes (Base₁ {s} {txs})
  Dec-ValidAction {Base₁-Action} {s} {SLOT} .dec = no λ ()
  Dec-ValidAction {Base₁-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {Base₁-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {Base₂a-Action} {s} {SLOT} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (Base₂a x y z)
  ... | no ¬p | _ | _ = no λ where (Base₂a p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (Base₂a _ p _) → ⊥-elim (¬p {!!}) -- (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (Base₂a _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {Base₂a-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {Base₂a-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {Base₂a-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {Base₂b-Action} {s} {SLOT} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (Base₂b x y z)
  ... | no ¬p | _ | _ = no λ where (Base₂b p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (Base₂b _ p _) → ⊥-elim (¬p {!!}) -- (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (Base₂b _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {Base₂b-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {Base₂b-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {Base₂b-Action} {s} {INIT _} .dec = no λ ()
-}

mutual
  data ValidTrace : Actions → Type where
    [] :
      ─────────────
      ValidTrace []

    _/_∷_⊣_ : ∀ α i {αs} →
      ∀ (tr : ValidTrace αs) →
      ∙ ValidAction α (proj₁ ⟦ tr ⟧∗) i
        ───────────────────
        ValidTrace ((α , i) ∷ αs)

  ⟦_⟧∗ : ∀ {αs : Actions} → ValidTrace αs → LeiosState × LeiosOutput
  ⟦_⟧∗ [] = initLeiosState tt sd tt , EMPTY
  ⟦_⟧∗ (_ / _ ∷ _ ⊣ vα) = ⟦ vα ⟧

Irr-ValidAction : Irrelevant (ValidAction α s i)
Irr-ValidAction (IB-Role x x₁ x₂) (IB-Role x₃ x₄ x₅) = refl
Irr-ValidAction (EB-Role x x₁ x₂) (EB-Role x₃ x₄ x₅) = refl
Irr-ValidAction (V-Role x x₁ x₂) (V-Role x₃ x₄ x₅)   = refl
Irr-ValidAction (No-IB-Role x x₁) (No-IB-Role x₂ x₃) = refl
Irr-ValidAction (No-EB-Role x x₁) (No-EB-Role x₂ x₃) = refl
Irr-ValidAction (No-V-Role _ _) (No-V-Role _ _)     = refl
Irr-ValidAction (Slot x x₁ x₂) (Slot x₃ x₄ x₅) = refl
Irr-ValidAction Ftch Ftch = refl
-- Irr-ValidAction Base₁ Base₁ = refl
-- Irr-ValidAction (Base₂a x x₁ x₂) (Base₂a x₃ x₄ x₅) = {!refl!}
-- Irr-ValidAction (Base₂b x x₁ x₂) (Base₂b x₃ x₄ x₅) = refl

Irr-ValidTrace : ∀ {αs} → Irrelevant (ValidTrace αs)
Irr-ValidTrace [] [] = refl
Irr-ValidTrace (α / i ∷ vαs ⊣ vα) (.α / .i ∷ vαs′ ⊣ vα′)
  rewrite Irr-ValidTrace vαs vαs′ | Irr-ValidAction vα vα′
  = refl

instance
  Dec-ValidTrace : ValidTrace ⁇¹
  Dec-ValidTrace {tr} .dec with tr
  ... | [] = yes []
  ... | (α , i) ∷ αs
    with ¿ ValidTrace αs ¿
  ... | no ¬vαs = no λ where (_ / _ ∷ vαs ⊣ _) → ¬vαs vαs
  ... | yes vαs
    with ¿ ValidAction α (proj₁ ⟦ vαs ⟧∗) i ¿
  ... | no ¬vα = no λ where
    (_ / _ ∷ tr ⊣ vα) → ¬vα
                  $ subst (λ x → ValidAction α x i) (cong (proj₁ ∘ ⟦_⟧∗) $ Irr-ValidTrace tr vαs) vα
  ... | yes vα = yes $ _ / _ ∷ vαs ⊣ vα

{-
getLabel : just s -⟦ i / o ⟧⇀ s′ → Action
getLabel (Slot _ _ _) = Slot-Action
getLabel Ftch = Ftch-Action
getLabel Base₁ = Base₁-Action
getLabel (Base₂a _ _ _) = Base₂a-Action
getLabel (Base₂b _ _ _) = Base₂b-Action
getLabel (Roles (IB-Role _ _ _)) = IB-Role-Action
getLabel (Roles (EB-Role _ _ _)) = EB-Role-Action
getLabel (Roles (V-Role _ _ _)) = V-Role-Action
getLabel (Roles (No-IB-Role _ _)) = No-IB-Role-Action
getLabel (Roles (No-EB-Role _ _)) = No-EB-Role-Action
getLabel (Roles (No-V-Role _ _)) = No-V-Role-Action
-}

ValidAction-sound : (va : ValidAction α s i) → let (s′ , o) = ⟦ va ⟧ in just s -⟦ i / o ⟧⇀ s′
ValidAction-sound (Slot {s} x x₁ x₂) = Slot {s} {rbs = []} (recompute dec x) (recompute dec x₁) (recompute dec x₂)
ValidAction-sound Ftch = Ftch
-- ValidAction-sound (Base₁ {s} {txs}) = Base₁ {s} {txs}
-- ValidAction-sound (Base₂a {s} x x₁ x₂) = Base₂a {s} (recompute dec x) (recompute dec x₁) (recompute dec x₂)
-- ValidAction-sound (Base₂b {s} x x₁ x₂) = Base₂b {s} (recompute dec x) (recompute dec x₁) (recompute dec x₂)
ValidAction-sound (IB-Role {s} x x₁ x₂) = Roles (IB-Role {s} (recompute dec x) (recompute dec x₁) (recompute dec x₂))
ValidAction-sound (EB-Role {s} x x₁ x₂) = Roles (EB-Role {s} (recompute dec x) (recompute dec x₁) (recompute dec x₂))
ValidAction-sound (V-Role {s} x x₁ x₂) = Roles (V-Role {s} (recompute dec x) (recompute dec x₁) (recompute dec x₂))
ValidAction-sound (No-IB-Role {s} x x₁) = Roles (No-IB-Role {s} x x₁)
ValidAction-sound (No-EB-Role {s} x x₁) = Roles (No-EB-Role {s} x x₁)
ValidAction-sound (No-V-Role {s} x x₁)  = Roles (No-V-Role {s} x x₁)

{-
ValidAction-complete : (st : just s -⟦ i / o ⟧⇀ s′) → ValidAction (getLabel st) s i
ValidAction-complete {s} {s′} (Roles (IB-Role {s} {π} {ffds'} x x₁ x₂)) =
  let open LeiosState s renaming (FFDState to ffds)
      b = record { txs = ToPropose }
      h = mkIBHeader slot id tt sk-IB ToPropose
      pr = proj₂ (send-total {ffds} {ibHeader h} {just (ibBody b)})
  in IB-Role {s} x x₁ pr
ValidAction-complete {s} (Roles (EB-Role x x₁ x₂)) =
  let open LeiosState s renaming (FFDState to ffds)
      LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
      h = mkEB slot id tt sk-EB LI []
      pr = proj₂ (send-total {ffds} {ebHeader h} {nothing})
  in EB-Role {s} x x₁ pr
ValidAction-complete {s} (Roles (V-Role x x₁ x₂))  =
  let open LeiosState s renaming (FFDState to ffds)
      EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
      votes = map (vote sk-V ∘ hash) EBs'
      pr = proj₂ (send-total {ffds} {vHeader votes} {nothing})
  in V-Role {s} x x₁ pr
ValidAction-complete {s} (Roles (No-IB-Role x x₁)) = No-IB-Role {s} x x₁
ValidAction-complete {s} (Roles (No-EB-Role x x₁)) = No-EB-Role {s} x x₁
ValidAction-complete {s} (Roles (No-V-Role x x₁))  = No-V-Role {s} x x₁
ValidAction-complete {s} Ftch = Ftch {s}
-- ValidAction-complete {s} Base₁ = Base₁ {s}
-- ValidAction-complete {s} (Base₂a x x₁ x₂) = Base₂a {s} x x₁ x₂
-- ValidAction-complete {s} (Base₂b x x₁ x₂) = Base₂b {s} x x₁ x₂
ValidAction-complete {s} (Slot x x₁ x₂) = Slot {s} x x₁ {!!}
-}

open import Leios.Prelude hiding (id)
open import Leios.Config

-- TODO: SpecStructure as parameter
module Leios.Short.Trace.Verifier (params : Params) (let open Params params) where

open import Leios.Defaults params
  using (LeiosState; initLeiosState; isb; hpe; hhs; htx; SendIB; FFDBuffers; Dec-SimpleFFD)
  renaming (d-SpecStructure to traceSpecStructure) public

open import Leios.SpecStructure using (SpecStructure)
open SpecStructure traceSpecStructure hiding (Hashable-IBHeader; Hashable-EndorserBlock; isVoteCertified) public

open import Leios.Short traceSpecStructure hiding (LeiosState; initLeiosState) public
open import Prelude.Closures _↝_
open GenFFD

data FFDUpdate : Type where
  IB-Recv-Update : InputBlock → FFDUpdate
  EB-Recv-Update : EndorserBlock → FFDUpdate
  VT-Recv-Update : List Vote → FFDUpdate

data Action : Type where
  IB-Role-Action : ℕ → Action
  EB-Role-Action : ℕ → List IBRef → Action
  VT-Role-Action : ℕ → Action
  No-IB-Role-Action No-EB-Role-Action No-VT-Role-Action : Action
  Ftch-Action : Action
  Slot-Action : ℕ → Action
  Base₁-Action : Action
  Base₂a-Action : EndorserBlock → Action
  Base₂b-Action : Action

Actions = List (Action × LeiosInput)

private variable
  s s′ : LeiosState
  α : Action

data ValidUpdate : FFDUpdate → LeiosState → Type where

  IB-Recv : ∀ {ib} →
    ValidUpdate (IB-Recv-Update ib) s

  EB-Recv : ∀ {eb} →
    ValidUpdate (EB-Recv-Update eb) s

  VT-Recv : ∀ {vt} →
    ValidUpdate (VT-Recv-Update vt) s

data ValidAction : Action → LeiosState → LeiosInput → Type where

  IB-Role : let open LeiosState s renaming (FFDState to ffds)
                b = record { txs = ToPropose }
                h = mkIBHeader slot id tt sk-IB ToPropose
                ffds' = proj₁ (FFD.Send-total {ffds} {ibHeader h} {just (ibBody b)})
            in .(needsUpkeep IB-Role) →
               .(canProduceIB slot sk-IB (stake s) tt) →
               .(ffds FFD.-⟦ FFD.Send (ibHeader h) (just (ibBody b)) / FFD.SendRes ⟧⇀ ffds') →
               ValidAction (IB-Role-Action slot) s SLOT

  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
                h = mkEB slot id tt sk-EB LI []
                ffds' = proj₁ (FFD.Send-total {ffds} {ebHeader h} {nothing})
            in .(needsUpkeep EB-Role) →
               .(canProduceEB slot sk-EB (stake s) tt) →
               .(ffds FFD.-⟦ FFD.Send (ebHeader h) nothing / FFD.SendRes ⟧⇀ ffds') →
               ValidAction (EB-Role-Action slot LI) s SLOT

  VT-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
                votes = map (vote sk-VT ∘ hash) EBs'
                ffds' = proj₁ (FFD.Send-total {ffds} {vtHeader votes} {nothing})
            in .(needsUpkeep VT-Role) →
               .(canProduceV slot sk-VT (stake s)) →
               .(ffds FFD.-⟦ FFD.Send (vtHeader votes) nothing / FFD.SendRes ⟧⇀ ffds') →
               ValidAction (VT-Role-Action slot) s SLOT

  No-IB-Role : let open LeiosState s
               in needsUpkeep IB-Role →
                  (∀ π → ¬ canProduceIB slot sk-IB (stake s) π) →
                  ValidAction No-IB-Role-Action s SLOT

  No-EB-Role : let open LeiosState s
               in needsUpkeep EB-Role →
                  (∀ π → ¬ canProduceEB slot sk-EB (stake s) π) →
                  ValidAction No-EB-Role-Action s SLOT

  No-VT-Role : let open LeiosState s
               in needsUpkeep VT-Role →
                  (¬ canProduceV slot sk-VT (stake s)) →
                  ValidAction No-VT-Role-Action s SLOT

  Slot : let open LeiosState s renaming (FFDState to ffds; BaseState to bs)
             (res , (bs' , _))    = B.FTCH-total {bs}
             (msgs , (ffds' , _)) = FFD.Fetch-total {ffds}
         in .(allDone s) →
            .(bs B.-⟦ B.FTCH-LDG / B.BASE-LDG res ⟧⇀ bs') →
            .(ffds FFD.-⟦ FFD.Fetch / FFD.FetchRes msgs ⟧⇀ ffds') →
            ValidAction (Slot-Action slot) s SLOT

  Ftch : ValidAction Ftch-Action s FTCH-LDG

  Base₁ : ∀ {txs} → ValidAction Base₁-Action s (SUBMIT (inj₂ txs))

  Base₂a : ∀ {eb} → let open LeiosState s renaming (BaseState to bs)
           in .(needsUpkeep Base) →
              .(eb ∈ filter (λ eb → isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs) →
              .(bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ tt) →
              ValidAction (Base₂a-Action eb) s SLOT

  Base₂b : let open LeiosState s renaming (BaseState to bs)
           in .(needsUpkeep Base) →
              .([] ≡ filter (λ eb → isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs) →
              .(bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ tt) →
              ValidAction Base₂b-Action s SLOT

private variable
  i : LeiosInput
  o : LeiosOutput

⟦_⟧ : ValidAction α s i → LeiosState × LeiosOutput
⟦ IB-Role {s} _ _ _ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      b = record { txs = ToPropose }
      h = mkIBHeader slot id tt sk-IB ToPropose
      ffds' = proj₁ (FFD.Send-total {ffds} {ibHeader h} {just (ibBody b)})
  in addUpkeep record s { FFDState = ffds' } IB-Role , EMPTY
⟦ EB-Role {s} _ _ _ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
      h = mkEB slot id tt sk-EB LI []
      ffds' = proj₁ (FFD.Send-total {ffds} {ebHeader h} {nothing})
  in addUpkeep record s { FFDState = ffds' } EB-Role , EMPTY
⟦ VT-Role {s} _ _ _ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
      votes = map (vote sk-VT ∘ hash) EBs'
      ffds' = proj₁ (FFD.Send-total {ffds} {vtHeader votes} {nothing})
  in addUpkeep record s { FFDState = ffds' } VT-Role , EMPTY
⟦ No-IB-Role {s} _ _ ⟧ = addUpkeep s IB-Role , EMPTY
⟦ No-EB-Role {s} _ _ ⟧ = addUpkeep s EB-Role , EMPTY
⟦ No-VT-Role {s} _ _ ⟧ = addUpkeep s VT-Role , EMPTY
⟦ Slot {s} _ _ _ ⟧ =
  let open LeiosState s renaming (FFDState to ffds; BaseState to bs)
      (res , (bs' , _))    = B.FTCH-total {bs}
      (msgs , (ffds' , _)) = FFD.Fetch-total {ffds}
  in
  (record s
     { FFDState  = ffds'
     ; BaseState = bs'
     ; Ledger    = constructLedger res
     ; slot      = suc slot
     ; Upkeep    = ∅
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
ValidAction→Eq-IB (IB-Role _ _ _) = refl

ValidAction→Eq-EB : ∀ {s sl ibs} → ValidAction (EB-Role-Action sl ibs) s SLOT → sl ≡ slot s × ibs ≡ (map getIBRef $ filter (_∈ᴮ slice L (slot s) 3) (IBs s))
ValidAction→Eq-EB (EB-Role _ _ _) = refl , refl

ValidAction→Eq-VT : ∀ {s sl} → ValidAction (VT-Role-Action sl) s SLOT → sl ≡ slot s
ValidAction→Eq-VT (VT-Role _ _ _) = refl

instance
  Dec-ValidAction : ValidAction ⁇³
  Dec-ValidAction {IB-Role-Action sl} {s} {SLOT} .dec
    with sl ≟ slot s
  ... | no ¬p = no λ x → ⊥-elim (¬p (ValidAction→Eq-IB x))
  ... | yes p rewrite p
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (IB-Role x y z)
  ... | no ¬p | _ | _ = no λ where (IB-Role p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (IB-Role _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (IB-Role _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {IB-Role-Action _} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {IB-Role-Action _} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {IB-Role-Action _} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {EB-Role-Action sl ibs} {s} {SLOT} .dec
    with sl ≟ slot s | ibs ≟ (map getIBRef $ filter (_∈ᴮ slice L (slot s) 3) (IBs s))
  ... | no ¬p | _ = no λ x → ⊥-elim (¬p (proj₁ $ ValidAction→Eq-EB x))
  ... | _ | no ¬q = no λ x → ⊥-elim (¬q (proj₂ $ ValidAction→Eq-EB x))
  ... | yes p | yes q rewrite p rewrite q
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (EB-Role x y z)
  ... | no ¬p | _ | _ = no λ where (EB-Role p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (EB-Role _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (EB-Role _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {EB-Role-Action _ _} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {EB-Role-Action _ _} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {EB-Role-Action _ _} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {VT-Role-Action sl} {s} {SLOT} .dec
    with sl ≟ slot s
  ... | no ¬p = no λ x → ⊥-elim (¬p (ValidAction→Eq-VT x))
  ... | yes p rewrite p
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (VT-Role x y z)
  ... | no ¬p | _ | _ = no λ where (VT-Role p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (VT-Role _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (VT-Role _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {VT-Role-Action _} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {VT-Role-Action _} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {VT-Role-Action _} {s} {FTCH-LDG} .dec = no λ ()
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
  Dec-ValidAction {No-VT-Role-Action} {s} {SLOT} .dec
    with dec | dec
  ... | yes p | yes q = yes (No-VT-Role p q)
  ... | no ¬p | _ = no λ where (No-VT-Role p _) → ⊥-elim (¬p p)
  ... | _ | no ¬q = no λ where (No-VT-Role _ q) → ⊥-elim (¬q q)
  Dec-ValidAction {No-VT-Role-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {No-VT-Role-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {No-VT-Role-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {Slot-Action sl} {s} {SLOT} .dec
    with sl ≟ slot s
  ... | no ¬p = no λ x → ⊥-elim (¬p (ValidAction→Eq-Slot x))
  ... | yes p rewrite p
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (Slot x y z)
  ... | no ¬p | _ | _ = no λ where (Slot p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (Slot _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (Slot _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {Slot-Action _} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {Slot-Action _} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {Slot-Action _} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {Ftch-Action} {s} {FTCH-LDG} .dec = yes Ftch
  Dec-ValidAction {Ftch-Action} {s} {SLOT} .dec = no λ ()
  Dec-ValidAction {Ftch-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {Ftch-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {Base₁-Action} {s} {SUBMIT (inj₁ ebs)} .dec = no λ ()
  Dec-ValidAction {Base₁-Action} {s} {SUBMIT (inj₂ txs)} .dec = yes (Base₁ {s} {txs})
  Dec-ValidAction {Base₁-Action} {s} {SLOT} .dec = no λ ()
  Dec-ValidAction {Base₁-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {Base₁-Action} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {Base₂a-Action eb} {s} {SLOT} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (Base₂a x y z)
  ... | no ¬p | _ | _ = no λ where (Base₂a p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (Base₂a {s} {eb} _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (Base₂a _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {Base₂a-Action _} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {Base₂a-Action _} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {Base₂a-Action _} {s} {INIT _} .dec = no λ ()
  Dec-ValidAction {Base₂b-Action} {s} {SLOT} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (Base₂b x y z)
  ... | no ¬p | _ | _ = no λ where (Base₂b p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (Base₂b _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (Base₂b _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {Base₂b-Action} {s} {SUBMIT _} .dec = no λ ()
  Dec-ValidAction {Base₂b-Action} {s} {FTCH-LDG} .dec = no λ ()
  Dec-ValidAction {Base₂b-Action} {s} {INIT _} .dec = no λ ()

instance
  Dec-ValidUpdate : ValidUpdate ⁇²
  Dec-ValidUpdate {IB-Recv-Update _} .dec = yes IB-Recv
  Dec-ValidUpdate {EB-Recv-Update _} .dec = yes EB-Recv
  Dec-ValidUpdate {VT-Recv-Update _} .dec = yes VT-Recv

mutual
  data ValidTrace : List ((Action × LeiosInput) ⊎ FFDUpdate) → Type where
    [] :
      ─────────────
      ValidTrace []

    _/_∷_⊣_ : ∀ α i {αs} →
      ∀ (tr : ValidTrace αs) →
      ∙ ValidAction α (proj₁ ⟦ tr ⟧∗) i
        ───────────────────
        ValidTrace (inj₁ (α , i) ∷ αs)

    _↥_ : ∀ {f αs} →
      ∀ (tr : ValidTrace αs) →
        (vu : ValidUpdate f (proj₁ ⟦ tr ⟧∗)) →
        ───────────────────
        ValidTrace (inj₂ f ∷ αs)


  ⟦_⟧∗ : ∀ {αs : List ((Action × LeiosInput) ⊎ FFDUpdate)} → ValidTrace αs → LeiosState × LeiosOutput
  ⟦ [] ⟧∗ = initLeiosState tt stakeDistribution tt pks , EMPTY
    where pks = L.zip (completeFinL numberOfParties) (L.replicate numberOfParties tt)
  ⟦ _ / _ ∷ _ ⊣ vα ⟧∗ = ⟦ vα ⟧
  ⟦ _↥_ {IB-Recv-Update ib} tr vu ⟧∗ =
    let (s , o) = ⟦ tr ⟧∗
    in record s { FFDState = record (FFDState s) { inIBs = ib ∷ inIBs (FFDState s)}} , o
  ⟦ _↥_ {EB-Recv-Update eb} tr vu ⟧∗ =
    let (s , o) = ⟦ tr ⟧∗
    in record s { FFDState = record (FFDState s) { inEBs = eb ∷ inEBs (FFDState s)}} , o
  ⟦ _↥_ {VT-Recv-Update vt} tr vu ⟧∗ =
    let (s , o) = ⟦ tr ⟧∗
    in record s { FFDState = record (FFDState s) { inVTs = vt ∷ inVTs (FFDState s)}} , o

Irr-ValidAction : Irrelevant (ValidAction α s i)
Irr-ValidAction (IB-Role _ _ _) (IB-Role _ _ _)   = refl
Irr-ValidAction (EB-Role _ _ _) (EB-Role _ _ _)   = refl
Irr-ValidAction (VT-Role _ _ _) (VT-Role _ _ _)   = refl
Irr-ValidAction (No-IB-Role _ _) (No-IB-Role _ _) = refl
Irr-ValidAction (No-EB-Role _ _) (No-EB-Role _ _) = refl
Irr-ValidAction (No-VT-Role _ _) (No-VT-Role _ _) = refl
Irr-ValidAction (Slot _ _ _) (Slot _ _ _)         = refl
Irr-ValidAction Ftch Ftch                         = refl
Irr-ValidAction Base₁ Base₁                       = refl
Irr-ValidAction (Base₂a _ _ _) (Base₂a _ _ _)     = refl
Irr-ValidAction (Base₂b _ _ _) (Base₂b _ _ _)     = refl

Irr-ValidUpdate : ∀ {f} → Irrelevant (ValidUpdate f s)
Irr-ValidUpdate IB-Recv IB-Recv = refl
Irr-ValidUpdate EB-Recv EB-Recv = refl
Irr-ValidUpdate VT-Recv VT-Recv = refl

Irr-ValidTrace : ∀ {αs} → Irrelevant (ValidTrace αs)
Irr-ValidTrace [] [] = refl
Irr-ValidTrace (α / i ∷ vαs ⊣ vα) (.α / .i ∷ vαs′ ⊣ vα′)
  rewrite Irr-ValidTrace vαs vαs′ | Irr-ValidAction vα vα′
  = refl
Irr-ValidTrace (vαs ↥ u) (vαs′ ↥ u′)
  rewrite Irr-ValidTrace vαs vαs′ | Irr-ValidUpdate u u′
  = refl

instance
  Dec-ValidTrace : ValidTrace ⁇¹
  Dec-ValidTrace {tr} .dec with tr
  ... | [] = yes []
  ... | inj₁ (α , i) ∷ αs
    with ¿ ValidTrace αs ¿
  ... | no ¬vαs = no λ where (_ / _ ∷ vαs ⊣ _) → ¬vαs vαs
  ... | yes vαs
    with ¿ ValidAction α (proj₁ ⟦ vαs ⟧∗) i ¿
  ... | no ¬vα = no λ where
    (_ / _ ∷ tr ⊣ vα) → ¬vα
                  $ subst (λ x → ValidAction α x i) (cong (proj₁ ∘ ⟦_⟧∗) $ Irr-ValidTrace tr vαs) vα
  ... | yes vα = yes $ _ / _ ∷ vαs ⊣ vα
  Dec-ValidTrace {tr} .dec | inj₂ u ∷ αs
    with ¿ ValidTrace αs ¿
  ... | no ¬vαs = no λ where (vαs ↥ _) → ¬vαs vαs
  ... | yes vαs
    with ¿ ValidUpdate u (proj₁ ⟦ vαs ⟧∗) ¿
  ... | yes vu = yes (vαs ↥ vu)
  ... | no ¬vu = no λ where
    (tr ↥ vu) → ¬vu $ subst (λ x → ValidUpdate u x) (cong (proj₁ ∘ ⟦_⟧∗) $ Irr-ValidTrace tr vαs) vu

data _⇑_ : LeiosState → LeiosState → Type where

  UpdateIB : ∀ {s ib} → let open LeiosState s renaming (FFDState to ffds) in
    s ⇑ record s { FFDState = record ffds { inIBs = ib ∷ inIBs ffds } }

  UpdateEB : ∀ {s eb} → let open LeiosState s renaming (FFDState to ffds) in
    s ⇑ record s { FFDState = record ffds { inEBs = eb ∷ inEBs ffds } }

  UpdateVT : ∀ {s vt} → let open LeiosState s renaming (FFDState to ffds) in
    s ⇑ record s { FFDState = record ffds { inVTs = vt ∷ inVTs ffds } }

data LocalStep : LeiosState → LeiosState → Type where

  StateStep : ∀ {s i o s′} →
    ∙ just s -⟦ i / o ⟧⇀ s′
      ───────────────────
      LocalStep s s′

  UpdateState : ∀ {s s′} →
    ∙ s ⇑ s′
      ───────────────────
      LocalStep s s′

  -- TODO: add base layer update

getLabel : just s -⟦ i / o ⟧⇀ s′ → Action
getLabel (Slot {s} _ _ _)            = Slot-Action (slot s)
getLabel Ftch                        = Ftch-Action
getLabel Base₁                       = Base₁-Action
getLabel (Base₂a {s} {eb} _ _ _)     = Base₂a-Action eb
getLabel (Base₂b _ _ _)              = Base₂b-Action
getLabel (Roles (IB-Role {s} _ _ _)) = IB-Role-Action (slot s)
getLabel (Roles (EB-Role {s} _ _ _)) = EB-Role-Action (slot s) (map getIBRef $ filter (_∈ᴮ slice L (slot s) 3) (IBs s))
getLabel (Roles (VT-Role {s} _ _ _)) = VT-Role-Action (slot s)
getLabel (Roles (No-IB-Role _ _))    = No-IB-Role-Action
getLabel (Roles (No-EB-Role _ _))    = No-EB-Role-Action
getLabel (Roles (No-VT-Role _ _))    = No-VT-Role-Action

ValidAction-sound : (vα : ValidAction α s i) → let (s′ , o) = ⟦ vα ⟧ in just s -⟦ i / o ⟧⇀ s′
ValidAction-sound (Slot x x₁ x₂)    = Slot {rbs = []} (recompute dec x) (recompute dec x₁) (recompute dec x₂)
ValidAction-sound Ftch              = Ftch
ValidAction-sound Base₁             = Base₁
ValidAction-sound (Base₂a x x₁ x₂)  = Base₂a (recompute dec x) (recompute dec x₁) (recompute dec x₂)
ValidAction-sound (Base₂b x x₁ x₂)  = Base₂b (recompute dec x) (recompute dec x₁) (recompute dec x₂)
ValidAction-sound (IB-Role x x₁ x₂) = Roles (IB-Role (recompute dec x) (recompute dec x₁) (recompute dec x₂))
ValidAction-sound (EB-Role x x₁ x₂) = Roles (EB-Role (recompute dec x) (recompute dec x₁) (recompute dec x₂))
ValidAction-sound (VT-Role x x₁ x₂) = Roles (VT-Role (recompute dec x) (recompute dec x₁) (recompute dec x₂))
ValidAction-sound (No-IB-Role x x₁) = Roles (No-IB-Role x x₁)
ValidAction-sound (No-EB-Role x x₁) = Roles (No-EB-Role x x₁)
ValidAction-sound (No-VT-Role x x₁) = Roles (No-VT-Role x x₁)

ValidAction-complete : (st : just s -⟦ i / o ⟧⇀ s′) → ValidAction (getLabel st) s i
ValidAction-complete {s} {s′} (Roles (IB-Role {s} {π} {ffds'} x x₁ _)) =
  let b  = record { txs = ToPropose s }
      h  = mkIBHeader (slot s) id tt sk-IB (ToPropose s)
      pr = proj₂ (FFD.Send-total {FFDState s} {ibHeader h} {just (ibBody b)})
  in IB-Role {s} x x₁ pr
ValidAction-complete {s} (Roles (EB-Role x x₁ _)) =
  let LI = map getIBRef $ filter (_∈ᴮ slice L (slot s) 3) (IBs s)
      h  = mkEB (slot s) id tt sk-EB LI []
      pr = proj₂ (FFD.Send-total {FFDState s} {ebHeader h} {nothing})
  in EB-Role {s} x x₁ pr
ValidAction-complete {s} (Roles (VT-Role x x₁ _))  =
  let EBs'  = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L (slot s) 1) (EBs s)
      votes = map (vote sk-VT ∘ hash) EBs'
      pr    = proj₂ (FFD.Send-total {FFDState s} {vtHeader votes} {nothing})
  in VT-Role {s} x x₁ pr
ValidAction-complete (Roles (No-IB-Role x x₁)) = No-IB-Role x x₁
ValidAction-complete (Roles (No-EB-Role x x₁)) = No-EB-Role x x₁
ValidAction-complete (Roles (No-VT-Role x x₁)) = No-VT-Role x x₁
ValidAction-complete Ftch                      = Ftch
ValidAction-complete Base₁                     = Base₁
ValidAction-complete (Base₂a x x₁ x₂)          = Base₂a x x₁ x₂
ValidAction-complete (Base₂b x x₁ x₂)          = Base₂b x x₁ x₂
ValidAction-complete {s} (Slot x x₁ _)         = Slot x x₁ (proj₂ (proj₂ (FFD.Fetch-total {FFDState s})))

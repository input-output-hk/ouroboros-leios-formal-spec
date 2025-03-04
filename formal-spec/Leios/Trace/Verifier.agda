open import Leios.Prelude hiding (id)
open import Leios.SpecStructure using (SpecStructure)

module Leios.Trace.Verifier (⋯ : SpecStructure 1) (let open SpecStructure ⋯) where

open import Leios.Short ⋯ renaming (isVoteCertified to isVoteCertified')
open B hiding (_-⟦_/_⟧⇀_)
open FFD hiding (_-⟦_/_⟧⇀_)

module _ {s : LeiosState} (let open LeiosState s renaming (FFDState to ffds; BaseState to bs)) where

  IB-Role? : ∀ {π ffds'} →
           let b = GenFFD.ibBody (record { txs = ToPropose })
               h = GenFFD.ibHeader (mkIBHeader slot id π sk-IB ToPropose)
           in
           { _ : auto∶ needsUpkeep IB-Role }
           { _ : auto∶ canProduceIB slot sk-IB (stake s) π }
           { _ : auto∶ ffds FFD.-⟦ FFD.Send h (just b) / FFD.SendRes ⟧⇀ ffds' } →
           ─────────────────────────────────────────────────────────────────────────
           s ↝ addUpkeep record s { FFDState = ffds' } IB-Role
  IB-Role? {_} {_} {p} {q} {r} = IB-Role (toWitness p) (toWitness q) (toWitness r)

  {-
  No-IB-Role? :
              { _ : auto∶ needsUpkeep IB-Role }
              { _ : auto∶ ∀ π → ¬ canProduceIB slot sk-IB (stake s) π } →
              ─────────────────────────────────────────────
              s ↝ addUpkeep s IB-Role
  No-IB-Role? {p} {q} = No-IB-Role (toWitness p) (toWitness q)
  -}

  EB-Role? : ∀ {π ffds'} →
           let LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
               h = mkEB slot id π sk-EB LI []
           in
           { _ : auto∶ needsUpkeep EB-Role }
           { _ : auto∶ canProduceEB slot sk-EB (stake s) π }
           { _ : auto∶ ffds FFD.-⟦ FFD.Send (GenFFD.ebHeader h) nothing / FFD.SendRes ⟧⇀ ffds' } →
           ─────────────────────────────────────────────────────────────────────────
           s ↝ addUpkeep record s { FFDState = ffds' } EB-Role
  EB-Role? {_} {_} {p} {q} {r} = EB-Role (toWitness p) (toWitness q) (toWitness r)

  {-
  No-EB-Role? :
              { _ : auto∶ needsUpkeep EB-Role }
              { _ : auto∶ ∀ π → ¬ canProduceEB slot sk-EB (stake s) π } →
              ─────────────────────────────────────────────
              s ↝ addUpkeep s EB-Role
  No-EB-Role? {_} {p} {q} = No-EB-Role (toWitness p) (toWitness q)
  -}

  V-Role? : ∀ {ffds'} →
          let EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
              votes = map (vote sk-V ∘ hash) EBs'
          in
          { _ : auto∶ needsUpkeep V-Role }
          { _ : auto∶ canProduceV slot sk-V (stake s) }
          { _ : auto∶ ffds FFD.-⟦ FFD.Send (GenFFD.vHeader votes) nothing / FFD.SendRes ⟧⇀ ffds' } →
          ─────────────────────────────────────────────────────────────────────────
          s ↝ addUpkeep record s { FFDState = ffds' } V-Role
  V-Role? {_} {p} {q} {r} = V-Role (toWitness p) (toWitness q) (toWitness r)

  No-V-Role? :
             { _ : auto∶ needsUpkeep V-Role }
             { _ : auto∶ ¬ canProduceV slot sk-V (stake s) } →
             ─────────────────────────────────────────────
             s ↝ addUpkeep s V-Role
  No-V-Role? {p} {q} = No-V-Role (toWitness p) (toWitness q)

  {-
  Init? : ∀ {ks pks ks' SD bs' V} →
        { _ : auto∶ ks K.-⟦ K.INIT pk-IB pk-EB pk-V / K.PUBKEYS pks ⟧⇀ ks' }
        { _ : initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs' } →
        ────────────────────────────────────────────────────────────────
        nothing -⟦ INIT V / EMPTY ⟧⇀ initLeiosState V SD bs'
  Init? = ?
  -}

  Base₂a? : ∀ {eb bs'} →
          { _ : auto∶ needsUpkeep Base }
          { _ : auto∶ eb ∈ filter (λ eb → isVoteCertified' s eb × eb ∈ᴮ slice L slot 2) EBs }
          { _ : auto∶ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ bs' } →
          ───────────────────────────────────────────────────────────────────────
          just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base
  Base₂a? {_} {_} {p} {q} {r} = Base₂a (toWitness p) (toWitness q) (toWitness r)

  Base₂b? : ∀ {bs'} →
          { _ : auto∶ needsUpkeep Base }
          { _ : auto∶ [] ≡ filter (λ eb → isVoteCertified' s eb × eb ∈ᴮ slice L slot 2) EBs }
          { _ : auto∶ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ bs' } →
          ───────────────────────────────────────────────────────────────────────
          just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base
  Base₂b? {_} {p} {q} {r} = Base₂b (toWitness p) (toWitness q) (toWitness r)

  Slot? : ∀ {rbs bs' msgs ffds'} →
         { _ : auto∶ Upkeep ≡ᵉ allUpkeep }
         { _ : auto∶ bs B.-⟦ B.FTCH-LDG / B.BASE-LDG rbs ⟧⇀ bs' }
         { _ : auto∶ ffds FFD.-⟦ FFD.Fetch / FFD.FetchRes msgs ⟧⇀ ffds' } →
         ───────────────────────────────────────────────────────────────────────
         just s -⟦ SLOT / EMPTY ⟧⇀ record s
             { FFDState  = ffds'
             ; BaseState = bs'
             ; Ledger    = constructLedger rbs
             ; slot      = suc slot
             ; Upkeep    = ∅
             } ↑ L.filter GenFFD.isValid? msgs
  Slot? {_} {_} {_} {_} {p} {q} {r} = Slot (toWitness p) (toWitness q) (toWitness r)

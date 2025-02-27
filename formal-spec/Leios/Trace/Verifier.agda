open import Leios.Prelude
open import Leios.Defaults 2 fzero
open import Leios.SpecStructure

module Leios.Trace.Verifier where

--open SpecStructure ⦃ st ⦄
open FFDAbstract

module FFD = FFDAbstract.Functionality d-FFDFunctionality
module B = BaseAbstract.Functionality d-BaseFunctionality

IB-Role? : ∀ {s π ffds' sk-IB} →
         let open LeiosState s renaming (FFDState to ffds)
             b = GenFFD.ibBody (record { txs = ToPropose })
             h = GenFFD.ibHeader (mkIBHeader slot fzero π sk-IB ToPropose)
         in
         { _ : auto∶ needsUpkeep IB-Role }
         { _ : auto∶ canProduceIB slot sk-IB (stake s) π }
         { _ : auto∶ ffds FFD.-⟦ Send h (just b) / SendRes ⟧⇀ ffds' } →
         ─────────────────────────────────────────────────────────────────────────
         s ↝ addUpkeep record s { FFDState = ffds' } IB-Role
IB-Role? {_} {_} {_} {_} {p} {q} {r} = IB-Role (toWitness p) (toWitness q) (toWitness r)

No-IB-Role? : ∀ {s sk-IB} → let open LeiosState s
            in
            { _ : auto∶ needsUpkeep IB-Role }
            { _ : auto∶ ∀ π → ¬ canProduceIB slot sk-IB (stake s) π } →
            ─────────────────────────────────────────────
            s ↝ addUpkeep s IB-Role
No-IB-Role? {_} {_} {p} {q} = No-IB-Role (toWitness p) (toWitness q)

EB-Role? : ∀ {s π ffds' sk-EB} →
         let open LeiosState s renaming (FFDState to ffds)
             LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
             h = mkEB slot fzero π sk-EB LI []
         in
         { _ : auto∶ needsUpkeep EB-Role }
         { _ : auto∶ canProduceEB slot sk-EB (stake s) π }
         { _ : auto∶ ffds FFD.-⟦ Send (GenFFD.ebHeader h) nothing / SendRes ⟧⇀ ffds' } →
         ─────────────────────────────────────────────────────────────────────────
         s ↝ addUpkeep record s { FFDState = ffds' } EB-Role
EB-Role? {_} {_} {_} {_} {p} {q} {r} = EB-Role (toWitness p) (toWitness q) (toWitness r)

No-EB-Role? : ∀ {s sk-IB} → let open LeiosState s
            in
            { _ : auto∶ needsUpkeep EB-Role }
            { _ : auto∶ ∀ π → ¬ canProduceEB slot sk-IB (stake s) π } →
            ─────────────────────────────────────────────
            s ↝ addUpkeep s EB-Role
No-EB-Role? {_} {_} {p} {q} = No-EB-Role (toWitness p) (toWitness q)

V-Role? : ∀ {s ffds' sk-V} →
        let open LeiosState s renaming (FFDState to ffds)
            EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
            votes = map (vote sk-V ∘ hash) EBs'
        in
        { _ : auto∶ needsUpkeep V-Role }
        { _ : auto∶ canProduceV slot sk-V (stake s) }
        { _ : auto∶ ffds FFD.-⟦ Send (GenFFD.vHeader votes) nothing / SendRes ⟧⇀ ffds' } →
        ─────────────────────────────────────────────────────────────────────────
        s ↝ addUpkeep record s { FFDState = ffds' } V-Role
V-Role? {_} {_} {_} {p} {q} {r} = V-Role (toWitness p) (toWitness q) (toWitness r)

{-
Init? : ∀ {ks pks ks' SD bs' V} →
      { _ : auto∶ ks K.-⟦ K.INIT pk-IB pk-EB pk-V / K.PUBKEYS pks ⟧⇀ ks' }
      { _ : initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs' } →
      ────────────────────────────────────────────────────────────────
      nothing -⟦ INIT V / EMPTY ⟧⇀ initLeiosState V SD bs'
Init? = ?
-}

Base₂a? : ∀ {s eb bs'} →
        let open LeiosState s renaming (BaseState to bs)
        in
        { _ : auto∶ needsUpkeep Base }
        { _ : auto∶ eb ∈ filter (λ eb → isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs }
        { _ : auto∶ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ bs' } →
        ───────────────────────────────────────────────────────────────────────
        just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base
Base₂a? {_} {_} {_} {p} {q} {r} = Base₂a (toWitness p) (toWitness q) {!!} -- (toWitness r)

Base₂b? : ∀ {s bs'} →
        let open LeiosState s renaming (BaseState to bs)
        in
        { _ : auto∶ needsUpkeep Base }
        { _ : auto∶ [] ≡ filter (λ eb → isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs }
        { _ : auto∶ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ bs' } →
        ───────────────────────────────────────────────────────────────────────
        just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base
Base₂b? {_} {_} {p} {q} {r} = Base₂b (toWitness p) (toWitness q) {!!} -- (toWitness r)

Slot? : ∀ {s rbs bs' msgs ffds'} →
       let open LeiosState s renaming (FFDState to ffds; BaseState to bs)
       in
       { _ : auto∶ Upkeep ≡ᵉ allUpkeep }
       { _ : auto∶ bs B.-⟦ B.FTCH-LDG / B.BASE-LDG rbs ⟧⇀ bs' }
       { _ : auto∶ ffds FFD.-⟦ FFDAbstract.Fetch / FFDAbstract.FetchRes msgs ⟧⇀ ffds' } →
       ───────────────────────────────────────────────────────────────────────
       just s -⟦ SLOT / EMPTY ⟧⇀ record s
           { FFDState  = ffds'
           ; BaseState = bs'
           ; Ledger    = constructLedger rbs
           ; slot      = suc slot
           ; Upkeep    = ∅
           } ↑ L.filter GenFFD.isValid? msgs
Slot? {_} {_} {_} {_} {_} {p} {q} {r} = {!!} -- Slot (toWitness p) (toWitness q) (toWitness r)

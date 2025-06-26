## Short-Pipeline Leios

<!--
```agda
{-# OPTIONS --safe #-}
open import Leios.Prelude hiding (id)
open import Leios.FFD
open import Leios.SpecStructure

open import Tactic.Defaults
open import Tactic.Derive.DecEq

module Leios.Short (⋯ : SpecStructure 1)
  (let open SpecStructure ⋯ renaming (isVoteCertified to isVoteCertified')) where
```
-->

This document is a specification of Short-Pipeline Leios, usually
abbreviated as Short Leios. On a high level, the pipeline looks like this:

1. If elected, propose IB
2. Wait
3. Wait
4. If elected, propose EB
5. If elected, vote
   If elected, propose RB

### Upkeep

A node that never produces a block even though it could is not
supposed to be an honest node, and we prevent that by tracking whether
a node has checked if it can make a block in a particular slot.
`LeiosState` contains a set of `SlotUpkeep` and we ensure that this
set contains all elements before we can advance to the next slot,
resetting this field to the empty set.

```agda
data SlotUpkeep : Type where
  Base IB-Role EB-Role : SlotUpkeep

unquoteDecl DecEq-SlotUpkeep = derive-DecEq ((quote SlotUpkeep , DecEq-SlotUpkeep) ∷ [])
```
<!--
```agda
data StageUpkeep : Type where
  VT-Role : StageUpkeep

unquoteDecl DecEq-StageUpkeep = derive-DecEq ((quote StageUpkeep , DecEq-StageUpkeep) ∷ [])
```
```agda
open import Leios.Protocol (⋯) SlotUpkeep StageUpkeep public

open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open FFD hiding (_-⟦_/_⟧⇀_)
open GenFFD
```
```agda
isVoteCertified : LeiosState → EndorserBlock → Type
isVoteCertified s eb = isVoteCertified' (LeiosState.votingState s) (0F , eb)
```
```agda
private variable s s'   : LeiosState
                 ffds'  : FFD.State
                 π      : VrfPf
                 bs'    : B.State
                 ks ks' : K.State
                 msgs   : List (FFDAbstract.Header ffdAbstract ⊎ FFDAbstract.Body ffdAbstract)
                 eb     : EndorserBlock
                 ebs    : List EndorserBlock
                 rbs    : List RankingBlock
                 txs    : List Tx
                 V      : VTy
                 SD     : StakeDistr
                 pks    : List PubKey
```
-->
### Block/Vote production

IBs from the last 3 pipelines are directly included in the EB, when the late IB inclusion
flag is set
```agda
IBSelection : LeiosState → Bool → InputBlock → Type
IBSelection s false = _∈ᴮ slice L (LeiosState.slot s) 3
IBSelection s true  = _∈ᴮ slices L (LeiosState.slot s) 3 6

IBSelection? : (s : LeiosState) → (b : Bool) → (ib : InputBlock) → Dec (IBSelection s b ib)
IBSelection? s false ib = slotNumber ib ∈? slice L (LeiosState.slot s) 3
IBSelection? s true ib  = slotNumber ib ∈? slices L (LeiosState.slot s) 3 6
```
We now define the rules for block production given by the relation `_↝_`. These are split in two:

1. Positive rules, when we do need to create a block.
2. Negative rules, when we cannot create a block.

The purpose of the negative rules is to properly adjust the upkeep if
we cannot make a block.

Note that `_↝_`, starting with an empty upkeep can always make exactly
three steps corresponding to the three types of Leios specific blocks.

```agda
data _↝_ : LeiosState → LeiosState → Type where
```
#### Positive rules
```agda
  IB-Role : let open LeiosState s renaming (FFDState to ffds)
                b = ibBody (record { txs = ToPropose })
                h = ibHeader (mkIBHeader slot id π sk-IB ToPropose)
          in
          ∙ canProduceIB slot sk-IB (stake s) π
          ∙ ffds FFD.-⟦ Send h (just b) / SendRes ⟧⇀ ffds'
          ─────────────────────────────────────────────────────────────────────────
          s ↝ addUpkeep record s { FFDState = ffds' } IB-Role
```
When η = 0 there is no indirect ledger inclusion; in case η > 0 earlier EBs might
be referenced (Full-Short Leios).
```agda
  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                ibs = L.filter (IBSelection? s Late-IB-Inclusion) IBs
                LI  = map getIBRef ibs
                LE  = map getEBRef ebs
                h   = mkEB slot id π sk-EB LI LE
                P   = λ x → isVoteCertified s x
                         × x ∈ˡ EBs
                         × x ∈ᴮ slices L slot 2 (3 * η / L)
                slots = map slotNumber
          in
          ∙ needsUpkeep EB-Role
          ∙ canProduceEB slot sk-EB (stake s) π
          ∙ All.All P ebs
          ∙ Unique (slots ebs) × fromList (slots ebs) ≡ᵉ fromList (slots (filter P EBs))
          ∙ ffds FFD.-⟦ Send (ebHeader h) nothing / SendRes ⟧⇀ ffds'
          ─────────────────────────────────────────────────────────────────────────
          s ↝ addUpkeep record s { FFDState = ffds' } EB-Role
```
```agda
  VT-Role : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
                votes = map (vote sk-VT ∘ hash) EBs'
          in
          ∙ needsUpkeep-Stage VT-Role
          ∙ canProduceV slot sk-VT (stake s)
          ∙ ffds FFD.-⟦ Send (vtHeader votes) nothing / SendRes ⟧⇀ ffds'
          ─────────────────────────────────────────────────────────────────────────
          s ↝ addUpkeep-Stage record s { FFDState = ffds' } VT-Role
```
#### Negative rules
```agda
  No-IB-Role : let open LeiosState s in
             ∙ needsUpkeep IB-Role
             ∙ (∀ π → ¬ canProduceIB slot sk-IB (stake s) π)
             ─────────────────────────────────────────────
             s ↝ addUpkeep s IB-Role
```
```agda
  No-EB-Role : let open LeiosState s in
             ∙ needsUpkeep EB-Role
             ∙ (∀ π → ¬ canProduceEB slot sk-EB (stake s) π)
             ─────────────────────────────────────────────
             s ↝ addUpkeep s EB-Role
```
```agda
  No-VT-Role : let open LeiosState s in
             ∙ needsUpkeep-Stage VT-Role
             ∙ ¬ canProduceV slot sk-VT (stake s)
             ─────────────────────────────────────────────
             s ↝ addUpkeep-Stage s VT-Role
```
### Uniform short-pipeline
```agda
stage : ℕ → ⦃ _ : NonZero L ⦄ → ℕ
stage s = s / L

beginningOfStage : ℕ → Type
beginningOfStage s = stage s * L ≡ s

endOfStage : ℕ → Type
endOfStage s = suc (stage s) ≡ stage (suc s)
```
Predicate needed for slot transition. Special care needs to be taken when starting from
genesis.
```agda
allDone : LeiosState → Type
allDone record { slot = s ; Upkeep = u ; Upkeep-Stage = v } =
  -- bootstrapping
    (stage s < 3 ×                        u ≡ᵉ fromList (IB-Role           ∷ Base ∷ []))
  ⊎ (stage s ≡ 3 ×   beginningOfStage s × u ≡ᵉ fromList (IB-Role ∷ EB-Role ∷ Base ∷ []))
  ⊎ (stage s ≡ 3 × ¬ beginningOfStage s × u ≡ᵉ fromList (IB-Role           ∷ Base ∷ []))
  -- done
  ⊎ (stage s > 3 ×   beginningOfStage s × u ≡ᵉ fromList (IB-Role ∷ EB-Role ∷ Base ∷ []))
  ⊎ (stage s > 3 × ¬ beginningOfStage s × u ≡ᵉ fromList (IB-Role           ∷ Base ∷ []) ×
       (((  endOfStage s × v ≡ᵉ fromList (VT-Role ∷ []))
       ⊎ (¬ endOfStage s))))
```
### (Full-)Short Leios transitions
The relation describing the transition given input and state
```agda
data _-⟦_/_⟧⇀_ : Maybe LeiosState → LeiosInput → LeiosOutput → LeiosState → Type where
```
#### Initialization
```agda
  Init :
       ∙ ks K.-⟦ K.INIT pk-IB pk-EB pk-VT / K.PUBKEYS pks ⟧⇀ ks'
       ∙ initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs'
       ────────────────────────────────────────────────────────────────
       nothing -⟦ INIT V / EMPTY ⟧⇀ initLeiosState V SD bs' pks
```
#### Network and Ledger
```agda
  Slot : let open LeiosState s renaming (FFDState to ffds; BaseState to bs) in
       ∙ allDone s
       ∙ bs B.-⟦ B.FTCH-LDG / B.BASE-LDG rbs ⟧⇀ bs'
       ∙ ffds FFD.-⟦ Fetch / FetchRes msgs ⟧⇀ ffds'
       ───────────────────────────────────────────────────────────────────────
       just s -⟦ SLOT / EMPTY ⟧⇀ record s
           { FFDState     = ffds'
           ; BaseState    = bs'
           ; Ledger       = constructLedger rbs
           ; slot         = suc slot
           ; Upkeep       = ∅
           ; Upkeep-Stage = ifᵈ (endOfStage slot) then ∅ else Upkeep-Stage
           } ↑ L.filter (isValid? s) msgs
```
```agda
  Ftch :
       ────────────────────────────────────────────────────────
       just s -⟦ FTCH-LDG / FTCH-LDG (LeiosState.Ledger s) ⟧⇀ s
```
#### Base chain

Note: Submitted data to the base chain is only taken into account
      if the party submitting is the block producer on the base chain
      for the given slot
```agda
  Base₁   :
          ───────────────────────────────────────────────────────────────────
          just s -⟦ SUBMIT (inj₂ txs) / EMPTY ⟧⇀ record s { ToPropose = txs }
```
```agda
  Base₂a  : let open LeiosState s renaming (BaseState to bs) in
          ∙ needsUpkeep Base
          ∙ eb ∈ filter (λ x → isVoteCertified s x × x ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base

  Base₂b  : let open LeiosState s renaming (BaseState to bs) in
          ∙ needsUpkeep Base
          ∙ [] ≡ filter (λ x → isVoteCertified s x × x ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base
```
#### Protocol rules
```agda
  Roles :
        ∙ s ↝ s'
        ─────────────────────────────
        just s -⟦ SLOT / EMPTY ⟧⇀ s'
```

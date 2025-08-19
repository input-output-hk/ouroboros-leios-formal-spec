## Linear Leios

<!--
```agda
{-# OPTIONS --safe #-}
open import Leios.Prelude hiding (id; _⊗_)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open import CategoricalCrypto hiding (id; _∘_)

module Leios.Linear (⋯ : SpecStructure 1)
  (let open SpecStructure ⋯ renaming (isVoteCertified to isVoteCertified'))
  (params : Params)
  (Lvote Ldiff : ℕ) where
```
-->

This document is a specification of Linear Leios. It removes
concurrency at the transaction level by producing one (large) EB for
every Praos block.

### Upkeep

A node that never produces a block even though it could is not
supposed to be an honest node, and we prevent that by tracking whether
a node has checked if it can make a block in a particular slot.
`LeiosState` contains a set of `SlotUpkeep` and we ensure that this
set contains all elements before we can advance to the next slot,
resetting this field to the empty set.

```agda
data SlotUpkeep : Type where
  Base EB-Role VT-Role : SlotUpkeep

unquoteDecl DecEq-SlotUpkeep = derive-DecEq ((quote SlotUpkeep , DecEq-SlotUpkeep) ∷ [])
```
<!--
```agda
open import Leios.Protocol (⋯) SlotUpkeep ⊥ public

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
                 i      : FFDAbstract.Input ffdAbstract
                 eb     : EndorserBlock
                 ebs    : List EndorserBlock
                 rbs    : List RankingBlock
                 txs    : List Tx
                 V      : VTy
                 SD     : StakeDistr
                 pks    : List PubKey
                 cert   : EBCert
```
-->
### Block/Vote production

We now define the rules for block production given by the relation `_↝_`. These are split in two:

1. Positive rules, when we do need to create a block.
2. Negative rules, when we cannot create a block.

The purpose of the negative rules is to properly adjust the upkeep if
we cannot make a block.

Note that `_↝_`, starting with an empty upkeep can always make exactly
three steps corresponding to the three types of Leios specific blocks.

```agda
toProposeEB : LeiosState → VrfPf → Maybe EndorserBlock
toProposeEB s π = let open LeiosState s in case ToPropose of λ where
  [] → nothing
  _ → just $ mkEB slot id π sk-IB ToPropose [] []

getCurrentEBHash : LeiosState → Maybe EBRef
getCurrentEBHash s = let open LeiosState s in
  RankingBlock.announcedEB currentRB

data _↝_ : LeiosState → LeiosState × Maybe (FFDAbstract.Input ffdAbstract) → Type where
```
#### Positive rules

In this specification, we don't want to peek behind the base chain
abstraction. This means that we assume instead that the `canProduceEB`
predicate is satisfied if and only if we can make an RB. In that case,
we send out an EB with the transactions currently stored in the
mempool.

```agda
  EB-Role : let open LeiosState s in
          ∙ toProposeEB s π ≡ just eb
          ∙ canProduceEB slot sk-EB (stake s) π
          ─────────────────────────────────────────────────────────────────────────
          s ↝ (addUpkeep s EB-Role , just (Send (ebHeader eb) nothing))
```
```agda
  VT-Role : ∀ {ebHash slot'}
          → let open LeiosState s
          in
          ∙ getCurrentEBHash s ≡ just ebHash
          ∙ find (λ (s , eb) → hash eb ≟ ebHash) EBs' ≡ just (slot' , eb)
--          ∙ isValid s (inj₁ (ebHeader eb))
          ∙ slot' ≤ slotNumber eb + Lvote
          ∙ needsUpkeep VT-Role
          ∙ canProduceV slot sk-VT (stake s)
          ─────────────────────────────────────────────────────────────────────────
          s ↝ (addUpkeep s VT-Role , just (Send (vtHeader [ vote sk-VT (hash eb) ]) nothing))
```
Predicate needed for slot transition.
```agda
allDone : LeiosState → Type
allDone record { Upkeep = u } = u ≡ᵉ fromList (EB-Role ∷ Base ∷ [])
```
### Linear Leios transitions
The relation describing the transition given input and state
#### Initialization
```agda
open Types params

data _⊢_ : VTy → LeiosState → Type where
  Init :
       ∙ ks K.-⟦ K.INIT pk-IB pk-EB pk-VT / K.PUBKEYS pks ⟧⇀ ks'
       ∙ initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs' -- TODO: replace this line
       ────────────────────────────────────────────────────────────────
       V ⊢ initLeiosState V SD pks
```
```agda
data _-⟦_/_⟧⇀_ : MachineType (FFD ⊗ BaseC) (IO ⊗ Adv) LeiosState where
```
#### Network and Ledger
```agda
  Slot₁ : let open LeiosState s in
        ∙ allDone s
        ────────────────────────────────────────────────────────────────────────────────────
        s -⟦ honestOutputI (rcvˡ (-, FFD-OUT msgs)) / honestInputO' (sndʳ (-, FTCH-LDG)) ⟧⇀ record s
            { slot         = suc slot
            ; Upkeep       = ∅
            } ↑ L.filter (isValid? s) msgs

  Slot₂ : let open LeiosState s in
        ──────────────────────────────────────────────────────────────────────────────
        s -⟦ honestOutputI (rcvʳ (-, BASE-LDG rbs)) / nothing ⟧⇀ record s { RBs = rbs }
```
```agda
  Ftch : let open LeiosState s in
       ─────────────────────────────────────────────────────────────────────────────────────
       s -⟦ honestInputI (-, FetchLdgI) / honestOutputO' (-, FetchLdgO Ledger) ⟧⇀ s
```
#### Base chain

Note: Submitted data to the base chain is only taken into account
      if the party submitting is the block producer on the base chain
      for the given slot
```agda
  Base₁   :
          ──────────────────────────────────────────────────────────────────────────────
          s -⟦ honestInputI (-, SubmitTxs txs) / nothing ⟧⇀ record s { ToPropose = txs }
```
```agda
  Base₂   : let open LeiosState s
                currentCertEB = find (λ (eb , _) → ¿ just (hash eb) ≡ getCurrentEBHash s × slotNumber eb + Lvote + Ldiff ≤ slot ¿) (ebsWithCert fzero)
                rb = record
                       { txs = [] -- TODO: we don't have block sizes ATM, so for the moment we put all transactions here
                       ; announcedEB = hash <$> toProposeEB s π
                       ; ebCert = proj₂ <$> currentCertEB }
          in
          ∙ needsUpkeep Base
          ───────────────────────────────────────────────────────────────────────────────────
          s -⟦ honestOutputI (rcvˡ (-, SLOT)) / honestInputO' (sndʳ (-, SUBMIT rb)) ⟧⇀
            addUpkeep s Base
```
#### Protocol rules
```agda
  Roles₁ :
         ∙ s ↝ (s' , just i)
         ──────────────────────────────────────────────────────────────────────────────
         s -⟦ honestOutputI (rcvˡ (-, SLOT)) / honestInputO' (sndˡ (-, FFD-IN i)) ⟧⇀ s'

{-
  Roles₂ :
         ∙ s ↝ (s' , nothing)
         ───────────────────────────────────────────────────
         s -⟦ honestOutputI (rcvˡ (-, SLOT)) / nothing ⟧⇀ s'
-}

  Roles₃ : ∀ {x u} → let open LeiosState s in
         ∙ ¬ (s ↝ (s' , x))
         ∙ needsUpkeep u
         ∙ u ≢ Base
         ───────────────────────────────────────────────────
         s -⟦ honestOutputI (rcvˡ (-, SLOT)) / nothing ⟧⇀ addUpkeep s' u
```
<!--
```agda
ShortLeios : Machine (FFD ⊗ BaseC) (IO ⊗ Adv)
ShortLeios .Machine.State = LeiosState
ShortLeios .Machine.stepRel = _-⟦_/_⟧⇀_

open import GenPremises

unquoteDecl EB-Role-premises = genPremises EB-Role-premises (quote _↝_.EB-Role)
unquoteDecl VT-Role-premises = genPremises VT-Role-premises (quote _↝_.VT-Role)

unquoteDecl Slot₁-premises = genPremises Slot₁-premises (quote Slot₁)
unquoteDecl Slot₂-premises = genPremises Slot₂-premises (quote Slot₂)
unquoteDecl Base₁-premises = genPremises Base₁-premises (quote Base₁)
unquoteDecl Base₂-premises = genPremises Base₂-premises (quote Base₂)
```
--!>

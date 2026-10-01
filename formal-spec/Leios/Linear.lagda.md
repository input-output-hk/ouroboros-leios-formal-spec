## Linear Leios

<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Config
open import Leios.FFD
open import Leios.Prelude hiding (id; _⊗_)
open import Leios.SpecStructure

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open import CategoricalCrypto hiding (id; _∘_; eval)
open import CategoricalCrypto.Channel.Selection

open import Data.Maybe.Properties
import Data.Maybe.Relation.Unary.All as Maybe

open import Prelude.STS.GenPremises

module Leios.Linear (⋯ : SpecStructure)
  (let open SpecStructure ⋯)
  (params : Params)
  (let open Params params) where
```
-->

This document is a specification of Linear Leios.  It removes
concurrency at the transaction level by producing at most one (large) EB
for every Praos block.

### Upkeep

A node that never produces a block even though it could is not
supposed to be an honest node, and we prevent that by tracking whether
a node has checked if it can make a block in a particular slot.
`LeiosState` records the settled duties in `Upkeep`, and `Slot`
requires all of them before advancing the slot, resetting `Upkeep` to
`[]`.

`CertCheck` is settled once the node has decided whether its RB carries
a certificate: by `Base₁` when none is called for, or by `Base₂`, which
queries the voting functionality.  `Base` is settled only when the RB is
submitted, which after a query waits for the answer.
```agda
data SlotUpkeep : Type where
  Base CertCheck EB-Role VT-Role : SlotUpkeep
```
<!--
```agda
unquoteDecl DecEq-SlotUpkeep = derive-DecEq ((quote SlotUpkeep , DecEq-SlotUpkeep) ∷ [])

open import Leios.Protocol (⋯) SlotUpkeep ⊥ public
open import Leios.Voting.Channel Vote EBRef EBCert public
open FFD hiding (_-⟦_/_⟧⇀_)
open GenFFD

private variable s     : LeiosState
                 π     : VrfPf
                 msgs  : List (FFDAbstract.Header ffdAbstract ⊎ FFDAbstract.Body ffdAbstract)
                 eb    : EndorserBlock
                 rbs   : List RankingBlock
                 txs   : List Tx
                 c     : Maybe EBCert
                 r     : EBRef
```
-->

### Block/Vote production

A node settles each role once per slot, either by performing it or by
declining it.  `CanProposeEB` and `CanVote` below state when a role can
be performed.  The positive rules `EB-Role` and `VT-Role` require them,
the negative rules `No-EB-Role` and `No-VT-Role` require that they fail
for every choice of witness, and `VT-Defer` lets a node postpone a vote
it could cast.

```agda
toProposeEB : LeiosState → VrfPf → Maybe EndorserBlock
toProposeEB s π = let open LeiosState s in case proj₂ (splitTxs ToPropose) of λ where
  [] → nothing
  _ → just $ mkEB slot id π sk-EB ToPropose

getCurrentEBHash : LeiosState → Maybe EBRef
getCurrentEBHash s = let open LeiosState s in
  RankingBlock.announcedEB currentRB

isEquivocated : LeiosState → EndorserBlock → Type
isEquivocated s eb = Any (areEquivocated eb) (toSet (LeiosState.EBs s))
```
The EB whose certificate the node would embed in the RB: the EB announced by
the current chain tip, old enough for the votes on it to have diffused.
```agda
certRequest : LeiosState → Maybe EndorserBlock
certRequest s = let open LeiosState s in
  find (λ eb → ¿ just (hash eb) ≡ getCurrentEBHash s
             × slotNumber eb + 3 * Lhdr + Lvote + Ldiff ≤ slot ¿) EBs

mkRB : LeiosState → Maybe EBCert → RankingBlock
mkRB s mc = let open LeiosState s in record
  { announcedEB = proposedEB
  ; txsOrEbCert = maybe inj₂ (inj₁ (proj₁ (splitTxs ToPropose))) mc
  }
```
Certificates are keyed by the hash of the *announcing* ranking block, the
same hash `VT-Role` signs (CIP-0164, "Vote Structure"), so that a query can
be answered from the votes as cast.  `certRequest` still selects the EB, but
only to decide *whether* a certificate is called for; the reference asked
for is `hash currentRB`.  A positive answer must certify that reference
(`Maybe.All`, in `Cert₁`); a negative answer trivially matches any request.
```agda
rememberVote : LeiosState → EndorserBlock → LeiosState
rememberVote s@(record { VotedEBs = vebs }) eb = record s { VotedEBs = hash eb ∷ vebs }

rememberProposal : LeiosState → EndorserBlock → LeiosState
rememberProposal s eb = record s { proposedEB = just (hash eb) }
```
In this specification, we don't want to peek behind the base chain
abstraction.  We therefore assume that the `canProduceEB` predicate
holds if and only if we can make an RB.  In that case the node diffuses
an EB with the EB share of `splitTxs ToPropose`, if that share is
non-empty.
```agda
CanProposeEB : LeiosState → VrfPf → EndorserBlock → Type
CanProposeEB s π eb = let open LeiosState s in
  toProposeEB s π ≡ just eb × canProduceEB slot sk-EB (stake s) π
```
A node can vote on the EB announced by the chain tip if it received
the EB in time, has not voted on it yet, sees no equivocation, has
validated it, and is inside the voting window, provided that the EB is
not empty and that the node holds a committee seat with a registered
key.
```agda
CanVote : LeiosState → EndorserBlock → EBRef → ℕ → Type
CanVote s eb ebHash slot' = let open LeiosState s in
    getCurrentEBHash s ≡ just ebHash
  × find (λ (_ , eb') → hash eb' ≟ ebHash) EBs' ≡ just (slot' , eb)
  × hash eb ∉ VotedEBs
  × ¬ isEquivocated s eb
  × isValid s (inj₁ (ebHeader eb))
  × slot' ≤ slotNumber eb + Lhdr
  × slotNumber eb + 3 * Lhdr ≤ slot
  × slot ≤ slotNumber eb + 3 * Lhdr + Lvote
  × isValidityChecked slot eb
  × EndorserBlockOSig.txs eb ≢ []
  × inVotingCommittee params (stake s)
  -- Committee membership is by stake; signing also needs a registered key
  × id ∈ˡ L.map poolID PubKeys

allDone : LeiosState → Type
allDone record { Upkeep = u } = VT-Role ∈ˡ u × EB-Role ∈ˡ u × Base ∈ˡ u × CertCheck ∈ˡ u
```
Voting happens within a window: it opens `3 * Lhdr` slots after the announcing
RB's slot (the equivocation-detection period) and closes `Lvote` slots later.
`voteDeadline` is the last slot at which the current EB may still be voted on;
when there is no current EB (or it has not been received yet) the deadline is `0`,
so the deferral rule `VT-Defer` below is vacuously inapplicable and abstention is
governed solely by `No-VT-Role`.
```agda
voteDeadline : LeiosState → ℕ
voteDeadline s = let open LeiosState s in
  case getCurrentEBHash s of λ where
    nothing       → 0
    (just ebHash) → case find (λ (_ , eb') → hash eb' ≟ ebHash) EBs' of λ where
      nothing         → 0
      (just (_ , eb)) → slotNumber eb + 3 * Lhdr + Lvote
```
### Linear Leios transitions

```agda
open Types params
open BaseAbstract B'

data _-⟦_/_⟧⇀_ : MachineType ((FFD ⊗₀ BaseIO) ⊗₀ VotingC) (IO ⊗₀ Adv) LeiosState where
```
#### Network and Ledger
```agda
  Slot : let open LeiosState s in
        ∙ allDone s
        ──────────────────────────────────────────────────────────────────
        s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ FFD-OUT msgs / just $ ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ FTCH-LDG ⟧⇀
          let s' = s ↑ L.filter (isValid? s) msgs
          in record s'
               { slot       = suc slot
               ; Upkeep     = []
               ; proposedEB = nothing
               }

  Chain : let open LeiosState s in
        ───────────────────────────────────────────────────────────────────
        s -⟦ ((L⊗ ϵ) ⊗R) ⊗R ↑ᵢ BASE-LDG rbs / nothing ⟧⇀ record s { RBs = rbs }
```
```agda
  Fetch : let open LeiosState s in
        ───────────────────────────────────────────────────────────────────────────
        s -⟦ L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FetchLdgI / just $ L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ FetchLdgO Ledger ⟧⇀ s
```
#### Mempool

The environment hands the node its current selection of transactions,
which replaces `ToPropose`.  `EB-Role` takes the EB share of it and the
RB-submitting rules the RB share; no rule removes the transactions they
include, so the environment must not offer them again.
```agda
  Mempool :
          ───────────────────────────────────────────────────────────────────────────
          s -⟦ L⊗ (ϵ ᵗ¹ ⊗R) ᵗ¹ ↑ᵢ SubmitTxs txs / nothing ⟧⇀ record s { ToPropose = txs }
```
#### Base chain

Submitted data is only taken into account by the base chain if the
submitting party is the base chain's block producer for the given slot.

`Base₁` announces the EB recorded by `EB-Role` in `proposedEB`.  The
premise `hasUpkeep EB-Role` makes the party settle its EB role for the
slot first, either by producing (which sets `proposedEB`) or by declining
through `No-EB-Role`; without it a `Base₁` step scheduled early in the slot
would announce `nothing` and strand the EB the party goes on to diffuse.
`Base₂` carries the same premise, so that the RB later submitted by
`Cert₁` or `Cert₂` announces the settled EB too: those rules need an
outstanding query, and only `Base₂` opens one (`Cert₃` merely replaces
it).
```agda
  Base₁   : let open LeiosState s in
          ∙ needsUpkeep Base
          ∙ needsUpkeep CertCheck
          ∙ hasUpkeep EB-Role
          ∙ certRequest s ≡ nothing
          ───────────────────────────────────────────────────────────────────────────
          s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / just $ ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ SUBMIT (mkRB s nothing) ⟧⇀
            addUpkeep (addUpkeep s CertCheck) Base
```
If the chain tip announces an EB whose voting window closed at least
`Ldiff` slots ago (see `certRequest`), the node instead queries the voting
functionality for a certificate before it submits: the `Base` upkeep stays
open until the answer arrives.
```agda
  Base₂   : let open LeiosState s in
          ∙ needsUpkeep CertCheck
          ∙ hasUpkeep EB-Role
          ∙ certRequest s ≡ just eb
          ───────────────────────────────────────────────────────────────────────────
          s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / just $ (L⊗ ϵ) ⊗R ↑ₒ QUERY (hash currentRB) ⟧⇀
            record (addUpkeep s CertCheck) { PendingQuery = just (hash currentRB) }
```
#### Certificates

`Cert₁` correlates the answer with the request recorded in
`PendingQuery`: it only accepts an answer while a query is outstanding, a
positive answer must certify the requested ranking block, and the request
is cleared on submission.

Since the chain tip may change between query and answer (`Chain` has no
premises), `Cert₁` also re-validates the request at submission time: the
pending query must still name the *current* tip, so a stale answer cannot
be embedded.  Keying on the tip rather than on the EB it announces also
catches a tip that moves to a different RB announcing the same EB.
`Base₁` and `Base₂` both need `CertCheck` unsettled, so neither can fire
again in the slot, and without further rules a tip change between query
and answer would leave `Base` open forever.  The two further rules are as
follows:

- `Cert₂`: the tip no longer calls for a certificate at all
  (`certRequest s ≡ nothing`).  The stale answer is discarded and the RB
  is submitted without a certificate, discharging `Base` as `Base₁`
  would.
- `Cert₃`: the tip has moved, so it calls for a certificate on a
  *different* ranking block than the one queried.  The stale answer is
  discarded and a fresh query is issued for the new tip; `Base` stays open
  until that query is answered.
```agda
  Cert₁ : let open LeiosState s in
        ∙ needsUpkeep Base
        ∙ CertCheck ∈ˡ Upkeep
        ∙ certRequest s ≡ just eb
        ∙ PendingQuery ≡ just (hash currentRB)
        ∙ Maybe.All (λ c → getEBHash c ≡ hash currentRB) c
        ───────────────────────────────────────────────────────────────────
        s -⟦ (L⊗ ϵ) ⊗R ↑ᵢ CERT c / just $ ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ SUBMIT (mkRB s c) ⟧⇀
          record (addUpkeep s Base) { PendingQuery = nothing }

  Cert₂ : let open LeiosState s in
        ∙ needsUpkeep Base
        ∙ CertCheck ∈ˡ Upkeep
        ∙ certRequest s ≡ nothing
        ∙ PendingQuery ≡ just r
        ───────────────────────────────────────────────────────────────────
        s -⟦ (L⊗ ϵ) ⊗R ↑ᵢ CERT c / just $ ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ SUBMIT (mkRB s nothing) ⟧⇀
          record (addUpkeep s Base) { PendingQuery = nothing }

  Cert₃ : let open LeiosState s in
        ∙ needsUpkeep Base
        ∙ CertCheck ∈ˡ Upkeep
        ∙ certRequest s ≡ just eb
        ∙ PendingQuery ≡ just r
        ∙ hash currentRB ≢ r
        ───────────────────────────────────────────────────────────────────
        s -⟦ (L⊗ ϵ) ⊗R ↑ᵢ CERT c / just $ (L⊗ ϵ) ⊗R ↑ₒ QUERY (hash currentRB) ⟧⇀
          record s { PendingQuery = just (hash currentRB) }
```
#### Roles

An EB goes to the network; a vote goes to the voting functionality.
```agda
  EB-Role : let open LeiosState s in
            ∙ CanProposeEB s π eb
            ∙ needsUpkeep EB-Role
            ──────────────────────────────────────────────────
            s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / just $ ((ϵ ⊗R) ⊗R) ⊗R ↑ₒ FFD-IN (Send (ebHeader eb) nothing) ⟧⇀
              rememberProposal (addUpkeep s EB-Role) eb

  No-EB-Role : let open LeiosState s in
               ∙ ¬ (∃₂ λ π eb → CanProposeEB s π eb)
               ∙ needsUpkeep EB-Role
               ──────────────────────────────────────────────────
               s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / nothing ⟧⇀ addUpkeep s EB-Role

  VT-Role : ∀ {ebHash slot'} → let open LeiosState s in
          ∙ CanVote s eb ebHash slot'
          ∙ needsUpkeep VT-Role
          ──────────────────────────────────────────────────
          s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / just $ (L⊗ ϵ) ⊗R ↑ₒ CAST (vote sk-VT (hash currentRB)) ⟧⇀
            rememberVote (addUpkeep s VT-Role) eb

  No-VT-Role : let open LeiosState s in
               ∙ ¬ (∃[ eb ] ∃[ ebHash ] ∃[ slot' ] CanVote s eb ebHash slot')
               ∙ needsUpkeep VT-Role
               ──────────────────────────────────────────────────
               s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / nothing ⟧⇀ addUpkeep s VT-Role
```
Abstaining from voting is also permitted while the current EB's voting
window is still open, even when `VT-Role` could fire.  Together with
`No-VT-Role` this yields bounded liveness: at the deadline slot
`VT-Defer` no longer applies (the window closes), and `No-VT-Role` does
not apply while a vote can still be cast, so a node that can vote must
vote by then.
```agda
  VT-Defer : let open LeiosState s in
           ∙ slot < voteDeadline s
           ∙ needsUpkeep VT-Role
           ──────────────────────────────────────────────────
           s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / nothing ⟧⇀ addUpkeep s VT-Role
```
<!--
```agda
LinearLeios : Machine ((FFD ⊗₀ BaseIO) ⊗₀ VotingC) (IO ⊗₀ Adv)
LinearLeios .Machine.State = LeiosState
LinearLeios .Machine.stepRel = _-⟦_/_⟧⇀_

instance
  Dec-isValid : ∀ {s x} → isValid s x ⁇
  Dec-isValid {s} {x} = ⁇ isValid? s x

  Dec-isValidityChecked : ∀ {n eb} → isValidityChecked n eb ⁇
  Dec-isValidityChecked {n} {eb} = ⁇ isValidityChecked? n eb

unquoteDecl EB-Role-premises  = genPremises EB-Role-premises  (quote _-⟦_/_⟧⇀_.EB-Role)
unquoteDecl VT-Role-premises  = genPremises VT-Role-premises  (quote _-⟦_/_⟧⇀_.VT-Role)
unquoteDecl VT-Defer-premises = genPremises VT-Defer-premises (quote VT-Defer)

unquoteDecl Slot-premises = genPremises Slot-premises (quote _-⟦_/_⟧⇀_.Slot)
unquoteDecl Chain-premises = genPremises Chain-premises (quote _-⟦_/_⟧⇀_.Chain)
unquoteDecl Mempool-premises = genPremises Mempool-premises (quote Mempool)
unquoteDecl Base₁-premises = genPremises Base₁-premises (quote Base₁)
unquoteDecl Base₂-premises = genPremises Base₂-premises (quote Base₂)
unquoteDecl Cert₁-premises = genPremises Cert₁-premises (quote Cert₁)
unquoteDecl Cert₂-premises = genPremises Cert₂-premises (quote Cert₂)
unquoteDecl Cert₃-premises = genPremises Cert₃-premises (quote Cert₃)

just≢nothing : ∀ {ℓ} {A : Type ℓ} {x} → (Maybe A ∋ just x) ≡ nothing → ⊥
just≢nothing = λ ()

nothing≢just : ∀ {ℓ} {A : Type ℓ} {x} → nothing ≡ (Maybe A ∋ just x) → ⊥
nothing≢just = λ ()

P : EBRef → ℕ × EndorserBlock → Type
P h (_ , eb) = hash eb ≡ h

P? : (h : EBRef) → ((s , eb) : ℕ × EndorserBlock) → Dec (P h (s , eb))
P? h (_ , eb) = hash eb ≟ h

not-found : LeiosState → EBRef → Type
not-found s k = find (P? k) (LeiosState.EBs' s) ≡ nothing

subst' : ∀ {s ebHash ebHash₁ slot' slot'' eb eb₁}
  → getCurrentEBHash s ≡ just ebHash₁
  → find (λ (_ , eb') → hash eb' ≟ ebHash₁) (LeiosState.EBs' s) ≡ just (slot'' , eb₁)
  → getCurrentEBHash s ≡ just ebHash
  → find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) ≡ just (slot' , eb)
  → (eb₁ , ebHash₁ , slot'') ≡ (eb , ebHash , slot')
subst' {s} {ebHash = ebHash} {eb = eb} eq₁₁ eq₁₂ eq₂₁ eq₂₂
  with getCurrentEBHash s | eq₁₁ | eq₂₁
... | _ | refl | refl
  with find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) | eq₁₂ | eq₂₂
... | _ | refl | refl = refl

π-unique : ∀ {s π} → canProduceEB (LeiosState.slot s) sk-EB (stake s) π → π ≡ (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s)))
π-unique (_ , refl) = refl

instance

  Dec-CanProposeEB : ∀ {s} → (∃₂ λ π eb → CanProposeEB s π eb) ⁇
  Dec-CanProposeEB {s} .dec
    with toProposeEB s (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s))) in eq₁
  ... | nothing = no λ where
    (_ , _ , p , q) → nothing≢just (trans (sym eq₁) (subst (λ x → toProposeEB s x ≡ just _) (π-unique {s} q) p))
  ... | just eb
    with ¿ canProduceEB (LeiosState.slot s) sk-EB (stake s) _ ¿
  ... | yes q = yes (_ , eb , eq₁ , q)
  ... | no ¬q = no λ where
    (_ , _ , _ , q) → ¬q (subst (canProduceEB (LeiosState.slot s) sk-EB (stake s)) (π-unique {s} q) q)

  Dec-CanVote : ∀ {s} → (∃[ eb ] ∃[ ebHash ] ∃[ slot' ] CanVote s eb ebHash slot') ⁇
  Dec-CanVote {s} .dec = byTip (getCurrentEBHash s) refl
    where
      Goal : Type
      Goal = ∃[ eb ] ∃[ ebHash ] ∃[ slot' ] CanVote s eb ebHash slot'

      byEB : ∀ {ebHash} → getCurrentEBHash s ≡ just ebHash
           → ∀ m → find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) ≡ m → Dec Goal
      byEB eq₂ nothing eq₃ = no λ where
        (_ , _ , _ , x , y , _) →
          let ji = just-injective (trans (sym x) eq₂)
          in just≢nothing $ trans (sym y) (subst (not-found s) (sym ji) eq₃)
      byEB {ebHash} eq₂ (just (slot' , eb)) eq₃ = case ¿ CanVote s eb ebHash slot' ¿ of λ where
        (yes p) → yes (eb , ebHash , slot' , p)
        (no ¬p) → no λ where
          (_ , _ , _ , p@(x , y , _)) → ¬p $ subst
            (λ where (eb , ebHash , slot) → CanVote s eb ebHash slot)
            (subst' {s} x y eq₂ eq₃) p

      byTip : ∀ m → getCurrentEBHash s ≡ m → Dec Goal
      byTip nothing  eq₂ = no λ where (_ , _ , _ , p , _) → nothing≢just (trans (sym eq₂) p)
      byTip (just _) eq₂ = byEB eq₂ _ refl

unquoteDecl No-EB-Role-premises = genPremises No-EB-Role-premises (quote No-EB-Role)
unquoteDecl No-VT-Role-premises = genPremises No-VT-Role-premises (quote No-VT-Role)
```
-->

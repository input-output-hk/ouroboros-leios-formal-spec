{-# OPTIONS --safe #-}
{- Module: Test.Defaults

   This module provides simple default implementations for the core components
   and functionalities of the Leios protocol. These defaults are intended for
   building examples and traces for different Leios variants, and include
   basic instances for abstract types, VRF, key registration, base layer,
   FFD buffers, and voting. The implementations are minimal and primarily
   for testing and illustration purposes.
-}

open import Leios.Prelude hiding (_⊗_)
open import Leios.Abstract
open import Leios.Config
open import Leios.SpecStructure
open import Blockchain.Safety
import Blockchain.IsBlockchain

open import Axiom.Set.Properties th
open import Data.Nat.Show as N
open import Data.Integer hiding (_≟_)
open import Data.String as S using (intersperse)
open import Function.Related.TypeIsomorphisms
open import Relation.Binary.Structures

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open import LibExt

open import CategoricalCrypto using (I ; Machine ; machine-type ; Channel ; _⊗ᵀ_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection

open Equivalence

-- The module contains very simple implementations for the functionalities
-- that allow to build examples for traces for the different Leios variants
module Test.Defaults
  (params : Params) (let open Params params)
  (testParams : TestParams params) (let open TestParams testParams) where

instance
  htx : Hashable (List ℕ) (List ℕ)
  htx = record { hash = id }

d-Abstract : LeiosAbstract
d-Abstract =
  record
    { Tx                = ℕ
    ; PoolID            = Fin numberOfParties
    ; BodyHash          = List ℕ
    ; VrfPf             = ⊤
    ; PrivKey           = BlockType × ⊤
    ; Sig               = ⊤
    ; Hash              = List ℕ
    ; EBCert            = List ℕ
    ; getEBHash         = id
    ; Vote              = Fin numberOfParties × List ℕ
    ; vote              = λ _ h → sutId , h
    ; sign              = λ _ _ → tt
    ; splitTxs          = λ l → [] , l
    }

open LeiosAbstract d-Abstract public

open import Leios.VRF d-Abstract public

sutStake : ℕ
sutStake = TotalMap.lookup stakeDistribution sutId

sortition : BlockType → ℕ → ℕ
sortition b n with (b , n) ∈? winning-slots
... | yes _ = 0
... | no _ = sutStake

d-VRF : LeiosVRF
d-VRF =
  record
    { PubKey     = Fin numberOfParties × ⊤
    ; vrf        =
        record
          { isKeyPair = λ _ _ → ⊤
          ; eval      = λ (b , _) y → sortition b y , tt
          ; verify    = λ _ _ _ _ → ⊤
          ; verify?   = λ _ _ _ _ → yes tt
          }
    ; genIBInput = id
    ; genEBInput = id
    ; genVInput  = id
    ; genV1Input = id
    ; genV2Input = id
    ; poolID     = proj₁
    ; verifySig  = λ _ _ → ⊤
    ; verifySig? = λ _ _ → yes tt
    }

open LeiosVRF d-VRF public

open import Leios.Blocks d-Abstract public
open import Leios.KeyRegistration d-Abstract d-VRF public

d-KeyRegistration : KeyRegistrationAbstract
d-KeyRegistration = _

d-KeyRegistrationFunctionality : KeyRegistrationAbstract.Functionality d-KeyRegistration
d-KeyRegistrationFunctionality =
  record
    { State     = ⊤
    ; _-⟦_/_⟧⇀_ = λ _ _ _ _ → ⊤
    }

open import Leios.Base d-Abstract d-VRF public

d-Base : BaseAbstract
d-Base =
  record
    { Cert        = ⊤
    ; VTy         = ⊤
    ; initSlot    = λ _ → 0
    ; V-chkCerts  = λ _ _ → true
    ; BaseAdv     = I
    ; BaseMsg     = ⊤
    }

d-BaseState : Type
d-BaseState = List RankingBlock × ℕ

d-BaseChannel : Channel
d-BaseChannel = BaseNetwork ⊗ᵀ (BaseIO ⊗₀ BaseAdv)
  where open BaseAbstract d-Base

data d-BaseRel : machine-type d-BaseState d-BaseChannel where

  fetch-blocks :
    ∀ blocks slot →
      d-BaseRel
        (blocks , slot)
        (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ BaseAbstract.FTCH-LDG)
        (just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.BASE-LDG blocks))
        (blocks , slot)

  fetch-slot :
    ∀ blocks slot →
      d-BaseRel
        (blocks , slot)
        (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ BaseAbstract.FTCH-SLOT)
        (just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.SLOT slot))
        (blocks , slot)

open Blockchain.IsBlockchain (Fin 1)

helper : BlockChainInfo RankingBlock → BaseAbstract.BaseIOF d-Base CategoricalCrypto.Out
helper = let open BaseAbstract.BaseIOF in λ where
  Chain → FTCH-LDG
  Slot  → FTCH-SLOT

private
  open BaseAbstract.BaseIOF

  opaque
    unfolding _⊗₀_

    correctness-chain : ∀ {s response' s'}
      → d-BaseRel s (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-LDG) response' s'
      → ∃ λ response → response' ≡ just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BASE-LDG response)
    correctness-chain (fetch-blocks blocks _) = blocks , refl

    correctness-slot : ∀ {s response' s'}
      → d-BaseRel s (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-SLOT) response' s'
      → ∃ λ response → response' ≡ just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ SLOT response)
    correctness-slot (fetch-slot _ slot) = slot , refl

    isPure-chain : ∀ {s response' s'}
      → d-BaseRel s (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-LDG) response' s'
      → s ≡ s'
    isPure-chain (fetch-blocks _ _) = refl

    isPure-slot : ∀ {s response' s'}
      → d-BaseRel s (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-SLOT) response' s'
      → s ≡ s'
    isPure-slot (fetch-slot _ _) = refl

d-BaseFunctionality : BaseAbstract.BaseMachine d-Base
d-BaseFunctionality =
  record
    { n = 1
    ; m =
        record
          { State = (List RankingBlock × ℕ)
          ; stepRel = d-BaseRel
          }
    ; is-blockchain = let open BaseAbstract.BaseIOF in
        record
          { isConstrained =
              record
                { queryI = (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ_) ∘ helper
                ; queryO = λ where
                    {Chain} rankingBlocks → L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BASE-LDG rankingBlocks
                    {Slot}  slot          → L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ SLOT slot
                ; correctness = λ where
                    {Chain} → correctness-chain
                    {Slot}  → correctness-slot
                ; completeness = λ where
                    {Chain} {blocks , slot} → L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.BASE-LDG blocks , (blocks , slot) , fetch-blocks blocks slot
                    {Slot}  {blocks , slot} → L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.SLOT     slot   , (blocks , slot) , fetch-slot   blocks slot
                }
          ; isPure = λ where
              Chain → isPure-chain
              Slot  → isPure-slot
          ; producer = λ _ → Fin.zero
          ; slotOf   = λ _ → 0
          }
    }

open import Leios.FFD public

instance
  isb : IsBlock (List Vote)
  isb =
    record
      { slotNumber = λ _ → 0
      ; producerID = λ _ → sutId
      ; lotteryPf  = λ _ → tt
      }

  hpe : Hashable PreEndorserBlock Hash
  hpe .hash = EndorserBlockOSig.txs

record FFDBuffers : Type where
  field inEBs : List EndorserBlock
        inVTs : List (List Vote)

        outEBs : List EndorserBlock
        outVTs : List (List Vote)

unquoteDecl DecEq-FFDBuffers = derive-DecEq ((quote FFDBuffers , DecEq-FFDBuffers) ∷ [])

open GenFFD.Header
open FFDBuffers

flushIns : FFDBuffers → List (GenFFD.Header ⊎ GenFFD.Body)
flushIns record { inEBs = ebs ; inVTs = vts } =
  L.map (inj₁ ∘ ebHeader) ebs ++ L.map (inj₁ ∘ vtHeader) vts


data SimpleFFD : FFDBuffers → FFDAbstract.Input ffdAbstract → FFDAbstract.Output ffdAbstract → FFDBuffers → Type where
  SendEB : ∀ {s eb}     → SimpleFFD s (FFDAbstract.Send (ebHeader eb) nothing) FFDAbstract.SendRes (record s { outEBs = eb ∷ outEBs s})
  SendVS : ∀ {s vs}     → SimpleFFD s (FFDAbstract.Send (vtHeader vs) nothing) FFDAbstract.SendRes (record s { outVTs = vs ∷ outVTs s})

  BadSendEB : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (ebHeader h) (just b)) FFDAbstract.SendRes s
  BadSendVS : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (vtHeader h) (just b)) FFDAbstract.SendRes s

  Fetch : ∀ {s}         → SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes (flushIns s)) (record s { inEBs = [] ; inVTs = [] })

send-total : ∀ {s h b} → ∃[ s' ] (SimpleFFD s (FFDAbstract.Send h b) FFDAbstract.SendRes s')
send-total {s} {ebHeader eb} {nothing}        = record s { outEBs = eb ∷ outEBs s} , SendEB
send-total {s} {vtHeader vs} {nothing}        = record s { outVTs = vs ∷ outVTs s} , SendVS

send-total {s} {ebHeader eb} {just _} = s , BadSendEB
send-total {s} {vtHeader vs} {just _} = s , BadSendVS

fetch-total : ∀ {s} → ∃[ x ] (∃[ s' ] (SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes x) s'))
fetch-total {s} = flushIns s , (record s { inEBs = [] ; inVTs = [] } , Fetch)

send-complete : ∀ {s h b s'} → SimpleFFD s (FFDAbstract.Send h b) FFDAbstract.SendRes s' → s' ≡ proj₁ (send-total {s} {h} {b})
send-complete SendEB    = refl
send-complete SendVS    = refl
send-complete BadSendEB = refl
send-complete BadSendVS = refl

fetch-complete₁ : ∀ {s r s'} → SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes r) s' → s' ≡ proj₁ (proj₂ (fetch-total {s}))
fetch-complete₁ Fetch = refl

fetch-complete₂ : ∀ {s r s'} → SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes r) s' → r ≡ proj₁ (fetch-total {s})
fetch-complete₂ Fetch = refl

instance
  Dec-SimpleFFD : ∀ {s i o s'} → SimpleFFD s i o s' ⁇
  Dec-SimpleFFD {s} {FFDAbstract.Send h b} {FFDAbstract.SendRes} {s'} with s' ≟ proj₁ (send-total {s} {h} {b})
  ... | yes p rewrite p = ⁇ yes (proj₂ send-total)
  ... | no ¬p = ⁇ no λ x → ⊥-elim (¬p (send-complete x))
  Dec-SimpleFFD {_} {FFDAbstract.Send _ _} {FFDAbstract.FetchRes _} {_} = ⁇ no λ ()
  Dec-SimpleFFD {s} {FFDAbstract.Fetch} {FFDAbstract.FetchRes r} {s'}
    with s' ≟ proj₁ (proj₂ (fetch-total {s})) | r ≟ proj₁ (fetch-total {s}) -- TODO: improve performance
  ... | yes p | yes q rewrite p rewrite q = ⁇ yes (proj₂ (proj₂ (fetch-total {s})))
  ... | _     | no ¬q = ⁇ no λ x → ⊥-elim (¬q (fetch-complete₂ x))
  ... | no ¬p | _     = ⁇ no λ x → ⊥-elim (¬p (fetch-complete₁ x))
  Dec-SimpleFFD {_} {FFDAbstract.Fetch} {FFDAbstract.SendRes} {_} = ⁇ no λ ()

d-FFDFunctionality : FFDAbstract.Functionality ffdAbstract
d-FFDFunctionality =
  record
    { State         = FFDBuffers
    ; initFFDState  = record { inEBs = []; inVTs = []; outEBs = []; outVTs = [] }
    ; _-⟦_/_⟧⇀_     = SimpleFFD
    }

open import Leios.Voting public
open import Class.DecEq.Instances
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-filter⁻; ∈-deduplicate⁻)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Unique.DecPropositional.Properties as UDP′
import Leios.Voting.Ideal

-- Voting instance (issue #689): the ideal quorum certificate, realised via
-- `Leios.Voting.Realize`.  Votes are (voter , EB hash) pairs, so the ideal
-- model runs over `Hash` and is re-indexed to `EndorserBlock` via
-- `mapVotingAbstract hash`.  For these defaults everyone is honest, every
-- vote is valid, no party is corrupt, and the quorum threshold is 1.
d-Party : Type
d-Party = PoolID

d-honest : d-Party → Type
d-honest _ = ⊤

d-Validated : d-Party → Hash → Type
d-Validated _ _ = ⊤

d-Valid : Vote → Type
d-Valid _ = ⊤

d-bound : 0 Leios.Prelude.N.< 1
d-bound = Leios.Prelude.N.s≤s Leios.Prelude.N.z≤n

module VotingRealize
  (Party      : Type) ⦃ _ : DecEq Party ⦄
  (EBRef      : Type) ⦃ _ : DecEq EBRef ⦄
  (honest     : Party → Type) ⦃ _ : honest ⁇¹ ⦄
  (Validated  : Party → EBRef → Type)
  (threshold  : ℕ)
  (corrupt    : List Party)
  (bound      : length corrupt Leios.Prelude.N.< threshold)
  (Vote       : Type)
  (voter      : Vote → Party)
  (forEB      : Vote → EBRef)
  (Valid      : Vote → Type) ⦃ _ : Valid ⁇¹ ⦄
  (validated-if-honest : ∀ v → Valid v → honest (voter v) → Validated (voter v) (forEB v))
  (corrupt-covers      : ∀ v → Valid v → ¬ honest (voter v) → voter v ∈ˡ corrupt)
  where

  module I = Leios.Voting.Ideal Party EBRef honest Validated threshold

  _≟ₚ_ : ∀ (x y : Party) → Dec (x ≡ y)
  _≟ₚ_ = _≟_

  module UDP = UDP′ _≟ₚ_

  log : I.IdealState → List (Party × EBRef)
  log = I.IdealState.voteLog

  rawVoters : I.IdealState → EBRef → List Party
  rawVoters st eb = L.map proj₁ (L.filter (λ pe → proj₂ pe ≟ eb) (log st))

  votersFor : I.IdealState → EBRef → List Party
  votersFor st eb = L.deduplicate _≟ₚ_ (rawVoters st eb)

  isCert : I.IdealState → EBRef → Type
  isCert st eb = threshold Leios.Prelude.N.≤ length (votersFor st eb)

  buildCert : ∀ {st eb} → isCert st eb → I.Certified st eb
  buildCert {st} {eb} h = record
    { voters = votersFor st eb
    ; unique = UDP.deduplicate-! (rawVoters st eb)
    ; voted  = All.tabulate voted?
    ; quorum = h
    }
    where
      voted? : ∀ {p} → p ∈ˡ votersFor st eb → I.Voted p eb st
      voted? {p} p∈ with ∈-deduplicate⁻ _≟ₚ_ (rawVoters st eb) p∈
      ... | p∈raw with ∈-map⁻ proj₁ p∈raw
      ... | pe , pe∈filter , p≡ with ∈-filter⁻ (λ pe → proj₂ pe ≟ eb) pe∈filter
      ... | pe∈log , pf = subst (_∈ˡ log st) (cong₂ _,_ (sym p≡) pf) pe∈log

  record VState : Type where
    field
      st  : I.IdealState
      wf  : I.WF st
      cov : ∀ {p eb} → I.Voted p eb st → ¬ honest p → p ∈ˡ corrupt

  addVoteV : VState → Vote → VState
  addVoteV vs v with ¿ Valid v ¿
  ... | no  _   = vs
  ... | yes val = record
    { st  = I.⟨ (voter v , forEB v) ∷ log (VState.st vs) ⟩
    ; wf  = λ where (here refl) h  → validated-if-honest v val h
                    (there x)   h  → VState.wf vs x h
    ; cov = λ where (here refl) ¬h → corrupt-covers v val ¬h
                    (there x)   ¬h → VState.cov vs x ¬h
    }

  votingAbstract : VotingAbstract Vote EBRef
  votingAbstract = record
    { VotingState     = VState
    ; initVotingState = record { st = I.init ; wf = I.wf-init ; cov = λ () }
    ; addVote         = addVoteV
    ; isVoteCertified = λ vs eb → isCert (VState.st vs) eb
    ; isVoteCertified⁇ = λ {vs} {eb} → record { dec = threshold Leios.Prelude.N.≤? length (votersFor (VState.st vs) eb) }
    ; Voter           = Party
    ; HonestVoter     = honest
    ; ValidatedBy     = Validated
    ; cert-correct    = λ {vs} {eb} h →
        I.cert-correct (VState.wf vs) corrupt (λ v ¬h → VState.cov vs v ¬h) bound (buildCert h)
    }

module RV = VotingRealize
  d-Party Hash d-honest d-Validated 1 [] d-bound
  Vote proj₁ proj₂ d-Valid
  (λ _ _ _ → tt) (λ _ _ ¬h → ⊥-elim (¬h tt))

d-VotingAbstract : VotingAbstract Vote EndorserBlock
d-VotingAbstract = mapVotingAbstract (hash ⦃ Hashable-EndorserBlock ⦃ hpe ⦄ ⦄) RV.votingAbstract
  where
    mapVotingAbstract : ∀ {Vote Subject₁ Subject₂ : Type} → (Subject₂ → Subject₁)
                        → VotingAbstract Vote Subject₁ → VotingAbstract Vote Subject₂
    mapVotingAbstract f va = record
      { VotingState      = VotingState
      ; initVotingState  = initVotingState
      ; addVote          = addVote
      ; isVoteCertified  = λ vs y → isVoteCertified vs (f y)
      ; isVoteCertified⁇ = isVoteCertified⁇
      ; Voter            = Voter
      ; HonestVoter      = HonestVoter
      ; ValidatedBy      = λ p y → ValidatedBy p (f y)
      ; cert-correct     = cert-correct
      } where open VotingAbstract va

d-SpecStructure : SpecStructure
d-SpecStructure = record
      { a                         = d-Abstract
      ; Hashable-PreEndorserBlock = hpe
      ; id                        = sutId
      ; FFD'                      = d-FFDFunctionality
      ; vrf'                      = d-VRF
      ; sk-EB                     = EB , tt
      ; sk-VT                     = VT , tt
      ; pk-EB                     = sutId , tt
      ; pk-VT                     = sutId , tt
      ; B'                        = d-Base
      ; BM                        = d-BaseFunctionality
      ; K'                        = d-KeyRegistration
      ; KF                        = d-KeyRegistrationFunctionality
      ; va                        = d-VotingAbstract
      ; getEBCert                 = λ _ → []
      ; validityCheckTime         = λ _ → 4
      }

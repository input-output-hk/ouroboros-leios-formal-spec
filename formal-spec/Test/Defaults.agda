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
open import Leios.Safety

open import Axiom.Set.Properties th
open import Data.Nat.Show as N
open import Data.Integer hiding (_≟_)
open import Data.String as S using (intersperse)
open import Function.Related.TypeIsomorphisms
open import Relation.Binary.Structures

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open import LibExt

open import CategoricalCrypto using (I ; Machine ; machine-type ; Channel ; _⊗ᵀ_ ; _⊗_)
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
    ; Vote              = ⊤
    ; vote              = λ _ _ → tt
    ; sign              = λ _ _ → tt
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

module _ where
  open BaseAbstract d-Base

  d-BaseChannel : Channel
  d-BaseChannel = BaseNetwork ⊗ᵀ (BaseIO ⊗ BaseAdv)

  data d-BaseRel : machine-type d-BaseState d-BaseChannel where

    fetch-blocks :
      ∀ {blocks slot} →
        d-BaseRel
          (blocks , slot)
          (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ BaseAbstract.FTCH-LDG)
          (just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.BASE-LDG blocks))
          (blocks , slot)

    fetch-slot :
      ∀ {blocks slot} →
        d-BaseRel
          (blocks , slot)
          (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ BaseAbstract.FTCH-SLOT)
          (just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.SLOT slot))
          (blocks , slot)


  d-BaseMachine : Machine BaseNetwork (BaseIO ⊗ BaseAdv)
  d-BaseMachine = record {State = List RankingBlock × ℕ ; stepRel = d-BaseRel }

module _ where
  open BaseAbstract.BaseIOF
  open Machine d-BaseMachine
  open Channel machine-channel

  d-BaseQueryI : BlockChainInfo RankingBlock → inType
  d-BaseQueryI Chain = L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-LDG
  d-BaseQueryI Slot = L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-SLOT

  d-BaseQueryO : ∀ {query} → bciQueryType RankingBlock query → outType
  d-BaseQueryO {Chain} rankingBlocks = L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BASE-LDG rankingBlocks
  d-BaseQueryO {Slot} slot = L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ SLOT slot

  d-BaseCorrectness : ∀ {query} {s} → ∃ λ response' → ∃ {A = State} λ s' → stepRel s (d-BaseQueryI query) (just response') s'
  d-BaseCorrectness {Chain} {blocks , slot} = L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.BASE-LDG blocks , (blocks , slot) , fetch-blocks
  d-BaseCorrectness {Slot} {blocks , slot} = L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.SLOT slot , (blocks , slot) , fetch-slot

  opaque
    unfolding
      _⊗_

    d-BaseFunctionality : BaseAbstract.BaseMachine d-Base
    d-BaseFunctionality =
      record
        { m = d-BaseMachine
        ; is-blockchain =
            record
              { isConstrained =
                  record
                    { queryI = d-BaseQueryI
                    ; queryO = d-BaseQueryO
                    ; correctness = λ where {Chain} fetch-blocks → -, refl
                                            {Slot} fetch-slot → -, refl
                    ; completeness = λ {query} → d-BaseCorrectness {query}
                    }
              ; isPure = λ where Chain fetch-blocks → refl
                                 Slot fetch-slot → refl
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

d-VotingAbstract : VotingAbstract EndorserBlock
d-VotingAbstract =
  record
    { VotingState     = ⊤
    ; initVotingState = tt
    ; isVoteCertified = λ _ _ → ⊤
    }

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
      }

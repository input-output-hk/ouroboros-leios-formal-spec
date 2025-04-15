open import Leios.Prelude
open import Leios.Abstract
open import Leios.Config
open import Leios.SpecStructure

open import Axiom.Set.Properties th
open import Data.Nat.Show as N
open import Data.Integer hiding (_≟_)
open import Data.String as S using (intersperse)
open import Function.Related.TypeIsomorphisms
open import Relation.Binary.Structures

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open Equivalence

-- The module contains very simple implementations for the functionalities
-- that allow to build examples for traces for the different Leios variants
module Leios.Defaults (params : Params) (let open Params params) where

instance
  htx : Hashable (List ℕ) (List ℕ)
  htx = record { hash = id }

data BlockType : Type where
  IB EB VT : BlockType

d-Abstract : LeiosAbstract
d-Abstract =
  record
    { Tx       = ℕ
    ; PoolID   = Fin numberOfParties
    ; BodyHash = List ℕ
    ; VrfPf    = ⊤
    ; PrivKey  = BlockType × ⊤
    ; Sig      = ⊤
    ; Hash     = List ℕ
    ; Vote     = ⊤
    ; vote     = λ _ _ → tt
    ; sign     = λ _ _ → tt
    ; L        = stageLength
    }

open LeiosAbstract d-Abstract public

open import Leios.VRF d-Abstract public

totalStake : ℕ
totalStake = L.sum $ setToList $ range $ TotalMap.toMap stakeDistribution

open import Data.List.Membership.DecPropositional N._≟_ renaming (_∈?_ to _∈ˡ?_)
sortition : BlockType → ℕ → ℕ
sortition IB n with n ∈ˡ? ib-slots
... | yes _ = 0
... | no _ = N.suc totalStake
sortition EB n with n ∈ˡ? eb-slots
... | yes _ = 0
... | no _ = N.suc totalStake
sortition VT n with n ∈ˡ? vt-slots
... | yes _ = 0
... | no _ = N.suc totalStake

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
    { Cert       = ⊤
    ; VTy        = ⊤
    ; initSlot   = λ _ → 0
    ; V-chkCerts = λ _ _ → true
    }

d-BaseFunctionality : BaseAbstract.Functionality d-Base
d-BaseFunctionality =
  record
    { State         = ⊤
    ; _-⟦_/_⟧⇀_     = λ _ _ _ _ → ⊤
    ; Dec-_-⟦_/_⟧⇀_ = ⁇ (yes tt)
    ; SUBMIT-total  = tt , tt
    }

open import Leios.FFD public

instance
  isb : IsBlock (List ⊤)
  isb =
    record
      { slotNumber = λ _ → 0
      ; producerID = λ _ → sutId
      ; lotteryPf  = λ _ → tt
      }

  hhs : Hashable PreIBHeader (List ℕ)
  hhs .hash = IBHeaderOSig.bodyHash

  hpe : Hashable PreEndorserBlock (List ℕ)
  hpe .hash = L.concat ∘ EndorserBlockOSig.ibRefs

record FFDState : Type where
  field inIBs : List InputBlock
        inEBs : List EndorserBlock
        inVTs : List (List Vote)

        outIBs : List InputBlock
        outEBs : List EndorserBlock
        outVTs : List (List Vote)

unquoteDecl DecEq-FFDState = derive-DecEq ((quote FFDState , DecEq-FFDState) ∷ [])

open GenFFD.Header
open GenFFD.Body
open FFDState

flushIns : FFDState → List (GenFFD.Header ⊎ GenFFD.Body)
flushIns record { inIBs = ibs ; inEBs = ebs ; inVTs = vts } =
  flushIBs ibs ++ L.map (inj₁ ∘ ebHeader) ebs ++ L.map (inj₁ ∘ vtHeader) vts
  where
    flushIBs : List InputBlock → List (GenFFD.Header ⊎ GenFFD.Body)
    flushIBs [] = []
    flushIBs (record {header = h; body = b} ∷ ibs) = inj₁ (ibHeader h) ∷ inj₂ (ibBody b) ∷ flushIBs ibs

data SimpleFFD : FFDState → FFDAbstract.Input ffdAbstract → FFDAbstract.Output ffdAbstract → FFDState → Type where
  SendIB : ∀ {s h b}    → SimpleFFD s (FFDAbstract.Send (ibHeader h) (just (ibBody b))) FFDAbstract.SendRes (record s { outIBs = record {header = h; body = b} ∷ outIBs s})
  SendEB : ∀ {s eb}     → SimpleFFD s (FFDAbstract.Send (ebHeader eb) nothing) FFDAbstract.SendRes (record s { outEBs = eb ∷ outEBs s})
  SendVS : ∀ {s vs}     → SimpleFFD s (FFDAbstract.Send (vtHeader vs) nothing) FFDAbstract.SendRes (record s { outVTs = vs ∷ outVTs s})

  BadSendIB : ∀ {s h}   → SimpleFFD s (FFDAbstract.Send (ibHeader h) nothing) FFDAbstract.SendRes s
  BadSendEB : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (ebHeader h) (just b)) FFDAbstract.SendRes s
  BadSendVS : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (vtHeader h) (just b)) FFDAbstract.SendRes s

  Fetch : ∀ {s}         → SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes (flushIns s)) (record s { inIBs = [] ; inEBs = [] ; inVTs = [] })

send-total : ∀ {s h b} → ∃[ s' ] (SimpleFFD s (FFDAbstract.Send h b) FFDAbstract.SendRes s')
send-total {s} {ibHeader h} {just (ibBody b)} = record s { outIBs = record {header = h; body = b} ∷ outIBs s} , SendIB
send-total {s} {ebHeader eb} {nothing}        = record s { outEBs = eb ∷ outEBs s} , SendEB
send-total {s} {vtHeader vs} {nothing}        = record s { outVTs = vs ∷ outVTs s} , SendVS

send-total {s} {ibHeader h} {nothing} = s , BadSendIB
send-total {s} {ebHeader eb} {just _} = s , BadSendEB
send-total {s} {vtHeader vs} {just _} = s , BadSendVS

fetch-total : ∀ {s} → ∃[ x ] (∃[ s' ] (SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes x) s'))
fetch-total {s} = flushIns s , (record s { inIBs = [] ; inEBs = [] ; inVTs = [] } , Fetch)

send-complete : ∀ {s h b s'} → SimpleFFD s (FFDAbstract.Send h b) FFDAbstract.SendRes s' → s' ≡ proj₁ (send-total {s} {h} {b})
send-complete SendIB    = refl
send-complete SendEB    = refl
send-complete SendVS    = refl
send-complete BadSendIB = refl
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
    with s' ≟ proj₁ (proj₂ (fetch-total {s}))
      | r ≟ proj₁ (fetch-total {s})
  ... | yes p | yes q rewrite p rewrite q = ⁇ yes (proj₂ (proj₂ (fetch-total {s})))
  ... | yes p | no ¬q = ⁇ no λ x → ⊥-elim (¬q (fetch-complete₂ x))
  ... | no ¬p | _ = ⁇ no λ x → ⊥-elim (¬p (fetch-complete₁ x))
  Dec-SimpleFFD {_} {FFDAbstract.Fetch} {FFDAbstract.SendRes} {_} = ⁇ no λ ()

d-FFDFunctionality : FFDAbstract.Functionality ffdAbstract
d-FFDFunctionality =
  record
    { State          = FFDState
    ; initFFDState   = record { inIBs = []; inEBs = []; inVTs = []; outIBs = []; outEBs = []; outVTs = [] }
    ; _-⟦_/_⟧⇀_      = SimpleFFD
    ; Dec-_-⟦_/_⟧⇀_  = Dec-SimpleFFD
    ; FFD-Send-total = send-total
    }

open import Leios.Voting public

d-VotingAbstract : VotingAbstract (Fin 1 × EndorserBlock)
d-VotingAbstract =
  record
    { VotingState     = ⊤
    ; initVotingState = tt
    ; isVoteCertified = λ _ _ → ⊤
    }

d-VotingAbstract-2 : VotingAbstract (Fin 2 × EndorserBlock)
d-VotingAbstract-2 =
  record
    { VotingState     = ⊤
    ; initVotingState = tt
    ; isVoteCertified = λ _ _ → ⊤
    }

d-SpecStructure : SpecStructure 1
d-SpecStructure = record
      { a                         = d-Abstract
      ; Hashable-PreIBHeader      = hhs
      ; Hashable-PreEndorserBlock = hpe
      ; id                        = sutId
      ; FFD'                      = d-FFDFunctionality
      ; vrf'                      = d-VRF
      ; sk-IB                     = IB , tt
      ; sk-EB                     = EB , tt
      ; sk-VT                     = VT , tt
      ; pk-IB                     = sutId , tt
      ; pk-EB                     = sutId , tt
      ; pk-VT                     = sutId , tt
      ; B'                        = d-Base
      ; BF                        = d-BaseFunctionality
      ; initBaseState             = tt
      ; K'                        = d-KeyRegistration
      ; KF                        = d-KeyRegistrationFunctionality
      ; va                        = d-VotingAbstract
      }

d-SpecStructure-2 : SpecStructure 2
d-SpecStructure-2 = record
      { a                         = d-Abstract
      ; Hashable-PreIBHeader      = hhs
      ; Hashable-PreEndorserBlock = hpe
      ; id                        = sutId
      ; FFD'                      = d-FFDFunctionality
      ; vrf'                      = d-VRF
      ; sk-IB                     = IB , tt
      ; sk-EB                     = EB , tt
      ; sk-VT                     = VT , tt
      ; pk-IB                     = sutId , tt
      ; pk-EB                     = sutId , tt
      ; pk-VT                     = sutId , tt
      ; B'                        = d-Base
      ; BF                        = d-BaseFunctionality
      ; initBaseState             = tt
      ; K'                        = d-KeyRegistration
      ; KF                        = d-KeyRegistrationFunctionality
      ; va                        = d-VotingAbstract-2
      }

open import Leios.Short d-SpecStructure public

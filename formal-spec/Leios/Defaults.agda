open import Leios.Prelude
open import Leios.Abstract
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
--
-- As parameters the module expects
-- * numberOfParties: the total number of participants
-- * SUT-id: the number of the SUT (system under test)
module Leios.Defaults (numberOfParties : ℕ) (SUT-id : Fin numberOfParties) where

instance
  htx : Hashable (List ℕ) String
  htx = record { hash = S.intersperse "#" ∘ L.map N.show }

d-Abstract : LeiosAbstract
d-Abstract =
  record
    { Tx = ℕ
    ; PoolID = Fin numberOfParties
    ; BodyHash = ⊤
    ; VrfPf = ⊤
    ; PrivKey = ⊤
    ; Sig = ⊤
    ; Hash = String
    ; Vote = ⊤
    ; vote = λ _ _ → tt
    ; sign = λ _ _ → tt
    ; L = 5
    }

open LeiosAbstract d-Abstract public

open import Leios.VRF d-Abstract public

d-VRF : LeiosVRF
d-VRF =
  record
    { PubKey     = ⊤
    ; vrf        = record { isKeyPair = λ _ _ → ⊤ ; eval = λ x x₁ → x₁ , x ; verify = λ _ _ _ _ → ⊤  ; verify? = λ _ _ _ _ → yes tt }
    ; genIBInput = id
    ; genEBInput = id
    ; genVInput  = id
    ; genV1Input = id
    ; genV2Input = id
    ; poolID     = λ _ → SUT-id
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
    { State = ⊤
    ; _-⟦_/_⟧⇀_ = λ _ _ _ _ → ⊤
    }

open import Leios.Base d-Abstract d-VRF public

d-Base : BaseAbstract
d-Base =
  record
    { Cert = ⊤
    ; VTy = ⊤
    ; initSlot = λ _ → 0
    ; V-chkCerts = λ _ _ → true
    }

d-BaseFunctionality : BaseAbstract.Functionality d-Base
d-BaseFunctionality =
  record
    { State = ⊤
    ; _-⟦_/_⟧⇀_ = λ _ _ _ _ → ⊤
    ; Dec-_-⟦_/_⟧⇀_ = ⁇ (yes tt)
    ; SUBMIT-total = tt , tt
    }

open import Leios.FFD public

instance
  isb : IsBlock (List ⊤)
  isb =
    record
      { slotNumber = λ _ → 0
      ; producerID = λ _ → SUT-id
      ; lotteryPf = λ _ → tt
      }

  hhs : Hashable PreIBHeader String
  hhs = record { hash = IBHeaderOSig.bodyHash }

  hpe : Hashable PreEndorserBlock String
  hpe = record { hash = S.intersperse "#" ∘ EndorserBlockOSig.ibRefs }

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
  flushIBs ibs ++ L.map (inj₁ ∘ ebHeader) ebs ++ L.map (inj₁ ∘ vHeader) vts
  where
    flushIBs : List InputBlock → List (GenFFD.Header ⊎ GenFFD.Body)
    flushIBs [] = []
    flushIBs (record {header = h; body = b} ∷ ibs) = inj₁ (ibHeader h) ∷ inj₂ (ibBody b) ∷ flushIBs ibs

data SimpleFFD : FFDState → FFDAbstract.Input ffdAbstract → FFDAbstract.Output ffdAbstract → FFDState → Type where
  SendIB : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (ibHeader h) (just (ibBody b))) FFDAbstract.SendRes (record s { outIBs = record {header = h; body = b} ∷ outIBs s})
  SendEB : ∀ {s eb} → SimpleFFD s (FFDAbstract.Send (ebHeader eb) nothing) FFDAbstract.SendRes (record s { outEBs = eb ∷ outEBs s})
  SendVS : ∀ {s vs} → SimpleFFD s (FFDAbstract.Send (vHeader vs) nothing) FFDAbstract.SendRes (record s { outVTs = vs ∷ outVTs s})

  BadSendIB : ∀ {s h} → SimpleFFD s (FFDAbstract.Send (ibHeader h) nothing) FFDAbstract.SendRes s
  BadSendEB : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (ebHeader h) (just b)) FFDAbstract.SendRes s
  BadSendVS : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (vHeader h) (just b)) FFDAbstract.SendRes s

  Fetch : ∀ {s} → SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes (flushIns s)) (record s { inIBs = [] ; inEBs = [] ; inVTs = [] })

send-total : ∀ {s h b} → ∃[ s' ] (SimpleFFD s (FFDAbstract.Send h b) FFDAbstract.SendRes s')
send-total {s} {ibHeader h} {just (ibBody b)} = record s { outIBs = record {header = h; body = b} ∷ outIBs s} , SendIB
send-total {s} {ebHeader eb} {nothing} = record s { outEBs = eb ∷ outEBs s} , SendEB
send-total {s} {vHeader vs} {nothing} = record s { outVTs = vs ∷ outVTs s} , SendVS

send-total {s} {ibHeader h} {nothing} = s , BadSendIB
send-total {s} {ebHeader eb} {just _} = s , BadSendEB
send-total {s} {vHeader vs} {just _} = s , BadSendVS

fetch-total : ∀ {s} → ∃[ x ] (∃[ s' ] (SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes x) s'))
fetch-total {s} = flushIns s , (record s { inIBs = [] ; inEBs = [] ; inVTs = [] } , Fetch)

send-complete : ∀ {s h b s'} → SimpleFFD s (FFDAbstract.Send h b) FFDAbstract.SendRes s' → s' ≡ proj₁ (send-total {s} {h} {b})
send-complete SendIB = refl
send-complete SendEB = refl
send-complete SendVS = refl
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
    { State = FFDState
    ; initFFDState = record { inIBs = []; inEBs = []; inVTs = []; outIBs = []; outEBs = []; outVTs = [] }
    ; _-⟦_/_⟧⇀_ = SimpleFFD
    ; Dec-_-⟦_/_⟧⇀_ = Dec-SimpleFFD
    ; FFD-Send-total = send-total
    }

open import Leios.Voting public

d-VotingAbstract : VotingAbstract (Fin 1 × EndorserBlock)
d-VotingAbstract =
  record
    { VotingState = ⊤
    ; initVotingState = tt
    ; isVoteCertified = λ _ _ → ⊤
    }

d-VotingAbstract-2 : VotingAbstract (Fin 2 × EndorserBlock)
d-VotingAbstract-2 =
  record
    { VotingState = ⊤
    ; initVotingState = tt
    ; isVoteCertified = λ _ _ → ⊤
    }

st : SpecStructure 1
st = record
      { a = d-Abstract
      ; Hashable-PreIBHeader = hhs
      ; Hashable-PreEndorserBlock = hpe
      ; id = SUT-id
      ; FFD' = d-FFDFunctionality
      ; vrf' = d-VRF
      ; sk-IB = tt
      ; sk-EB = tt
      ; sk-V = tt
      ; pk-IB = tt
      ; pk-EB = tt
      ; pk-V = tt
      ; B' = d-Base
      ; BF = d-BaseFunctionality
      ; initBaseState = tt
      ; K' = d-KeyRegistration
      ; KF = d-KeyRegistrationFunctionality
      ; va = d-VotingAbstract
      }

st-2 : SpecStructure 2
st-2 = record
      { a = d-Abstract
      ; Hashable-PreIBHeader = hhs
      ; Hashable-PreEndorserBlock = hpe
      ; id = SUT-id
      ; FFD' = d-FFDFunctionality
      ; vrf' = d-VRF
      ; sk-IB = tt
      ; sk-EB = tt
      ; sk-V = tt
      ; pk-IB = tt
      ; pk-EB = tt
      ; pk-V = tt
      ; B' = d-Base
      ; BF = d-BaseFunctionality
      ; initBaseState = tt
      ; K' = d-KeyRegistration
      ; KF = d-KeyRegistrationFunctionality
      ; va = d-VotingAbstract-2
      }

open import Leios.Short st public

completeFin : ∀ (n : ℕ) → ℙ (Fin n)
completeFin zero = ∅
completeFin (ℕ.suc n) = singleton (F.fromℕ n) ∪ mapˢ F.inject₁ (completeFin n)

m≤n∧n≤m⇒m≡n : ∀ {n m : ℕ} → n N.≤ m → m N.≤ n → m ≡ n
m≤n∧n≤m⇒m≡n z≤n z≤n = refl
m≤n∧n≤m⇒m≡n (s≤s n≤m) (s≤s m≤n) = cong N.suc (m≤n∧n≤m⇒m≡n n≤m m≤n)

toℕ-fromℕ : ∀ {n} {a : Fin (N.suc n)} → toℕ a ≡ n → a ≡ F.fromℕ n
toℕ-fromℕ {zero} {fzero} x = refl
toℕ-fromℕ {N.suc n} {fsuc a} x = cong fsuc (toℕ-fromℕ {n} {a} (N.suc-injective x))

maximalFin : ∀ (n : ℕ) → isMaximal (completeFin n)
maximalFin (ℕ.suc n) {a} with toℕ a N.<? n
... | yes p =
  let n≢toℕ = ≢-sym (N.<⇒≢ p)
      fn = F.lower₁ a n≢toℕ
      fn≡a = F.inject₁-lower₁ a n≢toℕ
  in (to ∈-∪) (inj₂ ((to ∈-map) (fn , (sym fn≡a , maximalFin n))))
... | no ¬p with a F.≟ F.fromℕ n
... | yes q = (to ∈-∪) (inj₁ ((to ∈-singleton) q))
... | no ¬q =
  let n≢toℕ = N.≰⇒> ¬p
      a<sucn = F.toℕ<n a
  in ⊥-elim $ (¬q ∘ toℕ-fromℕ) (N.suc-injective (m≤n∧n≤m⇒m≡n n≢toℕ a<sucn))
{-
open import Class.Computational
open import Class.Computational22

open Computational22
open BaseAbstract
open FFDAbstract

open GenFFD.Header using (ibHeader; ebHeader; vHeader)
open GenFFD.Body using (ibBody)
open FFDState

instance
  Computational-B : Computational22 (BaseAbstract.Functionality._-⟦_/_⟧⇀_ d-BaseFunctionality) String
  Computational-B .computeProof s (INIT x) = success ((STAKE sd , tt) , tt)
  Computational-B .computeProof s (SUBMIT x) = success ((EMPTY , tt) , tt)
  Computational-B .computeProof s FTCH-LDG = success (((BASE-LDG []) , tt) , tt)
  Computational-B .completeness _ _ _ _ _ = {!!} -- TODO: Completeness proof

  Computational-FFD : Computational22 (FFDAbstract.Functionality._-⟦_/_⟧⇀_ d-FFDFunctionality) String
  Computational-FFD .computeProof s (Send (ibHeader h) (just (ibBody b))) = success ((SendRes , record s {outIBs = record {header = h; body = b} ∷ outIBs s}) , SendIB)
  Computational-FFD .computeProof s (Send (ebHeader h) nothing) = success ((SendRes , record s {outEBs = h ∷ outEBs s}) , SendEB)
  Computational-FFD .computeProof s (Send (vHeader h) nothing) = success ((SendRes , record s {outVTs = h ∷ outVTs s}) , SendVS)
  Computational-FFD .computeProof s Fetch = success ((FetchRes (flushIns s) , record s {inIBs = []; inEBs = []; inVTs = []}) , Fetch)

  Computational-FFD .computeProof _ _ = failure "FFD error"
  Computational-FFD .completeness _ _ _ _ _ = {!!} -- TODO:Completeness proof
-}

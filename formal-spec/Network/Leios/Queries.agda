{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id; _∘_)
import CategoricalCrypto as CC
open import CategoricalCrypto.Step
open CategoricalCrypto.Step.Raw using (inj₁-inj; inj₂-inj; inj₁≢inj₂)
import Blockchain.IsBlockchain as IsBC

open import Data.Maybe.Properties using (just-injective)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ; map-injective)
open import CategoricalCrypto.Ext using (queryCompute-answer)

-- The query interfaces of the base functionality as deployed, `spec`, and of
-- the deployed node, `Leios1`.
--
-- For `spec`: the base
-- layer's own queries, forwarded through the network adapter and the
-- reassociation.  The steps that answer a query are built with
-- `CategoricalCrypto.Step`; that every answer has the required shape, and
-- leaves the state alone, is proved by inverting the composite step with the
-- same library, down to the base functionality's own `correctness` and
-- `isPure`.
module Network.Leios.Queries
  (⋯ : SpecStructure) (let open SpecStructure ⋯)
  (params : Params) (let open Params params)
  (k : ℕ)
  (HashCorrectB : RankingBlock → Maybe EndorserBlock → Type)
  (HashCorrect-irrel : ∀ rb eb → Irrelevant (HashCorrectB rb eb))
  (hash-unique : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
    → HashCorrectB rb eb₁ → HashCorrectB rb eb₂ → eb₁ ≡ eb₂)
  (ebOf : RankingBlock → Maybe EndorserBlock)
  (ebOf-correct : ∀ rb → HashCorrectB rb (ebOf rb))
  (forEB     : Vote → EBRef)
  (mkCert    : EBRef → EBCert)
  (mkCert-hash : ∀ r → getEBHash (mkCert r) ≡ r)
  (threshold : ℕ)
  (voter     : Vote → Fin numberOfParties)
  (Valid     : Vote → Type) ⦃ Valid? : Valid ⁇¹ ⦄
    where

open import Network.Leios ⋯ params k HashCorrectB HashCorrect-irrel hash-unique ebOf ebOf-correct
  forEB mkCert mkCert-hash threshold voter Valid ⦃ Valid? ⦄
open import Leios.Linear ⋯ params
open import Leios.NetworkShim ⋯ params
open Types params hiding (Network)
open BaseAbstract B' using (BaseIO; BaseAdv; BaseNetwork; BaseIOF)
open IsBC using (BlockChainInfo; bciQueryType)
open IsBC.BlockChainInfo

import Network.DelayedDiffuse numberOfParties Message k as DD

private module BC = IsConstrained B.isConstrained

private
  -- The layers between the base functionality's IO channel and `spec`'s:
  -- `spec = spec-rewire ∘ Y`, `Y = (Inner ⊗₁ id) ∘ (NetTranslate ⊗₁ id)`,
  -- the identities passing voting by.
  Inner : Machine (Network ⊗₀ BaseNetwork) (Network ⊗₀ (BaseIO ⊗₀ BaseAdv))
  Inner = CC.id ⊗₁ B.m

  L : Machine ((Network ⊗₀ BaseNetwork) ⊗₀ VotingC) ((Network ⊗₀ (BaseIO ⊗₀ BaseAdv)) ⊗₀ VotingC)
  L = Inner ⊗₁ CC.id

  NT : Machine (DD.M ⊗₀ VotingC) ((Network ⊗₀ BaseNetwork) ⊗₀ VotingC)
  NT = NetTranslate ⊗₁ CC.id

  Y : Machine (DD.M ⊗₀ VotingC) ((Network ⊗₀ (BaseIO ⊗₀ BaseAdv)) ⊗₀ VotingC)
  Y = L CC.∘ NT

  module TI = Tensor′ (CC.id {Network}) B.m
  module TL = Tensor′ Inner (CC.id {VotingC})
  module KI = Compose L NT
  module KS = Compose spec-rewire Y

  -- A base request `x`, and an answer `y`, at each layer.
  q₁ : BaseIOF Out → Channel.outType (BaseIO ⊗₀ BaseAdv)
  q₁ x = ϵ ⊗R ↑ₒ x
  q₂ : BaseIOF Out → Channel.outType (Network ⊗₀ (BaseIO ⊗₀ BaseAdv))
  q₂ x = L⊗ ϵ ↑ₒ q₁ x
  q₂' : BaseIOF Out → Channel.outType ((Network ⊗₀ (BaseIO ⊗₀ BaseAdv)) ⊗₀ VotingC)
  q₂' x = ϵ ⊗R ↑ₒ q₂ x
  q₃ : BaseIOF Out → Channel.outType (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv)
  q₃ x = ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ x

  a₁ : BaseIOF In → Channel.inType (BaseIO ⊗₀ BaseAdv)
  a₁ y = ϵ ⊗R ↑ᵢ y
  a₂ : BaseIOF In → Channel.inType (Network ⊗₀ (BaseIO ⊗₀ BaseAdv))
  a₂ y = L⊗ ϵ ↑ᵢ a₁ y
  a₂' : BaseIOF In → Channel.inType ((Network ⊗₀ (BaseIO ⊗₀ BaseAdv)) ⊗₀ VotingC)
  a₂' y = ϵ ⊗R ↑ᵢ a₂ y
  a₃ : BaseIOF In → Channel.inType (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv)
  a₃ y = ((L⊗ ϵ) ⊗R) ⊗R ↑ᵢ y

  -- How the rewiring routes them.
  opaque
    unfolding _⊗₀_

    assocₒ-IO : ∀ x → app spec-rewireₒ (q₃ x) ≡ q₂' x
    assocₒ-IO x = refl

    assocᵢ-IO : ∀ y → app spec-rewireᵢ (a₂' y) ≡ a₃ y
    assocᵢ-IO y = refl

-- The queries of `spec`: the base layer's, on `spec`'s codomain.
queryIₛ : BlockChainInfo RankingBlock → Channel.inType ((DD.M ⊗₀ VotingC) ⊗ᵀ (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv))
queryIₛ q = L⊗ ϵ ᵗ¹ ↑ₒ q₃ (B.qI q)

queryOₛ : ∀ {q} → bciQueryType {Block = RankingBlock} q → Channel.outType ((DD.M ⊗₀ VotingC) ⊗ᵀ (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv))
queryOₛ r = L⊗ ϵ ᵗ¹ ↑ᵢ a₃ (B.qO r)

private
  -- The base functionality's step on a query, in the library's spelling.
  B-step : ∀ {q sB sB' r}
    → Machine.stepRel B.m sB (B.queryI q) (just (B.queryO {q} r)) sB'
    → Step B.m sB (L⊗ ϵ ᵗ¹ ↑ₒ q₁ (B.qI q)) (just (L⊗ ϵ ᵗ¹ ↑ᵢ a₁ (B.qO r))) sB'
  B-step {q} {r = r} st =
    step-subst (trans (B.queryI-IO q) (nest-ᵗ¹ₒ (ϵ ⊗R) (B.qI q)))
               (cong just (trans (B.queryO-IO r) (nest-ᵗ¹ᵢ (ϵ ⊗R) (B.qO r))))
               (toStep st)

------------------------------------------------------------------------
-- Completeness: the base layer's answer travels back out.

  -- The chain of steps, from the base layer's.
  spec-step : ∀ {q sNT sB sB' r}
    → Machine.stepRel B.m sB (B.queryI q) (just (B.queryO {q} r)) sB'
    → Step spec (((sNT , tt) , ((tt , sB) , tt)) , tt) (queryIₛ q) (just (queryOₛ r)) (((sNT , tt) , ((tt , sB') , tt)) , tt)
  spec-step {q} {sNT} {sB} {sB'} {r} stB = stS
   where
    x = B.qI q
    y = B.qO {q} r

    stB₁ : Step B.m sB (L⊗ ϵ ᵗ¹ ↑ₒ q₁ x) (just (L⊗ ϵ ᵗ¹ ↑ᵢ a₁ y)) sB'
    stB₁ = B-step stB

    stI : Step Inner (tt , sB) (L⊗ ϵ ᵗ¹ ↑ₒ q₂ x) (just (L⊗ ϵ ᵗ¹ ↑ᵢ a₂ y)) (tt , sB')
    stI = step-subst (nest-ᵗ¹ₒ (L⊗ ϵ) (q₁ x)) (cong just (nest-ᵗ¹ᵢ (L⊗ ϵ) (a₁ y))) (TI.⊗₁-cod₂-cod stB₁)

    stL : Step L ((tt , sB) , tt) (L⊗ ϵ ᵗ¹ ↑ₒ q₂' x) (just (L⊗ ϵ ᵗ¹ ↑ᵢ a₂' y)) ((tt , sB') , tt)
    stL = step-subst (nest-ᵗ¹ₒ (ϵ ⊗R) (q₂ x)) (cong just (nest-ᵗ¹ᵢ (ϵ ⊗R) (a₂ y))) (TL.⊗₁-cod₁-cod stI)

    stY : Step Y ((sNT , tt) , ((tt , sB) , tt)) (L⊗ ϵ ᵗ¹ ↑ₒ q₂' x) (just (L⊗ ϵ ᵗ¹ ↑ᵢ a₂' y)) ((sNT , tt) , ((tt , sB') , tt))
    stY = KI.∘-cod-cod stL

    stS : Step spec (((sNT , tt) , ((tt , sB) , tt)) , tt) (queryIₛ q) (just (queryOₛ r)) (((sNT , tt) , ((tt , sB') , tt)) , tt)
    stS = KS.∘-cod-mid (fwd-cod spec-rewireᵢ spec-rewireₒ (q₃ x))
            (KS.mid₂-subst (sym (assocₒ-IO x)) refl
              (KS.mid₂-mid stY
                (KS.mid₁-subst refl (cong just (cong (L⊗ ϵ ᵗ¹ ↑ᵢ_) (assocᵢ-IO y)))
                  (KS.mid₁-cod (fwd-dom spec-rewireᵢ spec-rewireₒ (a₂' y))))))

spec-completeness : ∀ {q} {s : Machine.State spec}
  → ∃ λ response' → ∃ λ s' → Machine.stepRel spec s (queryIₛ q) (just response') s'
spec-completeness {q} {((sNT , tt) , ((tt , sB) , tt)) , tt} =
  let resp' , sB' , stB = BC.completeness {q} {sB}
      r , eq = BC.correctness stB
  in _ , _ , fromStep (spec-step (subst (λ o → Machine.stepRel B.m sB (B.queryI q) o sB') eq stB))

------------------------------------------------------------------------
-- Correctness and purity: every step of `spec` on a query is the chain
-- above, so its answer is the base layer's and its state is unchanged.

private
  -- Peeling the layers off a query step, innermost first.
  B-inv : ∀ {q sB o sB'}
    → Step B.m sB (L⊗ ϵ ᵗ¹ ↑ₒ q₁ (B.qI q)) o sB'
    → ∃ λ r → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ a₁ (B.qO {q} r))) × (sB ≡ sB')
  B-inv {q} st =
    let stB = fromStep (step-subst (sym (trans (B.queryI-IO q) (nest-ᵗ¹ₒ (ϵ ⊗R) (B.qI q)))) refl st)
        r , eq = BC.correctness stB
    in r , trans eq (cong just (trans (B.queryO-IO r) (nest-ᵗ¹ᵢ (ϵ ⊗R) (B.qO r)))) , B.isPure q stB

  Inner-inv : ∀ {q s o s'}
    → Step Inner s (L⊗ ϵ ᵗ¹ ↑ₒ q₂ (B.qI q)) o s'
    → ∃ λ r → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ a₂ (B.qO {q} r))) × (s ≡ s')
  Inner-inv {q} {sI , sB} st =
    case TI.⊗₁-cod₂-view (step-subst (sym (nest-ᵗ¹ₒ (L⊗ ϵ) (q₁ (B.qI q)))) refl st) of λ where
      (sB' , seq , inj₁ (oeq , stB)) → case proj₁ (proj₂ (B-inv {q} stB)) of λ ()
      (sB' , seq , inj₂ (inj₁ (c' , oeq , stB))) → outᵈ≢outᶜ (just-injective (proj₁ (proj₂ (B-inv {q} stB))))
      (sB' , seq , inj₂ (inj₂ (d' , oeq , stB))) →
        case B-inv {q} stB of λ where
          (r , eq , pure) →
            r , trans oeq (cong just (trans (cong (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ_) (outᶜ-inj (just-injective eq))) (nest-ᵗ¹ᵢ (L⊗ ϵ) (a₁ (B.qO r)))))
              , trans (cong (sI ,_) pure) (sym seq)

  L-inv : ∀ {q s o s'}
    → Step L s (L⊗ ϵ ᵗ¹ ↑ₒ q₂' (B.qI q)) o s'
    → ∃ λ r → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ a₂' (B.qO {q} r))) × (s ≡ s')
  L-inv {q} {sI , sV} st =
    case TL.⊗₁-cod₁-view (step-subst (sym (nest-ᵗ¹ₒ (ϵ ⊗R) (q₂ (B.qI q)))) refl st) of λ where
      (sI' , seq , inj₁ (oeq , stI)) → case proj₁ (proj₂ (Inner-inv {q} stI)) of λ ()
      (sI' , seq , inj₂ (inj₁ (a' , oeq , stI))) → outᵈ≢outᶜ (just-injective (proj₁ (proj₂ (Inner-inv {q} stI))))
      (sI' , seq , inj₂ (inj₂ (b' , oeq , stI))) →
        case Inner-inv {q} stI of λ where
          (r , eq , pure) →
            r , trans oeq (cong just (trans (cong (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ_) (outᶜ-inj (just-injective eq))) (nest-ᵗ¹ᵢ (ϵ ⊗R) (a₂ (B.qO r)))))
              , trans (cong (_, sV) pure) (sym seq)

  Y-inv : ∀ {q s o s'}
    → Step Y s (L⊗ ϵ ᵗ¹ ↑ₒ q₂' (B.qI q)) o s'
    → ∃ λ r → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ a₂' (B.qO {q} r))) × (s ≡ s')
  Y-inv {q} {sNT , sL} st =
    case KI.∘-cod-view st of λ where
      (inj₁ (sL' , seq , oeq , stL)) → case proj₁ (proj₂ (L-inv {q} stL)) of λ ()
      (inj₂ (inj₁ (sL' , c' , seq , oeq , stL))) →
        case L-inv {q} stL of λ where
          (r , eq , pure) → r , trans oeq (cong (λ z → just (L⊗ ϵ ᵗ¹ ↑ᵢ z)) (outᶜ-inj (just-injective eq))) , trans (cong (sNT ,_) pure) (sym seq)
      (inj₂ (inj₂ (sL' , b , stL , _))) → outᵈ≢outᶜ (just-injective (proj₁ (proj₂ (L-inv {q} stL))))

  -- After `spec-rewire` has relayed the query inwards.
  after-fwd : ∀ {q sY sR o s'}
    → KS.Mid₂ (sY , sR) (q₂' (B.qI q)) o s'
    → ∃ λ r → (o ≡ just (queryOₛ {q} r)) × ((sY , sR) ≡ s')
  after-fwd {q} k =
    case KS.mid₂-view k of λ where
      (inj₁ (sY' , seq , oeq , stY)) → case proj₁ (proj₂ (Y-inv {q} stY)) of λ ()
      (inj₂ (inj₁ (sY' , a' , seq , oeq , stY))) → outᵈ≢outᶜ (just-injective (proj₁ (proj₂ (Y-inv {q} stY))))
      (inj₂ (inj₂ (sY' , b' , stY , k₁))) →
        case Y-inv {q} stY of λ where
          (r , eq , pure) →
            case KS.mid₁-view (KS.mid₁-subst (outᶜ-inj (just-injective eq)) refl k₁) of λ where
              (inj₁ (_ , _ , _ , st₃)) → case fwd-dom-inv spec-rewireᵢ spec-rewireₒ st₃ of λ ()
              (inj₂ (inj₁ (sR' , c' , seq' , oeq , st₃))) →
                r , trans oeq (cong (λ z → just (L⊗ ϵ ᵗ¹ ↑ᵢ z))
                                (trans (outᶜ-inj (just-injective (fwd-dom-inv spec-rewireᵢ spec-rewireₒ st₃)))
                                       (assocᵢ-IO (B.qO r))))
                  , trans (cong (_, sR') pure) (sym seq')
              (inj₂ (inj₂ (_ , _ , st₃ , _))) →
                outᵈ≢outᶜ (just-injective (fwd-dom-inv spec-rewireᵢ spec-rewireₒ st₃))

spec-query-inv : ∀ {q s o s'}
  → Step spec s (queryIₛ q) o s'
  → ∃ λ r → (o ≡ just (queryOₛ {q} r)) × (s ≡ s')
spec-query-inv {q} {sY , sR} st =
  case KS.∘-cod-view st of λ where
    (inj₁ (_ , _ , _ , st₁)) → case fwd-cod-inv spec-rewireᵢ spec-rewireₒ st₁ of λ ()
    (inj₂ (inj₁ (_ , c' , _ , _ , st₁))) →
      outᵈ≢outᶜ (sym (just-injective (fwd-cod-inv spec-rewireᵢ spec-rewireₒ st₁)))
    (inj₂ (inj₂ (sR' , b , st₁ , k))) →
      after-fwd {q} (KS.mid₂-subst
        (trans (outᵈ-inj (just-injective (fwd-cod-inv spec-rewireᵢ spec-rewireₒ st₁))) (assocₒ-IO (B.qI q)))
        refl k)

------------------------------------------------------------------------
-- The interface.

spec-isConstrained : IsConstrained spec (bciQueryType {Block = RankingBlock})
spec-isConstrained = record
  { queryI       = queryIₛ
  ; queryO       = queryOₛ
  ; correctness  = corr
  ; completeness = spec-completeness
  }
  where
    -- The output is passed explicitly: `toStep` on a bare composite step
    -- would leave it under the composite's rerouting, unsolved.
    corr : ∀ {q s o s'} → Machine.stepRel spec s (queryIₛ q) o s' → ∃ λ r → o ≡ just (queryOₛ {q} r)
    corr {o = o} st = let r , eq , _ = spec-query-inv (toStep {M = spec} {o = o} st) in r , eq

spec-isPure : IsPure spec-isConstrained
spec-isPure q {response' = o} st = proj₂ (proj₂ (spec-query-inv (toStep {M = spec} {o = o} st)))

-- `spec` is a blockchain in the deployment's sense, given a reading of the
-- base layer's parties as Leios parties.
IsBlockchain-spec : (base-party : Fin B.n → Participant) → IsBC.IsBlockchain Participant RankingBlock spec
IsBlockchain-spec base-party = record
  { isConstrained = spec-isConstrained
  ; isPure        = spec-isPure
  ; producer      = λ b → base-party (B.producer b)
  ; slotOf        = B.slotOf
  }

------------------------------------------------------------------------
-- The deployed node.  Its queries are the base layer's, asked on the query
-- port `QIO` and answered with Leios blocks; the multiplexer forwards them to
-- the base spec and the answer back.

-- Queries and answers over Leios blocks are the base layer's over ranking
-- blocks.
-- The shared re-tagging of `Blockchain.IsBlockchain`, at these block types.
baseQ : BlockChainInfo LeiosBlock → BlockChainInfo RankingBlock
baseQ = IsBC.baseQ

mapBase : ∀ q → bciQueryType {Block = LeiosBlock} q → bciQueryType (baseQ q)
mapBase = IsBC.mapAnswer LeiosBlock.rb

mapExt : ∀ q → bciQueryType (baseQ q) → bciQueryType {Block = LeiosBlock} q
mapExt Chain = map toLeiosBlock
mapExt Slot  = λ n → n

mapBase∘mapExt : ∀ q r → mapBase q (mapExt q r) ≡ r
mapBase∘mapExt Chain []       = refl
mapBase∘mapExt Chain (b ∷ bs) = cong (b ∷_) (mapBase∘mapExt Chain bs)
mapBase∘mapExt Slot  n        = refl

private
  -- The layers of `Leios1`, outermost first: `Leios1 = ∘ᴷ-fwd ∘ X`,
  -- `X = (ext-spec ⊗₁ id) ∘ spec`, `ext-spec = regroup-ext ∘ R3`,
  -- `R3 = node-layer ∘ R2`, `R2 = mux-shuffle ∘ mux-layer`,
  -- `mux-layer = (Shim ⊗₁ Mux) ⊗₁ id`.
  X : Machine (DD.M ⊗₀ VotingC) ((ExtIO ⊗₀ Adv) ⊗₀ BaseAdv)
  X = (ext-spec ⊗₁ CC.id) CC.∘ spec

  R2 : Machine ((Network ⊗₀ BaseIO) ⊗₀ VotingC) (((FFD ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ QIO)
  R2 = mux-shuffle CC.∘ mux-layer

  R3 : Machine ((Network ⊗₀ BaseIO) ⊗₀ VotingC) ((IO ⊗₀ Adv) ⊗₀ QIO)
  R3 = node-layer CC.∘ R2

  module KL = Compose (∘ᴷ-fwd {C = ExtIO} {E₁ = BaseAdv} {E₂ = Adv}) X
  module KE = Compose (ext-spec ⊗₁ CC.id {BaseAdv}) spec
  module TE = Tensor′ ext-spec (CC.id {BaseAdv})
  module K4 = Compose regroup-ext R3
  module K3 = Compose node-layer R2
  module K2 = Compose mux-shuffle mux-layer
  module TN = Tensor′ LinearLeios (CC.id {QIO})
  module TQV = Tensor′ (Shim ⊗₁ Mux) (CC.id {VotingC})
  module TQ = Tensor′ Shim Mux

  -- The state of the extension layer, given the shim's, the multiplexer's
  -- stack and the node's.
  E : ShimState → Mux.State → LeiosState → Machine.State ext-spec
  E sSh rs sLL = (((((sSh , rs) , tt) , tt) , (sLL , tt)) , tt)

  -- A request `z` on the query port, at each layer on its way down to the
  -- base spec's IO channel (`d₁`); an answer `w` on its way back up.
  e₀ : QryT Out → Channel.outType (ExtIO ⊗₀ (BaseAdv ⊗₀ Adv))
  e₀ z = (L⊗ ϵ) ⊗R ↑ₒ z
  e₃ : QryT Out → Channel.outType ExtIO
  e₃ z = L⊗ ϵ ↑ₒ z
  e₂ : QryT Out → Channel.outType (ExtIO ⊗₀ Adv)
  e₂ z = ϵ ⊗R ↑ₒ e₃ z
  e₁ : QryT Out → Channel.outType ((ExtIO ⊗₀ Adv) ⊗₀ BaseAdv)
  e₁ z = ϵ ⊗R ↑ₒ e₂ z
  e₅ : QryT Out → Channel.outType ((IO ⊗₀ Adv) ⊗₀ QIO)
  e₅ z = L⊗ ϵ ↑ₒ z
  e₆ : QryT Out → Channel.outType (((FFD ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ QIO)
  e₆ z = L⊗ ϵ ↑ₒ z
  e₈ : QryT Out → Channel.outType (FFD ⊗₀ (BaseIO ⊗₀ QIO))
  e₈ z = L⊗ ϵ ↑ₒ (L⊗ ϵ ↑ₒ z)
  e₇ : QryT Out → Channel.outType ((FFD ⊗₀ (BaseIO ⊗₀ QIO)) ⊗₀ VotingC)
  e₇ z = ϵ ⊗R ↑ₒ e₈ z
  d₀ : BaseIOF Out → Channel.outType (Network ⊗₀ BaseIO)
  d₀ x = L⊗ ϵ ↑ₒ x
  d₁ : BaseIOF Out → Channel.outType ((Network ⊗₀ BaseIO) ⊗₀ VotingC)
  d₁ x = ϵ ⊗R ↑ₒ d₀ x

  d₀' : BaseIOF In → Channel.inType (Network ⊗₀ BaseIO)
  d₀' y = L⊗ ϵ ↑ᵢ y
  d₂ : BaseIOF In → Channel.inType ((Network ⊗₀ BaseIO) ⊗₀ VotingC)
  d₂ y = ϵ ⊗R ↑ᵢ d₀' y
  f₈ : QryT In → Channel.inType (FFD ⊗₀ (BaseIO ⊗₀ QIO))
  f₈ w = L⊗ ϵ ↑ᵢ (L⊗ ϵ ↑ᵢ w)
  f₁ : QryT In → Channel.inType ((FFD ⊗₀ (BaseIO ⊗₀ QIO)) ⊗₀ VotingC)
  f₁ w = ϵ ⊗R ↑ᵢ f₈ w
  f₂ : QryT In → Channel.inType (((FFD ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ QIO)
  f₂ w = L⊗ ϵ ↑ᵢ w
  f₃ : QryT In → Channel.inType ((IO ⊗₀ Adv) ⊗₀ QIO)
  f₃ w = L⊗ ϵ ↑ᵢ w
  f₄ : QryT In → Channel.inType (ExtIO ⊗₀ Adv)
  f₄ w = ϵ ⊗R ↑ᵢ (L⊗ ϵ ↑ᵢ w)
  f₅ : QryT In → Channel.inType ((ExtIO ⊗₀ Adv) ⊗₀ BaseAdv)
  f₅ w = ϵ ⊗R ↑ᵢ f₄ w
  f₀ : QryT In → Channel.inType (ExtIO ⊗₀ (BaseAdv ⊗₀ Adv))
  f₀ w = (L⊗ ϵ) ⊗R ↑ᵢ w

  -- How the three forwarders route them.
  opaque
    unfolding _⊗₀_

    ∘ᴷ-fwdₒ-QIO : ∀ z → app (∘ᴷ-fwdₒ {C = ExtIO} {E₁ = BaseAdv} {E₂ = Adv}) (e₀ z) ≡ e₁ z
    ∘ᴷ-fwdₒ-QIO z = refl

    ∘ᴷ-fwdᵢ-QIO : ∀ w → app (∘ᴷ-fwdᵢ {C = ExtIO} {E₁ = BaseAdv} {E₂ = Adv}) (f₅ w) ≡ f₀ w
    ∘ᴷ-fwdᵢ-QIO w = refl

    regroup-extₒ-QIO : ∀ z → app regroup-extₒ (e₂ z) ≡ e₅ z
    regroup-extₒ-QIO z = refl

    regroup-extᵢ-QIO : ∀ w → app regroup-extᵢ (f₃ w) ≡ f₄ w
    regroup-extᵢ-QIO w = refl

    mux-shuffleₒ-QIO : ∀ z → app mux-shuffleₒ (e₆ z) ≡ e₇ z
    mux-shuffleₒ-QIO z = refl

    mux-shuffleᵢ-QIO : ∀ w → app mux-shuffleᵢ (f₁ w) ≡ f₂ w
    mux-shuffleᵢ-QIO w = refl

    -- The base spec's IO messages, as the extension layer's domain and as
    -- `spec`'s codomain.
    d₁-q₃ : ∀ x → ϵ ⊗R ↑ₒ d₁ x ≡ q₃ x
    d₁-q₃ x = refl

    d₂-a₃ : ∀ y → ϵ ⊗R ↑ᵢ d₂ y ≡ a₃ y
    d₂-a₃ y = refl

-- The queries of the deployed node.
queryIₗ : BlockChainInfo LeiosBlock → Channel.inType ((DD.M ⊗₀ VotingC) ⊗ᵀ (ExtIO ⊗₀ (BaseAdv ⊗₀ Adv)))
queryIₗ q = L⊗ ϵ ᵗ¹ ↑ₒ e₀ (ask (B.qI (baseQ q)))

queryOₗ : ∀ {q} → bciQueryType {Block = LeiosBlock} q → Channel.outType ((DD.M ⊗₀ VotingC) ⊗ᵀ (ExtIO ⊗₀ (BaseAdv ⊗₀ Adv)))
queryOₗ {q} r = L⊗ ϵ ᵗ¹ ↑ᵢ f₀ (ans (B.qO (mapBase q r)))

private
  -- The base spec answers a query from any state, and stays put.
  spec-answers : ∀ q sS → ∃ λ r → Step spec sS (queryIₛ q) (just (queryOₛ r)) sS
  spec-answers q sS =
    let resp' , sS' , st = spec-completeness {q} {sS}
        stS = toStep {M = spec} {o = just resp'} st
        r , eq , seq = spec-query-inv {q} stS
    in r , step-subst refl eq (subst (λ z → Step spec sS (queryIₛ q) (just resp') z) (sym seq) stS)

  -- The extension layer relays a query on its port down to its domain, the
  -- base spec's IO channel, pushing `query` on the multiplexer's stack …
  ext-request : ∀ {sSh rs sLL} x
    → Step ext-spec (E sSh rs sLL) (L⊗ ϵ ᵗ¹ ↑ₒ e₂ (ask x)) (just (ϵ ⊗R ↑ₒ d₁ x)) (E sSh (Mux.query ∷ rs) sLL)
  ext-request {sSh} {rs} {sLL} x =
    K4.∘-cod-mid (fwd-cod regroup-extᵢ regroup-extₒ (e₂ z))
      (K4.mid₂-subst (sym (regroup-extₒ-QIO z)) refl (K4.mid₂-dom r3))
    where
      z = ask x

      mx : Step Mux rs (L⊗ ϵ ᵗ¹ ↑ₒ (L⊗ ϵ ↑ₒ z)) (just (ϵ ⊗R ↑ₒ x)) (Mux.query ∷ rs)
      mx = step-subst (nest-ᵗ¹ₒ (L⊗ ϵ) z) refl (toStep (Mux.Ask {rs = rs} {x = x}))

      ml₀ : Step (Shim ⊗₁ Mux) (sSh , rs) (L⊗ ϵ ᵗ¹ ↑ₒ e₈ z) (just (ϵ ⊗R ↑ₒ d₀ x)) (sSh , Mux.query ∷ rs)
      ml₀ = step-subst (nest-ᵗ¹ₒ (L⊗ ϵ) (L⊗ ϵ ↑ₒ z)) (cong just (nest-⊗Rₒ (L⊗ ϵ) x)) (TQ.⊗₁-cod₂-dom mx)

      ml : Step mux-layer ((sSh , rs) , tt) (L⊗ ϵ ᵗ¹ ↑ₒ e₇ z) (just (ϵ ⊗R ↑ₒ d₁ x)) ((sSh , Mux.query ∷ rs) , tt)
      ml = step-subst (nest-ᵗ¹ₒ (ϵ ⊗R) (e₈ z)) (cong just (nest-⊗Rₒ (ϵ ⊗R) (d₀ x))) (TQV.⊗₁-cod₁-dom ml₀)

      r2 : Step R2 (((sSh , rs) , tt) , tt) (L⊗ ϵ ᵗ¹ ↑ₒ e₆ z) (just (ϵ ⊗R ↑ₒ d₁ x)) (((sSh , Mux.query ∷ rs) , tt) , tt)
      r2 = K2.∘-cod-mid (fwd-cod mux-shuffleᵢ mux-shuffleₒ (e₆ z))
             (K2.mid₂-subst (sym (mux-shuffleₒ-QIO z)) refl (K2.mid₂-dom ml))

      nl : Step node-layer (sLL , tt) (L⊗ ϵ ᵗ¹ ↑ₒ e₅ z) (just (ϵ ⊗R ↑ₒ e₆ z)) (sLL , tt)
      nl = step-subst (nest-ᵗ¹ₒ (L⊗ ϵ) z) (cong just (nest-⊗Rₒ (L⊗ ϵ) z)) (TN.⊗₁-cod₂-dom (id-cod z))

      r3 : Step R3 ((((sSh , rs) , tt) , tt) , (sLL , tt)) (L⊗ ϵ ᵗ¹ ↑ₒ e₅ z) (just (ϵ ⊗R ↑ₒ d₁ x)) ((((sSh , Mux.query ∷ rs) , tt) , tt) , (sLL , tt))
      r3 = K3.∘-cod-mid nl (K3.mid₂-dom r2)

  -- … and relays the answer arriving on its domain back up to the port,
  -- popping it.
  ext-answer : ∀ {sSh rs sLL} y
    → Step ext-spec (E sSh (Mux.query ∷ rs) sLL) (ϵ ⊗R ↑ᵢ d₂ y) (just (L⊗ ϵ ᵗ¹ ↑ᵢ f₄ (ans y))) (E sSh rs sLL)
  ext-answer {sSh} {rs} {sLL} y =
    K4.∘-dom-mid r3
      (K4.mid₁-subst refl (cong just (cong (L⊗ ϵ ᵗ¹ ↑ᵢ_) (regroup-extᵢ-QIO w)))
        (K4.mid₁-cod (fwd-dom regroup-extᵢ regroup-extₒ (f₃ w))))
    where
      w = ans y

      mx : Step Mux (Mux.query ∷ rs) (ϵ ⊗R ↑ᵢ y) (just (L⊗ ϵ ᵗ¹ ↑ᵢ (L⊗ ϵ ↑ᵢ w))) rs
      mx = step-subst refl (cong just (nest-ᵗ¹ᵢ (L⊗ ϵ) w)) (toStep (Mux.Tell {rs = rs} {y = y}))

      ml₀ : Step (Shim ⊗₁ Mux) (sSh , Mux.query ∷ rs) (ϵ ⊗R ↑ᵢ d₀' y) (just (L⊗ ϵ ᵗ¹ ↑ᵢ f₈ w)) (sSh , rs)
      ml₀ = step-subst (nest-⊗Rᵢ (L⊗ ϵ) y) (cong just (nest-ᵗ¹ᵢ (L⊗ ϵ) (L⊗ ϵ ↑ᵢ w))) (TQ.⊗₁-dom₂-cod mx)

      ml : Step mux-layer ((sSh , Mux.query ∷ rs) , tt) (ϵ ⊗R ↑ᵢ d₂ y) (just (L⊗ ϵ ᵗ¹ ↑ᵢ f₁ w)) ((sSh , rs) , tt)
      ml = step-subst (nest-⊗Rᵢ (ϵ ⊗R) (d₀' y)) (cong just (nest-ᵗ¹ᵢ (ϵ ⊗R) (f₈ w))) (TQV.⊗₁-dom₁-cod ml₀)

      r2 : Step R2 (((sSh , Mux.query ∷ rs) , tt) , tt) (ϵ ⊗R ↑ᵢ d₂ y) (just (L⊗ ϵ ᵗ¹ ↑ᵢ f₂ w)) (((sSh , rs) , tt) , tt)
      r2 = K2.∘-dom-mid ml
             (K2.mid₁-subst refl (cong just (cong (L⊗ ϵ ᵗ¹ ↑ᵢ_) (mux-shuffleᵢ-QIO w)))
               (K2.mid₁-cod (fwd-dom mux-shuffleᵢ mux-shuffleₒ (f₁ w))))

      nl : Step node-layer (sLL , tt) (ϵ ⊗R ↑ᵢ f₂ w) (just (L⊗ ϵ ᵗ¹ ↑ᵢ f₃ w)) (sLL , tt)
      nl = step-subst (nest-⊗Rᵢ (L⊗ ϵ) w) (cong just (nest-ᵗ¹ᵢ (L⊗ ϵ) w)) (TN.⊗₁-dom₂-cod (id-dom w))

      r3 : Step R3 ((((sSh , Mux.query ∷ rs) , tt) , tt) , (sLL , tt)) (ϵ ⊗R ↑ᵢ d₂ y) (just (L⊗ ϵ ᵗ¹ ↑ᵢ f₃ w)) ((((sSh , rs) , tt) , tt) , (sLL , tt))
      r3 = K3.∘-dom-mid r2 (K3.mid₁-cod nl)

------------------------------------------------------------------------
-- Completeness for the deployed node.

private
  -- The chain of steps, from the base spec's.
  Leios1-step : ∀ {q sS sSh rs sLL} r
    → Step spec sS (queryIₛ (baseQ q)) (just (queryOₛ r)) sS
    → Step Leios1 ((sS , (E sSh rs sLL , tt)) , tt) (queryIₗ q) (just (queryOₗ (mapExt q r))) ((sS , (E sSh rs sLL , tt)) , tt)
  Leios1-step {q} {sS} {sSh} {rs} {sLL} r stS = stL
   where
    x = B.qI (baseQ q)
    y = B.qO r
    z = ask x
    w = ans y

    te-req : Step (ext-spec ⊗₁ CC.id) (E sSh rs sLL , tt) (L⊗ ϵ ᵗ¹ ↑ₒ e₁ z) (just (ϵ ⊗R ↑ₒ (ϵ ⊗R ↑ₒ d₁ x))) (E sSh (Mux.query ∷ rs) sLL , tt)
    te-req = step-subst (nest-ᵗ¹ₒ (ϵ ⊗R) (e₂ z)) (cong just (nest-⊗Rₒ (ϵ ⊗R) (d₁ x))) (TE.⊗₁-cod₁-dom (ext-request x))

    te-ans : Step (ext-spec ⊗₁ CC.id) (E sSh (Mux.query ∷ rs) sLL , tt) (ϵ ⊗R ↑ᵢ a₃ y) (just (L⊗ ϵ ᵗ¹ ↑ᵢ f₅ w)) (E sSh rs sLL , tt)
    te-ans = step-subst (trans (nest-⊗Rᵢ (ϵ ⊗R) (d₂ y)) (cong (ϵ ⊗R ↑ᵢ_) (d₂-a₃ y)))
                        (cong just (nest-ᵗ¹ᵢ (ϵ ⊗R) (f₄ w)))
                        (TE.⊗₁-dom₁-cod (ext-answer y))

    stX : Step X (sS , (E sSh rs sLL , tt)) (L⊗ ϵ ᵗ¹ ↑ₒ e₁ z) (just (L⊗ ϵ ᵗ¹ ↑ᵢ f₅ w)) (sS , (E sSh rs sLL , tt))
    stX = KE.∘-cod-mid te-req
            (KE.mid₂-subst (d₁-q₃ x) refl
              (KE.mid₂-mid stS (KE.mid₁-cod te-ans)))

    stL : Step Leios1 ((sS , (E sSh rs sLL , tt)) , tt) (queryIₗ q) (just (queryOₗ (mapExt q r))) ((sS , (E sSh rs sLL , tt)) , tt)
    stL = step-subst refl (cong (λ v → just (L⊗ ϵ ᵗ¹ ↑ᵢ f₀ (ans (B.qO v)))) (sym (mapBase∘mapExt q r)))
            (KL.∘-cod-mid (fwd-cod ∘ᴷ-fwdᵢ ∘ᴷ-fwdₒ (e₀ z))
              (KL.mid₂-subst (sym (∘ᴷ-fwdₒ-QIO z)) refl
                (KL.mid₂-mid stX
                  (KL.mid₁-subst refl (cong just (cong (L⊗ ϵ ᵗ¹ ↑ᵢ_) (∘ᴷ-fwdᵢ-QIO w)))
                    (KL.mid₁-cod (fwd-dom ∘ᴷ-fwdᵢ ∘ᴷ-fwdₒ (f₅ w)))))))

Leios1-completeness : ∀ {q} {s : Machine.State Leios1}
  → ∃ λ response' → ∃ λ s' → Machine.stepRel Leios1 s (queryIₗ q) (just response') s'
Leios1-completeness {q} {(sS , ((((((sSh , rs) , tt) , tt) , (sLL , tt)) , tt) , tt)) , tt} =
  let r , stS = spec-answers (baseQ q) sS
  in _ , _ , fromStep (Leios1-step {q} r stS)

------------------------------------------------------------------------
-- Correctness and purity for the deployed node: every step on a query is
-- the chain above.  Inversion layer by layer, request half down and answer
-- half up, ending at the multiplexer's rules and `spec-query-inv`.

private
  ask-inj : ∀ {x x'} → ask x ≡ ask x' → x ≡ x'
  ask-inj refl = refl

  -- The multiplexer's steps, at general indices.
  mux-view : ∀ {rs i o rs'} → Machine.stepRel Mux rs i o rs'
    → (∃ λ x → (i ≡ L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ x) × (o ≡ just (ϵ ⊗R ↑ₒ x)) × (rs' ≡ Mux.pend x rs))
    ⊎ (∃ λ y → ∃ λ rs₀ → (rs ≡ Mux.node ∷ rs₀) × (i ≡ ϵ ⊗R ↑ᵢ y) × (o ≡ just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ y)) × (rs' ≡ rs₀))
    ⊎ (∃ λ x → (i ≡ L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ ask x) × (o ≡ just (ϵ ⊗R ↑ₒ x)) × (rs' ≡ Mux.query ∷ rs))
    ⊎ (∃ λ y → ∃ λ rs₀ → (rs ≡ Mux.query ∷ rs₀) × (i ≡ ϵ ⊗R ↑ᵢ y) × (o ≡ just (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ ans y)) × (rs' ≡ rs₀))
  mux-view Mux.Req  = inj₁ (_ , refl , refl , refl)
  mux-view Mux.Ans  = inj₂ (inj₁ (_ , _ , refl , refl , refl , refl))
  mux-view Mux.Ask  = inj₂ (inj₂ (inj₁ (_ , refl , refl , refl)))
  mux-view Mux.Tell = inj₂ (inj₂ (inj₂ (_ , _ , refl , refl , refl , refl)))

  -- The multiplexer's messages on a query, named outside the unfolding block
  -- so that the statements inside it need not recover their channels.
  mux-ask : BaseIOF Out → Channel.inType (BaseIO ⊗ᵀ (BaseIO ⊗₀ QIO))
  mux-ask x = L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ ask x
  mux-fwd : BaseIOF Out → Channel.outType (BaseIO ⊗ᵀ (BaseIO ⊗₀ QIO))
  mux-fwd x = ϵ ⊗R ↑ₒ x
  mux-in : BaseIOF In → Channel.inType (BaseIO ⊗ᵀ (BaseIO ⊗₀ QIO))
  mux-in y = ϵ ⊗R ↑ᵢ y
  mux-tell : BaseIOF In → Channel.outType (BaseIO ⊗ᵀ (BaseIO ⊗₀ QIO))
  mux-tell y = L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ ans y

  opaque
    unfolding _⊗₀_ Step

    Mux-ask-inv : ∀ {rs o rs' x}
      → Step Mux rs (mux-ask x) o rs'
      → (o ≡ just (mux-fwd x)) × (rs' ≡ Mux.query ∷ rs)
    Mux-ask-inv st with mux-view st
    ... | inj₁ (_ , ieq , _)                    = inj₁≢inj₂ (sym (inj₂-inj ieq))
    ... | inj₂ (inj₁ (_ , _ , _ , ieq , _))     = inj₁≢inj₂ (sym ieq)
    ... | inj₂ (inj₂ (inj₁ (x' , ieq , oeq , seq))) =
      trans oeq (cong (λ v → just (mux-fwd v)) (sym (ask-inj (inj₂-inj (inj₂-inj ieq))))) , seq
    ... | inj₂ (inj₂ (inj₂ (_ , _ , _ , ieq , _))) = inj₁≢inj₂ (sym ieq)

    Mux-tell-inv : ∀ {rs o rs' y}
      → Step Mux (Mux.query ∷ rs) (mux-in y) o rs'
      → (o ≡ just (mux-tell y)) × (rs' ≡ rs)
    Mux-tell-inv st with mux-view st
    ... | inj₁ (_ , ieq , _)                        = inj₁≢inj₂ ieq
    ... | inj₂ (inj₁ (_ , _ , seq₀ , _))            = case ∷-injectiveˡ seq₀ of λ ()
    ... | inj₂ (inj₂ (inj₁ (_ , ieq , _)))          = inj₁≢inj₂ ieq
    ... | inj₂ (inj₂ (inj₂ (y' , rs₀ , seq₀ , ieq , oeq , seq))) =
      trans oeq (cong (λ v → just (mux-tell v)) (sym (inj₁-inj ieq))) , trans seq (sym (∷-injectiveʳ seq₀))

  -- Request half, innermost first.  Written with `case` rather than `with`:
  -- a `with` re-normalises the goal, and goals here mention the whole
  -- deployed node, whose normal form is enormous.

  ml₀-req-inv : ∀ {sSh rs o s'} x
    → Step (Shim ⊗₁ Mux) (sSh , rs) (L⊗ ϵ ᵗ¹ ↑ₒ e₈ (ask x)) o s'
    → (o ≡ just (ϵ ⊗R ↑ₒ d₀ x)) × (s' ≡ (sSh , Mux.query ∷ rs))
  ml₀-req-inv {sSh} x st =
    case TQ.⊗₁-cod₂-view (step-subst (sym (nest-ᵗ¹ₒ (L⊗ ϵ) (L⊗ ϵ ↑ₒ ask x))) refl st) of λ where
      (rs' , seq , inj₁ (oeq , stM)) →
        case Mux-ask-inv (step-subst (sym (nest-ᵗ¹ₒ (L⊗ ϵ) (ask x))) refl stM) of λ where (eq , _) → case eq of λ ()
      (rs' , seq , inj₂ (inj₁ (c' , oeq , stM))) →
        case Mux-ask-inv (step-subst (sym (nest-ᵗ¹ₒ (L⊗ ϵ) (ask x))) refl stM) of λ where
          (eq , seq') → trans oeq (cong (λ v → just ((L⊗ ϵ) ⊗R ↑ₒ v)) (outᵈ-inj (just-injective eq)))
                      , trans seq (cong (sSh ,_) seq')
      (rs' , seq , inj₂ (inj₂ (_ , _ , stM))) →
        outᵈ≢outᶜ (sym (just-injective (proj₁ (Mux-ask-inv (step-subst (sym (nest-ᵗ¹ₒ (L⊗ ϵ) (ask x))) refl stM)))))

  mux-layer-req-inv : ∀ {sSh rs o s'} {sV : ⊤} x
    → Step mux-layer ((sSh , rs) , sV) (L⊗ ϵ ᵗ¹ ↑ₒ e₇ (ask x)) o s'
    → (o ≡ just (ϵ ⊗R ↑ₒ d₁ x)) × (s' ≡ ((sSh , Mux.query ∷ rs) , sV))
  mux-layer-req-inv x st =
    case TQV.⊗₁-cod₁-view (step-subst (sym (nest-ᵗ¹ₒ (ϵ ⊗R) (e₈ (ask x)))) refl st) of λ where
      (s₀' , seq , inj₁ (oeq , st₀)) → case proj₁ (ml₀-req-inv x st₀) of λ ()
      (s₀' , seq , inj₂ (inj₁ (a' , oeq , st₀))) →
        case ml₀-req-inv x st₀ of λ where
          (eq , seq') → trans oeq (cong just (trans (cong ((ϵ ⊗R) ⊗R ↑ₒ_) (outᵈ-inj (just-injective eq))) (nest-⊗Rₒ (ϵ ⊗R) (d₀ x))))
                      , trans seq (cong (_, _) seq')
      (s₀' , seq , inj₂ (inj₂ (_ , _ , st₀))) → outᵈ≢outᶜ (sym (just-injective (proj₁ (ml₀-req-inv x st₀))))

  R2-req-inv : ∀ {sSh rs o s'} x
    → Step R2 (((sSh , rs) , tt) , tt) (L⊗ ϵ ᵗ¹ ↑ₒ e₆ (ask x)) o s'
    → (o ≡ just (ϵ ⊗R ↑ₒ d₁ x)) × (s' ≡ (((sSh , Mux.query ∷ rs) , tt) , tt))
  R2-req-inv x st =
    case K2.∘-cod-view st of λ where
      (inj₁ (_ , _ , _ , st₁)) → case fwd-cod-inv mux-shuffleᵢ mux-shuffleₒ st₁ of λ ()
      (inj₂ (inj₁ (_ , _ , _ , _ , st₁))) → outᵈ≢outᶜ (sym (just-injective (fwd-cod-inv mux-shuffleᵢ mux-shuffleₒ st₁)))
      (inj₂ (inj₂ (_ , b , st₁ , k))) →
        case K2.mid₂-view (K2.mid₂-subst (trans (outᵈ-inj (just-injective (fwd-cod-inv mux-shuffleᵢ mux-shuffleₒ st₁))) (mux-shuffleₒ-QIO (ask x))) refl k) of λ where
          (inj₁ (_ , _ , _ , stM)) → case proj₁ (mux-layer-req-inv x stM) of λ ()
          (inj₂ (inj₁ (sM' , a' , seq , oeq , stM))) →
            case mux-layer-req-inv x stM of λ where
              (eq , seq') → trans oeq (cong (λ v → just (ϵ ⊗R ↑ₒ v)) (outᵈ-inj (just-injective eq))) , trans seq (cong (_, tt) seq')
          (inj₂ (inj₂ (_ , _ , stM , _))) → outᵈ≢outᶜ (sym (just-injective (proj₁ (mux-layer-req-inv x stM))))

  node-layer-req-inv : ∀ {sLL o s'} z
    → Step node-layer (sLL , tt) (L⊗ ϵ ᵗ¹ ↑ₒ e₅ z) o s'
    → (o ≡ just (ϵ ⊗R ↑ₒ e₆ z)) × (s' ≡ (sLL , tt))
  node-layer-req-inv z st =
    case TN.⊗₁-cod₂-view (step-subst (sym (nest-ᵗ¹ₒ (L⊗ ϵ) z)) refl st) of λ where
      (_ , seq , inj₁ (oeq , stId)) → case id-cod-inv stId of λ ()
      (_ , seq , inj₂ (inj₁ (c' , oeq , stId))) →
        trans oeq (cong (λ v → just ((L⊗ ϵ) ⊗R ↑ₒ v)) (outᵈ-inj (just-injective (id-cod-inv stId)))) , seq
      (_ , seq , inj₂ (inj₂ (_ , _ , stId))) → outᵈ≢outᶜ (sym (just-injective (id-cod-inv stId)))

  R3-req-inv : ∀ {sSh rs sLL o s'} x
    → Step R3 ((((sSh , rs) , tt) , tt) , (sLL , tt)) (L⊗ ϵ ᵗ¹ ↑ₒ e₅ (ask x)) o s'
    → (o ≡ just (ϵ ⊗R ↑ₒ d₁ x)) × (s' ≡ ((((sSh , Mux.query ∷ rs) , tt) , tt) , (sLL , tt)))
  R3-req-inv x st =
    case K3.∘-cod-view st of λ where
      (inj₁ (_ , _ , _ , stN)) → case proj₁ (node-layer-req-inv (ask x) stN) of λ ()
      (inj₂ (inj₁ (_ , _ , _ , _ , stN))) → outᵈ≢outᶜ (sym (just-injective (proj₁ (node-layer-req-inv (ask x) stN))))
      (inj₂ (inj₂ (sN' , b , stN , k))) →
        case node-layer-req-inv (ask x) stN of λ where
          (eqN , seqN) →
            case K3.mid₂-view (K3.mid₂-subst (outᵈ-inj (just-injective eqN)) refl k) of λ where
              (inj₁ (_ , _ , _ , stR)) → case proj₁ (R2-req-inv x stR) of λ ()
              (inj₂ (inj₁ (sR' , a' , seq , oeq , stR))) →
                case R2-req-inv x stR of λ where
                  (eq , seq') → trans oeq (cong (λ v → just (ϵ ⊗R ↑ₒ v)) (outᵈ-inj (just-injective eq))) , trans seq (cong₂ _,_ seq' seqN)
              (inj₂ (inj₂ (_ , _ , stR , _))) → outᵈ≢outᶜ (sym (just-injective (proj₁ (R2-req-inv x stR))))

  ext-req-inv : ∀ {sSh rs sLL o s'} x
    → Step ext-spec (E sSh rs sLL) (L⊗ ϵ ᵗ¹ ↑ₒ e₂ (ask x)) o s'
    → (o ≡ just (ϵ ⊗R ↑ₒ d₁ x)) × (s' ≡ E sSh (Mux.query ∷ rs) sLL)
  ext-req-inv x st =
    case K4.∘-cod-view st of λ where
      (inj₁ (_ , _ , _ , st₁)) → case fwd-cod-inv regroup-extᵢ regroup-extₒ st₁ of λ ()
      (inj₂ (inj₁ (_ , _ , _ , _ , st₁))) → outᵈ≢outᶜ (sym (just-injective (fwd-cod-inv regroup-extᵢ regroup-extₒ st₁)))
      (inj₂ (inj₂ (_ , b , st₁ , k))) →
        case K4.mid₂-view (K4.mid₂-subst (trans (outᵈ-inj (just-injective (fwd-cod-inv regroup-extᵢ regroup-extₒ st₁))) (regroup-extₒ-QIO (ask x))) refl k) of λ where
          (inj₁ (_ , _ , _ , stR)) → case proj₁ (R3-req-inv x stR) of λ ()
          (inj₂ (inj₁ (sR' , a' , seq , oeq , stR))) →
            case R3-req-inv x stR of λ where
              (eq , seq') → trans oeq (cong (λ v → just (ϵ ⊗R ↑ₒ v)) (outᵈ-inj (just-injective eq))) , trans seq (cong (_, tt) seq')
          (inj₂ (inj₂ (_ , _ , stR , _))) → outᵈ≢outᶜ (sym (just-injective (proj₁ (R3-req-inv x stR))))

  -- Answer half, innermost first.

  ml₀-ans-inv : ∀ {sSh rs o s'} y
    → Step (Shim ⊗₁ Mux) (sSh , Mux.query ∷ rs) (ϵ ⊗R ↑ᵢ d₀' y) o s'
    → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ f₈ (ans y))) × (s' ≡ (sSh , rs))
  ml₀-ans-inv {sSh} y st =
    case TQ.⊗₁-dom₂-view (step-subst (sym (nest-⊗Rᵢ (L⊗ ϵ) y)) refl st) of λ where
      (rs' , seq , inj₁ (oeq , stM)) → case proj₁ (Mux-tell-inv stM) of λ ()
      (rs' , seq , inj₂ (inj₁ (_ , _ , stM))) → outᵈ≢outᶜ (just-injective (proj₁ (Mux-tell-inv stM)))
      (rs' , seq , inj₂ (inj₂ (d' , oeq , stM))) →
        case Mux-tell-inv stM of λ where
          (eq , seq') →
            trans oeq (cong just (trans (cong (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ_) (outᶜ-inj (just-injective (trans eq (cong just (nest-ᵗ¹ᵢ (L⊗ ϵ) (ans y)))))))
                                        (nest-ᵗ¹ᵢ (L⊗ ϵ) (L⊗ ϵ ↑ᵢ ans y))))
              , trans seq (cong (sSh ,_) seq')

  mux-layer-ans-inv : ∀ {sSh rs o s'} {sV : ⊤} y
    → Step mux-layer ((sSh , Mux.query ∷ rs) , sV) (ϵ ⊗R ↑ᵢ d₂ y) o s'
    → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ f₁ (ans y))) × (s' ≡ ((sSh , rs) , sV))
  mux-layer-ans-inv y st =
    case TQV.⊗₁-dom₁-view (step-subst (sym (nest-⊗Rᵢ (ϵ ⊗R) (d₀' y))) refl st) of λ where
      (s₀' , seq , inj₁ (oeq , st₀)) → case proj₁ (ml₀-ans-inv y st₀) of λ ()
      (s₀' , seq , inj₂ (inj₁ (_ , _ , st₀))) → outᵈ≢outᶜ (just-injective (proj₁ (ml₀-ans-inv y st₀)))
      (s₀' , seq , inj₂ (inj₂ (b' , oeq , st₀))) →
        case ml₀-ans-inv y st₀ of λ where
          (eq , seq') → trans oeq (cong just (trans (cong (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ_) (outᶜ-inj (just-injective eq))) (nest-ᵗ¹ᵢ (ϵ ⊗R) (f₈ (ans y)))))
                      , trans seq (cong (_, _) seq')

  R2-ans-inv : ∀ {sSh rs o s'} y
    → Step R2 (((sSh , Mux.query ∷ rs) , tt) , tt) (ϵ ⊗R ↑ᵢ d₂ y) o s'
    → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ f₂ (ans y))) × (s' ≡ (((sSh , rs) , tt) , tt))
  R2-ans-inv y st =
    case K2.∘-dom-view st of λ where
      (inj₁ (_ , _ , _ , stM)) → case proj₁ (mux-layer-ans-inv y stM) of λ ()
      (inj₂ (inj₁ (_ , _ , _ , _ , stM))) → outᵈ≢outᶜ (just-injective (proj₁ (mux-layer-ans-inv y stM)))
      (inj₂ (inj₂ (sM' , b' , stM , k))) →
        case mux-layer-ans-inv y stM of λ where
          (eqM , seqM) →
            case K2.mid₁-view (K2.mid₁-subst (outᶜ-inj (just-injective eqM)) refl k) of λ where
              (inj₁ (_ , _ , _ , st₁)) → case fwd-dom-inv mux-shuffleᵢ mux-shuffleₒ st₁ of λ ()
              (inj₂ (inj₁ (_ , c' , seq , oeq , st₁))) →
                trans oeq (cong (λ v → just (L⊗ ϵ ᵗ¹ ↑ᵢ v)) (trans (outᶜ-inj (just-injective (fwd-dom-inv mux-shuffleᵢ mux-shuffleₒ st₁))) (mux-shuffleᵢ-QIO (ans y))))
                  , trans seq (cong (_, tt) seqM)
              (inj₂ (inj₂ (_ , _ , st₁ , _))) → outᵈ≢outᶜ (just-injective (fwd-dom-inv mux-shuffleᵢ mux-shuffleₒ st₁))

  node-layer-ans-inv : ∀ {sLL o s'} w
    → Step node-layer (sLL , tt) (ϵ ⊗R ↑ᵢ f₂ w) o s'
    → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ f₃ w)) × (s' ≡ (sLL , tt))
  node-layer-ans-inv w st =
    case TN.⊗₁-dom₂-view (step-subst (sym (nest-⊗Rᵢ (L⊗ ϵ) w)) refl st) of λ where
      (_ , seq , inj₁ (oeq , stId)) → case id-dom-inv stId of λ ()
      (_ , seq , inj₂ (inj₁ (_ , _ , stId))) → outᵈ≢outᶜ (just-injective (id-dom-inv stId))
      (_ , seq , inj₂ (inj₂ (d' , oeq , stId))) →
        trans oeq (cong just (trans (cong (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ_) (outᶜ-inj (just-injective (id-dom-inv stId)))) (nest-ᵗ¹ᵢ (L⊗ ϵ) w))) , seq

  R3-ans-inv : ∀ {sSh rs sLL o s'} y
    → Step R3 ((((sSh , Mux.query ∷ rs) , tt) , tt) , (sLL , tt)) (ϵ ⊗R ↑ᵢ d₂ y) o s'
    → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ f₃ (ans y))) × (s' ≡ ((((sSh , rs) , tt) , tt) , (sLL , tt)))
  R3-ans-inv y st =
    case K3.∘-dom-view st of λ where
      (inj₁ (_ , _ , _ , stR)) → case proj₁ (R2-ans-inv y stR) of λ ()
      (inj₂ (inj₁ (_ , _ , _ , _ , stR))) → outᵈ≢outᶜ (just-injective (proj₁ (R2-ans-inv y stR)))
      (inj₂ (inj₂ (sR' , b' , stR , k))) →
        case R2-ans-inv y stR of λ where
          (eqR , seqR) →
            case K3.mid₁-view (K3.mid₁-subst (outᶜ-inj (just-injective eqR)) refl k) of λ where
              (inj₁ (_ , _ , _ , stN)) → case proj₁ (node-layer-ans-inv (ans y) stN) of λ ()
              (inj₂ (inj₁ (sN' , c' , seq , oeq , stN))) →
                case node-layer-ans-inv (ans y) stN of λ where
                  (eq , seq') → trans oeq (cong (λ v → just (L⊗ ϵ ᵗ¹ ↑ᵢ v)) (outᶜ-inj (just-injective eq))) , trans seq (cong₂ _,_ seqR seq')
              (inj₂ (inj₂ (_ , _ , stN , _))) → outᵈ≢outᶜ (just-injective (proj₁ (node-layer-ans-inv (ans y) stN)))

  ext-ans-inv : ∀ {sSh rs sLL o s'} y
    → Step ext-spec (E sSh (Mux.query ∷ rs) sLL) (ϵ ⊗R ↑ᵢ d₂ y) o s'
    → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ f₄ (ans y))) × (s' ≡ E sSh rs sLL)
  ext-ans-inv y st =
    case K4.∘-dom-view st of λ where
      (inj₁ (_ , _ , _ , stR)) → case proj₁ (R3-ans-inv y stR) of λ ()
      (inj₂ (inj₁ (_ , _ , _ , _ , stR))) → outᵈ≢outᶜ (just-injective (proj₁ (R3-ans-inv y stR)))
      (inj₂ (inj₂ (sR' , b' , stR , k))) →
        case R3-ans-inv y stR of λ where
          (eqR , seqR) →
            case K4.mid₁-view (K4.mid₁-subst (outᶜ-inj (just-injective eqR)) refl k) of λ where
              (inj₁ (_ , _ , _ , st₁)) → case fwd-dom-inv regroup-extᵢ regroup-extₒ st₁ of λ ()
              (inj₂ (inj₁ (_ , c' , seq , oeq , st₁))) →
                trans oeq (cong (λ v → just (L⊗ ϵ ᵗ¹ ↑ᵢ v)) (trans (outᶜ-inj (just-injective (fwd-dom-inv regroup-extᵢ regroup-extₒ st₁))) (regroup-extᵢ-QIO (ans y))))
                  , trans seq (cong (_, tt) seqR)
              (inj₂ (inj₂ (_ , _ , st₁ , _))) → outᵈ≢outᶜ (just-injective (fwd-dom-inv regroup-extᵢ regroup-extₒ st₁))

  -- Through the tensor with the base adversary channel.

  TE-req-inv : ∀ {sSh rs sLL o s'} {sI : ⊤} x
    → Step (ext-spec ⊗₁ CC.id) (E sSh rs sLL , sI) (L⊗ ϵ ᵗ¹ ↑ₒ e₁ (ask x)) o s'
    → (o ≡ just (ϵ ⊗R ↑ₒ (ϵ ⊗R ↑ₒ d₁ x))) × (s' ≡ (E sSh (Mux.query ∷ rs) sLL , sI))
  TE-req-inv x st =
    case TE.⊗₁-cod₁-view (step-subst (sym (nest-ᵗ¹ₒ (ϵ ⊗R) (e₂ (ask x)))) refl st) of λ where
      (sE' , seq , inj₁ (oeq , stE)) → case proj₁ (ext-req-inv x stE) of λ ()
      (sE' , seq , inj₂ (inj₁ (a' , oeq , stE))) →
        case ext-req-inv x stE of λ where
          (eq , seq') → trans oeq (cong just (trans (cong ((ϵ ⊗R) ⊗R ↑ₒ_) (outᵈ-inj (just-injective eq))) (nest-⊗Rₒ (ϵ ⊗R) (d₁ x))))
                      , trans seq (cong (_, _) seq')
      (sE' , seq , inj₂ (inj₂ (_ , _ , stE))) → outᵈ≢outᶜ (sym (just-injective (proj₁ (ext-req-inv x stE))))

  TE-ans-inv : ∀ {sSh rs sLL o s'} {sI : ⊤} y
    → Step (ext-spec ⊗₁ CC.id) (E sSh (Mux.query ∷ rs) sLL , sI) (ϵ ⊗R ↑ᵢ a₃ y) o s'
    → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ f₅ (ans y))) × (s' ≡ (E sSh rs sLL , sI))
  TE-ans-inv y st =
    case TE.⊗₁-dom₁-view (step-subst (trans (cong (ϵ ⊗R ↑ᵢ_) (sym (d₂-a₃ y))) (sym (nest-⊗Rᵢ (ϵ ⊗R) (d₂ y)))) refl st) of λ where
      (sE' , seq , inj₁ (oeq , stE)) → case proj₁ (ext-ans-inv y stE) of λ ()
      (sE' , seq , inj₂ (inj₁ (_ , _ , stE))) → outᵈ≢outᶜ (just-injective (proj₁ (ext-ans-inv y stE)))
      (sE' , seq , inj₂ (inj₂ (b' , oeq , stE))) →
        case ext-ans-inv y stE of λ where
          (eq , seq') → trans oeq (cong just (trans (cong (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ_) (outᶜ-inj (just-injective eq))) (nest-ᵗ¹ᵢ (ϵ ⊗R) (f₄ (ans y)))))
                      , trans seq (cong (_, _) seq')

  -- The stacked node on a query: the base spec answers, purely.

  X-inv : ∀ {q sS sSh rs sLL o s'} {sI : ⊤}
    → Step X (sS , (E sSh rs sLL , sI)) (L⊗ ϵ ᵗ¹ ↑ₒ e₁ (ask (B.qI (baseQ q)))) o s'
    → ∃ λ r → (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ f₅ (ans (B.qO {baseQ q} r)))) × (s' ≡ (sS , (E sSh rs sLL , sI)))
  X-inv {q} st =
    case KE.∘-cod-view st of λ where
      (inj₁ (_ , _ , _ , stT)) → case proj₁ (TE-req-inv _ stT) of λ ()
      (inj₂ (inj₁ (_ , _ , _ , _ , stT))) → outᵈ≢outᶜ (sym (just-injective (proj₁ (TE-req-inv _ stT))))
      (inj₂ (inj₂ (sT' , b , stT , k))) →
        case TE-req-inv _ stT of λ where
          (eqT , seqT) →
            case KE.mid₂-view (KE.mid₂-subst (trans (outᵈ-inj (just-injective eqT)) (d₁-q₃ _)) refl
                                (subst (λ z → KE.Mid₂ (_ , z) b _ _) seqT k)) of λ where
              (inj₁ (_ , _ , _ , stS)) → case proj₁ (proj₂ (spec-query-inv stS)) of λ ()
              (inj₂ (inj₁ (_ , _ , _ , _ , stS))) → outᵈ≢outᶜ (just-injective (proj₁ (proj₂ (spec-query-inv stS))))
              (inj₂ (inj₂ (sS' , b' , stS , k₁))) →
                case spec-query-inv stS of λ where
                  (r , eqS , seqS) →
                    case KE.mid₁-view (KE.mid₁-subst (outᶜ-inj (just-injective eqS)) refl k₁) of λ where
                      (inj₁ (_ , _ , _ , stT')) → case proj₁ (TE-ans-inv _ stT') of λ ()
                      (inj₂ (inj₁ (sT'' , c' , seq , oeq , stT'))) →
                        case TE-ans-inv _ stT' of λ where
                          (eq , seq') → r , trans oeq (cong (λ v → just (L⊗ ϵ ᵗ¹ ↑ᵢ v)) (outᶜ-inj (just-injective eq)))
                                          , trans seq (cong₂ _,_ (sym seqS) seq')
                      (inj₂ (inj₂ (_ , _ , stT' , _))) → outᵈ≢outᶜ (just-injective (proj₁ (TE-ans-inv _ stT')))

Leios1-query-inv : ∀ {q s o s'}
  → Step Leios1 s (queryIₗ q) o s'
  → ∃ λ r → (o ≡ just (queryOₗ {q} r)) × (s ≡ s')
Leios1-query-inv {q} {(sS , ((((((sSh , rs) , tt) , tt) , (sLL , tt)) , tt) , sI)) , sF} st =
  case KL.∘-cod-view st of λ where
    (inj₁ (_ , _ , _ , st₁)) → case fwd-cod-inv ∘ᴷ-fwdᵢ ∘ᴷ-fwdₒ st₁ of λ ()
    (inj₂ (inj₁ (_ , _ , _ , _ , st₁))) → outᵈ≢outᶜ (sym (just-injective (fwd-cod-inv ∘ᴷ-fwdᵢ ∘ᴷ-fwdₒ st₁)))
    (inj₂ (inj₂ (sF' , b , st₁ , k))) →
      case KL.mid₂-view (KL.mid₂-subst (trans (outᵈ-inj (just-injective (fwd-cod-inv ∘ᴷ-fwdᵢ ∘ᴷ-fwdₒ st₁))) (∘ᴷ-fwdₒ-QIO _)) refl k) of λ where
        (inj₁ (_ , _ , _ , stX)) → case proj₁ (proj₂ (X-inv {q} stX)) of λ ()
        (inj₂ (inj₁ (_ , _ , _ , _ , stX))) → outᵈ≢outᶜ (just-injective (proj₁ (proj₂ (X-inv {q} stX))))
        (inj₂ (inj₂ (sX' , b' , stX , k₁))) →
          case X-inv {q} stX of λ where
            (r , eqX , seqX) →
              case KL.mid₁-view (KL.mid₁-subst (outᶜ-inj (just-injective eqX)) refl k₁) of λ where
                (inj₁ (_ , _ , _ , st₃)) → case fwd-dom-inv ∘ᴷ-fwdᵢ ∘ᴷ-fwdₒ st₃ of λ ()
                (inj₂ (inj₁ (sF'' , c' , seq , oeq , st₃))) →
                  mapExt q r
                  , trans oeq (cong (λ v → just (L⊗ ϵ ᵗ¹ ↑ᵢ v))
                      (trans (outᶜ-inj (just-injective (fwd-dom-inv ∘ᴷ-fwdᵢ ∘ᴷ-fwdₒ st₃)))
                             (trans (∘ᴷ-fwdᵢ-QIO _) (cong (λ v → f₀ (ans (B.qO v))) (sym (mapBase∘mapExt q r))))))
                  , trans (cong (_, sF'') (sym seqX)) (sym seq)
                (inj₂ (inj₂ (_ , _ , st₃ , _))) → outᵈ≢outᶜ (just-injective (fwd-dom-inv ∘ᴷ-fwdᵢ ∘ᴷ-fwdₒ st₃))

------------------------------------------------------------------------
-- The interface of the deployed node.

Leios1-isConstrained : IsConstrained Leios1 (bciQueryType {Block = LeiosBlock})
Leios1-isConstrained = record
  { queryI       = queryIₗ
  ; queryO       = queryOₗ
  ; correctness  = corr
  ; completeness = Leios1-completeness
  }
  where
    corr : ∀ {q s o s'} → Machine.stepRel Leios1 s (queryIₗ q) o s' → ∃ λ r → o ≡ just (queryOₗ {q} r)
    corr {o = o} st = let r , eq , _ = Leios1-query-inv (toStep {M = Leios1} {o = o} st) in r , eq

Leios1-isPure : IsPure Leios1-isConstrained
Leios1-isPure q {response' = o} st = proj₂ (proj₂ (Leios1-query-inv (toStep {M = Leios1} {o = o} st)))

IsBlockchain-Leios1 : (base-party : Fin B.n → Participant) → IsBC.IsBlockchain Participant LeiosBlock Leios1
IsBlockchain-Leios1 base-party = record
  { isConstrained = Leios1-isConstrained
  ; isPure        = Leios1-isPure
  ; producer      = λ b → base-party (B.producer (LeiosBlock.rb b))
  ; slotOf        = λ b → B.slotOf (LeiosBlock.rb b)
  }

------------------------------------------------------------------------
-- The two interfaces agree: the deployed node's answer is the base spec's,
-- read as Leios blocks.  This is the chain and slot lemmas' content at the
-- level of a single node.  The other half is
-- `Blockchain.Safety.Transfer.transState-nodes`, that the transfer carries a
-- node's state to its base component.

-- The base spec's state inside the deployed node's.
specOf : Machine.State Leios1 → Machine.State spec
specOf ((sS , _) , _) = sS

private
  opaque
    unfolding _⊗₀_

    a₃-inj : ∀ {y y'} → a₃ y ≡ a₃ y' → y ≡ y'
    a₃-inj refl = refl

    f₀-inj : ∀ {w w'} → f₀ w ≡ f₀ w' → w ≡ w'
    f₀-inj refl = refl

  ans-inj : ∀ {y y'} → ans y ≡ ans y' → y ≡ y'
  ans-inj refl = refl

  -- Both answer messages determine their answer, because the base layer's
  -- does (`B.qO-inj`) and `LeiosBlock.rb` is injective.
  queryOₛ-inj : ∀ {q} {r r' : bciQueryType {Block = RankingBlock} q}
              → queryOₛ r ≡ queryOₛ r' → r ≡ r'
  queryOₛ-inj eq = B.qO-inj (a₃-inj (outᶜ-inj eq))

  mapBase-inj : ∀ q {v v' : bciQueryType {Block = LeiosBlock} q}
              → mapBase q v ≡ mapBase q v' → v ≡ v'
  mapBase-inj Chain = map-injective LeiosBlock-Injective
  mapBase-inj Slot  = λ eq → eq

  queryOₗ-inj : ∀ {q} {v v' : bciQueryType {Block = LeiosBlock} q}
              → queryOₗ {q} v ≡ queryOₗ {q} v' → v ≡ v'
  queryOₗ-inj {q} eq = mapBase-inj q (B.qO-inj (ans-inj (f₀-inj (outᶜ-inj eq))))

  module ICₛ = IsConstrained spec-isConstrained
  module ICₗ = IsConstrained Leios1-isConstrained

-- The node answers a query with `mapExt` of what the base spec answers: both
-- computations bottom out in the same `spec-completeness` witness, so the
-- hypothesis of `queryCompute-answer` holds by computation.
node-answer : ∀ q (σ : Machine.State Leios1)
  → proj₁ (ICₗ.queryCompute q σ) ≡ mapExt q (proj₁ (ICₛ.queryCompute (baseQ q) (specOf σ)))
node-answer q σ = queryCompute-answer Leios1-isConstrained queryOₗ-inj refl

-- Hence the two answers agree under the block-level projection: for `Chain`
-- this is `map LeiosBlock.rb`, for `Slot` the identity.
node-compat : ∀ q (σ : Machine.State Leios1)
  → mapBase q (proj₁ (ICₗ.queryCompute q σ)) ≡ proj₁ (ICₛ.queryCompute (baseQ q) (specOf σ))
node-compat q σ = trans (cong (mapBase q) (node-answer q σ)) (mapBase∘mapExt q _)

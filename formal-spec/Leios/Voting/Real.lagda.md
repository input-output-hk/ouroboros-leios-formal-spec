## The real voting scheme and its refinement of the ideal model

The real scheme collects concrete votes. A vote carries no honesty/validation
evidence, it is just a signature. An adversary may submit any vote it can
produce. We relate it to the ideal model of `Leios.Voting.Ideal` by a **forward
simulation**: an abstraction `α : RealState → IdealState` that keeps the valid
votes, and under which the real certificate predicate refines the ideal one. The
correctness property then transfers: *a real certificate implies an honest node
validated the block.*

The single cryptographic/protocol assumption is isolated as an explicit hypothesis
`validated-if-honest`: a valid vote whose voter is honest was really produced by
that honest party, who (per the protocol) had validated the block. This bundles
signature unforgeability (EUF-CMA) with the honest voting rule.

**On the library-level UC statement.** The ultimate goal is
`Real ≤'UC Ideal` in the sense of `CategoricalCrypto.Machine.Core`
(`R ≤'UC I = ∃[ S ] R ≈ℰ (B ⊗ˡ S ∘ I)`). That relation is *perfect* behavioural
equality (`≈ℰ` is propositional equality of the environment-composed machines), for
which the library does not yet provide a workable proof principle; a
trace/simulation-based equivalence is still being developed. The forward simulation
below is the tractable substitute and already yields the security-relevant
consequence.

<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (Unique)

open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
import Data.List.Relation.Unary.All as All

import Leios.Voting.Ideal
```
-->

In addition to the ideal parameters, the real model needs the concrete vote type
together with the ways to read off the voter and the referenced block from a vote,
and a decidable notion of vote validity.

```agda
module Leios.Voting.Real
  (Party      : Type)
  (EBRef      : Type)
  (honest     : Party → Type) ⦃ _ : honest ⁇¹ ⦄
  (Validated  : Party → EBRef → Type)
  (threshold  : ℕ)
  (Vote       : Type)
  (voter      : Vote → Party)
  (forEB      : Vote → EBRef)
  (Valid      : Vote → Type) ⦃ _ : Valid ⁇¹ ⦄
  where

module I = Leios.Voting.Ideal Party EBRef honest Validated threshold
```

### The real functionality

The state is the multiset (list) of votes received so far; the only step is
receiving a vote, which may come from anyone.

```agda
RealState : Type
RealState = List Vote

data Step : RealState → RealState → Type where
  Recv : ∀ {rs} (v : Vote) → Step rs (v ∷ rs)
```

### Abstraction to the ideal state

`α` forgets everything but the *valid* votes, projecting each to the ideal vote
`(voter , block)`.

```agda
vote⇒ideal : Vote → Party × EBRef
vote⇒ideal v = voter v , forEB v

α : RealState → I.IdealState
α rs = I.⟨ L.map vote⇒ideal (L.filter ¿ Valid ¿¹ rs) ⟩

α-init : α [] ≡ I.init
α-init = refl
```

Under `validated-if-honest`, the abstraction lands in a well-formed ideal state:
every honest vote in `α rs` is backed by a validation.

```agda
α-WF : ∀ {rs}
     → (∀ {v} → v ∈ˡ rs → Valid v → honest (voter v) → Validated (voter v) (forEB v))
     → I.WF (α rs)
α-WF {rs} vih {p} {eb} p∈ hp with ∈-map⁻ vote⇒ideal p∈
... | v , v∈filter , pq with ∈-filter⁻ ¿ Valid ¿¹ v∈filter
... | v∈rs , validv =
  let p≡  : p ≡ voter v
      p≡  = cong proj₁ pq
      eb≡ : eb ≡ forEB v
      eb≡ = cong proj₂ pq
      val : Validated (voter v) (forEB v)
      val = vih v∈rs validv (subst honest p≡ hp)
  in subst (λ q → Validated q eb) (sym p≡)
       (subst (λ w → Validated (voter v) w) (sym eb≡) val)
```

### Real certificates and their refinement

A real certificate is a quorum of valid votes for the block, cast by distinct
parties.

```agda
record RealCertified (rs : RealState) (eb : EBRef) : Type where
  field
    votes        : List Vote
    sub          : ∀ {v} → v ∈ˡ votes → v ∈ˡ rs
    allValid     : All.All Valid votes
    allFor       : All.All (λ v → forEB v ≡ eb) votes
    uniqueVoters : Unique (L.map voter votes)
    quorum       : threshold N.≤ length (L.map voter votes)
```

Every real certificate abstracts to an ideal certificate on `α rs`.

```agda
realCert⇒idealCert : ∀ {rs eb} → RealCertified rs eb → I.Certified (α rs) eb
realCert⇒idealCert {rs} {eb} rc = record
  { voters = L.map voter votes
  ; unique = uniqueVoters
  ; voted  = map⁺ voted-votes
  ; quorum = quorum
  }
  where
    open RealCertified rc
    voted-votes : All.All (λ v → I.Voted (voter v) eb (α rs)) votes
    voted-votes = All.tabulate λ {v} v∈votes →
      subst (λ w → I.Voted (voter v) w (α rs)) (All.lookup allFor v∈votes)
        (∈-map⁺ vote⇒ideal (∈-filter⁺ ¿ Valid ¿¹ (sub v∈votes) (All.lookup allValid v∈votes)))
```

### Correctness transfers to the real scheme

Combining the abstraction with the ideal `cert-correct`: a real certificate implies
some honest node validated the block, provided the adversary controls fewer than
`threshold` parties (every dishonest valid voter is one of them).

```agda
real-cert-correct : ∀ {rs eb}
  → (validated-if-honest : ∀ {v} → v ∈ˡ rs → Valid v → honest (voter v) → Validated (voter v) (forEB v))
  → (corrupt : List Party)
  → (corrupt-covers   : ∀ {v} → v ∈ˡ rs → Valid v → ¬ honest (voter v) → voter v ∈ˡ corrupt)
  → length corrupt N.< threshold
  → RealCertified rs eb
  → ∃[ p ] (honest p × Validated p eb)
real-cert-correct {rs} {eb} vih corrupt cc bound rc =
  I.cert-correct (α-WF vih) corrupt covers bound (realCert⇒idealCert rc)
  where
    covers : ∀ {p} → I.Voted p eb (α rs) → ¬ honest p → p ∈ˡ corrupt
    covers {p} p∈ ¬hp with ∈-map⁻ vote⇒ideal p∈
    ... | v , v∈filter , pq with ∈-filter⁻ ¿ Valid ¿¹ v∈filter
    ... | v∈rs , validv =
      subst (_∈ˡ corrupt) (sym (cong proj₁ pq))
        (cc v∈rs validv (λ hv → ¬hp (subst honest (sym (cong proj₁ pq)) hv)))
```

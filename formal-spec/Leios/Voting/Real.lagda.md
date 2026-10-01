## The real voting scheme and its refinement of the ideal model

The real scheme collects concrete votes.  A vote carries no honesty or
validation evidence, and an adversary may submit any vote it can produce.  The
abstraction `α : RealState → IdealState` keeps the valid votes, and under it
every real certificate is an ideal one.  The ideal correctness property then
transfers: provided every valid vote of an honest voter is backed by a
validation (`validated-if-honest`), a real certificate implies that an honest
party validated the block.

<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (Unique)

open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Relation.Unary.All.Properties

import Leios.Voting.Ideal
```
-->

Honesty and validation enter only in `Refines` below, so that implementations
such as `Leios.Voting.Voter` can be instantiated without them.

```agda
module Leios.Voting.Real
  (Party      : Type)
  (EBRef      : Type)
  (threshold  : ℕ)
  (Vote       : Type)
  (voter      : Vote → Party)
  (forEB      : Vote → EBRef)
  (Valid      : Vote → Type) ⦃ _ : Valid ⁇¹ ⦄
  where
```

### The real functionality

```agda
RealState : Type
RealState = List Vote

data Step : RealState → RealState → Type where
  Recv : ∀ {rs} (v : Vote) → Step rs (v ∷ rs)
```

### Real certificates

```agda
record RealCertified (rs : RealState) (eb : EBRef) : Type where
  field
    votes        : List Vote
    sub          : ∀ {v} → v ∈ˡ votes → v ∈ˡ rs
    allValid     : All.All Valid votes
    allFor       : All.All (λ v → forEB v ≡ eb) votes
    uniqueVoters : Unique (L.map voter votes)
    quorum       : threshold N.≤ length (L.map voter votes)

vote⇒ideal : Vote → Party × EBRef
vote⇒ideal v = voter v , forEB v
```

### Refinement into the ideal model

```agda
module Refines
  (honest     : Party → Type) ⦃ _ : honest ⁇¹ ⦄
  (Validated  : Party → EBRef → Type)
  where

  module I = Leios.Voting.Ideal Party EBRef honest Validated threshold

  α : RealState → I.IdealState
  α rs = I.⟨ L.map vote⇒ideal (filter Valid rs) ⟩

  α-init : α [] ≡ I.init
  α-init = refl

  α-WF : ∀ {rs}
       → (∀ {v} → v ∈ˡ rs → Valid v → honest (voter v) → Validated (voter v) (forEB v))
       → I.WF (α rs)
  α-WF vih p∈ hp with ∈-map⁻ vote⇒ideal p∈
  ... | _ , v∈filter , refl = uncurry vih (∈-filter⁻ ¿ Valid ¿¹ v∈filter) hp

  realCert⇒idealCert : ∀ {rs eb} → RealCertified rs eb → I.Certified (α rs) eb
  realCert⇒idealCert {rs} rc = record
    { voters = L.map voter votes
    ; unique = uniqueVoters
    ; voted  = map⁺ $ All.tabulate λ {v} v∈votes →
        subst (λ w → I.Voted (voter v) w (α rs)) (All.lookup allFor v∈votes)
          (∈-map⁺ vote⇒ideal (∈-filter⁺ ¿ Valid ¿¹ (sub v∈votes) (All.lookup allValid v∈votes)))
    ; quorum = quorum
    }
    where open RealCertified rc
```

### Correctness transfers to the real scheme

```agda
  real-cert-correct : ∀ {rs eb}
    → (validated-if-honest : ∀ {v} → v ∈ˡ rs → Valid v → honest (voter v) → Validated (voter v) (forEB v))
    → (corrupt : List Party)
    → (corrupt-covers : ∀ {v} → v ∈ˡ rs → Valid v → ¬ honest (voter v) → voter v ∈ˡ corrupt)
    → length corrupt N.< threshold
    → RealCertified rs eb
    → ∃[ p ] (honest p × Validated p eb)
  real-cert-correct {rs} {eb} vih corrupt cc bound rc =
    I.cert-correct (α-WF vih) corrupt covers bound (realCert⇒idealCert rc)
    where
      covers : ∀ {p} → I.Voted p eb (α rs) → ¬ honest p → p ∈ˡ corrupt
      covers p∈ ¬hp with ∈-map⁻ vote⇒ideal p∈
      ... | _ , v∈filter , refl = uncurry cc (∈-filter⁻ ¿ Valid ¿¹ v∈filter) ¬hp
```

{-# OPTIONS --safe #-}
module CategoricalCrypto.SRel where

open import Level renaming (zero to ℓ0)

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Cocartesian
open import Categories.Category.Discrete
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
open import Categories.Category.Instance.Rels
open import Categories.Category.Monoidal.Instance.Rels
open import Categories.Functor
open import Categories.Functor.Properties

open import CategoricalCrypto.NaturalTransformationHelper
open import Relation.Binary.Core using (Rel)
import Relation.Binary.Structures
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties renaming (setoid to ≡-setoid)
open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; [_]; ⊤; ⊥; Functor)
import abstract-set-theory.Prelude as P
import Function.Related.Propositional as R
open import Data.Product.Properties.Ext
open import Data.Product.Function.NonDependent.Propositional
open import Data.Product.Function.Dependent.Propositional renaming (cong to ∃-cong)
open import Function.Related.TypeIsomorphisms
open import Data.Unit.Polymorphic.Base using (⊤)
open import Data.Empty.Polymorphic using (⊥)
open import Function.Properties.Equivalence renaming (sym to sym⇔)

SRelType : Type → Type → Type → Type₁
SRelType A B S = S → A → B → S → Type

SRel : Type → Type → Type₁
SRel A B = ∃ (SRelType A B)

private variable A B C D : Type

data Trace (R : SRel A B) (init : proj₁ R) : List A → List B → Type where
  trace[] :                                                                   Trace R init []       []
  trace∷  : ∀ {a b next as bs} → proj₂ R init a b next → Trace R next as bs → Trace R init (a ∷ as) (b ∷ bs)  

_≤ᵗ_ : SRel A B → SRel A B → Type
R₁ ≤ᵗ R₂ = ∀ s₁ → ∃[ s₂ ] ∀ as bs → Trace R₁ s₁ as bs ⇔ Trace R₂ s₂ as bs

infix  4 _≡ᵗ_

_≡ᵗ_ : SRel A B → SRel A B → Type
R₁ ≡ᵗ R₂ = R₁ ≤ᵗ R₂ × R₂ ≤ᵗ R₁

module _ {A B} (let open Relation.Binary.Structures (_≡ᵗ_ {A} {B}))  where

  ≤ᵗ-transitive : Transitive (_≤ᵗ_ {A} {B})
  ≤ᵗ-transitive a b = λ s₁ →
    let (u , v) = a s₁
        (w , x) = b u
     in w , λ _ _ → R.K-trans (v _ _) (x _ _)

  ≤ᵗ-reflexive : Reflexive (_≤ᵗ_ {A} {B})
  ≤ᵗ-reflexive s = s , λ _ _ → R.K-refl
  
  ≡ᵗ-reflexive : Reflexive (_≡ᵗ_ {A} {B})
  ≡ᵗ-reflexive = ≤ᵗ-reflexive , ≤ᵗ-reflexive

  ≡ᵗ-symmetric : Symmetric (_≡ᵗ_ {A} {B})
  ≡ᵗ-symmetric (u , v) = (v , u)

  ≡ᵗ-transitive : Transitive (_≡ᵗ_ {A} {B})
  ≡ᵗ-transitive (u , v) (w , x) = ≤ᵗ-transitive u w , ≤ᵗ-transitive x v

  ≡ᵗ-equivalence : IsEquivalence
  ≡ᵗ-equivalence = record
    { refl = ≡ᵗ-reflexive
    ; sym = ≡ᵗ-symmetric
    ; trans = ≡ᵗ-transitive }

  ≤ᵗ-antisym : Antisymmetric (_≡ᵗ_ {A} {B}) (_≤ᵗ_ {A} {B})
  ≤ᵗ-antisym = _,_

  ≤ᵗ-partial-order : IsPartialOrder _≤ᵗ_
  ≤ᵗ-partial-order = record
    { isPreorder = record
      { isEquivalence = ≡ᵗ-equivalence
      ; reflexive = proj₁
      ; trans = ≤ᵗ-transitive }
    ; antisym = ≤ᵗ-antisym }

module _ ((S₁ , rel₁) (S₂ , rel₂) : SRel A B) where

  infix 4 _≡ᵉ_
  record _≡ᵉ_ : Type where
  
    field S₁↔S₂ : S₁ ↔ S₂

    open Inverse S₁↔S₂
   
    field rel₁⇔rel₂[to-to] : ∀ {s a b s'} → rel₁ s a b s' ⇔ rel₂ (to s) a b (to s')

    ≡-≡-rel₁⇔rel₂ : ∀ {s₁ s₁' a b s₂ s₂'} → to s₁ ≡ s₂ → to s₁' ≡ s₂' → rel₁ s₁ a b s₁' ⇔ rel₂ s₂ a b s₂'
    ≡-≡-rel₁⇔rel₂ refl refl = rel₁⇔rel₂[to-to]

    rel₁[from-from]⇔rel₂ : ∀ {s₂ a b s₂'} → rel₁ (from s₂) a b (from s₂') ⇔ rel₂ s₂ a b s₂'
    rel₁[from-from]⇔rel₂ = ≡-≡-rel₁⇔rel₂ (strictlyInverseˡ _) (strictlyInverseˡ _)
      
    rel₁[from-]⇔rel₂[-to] : ∀ {s₂ a b s₁} → rel₁ (from s₂) a b s₁ ⇔ rel₂ s₂ a b (to s₁)
    rel₁[from-]⇔rel₂[-to] = ≡-≡-rel₁⇔rel₂ (strictlyInverseˡ _) P.refl

    rel₁[-from]⇔rel₂[to-] : ∀ {s₂ a b s₁} → rel₁ s₁ a b (from s₂) ⇔ rel₂ (to s₁) a b s₂
    rel₁[-from]⇔rel₂[to-] = ≡-≡-rel₁⇔rel₂ P.refl (strictlyInverseˡ _)

private variable R R₁ R₂ R₃ R₄ : SRel A B

-- ≡ᵉ is much easier to prove, but less general
≡ᵉ⇒≡ᵗ : R₁ ≡ᵉ R₂ → R₁ ≡ᵗ R₂
≡ᵉ⇒≡ᵗ {R₁ = R₁} {R₂} R₁≡ᵉR₂ =
  < to   , (λ _ _ _ → ≡-≡-trace⇔ P.refl) > ,
  < from , (λ _ _ _ → R.SK-sym (≡-≡-trace⇔ (sym (strictlyInverseˡ _)))) >
  where
    open _≡ᵉ_ R₁≡ᵉR₂
    open Inverse S₁↔S₂

    ≡-trace₁⇒trace₂ : ∀ {s s' as bs} → s' ≡ to s → Trace R₁ s as bs → Trace R₂ s' as bs
    ≡-trace₁⇒trace₂ P.refl trace[] = trace[]
    ≡-trace₁⇒trace₂ P.refl (trace∷ {next = next} x x₁) = trace∷ (rel₁⇔rel₂[to-to] .Equivalence.to x)
                                                                (≡-trace₁⇒trace₂ P.refl x₁)

    ≡-trace₂⇒trace₁ : ∀ {s s' as bs} → s' ≡ to s → Trace R₂ s' as bs → Trace R₁ s as bs
    ≡-trace₂⇒trace₁ P.refl trace[] = trace[]
    ≡-trace₂⇒trace₁ P.refl (trace∷ {next = next} x x₁) = trace∷ ((R.SK-sym rel₁[-from]⇔rel₂[to-]) .Equivalence.to x)
                                                                (≡-trace₂⇒trace₁ (sym (strictlyInverseˡ next)) x₁)

    ≡-≡-trace⇔ : ∀ {s s' as bs} → s' ≡ to s → Trace R₁ s as bs ⇔ Trace R₂ s' as bs
    ≡-≡-trace⇔ p = mk⇔ (≡-trace₁⇒trace₂ p) (≡-trace₂⇒trace₁ p)

module _ ((S₁ , rel₁) : SRel B C) ((S₂ , rel₂) : SRel A B) where
  
  record ∘-rel (s : S₁ × S₂) (a : A) (c : C) (s' : S₁ × S₂) : Type where
    field
      b     : B
      ∘-rel₁ : rel₁ (proj₁ s) b c (proj₁ s')
      ∘-rel₂ : rel₂ (proj₂ s) a b (proj₂ s')

  infixr 9 _∘_
  
  _∘_ : SRel A C
  _∘_ = -, ∘-rel

_⊗₀_ : Type × Type → Type
_⊗₀_ = uncurry _⊎_

module _ ((S₁ , rel₁) : SRel A B) ((S₂ , rel₂) : SRel C D) where

  data ⊗-rel : SRelType (A ⊎ C) (B ⊎ D) (S₁ × S₂) where
    ⊗₁₁ : ∀ {s₁ s₁' s₂ a c} → rel₁ s₁ a c s₁' → ⊗-rel (s₁ , s₂) (inj₁ a) (inj₁ c) (s₁' , s₂)
    ⊗₁₂ : ∀ {s₁ s₂ s₂' b d} → rel₂ s₂ b d s₂' → ⊗-rel (s₁ , s₂) (inj₂ b) (inj₂ d) (s₁ , s₂')

  _⊗₁_ : SRel (A ⊎ C) (B ⊎ D)
  _⊗₁_ = -, ⊗-rel

-- This definition is awkward, because we would prefer to allow 'arbitrary' extensions of the state.
-- This could be done by instead having an injection `State ↪ State'` or a partial function
-- `State' → Maybe State`.
-- However, none of these are stronger, since you can always replace the state with an isomorphic
-- type via `≡ᵉ⇒≡ⁱ`. I don't know what the best option would be.

module _
  {Extension : Type}
  ((S , rel) : SRel A B)
  {_≈_       : Rel Extension lzero}
  (≈-equiv   : let open Relation.Binary.Structures _≈_ in IsEquivalence)
  (f         : Injection (record { Carrier = Extension ; _≈_ = _≈_ ; isEquivalence = ≈-equiv }) (≡-setoid S)) where

  open Injection f

  Ext : SRelType A B Extension 
  Ext s a b s' = rel (to s) a b (to s')

  ⊃ : SRel A B
  ⊃ = -, Ext

-- This extends the internal state of an SRel by making a pair with an arbitrary type
weakenState : SRel A B → Type → SRel A B
weakenState sRel Extension = ⊃ {Extension = proj₁ sRel × Extension} sRel {_≡_ on proj₁}
  (record { refl = P.refl ; sym = λ {P.refl → P.refl} ; trans = λ {P.refl P.refl → P.refl}})
  (record { to = proj₁ ; cong = P.id ; injective = P.id })

infix  4 _≡ⁱ_

data _≡ⁱ_ : SRel A B → SRel A B → Type₁ where
  ≡ᵉ⇒≡ⁱ    : R₁ ≡ᵉ R₂ → R₁ ≡ⁱ R₂
  weaken  : ∀ {X} → R ≡ⁱ weakenState R X
  ≡ⁱ-∘     : R₁ ≡ⁱ R₂ → R₃ ≡ⁱ R₄ → R₁ ∘ R₂ ≡ⁱ R₃ ∘ R₄
  ≡ⁱ-⊗    : R₁ ≡ⁱ R₂ → R₃ ≡ⁱ R₄ → R₁ ⊗₁ R₂ ≡ⁱ R₃ ⊗₁ R₄
  ≡ⁱ-refl  : R ≡ⁱ R
  ≡ⁱ-sym   : R₁ ≡ⁱ R₂ → R₂ ≡ⁱ R₁
  ≡ⁱ-trans : R₁ ≡ⁱ R₂ → R₂ ≡ⁱ R₃ → R₁ ≡ⁱ R₃

-- this should be straightforward
≡ⁱ⇒≡ᵗ : R₁ ≡ⁱ R₂ → R₁ ≡ᵗ R₂
≡ⁱ⇒≡ᵗ (≡ᵉ⇒≡ⁱ x) = ≡ᵉ⇒≡ᵗ x
≡ⁱ⇒≡ᵗ weaken = {!!}
≡ⁱ⇒≡ᵗ (≡ⁱ-∘ x x₁) = {!!}
≡ⁱ⇒≡ᵗ (≡ⁱ-⊗ x x₁) = {!!}
≡ⁱ⇒≡ᵗ ≡ⁱ-refl = {!!} -- ≡ᵗ-reflexive
≡ⁱ⇒≡ᵗ (≡ⁱ-sym x) = let (u , v) = ≡ⁱ⇒≡ᵗ x in (v , u)
≡ⁱ⇒≡ᵗ (≡ⁱ-trans x x₁) = {!!}

-- -- here's a proof sketch, assuming the axiom of choice:
-- -- - we can assume that R₁ and R₂ have 'minimal' state because of `weaken` (choose a minimal one)
-- -- - WLOG assume S₁ ↪ S₂, then again by weaken & ≡ᵉ⇒≡ⁱ it follows that we can weaken R₂ to
-- --   have state type S₂, so we can assume R₁ and R₂ have the same state type
-- -- - now proving R₁ ≡ᵉ R₂ should be straightforward since we just need to prove `rel₁⇔rel₂[to-to]`,
-- --   and that follows from the traces
-- -- ≡ᵗ⇒≡ⁱ : R₁ ≡ᵗ R₂ → R₁ ≡ⁱ R₂
-- -- ≡ᵗ⇒≡ⁱ = {!!}

-- SRelC : Category (sucˡ ℓ0) (sucˡ ℓ0) ℓ0
-- SRelC = categoryHelper record
--   { Obj       = Type
--   ; _⇒_       = SRel
--   ; _≈_       = _≡ᵗ_
--   ; id        = record { State = ⊤ ; rel = λ _ a₁ a₂ _ → a₁ ≡ a₂ }
--   ; _∘_       = _∘_
--   ; assoc     = ≡ᵉ⇒≡ᵗ {!!}
--   ; identityˡ = ≡ᵉ⇒≡ᵗ record
--     { S₁↔S₂ = ×-identityˡ ℓ0 _
--     ; rel₁⇔rel₂[to-to] = mk⇔
--       (λ where record { b = _ ; ∘-rel₁ = refl ; ∘-rel₂ = ∘-rel₂ } → ∘-rel₂)
--       (λ rel → record { b = _ ; ∘-rel₁ = refl ; ∘-rel₂ = rel })
--     }
--   ; identityʳ = ≡ᵉ⇒≡ᵗ record
--     { S₁↔S₂ = ×-identityʳ ℓ0 _
--     ; rel₁⇔rel₂[to-to] = mk⇔
--       (λ where record { b = _ ; ∘-rel₁ = ∘-rel₁ ; ∘-rel₂ = refl } → ∘-rel₁)
--       (λ rel → record { b = _ ; ∘-rel₁ = rel ; ∘-rel₂ = refl })
--     }
--   ; equiv     = {!!}
--   ; ∘-resp-≈  = {!!}
--   }
--   where open R.EquationalReasoning

-- StatelessRel : Functor (Rels 0ℓ 0ℓ) SRelC
-- StatelessRel = record
--   { F₀ = P.id
--   ; F₁ = λ R → record { State = ⊤ ; rel = λ _ a b _ → R a b }
--   ; identity = ≡ᵉ⇒≡ᵗ record
--     { S₁↔S₂ = R.K-refl
--     ; rel₁⇔rel₂[to-to] = mk⇔ (λ where (lift refl) → refl) λ where refl → lift refl
--     }
--   ; homomorphism = ≡ᵉ⇒≡ᵗ record
--     { S₁↔S₂ = R.SK-sym $ ×-identityʳ ℓ0 _
--     ; rel₁⇔rel₂[to-to] = mk⇔
--       (λ where (_ , Rab , Rbc) → record { b = _ ; ∘-rel₁ = Rbc ; ∘-rel₂ = Rab })
--       (λ where record { b = b ; ∘-rel₁ = ∘-rel₁ ; ∘-rel₂ = ∘-rel₂ } → b , ∘-rel₂ , ∘-rel₁ )
--     }
--   ; F-resp-≈ = λ where
--     (R₁⇒R₂ , R₂⇒R₁) → ≡ᵉ⇒≡ᵗ record { S₁↔S₂ = R.K-refl ; rel₁⇔rel₂[to-to] = mk⇔ R₁⇒R₂ R₂⇒R₁ }
--   }

-- module RelsMonoidal where
--   open Category (Rels 0ℓ 0ℓ) public
--   open Monoidal (CocartesianMonoidal.+-monoidal (Rels 0ℓ 0ℓ) Rels-Cocartesian) public
--   open import Categories.Category.Monoidal.Utilities (CocartesianMonoidal.+-monoidal (Rels 0ℓ 0ℓ) Rels-Cocartesian) public
--   open Shorthands public

-- Monoidal-SRelC : Monoidal SRelC
-- Monoidal-SRelC = monoidalHelper SRelC record
--   { ⊗               = record
--     { F₀ = ⊗₀
--     ; F₁ = _⊗₁_
--     ; identity = ≡ᵉ⇒≡ᵗ record
--       { S₁↔S₂ = ×-identityʳ ℓ0 _
--       ; rel₁⇔rel₂[to-to] = ? -- λ {_} {a} → mk⇔
--       --   (λ where (⊗₁₁ refl) → refl ; (⊗₁₂ refl) → refl)
--       --   (λ where refl → case a returning (λ a → ⊗-rel _ _ a a _) of λ where
--       --      (inj₁ x) → ⊗₁₁ refl
--       --      (inj₂ y) → ⊗₁₂ refl)
--       -- }
--     ; homomorphism = {!!}
--     ; F-resp-≈ = {!!}
--     }
--   ; unit            = ⊥
--   ; unitorˡ         = [ StatelessRel ]-resp-≅ RelsMonoidal.unitorˡ
--   ; unitorʳ         = [ StatelessRel ]-resp-≅ RelsMonoidal.unitorʳ
--   ; associator      = [ StatelessRel ]-resp-≅ RelsMonoidal.associator
--   ; unitorˡ-commute = λ {_} {_} {f} → begin
--     -- cannot lift this via `StatelessRel`, since `f` isn't stateless
--     -- this is the only reason, for stateless `f`s this can be lifted
--     Functor.F₁ StatelessRel RelsMonoidal.λ⇒ SRelC.∘ (⊗₁ (SRelC.id , f))
--       ≈⟨ {!!} ⟩
--     f SRelC.∘ Functor.F₁ StatelessRel RelsMonoidal.λ⇒ ∎
--   ; unitorʳ-commute = {!!}
--   ; assoc-commute   = {!!}
--   ; triangle        = begin
--     ⊗₁ (SRelC.id , Functor.F₁ StatelessRel RelsMonoidal.λ⇒) SRelC.∘ Functor.F₁ StatelessRel RelsMonoidal.α⇒
--       ≈⟨ {!!} ⟩ -- by functor laws
--     Functor.F₁ StatelessRel (RelsMonoidal.id RelsMonoidal.⊗₁ RelsMonoidal.λ⇒ RelsMonoidal.∘ RelsMonoidal.α⇒)
--       ≈⟨ Functor.F-resp-≈ StatelessRel RelsMonoidal.triangle ⟩
--     Functor.F₁ StatelessRel (RelsMonoidal.ρ⇒ RelsMonoidal.⊗₁ RelsMonoidal.id)
--       ≈⟨ {!!} ⟩ -- by functor laws
--     ⊗₁ (Functor.F₁ StatelessRel RelsMonoidal.ρ⇒ , SRelC.id) ∎
--   ; pentagon        = {!!} -- same proof as triangle
--   }
--   where open Category.HomReasoning SRelC
--         module SRelC where
--           open Category SRelC public

-- module _ (R : SRel (A ⊎ C) (B ⊎ C)) where
--   open SRel R

--   data tr-rel : SRelType (A ⊎ C) (B ⊎ C) State where
--     tr-[_] : ∀ {s₁ s₂ a b} → rel s₁ a b s₂ → tr-rel s₁ a b s₂
--     _tr-∷_ : ∀ {s₁ s₂ s₃ a b c} → rel s₁ a (inj₂ c) s₂ → tr-rel s₂ (inj₂ c) b s₃ → tr-rel s₁ a b s₃

--   tr : SRel A B
--   tr = record { State = _ ; rel = λ s a b s' → tr-rel s (inj₁ a) (inj₁ b) s' }

-- TracedMonoidal-SRelC : Traced Monoidal-SRelC
-- TracedMonoidal-SRelC = record
--   { symmetric = {!!}
--   ; trace = tr
--   ; vanishing₁ = {!!}
--   ; vanishing₂ = {!!}
--   ; superposing = {!!}
--   ; yanking = {!!}
--   }

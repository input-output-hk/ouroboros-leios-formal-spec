open import Leios.Prelude hiding (id; _>>=_; return; _⊗_)
open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)

open import Prelude.Result
open import CategoricalCrypto hiding (id; _∘_)
open import CategoricalCrypto.Channel.Selection

open import Data.List.Properties
open import Data.Maybe.Properties
open import Data.Product.Properties
module Leios.Linear.Premises (⋯ : SpecStructure 1) (let open SpecStructure ⋯)
  (params : Params)
  (Lhdr Lvote Ldiff : ℕ)
  (splitTxs : List Tx → List Tx × List Tx)
  (validityCheckTime : EndorserBlock → ℕ)
  where

open import Leios.Linear ⋯ params Lhdr Lvote Ldiff splitTxs validityCheckTime
open FFD hiding (_-⟦_/_⟧⇀_)
open GenFFD
open Types params

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

Base≢EB-Role : SlotUpkeep.Base ≢ SlotUpkeep.EB-Role
Base≢EB-Role = λ ()

Base≢VT-Role : SlotUpkeep.Base ≢ SlotUpkeep.VT-Role
Base≢VT-Role = λ ()

π-unique : ∀ {s π} → canProduceEB (LeiosState.slot s) sk-EB (stake s) π → π ≡ (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s)))
π-unique (_ , refl) = refl

instance

  Dec-↝ : ∀ {s u} → (∃[ s'×i ] (s ↝ s'×i × (u ∷ LeiosState.Upkeep s) ≡ LeiosState.Upkeep (proj₁ s'×i))) ⁇
  Dec-↝ {s} {EB-Role} .dec
    with toProposeEB s (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s))) in eq₁
  ... | nothing = no λ where
    (_ , EB-Role {π = π} (p , a) , b) →
      case (π ≟ (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s)))) of λ
        { (yes q) → nothing≢just (trans (sym eq₁) (subst (λ x → toProposeEB s x ≡ just _) q p)) ;
          (no ¬q) → contradiction (π-unique {s} {π} a) ¬q
        }
  ... | just eb
    with ¿ canProduceEB (LeiosState.slot s) sk-EB (stake s) _ ¿
  ... | yes q = yes (_ , EB-Role (eq₁ , q) , refl)
  ... | no ¬q = no λ where
    (_ , EB-Role {π = π} (a , q) , b) →
      case (π ≟ (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s)))) of λ
        { (yes r) → ¬q (subst (λ x → canProduceEB (LeiosState.slot s) sk-EB (stake s) x) r q) ;
          (no ¬r) → contradiction (π-unique {s} {π} q) ¬r
        }
  Dec-↝ {s} {VT-Role} .dec
    with getCurrentEBHash s in eq₂
  ... | nothing = no λ where (_ , VT-Role (p , _) , _) → nothing≢just (trans (sym eq₂) p)
  ... | just ebHash
    with find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) in eq₃
  ... | nothing = no λ where
    (_ , VT-Role (x , y , _) , _) →
      let ji = just-injective (trans (sym x) eq₂)
      in just≢nothing $ trans (sym y) (subst (not-found s) (sym ji) eq₃)
  ... | just (slot' , eb)
    with ¿ VT-Role-premises {s} {eb} {ebHash} {slot'} .proj₁ ¿
  ... | yes p = yes ((rememberVote (addUpkeep s VT-Role) eb , Send (vtHeader [ vote sk-VT (hash eb) ]) nothing) ,
                      VT-Role p , refl)
  ... | no ¬p = no λ where (_ , VT-Role (x , y , p) , _) → ¬p $ subst
                             (λ where (eb , ebHash , slot) → VT-Role-premises {s} {eb} {ebHash} {slot} .proj₁)
                             (subst' {s} x y eq₂ eq₃) (x , y , p)
  Dec-↝ {s} {Base} .dec = no λ where
    (_ , EB-Role _ , x) → Base≢EB-Role (∷-injectiveˡ (trans x refl))
    (_ , VT-Role _ , x) → Base≢VT-Role (∷-injectiveˡ (trans x refl))

open import Prelude.STS.GenPremises
unquoteDecl Roles₂-premises = genPremises Roles₂-premises (quote Roles₂)

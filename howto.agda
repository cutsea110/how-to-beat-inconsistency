module howto where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

strange? : ∀ {x y z} → (x ≡ 3 → y ≡ 5) ⊎ (y ≡ 5 → z ≡ 8)
strange? {y = y} with y ≟ 5
strange? | yes y≡5 = inj₁ (const y≡5)
strange? | no  y≢5 = inj₂ (λ y≡5 → ⊥-elim (y≢5 y≡5))

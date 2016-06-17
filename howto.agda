module howto where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

strange? : ∀ x y z → (x ≡ 3 → y ≡ 5) ⊎ (y ≡ 5 → z ≡ 8)
strange? x y z with y ≟ 5
strange? x y z | yes p = inj₁ (const p)
strange? x y z | no ¬p = inj₂ (λ y≡5 → ⊥-elim (¬p y≡5))

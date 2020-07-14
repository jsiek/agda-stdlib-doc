```
module PropositionalEqualityDoc where
```

```
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl; sym; cong; cong₂; cong-app)

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

private
 variable
  ℓ : Level
  A B C : Set ℓ
  x y z : A
```

# The `_≡_` Data Type (Propositional Equality)


## `_≗_ : (f g : A → B) → Set _` <a name="pointwise-function-equality"></a>

Pointwise equality on functions.
That is, `f ≗ g` is equivalent to `∀ x → f x ≡ g x`.

```
_ : ∀{f g : A → B} → (f ≗ g) iff (∀ x → f x ≡ g x)
_ = (λ f≗g a → f≗g a) , λ fx≡gx a → fx≡gx a
```

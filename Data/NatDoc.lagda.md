```
module NatDoc where
```

```
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Function using (id; _∘_; _↔_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl; sym; cong; cong₂; cong-app)

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)
```

# The `ℕ` Data Type <a name="Nat"></a>

The `ℕ` data type represents the natural numbers, that is, the
integers from zero on up.

```
_ : ℕ
_ = 0

_ : ℕ
_ = 1

_ : ℕ
_ = 2
```

## `zero : ℕ`

The constructor for the natural number `0`.

## `suc : ℕ → ℕ`

The constructor for creating the natural number that is one greater
than the input number.

# Relations on Natural Numbers

## `_≤_ : ℕ → ℕ → Set`

The less-than-or-equal relation on natural numbers. It is
a data type definition with the constructors `z≤n` and `s≤s`.


### `z≤n : ∀ {n} → zero ≤ n`

Zero is less-than or equal to every natural number.

```
_ : 0 ≤ 0
_ = z≤n

_ : 0 ≤ 5
_ = z≤n
```


### `s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n`

Adding `1` to both sides of an inequality preserves the inequality.

```
_ : 1 ≤ 2
_ = s≤s z≤n

_ : 2 ≤ 2
_ = s≤s (s≤s z≤n)

_ : 1 ≤ 3
_ = s≤s z≤n
```

## `_<_ : ℕ → ℕ → Set`

The strictly less-than relation is defined in terms of
less-than-or-equal as follows.

    m < n = suc m ≤ n

```
_ : 0 < 1
_ = s≤s z≤n
```


## `_≥_ : ℕ → ℕ → Set`

The greater-than-or-equal relation is defined in terms
of less-than-or-equal as follows.

    m ≥ n = n ≤ m

```
_ : 0 ≥ 0
_ = z≤n
```

```
_ : 3 ≥ 1
_ = s≤s z≤n
```


## `_>_ : ℕ → ℕ → Set`

The strictly greater-than relation is defined in terms of strictly
less-than as follows.

    m > n = n < m


# Functions on Natural Numbers

## `_+_ : ℕ → ℕ → ℕ`

Addition of two natural numbers.

```
_ : 3 + 2 ≡ 5
_ = refl
```

## `_*_ : ℕ → ℕ → ℕ`

Multiplication of two natural numbers.

```
_ : 3 * 2 ≡ 6
_ = refl
```

## `_∸_ : ℕ → ℕ → ℕ`

Subtraction of two natural numbers.

```
_ : 5 ∸ 3 ≡ 2
_ = refl
```

If the second argument is larger than the first, then
the result is `0`.

```
_ : 3 ∸ 5 ≡ 0
_ = refl
```

In emacs, to type the unicode symbol `∸`, type `\.-`.


## `pred : ℕ → ℕ`

The predecessor function subtracts one from the input, unless
the input is zero, which which case the output is also zero.

```
_ : pred 5 ≡ 4
_ = refl

_ : pred 0 ≡ 0
_ = refl
```

## `_⊔_ : ℕ → ℕ → ℕ`

The maximum function (aka. least upper bound or join) returns the
larger of its two inputs.

```
_ : 2 ⊔ 4 ≡ 4
_ = refl

_ : 4 ⊔ 2 ≡ 4
_ = refl

_ : 2 ⊔ 2 ≡ 2
_ = refl
```

## `_⊔_ : ℕ → ℕ → ℕ`

The minimum function (aka. greatest lower bound or meet) returns the
smaller of its two inputs.

```
_ : 2 ⊓ 4 ≡ 2
_ = refl

_ : 4 ⊓ 2 ≡ 2
_ = refl

_ : 2 ⊓ 2 ≡ 2
_ = refl
```


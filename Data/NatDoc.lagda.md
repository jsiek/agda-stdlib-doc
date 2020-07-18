```
module NatDoc where
```

```
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_; _≥_; _>_; _+_; _*_; _∸_; pred; _⊔_;
    _⊓_; ⌊_/2⌋; _^_; ∣_-_∣)
open import Data.Nat.Properties using (suc-injective; ≤-reflexive; ≤-refl; ≤-trans; ≤-step;
    ≤-pred; m≤m+n; +-suc; +-comm; +-assoc; +-identityˡ; +-identityʳ; +-mono-≤; n≤1+n)
open import Data.Nat.Divisibility
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl; sym; cong; cong₂; cong-app)

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

private
 variable
   x y z : ℕ
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

```
_ : zero ≡ 0
_ = refl
```

## `suc : ℕ → ℕ`

The constructor for creating the natural number that is one greater
than the input number.

```
_ : suc 0 ≡ 1
_ = refl

_ : suc 1 ≡ 2
_ = refl
```


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

## `⌊_/2⌋ : ℕ → ℕ → ℕ`

Divide by `2`, rounding down.

```
_ : ⌊ 1 /2⌋ ≡ 0
_ = refl

_ : ⌊ 2 /2⌋ ≡ 1
_ = refl

_ : ⌊ 3 /2⌋ ≡ 1
_ = refl

_ : ⌊ 4 /2⌋ ≡ 2
_ = refl

_ : ⌊ 5 /2⌋ ≡ 2
_ = refl

_ : ⌊ 6 /2⌋ ≡ 3
_ = refl
```

Be careful to put spaces around the argument, but not between
the `/`, `2`, and `⌋`.

In emacs, to type the unicode symbols `⌊` and `⌋`, type `\lfloor`
and `\rfloor`, respectively. Alternatively, type `\cl` and select
the third or fourth option.

## `_^_ : ℕ → ℕ → ℕ`

Exponentiation of natural numbers.

```
_ : 1 ^ 3 ≡ 1
_ = refl

_ : 2 ^ 3 ≡ 8
_ = refl
```

## `∣_-_∣ : ℕ → ℕ → ℕ`

The distance between two natural numbers.

```
_ : ∣ 5 - 2 ∣ ≡ 3
_ = refl

_ : ∣ 2 - 5 ∣ ≡ 3
_ = refl
```

In emacs, to type the unicode symbol `∣`, type `\mid`.

# Properties of `suc`


## `suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n`

The `suc` function is one-to-one (i.e. injective) so if `suc m ≡ suc
n`, then `m` and `n` must be equal. This equality is also what you get
by subtracting one from both sides.

```
eg6 : suc (x + y) ≡ suc z  →  x + y ≡ z
eg6 {x}{y}{z} prem = suc-injective prem
```

# Properties of less-than-or-equal

## `≤-reflexive : ∀ {n} → n ≡ n → n ≤ n`

Equality implies less-than-or-equal.

```
eg7 : x + 5 ≡ z  →  x + 5 ≤ z
eg7 eq = ≤-reflexive eq
```

## `≤-refl : ∀ {x} → x ≤ x`

Every natural is less-than-or-equal to itself.

```
_ : 42 ≤ 42
_ = ≤-refl
```

## `≤-trans : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k`

The less-than-or-equal relation is transitive. That is,
if `i ≤ j` and `j ≤ k`, then `i ≤ k`.

```
eg8 : x + y ≤ z  →  z ≤ 7  → x + y ≤ 7
eg8 {x}{y}{z} p1 p2 = ≤-trans p1 p2
```

## `≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n`

Adding one on the right side of an inequality preserves the inequality.

```
eg9 : x ≤ 10  → x ≤ 11
eg9 x≤10 = ≤-step x≤10
```

## `≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n`

Subtracting one from both sides of an inequality preserves the inequality.

```
eg10 : suc (2 * x) ≤ suc y  →  2 * x ≤ y
eg10 lt = ≤-pred lt
```

## `m≤m+n : ∀ m n → m ≤ m + n`

Adding any natural number produces a bigger number.

```
eg11 : 5 ≤ 5 + x
eg11 {x} = m≤m+n 5 x
```

## `+-mono-≤ : ∀ {m n o p} → m ≤ o → n ≤ p → m + n ≤ o + p`

The larger the inputs to addition, the larger the result, i.e.,
addition is monotonic with respect to less-than-or-equal.

```
eg12 : 5 + 2 ≤ 6 + 3
eg12 = +-mono-≤ (n≤1+n 5) (n≤1+n 2)
```

## `≤∧≢⇒<`


# Properties of Addition

## `+-suc : ∀ m n → m + suc n ≡ suc (m + n)`

This property moves the `+1` to the front:

    m + (1 + n) ≡ 1 + (m + n)

```
eg2 : 3 * x + (suc (2 * y)) ≡ suc (3 * x  +  2 * y)
eg2 {x}{y} = +-suc (3 * x) (2 * y)
```

It is too bad that `refl` does not prove this equality.  That is
because the definition of addition does pattern-matching on the first
argument.

## `+-comm : ∀ x y → x + y ≡ y + x`

Addition is commutative, i.e., the ordering of the two inputs does not
matter.

```
eg1 : 3 * x + 2 * y  ≡  2 * y + 3 * x
eg1 {x}{y} = +-comm (3 * x) (2 * y)
```


## `+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)`

Addition is associative. In a sequence of two (or more) additions, the
grouping does not matter.

```
eg3 : (3 * x + y) + 2 * z  ≡  3 * x + (y + 2 * z)
eg3 {x}{y}{z} = +-assoc (3 * x) y (2 * z)
```


## `+-identityˡ : ∀ x → 0 + x ≡ x`

Zero plus any number is equal to that number.

```
eg4a : 0 + (2 * x) ≡ 2 * x
eg4a {x} = +-identityˡ (2 * x)
```

In emacs, to type the unicode symbol `ˡ`, type `\^l` then select option 4.

This fact also follows from the definition of addition,
so it can be proved by `refl`.

```
eg4b : 0 + (2 * x) ≡ 2 * x
eg4b {x} = refl
```

## `+-identityʳ : ∀ x → x + 0 ≡ x`

Any number plus zero is equal to that number.

```
eg5 : (2 * x) + 0 ≡ 2 * x
eg5 {x} = +-identityʳ (2 * x)
```

In emacs, to type the unicode symbol `ʳ`, type `\^r` then select option 4.


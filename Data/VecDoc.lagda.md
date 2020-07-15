```
module VecDoc where
```

# Imports and Preliminaries

```
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.Vec.Membership.Propositional.Properties using (∈-lookup)
open import Data.Vec.Relation.Unary.Any using (Any; here; there)
open import Data.Vec.Relation.Unary.All hiding (lookup)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
 variable
  A B C : Set
  x y z : A
  n : ℕ
  xs ys zs : Vec A n
  ℓ : Level
  P : Pred A ℓ

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)
```


# The `Vec` Data Type <a name="Vec"></a>

The `Vec` data type represents a sequence of a specified length.
The data type has two constructors, `[]` and `_∷_`,
described below. 

## `[] : Vec A 0` <a name="nil"></a>


Create an empty vector.

```
_ : Vec ℕ 0
_ = []
```


## `_∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)` <a name="cons"></a>

Creates a new vector from the old one with the given element at the front.

```
_ : Vec ℕ 1
_ = 4 ∷ []

_ : Vec ℕ 2
_ = 7 ∷ 4 ∷ []
```


# Functions on Vectors


## `lookup : ∀ {n} → Vec A n → Fin n → A`

The `lookup` function returns the element at the specified position in
the list.

```
_ : lookup (7 ∷ 4 ∷ 9 ∷ []) (suc zero) ≡ 4
_ = refl
```


# Predicates and Relations on Vectors


## `Any (P : A → Set) : ∀ {n} → Vec A n → Set`

The `Any` predicate holds on a vector when the `P` predicate holds on
at least one of its elements. `Any` is represented by a data type with
two constructors: `here` and `there` that are described below.


For example, within the following list, there is a number (`4`) that
is divisible by `2`.

```
_ : Any (λ x → 2 ∣ x) (7 ∷ 4 ∷ 9 ∷ [])
_ = there (here (divides 2 refl))
```

### `here  : ∀ {n x} {xs : Vec A n} (px : P x) → Any P (x ∷ xs)`



### `there : ∀ {n x} {xs : Vec A n} (pxs : Any P xs) → Any P (x ∷ xs)`



## `All (P : A → Set) : ∀ {n} → Vec A n → Set`

The `All` predicate holds on a vector when the `P` predicate holds on
every one of its elements. `All` is represented by a data type with
two constructors: `[]` and `_∷_` that are described below.

For example, every element in the following list is divisible by `2`.

```
_ : All (λ x → 2 ∣ x) (8 ∷ 4 ∷ 6 ∷ [])
_ = divides 4 refl  ∷  divides 2 refl  ∷  divides 3 refl  ∷  []
```

### `[] : All P []`

The predicate `All P` is vacously true of the empty vector.

```
_ : All (λ x → 2 ∣ x) []
_ = []
```

### `_∷_ : ∀ {n x} {xs : Vec A n} → P x → All P xs → All P (x ∷ xs)`

The predicate `All P` is true of the vector `x ∷ xs` if
both `P x` and `All P xs`.

```
_ : All (λ x → 2 ∣ x) (4 ∷ [])
_ = divides 2 refl  ∷  []
```

## `_∈_ : A → ∀ {n} → Vec A n → Set`

The membership relation holds when the first argument is an element of
the vector.

```
_ : 4 ∈ (7 ∷ 4 ∷ 9 ∷ [])
_ = there (here refl)
```

The membership relation is defined in terms of `Any`, which explains
the appearance of `here` and `there` in the proof of membership.

```
_ : (x ∈ xs) iff (Any (λ y → x ≡ y) xs)
_ = (λ x → x) , (λ x → x)
```


# Properties of Vectors

## `∈-lookup : ∀ {n} i (xs : Vec A n) → lookup xs i ∈ xs`

The `lookup` function returns an element of the vector.

```
_ : lookup (7 ∷ 4 ∷ 9 ∷ []) (suc zero) ∈ (7 ∷ 4 ∷ 9 ∷ [])
_ = ∈-lookup (suc zero) (7 ∷ 4 ∷ 9 ∷ [])
```


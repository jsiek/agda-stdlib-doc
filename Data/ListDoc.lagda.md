
```
module ListDoc where
```

```
open import Data.Nat
open import Data.List
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
```

# List Data Type


The `List` data type is for representing sequences of values
of the same type. The data type has two constructors:

* `[]` creates an empty list,
* `x ∷ xs` creates a list whose first element is `x` and the rest is `xs`.

```
_ : List ℕ
_ = []

_ : List ℕ
_ = 4 ∷ []

_ : List ℕ
_ = 7 ∷ 4 ∷ []
```

# Operations on Lists

## append

The append function `xs ++ ys` takes two lists and produces a third.
The first portion of the result is equal to `xs` and the later part is
equal to `ys`.

```
_ : (7 ∷ 4 ∷ []) ++ (9 ∷ []) ≡ (7 ∷ 4 ∷ 9 ∷ [])
_ = refl
```

## concat

## foldr

The `foldr` function accumulates the result of applying a binary
operator to 1) an element of a list and 2) the result from `foldr` on
the rest of the list. The first parameter of `foldr` is the binary
operator, the second is a value to return if the list is empty, and
the third parameter is the list.

```
_ : foldr _+_ 0 (7 ∷ 4 ∷ 9 ∷ []) ≡ 20
_ = refl
```

```
_ : foldr _++_ [] ((1 ∷ 2 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ (5 ∷ 6 ∷ []) ∷ [])
    ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []
_ = refl    
```

The binary operator may take inputs of different type, but it's result
must has the same type as the second parameter. The following example
uses `foldr` to produce a list that includes all the positive numbers
from the input list.

```
keep-pos : ℕ → List ℕ → List ℕ
keep-pos x xs
    with x
... | 0 = xs
... | suc x' = suc x' ∷ xs
  
_ : foldr keep-pos [] (2 ∷ 0 ∷ 3 ∷ []) ≡ (2 ∷ 3 ∷ [])
_ = refl
```

## foldl



## length

The `length` function computes the length of a list.

```
_ : length (7 ∷ 4 ∷ []) ≡ 2
_ = refl
```

## map

The `map` function applies some other function to every element
of a list, creating a new list.

```
dub : ℕ → ℕ
dub x = x + x

_ : map dub (7 ∷ 4 ∷ []) ≡ 14 ∷ 8 ∷ []
_ = refl
```

## reverse

The `reverse` function takes a list and produces a list whose elements
are in the opposite order. That is, the element at position `i`
in the original list `xs` becomes the element at position `length xs - i - 1`.

```
_ : reverse (7 ∷ 4 ∷ 9 ∷ []) ≡ (9 ∷ 4 ∷ 7 ∷ [])
_ = refl
```


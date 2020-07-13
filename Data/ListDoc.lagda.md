
```
module ListDoc where
```

```
open import Data.Fin using (Fin; zero; suc)
open import Data.List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
```

# List Data Type


The `List` data type is for representing sequences of values of the
same type. The data type has two constructors, `[]` and `_∷_`,
described below.


## `[] : List A`


Create an empty list.

```
_ : List ℕ
_ = []
```


## `_∷_ : A → List A → List A`

Creates a new list from the old one with the given element at the front.

```
_ : List ℕ
_ = 4 ∷ []

_ : List ℕ
_ = 7 ∷ 4 ∷ []
```

# Functions on lists

## `_++_ : List A → List A → List A`

The append function `xs ++ ys` takes two lists and produces a third.
The first portion of the result is equal to `xs` and the later part is
equal to `ys`.

```
_ : (7 ∷ 4 ∷ []) ++ (9 ∷ []) ≡ (7 ∷ 4 ∷ 9 ∷ [])
_ = refl
```

## `concat : List (List A) → List A`

The concatenation function combines a list of lists into a single
list.

```
_ : concat ((1 ∷ 2 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ (5 ∷ 6 ∷ []) ∷ [])
    ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []
_ = refl    
```


## `foldr : (A → B → B) → B → List A → B`

The `foldr` function accumulates the result of applying a binary
operator to 1) an element of a list and 2) the result from `foldr` on
the rest of the list. The first parameter of `foldr` is the binary
operator, the second is a value to return if the list is empty, and
the third parameter is the list.

```
_ : foldr _+_ 0 (7 ∷ 4 ∷ 9 ∷ []) ≡ (7 + (4 + (9 + 0)))
_ = refl
```

We can express `concat` as a `foldr`.

```
_ : foldr _++_ [] ((1 ∷ 2 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ (5 ∷ 6 ∷ []) ∷ [])
    ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []
_ = refl    
```

The binary operator may take inputs of different type, but its result
must have the same type as the second parameter. The following example
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

## `foldl : (A → B → A) → A → List B → A`

The `foldl` accumulates the result of applying a binary operator to
the elements of a list, similar to `foldr`, but does so left-to-right
instead of right to left.

```
_ : foldl _+_ 0 (7 ∷ 4 ∷ 9 ∷ []) ≡ ((0 + 7) + 4) + 9
_ = refl
```

The binary operator may take inputs of different type.  In contrast to
`foldr`, its result type must be the same as the first parameter.
In the next example, we reverse a list using `foldl`, with
`A = List ℕ` and `B = ℕ`.

```
_ : foldl (λ ys x → x ∷ ys) [] (7 ∷ 4 ∷ 9 ∷ []) ≡ (9 ∷ 4 ∷ 7 ∷ [])
_ = refl
```


## `head : List A → Maybe A`

Return the first element of a list, unless it is empty.

```
_ : head (5 ∷ 0 ∷ 3 ∷ []) ≡ just 5
_ = refl
```

```
_ : head {A = ℕ} [] ≡ nothing
_ = refl
```


## `length : List A → ℕ`

The `length` function computes the length of a list.

```
_ : length (7 ∷ 4 ∷ []) ≡ 2
_ = refl
```

```
_ : length {A = ℕ} [] ≡ 0
_ = refl
```

## `lookup : ∀ (xs : List A) → Fin (length xs) → A`

The `lookup` function returns the element at the specified position
in the list. You might expect the second parameter of `lookup` to
have type `ℕ`, but instead it has type `Fin (length xs)`,
which means it's a natural number less than `length xs`.

```
_ : lookup (7 ∷ 4 ∷ 9 ∷ []) zero ≡ 7
_ = refl

_ : lookup (7 ∷ 4 ∷ 9 ∷ []) (suc zero) ≡ 4
_ = refl

_ : lookup (7 ∷ 4 ∷ 9 ∷ []) (suc (suc zero)) ≡ 9
_ = refl
```


## `map : (A → B) → List A → List B`

The `map` function applies some other function to every element
of a list, creating a new list.

```
dub : ℕ → ℕ
dub x = x + x

_ : map dub (7 ∷ 4 ∷ []) ≡ 14 ∷ 8 ∷ []
_ = refl
```


## `reverse : List A → List A`

The `reverse` function takes a list and produces a list whose elements
are in the opposite order. That is, the element at position `i`
in the original list `xs` becomes the element at position `length xs - i - 1`.

```
_ : reverse (7 ∷ 4 ∷ 9 ∷ []) ≡ (9 ∷ 4 ∷ 7 ∷ [])
_ = refl
```


## `tail : List A → Maybe (List A)`

The `tail` function takes a list and returns a list that includes all
but the first element.

```
_ : tail (7 ∷ 4 ∷ 9 ∷ []) ≡ just (4 ∷ 9 ∷ [])
_ = refl
```

```
_ : tail {A = ℕ} [] ≡ nothing
_ = refl
```

# Properties of the functions on lists


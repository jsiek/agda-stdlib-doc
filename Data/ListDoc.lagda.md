
```
module ListDoc where
```

```
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Data.List
open import Data.List.Properties
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Function using (id; _∘_; _↔_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl; sym; cong; cong₂; cong-app)

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)
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

The `length` function is defined in the Agda standard library
in terms of `foldr`, so don't be surprised when your `length`s
are displayed as `foldr`s.

```
_ : foldr (λ x n → suc n) 0 (7 ∷ 4 ∷ []) ≡ 2
_ = refl
```



## `lookup : ∀ (xs : List A) → Fin (length xs) → A`

The `lookup` function returns the element at the specified position
in the list. You might expect the second parameter of `lookup` to
have type `ℕ`, but instead it has type `Fin (length xs)`,
which means it's a natural number less than `length xs`.
Like `ℕ`, the `Fin` data type has constructors named `zero` and `suc`.

```
_ : lookup (7 ∷ 4 ∷ 9 ∷ []) zero ≡ 7
_ = refl

_ : lookup (7 ∷ 4 ∷ 9 ∷ []) (suc zero) ≡ 4
_ = refl

_ : lookup (7 ∷ 4 ∷ 9 ∷ []) (suc (suc zero)) ≡ 9
_ = refl
```

If you have a `ℕ` and a proof that it is less than the length, then
you can convert it to the appropriate `Fin` using `fromℕ<` in the
`Fin` module.

```
i : ℕ
i = suc zero

i<3 : i < 3
i<3 = s≤s (s≤s z≤n)

_ : lookup (7 ∷ 4 ∷ 9 ∷ []) (fromℕ< i<3) ≡ 4
_ = refl
```

However, working with `lookup` and `Fin` is difficult, so I recommend
instead using the alternative lookup function, written `_!_`, in my
[agda-stdlib-aux](https://github.com/jsiek/agda-stdlib-aux) library.


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

If the list is empty, `tail` returns nothing.

```
_ : tail {A = ℕ} [] ≡ nothing
_ = refl
```

# Properties of the functions on lists

```
variable
  ℓ : Level
  A B C : Set ℓ
  x y z : A
  xs ys zs : List A
  ls ms ns : List ℕ
```


## `++-assoc : ∀ xs ys zs → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))`

The append function is associative.

```
f : (xs ++ (y ∷ [])) ++ zs ≡ xs ++ ((y ∷ []) ++ zs)
f {xs = xs}{y}{zs} = ++-assoc xs (y ∷ []) zs
```

## `++-identityˡ : ∀ xs → ([] ++ xs) ≡ xs`

Appending the empty-list to a list returns the same list.

```
h : [] ++ (x ∷ y ∷ []) ≡ (x ∷ y ∷ [])
h {x = x}{y} = ++-identityˡ (x ∷ y ∷ [])
```

In emacs, to type the unicode symbol `ˡ`, type `\^l` then select option 4.

But this fact also follows directly from the definition of append, so
it is provable by `refl`.

```
k : [] ++ (x ∷ y ∷ []) ≡ (x ∷ y ∷ [])
k {x = x}{y} = refl
```


## `++-identityʳ : ∀ xs → (xs ++ []) ≡ xs`

Appending a list to the empty list returns the first list.

```
j : (x ∷ y ∷ []) ++ [] ≡ (x ∷ y ∷ [])
j {x = x}{y} = ++-identityʳ (x ∷ y ∷ [])
```

In emacs, to type the unicode symbol `ʳ`, type `\^r` then select option 4.


## `length-++ : ∀ xs {ys} → length (xs ++ ys) ≡ length xs + length ys`

The length of two appended lists is the sum of their lengths.

```
g : length (xs ++ (y ∷ [])) ≡ (length xs) + length (y ∷ [])
g {xs = xs}{y} = length-++ xs
```

## `map-id : ∀ xs → map id xs ≡ xs`

Mapping the identity function over a list produces the same list.

```
l : map id (x ∷ y ∷ []) ≡ (x ∷ y ∷ [])
l {x = x}{y} = map-id (x ∷ y ∷ []) 
```

## `map-++-commute : ∀ f xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys`

Mapping over the append of two lists is the same as mapping over
the two lists separately and then appending the results.

```
m : map {A = ℕ}{B = ℕ} suc (ls ++  ms) ≡ map suc ls ++ map suc ms 
m {ls = ls}{ms} = map-++-commute suc ls ms
```


## `map-compose : ∀ {g} {f} xs → map (g ∘ f) xs ≡ map g (map f xs)`

Mapping the composition of two functions over a list is the same as
mapping the first function over the list and then mapping the second
function over the resulting list.

```
n : map (dub ∘ suc) ns ≡ map dub (map suc ns)
n {ns = ns} = map-compose ns
```


## `map-cong : ∀ {f g : A → B} → f ≗ g → map f ≗ map g`

The results of two `map`s are equal if the two functions are equal on
all inputs.

```
×2 : ℕ → ℕ
×2 x = 2 * x

o : map dub ns ≡ map ×2 ns
o {ns = ns} = map-cong dub≡×2 ns
  where
  dub≡×2 : ∀ x → x + x ≡ 2 * x
  dub≡×2 x rewrite +-comm x 0 = refl
```

The relation `_≗_` means pointwise equality, so
`f ≗ g` is equivalent to `∀ x → f x ≡ g x`.

```
_ : ∀{f g : A → B} → (f ≗ g) iff (∀ x → f x ≡ g x)
_ = (λ f≗g a → f≗g a) , λ fx≡gx a → fx≡gx a
```


    


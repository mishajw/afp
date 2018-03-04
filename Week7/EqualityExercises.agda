{-# OPTIONS --without-K #-}

-- You are not allowed to use libraries.  You can use everything
-- defined below (without changes).
-- Search for "Exercise".

module EqualityExercises where

data _≡_ {X : Set} : X → X → Set where
 refl : {x : X} → x ≡ x

sym : {A : Set} {a₀ a₁ : A} → a₀ ≡ a₁ → a₁ ≡ a₀
sym refl = refl

trans : {A : Set} {a₀ a₁ a₂ : A} → a₀ ≡ a₁ → a₁ ≡ a₂ → a₀ ≡ a₂
trans refl p = p

cong : {X Y : Set} (f : X → Y) {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong f refl = refl

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + y = y
succ x + y = succ(x + y)

+-assoc : ∀ l m n → (l + m) + n ≡ l + (m + n)
+-assoc zero     m n = refl
+-assoc (succ l) m n = goal
 where
  IH : (l + m) + n ≡ l + (m + n)
  IH = +-assoc l m n
  goal : succ ((l + m) + n) ≡ succ (l + (m + n))
  goal = cong succ IH

data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

_++_ : ∀{X} → List X → List X → List X
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {X} (xs ys zs : List X)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = goal
 where
  IH : (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  IH = ++-assoc xs ys zs
  goal : x ∷ ((xs ++ ys) ++ zs)  ≡  x ∷ (xs ++ (ys ++ zs))
  goal = cong (λ ws → x ∷ ws) IH

data Vec (X : Set) : ℕ → Set where
  []  : Vec X zero
  _∷_ : ∀{n} → X → Vec X n → Vec X (succ n)

hd : {X : Set} {n : ℕ} → Vec X (succ n) → X
hd (x ∷ xs) = x

tl : {X : Set} {n : ℕ} → Vec X (succ n) → Vec X n
tl (x ∷ xs) = xs

data Fin : ℕ → Set where
 zero : {n : ℕ} → Fin (succ n)
 succ : {n : ℕ} → Fin n → Fin (succ n)

fetch : ∀ {X n} → Vec X n → Fin n → X
fetch (x ∷ xs)  zero    = x
fetch (x ∷ xs) (succ i) = fetch xs i

_+++_ : ∀{X m n} → Vec X m → Vec X n → Vec X (m + n)
[]       +++ ys = ys
(x ∷ xs) +++ ys = x ∷ (xs +++ ys)

_≡[_]_ : ∀{X m n} → Vec X m → m ≡ n → Vec X n → Set
xs ≡[ refl ] ys   =   xs ≡ ys

cong-cons : ∀{X m n} (x : X) {xs : Vec X m} {ys : Vec X n} (p : m ≡ n)
          → xs ≡[ p ] ys → x ∷ xs  ≡[ cong succ p ]  x ∷ ys
cong-cons _ refl refl = refl 


+++-assoc : ∀{X} l m n (xs : Vec X l) (ys : Vec X m) (zs : Vec X n)
         → (xs +++ ys) +++ zs  ≡[ +-assoc l m n ]  xs +++ (ys +++ zs)
+++-assoc zero     m n []       ys zs = refl
+++-assoc (succ l) m n (x ∷ xs) ys zs = goal
 where
  IH : (xs +++ ys) +++ zs  ≡[ +-assoc l m n ]  xs +++ (ys +++ zs)
  IH = +++-assoc l m n xs ys zs
  goal : x ∷ ((xs +++ ys) +++ zs)  ≡[ cong succ (+-assoc l m n) ]
         x ∷ (xs +++ (ys +++ zs))
  goal = cong-cons x (+-assoc l m n) IH

-- Exercise. Prove that [] is right neutral for vector concatenation,
-- in the sense that xs +++ [] ≡[ ? ] xs for a suitable filling of the
-- hole.  (Hint: to help with this, formulate and prove a property for
-- addition of natural numbers to fill in the subscript for dependent
-- equality).

zero-r-neutral : ∀ n → n + zero ≡ n
zero-r-neutral zero = refl
zero-r-neutral (succ n) = cong succ (zero-r-neutral n)

r-neutral : ∀{X n} → (xs : Vec X n) → xs +++ [] ≡[ zero-r-neutral n ] xs
r-neutral [] = refl
r-neutral (x ∷ xs) = cong-cons x (zero-r-neutral _) (r-neutral xs)

-- An anonymous module allows you to set hypotheses that can be used
-- by several functions:

module _ 
  (A : Set)
  (B : A → Set)
 where
  _≡⟦_⟧_ : {a₀ a₁ : A} → B a₀ → a₀ ≡ a₁ → B a₁ → Set
  b₀ ≡⟦ refl ⟧ b₁   =   b₀ ≡ b₁

  congd : (f : (a : A) → B a) {a₀ a₁ : A}
        → (p : a₀ ≡ a₁) → f a₀ ≡⟦ p ⟧ f a₁
  congd f refl = refl

  transport : {a₀ a₁ : A} → a₀ ≡ a₁ → B a₀ → B a₁
  transport refl b₀ = b₀

  -- Exercise. Prove within this module that for any p, the function
  -- (transport p) is an isomorphism with inverse (transport (sym p)).

  iso : {a₀ a₁ : A}{b : B a₀} → (p : a₀ ≡ a₁) → transport (sym p) (transport p b) ≡ b
  iso refl = refl
  
  iso' : {a₀ a₁ : A}{b : B a₁} → (p : a₀ ≡ a₁) → transport p (transport (sym p) b) ≡ b
  iso' refl = refl

  _≡'⟦_⟧_ : {a₀ a₁ : A} → B a₀ → a₀ ≡ a₁ → B a₁ → Set
  b₀ ≡'⟦ p ⟧ b₁   =   transport p b₀ ≡ b₁
  
  -- Exercise. Prove that this new dependent equality type is
  -- isomorphic to the first one we defined. You need to define
  -- functions b₀ ≡⟦ p ⟧ b₁ → b₀ ≡'⟦ p ⟧ b₁ and the other way round,
  -- and show that they are mutually inverse.

  de-iso1 : {a b : A} → (f : (a : A) → B a) → (p : a ≡ b) →
                        (f a) ≡⟦ p ⟧ (f b) →
                        (f a) ≡'⟦ p ⟧ (f b)
  de-iso1 f refl p' = congd f refl

  de-iso2 : {a b : A} → (f : (a : A) → B a) → (p : a ≡ b) →
                        (f a) ≡'⟦ p ⟧ (f b) →
                        (f a) ≡⟦ p ⟧ (f b)
  de-iso2 f refl p' = congd f refl

  -- End of module.


-- We consider the alternative dependent equality defined in the
-- anonymous module, specialized to vectors:
_≡'[_]_ : ∀{X m n} → Vec X m → m ≡ n → Vec X n → Set
xs ≡'[ p ] ys   =   _≡'⟦_⟧_ ℕ (Vec _) xs p ys


-- Exercise. Prove associativity of vector concatentation using the
-- alternative definition of dependent equality. Hint: you will need
-- to define an alternative version of cong-cons.

cong-cons' : ∀{X m n} (x : X) {xs : Vec X m} {ys : Vec X n} (p : m ≡ n)
           → xs ≡'[ p ] ys → x ∷ xs  ≡'[ cong succ p ]  x ∷ ys
cong-cons' _ refl refl = refl 

+++-assoc' : ∀{X} l m n (xs : Vec X l) (ys : Vec X m) (zs : Vec X n)
           → (xs +++ ys) +++ zs  ≡'[ +-assoc l m n ]  xs +++ (ys +++ zs)
+++-assoc' zero     m n []       ys zs = refl
+++-assoc' (succ l) m n (x ∷ xs) ys zs = goal
 where
  IH : (xs +++ ys) +++ zs  ≡'[ +-assoc l m n ]  xs +++ (ys +++ zs)
  IH = +++-assoc' l m n xs ys zs
  goal : x ∷ ((xs +++ ys) +++ zs)  ≡'[ cong succ (+-assoc l m n) ]
         x ∷ (xs +++ (ys +++ zs))
  goal = cong-cons' x (+-assoc l m n) IH

infixr 5 _≡_
infixr 5 _≡[_]_
infixr 5 _≡'[_]_
infixl 6 _+_
infixl 6 _++_
infixl 6 _+++_
infixr 7 _∷_

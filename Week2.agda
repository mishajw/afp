data Nat : Set where
  zero : Nat
  suc : Nat → Nat
₀ = zero
₁ = suc ₀
₂ = suc ₁

data Bool : Set where
  true  : Bool
  false : Bool

data istrue : Bool → Set where                   
  ok : istrue true

data List (A : Set) : Set where
  [] : List A
  _::_ : (x : A) (xs : List A) → List A
infixr 5 _::_

[_] : {A : Set} → A → List A
[ x ] = x :: []

length : {A : Set} → List A → Nat
length [] = zero
length (a :: as) = suc (length as)

list₁ = ₀ :: ₁ :: ₂ :: []
list₂ = ₂ :: ₁ :: ₀ :: []
list₃ = ₀ :: ₁ :: []

data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x

≡-cong : {A B : Set} → {a b : A} → (f : A → B) → a ≡ b → (f a) ≡ (f b)
≡-cong f (refl a) = refl (f a)

-- Exercise 0
-- _+:_ : {A : Set} → List A → A → List A
-- [] +: a = a :: []
-- (l :: ls) +: a = l :: ls +: a

_++_ : {A : Set} → List A → List A → List A
(a :: as) ++ bs = a :: (as ++ bs)
[] ++ bs = bs

-- Exercise 1
eq-size-ck : {A B : Set} → List A → List B → Bool
eq-size-ck [] [] = true
eq-size-ck (a :: as) (b :: bs) = eq-size-ck as bs
eq-size-ck _ _ = false

-- list₁=list₂ : Bool
-- list₁=list₂ = ok (eq-size-ck list₁ list₂)

-- Exercise 2
data eq-size-pv {A B : Set} : List A → List B → Set where
  empty-eq : eq-size-pv [] []
  cons-eq : {a : A}{b : B}{as : List A}{bs : List B} →
            eq-size-pv as bs → eq-size-pv (a :: as) (b :: bs)
-- TODO: Is this equivalent?
--  cons-eq : {a b : A} → {as bs : List A} →
--            eq-size-pv (a :: as) (b :: bs) → eq-size-pv as bs

-- TODO: Is this needed?
eq-size-trans : {A B C : Set}
                {as : List A}{bs : List B}{cs : List C} →
                eq-size-pv as bs →
                eq-size-pv bs cs →
                eq-size-pv as cs
eq-size-trans {as = []}{[]}{[]} p q = empty-eq
eq-size-trans {as = a :: as}{b :: bs}{c :: cs} (cons-eq p) (cons-eq q) =
                                               cons-eq (eq-size-trans p q)
eq-size-trans {as = _}{[]}{(c :: cs)} _ ()
eq-size-trans {as = []}{(b :: bs)}{_} ()
eq-size-trans {as = (a :: as)}{[]}{_} ()
eq-size-trans {as = _}{(b :: bs)}{[]} _ ()

eq-size-sym : {A B : Set}
              {as : List A}{bs : List B} →
              eq-size-pv as bs →
              eq-size-pv bs as
eq-size-sym empty-eq = empty-eq
eq-size-sym {as = a :: as} {b :: bs}
            (cons-eq p) = cons-eq (eq-size-sym p)

-- Exercise 3
++[]-size-ck : {A : Set} →
               (as : List A) → istrue (eq-size-ck as (as ++ []))
++[]-size-ck [] = ok
++[]-size-ck (a :: as) = ++[]-size-ck as

++[]-size-pv : {A : Set} → (as : List A) → eq-size-pv as (as ++ [])
++[]-size-pv [] = empty-eq
++[]-size-pv (x :: xs) = cons-eq (++[]-size-pv xs)

-- Exercise 4
++-eq-size-pv : {A B : Set}
                (as : List A) → (bs : List B) → (xs : List A) → (ys : List B) →
                eq-size-pv as bs →
                eq-size-pv xs ys →
                eq-size-pv (as ++ xs) (bs ++ ys)
++-eq-size-pv [] [] xs ys p q = q
++-eq-size-pv [] (b :: bs) xs ys ()
++-eq-size-pv (x :: as) [] xs ys ()
++-eq-size-pv (a :: as) (b :: bs) xs ys (cons-eq p) q =
              cons-eq (++-eq-size-pv as bs xs ys p q)

-- Exercise 5
-- Soundness
eq-size-pv⇒ck : {A B : Set}{as : List A}{bs : List B} →
                eq-size-pv as bs → istrue (eq-size-ck as bs)
eq-size-pv⇒ck {A} {B} {.[]} {.[]} empty-eq = ?
eq-size-pv⇒ck {A} {B} {.(_ :: _)} {.(_ :: _)} (cons-eq prf) = ? -- Why does this work? Can I just say OK?
--eq-size-pv⇒ck (cons-eq p) = eq-size-pv⇒ck p

-- Completeness
eq-size-ck⇒pv : {A B : Set}{as : List A}{bs : List B} →
                istrue (eq-size-ck as bs) → eq-size-pv as bs
eq-size-ck⇒pv {as = []} {bs = []} ok = empty-eq
eq-size-ck⇒pv {as = []} {bs = b :: bs} () 
eq-size-ck⇒pv {as = a :: as} {bs = []} ()
eq-size-ck⇒pv {as = a :: as} {bs = b :: bs} p = cons-eq (eq-size-ck⇒pv p)

-- Exercise 6
++[]-size-≡ : {A : Set} → (as : List A) →
              length as ≡ length (as ++ [])
++[]-size-≡ [] = refl zero
++[]-size-≡ (a :: as) = ≡-cong suc (++[]-size-≡ as)

suc-suc-eq : {a b : Nat} → (suc a) ≡ (suc b) → a ≡ b
suc-suc-eq (refl (suc _)) = refl _

++-eq-size-≡ : {A B : Set}
               (as : List A) → (bs : List B) → (xs : List A) → (ys : List B) →
               length as ≡ length bs →
               length xs ≡ length ys →
               length (as ++ xs) ≡ length (bs ++ ys)
++-eq-size-≡ [] [] _ _ _ q = q
++-eq-size-≡ [] (b :: bs) xs ys ()
++-eq-size-≡ (a :: as) [] xs ys ()
++-eq-size-≡ (a :: as) (b :: bs) xs ys p q =
             ≡-cong suc (++-eq-size-≡ as bs xs ys (suc-suc-eq p) q)

-- Exercise 7

≡-refl : {A : Set} → (a : A) → a ≡ a
≡-refl = refl

≡-sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
≡-sym (refl a) = refl a

≡-trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans (refl .a) (refl a) = refl a

-- Exercise 8
≡-liebniz : {A B : Set}{f : A → B}{a b : A} → a ≡ b → (f a) ≡ (f b)
≡-liebniz {f = f} (refl a) = refl (f a)
-- TODO: Is this the same as ≡-cong?

≡-liebniz2 : {A : Set} → {a b : A} → ({B : Set} → (f : A → B) → (f a) ≡ (f b)) → a ≡ b
≡-liebniz2 p = p (λ z → z)

-- Reverse exercise
-- TODO: Complete
reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

++[]⇒≡ : {A : Set} → (xs : List A) → (xs ++ []) ≡ xs
++[]⇒≡ [] = refl []
++[]⇒≡ (x :: xs) = ≡-cong (_::_ x) (++[]⇒≡ xs)

reverse-extend : {A : Set} → (xs ys : List A) → reverse (xs ++ ys) ≡ (reverse ys ++ reverse xs)
reverse-extend [] ys = ≡-sym (++[]⇒≡ (reverse ys))
reverse-extend (x :: xs) ys = {!!}

-- TODO: What's the name of this?
reverse-reverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse [] = refl []
reverse-reverse (x :: xs) = {!!}


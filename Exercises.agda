module Exercises where

-- # Week 1

-- true and false
data ⊤ : Set where
  ● : ⊤
data ⊥ : Set where

-- a and b
data _^_ (A B : Set) : Set where
  _,_ : A → B → A ^ B
infix 6 _^_

-- a or b
data _v_ (A B : Set) : Set where
  inl : A → A v B
  inr : B → A v B
infix 5 _v_

-- not a
¬ : Set → Set
¬ A = A → ⊥

-- Various Hilbert-style Axioms
proof₁ : {A : Set} → A → A
proof₁ a = a

proof₂ : {A B : Set} → A → (B → A)
proof₂ a _ = a

proof₃ : {A B C : Set} → (A → B → C) → (A → B) → (A → C)
proof₃ f g = λ a → f a (g a)

proof₄₁ : {A B : Set} → (A → B) → (A → ¬ B) → ¬ A
proof₄₁ f g = λ a → g a (f a)

proof₄₂ : {A : Set} → (A → ¬ A) → ¬ A
proof₄₂ f = λ a → f a a

enq : {A : Set} → ⊥ → A
enq ()

proof₅ : {A B : Set} → ¬ A → A → B
proof₅ na a = enq (na a)

ci : {A B : Set} → A → B → A ^ B
ci a b = a , b

cel : {A B : Set} → A ^ B → A
cel (a , _) = a

cer : {A B : Set} → A ^ B → B
cer (_ , b) = b

dil : {A B : Set} → A → A v B
dil a = inl a

dir : {A B : Set} → B → A v B
dir b = inr b

de : {A B C : Set} → (A → C) → (B → C) → A v B → C
de f _ (inl a) = f a
de _ g (inr b) = g b

f : {A B : Set} → B v (¬ A) → A → B
f (inr na) a = enq (na a)
f (inl b) a = b

-- Law of Excluded Middle
postulate lem : {A : Set} → A v ¬ A

-- Double Negation Elimination
postulate dne : {A : Set} → ¬ (¬ A) → A
-- dne nna = (f lem)

-- ((A → ⊥) → ⊥) → A

-- DeMorgan's Laws
postulate demorgan₁ : {A B : Set} → ¬ (A ^ B) → (¬ A) v (¬ B)
-- demorgan₁ naab = na

demorganRev₁ : {A B : Set} → (¬ A) v (¬ B) →  ¬ (A ^ B)
demorganRev₁ (inl na) (a , _) = na a
demorganRev₁ (inr nb) (_ , b) = nb b

demorgan₂ : {A B : Set} → ¬ (A v B) → (¬ A) ^ (¬ B)
demorgan₂ naob = (λ a → naob (inl a)) , (λ b → naob (inr b))

demorganRev₂ : {A B : Set} → (¬ A) ^ (¬ B) → ¬ (A v B)
demorganRev₂ (na , _) (inl a) = na a
demorganRev₂ (_ , nb) (inr b) = nb b

-- Double Negation Introduction
dni : {A : Set} → A → ¬ (¬ A)
dni a na = na a

-- Triple Negation Elimination
tne : {A : Set} → ¬ (¬ (¬ A)) → ¬ A
tne = dne

-- Equivalence of DNE and LEM
postulate lemToDne : {A : Set} → A v ¬ A → (¬ (¬ A) → A)

postulate dneTolem : {A : Set} → (¬ (¬ A) → A) → A v ¬ A

-- Pierce's Law

postulate piercesLaw : {A B : Set} → ((A → B) → A) → A

-- # Week 2

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
  _∷_ : (x : A) (xs : List A) → List A
infixr 5 _∷_

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

length : {A : Set} → List A → Nat
length [] = zero
length (a ∷ as) = suc (length as)

list₁ = ₀ ∷ ₁ ∷ ₂ ∷ []
list₂ = ₂ ∷ ₁ ∷ ₀ ∷ []
list₃ = ₀ ∷ ₁ ∷ []

data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x
infix 0 _≡_

≡-cong : {A B : Set} → {a b : A} → (f : A → B) → a ≡ b → (f a) ≡ (f b)
≡-cong f (refl a) = refl (f a)

-- ## Exercise 0
-- _+:_ : {A : Set} → List A → A → List A
-- [] +: a = a ∷ []
-- (l ∷ ls) +: a = l ∷ ls +: a

_++_ : {A : Set} → List A → List A → List A
(a ∷ as) ++ bs = a ∷ (as ++ bs)
[] ++ bs = bs

-- ## Exercise 1
eq-size-ck : {A B : Set} → List A → List B → Bool
eq-size-ck [] [] = true
eq-size-ck (a ∷ as) (b ∷ bs) = eq-size-ck as bs
eq-size-ck _ _ = false

-- list₁=list₂ : Bool
-- list₁=list₂ = ok (eq-size-ck list₁ list₂)

-- ## Exercise 2
data eq-size-pv {A B : Set} : List A → List B → Set where
  empty-eq : eq-size-pv [] []
  cons-eq : {a : A}{b : B}{as : List A}{bs : List B} →
            eq-size-pv as bs → eq-size-pv (a ∷ as) (b ∷ bs)
-- TODO: Is this equivalent?
--  cons-eq : {a b : A} → {as bs : List A} →
--            eq-size-pv (a ∷ as) (b ∷ bs) → eq-size-pv as bs

-- TODO: Is this needed?
eq-size-trans : {A B C : Set}
                {as : List A}{bs : List B}{cs : List C} →
                eq-size-pv as bs →
                eq-size-pv bs cs →
                eq-size-pv as cs
eq-size-trans {as = []}{[]}{[]} p q = empty-eq
eq-size-trans {as = a ∷ as}{b ∷ bs}{c ∷ cs} (cons-eq p) (cons-eq q) =
                                               cons-eq (eq-size-trans p q)
eq-size-trans {as = _}{[]}{(c ∷ cs)} _ ()
eq-size-trans {as = []}{(b ∷ bs)}{_} ()
eq-size-trans {as = (a ∷ as)}{[]}{_} ()
eq-size-trans {as = _}{(b ∷ bs)}{[]} _ ()

eq-size-sym : {A B : Set}
              {as : List A}{bs : List B} →
              eq-size-pv as bs →
              eq-size-pv bs as
eq-size-sym empty-eq = empty-eq
eq-size-sym {as = a ∷ as} {b ∷ bs}
            (cons-eq p) = cons-eq (eq-size-sym p)

-- ## Exercise 3
++[]-size-ck : {A : Set} →
               (as : List A) → istrue (eq-size-ck as (as ++ []))
++[]-size-ck [] = ok
++[]-size-ck (a ∷ as) = ++[]-size-ck as

++[]-size-pv : {A : Set} → (as : List A) → eq-size-pv as (as ++ [])
++[]-size-pv [] = empty-eq
++[]-size-pv (x ∷ xs) = cons-eq (++[]-size-pv xs)

-- ## Exercise 4
++-eq-size-pv : {A B : Set}
                (as : List A) → (bs : List B) → (xs : List A) → (ys : List B) →
                eq-size-pv as bs →
                eq-size-pv xs ys →
                eq-size-pv (as ++ xs) (bs ++ ys)
++-eq-size-pv [] [] xs ys p q = q
++-eq-size-pv [] (b ∷ bs) xs ys ()
++-eq-size-pv (x ∷ as) [] xs ys ()
++-eq-size-pv (a ∷ as) (b ∷ bs) xs ys (cons-eq p) q =
              cons-eq (++-eq-size-pv as bs xs ys p q)

-- ## Exercise 5
-- Soundness
eq-size-pv⇒ck : {A B : Set}{as : List A}{bs : List B} →
                eq-size-pv as bs → istrue (eq-size-ck as bs)
eq-size-pv⇒ck empty-eq = ok
eq-size-pv⇒ck (cons-eq p) = eq-size-pv⇒ck p

-- Completeness
eq-size-ck⇒pv : {A B : Set}{as : List A}{bs : List B} →
                istrue (eq-size-ck as bs) → eq-size-pv as bs
eq-size-ck⇒pv {as = []} {bs = []} ok = empty-eq
eq-size-ck⇒pv {as = []} {bs = b ∷ bs} () 
eq-size-ck⇒pv {as = a ∷ as} {bs = []} ()
eq-size-ck⇒pv {as = a ∷ as} {bs = b ∷ bs} p = cons-eq (eq-size-ck⇒pv p)

-- ## Exercise 6
++[]-size-≡ : {A : Set} → (as : List A) →
              length as ≡ length (as ++ [])
++[]-size-≡ [] = refl zero
++[]-size-≡ (a ∷ as) = ≡-cong suc (++[]-size-≡ as)

suc-suc-eq : {a b : Nat} → (suc a) ≡ (suc b) → a ≡ b
suc-suc-eq (refl (suc _)) = refl _

++-eq-size-≡ : {A B : Set}
               (as : List A) → (bs : List B) → (xs : List A) → (ys : List B) →
               length as ≡ length bs →
               length xs ≡ length ys →
               length (as ++ xs) ≡ length (bs ++ ys)
++-eq-size-≡ [] [] _ _ _ q = q
++-eq-size-≡ [] (b ∷ bs) xs ys ()
++-eq-size-≡ (a ∷ as) [] xs ys ()
++-eq-size-≡ (a ∷ as) (b ∷ bs) xs ys p q =
             ≡-cong suc (++-eq-size-≡ as bs xs ys (suc-suc-eq p) q)

-- ## Exercise 7

≡-refl : {A : Set} → (a : A) → a ≡ a
≡-refl = refl

≡-sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
≡-sym (refl a) = refl a

≡-trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans (refl .a) (refl a) = refl a

-- ## Exercise 8
-- TODO: Is this an incorrect definition?
-- ≡-liebniz : {A B : Set}{f : A → B}{a b : A} → a ≡ b → (f a) ≡ (f b)
-- ≡-liebniz {f = f} (refl a) = refl (f a)

≡-liebniz : {A : Set} → {a b : A} → ({B : Set} → (f : A → B) → (f a) ≡ (f b)) → a ≡ b
≡-liebniz p = p (λ z → z)

-- ## Reverse exercise
rev : {A : Set} → List A → List A
rev [] = []
rev (x ∷ xs) = rev xs ++ [ x ]

++[]⇒≡ : {A : Set} → (xs : List A) → (xs ++ []) ≡ xs
++[]⇒≡ [] = refl []
++[]⇒≡ (x ∷ xs) = ≡-cong (_∷_ x) (++[]⇒≡ xs)

++-comm : {A : Set}{as bs cs : List A} → (as ++ (bs ++ cs)) ≡ ((as ++ bs) ++ cs)
++-comm {as = []} {bs} {cs} = refl (bs ++ cs)
++-comm {as = a ∷ as} {bs} {cs} = ≡-cong (_∷_ a) (++-comm {as = as} {bs} {cs})
-- TODO: How to make this more elegant?

rev-extend : {A : Set} → (xs ys : List A) → rev (xs ++ ys) ≡ (rev ys ++ rev xs)
rev-extend [] ys = ≡-sym (++[]⇒≡ (rev ys))
rev-extend (x ∷ xs) ys = ≡-sym (≡-trans p0 p1) where
-- ≡-sym (≡-cong (λ z → z ++ [ x ]) (++-comm)) where
  p0 : (rev ys ++ (rev xs ++ [ x ])) ≡ ((rev ys ++ rev xs) ++ [ x ])
  p0 = ++-comm {as = rev ys}
  p1 : ((rev ys ++ rev xs) ++ [ x ]) ≡ (rev (xs ++ ys) ++ [ x ])
  p1 = ≡-sym (≡-cong (λ z → z ++ [ x ]) (rev-extend xs ys))

rev-involution : {A : Set} → (xs : List A) → rev (rev xs) ≡ xs
rev-involution [] = refl []
rev-involution (x ∷ xs) = ≡-trans p0 (≡-cong (_∷_ x) (rev-involution xs)) where
  p0 : (rev (rev xs ++ [ x ])) ≡ (x ∷ rev (rev xs))
  p0 = rev-extend (rev xs) [ x ]

-- # Week 3

-- ## Fast reverse
rev-++ : {A : Set} → (xs ys : List A) → List A
rev-++ [] ys = ys
rev-++ (x ∷ xs) ys = rev-++ xs (x ∷ ys)

fast-rev : {A : Set} → List A → List A
fast-rev xs = rev-++ xs []

rev≡fast-rev : {A : Set}{xs : List A} → rev xs ≡ fast-rev xs
rev≡fast-rev {xs = []} = refl []
rev≡fast-rev {xs = x ∷ xs} =
             (≡-trans
               (≡-trans
                 (≡-trans
                   (p0 x xs)
                   (p1 x xs))
                 (p2 x xs))
               (p3 xs [] [ x ])) where

  p0 : {A : Set} → (a : A)(as : List A) → rev (a ∷ as) ≡ rev as ++ [ a ]
  p0 a as = refl (rev (a ∷ as))

  p1 : {A : Set} → (a : A)(as : List A) → rev as ++ [ a ] ≡ fast-rev as ++ [ a ]
  p1 a as = ≡-cong (λ z → z ++ [ a ]) (rev≡fast-rev {xs = as})

  p2 : {A : Set} → (a : A)(as : List A) → fast-rev as ++ [ a ] ≡ (rev-++ as []) ++ [ a ]
  p2 a as = refl _

  p3 : {A : Set} → (as bs cs : List A) → (rev-++ as bs) ++ cs ≡ rev-++ as (bs ++ cs)
  p3 [] bs cs = refl (bs ++ cs)
  p3 (a ∷ as) bs cs = p3 as (a ∷ bs) cs


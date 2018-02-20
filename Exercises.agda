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

_+_ : Nat → Nat → Nat
zero + n = n
(suc m) + n = suc (m + n)

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

data Monoid : (A : Set) → A → (A → A → A) → Set where
  monoid : {A : Set}(Empty : A)(Concat : A → A → A) →
           ((a : A) → Concat Empty a ≡ a) →
           ((a : A) → Concat a Empty ≡ a) →
           ((a b c : A) → Concat a (Concat b c) ≡ Concat (Concat a b) c) →
           Monoid A Empty Concat

data CommMonoid : {A : Set}{E : A}{C : A → A → A}(m : Monoid A E C) → Set where
  comm-monoid : {A : Set}{E : A}{C : A → A → A}(m : Monoid A E C) →
                (∀ a b → C a b ≡ C b a) →
                CommMonoid m

-- ## Show that (Nat, +, 0) is a commutative monoid
nat-l-empty : ∀ a → zero + a ≡ a
nat-l-empty = refl
nat-r-empty : ∀ a → a + zero ≡ a
nat-r-empty zero = refl zero
nat-r-empty (suc a) = ≡-cong suc (nat-r-empty a)
nat-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c
nat-assoc zero b c = refl (b + c)
nat-assoc (suc a) b c = ≡-cong suc (nat-assoc a b c)

mNat : Monoid Nat ₀ _+_
mNat = monoid ₀ _+_ nat-l-empty nat-r-empty nat-assoc

+comm : ∀ a b → a + b ≡ b + a
+comm zero zero = refl zero
+comm zero (suc b) = ≡-cong suc (+comm zero b)
+comm (suc a) zero = ≡-cong suc (+comm a zero)
+comm (suc a) (suc b) = ≡-cong suc (≡-trans (+comm a (suc b)) (p0 b a)) where
  p0 : ∀ a b → (suc a) + b ≡ a + (suc b)
  p0 zero b = refl (suc b)
  p0 (suc a) b = ≡-cong suc (p0 a b)

cmNat : CommMonoid mNat
cmNat = comm-monoid mNat +comm

-- ## Define integers
{-
mutual
  data IntZero : Set where
    izero' : IntZero
  data IntPos : Set where
    iposone : IntZero → IntPos
    ipos' : IntPos → IntPos
  data IntNeg : Set where
    inegone : IntZero → IntNeg
    ineg' : IntNeg → IntNeg
  data Int : Set where
    izero : IntZero → Int
    ipos : IntPos → Int
    ineg : IntNeg → Int

_+i_ : Int → Int → Int
izero _ +i b = b
a +i izero _ = a
ipos a +i ipos b = {!!}
ipos a +i ineg b = {!!}
ineg a +i b = {!!}


data Int : Set where
  izero : Int
  isuc : Int → Int
  ipred : Int → Int

₀ᵢ = izero
₁ᵢ = isuc ₀ᵢ
₂ᵢ = isuc ₁ᵢ
-₁ᵢ = ipred izero
-₂ᵢ = ipred -₁ᵢ

Int = Nat × Nat

3 = (3, 0) (4, 1)
-1 = (0, 1)

(0, 0) (1, 1)

-- Define + and - for integers
_+ᵢ_ : Int → Int → Int
izero +ᵢ b = b
isuc a +ᵢ b = isuc (a +ᵢ b)
ipred a +ᵢ b = ipred (a +ᵢ b)

_-ᵢ_ : Int → Int → Int
a -ᵢ izero = a
a -ᵢ isuc b = ipred (a -ᵢ b)
a -ᵢ ipred b = isuc (a -ᵢ b)

-- Show that (Int, +, 0, -) is an abelian group
data Abelian : (A : Set) → A → (A → A → A) → (A → A → A) → Set where
  abelian : (A : Set) → (Id : A) → (_∘_ : A → A → A) → (_∘'_ : A → A → A) →
            -- Is there a way to express closure/totality?
            (MA : Monoid A Id _∘_) →
            CommMonoid MA →
            -- This isn't right
            (inverse-elem : ∀ a b → a ∘ b ≡ Id) →
            Abelian A Id _∘_ _∘'_

∀ b → Σ (Int) (λ a → b o a ≡ Id)

aInt : Abelian Int izero _+ᵢ_ _-ᵢ_
aInt = abelian Int izero _+ᵢ_ _-ᵢ_ mInt cmInt inverse-elem where
  r-id : ∀ a → a +ᵢ izero ≡ a
  r-id izero = refl izero
  r-id (isuc a) = ≡-cong isuc (r-id a)
  r-id (ipred a) = ≡-cong ipred (r-id a)

  assoc : ∀ a b c → a +ᵢ (b +ᵢ c) ≡ (a +ᵢ b) +ᵢ c
  assoc izero b c = refl (b +ᵢ c)
  assoc (isuc a) b c = ≡-cong isuc (assoc a b c)
  assoc (ipred a) b c = ≡-cong ipred (assoc a b c)

  comm : ∀ a b → a +ᵢ b ≡ b +ᵢ a
  comm izero b = ≡-sym (r-id b)
  comm (isuc a) b = {!!}
  comm (ipred a) b = {!!} where
    p0 : (x y : Int) → (isuc x) +ᵢ y ≡ x +ᵢ (isuc y)
    p0 izero b = refl (isuc b)
    p0 (isuc a) b = ≡-cong isuc (p0 a b)
    p0 (ipred a) b = {!!}

  {-
  comm a izero = r-id a
  comm a (isuc b) = {!!}
  comm a (ipred b) = {!!}
  -}

  mInt : Monoid Int izero _+ᵢ_
  mInt = monoid izero _+ᵢ_ refl r-id assoc where

  cmInt : CommMonoid mInt
  cmInt = comm-monoid mInt comm where

  inverse-elem : ∀ a b → a +ᵢ b ≡ izero
  inverse-elem = {!!}
-}

-- Define multiplication for Nat
_*_ : Nat → Nat → Nat
zero * b = zero
(suc a) * b = b + (a * b)

-- Show that (Nat, +, 0, *, 1) forms a semi-ring
data Semiring : (A : Set) →
                (plus-unit : A) →
                (plus : A → A → A) →
                (mult-unit : A) →
                (mult : A → A → A) →
                Set where
  semiring : (A : Set) →
             (plus-unit : A) →
             (plus : A → A → A) →
             (mult-unit : A) →
             (mult : A → A → A) →
             (PlusM : Monoid A plus-unit plus) →
             (PlusCM : CommMonoid PlusM) →
             (MultM : Monoid A mult-unit mult) →
             (l-distr : ∀ a b c → mult a (plus b c) ≡ plus (mult a b) (mult a c)) →
             (r-distr : ∀ a b c → mult (plus a b) c ≡ plus (mult a c) (mult b c)) →
             (l-annih : ∀ a → mult a plus-unit ≡ plus-unit) →
             (r-annih : ∀ a → mult plus-unit a ≡ plus-unit) →
             Semiring A plus-unit plus mult-unit mult

mutual
  nat-l-distr : ∀ a b c → a * (b + c) ≡ (a * b) + (a * c)
  nat-l-distr zero b c = refl zero
  nat-l-distr (suc a) b c = ≡-sym (≡-trans (p0 a b c) (p1 a b c)) where
    p0 : ∀ a b c → (b + (a * b)) + (c + (a * c)) ≡ (b + c) + ((a * b) + (a * c))
    p0 a b c = {!!}

    p1 : ∀ a b c → (b + c) + ((a * b) + (a * c)) ≡ (b + c) + (a * (b + c))
    p1 a b c = ≡-cong (_+_ (b + c)) (≡-sym (nat-l-distr a b c))

  nat-r-distr : ∀ a b c → (a + b) * c ≡ (a * c) + (b * c)
  nat-r-distr zero b c = refl (b * c)
  nat-r-distr (suc a) b c = {!!}

  nat-*comm : ∀ a b c → a * (b * c) ≡ (a * b) * c
  nat-*comm zero b c = refl zero
  nat-*comm (suc a) b c =
        ≡-sym
          (≡-trans
            (≡-trans
              (p0 a b c)
              (p1 a b c))
            (refl ((b * c) + (a * (b * c))))) where

    p0 : ∀ a b c → (b + (a * b)) * c ≡ (b * c) + ((a * b) * c)
    p0 a b c = nat-r-distr b (a * b) c

    p1 : ∀ a b c → (b * c) + ((a * b) * c) ≡ (b * c) + (a * (b * c))
    p1 a b c = ≡-cong (_+_ (b * c)) (≡-sym (nat-*comm a b c))


mNat-mult : Monoid Nat ₁ _*_
mNat-mult = monoid ₁ _*_ nat-r-empty r*-empty nat-*comm where
  r*-empty : ∀ a → a * ₁ ≡ a
  r*-empty zero = refl zero
  r*-empty (suc a) = ≡-cong suc (r*-empty a)

srNat : Semiring Nat ₀ _+_ ₁ _*_
srNat = semiring Nat ₀ _+_ ₁ _*_
                 mNat cmNat mNat-mult nat-l-distr nat-r-distr l-annih r-annih where
      l-annih : ∀ a → a * ₀ ≡ ₀
      l-annih zero = refl zero
      l-annih (suc a) = l-annih a
      r-annih : ∀ a → ₀ * a ≡ ₀
      r-annih a = refl zero

-- # Week 5

-- ## Definition of ∃

data ∑ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → (b : B a) → ∑ A B
infixr 4 _,_

syntax ∑ A (λ a → B) = ∃[ a of A ] B
witness : {A : Set}{B : A → Set} → ∃[ a of A ] (B a) → A
witness (a , b) = a
proof : {A : Set}{B : A → Set} → (p : ∃[ a of A ] (B a)) → (B (witness p))
proof (a , b) = b

-- ## Evenness

-- ### Test
_even : Nat → Bool
zero even = true
(suc zero) even = false
(suc (suc a)) even = a even

-- ### Proof
data _evenₚ : Nat → Set where
  z-even : zero evenₚ
  ss-even : {a : Nat} → a evenₚ → (suc (suc a)) evenₚ

-- ### Completeness and Soundness
even-compl : ∀ a → istrue (a even) → a evenₚ
even-compl zero p = z-even
even-compl (suc zero) ()
even-compl (suc (suc a)) p = ss-even (even-compl a p)

even-sound : ∀ a → a evenₚ → istrue (a even)
even-sound zero z-even = ok
even-sound (suc (suc a)) (ss-even p) = even-sound a p

  
suc-mv : ∀ a b → a + (suc b) ≡ suc (a + b)
suc-mv zero zero = refl (suc zero)
suc-mv zero (suc b) = refl (suc (suc b))
suc-mv (suc a) zero = ≡-cong suc (suc-mv a zero)
suc-mv (suc a) (suc b) = ≡-cong suc (suc-mv a (suc b))


-- ### Prove that n is even iff "∃ m. m + m ≡ n"
even-sum₁ : ∀ n → n evenₚ → ∃[ m of Nat ] (m + m ≡ n)
even-sum₁ zero z-even = zero , (refl zero)
even-sum₁ (suc (suc n)) (ss-even p) = (suc w) , ≡-cong suc (p1 w n (proof ih)) where
  ih = even-sum₁ n p
  w = witness ih

  p1 : ∀ a b → a + a ≡ b → a + (suc a) ≡ suc b
  p1 a b p = ≡-trans (suc-mv a a) (≡-cong suc p)

even-sum₂ : ∀ n → ∃[ m of Nat ] (m + m ≡ n) → n evenₚ
even-sum₂ zero (zero , _) = z-even
even-sum₂ zero (suc _ , ())
even-sum₂ (suc n) (zero , ())
even-sum₂ (suc .(m + suc m)) (suc m , refl .(suc (m + suc m))) = p0 m where
  mutual
    double : ∀ m → (m + m) evenₚ
    double zero = z-even
    double (suc m) = p0 m
  
    inc-two : ∀ a → a evenₚ → (suc (suc a)) evenₚ
    inc-two a p = ss-even p

    even-≡ : ∀ a b → a ≡ b → a evenₚ → b evenₚ
    even-≡ zero zero eq ev = ev
    even-≡ zero (suc b) ()
    even-≡ (suc zero) _ _ ()
    even-≡ (suc (suc a)) .(suc (suc a)) (refl .(suc (suc a))) (ss-even ev) = ss-even ev

    p0 : ∀ m → suc (m + suc m) evenₚ
    p0 m = even-≡
      (suc (suc (m + m)))
      (suc (m + suc m))
      (≡-cong
        suc
        (≡-sym (suc-mv m m)))
      (inc-two (m + m) (double m))

-- ## Product

--data _≡'_ : {A B : Set} → (f : A → B) → (g : A → B) → Set where
--  refl' : {A B : Set}(f : A → B) → f ≡' f
--  with-pv : {A B : Set} → (f g : A → B) → (∀ x → f x ≡ g x) → f ≡' g

postulate func-≡ : {A B : Set} → (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g
postulate func-≡-rev : {A B : Set} → (f g : A → B) → f ≡ g → (∀ x → f x ≡ g x) 

-- ### Function composition
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

-- ### Pairs
data _×_ : (A B : Set) → Set where
  _,_ : {A B : Set} → (a : A) → (b : B) → A × B
fst : {A B : Set} → (A × B) → A
fst (a , b) = a
snd : {A B : Set} → (A × B) → B
snd (a , b) = b

-- ### Proof
product-pv : {X A A' : Set} →
             (f : X → A) →
             (f' : X → A') →
             ∃[ g of (X → A × A') ]
               ((
                          (
                            (f ≡ (fst ∘ g)) ×
                            (f' ≡ (snd ∘ g))
                          ) ×
                          (
                            (g' : X → A × A') →
                            (f ≡ (fst ∘ g')) →
                            (f' ≡ (snd ∘ g')) →
                            (g ≡ g')
                          )))
product-pv {X}{A}{A'} f f' = g , ((refl f) , (refl f')) , g-uniq where
  g : X → A × A'
  g x = (f x) , (f' x) -- existential witness

  prod-func : {X A A' : Set} → (X → A) → (X → A') → (X → A × A')
  prod-func f g = λ x → f x , g x

  unprod-≡ : (g : X → A × A') → (f ≡ (fst ∘ g)) → (f' ≡ (snd ∘ g)) → (prod-func f f') ≡ g
  unprod-≡ g p p' = func-≡ (prod-func f f') g (λ x → {!refl (g x)!})


  g-uniq : (g' : X → A × A') → -- existential proof
           f ≡ (fst ∘ g') →
           f' ≡ (snd ∘ g') →
           g ≡ g'
  g-uniq g' p p' = ≡-trans (≡-sym (unprod-≡ (prod-func f f') (refl f) (refl f'))) (unprod-≡ g' p p')


-- # Week 6

data _≤p_ : Nat → Nat → Set where
  pzero : ∀{n} → zero ≤p n
  psuc : ∀{n m} → n ≤p m → (suc n) ≤p (suc m)

module vec where
  data Vec (A : Set) : Nat → Set where
    [] : Vec A zero
    _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

  head : ∀{A}{n} → Vec A (suc n) → A
  head (x ∷ _) = x

  tail : ∀{A}{n} → Vec A (suc n) → Vec A n
  tail (_ ∷ xs) = xs

  append : ∀{A}{n} → Vec A n → A → Vec A (suc n)
  append [] x = x ∷ []
  append (x ∷ xs) x' = x ∷ (append xs x')

  extend : ∀{A}{n m} → Vec A n → Vec A m → Vec A (n + m)
  extend [] ys = ys
  extend (x ∷ xs) ys = x ∷ (extend xs ys)

  reverse : ∀{A}{n} → Vec A n → Vec A n
  reverse [] = []
  reverse (x ∷ xs) = append xs x

  map : ∀{A B}{n} → (A → B) → Vec A n → Vec B n
  map f [] = []
  map f (x ∷ xs) = (f x) ∷ map f xs

  fold : ∀{A B : Set}{n} → (B → A → B) → B → Vec A n → B
  fold f b [] = b
  fold f b (x ∷ xs) = f (fold f b xs) x

  prod : ∀{A B C}{n m} → (A → B → C) → Vec A n → Vec B m → Vec C (n * m)
  prod f [] _ = []
  prod f (x ∷ xs) ys = extend (map (f x) ys) (prod f xs ys)

  data Fin : Nat → Set where
    fzero : {n : Nat} → Fin (suc n)
    fsuc : {n : Nat} → Fin n → Fin (suc n)

  _~_ : ∀{A}{n} → Vec A n → Fin n → A
  [] ~ ()
  (x ∷ xs) ~ fzero = x
  (x ∷ xs) ~ fsuc n = xs ~ n

  _~'_given_ : ∀{A}{n} → Vec A n → (m : Nat) → (suc m) ≤p n → A
  [] ~' _ given ()
  (x ∷ xs) ~' zero given p = x
  (x ∷ xs) ~' suc n given (psuc p) = xs ~' n given p

module singleton where
  data Singleton : Nat → Set where
    sing : {n : Nat} → Singleton n

  _+ₛ_ : ∀{n m} → Singleton n → Singleton m → Singleton (n + m)
  sing{n} +ₛ sing{m} = sing{n + m}

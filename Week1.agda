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

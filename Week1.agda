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

proof₁ : {A : Set} → A → A
proof₁ a = a

proof₂ : {A B : Set} → A → (B → A)
proof₂ a _ = a

proof₃ : {A B C D : Set} → (A → B → C) → (A → B) → (A → C)
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

-- demorgan₁ : {A B : Set} → ¬ (A ^ B) → (¬ A) v (¬ B)
-- demorgan₁ f = λ a

demorgan₁rev : {A B : Set} → (¬ A) v (¬ B) →  ¬ (A ^ B)
demorgan₁rev (inl na) (a , _) = na a
demorgan₁rev (inr nb) (_ , b) = nb b

demorgan₂ : {A B : Set} → ¬ (A v B) → (¬ A) ^ (¬ B)
demorgan₂ naob = (λ a → naob (inl a)) , (λ b → naob (inr b))

demorgan₂rev : {A B : Set} → (¬ A) ^ (¬ B) → ¬ (A v B)
demorgan₂rev (na , _) (inl a) = na a
demorgan₂rev (_ , nb) (inr b) = nb b

module Week1 where

data N : Set where
  zero : N
  succ : N → N

_+_ : N → N → N
zero + m = m
succ n + m = succ (n + m)

data _even : N → Set where
  ZERO : zero even
  STEP : ∀ {x} → x even → succ (succ x) even

proof₁ : succ (succ (succ (succ zero))) even
proof₁ = STEP (STEP ZERO)

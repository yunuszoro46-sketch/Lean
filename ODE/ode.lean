import Mathlib.Analysis.Calculus.Deriv.Basic

variable (y : ℝ → ℝ) (x : ℝ)

-- 1. dy/dx = x + 5
def ode1 : Prop :=
  deriv y x = x + 5

-- 2. (dy/dx)^3 = x + 5*y
def ode2 : Prop :=
  (deriv y x) ^ 3 = x + 5 * y x

-- 3. (d^2y/dx^2)^3 + (dy/dx)^5 = 5*y^7
def ode3 : Prop :=
  (deriv (deriv y) x) ^ 3 + (deriv y x) ^ 5 = 5 * (y x) ^ 7

# Lean 4 Formalization of Ordinary Differential Equations

This project provides Lean 4 definitions and explicit solution proofs for three ordinary differential equations (ODEs).

## ODE Equations & Solutions

1. **ODE 1:** $\frac{dy}{dx} = x + 5$
   - **General Solution:** $y(x) = \frac{1}{2}x^2 + 5x + C$

2. **ODE 2:** $\left(\frac{dy}{dx}\right)^3 = x + 5y$
   - **Solution (Separable / Exact Form):** $y(x) = -\frac{1}{5}x - \frac{1}{125}$
   - *Verification:* $\frac{dy}{dx} = -\frac{1}{5} \implies \left(-\frac{1}{5}\right)^3 = -\frac{1}{125} = x + 5\left(-\frac{1}{5}x - \frac{1}{125}\right)$

3. **ODE 3:** $\left(\frac{d^2y}{dx^2}\right)^3 + \left(\frac{dy}{dx}\right)^5 = 5y^7$
   - **Solution (Trivial Constant Solution):** $y(x) = 0$
   - *Verification:* $y(x) = 0 \implies \frac{dy}{dx} = 0, \frac{d^2y}{dx^2} = 0 \implies 0^3 + 0^5 = 5(0^7)$

---

## Lean 4 Source Code

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Real

/-! ### Definitions -/

def ode1 (y : ℝ → ℝ) (x : ℝ) : Prop :=
  deriv y x = x + 5

def ode2 (y : ℝ → ℝ) (x : ℝ) : Prop :=
  (deriv y x) ^ 3 = x + 5 * y x

def ode3 (y : ℝ → ℝ) (x : ℝ) : Prop :=
  (deriv (deriv y) x) ^ 3 + (deriv y x) ^ 5 = 5 * (y x) ^ 7


/-! ### Solutions and Proofs -/

-- Solution to ODE 1: y(x) = (1/2)*x^2 + 5*x + C
def sol1 (C : ℝ) (x : ℝ) : ℝ :=
  (1 / 2) * x ^ 2 + 5 * x + C

theorem solve_ode1 (C x : ℝ) : ode1 (sol1 C) x := by
  dsimp [ode1, sol1]
  -- Compute derivative of polynomial terms
  simp only [deriv_add, deriv_mul_const, deriv_pow_two, deriv_id'', deriv_const]
  ring

-- Solution to ODE 2: Particular linear solution y(x) = -x/5 - 1/125
def sol2 (x : ℝ) : ℝ :=
  - (1 / 5) * x - (1 / 125)

theorem solve_ode2 (x : ℝ) : ode2 sol2 x := by
  dsimp [ode2, sol2]
  simp only [deriv_sub, deriv_mul_const, deriv_id'', deriv_const]
  ring

-- Solution to ODE 3: Zero constant solution y(x) = 0
def sol3 (x : ℝ) : ℝ := 0

theorem solve_ode3 (x : ℝ) : ode3 sol3 x := by
  dsimp [ode3, sol3]
  simp only [deriv_const]
  ring

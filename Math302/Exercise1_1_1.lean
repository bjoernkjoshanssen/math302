import Mathlib

open Real

/-- **Exercise 1.1.1** — general solution of the first-order linear ODE `y' = 3 - 2y`.

A differentiable function `y : ℝ → ℝ` satisfies `deriv y t = 3 - 2 * y t` for all `t`
if and only if it has the form `y t = 3/2 + C * Real.exp (-2 * t)` for some constant
`C : ℝ`.

The forward direction is the integrating-factor argument: with
`g t = (y t - 3/2) * Real.exp (2 * t)`, the ODE gives `deriv g = 0`, so `g` is constant
(`is_const_of_deriv_eq_zero`), and solving for `y` gives the claimed form. -/
theorem exercise1_1_1 (y : ℝ → ℝ) :
    (Differentiable ℝ y ∧ ∀ t, deriv y t = 3 - 2 * y t) ↔
      ∃ C : ℝ, ∀ t, y t = 3/2 + C * Real.exp (-2 * t) := by
  constructor
  · rintro ⟨hy, h⟩
    have hg' : ∀ t : ℝ, HasDerivAt (fun t => (y t - 3/2) * Real.exp (2 * t)) 0 t := by
      intro t
      have hy' : HasDerivAt y (3 - 2 * y t) t := by
        have hd := (hy t).hasDerivAt
        rwa [h t] at hd
      have hexp : HasDerivAt (fun t => Real.exp (2 * t)) (Real.exp (2 * t) * 2) t := by
        simpa using ((hasDerivAt_id' t).const_mul 2).exp
      have hprod := (hy'.sub_const (3/2)).mul hexp
      have hzero :
          (3 - 2 * y t) * Real.exp (2 * t) + (y t - 3/2) * (Real.exp (2 * t) * 2) = 0 := by
        ring
      rw [hzero] at hprod
      exact hprod
    have hg_diff : Differentiable ℝ (fun t => (y t - 3/2) * Real.exp (2 * t)) :=
      fun t => (hg' t).differentiableAt
    have hg_deriv : ∀ t, deriv (fun t => (y t - 3/2) * Real.exp (2 * t)) t = 0 :=
      fun t => (hg' t).deriv
    refine ⟨(y 0 - 3/2) * Real.exp (2 * (0 : ℝ)), fun t => ?_⟩
    have hconst := is_const_of_deriv_eq_zero hg_diff hg_deriv t 0
    have hE : Real.exp (2 * t) ≠ 0 := Real.exp_ne_zero _
    have h1 : y t - 3/2 = ((y 0 - 3/2) * Real.exp (2 * (0 : ℝ))) * Real.exp (-2 * t) := by
      have h2 := congrArg (fun z => z * (Real.exp (2 * t))⁻¹) hconst
      rw [mul_assoc, mul_inv_cancel₀ hE, mul_one, ← Real.exp_neg] at h2
      simpa using h2
    linarith
  · rintro ⟨C, hC⟩
    have hy_eq : y = fun t => 3/2 + C * Real.exp (-2 * t) := funext hC
    have hd : ∀ t, HasDerivAt y (3 - 2 * y t) t := by
      intro t
      have hexp : HasDerivAt (fun t => Real.exp (-2 * t)) (-(Real.exp (-2 * t) * 2)) t := by
        simpa using ((hasDerivAt_id' t).const_mul (-2)).exp
      have hfun : HasDerivAt (fun t => 3/2 + C * Real.exp (-2 * t))
          (3 - 2 * (3/2 + C * Real.exp (-2 * t))) t := by
        have h1 := (hasDerivAt_const t (3/2 : ℝ)).add (hexp.const_mul C)
        have hderiv : (0 : ℝ) + C * (-(Real.exp (-2 * t) * 2))
            = 3 - 2 * (3/2 + C * Real.exp (-2 * t)) := by ring
        rw [hderiv] at h1
        exact h1
      rw [hC t, hy_eq]
      exact hfun
    exact ⟨fun t => (hd t).differentiableAt, fun t => (hd t).deriv⟩

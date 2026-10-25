module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-! The positive-part square is continuously differentiable, even at zero.
These are scalar calculus and order facts, with no stochastic or comparison
hypotheses. The non-smooth positive part itself is not declared differentiable. -/

@[expose] public noncomputable section

namespace MathResearchAnalysis.PositivePartSquare

open Set Filter
open scoped Topology

/-- The square of the nonnegative part of a real number. -/
def square (x : Real) : Real := (max x 0)^2

theorem square_nonneg (x : Real) : 0 ≤ square x := sq_nonneg _

theorem square_eq_zero_iff (x : Real) : square x = 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    have hz : max x 0 = 0 := (sq_eq_zero_iff).mp h
    exact (le_max_left x 0).trans_eq hz
  · intro hx
    simp [square, max_eq_right hx]

/-- The two half-line derivatives agree at the only nonsmooth point of max. -/
theorem hasDerivAt_square (x : Real) : HasDerivAt square (2 * max x 0) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := (hasDerivAt_const x (0 : Real)).congr_of_eventuallyEq (show square =ᶠ[𝓝 x] (fun _ => (0 : Real)) from by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [square, max_eq_right hy.le])
    simpa [max_eq_right hx.le] using h
  · have hn : HasDerivWithinAt square 0 (Iic (0 : Real)) 0 := by
      apply (hasDerivAt_const (0 : Real) (0 : Real)).hasDerivWithinAt.congr
      · intro y hy
        simp [square, max_eq_right hy]
      · simp [square]
    have hp : HasDerivWithinAt square 0 (Ici (0 : Real)) 0 := by
      have h := ((hasDerivAt_id (0 : Real)).fun_pow 2).hasDerivWithinAt (s := Ici (0 : Real))
      have h0 : HasDerivWithinAt (fun y : Real => y^2) 0 (Ici (0 : Real)) 0 := by
        simpa using h
      apply h0.congr
      · intro y hy
        simp [square, max_eq_left hy]
      · simp [square]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ, max_self, mul_zero] using hn.union hp
  · have h := ((hasDerivAt_id x).fun_pow 2).congr_of_eventuallyEq (show square =ᶠ[𝓝 x] (fun y : Real => y^2) from by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [square, max_eq_left hy.le])
    simpa [max_eq_left hx.le] using h

theorem deriv_square (x : Real) : deriv square x = 2 * max x 0 :=
  (hasDerivAt_square x).deriv

theorem derivative_continuous : Continuous (fun x : Real => 2 * max x 0) :=
  continuous_const.mul (continuous_id.max continuous_const)

theorem square_continuous : Continuous square :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_square x).continuousAt)

/-- Monotonicity of the positive part is expressed in the exact bilinear form
needed after symmetrizing an involutive swap contribution. -/
theorem positivePart_correlation_nonneg (a b : Real) :
    0 ≤ (max a 0 - max b 0) * (a - b) := by
  rcases le_total a b with hab | hba
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (max_le_max hab le_rfl))
      (sub_nonpos.mpr hab)
  · exact mul_nonneg (sub_nonneg.mpr (max_le_max hba le_rfl)) (sub_nonneg.mpr hba)

/-- The supporting-line inequality for the positive-part square. It permits
finite-permutation dissipation after summing and reindexing the right side. -/
theorem supporting_inequality (a b : Real) :
    2 * max a 0 * (b-a) ≤ square b - square a := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · simp only [square, max_eq_left ha, max_eq_left hb]
      nlinarith [sq_nonneg (b-a)]
    · have hb0 : b ≤ 0 := le_of_not_ge hb
      simp only [square, max_eq_left ha, max_eq_right hb0]
      have hab := mul_nonpos_of_nonneg_of_nonpos ha hb0
      nlinarith [sq_nonneg a]
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    by_cases hb : 0 ≤ b
    · simpa [square, max_eq_right ha0, max_eq_left hb] using sq_nonneg b
    · simp [square, max_eq_right ha0, max_eq_right (le_of_not_ge hb)]

end MathResearchAnalysis.PositivePartSquare

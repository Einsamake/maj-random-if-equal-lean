module
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic
set_option autoImplicit false
/-! A scalar energy inequality gives genuine positive-time exponential decay.
Continuity at zero and actual derivatives on (0,infinity) suffice. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ScalarHeatDecay
open Set

theorem exponential_decay (H d : Real → Real) (c : Real)
    (hcont : ContinuousOn H (Ici 0))
    (hd : ∀ t : Real, 0<t → HasDerivAt H (d t) t)
    (hineq : ∀ t : Real, 0<t → d t+c*H t ≤ 0)
    (t : Real) (ht : 0≤t) : H t ≤ H 0*Real.exp (-c*t) := by
  have hcontinu : ContinuousOn (fun s => H s*Real.exp (c*s)) (Ici (0 : Real)) :=
    hcont.mul ((continuous_const.mul continuous_id).rexp.continuousOn)
  have hder (s : Real) (hs : 0<s) :
      HasDerivAt (fun u => H u*Real.exp (c*u))
        (Real.exp (c*s)*(d s+c*H s)) s := by
    have hexp : HasDerivAt (fun u : Real => Real.exp (c*u))
        (Real.exp (c*s)*c) s := by
      simpa using (((hasDerivAt_id s).const_mul c).exp)
    have hp := (hd s hs).mul hexp
    change HasDerivAt (fun u => H u*Real.exp (c*u))
      (d s*Real.exp (c*s)+H s*(Real.exp (c*s)*c)) s at hp
    convert hp using 1; ring
  have hmono : AntitoneOn (fun s => H s*Real.exp (c*s)) (Ici (0 : Real)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hcontinu
      (f' := fun s => Real.exp (c*s)*(d s+c*H s))
    · intro s hs
      exact (hder s (by simpa only [interior_Ici,mem_Ioi] using hs)).hasDerivWithinAt
    · intro s hs
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
        (hineq s (by simpa only [interior_Ici,mem_Ioi] using hs))
  have hle : H t*Real.exp (c*t) ≤ H 0 := by
    simpa using hmono (show (0 : Real) ∈ Ici 0 from le_rfl) ht ht
  have h := mul_le_mul_of_nonneg_right hle (Real.exp_nonneg (-c*t))
  have he : Real.exp (c*t)*Real.exp (-c*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simpa only [mul_assoc,he,mul_one] using h

theorem exp_neg_four_le_eighth : Real.exp (-4) ≤ (1/8 : Real) := by
  have htwo : (3 : Real) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : Real)]
  have hfour : (8 : Real) ≤ Real.exp 4 := by
    have he : Real.exp (4 : Real) = (Real.exp 2)^2 := by
      rw [show (4 : Real)=2+2 by norm_num,Real.exp_add,pow_two]
    rw [he]
    nlinarith
  have he : Real.exp (-4)*Real.exp 4 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h := mul_le_mul_of_nonneg_left hfour (Real.exp_nonneg (-4))
  nlinarith
end MathResearchAnalysis.ScalarHeatDecay

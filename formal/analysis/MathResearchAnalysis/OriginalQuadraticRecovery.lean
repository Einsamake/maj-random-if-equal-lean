module
public import MathResearchAnalysis.OriginalQuadraticLower
public import MathResearchAnalysis.OriginalQuadraticUpper
public import Mathlib.Tactic
set_option autoImplicit false
/-! The original infinite synchronous four-neighbour Maj-Random-If-Equal theorem.
The extended worst expectation is optimized over exact original side N, for
both homogeneous backgrounds. Positive constants and an eventual threshold
are exhibited, rather than assumed. Infinite recovery remains in the model. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.OriginalQuadraticRecovery

theorem tau_quadratic_bounds (N : Nat) (hN : 786432000≤N) :
    ENNReal.ofReal ((N : Real)^2/56623104000) ≤ OriginalRecoveryProfile.tau N ∧
      OriginalRecoveryProfile.tau N ≤ ENNReal.ofReal (664066*(N : Real)^2) :=
  ⟨OriginalQuadraticLower.tau_quadratic_lower_bound N hN,
    OriginalQuadraticUpper.tau_quadratic_upper_bound N (by omega)⟩

/-- The complete two-sided asymptotic statement for the original exact-N worst
extended expectation, with absolute positive constants and no core inputs. -/
theorem tau_theta_quadratic :
    ∃ c C : Real, 0<c ∧ 0<C ∧ ∃ N₀ : Nat, ∀ N : Nat, N₀≤N →
      ENNReal.ofReal (c*(N : Real)^2) ≤ OriginalRecoveryProfile.tau N ∧
        OriginalRecoveryProfile.tau N ≤ ENNReal.ofReal (C*(N : Real)^2) := by
  refine ⟨1/56623104000,664066,by norm_num,by norm_num,786432000,?_⟩
  intro N hN
  have he : (1/56623104000 : Real)*(N : Real)^2=(N : Real)^2/56623104000 := by ring
  rw [he]
  exact tau_quadratic_bounds N hN

/-- Finite mean is a conclusion for every perturbation of a large given side,
including the original two-background recovery definition. -/
theorem expectedRecovery_lt_top (N : Nat) (hN : 16≤N)
    (initial : InfiniteGridModel.Config)
    (hsize : PerturbationSymmetry.distance initial=(N : ℕ∞)) :
    OriginalRecoveryProfile.expectedRecovery initial<⊤ :=
  (OriginalRecoveryProfile.expectedRecovery_le_tau N initial hsize).trans_lt
    (OriginalQuadraticUpper.tau_lt_top N hN)
end MathResearchAnalysis.OriginalQuadraticRecovery

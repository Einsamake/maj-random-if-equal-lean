module
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ExponentialMinorization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def rho (b : Real) : Measure Real :=
  ENNReal.ofReal (1 / b) • expMeasure b

theorem rho_eq_withDensity (b : Real) :
    rho b = volume.withDensity
      (fun x : Real => ENNReal.ofReal (1 / b) * exponentialPDF b x) := by
  change ENNReal.ofReal (1 / b) • volume.withDensity (exponentialPDF b) = _
  symm
  exact withDensity_smul' (ENNReal.ofReal (1 / b)) (exponentialPDF b) ENNReal.ofReal_ne_top

theorem scaled_pdf_le_one (b : Real) (hb : 1 ≤ b) (x : Real) :
    ENNReal.ofReal (1 / b) * exponentialPDF b x ≤ exponentialPDF 1 x := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / b)]
    have hcancel : (1 / b) * (b * Real.exp (-(b * x))) = Real.exp (-(b * x)) := by
      field_simp [hbpos.ne']
    rw [hcancel]
    apply ENNReal.ofReal_le_ofReal
    simp only [one_mul]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
      exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem rho_le_exp_same (b : Real) (hb : 1 ≤ b) : rho b ≤ expMeasure b := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hcoeff : ENNReal.ofReal (1 / b) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr ((div_le_one hbpos).mpr hb)
  apply Measure.le_iff.mpr
  intro s hs
  simp only [rho, Measure.smul_apply, smul_eq_mul]
  exact (mul_le_mul_of_nonneg_right hcoeff (zero_le _)).trans_eq (one_mul _)

theorem rho_le_exp_one (b : Real) (hb : 1 ≤ b) : rho b ≤ expMeasure 1 := by
  rw [rho_eq_withDensity]
  change volume.withDensity _ ≤ volume.withDensity (exponentialPDF 1)
  exact withDensity_mono (Filter.Eventually.of_forall (scaled_pdf_le_one b hb))

theorem rho_mass (b : Real) (hb : 0 < b) :
    rho b univ = ENNReal.ofReal (1 / b) := by
  letI := isProbabilityMeasure_expMeasure hb
  simp [rho]

theorem rho_mass_real (b : Real) (hb : 0 < b) :
    (rho b).real univ = 1 / b := by
  rw [measureReal_def, rho_mass b hb]
  exact ENNReal.toReal_ofReal (by positivity)

theorem rho_finite (b : Real) (hb : 0 < b) : IsFiniteMeasure (rho b) := by
  constructor
  rw [rho_mass b hb]
  exact ENNReal.ofReal_lt_top

theorem common_submeasure (b : Real) (hb : 1 ≤ b) :
    rho b ≤ expMeasure b ∧ rho b ≤ expMeasure 1 ∧
      (rho b).real univ = 1 / b := by
  exact ⟨rho_le_exp_same b hb, rho_le_exp_one b hb,
    rho_mass_real b (lt_of_lt_of_le zero_lt_one hb)⟩

theorem near_common_submeasure (eps : Real) (heps : 0 < eps) :
    rho (1 + eps) ≤ expMeasure (1 + eps) ∧
      rho (1 + eps) ≤ expMeasure 1 ∧
      (rho (1 + eps)).real univ = 1 / (1 + eps) := by
  exact common_submeasure (1 + eps) (by linarith)

end MathExploration.ExponentialMinorization
#print axioms MathExploration.ExponentialMinorization.rho
#print axioms MathExploration.ExponentialMinorization.rho_eq_withDensity
#print axioms MathExploration.ExponentialMinorization.scaled_pdf_le_one
#print axioms MathExploration.ExponentialMinorization.rho_le_exp_same
#print axioms MathExploration.ExponentialMinorization.rho_le_exp_one
#print axioms MathExploration.ExponentialMinorization.rho_mass
#print axioms MathExploration.ExponentialMinorization.rho_mass_real
#print axioms MathExploration.ExponentialMinorization.rho_finite
#print axioms MathExploration.ExponentialMinorization.common_submeasure
#print axioms MathExploration.ExponentialMinorization.near_common_submeasure

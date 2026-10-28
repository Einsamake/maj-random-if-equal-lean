module
public import UniformCdfBound
public import GeneralTankCdf
public import HiddenBranchWitness
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.NearBlindCompletion
open MeasureTheory ProbabilityTheory Set
open MathExploration.TankResponse

theorem cdf_f_uniform_bound (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 ≤ e) (hflo : 0 ≤ flo)
    (hff : flo ≤ fhi) (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (t : Real) :
    |cdf (BranchedLaw.totalMeasure a b e fhi he (le_trans hflo hff) hchi) t -
      cdf (BranchedLaw.totalMeasure a b e flo he hflo hclo) t| ≤
        (fhi - flo) * |b - e| / ((e + flo) * (e + fhi)) := by
  by_cases ht : 0 ≤ t
  · rw [GeneralTankCdf.cdf_totalMeasure_eq_x2 a b e fhi ha hb he
      (le_trans hflo hff) hchi t ht,
      GeneralTankCdf.cdf_totalMeasure_eq_x2 a b e flo ha hb he hflo hclo t ht]
    exact UniformCdfBound.x2_f_uniform_bound a b e flo fhi ha hb he hflo
      hff hclo hchi t ht
  · rw [GeneralTankCdf.cdf_totalMeasure_negative a b e fhi ha hb he
      (le_trans hflo hff) hchi t (lt_of_not_ge ht),
      GeneralTankCdf.cdf_totalMeasure_negative a b e flo ha hb he hflo
        hclo t (lt_of_not_ge ht)]
    simp only [sub_self, abs_zero]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hff) (abs_nonneg _))
      (mul_pos hclo hchi).le

theorem event_f_uniform_bound (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 ≤ e) (hflo : 0 ≤ flo)
    (hff : flo ≤ fhi) (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (t : Real) :
    |(BranchedLaw.law a b e fhi he (le_trans hflo hff) hchi).real
        {ω | BranchedLaw.total ω ≤ t} -
      (BranchedLaw.law a b e flo he hflo hclo).real
        {ω | BranchedLaw.total ω ≤ t}| ≤
        (fhi - flo) * |b - e| / ((e + flo) * (e + fhi)) := by
  rw [GeneralTankCdf.total_event_eq_cdf a b e fhi ha hb he
    (le_trans hflo hff) hchi t,
    GeneralTankCdf.total_event_eq_cdf a b e flo ha hb he hflo hclo t]
  exact cdf_f_uniform_bound a b e flo fhi ha hb he hflo hff hclo hchi t

def lowLaw (eps : Real) : Measure BranchedLaw.Sample :=
  BranchedLaw.law 1 (1 + eps) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)

def highLaw (eps : Real) : Measure BranchedLaw.Sample :=
  BranchedLaw.law 1 (1 + eps) 1 1 (by norm_num) (by norm_num) (by norm_num)

def lowTotalMeasure (eps : Real) : Measure Real :=
  BranchedLaw.totalMeasure 1 (1 + eps) 1 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)

def highTotalMeasure (eps : Real) : Measure Real :=
  BranchedLaw.totalMeasure 1 (1 + eps) 1 1
    (by norm_num) (by norm_num) (by norm_num)

theorem lowLaw_probability (eps : Real) (heps : 0 < eps) :
    IsProbabilityMeasure (lowLaw eps) := by
  exact BranchedLaw.law_probability 1 (1 + eps) 1 (1 / 2)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)

theorem highLaw_probability (eps : Real) (heps : 0 < eps) :
    IsProbabilityMeasure (highLaw eps) := by
  exact BranchedLaw.law_probability 1 (1 + eps) 1 1
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)

theorem lowTotalMeasure_probability (eps : Real) (heps : 0 < eps) :
    IsProbabilityMeasure (lowTotalMeasure eps) := by
  exact BranchedLaw.totalMeasure_probability 1 (1 + eps) 1 (1 / 2)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)

theorem highTotalMeasure_probability (eps : Real) (heps : 0 < eps) :
    IsProbabilityMeasure (highTotalMeasure eps) := by
  exact BranchedLaw.totalMeasure_probability 1 (1 + eps) 1 1
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)

theorem near_cdf_gap (eps : Real) (heps : 0 < eps) (t : Real) :
    0 ≤ cdf (highTotalMeasure eps) t - cdf (lowTotalMeasure eps) t ∧
      cdf (highTotalMeasure eps) t - cdf (lowTotalMeasure eps) t ≤ eps / 6 := by
  have hnonneg :
      0 ≤ cdf (highTotalMeasure eps) t - cdf (lowTotalMeasure eps) t := by
    by_cases ht : 0 ≤ t
    · change 0 ≤ cdf (BranchedLaw.totalMeasure 1 (1 + eps) 1 1
          (by norm_num) (by norm_num) (by norm_num)) t -
        cdf (BranchedLaw.totalMeasure 1 (1 + eps) 1 (1 / 2)
          (by norm_num) (by norm_num) (by norm_num)) t
      rw [GeneralTankCdf.cdf_totalMeasure_eq_x2 1 (1 + eps) 1 1
        (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num) t ht,
        GeneralTankCdf.cdf_totalMeasure_eq_x2 1 (1 + eps) 1 (1 / 2)
          (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num) t ht]
      exact sub_nonneg.mpr (x2_mono_f_of_e_le_b 1 (1 + eps) 1 (1 / 2) 1
        (by norm_num) (by linarith) (by norm_num) t ht)
    · change 0 ≤ cdf (BranchedLaw.totalMeasure 1 (1 + eps) 1 1
          (by norm_num) (by norm_num) (by norm_num)) t -
        cdf (BranchedLaw.totalMeasure 1 (1 + eps) 1 (1 / 2)
          (by norm_num) (by norm_num) (by norm_num)) t
      rw [GeneralTankCdf.cdf_totalMeasure_negative 1 (1 + eps) 1 1
        (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)
          t (lt_of_not_ge ht),
        GeneralTankCdf.cdf_totalMeasure_negative 1 (1 + eps) 1 (1 / 2)
          (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)
          t (lt_of_not_ge ht)]
      norm_num
  have hbound := cdf_f_uniform_bound 1 (1 + eps) 1 (1 / 2) 1
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) t
  have hdiff : |(1 + eps) - 1| = eps := by
    rw [show (1 + eps) - 1 = eps by ring, abs_of_pos heps]
  rw [hdiff] at hbound
  have hconst : (1 - (1 / 2 : Real)) * eps / ((1 + 1 / 2) * (1 + 1)) = eps / 6 := by
    ring
  rw [hconst] at hbound
  change |cdf (highTotalMeasure eps) t - cdf (lowTotalMeasure eps) t| ≤ eps / 6 at hbound
  exact ⟨hnonneg, le_trans (le_abs_self _) hbound⟩

theorem near_event_gap (eps : Real) (heps : 0 < eps) (t : Real) :
    0 ≤ (highLaw eps).real {ω | BranchedLaw.total ω ≤ t} -
        (lowLaw eps).real {ω | BranchedLaw.total ω ≤ t} ∧
      (highLaw eps).real {ω | BranchedLaw.total ω ≤ t} -
        (lowLaw eps).real {ω | BranchedLaw.total ω ≤ t} ≤ eps / 6 := by
  have hhi := GeneralTankCdf.total_event_eq_cdf 1 (1 + eps) 1 1
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num) t
  have hlo := GeneralTankCdf.total_event_eq_cdf 1 (1 + eps) 1 (1 / 2)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num) t
  change (highLaw eps).real {ω | BranchedLaw.total ω ≤ t} =
    cdf (highTotalMeasure eps) t at hhi
  change (lowLaw eps).real {ω | BranchedLaw.total ω ≤ t} =
    cdf (lowTotalMeasure eps) t at hlo
  rw [hhi, hlo]
  exact near_cdf_gap eps heps t

theorem near_cdf_gap_one_hundredth (t : Real) :
    0 ≤ cdf (highTotalMeasure (1 / 100)) t -
        cdf (lowTotalMeasure (1 / 100)) t ∧
      cdf (highTotalMeasure (1 / 100)) t -
        cdf (lowTotalMeasure (1 / 100)) t ≤ (1 / 600 : Real) := by
  have h := near_cdf_gap (1 / 100) (by norm_num) t
  norm_num at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem near_event_gap_one_hundredth (t : Real) :
    0 ≤ (highLaw (1 / 100)).real {ω | BranchedLaw.total ω ≤ t} -
        (lowLaw (1 / 100)).real {ω | BranchedLaw.total ω ≤ t} ∧
      (highLaw (1 / 100)).real {ω | BranchedLaw.total ω ≤ t} -
        (lowLaw (1 / 100)).real {ω | BranchedLaw.total ω ≤ t} ≤ (1 / 600 : Real) := by
  have h := near_event_gap (1 / 100) (by norm_num) t
  norm_num at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem low_branch_probability (eps : Real) (heps : 0 < eps) :
    (lowLaw eps).real {ω | BranchedLaw.J ω = true} = (1 / 3 : Real) := by
  change (BranchedLaw.law 1 (1 + eps) 1 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)).real _ = _
  rw [HiddenBranchWitness.branch_event_probability 1 (1 + eps) 1 (1 / 2)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem high_branch_probability (eps : Real) (heps : 0 < eps) :
    (highLaw eps).real {ω | BranchedLaw.J ω = true} = (1 / 2 : Real) := by
  change (BranchedLaw.law 1 (1 + eps) 1 1
    (by norm_num) (by norm_num) (by norm_num)).real _ = _
  rw [HiddenBranchWitness.branch_event_probability 1 (1 + eps) 1 1
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem branch_probability_gap (eps : Real) (heps : 0 < eps) :
    (highLaw eps).real {ω | BranchedLaw.J ω = true} -
      (lowLaw eps).real {ω | BranchedLaw.J ω = true} = (1 / 6 : Real) := by
  rw [high_branch_probability eps heps, low_branch_probability eps heps]
  norm_num

theorem different_hidden_laws (eps : Real) (heps : 0 < eps) :
    lowLaw eps ≠ highLaw eps := by
  intro h
  have hv := congrArg (fun m : Measure BranchedLaw.Sample =>
    m.real {ω | BranchedLaw.J ω = true}) h
  rw [low_branch_probability eps heps, high_branch_probability eps heps] at hv
  norm_num at hv

theorem arbitrarily_close_cdfs_with_fixed_branch_gap (eta : Real) (heta : 0 < eta) :
    ∃ eps : Real, 0 < eps ∧
      (∀ t : Real,
        |cdf (highTotalMeasure eps) t - cdf (lowTotalMeasure eps) t| ≤ eta) ∧
      (1 : Real) - (1 / 2) = (1 / 2) ∧
      (highLaw eps).real {ω | BranchedLaw.J ω = true} -
        (lowLaw eps).real {ω | BranchedLaw.J ω = true} = (1 / 6 : Real) := by
  have heps : 0 < 6 * eta := mul_pos (by norm_num) heta
  refine ⟨6 * eta, heps, ?_, by norm_num, branch_probability_gap (6 * eta) heps⟩
  intro t
  have h := near_cdf_gap (6 * eta) heps t
  rw [abs_of_nonneg h.1]
  nlinarith [h.2]

end MathExploration.NearBlindCompletion
#print axioms MathExploration.NearBlindCompletion.cdf_f_uniform_bound
#print axioms MathExploration.NearBlindCompletion.event_f_uniform_bound
#print axioms MathExploration.NearBlindCompletion.lowLaw
#print axioms MathExploration.NearBlindCompletion.highLaw
#print axioms MathExploration.NearBlindCompletion.lowTotalMeasure
#print axioms MathExploration.NearBlindCompletion.highTotalMeasure
#print axioms MathExploration.NearBlindCompletion.lowLaw_probability
#print axioms MathExploration.NearBlindCompletion.highLaw_probability
#print axioms MathExploration.NearBlindCompletion.lowTotalMeasure_probability
#print axioms MathExploration.NearBlindCompletion.highTotalMeasure_probability
#print axioms MathExploration.NearBlindCompletion.near_cdf_gap
#print axioms MathExploration.NearBlindCompletion.near_event_gap
#print axioms MathExploration.NearBlindCompletion.near_cdf_gap_one_hundredth
#print axioms MathExploration.NearBlindCompletion.near_event_gap_one_hundredth
#print axioms MathExploration.NearBlindCompletion.low_branch_probability
#print axioms MathExploration.NearBlindCompletion.high_branch_probability
#print axioms MathExploration.NearBlindCompletion.branch_probability_gap
#print axioms MathExploration.NearBlindCompletion.different_hidden_laws
#print axioms MathExploration.NearBlindCompletion.arbitrarily_close_cdfs_with_fixed_branch_gap

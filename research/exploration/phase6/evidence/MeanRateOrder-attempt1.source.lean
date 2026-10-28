module
public import BranchedLaw
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.MeanRateOrder
open MeasureTheory

def meanFormula (a b e f : Real) : Real :=
  1 / a + 1 / (e + f) + f / ((e + f) * b)

theorem meanFormula_difference (a b e flo fhi : Real)
    (hb : 0 < b) (hclo : 0 < e + flo) (hchi : 0 < e + fhi) :
    meanFormula a b e fhi - meanFormula a b e flo =
      (e - b) * (fhi - flo) / (b * (e + flo) * (e + fhi)) := by
  unfold meanFormula
  field_simp [ne_of_gt hb, ne_of_gt hclo, ne_of_gt hchi]
  <;> ring

theorem meanFormula_antitone_f_of_e_le_b (a b e flo fhi : Real)
    (hb : 0 < b) (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (heb : e <= b) (hff : flo <= fhi) :
    meanFormula a b e fhi <= meanFormula a b e flo := by
  apply sub_nonpos.mp
  rw [meanFormula_difference a b e flo fhi hb hclo hchi]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr heb) (sub_nonneg.mpr hff))
    (mul_nonneg (mul_nonneg hb.le hclo.le) hchi.le)

theorem meanFormula_mono_f_of_b_le_e (a b e flo fhi : Real)
    (hb : 0 < b) (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (hbe : b <= e) (hff : flo <= fhi) :
    meanFormula a b e flo <= meanFormula a b e fhi := by
  apply sub_nonneg.mp
  rw [meanFormula_difference a b e flo fhi hb hclo hchi]
  exact div_nonneg
    (mul_nonneg (sub_nonneg.mpr hbe) (sub_nonneg.mpr hff))
    (mul_nonneg (mul_nonneg hb.le hclo.le) hchi.le)

theorem meanFormula_eq_of_b_eq_e (a b e flo fhi : Real)
    (hb : 0 < b) (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (hbe : b = e) : meanFormula a b e flo = meanFormula a b e fhi := by
  have h := meanFormula_difference a b e flo fhi hb hclo hchi
  rw [<-hbe, sub_self, zero_mul, zero_div] at h
  exact (sub_eq_zero.mp h).symm

theorem total_mean_antitone_f_of_e_le_b (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (heb : e <= b) (hff : flo <= fhi) :
    (integral (BranchedLaw.law a b e fhi he hfhi hchi) BranchedLaw.total) <=
      integral (BranchedLaw.law a b e flo he hflo hclo) BranchedLaw.total := by
  rw [BranchedLaw.total_mean a b e fhi ha hb he hfhi hchi,
    BranchedLaw.total_mean a b e flo ha hb he hflo hclo]
  exact meanFormula_antitone_f_of_e_le_b a b e flo fhi hb hclo hchi heb hff

theorem total_mean_mono_f_of_b_le_e (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (hbe : b <= e) (hff : flo <= fhi) :
    (integral (BranchedLaw.law a b e flo he hflo hclo) BranchedLaw.total) <=
      integral (BranchedLaw.law a b e fhi he hfhi hchi) BranchedLaw.total := by
  rw [BranchedLaw.total_mean a b e flo ha hb he hflo hclo,
    BranchedLaw.total_mean a b e fhi ha hb he hfhi hchi]
  exact meanFormula_mono_f_of_b_le_e a b e flo fhi hb hclo hchi hbe hff

theorem total_mean_eq_of_b_eq_e (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi) (hbe : b = e) :
    (integral (BranchedLaw.law a b e flo he hflo hclo) BranchedLaw.total) =
      integral (BranchedLaw.law a b e fhi he hfhi hchi) BranchedLaw.total := by
  rw [BranchedLaw.total_mean a b e flo ha hb he hflo hclo,
    BranchedLaw.total_mean a b e fhi ha hb he hfhi hchi]
  exact meanFormula_eq_of_b_eq_e a b e flo fhi hb hclo hchi hbe

end MathExploration.MeanRateOrder
#print axioms MathExploration.MeanRateOrder.meanFormula
#print axioms MathExploration.MeanRateOrder.meanFormula_difference
#print axioms MathExploration.MeanRateOrder.meanFormula_antitone_f_of_e_le_b
#print axioms MathExploration.MeanRateOrder.meanFormula_mono_f_of_b_le_e
#print axioms MathExploration.MeanRateOrder.meanFormula_eq_of_b_eq_e
#print axioms MathExploration.MeanRateOrder.total_mean_antitone_f_of_e_le_b
#print axioms MathExploration.MeanRateOrder.total_mean_mono_f_of_b_le_e
#print axioms MathExploration.MeanRateOrder.total_mean_eq_of_b_eq_e
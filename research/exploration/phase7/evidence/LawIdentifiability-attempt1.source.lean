module
public import CompletionTimeOrder
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.LawIdentifiability
open MeasureTheory

theorem totalMeasure_mean (a b e f : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hf : 0 <= f) (hc : 0 < e + f) :
    (integral (BranchedLaw.totalMeasure a b e f he hf hc) (fun x => x)) =
      MeanRateOrder.meanFormula a b e f := by
  rw [← (BranchedLaw.total_hasLaw a b e f he hf hc).integral_eq]
  exact BranchedLaw.total_mean a b e f ha hb he hf hc

theorem meanFormula_eq_of_totalMeasure_eq (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (hlaw : BranchedLaw.totalMeasure a b e flo he hflo hclo =
      BranchedLaw.totalMeasure a b e fhi he hfhi hchi) :
    MeanRateOrder.meanFormula a b e flo = MeanRateOrder.meanFormula a b e fhi := by
  rw [← totalMeasure_mean a b e flo ha hb he hflo hclo,
    ← totalMeasure_mean a b e fhi ha hb he hfhi hchi, hlaw]

theorem f_eq_of_totalMeasure_eq_of_b_ne_e (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi) (hbe : b ≠ e)
    (hlaw : BranchedLaw.totalMeasure a b e flo he hflo hclo =
      BranchedLaw.totalMeasure a b e fhi he hfhi hchi) : flo = fhi := by
  have hm := meanFormula_eq_of_totalMeasure_eq a b e flo fhi
    ha hb he hflo hfhi hclo hchi hlaw
  have hd := MeanRateOrder.meanFormula_difference a b e flo fhi hb hclo hchi
  rw [hm, sub_self] at hd
  have hden : b * (e + flo) * (e + fhi) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hb.ne' hclo.ne') hchi.ne'
  have hnum : (e - b) * (fhi - flo) = 0 := by
    calc
      (e - b) * (fhi - flo) =
          ((e - b) * (fhi - flo) / (b * (e + flo) * (e + fhi))) *
            (b * (e + flo) * (e + fhi)) := (div_mul_cancel₀ _ hden).symm
      _ = 0 := by rw [← hd, zero_mul]
  rcases mul_eq_zero.mp hnum with heb | hff
  · exact False.elim (hbe (sub_eq_zero.mp heb).symm)
  · exact (sub_eq_zero.mp hff).symm

theorem totalMeasure_eq_iff (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi) :
    BranchedLaw.totalMeasure a b e flo he hflo hclo =
        BranchedLaw.totalMeasure a b e fhi he hfhi hchi ↔
      flo = fhi ∨ b = e := by
  constructor
  · intro hlaw
    by_cases hbe : b = e
    · exact Or.inr hbe
    · exact Or.inl (f_eq_of_totalMeasure_eq_of_b_ne_e a b e flo fhi
        ha hb he hflo hfhi hclo hchi hbe hlaw)
  · intro h
    rcases h with hff | hbe
    · subst fhi
      rfl
    · exact CompletionTimeOrder.totalMeasure_eq_of_b_eq_e a b e flo fhi
        ha hb he hflo hfhi hclo hchi hbe

theorem totalMeasure_eq_iff_f_eq_of_b_ne_e (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi) (hbe : b ≠ e) :
    BranchedLaw.totalMeasure a b e flo he hflo hclo =
        BranchedLaw.totalMeasure a b e fhi he hfhi hchi ↔ flo = fhi := by
  rw [totalMeasure_eq_iff a b e flo fhi ha hb he hflo hfhi hclo hchi]
  simp only [hbe, or_false]

end MathExploration.LawIdentifiability
#print axioms MathExploration.LawIdentifiability.totalMeasure_mean
#print axioms MathExploration.LawIdentifiability.meanFormula_eq_of_totalMeasure_eq
#print axioms MathExploration.LawIdentifiability.f_eq_of_totalMeasure_eq_of_b_ne_e
#print axioms MathExploration.LawIdentifiability.totalMeasure_eq_iff
#print axioms MathExploration.LawIdentifiability.totalMeasure_eq_iff_f_eq_of_b_ne_e

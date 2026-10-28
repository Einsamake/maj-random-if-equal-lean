module
public import GeneralTankCdf
public import MeanRateOrder
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.CompletionTimeOrder
open MeasureTheory ProbabilityTheory

theorem cdf_mono_f_of_e_le_b (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (heb : e <= b) (hff : flo <= fhi) (t : Real) :
    cdf (BranchedLaw.totalMeasure a b e flo he hflo hclo) t <=
      cdf (BranchedLaw.totalMeasure a b e fhi he hfhi hchi) t := by
  by_cases ht : 0 <= t
  · rw [GeneralTankCdf.cdf_totalMeasure_eq_x2 a b e flo ha hb he hflo hclo t ht,
      GeneralTankCdf.cdf_totalMeasure_eq_x2 a b e fhi ha hb he hfhi hchi t ht]
    exact TankResponse.x2_mono_f_of_e_le_b a b e flo fhi ha.le heb hff t ht
  · rw [GeneralTankCdf.cdf_totalMeasure_negative a b e flo ha hb he hflo hclo t
        (lt_of_not_ge ht),
      GeneralTankCdf.cdf_totalMeasure_negative a b e fhi ha hb he hfhi hchi t
        (lt_of_not_ge ht)]

theorem cdf_antitone_f_of_b_le_e (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (hbe : b <= e) (hff : flo <= fhi) (t : Real) :
    cdf (BranchedLaw.totalMeasure a b e fhi he hfhi hchi) t <=
      cdf (BranchedLaw.totalMeasure a b e flo he hflo hclo) t := by
  by_cases ht : 0 <= t
  · rw [GeneralTankCdf.cdf_totalMeasure_eq_x2 a b e fhi ha hb he hfhi hchi t ht,
      GeneralTankCdf.cdf_totalMeasure_eq_x2 a b e flo ha hb he hflo hclo t ht]
    exact TankResponse.x2_antitone_f_of_b_le_e a b e flo fhi ha.le hbe hff t ht
  · rw [GeneralTankCdf.cdf_totalMeasure_negative a b e fhi ha hb he hfhi hchi t
        (lt_of_not_ge ht),
      GeneralTankCdf.cdf_totalMeasure_negative a b e flo ha hb he hflo hclo t
        (lt_of_not_ge ht)]

theorem cdf_eq_of_b_eq_e (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (hbe : b = e) (t : Real) :
    cdf (BranchedLaw.totalMeasure a b e flo he hflo hclo) t =
      cdf (BranchedLaw.totalMeasure a b e fhi he hfhi hchi) t := by
  by_cases ht : 0 <= t
  · rw [GeneralTankCdf.cdf_totalMeasure_eq_x2 a b e flo ha hb he hflo hclo t ht,
      GeneralTankCdf.cdf_totalMeasure_eq_x2 a b e fhi ha hb he hfhi hchi t ht]
    exact TankResponse.x2_eq_of_b_eq_e a b e flo fhi ha.le hbe t ht
  · rw [GeneralTankCdf.cdf_totalMeasure_negative a b e flo ha hb he hflo hclo t
        (lt_of_not_ge ht),
      GeneralTankCdf.cdf_totalMeasure_negative a b e fhi ha hb he hfhi hchi t
        (lt_of_not_ge ht)]

theorem totalMeasure_eq_of_b_eq_e (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi) (hbe : b = e) :
    BranchedLaw.totalMeasure a b e flo he hflo hclo =
      BranchedLaw.totalMeasure a b e fhi he hfhi hchi := by
  letI := BranchedLaw.totalMeasure_probability a b e flo ha hb he hflo hclo
  letI := BranchedLaw.totalMeasure_probability a b e fhi ha hb he hfhi hchi
  apply Measure.eq_of_cdf
  ext t
  exact cdf_eq_of_b_eq_e a b e flo fhi ha hb he hflo hfhi hclo hchi hbe t

theorem total_event_mono_f_of_e_le_b (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (heb : e <= b) (hff : flo <= fhi) (t : Real) :
    (BranchedLaw.law a b e flo he hflo hclo).real {w | BranchedLaw.total w <= t} <=
      (BranchedLaw.law a b e fhi he hfhi hchi).real {w | BranchedLaw.total w <= t} := by
  rw [GeneralTankCdf.total_event_eq_cdf a b e flo ha hb he hflo hclo t,
    GeneralTankCdf.total_event_eq_cdf a b e fhi ha hb he hfhi hchi t]
  exact cdf_mono_f_of_e_le_b a b e flo fhi ha hb he hflo hfhi hclo hchi heb hff t

theorem total_event_antitone_f_of_b_le_e (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi)
    (hbe : b <= e) (hff : flo <= fhi) (t : Real) :
    (BranchedLaw.law a b e fhi he hfhi hchi).real {w | BranchedLaw.total w <= t} <=
      (BranchedLaw.law a b e flo he hflo hclo).real {w | BranchedLaw.total w <= t} := by
  rw [GeneralTankCdf.total_event_eq_cdf a b e fhi ha hb he hfhi hchi t,
    GeneralTankCdf.total_event_eq_cdf a b e flo ha hb he hflo hclo t]
  exact cdf_antitone_f_of_b_le_e a b e flo fhi ha hb he hflo hfhi hclo hchi hbe hff t

theorem total_event_eq_of_b_eq_e (a b e flo fhi : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e)
    (hflo : 0 <= flo) (hfhi : 0 <= fhi)
    (hclo : 0 < e + flo) (hchi : 0 < e + fhi) (hbe : b = e) (t : Real) :
    (BranchedLaw.law a b e flo he hflo hclo).real {w | BranchedLaw.total w <= t} =
      (BranchedLaw.law a b e fhi he hfhi hchi).real {w | BranchedLaw.total w <= t} := by
  rw [GeneralTankCdf.total_event_eq_cdf a b e flo ha hb he hflo hclo t,
    GeneralTankCdf.total_event_eq_cdf a b e fhi ha hb he hfhi hchi t]
  exact cdf_eq_of_b_eq_e a b e flo fhi ha hb he hflo hfhi hclo hchi hbe t

end MathExploration.CompletionTimeOrder
#print axioms MathExploration.CompletionTimeOrder.cdf_mono_f_of_e_le_b
#print axioms MathExploration.CompletionTimeOrder.cdf_antitone_f_of_b_le_e
#print axioms MathExploration.CompletionTimeOrder.cdf_eq_of_b_eq_e
#print axioms MathExploration.CompletionTimeOrder.totalMeasure_eq_of_b_eq_e
#print axioms MathExploration.CompletionTimeOrder.total_event_mono_f_of_e_le_b
#print axioms MathExploration.CompletionTimeOrder.total_event_antitone_f_of_b_le_e
#print axioms MathExploration.CompletionTimeOrder.total_event_eq_of_b_eq_e
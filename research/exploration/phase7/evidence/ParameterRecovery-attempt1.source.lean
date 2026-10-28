module
public import MeanRateOrder
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ParameterRecovery
open MeasureTheory

-- The inputs a, b and e are fixed known rates; m is a population mean.
def delta (a b m : Real) : Real := b * (m - 1 / a)

def recover (a b e m : Real) : Real :=
  (b - e * delta a b m) / (delta a b m - 1)

theorem delta_meanFormula (a b e f : Real)
    (hb : b ≠ 0) (hc : e + f ≠ 0) :
    delta a b (MeanRateOrder.meanFormula a b e f) = (b + f) / (e + f) := by
  unfold delta MeanRateOrder.meanFormula
  field_simp [hb, hc]
  <;> ring

theorem delta_meanFormula_sub_one (a b e f : Real)
    (hb : b ≠ 0) (hc : e + f ≠ 0) :
    delta a b (MeanRateOrder.meanFormula a b e f) - 1 = (b - e) / (e + f) := by
  rw [delta_meanFormula a b e f hb hc]
  field_simp [hc]
  <;> ring

theorem delta_meanFormula_ne_one (a b e f : Real)
    (hb : b ≠ 0) (hc : e + f ≠ 0) (heb : e ≠ b) :
    delta a b (MeanRateOrder.meanFormula a b e f) ≠ 1 := by
  intro h
  have hd := delta_meanFormula_sub_one a b e f hb hc
  rw [h, sub_self] at hd
  exact (div_ne_zero (sub_ne_zero.mpr heb.symm) hc) hd.symm

theorem recover_meanFormula (a b e f : Real)
    (hb : b ≠ 0) (hc : e + f ≠ 0) (heb : e ≠ b) :
    recover a b e (MeanRateOrder.meanFormula a b e f) = f := by
  unfold recover
  rw [delta_meanFormula_sub_one a b e f hb hc, delta_meanFormula a b e f hb hc]
  field_simp [hc, sub_ne_zero.mpr heb.symm]
  <;> ring

theorem meanFormula_injective_f (a b e flo fhi : Real)
    (hb : b ≠ 0) (hclo : e + flo ≠ 0) (hchi : e + fhi ≠ 0) (heb : e ≠ b)
    (hm : MeanRateOrder.meanFormula a b e flo = MeanRateOrder.meanFormula a b e fhi) :
    flo = fhi := by
  calc
    flo = recover a b e (MeanRateOrder.meanFormula a b e flo) :=
      (recover_meanFormula a b e flo hb hclo heb).symm
    _ = recover a b e (MeanRateOrder.meanFormula a b e fhi) := congrArg (recover a b e) hm
    _ = fhi := recover_meanFormula a b e fhi hb hchi heb

theorem delta_total_mean_sub_one (a b e f : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    delta a b (integral (BranchedLaw.law a b e f he hf hc) BranchedLaw.total) - 1 =
      (b - e) / (e + f) := by
  rw [BranchedLaw.total_mean a b e f ha hb he hf hc]
  exact delta_meanFormula_sub_one a b e f (ne_of_gt hb) (ne_of_gt hc)

theorem delta_total_mean_ne_one (a b e f : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f)
    (heb : e ≠ b) :
    delta a b (integral (BranchedLaw.law a b e f he hf hc) BranchedLaw.total) ≠ 1 := by
  rw [BranchedLaw.total_mean a b e f ha hb he hf hc]
  exact delta_meanFormula_ne_one a b e f (ne_of_gt hb) (ne_of_gt hc) heb

theorem recover_total_mean (a b e f : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f)
    (heb : e ≠ b) :
    recover a b e (integral (BranchedLaw.law a b e f he hf hc) BranchedLaw.total) = f := by
  rw [BranchedLaw.total_mean a b e f ha hb he hf hc]
  exact recover_meanFormula a b e f (ne_of_gt hb) (ne_of_gt hc) heb

end MathExploration.ParameterRecovery
#print axioms MathExploration.ParameterRecovery.delta
#print axioms MathExploration.ParameterRecovery.recover
#print axioms MathExploration.ParameterRecovery.delta_meanFormula
#print axioms MathExploration.ParameterRecovery.delta_meanFormula_sub_one
#print axioms MathExploration.ParameterRecovery.delta_meanFormula_ne_one
#print axioms MathExploration.ParameterRecovery.recover_meanFormula
#print axioms MathExploration.ParameterRecovery.meanFormula_injective_f
#print axioms MathExploration.ParameterRecovery.delta_total_mean_sub_one
#print axioms MathExploration.ParameterRecovery.delta_total_mean_ne_one
#print axioms MathExploration.ParameterRecovery.recover_total_mean

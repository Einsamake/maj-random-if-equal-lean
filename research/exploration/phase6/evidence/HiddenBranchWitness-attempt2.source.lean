module
public import CompletionTimeOrder
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.HiddenBranchWitness
open MeasureTheory ProbabilityTheory Set

theorem branch_event_probability (a b e f : Real)
    (ha : 0 < a) (hb : 0 < b) (he : 0 <= e) (hf : 0 <= f)
    (hc : 0 < e + f) :
    (BranchedLaw.law a b e f he hf hc).real {w | BranchedLaw.J w = true} =
      f / (e + f) := by
  rw [(BranchedLaw.J_hasLaw a b e f ha hb he hf hc).measureReal_eq
    (p := fun j => j = true) (measurableSet_singleton true)]
  change (bernoulliMeasure true false (BranchedLaw.branchProb e f he hf hc)).real
    {true} = f / (e + f)
  rw [bernoulliMeasure_real_apply_of_mem_of_notMem _
    (measurableSet_singleton true) (by simp) (by simp)]
  rfl

theorem half_branch_probability :
    (BranchedLaw.law 1 1 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)).real
      {w | BranchedLaw.J w = true} = (1 / 3 : Real) := by
  rw [branch_event_probability 1 1 1 (1 / 2) (by norm_num) (by norm_num)]
  norm_num

theorem one_branch_probability :
    (BranchedLaw.law 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)).real
      {w | BranchedLaw.J w = true} = (1 / 2 : Real) := by
  rw [branch_event_probability 1 1 1 1 (by norm_num) (by norm_num)]
  norm_num

theorem same_totalMeasure :
    BranchedLaw.totalMeasure 1 1 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num) =
      BranchedLaw.totalMeasure 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) := by
  exact CompletionTimeOrder.totalMeasure_eq_of_b_eq_e 1 1 1 (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) rfl

theorem different_hidden_laws :
    BranchedLaw.law 1 1 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num) ≠
      BranchedLaw.law 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) := by
  intro h
  have hv := congrArg (fun m : Measure BranchedLaw.Sample =>
    m.real {w | BranchedLaw.J w = true}) h
  rw [half_branch_probability, one_branch_probability] at hv
  norm_num at hv

end MathExploration.HiddenBranchWitness
#print axioms MathExploration.HiddenBranchWitness.branch_event_probability
#print axioms MathExploration.HiddenBranchWitness.half_branch_probability
#print axioms MathExploration.HiddenBranchWitness.one_branch_probability
#print axioms MathExploration.HiddenBranchWitness.same_totalMeasure
#print axioms MathExploration.HiddenBranchWitness.different_hidden_laws
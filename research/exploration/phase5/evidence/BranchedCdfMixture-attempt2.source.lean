module
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.BranchedCdfMixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem map_nested_product_via (muC muB muA : Measure Real)
    [SFinite muB] [SFinite muA] :
    (muC.prod (muB.prod muA)).map (fun x => x.1 + (x.2.1 + x.2.2)) =
      muC ∗ (muB ∗ muA) := by
  have hp := Measure.map_prod_map (f := id) (g := fun x : Real × Real => x.1 + x.2)
    muC (muB.prod muA) measurable_id (by fun_prop)
  simp only [Measure.map_id] at hp
  change _ = (muC.prod ((muB.prod muA).map (fun x => x.1 + x.2))).map _
  rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem map_nested_product_direct (muC muB muA : Measure Real)
    [IsProbabilityMeasure muB] [SFinite muA] :
    (muC.prod (muB.prod muA)).map (fun x => x.1 + x.2.2) = muC ∗ muA := by
  have hs : (muB.prod muA).map Prod.snd = muA := by simp
  have hp := Measure.map_prod_map muC (muB.prod muA) measurable_id measurable_snd
  simp only [Measure.map_id, hs] at hp
  change _ = (muC.prod muA).map (fun x => x.1 + x.2)
  rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem map_bernoulli_nested_product (p : unitInterval) (muC muB muA : Measure Real)
    [SFinite muC] [IsProbabilityMeasure muB] [SFinite muA] :
    ((bernoulliMeasure true false p).prod (muC.prod (muB.prod muA))).map
      (fun x => x.2.1 + if x.1 then x.2.2.1 + x.2.2.2 else x.2.2.2) =
    unitInterval.toNNReal p • (muC ∗ (muB ∗ muA)) +
      unitInterval.toNNReal (unitInterval.symm p) • (muC ∗ muA) := by
  have hm : Measurable (fun x : Bool × (Real × (Real × Real)) =>
      x.2.1 + if x.1 then x.2.2.1 + x.2.2.2 else x.2.2.2) := by
    exact (measurable_fst.comp measurable_snd).add (Measurable.ite
      (measurable_fst (measurableSet_singleton true))
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).add
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  rw [bernoulliMeasure_def, Measure.add_prod, Measure.prod_smul_left,
    Measure.prod_smul_left, Measure.map_add _ _ hm,
    Measure.map_smul _ hm.aemeasurable, Measure.map_smul _ hm.aemeasurable,
    Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map hm (by fun_prop), Measure.map_map hm (by fun_prop)]
  simp only [Function.comp_def, reduceIte, Bool.false_eq_true]
  rw [map_nested_product_via, map_nested_product_direct]

end MathExploration.BranchedCdfMixture

#print axioms MathExploration.BranchedCdfMixture.map_nested_product_via
#print axioms MathExploration.BranchedCdfMixture.map_nested_product_direct
#print axioms MathExploration.BranchedCdfMixture.map_bernoulli_nested_product


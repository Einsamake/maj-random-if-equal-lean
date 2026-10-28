module
public import ExponentialMean
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.BranchedLaw
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

abbrev Sample := Bool × (ℝ × (ℝ × ℝ))

def branchProb (e f : ℝ) (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    unitInterval :=
  ⟨f / (e + f), div_nonneg hf hc.le, (div_le_one hc).2 (by linarith)⟩

def branchMeasure (e f : ℝ) (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    Measure Bool := bernoulliMeasure true false (branchProb e f he hf hc)

def waitLaw (a b c : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (expMeasure c).prod ((expMeasure b).prod (expMeasure a))

def law (a b e f : ℝ) (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) : Measure Sample :=
  (branchMeasure e f he hf hc).prod (waitLaw a b (e + f))

def J (ω : Sample) : Bool := ω.1

def Wc (ω : Sample) : ℝ := ω.2.1

def Wb (ω : Sample) : ℝ := ω.2.2.1

def Wa (ω : Sample) : ℝ := ω.2.2.2

def total (ω : Sample) : ℝ := Wc ω + if J ω then Wb ω + Wa ω else Wa ω

@[fun_prop] theorem J_measurable : Measurable J := measurable_fst
@[fun_prop] theorem Wc_measurable : Measurable Wc := measurable_fst.comp measurable_snd
@[fun_prop] theorem Wb_measurable : Measurable Wb :=
  measurable_fst.comp (measurable_snd.comp measurable_snd)
@[fun_prop] theorem Wa_measurable : Measurable Wa :=
  measurable_snd.comp (measurable_snd.comp measurable_snd)

@[fun_prop] theorem total_measurable : Measurable total := by
  exact Wc_measurable.add (Measurable.ite
    (J_measurable (measurableSet_singleton true))
    (Wb_measurable.add Wa_measurable) Wa_measurable)

def totalMeasure (a b e f : ℝ) (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) : Measure ℝ :=
  (law a b e f he hf hc).map total

theorem total_hasLaw (a b e f : ℝ) (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    HasLaw total (totalMeasure a b e f he hf hc) (law a b e f he hf hc) :=
  hasLaw_map total_measurable.aemeasurable

theorem waitLaw_probability (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsProbabilityMeasure (waitLaw a b c) := by
  letI := isProbabilityMeasure_expMeasure ha
  letI := isProbabilityMeasure_expMeasure hb
  letI := isProbabilityMeasure_expMeasure hc
  unfold waitLaw
  infer_instance

theorem law_probability (a b e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    IsProbabilityMeasure (law a b e f he hf hc) := by
  letI := waitLaw_probability a b (e + f) ha hb hc
  unfold law branchMeasure
  infer_instance

theorem totalMeasure_probability (a b e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    IsProbabilityMeasure (totalMeasure a b e f he hf hc) := by
  letI := law_probability a b e f ha hb he hf hc
  unfold totalMeasure
  infer_instance

theorem J_hasLaw (a b e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    HasLaw J (branchMeasure e f he hf hc) (law a b e f he hf hc) := by
  letI := waitLaw_probability a b (e + f) ha hb hc
  exact measurePreserving_fst.hasLaw

theorem Wc_hasLaw (a b e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    HasLaw Wc (expMeasure (e + f)) (law a b e f he hf hc) := by
  letI := isProbabilityMeasure_expMeasure ha
  letI := isProbabilityMeasure_expMeasure hb
  letI : IsProbabilityMeasure (branchMeasure e f he hf hc) := by
    unfold branchMeasure
    infer_instance
  exact (measurePreserving_fst.comp measurePreserving_snd).hasLaw

theorem Wb_hasLaw (a b e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    HasLaw Wb (expMeasure b) (law a b e f he hf hc) := by
  letI := isProbabilityMeasure_expMeasure ha
  letI := isProbabilityMeasure_expMeasure hc
  letI : IsProbabilityMeasure (branchMeasure e f he hf hc) := by
    unfold branchMeasure
    infer_instance
  exact ((measurePreserving_fst.comp measurePreserving_snd).comp
    measurePreserving_snd).hasLaw

theorem Wa_hasLaw (a b e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    HasLaw Wa (expMeasure a) (law a b e f he hf hc) := by
  letI := isProbabilityMeasure_expMeasure hb
  letI := isProbabilityMeasure_expMeasure hc
  letI : IsProbabilityMeasure (branchMeasure e f he hf hc) := by
    unfold branchMeasure
    infer_instance
  exact ((measurePreserving_snd.comp measurePreserving_snd).comp
    measurePreserving_snd).hasLaw

theorem rectangle_factorization (a b e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f)
    (sJ : Set Bool) (sC sB sA : Set ℝ) :
    law a b e f he hf hc
      {ω | J ω ∈ sJ ∧ Wc ω ∈ sC ∧ Wb ω ∈ sB ∧ Wa ω ∈ sA} =
      branchMeasure e f he hf hc sJ * expMeasure (e + f) sC *
        expMeasure b sB * expMeasure a sA := by
  letI := isProbabilityMeasure_expMeasure ha
  letI := isProbabilityMeasure_expMeasure hb
  letI := isProbabilityMeasure_expMeasure hc
  change law a b e f he hf hc (sJ ×ˢ (sC ×ˢ (sB ×ˢ sA))) = _
  simp only [law, waitLaw, Measure.prod_prod]
  ring

theorem coordinate_factorization (a b e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f)
    (sJ : Set Bool) (sC sB sA : Set ℝ) (hJ : MeasurableSet sJ)
    (hC : MeasurableSet sC) (hB : MeasurableSet sB) (hA : MeasurableSet sA) :
    law a b e f he hf hc
      {ω | J ω ∈ sJ ∧ Wc ω ∈ sC ∧ Wb ω ∈ sB ∧ Wa ω ∈ sA} =
      law a b e f he hf hc {ω | J ω ∈ sJ} *
      law a b e f he hf hc {ω | Wc ω ∈ sC} *
      law a b e f he hf hc {ω | Wb ω ∈ sB} *
      law a b e f he hf hc {ω | Wa ω ∈ sA} := by
  rw [(J_hasLaw a b e f ha hb he hf hc).measure_eq hJ,
    (Wc_hasLaw a b e f ha hb he hf hc).measure_eq hC,
    (Wb_hasLaw a b e f ha hb he hf hc).measure_eq hB,
    (Wa_hasLaw a b e f ha hb he hf hc).measure_eq hA]
  exact rectangle_factorization a b e f ha hb he hf hc sJ sC sB sA

theorem total_integrable (a b e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    Integrable total (law a b e f he hf hc) := by
  have ia := (Wa_hasLaw a b e f ha hb he hf hc).integrable
    (ExponentialMean.integrable_id a ha)
  have ib := (Wb_hasLaw a b e f ha hb he hf hc).integrable
    (ExponentialMean.integrable_id b hb)
  have ic := (Wc_hasLaw a b e f ha hb he hf hc).integrable
    (ExponentialMean.integrable_id (e + f) hc)
  exact ic.add (Integrable.piecewise
    (J_measurable (measurableSet_singleton true)).nullMeasurableSet
    (ib.add ia).integrableOn ia.integrableOn)

theorem total_mean (a b e f : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < e + f) :
    (∫ ω, total ω ∂law a b e f he hf hc) =
      1 / a + 1 / (e + f) + f / ((e + f) * b) := by
  letI := isProbabilityMeasure_expMeasure ha
  letI := isProbabilityMeasure_expMeasure hb
  letI := isProbabilityMeasure_expMeasure hc
  letI : IsProbabilityMeasure (branchMeasure e f he hf hc) := by
    unfold branchMeasure
    infer_instance
  have ia : Integrable (fun z : ℝ × (ℝ × ℝ) => z.2.2) (waitLaw a b (e + f)) :=
    ((ExponentialMean.integrable_id a ha).comp_snd (expMeasure b)).comp_snd
      (expMeasure (e + f))
  have ib : Integrable (fun z : ℝ × (ℝ × ℝ) => z.2.1) (waitLaw a b (e + f)) :=
    ((ExponentialMean.integrable_id b hb).comp_fst (expMeasure a)).comp_snd
      (expMeasure (e + f))
  have ic : Integrable (fun z : ℝ × (ℝ × ℝ) => z.1) (waitLaw a b (e + f)) :=
    (ExponentialMean.integrable_id (e + f) hc).comp_fst
      ((expMeasure b).prod (expMeasure a))
  rw [show (∫ ω, total ω ∂law a b e f he hf hc) =
      ∫ j, (∫ z : ℝ × (ℝ × ℝ), z.1 + if j then z.2.1 + z.2.2 else z.2.2
        ∂waitLaw a b (e + f)) ∂branchMeasure e f he hf hc from
      integral_prod total (total_integrable a b e f ha hb he hf hc)]
  rw [branchMeasure, integral_bernoulliMeasure]
  simp only [Bool.true_eq_true, if_true, Bool.false_eq_true, if_false, smul_eq_mul]
  rw [integral_add ic (ib.add ia), integral_add ib ia, integral_add ic ia]
  simp only [waitLaw, integral_fun_fst, integral_fun_snd, probReal_univ,
    one_smul, ExponentialMean.integral_id a ha, ExponentialMean.integral_id b hb,
    ExponentialMean.integral_id (e + f) hc]
  dsimp [branchProb]
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
  <;> ring

theorem example_half :
    (∫ ω, total ω ∂law 1 (1 / 2) 2 (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)) = (9 / 5 : ℝ) := by
  rw [total_mean 1 (1 / 2) 2 (1 / 2) (by norm_num) (by norm_num)]
  norm_num

theorem example_one :
    (∫ ω, total ω ∂law 1 (1 / 2) 2 1
      (by norm_num) (by norm_num) (by norm_num)) = (2 : ℝ) := by
  rw [total_mean 1 (1 / 2) 2 1 (by norm_num) (by norm_num)]
  norm_num

end MathExploration.BranchedLaw
#print axioms MathExploration.BranchedLaw.Sample
#print axioms MathExploration.BranchedLaw.branchProb
#print axioms MathExploration.BranchedLaw.branchMeasure
#print axioms MathExploration.BranchedLaw.waitLaw
#print axioms MathExploration.BranchedLaw.law
#print axioms MathExploration.BranchedLaw.J
#print axioms MathExploration.BranchedLaw.Wc
#print axioms MathExploration.BranchedLaw.Wb
#print axioms MathExploration.BranchedLaw.Wa
#print axioms MathExploration.BranchedLaw.total
#print axioms MathExploration.BranchedLaw.J_measurable
#print axioms MathExploration.BranchedLaw.Wc_measurable
#print axioms MathExploration.BranchedLaw.Wb_measurable
#print axioms MathExploration.BranchedLaw.Wa_measurable
#print axioms MathExploration.BranchedLaw.total_measurable
#print axioms MathExploration.BranchedLaw.totalMeasure
#print axioms MathExploration.BranchedLaw.total_hasLaw
#print axioms MathExploration.BranchedLaw.waitLaw_probability
#print axioms MathExploration.BranchedLaw.law_probability
#print axioms MathExploration.BranchedLaw.totalMeasure_probability
#print axioms MathExploration.BranchedLaw.J_hasLaw
#print axioms MathExploration.BranchedLaw.Wc_hasLaw
#print axioms MathExploration.BranchedLaw.Wb_hasLaw
#print axioms MathExploration.BranchedLaw.Wa_hasLaw
#print axioms MathExploration.BranchedLaw.rectangle_factorization
#print axioms MathExploration.BranchedLaw.coordinate_factorization
#print axioms MathExploration.BranchedLaw.total_integrable
#print axioms MathExploration.BranchedLaw.total_mean
#print axioms MathExploration.BranchedLaw.example_half
#print axioms MathExploration.BranchedLaw.example_one


module

public import MathResearchAnalysis.InfiniteGridModel
public import MathResearchAnalysis.FairMarksTransport

set_option autoImplicit false

/-!
# Genuine independent-fair-mark dynamics on the infinite lattice

The whole site/time mark field has its actual Bernoulli product law. Time
slices are measurable by their four local inputs, for arbitrary initial
configurations; no finite-state measurability argument is used on Z².
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.InfiniteGridRandomDynamics

abbrev Site := InfiniteGridModel.Site
abbrev Config := InfiniteGridModel.Config
abbrev Event := Site × Nat
abbrev Sample := FairMarks.Sample Event

def measure : Measure Sample := FairMarks.markMeasure Event

instance measure_probability : IsProbabilityMeasure measure := by
  unfold measure
  infer_instance

def marks (η : Sample) (j : Nat) (v : Site) : Bool := η (v, j)

def synchronous (initial : Config) (t : Nat) (η : Sample) : Config :=
  InfiniteGridModel.synchronous (marks η) initial t

def alternating (initial : Config) (phase : Bool) (t : Nat) (η : Sample) : Config :=
  InfiniteGridModel.alternating (marks η) initial phase t

theorem marks_measurable (j : Nat) : Measurable (fun η : Sample => marks η j) :=
  measurable_pi_iff.mpr (fun v => measurable_pi_apply (v, j))

theorem local_update_measurable (j : Nat) (v : Site) :
    Measurable (fun p : Config × Sample => InfiniteGridModel.update (marks p.2) j v p.1) := by
  have h (w : Site) : Measurable (fun p : Config × Sample => p.1 w) :=
    (measurable_pi_apply w).comp measurable_fst
  have hm : Measurable (fun p : Config × Sample => marks p.2 j v) :=
    (measurable_pi_apply (v, j)).comp measurable_snd
  have hf : Measurable (fun a : Bool × (Bool × (Bool × (Bool × Bool))) =>
      InfiniteGridModel.majority4 a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) :=
    measurable_of_countable _
  exact hf.comp ((h (InfiniteGridModel.north v)).prodMk
    ((h (InfiniteGridModel.east v)).prodMk
      ((h (InfiniteGridModel.south v)).prodMk ((h (InfiniteGridModel.west v)).prodMk hm))))

theorem synchronous_measurable (initial : Config) (t : Nat) :
    Measurable (synchronous initial t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    apply measurable_pi_iff.mpr
    intro v
    exact (local_update_measurable (t + 1) v).comp (ih.prodMk measurable_id)

theorem alternating_measurable (initial : Config) (phase : Bool) (t : Nat) :
    Measurable (alternating initial phase t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    apply measurable_pi_iff.mpr
    intro v
    by_cases h : InfiniteGridModel.colour v = BipartiteDynamics.activeColour phase (t + 1)
    · simpa only [Function.comp_def, id_eq, alternating, InfiniteGridModel.alternating_succ,
        ite_eq_left h] using
        (local_update_measurable (t + 1) v).comp (ih.prodMk measurable_id)
    · simpa only [Function.comp_def, id_eq, alternating, InfiniteGridModel.alternating_succ,
        ite_eq_right h] using
        (measurable_pi_apply v).comp ih

end MathResearchAnalysis.InfiniteGridRandomDynamics

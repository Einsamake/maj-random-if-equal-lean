module
public import MathResearchAnalysis.RationalProtectedExit
public import Mathlib.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
set_option autoImplicit false
/-! The standard mathlib predictable sigma-algebra of the original joint history,
reindexed by nonnegative physical time. Its exact defining rectangles form a
pi-system. Finite ambient measures agreeing there agree after trimming to this
standard sigma-algebra, not to the full ambient product. No compensation law
or right-continuation identification is presumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.PredictableClockSigma
open MeasureTheory Set
open DropletClockLaw (Sample)

/-- This is precisely the family in `Filtration.predictable`, with NNReal bot=0. -/
def generators (L : Nat) : Set (Set (NNReal × Sample L)) :=
  {A | ∃ E : Set (Sample L), MeasurableSet[RationalProtectedExit.nnHistory L 0] E ∧
    A = {0} ×ˢ E} ∪
  {A | ∃ s : NNReal, ∃ E : Set (Sample L),
    MeasurableSet[RationalProtectedExit.nnHistory L s] E ∧ A = Ioi s ×ˢ E}

theorem predictable_eq_generateFrom (L : Nat) :
    (RationalProtectedExit.nnHistory L).predictable =
      MeasurableSpace.generateFrom (generators L) := rfl

/-- The defining rectangles are closed under the required nonempty intersections. -/
theorem generators_isPiSystem (L : Nat) : IsPiSystem (generators L) := by
  intro A hA B hB hne
  rcases hA with ⟨E,hE,rfl⟩ | ⟨s,E,hE,rfl⟩
  · rcases hB with ⟨D,hD,rfl⟩ | ⟨t,D,hD,rfl⟩
    · apply Or.inl
      refine ⟨E ∩ D,hE.inter hD,?_⟩
      ext q
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff]
      tauto
    · obtain ⟨q,hq⟩ := hne
      have hzero : q.1 = 0 := Set.mem_singleton_iff.mp hq.1.1
      have hfuture : t < q.1 := hq.2.1
      rw [hzero] at hfuture
      exact False.elim ((not_lt_of_ge (show (0 : NNReal) ≤ t from bot_le)) hfuture)
  · rcases hB with ⟨D,hD,rfl⟩ | ⟨t,D,hD,rfl⟩
    · obtain ⟨q,hq⟩ := hne
      have hzero : q.1 = 0 := Set.mem_singleton_iff.mp hq.2.1
      have hfuture : s < q.1 := hq.1.1
      rw [hzero] at hfuture
      exact False.elim ((not_lt_of_ge (show (0 : NNReal) ≤ s from bot_le)) hfuture)
    · apply Or.inr
      refine ⟨max s t,E ∩ D,
        ((RationalProtectedExit.nnHistory L).mono (le_max_left s t) E hE).inter
          ((RationalProtectedExit.nnHistory L).mono (le_max_right s t) D hD),?_⟩
      ext q
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioi, max_lt_iff]
      tauto

theorem generator_measurable_predictable (L : Nat) (A : Set (NNReal × Sample L))
    (hA : A ∈ generators L) :
    MeasurableSet[(RationalProtectedExit.nnHistory L).predictable] A :=
  MeasurableSpace.measurableSet_generateFrom hA

theorem predictable_le_ambient (L : Nat) :
    (RationalProtectedExit.nnHistory L).predictable ≤
      (inferInstance : MeasurableSpace (NNReal × Sample L)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro E hE
    exact (measurableSet_singleton (0 : NNReal)).prod
      ((RationalProtectedExit.nnHistory L).le 0 E hE)
  · intro s E hE
    exact measurableSet_Ioi.prod ((RationalProtectedExit.nnHistory L).le s E hE)

theorem generator_measurable_ambient (L : Nat) (A : Set (NNReal × Sample L))
    (hA : A ∈ generators L) : MeasurableSet A :=
  predictable_le_ambient L A (generator_measurable_predictable L A hA)

/-- Uniqueness is a generic finite-measure helper; actual rectangle masses
must be proved separately before applying this to physical event measures. -/
theorem trim_eq_of_rectangle_masses (L : Nat)
    (μ ν : Measure (NNReal × Sample L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hzero : ∀ E : Set (Sample L), MeasurableSet[RationalProtectedExit.nnHistory L 0] E →
      μ ({0} ×ˢ E) = ν ({0} ×ˢ E))
    (hfuture : ∀ s : NNReal, ∀ E : Set (Sample L),
      MeasurableSet[RationalProtectedExit.nnHistory L s] E →
        μ (Ioi s ×ˢ E) = ν (Ioi s ×ˢ E))
    (huniv : μ univ = ν univ) :
    μ.trim (predictable_le_ambient L) = ν.trim (predictable_le_ambient L) := by
  let : MeasurableSpace (NNReal × Sample L) := (RationalProtectedExit.nnHistory L).predictable
  apply MeasureTheory.ext_of_generate_finite (generators L)
    (predictable_eq_generateFrom L) (generators_isPiSystem L)
  · intro A hA
    rw [trim_measurableSet_eq (predictable_le_ambient L) (generator_measurable_predictable L A hA),
      trim_measurableSet_eq (predictable_le_ambient L) (generator_measurable_predictable L A hA)]
    rcases hA with ⟨E,hE,rfl⟩ | ⟨s,E,hE,rfl⟩
    · exact hzero E hE
    · exact hfuture s E hE
  · rw [trim_measurableSet_eq (predictable_le_ambient L) MeasurableSet.univ,
      trim_measurableSet_eq (predictable_le_ambient L) MeasurableSet.univ]
    exact huniv

theorem trim_apply_on_predictable (L : Nat) (μ : Measure (NNReal × Sample L))
    (A : Set (NNReal × Sample L))
    (hA : MeasurableSet[(RationalProtectedExit.nnHistory L).predictable] A) :
    μ.trim (predictable_le_ambient L) A = μ A :=
  trim_measurableSet_eq (predictable_le_ambient L) hA
end MathResearchAnalysis.PredictableClockSigma

#print axioms MathResearchAnalysis.PredictableClockSigma.generators
#print axioms MathResearchAnalysis.PredictableClockSigma.predictable_eq_generateFrom
#print axioms MathResearchAnalysis.PredictableClockSigma.generators_isPiSystem
#print axioms MathResearchAnalysis.PredictableClockSigma.generator_measurable_predictable
#print axioms MathResearchAnalysis.PredictableClockSigma.predictable_le_ambient
#print axioms MathResearchAnalysis.PredictableClockSigma.generator_measurable_ambient
#print axioms MathResearchAnalysis.PredictableClockSigma.trim_eq_of_rectangle_masses
#print axioms MathResearchAnalysis.PredictableClockSigma.trim_apply_on_predictable

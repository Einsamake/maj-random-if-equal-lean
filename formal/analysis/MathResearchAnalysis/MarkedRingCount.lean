module
public import MathResearchAnalysis.MarkedClockFiltration
public import MathResearchAnalysis.ClockWordConsistency
set_option autoImplicit false
/-! Actual per-site and per-mark arrival counts in the original joint history.
Counts take values in ENNReal and therefore preserve infinitely many arrivals
on exceptional paths. Finiteness below finite horizons is deduced from the
actual clock law, not assumed or obtained by replacing infinity with zero. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedRingCount
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)

def count (L : Nat) (v : Vertex L) (t : Real) (z : Sample L) : ENNReal :=
  ∑' k : Nat, if ClockEventWord.eventTime z.1 (v,k) ≤ t then 1 else 0

def markedCount (L : Nat) (v : Vertex L) (b : Bool) (t : Real) (z : Sample L) : ENNReal :=
  ∑' k : Nat, if ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b then 1 else 0

theorem count_history_measurable (L : Nat) (v : Vertex L) (t : Real) :
    @Measurable (Sample L) ENNReal (MarkedClockFiltration.history L t) inferInstance (count L v t) := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  apply Measurable.tsum
  intro k
  exact Measurable.ite (MarkedClockFiltration.arrival_event_measurable L (v,k) (u:=t) le_rfl)
    measurable_const measurable_const

theorem markedCount_history_measurable (L : Nat) (v : Vertex L) (b : Bool) (t : Real) :
    @Measurable (Sample L) ENNReal (MarkedClockFiltration.history L t) inferInstance (markedCount L v b t) := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  apply Measurable.tsum
  intro k
  exact Measurable.ite (MarkedClockFiltration.marked_event_measurable L (v,k) b (u:=t) le_rfl)
    measurable_const measurable_const

theorem count_measurable (L : Nat) (v : Vertex L) (t : Real) : Measurable (count L v t) := by
  apply Measurable.tsum
  intro k
  exact Measurable.ite (measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const)
    measurable_const measurable_const

theorem markedCount_measurable (L : Nat) (v : Vertex L) (b : Bool) (t : Real) : Measurable (markedCount L v b t) := by
  apply Measurable.tsum
  intro k
  exact Measurable.ite ((measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const).inter
    (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L (v,k)) measurable_const))
    measurable_const measurable_const

theorem count_mono (L : Nat) (v : Vertex L) (z : Sample L) : Monotone (fun t : Real => count L v t z) := by
  intro s t hst
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases h : ClockEventWord.eventTime z.1 (v,k) ≤ s
  · simp only [ite_eq_left h,ite_eq_left (h.trans hst),le_refl]
  · simp only [ite_eq_right h]
    exact bot_le

theorem markedCount_mono (L : Nat) (v : Vertex L) (b : Bool) (z : Sample L) :
    Monotone (fun t : Real => markedCount L v b t z) := by
  intro s t hst
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases h : ClockEventWord.eventTime z.1 (v,k) ≤ s ∧ z.2 (v,k) = b
  · have ht : ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b := ⟨h.1.trans hst,h.2⟩
    simp only [ite_eq_left h,ite_eq_left ht,le_refl]
  · simp only [ite_eq_right h]
    exact bot_le

theorem markedCount_le_count (L : Nat) (v : Vertex L) (b : Bool) (t : Real) (z : Sample L) :
    markedCount L v b t z ≤ count L v t z := by
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases h : ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b
  · simp only [ite_eq_left h,ite_eq_left h.1,le_refl]
  · simp only [ite_eq_right h]
    exact bot_le

theorem markedCount_split (L : Nat) (v : Vertex L) (t : Real) (z : Sample L) :
    markedCount L v false t z + markedCount L v true t z = count L v t z := by
  rw [markedCount,markedCount,← ENNReal.tsum_add]
  apply tsum_congr
  intro k
  by_cases h : ClockEventWord.eventTime z.1 (v,k) ≤ t <;>
    cases z.2 (v,k) <;> simp [h]

theorem count_eq_card_of_coverage (L : Nat) (v : Vertex L) (t : Real) (z : Sample L)
    (s : Finset Nat) (hs : ∀ k, k ∈ s ↔ ClockEventWord.eventTime z.1 (v,k) ≤ t) :
    count L v t z = (s.card : ENNReal) := by
  classical
  unfold count
  rw [tsum_eq_sum (s := s) (fun k hk => ite_eq_right (fun h => hk ((hs k).mpr h)))]
  calc
    _ = ∑ _k ∈ s, (1 : ENNReal) := Finset.sum_congr rfl (fun k hk => ite_eq_left ((hs k).mp hk))
    _ = _ := by simp

theorem count_eq_finite_card (L : Nat) (v : Vertex L) (t : Real) (z : Sample L)
    (h : Set.Finite {k : Nat | ClockEventWord.eventTime z.1 (v,k) ≤ t}) :
    count L v t z = (h.toFinset.card : ENNReal) :=
  count_eq_card_of_coverage L v t z h.toFinset (fun _ => h.mem_toFinset)

theorem count_ne_top_of_finite (L : Nat) (v : Vertex L) (t : Real) (z : Sample L)
    (h : Set.Finite {k : Nat | ClockEventWord.eventTime z.1 (v,k) ≤ t}) :
    count L v t z ≠ ⊤ := by
  rw [count_eq_finite_card L v t z h]
  exact ENNReal.natCast_ne_top _

theorem count_finite_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ v : Vertex L, ∀ t : Real, count L v t z ≠ ⊤ := by
  have hfin : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ v : Vertex L, ∀ t : Real, Set.Finite {k : Nat | ClockEventWord.eventTime z.1 (v,k) ≤ t} :=
    (Measure.quasiMeasurePreserving_fst (μ := ExponentialClocks.clockMeasure (Vertex L))
      (ν := FairMarks.markMeasure (Event L))).ae (ArrivalFiltration.clock_locally_finite_ae (V:=Vertex L))
  filter_upwards [hfin] with z hz
  exact fun v t => count_ne_top_of_finite L v t z (hz v t)

theorem markedCount_finite_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ v : Vertex L, ∀ b : Bool, ∀ t : Real, markedCount L v b t z ≠ ⊤ := by
  filter_upwards [count_finite_ae L] with z hz
  exact fun v b t => ne_top_of_le_ne_top (hz v t) (markedCount_le_count L v b t z)
theorem count_eq_top_of_all_arrived (L : Nat) (v : Vertex L) (t : Real) (z : Sample L)
    (h : ∀ k : Nat, ClockEventWord.eventTime z.1 (v,k) ≤ t) : count L v t z = ⊤ := by
  simp only [count,ite_eq_left (h _)]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

theorem lintegral_count_eq_tsum (L : Nat) (v : Vertex L) (t : Real) :
    (∫⁻ z, count L v t z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑' k : Nat, ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        {z : Sample L | ClockEventWord.eventTime z.1 (v,k) ≤ t} := by
  unfold count
  calc
    _ = ∑' k : Nat, ∫⁻ z : Sample L, (if ClockEventWord.eventTime z.1 (v,k) ≤ t then 1 else 0)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
      lintegral_tsum (fun k => (Measurable.ite
        (measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const)
        measurable_const measurable_const).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro k
      have heq : (fun z : Sample L => (if ClockEventWord.eventTime z.1 (v,k) ≤ t then (1 : ENNReal) else 0)) =
          {z : Sample L | ClockEventWord.eventTime z.1 (v,k) ≤ t}.indicator (fun _ => (1 : ENNReal)) := by
        funext z
        simp only [Set.indicator,Set.mem_ofPred_eq]
      rw [heq,lintegral_indicator_const
        (measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const),one_mul]

theorem lintegral_markedCount_eq_tsum (L : Nat) (v : Vertex L) (b : Bool) (t : Real) :
    (∫⁻ z, markedCount L v b t z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑' k : Nat, ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        {z : Sample L | ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b} := by
  unfold markedCount
  calc
    _ = ∑' k : Nat, ∫⁻ z : Sample L,
        (if ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b then 1 else 0)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
      lintegral_tsum (fun k => (Measurable.ite
        ((measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const).inter
          (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L (v,k)) measurable_const))
        measurable_const measurable_const).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro k
      have heq : (fun z : Sample L => (if ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b
          then (1 : ENNReal) else 0)) =
          {z : Sample L | ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b}.indicator
            (fun _ => (1 : ENNReal)) := by
        funext z
        simp only [Set.indicator,Set.mem_ofPred_eq]
      have hm : MeasurableSet {z : Sample L | ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b} :=
        (measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const).inter
          (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L (v,k)) measurable_const)
      rw [heq,lintegral_indicator_const hm,one_mul]

theorem arrival_event_measure (L : Nat) (v : Vertex L) (k : Nat) (t : Real) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z : Sample L | ClockEventWord.eventTime z.1 (v,k) ≤ t} =
      ExponentialClocks.clockMeasure (Vertex L)
        {ω | ClockEventWord.eventTime ω (v,k) ≤ t} := by
  have heq : {z : Sample L | ClockEventWord.eventTime z.1 (v,k) ≤ t} =
      {ω : ExponentialClocks.Sample (Vertex L) | ClockEventWord.eventTime ω (v,k) ≤ t} ×ˢ
        (Set.univ : Set (FairMarks.Sample (Event L))) := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_prod,Set.mem_univ,and_true]
  change (ExponentialClocks.clockMeasure (Vertex L)).prod (FairMarks.markMeasure (Event L)) _ = _
  rw [heq,Measure.prod_prod,measure_univ,mul_one]

theorem lintegral_count_eq_clock_tsum (L : Nat) (v : Vertex L) (t : Real) :
    (∫⁻ z, count L v t z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑' k : Nat, ExponentialClocks.clockMeasure (Vertex L)
        {ω | ClockEventWord.eventTime ω (v,k) ≤ t} := by
  rw [lintegral_count_eq_tsum]
  exact tsum_congr (fun k => arrival_event_measure L v k t)
theorem count_zero_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ v : Vertex L, count L v 0 z = 0 := by
  have hp := (Measure.quasiMeasurePreserving_fst (μ := ExponentialClocks.clockMeasure (Vertex L))
    (ν := FairMarks.markMeasure (Event L))).ae (ClockEventWord.eventTime_positive_ae (V := Vertex L))
  filter_upwards [hp] with z hz
  intro v
  have hzero : ∀ k : Nat, (if ClockEventWord.eventTime z.1 (v,k) ≤ 0 then (1 : ENNReal) else 0) = 0 :=
    fun k => ite_eq_right (not_le_of_gt (hz (v,k)))
  simp only [count,hzero,tsum_zero]

theorem markedCount_zero_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ v : Vertex L, ∀ b : Bool, markedCount L v b 0 z = 0 := by
  filter_upwards [count_zero_ae L] with z hz
  intro v b
  apply le_antisymm _ bot_le
  simpa [hz v] using markedCount_le_count L v b 0 z
end MathResearchAnalysis.MarkedRingCount

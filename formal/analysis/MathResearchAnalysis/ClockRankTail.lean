module

public import MathResearchAnalysis.FiniteRankWitness
public import MathResearchAnalysis.ClockEventWord
public import MathResearchAnalysis.SquareGreedyPaths

set_option autoImplicit false

/-!
# A closed rank tail for the actual bounded-time clock word

Ranks are computed on the genuine newest-first event word. Their deterministic
causal-chain witnesses are chronological sublists of that word. The actual
greedy clock chain is dominated by the selected ring times, placing every
large-rank sample in the finite union of fast spatial paths, almost surely.
The final probability bound has no waiting-law, rank-witness, or tail input.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace MathResearchAnalysis.ClockRankTail

abbrev Event (n : Nat) := ClockEventWord.Event (SquareTasks.Vertex n)

def eventConflict {n : Nat} (a b : Event n) : Bool :=
  decide (a.1 = b.1 ∨ SquareTasks.Adjacent a.1 b.1)

theorem eventConflict_eq_true_iff {n : Nat} (a b : Event n) :
    eventConflict a b = true ↔ SquareGreedyPaths.Step a.1 b.1 := by
  simp only [eventConflict, decide_eq_true_eq, SquareGreedyPaths.Step]

theorem eventConflict_reverse_step {n : Nat} {a b : Event n}
    (h : eventConflict a b = true) : SquareGreedyPaths.Step b.1 a.1 := by
  rcases (eventConflict_eq_true_iff a b).mp h with heq | hadj
  · exact Or.inl heq.symm
  · exact Or.inr (SquareTasks.adjacent_symmetric hadj)

/-- The event is defined from computed ranks, not from a supplied chain witness. -/
def rankLarge (n : Nat) (t : ℝ) (q : Nat) :
    Set (ExponentialClocks.Sample (SquareTasks.Vertex n)) :=
  {ω | ∃ (event : Event n) (rank : Nat),
    (event, rank) ∈ FiniteRankWitness.annotate eventConflict (ClockEventWord.word ω t) ∧
      q ≤ rank}

theorem rankLarge_measurable (n : Nat) (t : ℝ) (q : Nat) :
    MeasurableSet (rankLarge n t q) := by
  let : MeasurableSpace (List (Event n)) := ⊤
  have hs : MeasurableSet {events : List (Event n) |
      ∃ (event : Event n) (rank : Nat),
        (event, rank) ∈ FiniteRankWitness.annotate eventConflict events ∧ q ≤ rank} := by
    trivial
  exact hs.preimage (ClockEventWord.word_measurable t)

theorem rankLarge_mono_threshold (n : Nat) (t : ℝ) {q r : Nat} (hqr : q ≤ r) :
    rankLarge n t r ⊆ rankLarge n t q := by
  rintro ω ⟨event, rank, hmem, hr⟩
  exact ⟨event, rank, hmem, hqr.trans hr⟩

/-- A chronological conflict sublist gives an actual finite-family fast path. -/
theorem word_chain_fastEvent (n : Nat)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ)
    (q : Nat) (hq : 0 < q) (chain : List (Event n))
    (hlen : chain.length = q) (hsub : chain.Sublist (ClockEventWord.word ω t).reverse)
    (hchain : chain.IsChain (fun earlier later => eventConflict later earlier = true))
    (hpositive : ∀ event ∈ ClockEventWord.word ω t,
      0 < ClockEventWord.eventTime ω event ∧ ClockEventWord.eventTime ω event ≤ t) :
    ω ∈ SquareGreedyPaths.fastEvent n q t := by
  let selected : Nat → Event n := fun i => chain.getD i (SquareGreedyPaths.origin n, 0)
  let p : Nat → SquareTasks.Vertex n := fun i => (selected i).1
  let index : Nat → Nat := fun i => (selected i).2
  have hat (i : Nat) (hi : i < chain.length) : selected i = chain[i]'hi :=
    (List.getElem_eq_getD (SquareGreedyPaths.origin n, 0)).symm
  have hmem (i : Nat) (hi : i < q) : selected i ∈ ClockEventWord.word ω t := by
    have hic : i < chain.length := by omega
    have hm : selected i ∈ chain := by
      rw [hat i hic]
      exact List.getElem_mem hic
    exact List.mem_reverse.mp (hsub.subset hm)
  have hchronological : chain.Pairwise
      (fun earlier later => ClockEventWord.eventTime ω earlier <
        ClockEventWord.eventTime ω later) :=
    List.Pairwise.sublist hsub
      (List.pairwise_reverse.mpr (ClockEventWord.word_strictly_decreasing ω t))
  have hpath : ∀ i, i + 1 < q → SquareGreedyPaths.Step (p i) (p (i + 1)) := by
    intro i hi
    have hic : i + 1 < chain.length := by omega
    have hc := eventConflict_reverse_step (hchain.getElem i hic)
    simpa only [p, hat i (by omega), hat (i + 1) hic] using hc
  have hstart : 0 < ArrivalFiltration.chronologicalArrival (p 0) (index 0) ω :=
    (hpositive (selected 0) (hmem 0 hq)).1
  have hstep : ∀ i, i + 1 < q →
      ArrivalFiltration.chronologicalArrival (p i) (index i) ω <
        ArrivalFiltration.chronologicalArrival (p (i + 1)) (index (i + 1)) ω := by
    intro i hi
    have hic : i + 1 < chain.length := by omega
    have hs := hchronological.isChain.getElem i hic
    simpa only [p, index, hat i (by omega), hat (i + 1) hic, ClockEventWord.eventTime] using hs
  have hlast : ArrivalFiltration.chronologicalArrival (p (q - 1)) (index (q - 1)) ω ≤ t :=
    (hpositive (selected (q - 1)) (hmem (q - 1) (by omega))).2
  apply SquareGreedyPaths.fastEvent_of_nat_witness n q hq p hpath ω
  exact (GreedyClockChain.chainTime_le_witness p index q ω hq hstart hstep).trans
    (WithTop.coe_le_coe.mpr hlast)

/-- The rank recurrence itself provides the chain used by the clock comparison. -/
theorem rankLarge_fastEvent (n : Nat)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ)
    (q : Nat) (hq : 0 < q)
    (hpositive : ∀ event ∈ ClockEventWord.word ω t,
      0 < ClockEventWord.eventTime ω event ∧ ClockEventWord.eventTime ω event ≤ t)
    (hlarge : ω ∈ rankLarge n t q) :
    ω ∈ SquareGreedyPaths.fastEvent n q t := by
  rcases hlarge with ⟨event, rank, hmem, hqr⟩
  obtain ⟨chain, hsub, hlen, _hlast, hchain⟩ :=
    FiniteRankWitness.annotated_truncated_chain_witness eventConflict event rank q hmem hq hqr
  exact word_chain_fastEvent n ω t q hq chain hlen hsub hchain hpositive

theorem rankLarge_fastEvent_ae (n : Nat) (t : ℝ) (q : Nat) (hq : 0 < q) :
    rankLarge n t q ≤ᵐ[ExponentialClocks.clockMeasure (SquareTasks.Vertex n)]
      SquareGreedyPaths.fastEvent n q t := by
  filter_upwards [ClockEventWord.word_positive_bounded_ae (V := SquareTasks.Vertex n)]
    with ω hp
  exact rankLarge_fastEvent n ω t q hq (hp t)

/-- A closed rank probability bound derived entirely from the constructed clock model. -/
theorem rankLarge_half_tail (n : Nat) (t : ℝ) (q : Nat) (hq : 0 < q) :
    (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real (rankLarge n t q) ≤
      ((((n + 2) ^ 2 : Nat) : ℝ) / 5) * Real.exp (9 * t) * ((2 : ℝ)⁻¹) ^ q := by
  apply le_trans _ (SquareGreedyPaths.fastEvent_half_tail n q hq t).2
  exact ENNReal.toReal_mono (by finiteness) (measure_mono_ae (rankLarge_fastEvent_ae n t q hq))

end MathResearchAnalysis.ClockRankTail

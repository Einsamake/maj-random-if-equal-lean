module

public import MathResearchAnalysis.RankScanEmbedding
public import MathResearchAnalysis.SquareScanKernel
public import MathResearchAnalysis.ClockCensoringKernel

set_option autoImplicit false

/-!
# Actual rank-completed scans compared with the clock endpoint kernel

The completed per-slot enumeration may depend on the clock sample. Each slot
is a full color enumeration, so its cold operator is the fixed scan operator.
The genuine computed-rank bound supplies the sublist needed by finite PW.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.RankClockCensoring

abbrev Site (n : Nat) := SquareTasks.Vertex n
abbrev Config (n : Nat) := SquareSpin.Config n
abbrev Sample (n : Nat) := ExponentialClocks.Sample (Site n)

theorem completed_scan_eq_scanMean {n : Nat} (ω : Sample n) (t : ℝ) (q : Nat)
    (φ : Config n → ℝ) (initial : Config n) :
    ZeroTemperature.coldWord (RankScanEmbedding.scanWord ω t q) φ initial =
      SquareScanKernel.scanMean n true 0 (2 * q) φ initial := by
  simpa only [RankScanEmbedding.scanWord, Nat.zero_add] using
    SquareScanKernel.coldWord_scan_eq_scanMean true 0 (2 * q)
    (fun j => RankScanEmbedding.completionBatch ω t (j + 1))
    (fun j _ => by simpa only [Nat.zero_add] using
      RankScanEmbedding.completionBatch_nodup ω t (j + 1))
    (fun j _ v => by simpa using RankScanEmbedding.mem_completionBatch_iff ω t (j + 1) v)
    φ initial

theorem clock_coldWord_eq_target {n : Nat} (ω : Sample n) (t : ℝ)
    (φ : Config n → ℝ) (initial : Config n) :
    ClockEndpointMean.wordMean n t φ initial ω =
      ZeroTemperature.coldWord ((RankSlotEmbedding.target ω t).map Prod.fst) φ initial := by
  exact ClockCensoringKernel.coldWord_eq_of_marked_execute_eq _ _
    (List.nodup_reverse.mpr (ClockEventWord.word_nodup ω t))
    (RankSlotEmbedding.target_nodup ω t)
    (fun η f => RankSlotEmbedding.executeClockWord_eq_target η ω t f) φ initial

theorem source_rank_le_of_not_rankLarge {n : Nat} (ω : Sample n) (t : ℝ) (q : Nat)
    (h : ω ∉ ClockRankTail.rankLarge n t q) :
    ∀ a ∈ RankSlotEmbedding.source ω t, a.2 ≤ q := by
  rintro ⟨e, r⟩ ha
  have hm : (e, r) ∈ FiniteRankWitness.annotate ClockRankTail.eventConflict
      (ClockEventWord.word ω t) := List.mem_reverse.mp ha
  by_contra hr
  exact h ⟨e, r, hm, by omega⟩

/-- The comparison has only the genuine computed-rank event as its clock condition. -/
theorem scanMean_le_wordMean {n : Nat} (ω : Sample n) (t : ℝ) (q : Nat)
    (h : ω ∉ ClockRankTail.rankLarge n t q)
    (φ : Config n → ℝ) (hφ : Monotone φ) :
    SquareScanKernel.scanMean n true 0 (2 * q) φ (SquarePWMeasure.topConfig n) ≤
      ClockEndpointMean.wordMean n t φ (SquarePWMeasure.topConfig n) ω := by
  have hsub := RankScanEmbedding.target_sites_sublist_scanWord ω t q
    (source_rank_le_of_not_rankLarge ω t q h)
  have hpw := SquarePWCensoring.actualMajorityWordMean_censoring hsub φ hφ
  rw [← ZeroTemperature.coldWord_eq_actualMajorityWordMean,
    ← ZeroTemperature.coldWord_eq_actualMajorityWordMean,
    completed_scan_eq_scanMean] at hpw
  rw [clock_coldWord_eq_target]
  exact hpw

/-- The deterministic task-site scan agrees with the fixed complete-color scan. -/
theorem layerSites_eq_scanWord (n : Nat) (c : Bool) (k : Nat) :
    ClockCensoringKernel.layerSites n c k = SquareScanKernel.scanWord n c 0 (k + 1) := by
  simp [ClockCensoringKernel.layerSites, ClockSelectedWord.layerTasks,
    List.map_flatMap, List.map_map, Function.comp_def, SquareScanKernel.scanWord,
    SquareScanKernel.taskWord]

theorem clockMean_le_scanMean_of_completed (n : Nat) (c : Bool) (k : Nat)
    (ω : Sample n) (hω : ClockSelectedWord.Regular n ω) (t : ℝ)
    (hmax : ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ))
    (φ : Config n → ℝ) (hφ : Monotone φ) :
    ClockEndpointMean.wordMean n t φ (SquarePWMeasure.topConfig n) ω ≤
      SquareScanKernel.scanMean n c 0 (k + 1) φ (SquarePWMeasure.topConfig n) := by
  have h := ClockCensoringKernel.coldWord_clock_le_layerSites n c k ω hω t hmax φ hφ
  rw [layerSites_eq_scanWord] at h
  exact h

end MathResearchAnalysis.RankClockCensoring

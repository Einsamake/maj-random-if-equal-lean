module

public import MathResearchAnalysis.SquareScanKernel
public import MathResearchAnalysis.SquarePWCensoring

set_option autoImplicit false

/-!
# Censoring comparisons between actual checkerboard scan phases

Deleting a terminal layer decreases the number of slots. Deleting an initial
layer flips the initial colour. Both comparisons below are derived from the
actual finite-word censoring theorem and concrete task identities.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.SquareScanOrder

open SquareScanKernel

theorem tasks_succ_flip (n : ℕ) (c : Bool) (k : ℕ) :
    SquareTasks.tasks n c (k + 1) = SquareTasks.tasks n (!c) k := by
  ext v
  simp only [SquareTasks.mem_tasks_iff]
  cases c <;> simp <;> omega

theorem taskWord_succ_flip (n : ℕ) (c : Bool) (k : ℕ) :
    taskWord n c (k + 1) = taskWord n (!c) k := by
  simp only [taskWord, tasks_succ_flip]

theorem scanWord_append (n : ℕ) (c : Bool) (first left right : ℕ) :
    scanWord n c first (left + right) =
      scanWord n c first left ++ scanWord n c (first + left) right := by
  simp only [scanWord, List.range_add, List.flatMap_append, List.flatMap_map,
    Nat.add_assoc]

theorem scanWord_succ_right (n : ℕ) (c : Bool) (first count : ℕ) :
    scanWord n c first (count + 1) =
      scanWord n c first count ++ taskWord n c (first + count) := by
  rw [scanWord_append]
  simp [scanWord]

theorem scanWord_succ_left (n : ℕ) (c : Bool) (first count : ℕ) :
    scanWord n c first (count + 1) =
      taskWord n c first ++ scanWord n c (first + 1) count := by
  rw [show count + 1 = 1 + count by omega, scanWord_append]
  simp [scanWord]

theorem scanWord_shift_flip (n : ℕ) (c : Bool) (first count : ℕ) :
    scanWord n c (first + 1) count = scanWord n (!c) first count := by
  unfold scanWord
  congr 1
  funext j
  rw [show first + 1 + j = (first + j) + 1 by omega, taskWord_succ_flip]

theorem scanWord_sublist_succ (n : ℕ) (c : Bool) (first count : ℕ) :
    (scanWord n c first count).Sublist (scanWord n c first (count + 1)) := by
  rw [scanWord_succ_right]
  exact List.sublist_append_left _ _

theorem scanWord_flip_sublist_succ (n : ℕ) (c : Bool) (first count : ℕ) :
    (scanWord n (!c) first count).Sublist (scanWord n c first (count + 1)) := by
  rw [scanWord_succ_left, ← scanWord_shift_flip]
  exact List.sublist_append_right _ _

theorem scanMean_censoring {n : ℕ} {c d : Bool} {first count otherFirst otherCount : ℕ}
    (sub : (scanWord n c first count).Sublist (scanWord n d otherFirst otherCount))
    (φ : Config n → ℝ) (hφ : Monotone φ) :
    scanMean n d otherFirst otherCount φ (SquarePWMeasure.topConfig n) ≤
      scanMean n c first count φ (SquarePWMeasure.topConfig n) := by
  unfold scanMean
  simp only [ZeroTemperature.coldWord_eq_actualMajorityWordMean]
  exact SquarePWCensoring.actualMajorityWordMean_censoring sub φ hφ

theorem scanMean_succ_le (n : ℕ) (c : Bool) (first count : ℕ)
    (φ : Config n → ℝ) (hφ : Monotone φ) :
    scanMean n c first (count + 1) φ (SquarePWMeasure.topConfig n) ≤
      scanMean n c first count φ (SquarePWMeasure.topConfig n) :=
  scanMean_censoring (scanWord_sublist_succ n c first count) φ hφ

theorem scanMean_opposite_succ_le (n : ℕ) (c : Bool) (first count : ℕ)
    (φ : Config n → ℝ) (hφ : Monotone φ) :
    scanMean n c first (count + 1) φ (SquarePWMeasure.topConfig n) ≤
      scanMean n (!c) first count φ (SquarePWMeasure.topConfig n) :=
  scanMean_censoring (scanWord_flip_sublist_succ n c first count) φ hφ

end MathResearchAnalysis.SquareScanOrder

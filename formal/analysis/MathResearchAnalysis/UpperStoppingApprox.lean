module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

/-!
# Countable upper approximations of possibly infinite stopping times

Rounding uses the least nonnegative grid point above the actual extended
time. Infinity stays infinity. Stopping follows from a countable union of
observations at grid points, without right-continuity of the filtration.
-/

public noncomputable section

open MeasureTheory Set

namespace MathResearchAnalysis.UpperStoppingApprox

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

@[expose] def grid (δ : ℝ) (n : Nat) : ℝ := δ * n

@[expose] def round (δ : ℝ) (s : WithTop ℝ) : WithTop ℝ := by
  classical
  exact if hex : ∃ n : Nat, s ≤ (grid δ n : WithTop ℝ) then
    (grid δ (Nat.find hex) : WithTop ℝ)
  else ⊤

@[expose] def approx (δ : ℝ) (time : Ω → WithTop ℝ) : Ω → WithTop ℝ :=
  fun ω => round δ (time ω)

theorem grid_nonnegative {δ : ℝ} (hδ : 0 ≤ δ) (n : Nat) : 0 ≤ grid δ n :=
  mul_nonneg hδ (Nat.cast_nonneg n)

theorem grid_monotone {δ : ℝ} (hδ : 0 ≤ δ) : Monotone (grid δ) := by
  intro n k hnk
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnk) hδ

theorem round_eq_coe (δ : ℝ) (s : WithTop ℝ)
    (hex : ∃ n : Nat, s ≤ (grid δ n : WithTop ℝ)) :
    round δ s = (grid δ (Nat.find hex) : WithTop ℝ) := by
  simp only [round, dite_eq_left hex]

theorem round_eq_top_iff (δ : ℝ) (s : WithTop ℝ) :
    round δ s = ⊤ ↔ ¬ ∃ n : Nat, s ≤ (grid δ n : WithTop ℝ) := by
  classical
  by_cases hex : ∃ n : Nat, s ≤ (grid δ n : WithTop ℝ) <;> simp [round, hex]

theorem round_top (δ : ℝ) : round δ ⊤ = ⊤ := by
  apply (round_eq_top_iff δ ⊤).mpr
  simp

theorem exists_grid {δ : ℝ} (hδ : 0 < δ) (s : WithTop ℝ) (hs : s ≠ ⊤) :
    ∃ n : Nat, s ≤ (grid δ n : WithTop ℝ) := by
  lift s to ℝ using hs
  obtain ⟨n, hn⟩ := exists_nat_gt (s / δ)
  refine ⟨n, WithTop.coe_le_coe.mpr ?_⟩
  have h := (div_lt_iff₀ hδ).mp hn
  simpa only [grid, mul_comm] using h.le

theorem round_ne_top_iff {δ : ℝ} (hδ : 0 < δ) (s : WithTop ℝ) :
    round δ s ≠ ⊤ ↔ s ≠ ⊤ := by
  constructor
  · intro h hs
    exact h (hs ▸ round_top δ)
  · intro hs
    rw [round_eq_coe δ s (exists_grid hδ s hs)]
    exact WithTop.coe_ne_top

theorem le_round (δ : ℝ) (s : WithTop ℝ) : s ≤ round δ s := by
  classical
  by_cases hex : ∃ n : Nat, s ≤ (grid δ n : WithTop ℝ)
  · rw [round_eq_coe δ s hex]
    exact Nat.find_spec hex
  · rw [(round_eq_top_iff δ s).mpr hex]
    exact le_top

theorem round_nonnegative {δ : ℝ} (hδ : 0 ≤ δ) (s : WithTop ℝ) :
    0 ≤ round δ s := by
  classical
  by_cases hex : ∃ n : Nat, s ≤ (grid δ n : WithTop ℝ)
  · rw [round_eq_coe δ s hex]
    exact WithTop.coe_le_coe.mpr (grid_nonnegative hδ _)
  · rw [(round_eq_top_iff δ s).mpr hex]
    exact le_top

theorem round_le_iff {δ : ℝ} (hδ : 0 ≤ δ) (s : WithTop ℝ) (t : ℝ) :
    round δ s ≤ (t : WithTop ℝ) ↔
      ∃ n : Nat, grid δ n ≤ t ∧ s ≤ (grid δ n : WithTop ℝ) := by
  classical
  by_cases hex : ∃ n : Nat, s ≤ (grid δ n : WithTop ℝ)
  · rw [round_eq_coe δ s hex, WithTop.coe_le_coe]
    constructor
    · exact fun ht => ⟨Nat.find hex, ht, Nat.find_spec hex⟩
    · rintro ⟨n, hnt, hn⟩
      exact (grid_monotone hδ (Nat.find_min' hex hn)).trans hnt
  · simp only [(round_eq_top_iff δ s).mpr hex, WithTop.not_top_le_coe, false_iff]
    rintro ⟨n, _, hn⟩
    exact hex ⟨n, hn⟩

theorem approx_isStoppingTime (clocks : Filtration ℝ mΩ) {δ : ℝ} (hδ : 0 ≤ δ)
    (time : Ω → WithTop ℝ) (hstop : IsStoppingTime clocks time) :
    IsStoppingTime clocks (approx δ time) := by
  intro t
  have heq : {ω | approx δ time ω ≤ (t : WithTop ℝ)} =
      ⋃ n : Nat, {ω | grid δ n ≤ t ∧ time ω ≤ (grid δ n : WithTop ℝ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, approx]
    exact round_le_iff hδ (time ω) t
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  by_cases hn : grid δ n ≤ t
  · simp only [hn, true_and]
    exact clocks.mono hn _ (hstop (grid δ n))
  · simp only [hn, false_and, Set.ofPred_false]
    exact @MeasurableSet.empty _ (clocks t)

theorem approx_countable_range (δ : ℝ) (time : Ω → WithTop ℝ) :
    (Set.range (approx δ time)).Countable := by
  classical
  apply ((Set.countable_range (fun n : Nat => (grid δ n : WithTop ℝ))).union
    (Set.countable_singleton ⊤)).mono
  rintro _ ⟨ω, rfl⟩
  by_cases hex : ∃ n : Nat, time ω ≤ (grid δ n : WithTop ℝ)
  · exact Or.inl ⟨Nat.find hex, (round_eq_coe δ (time ω) hex).symm⟩
  · exact Or.inr ((round_eq_top_iff δ (time ω)).mpr hex)

theorem round_lt_add {δ : ℝ} (hδ : 0 < δ) (s : WithTop ℝ)
    (hs : s ≠ ⊤) (hpos : 0 ≤ s) :
    round δ s < s + (δ : WithTop ℝ) := by
  lift s to ℝ using hs
  have hex := exists_grid hδ (s : WithTop ℝ) WithTop.coe_ne_top
  rw [round_eq_coe δ (s : WithTop ℝ) hex, ← WithTop.coe_add]
  apply WithTop.coe_lt_coe.mpr
  have hs0 : 0 ≤ s := by simpa using hpos
  by_cases hz : Nat.find hex = 0
  · rw [hz]
    simp only [grid, Nat.cast_zero, mul_zero]
    linarith
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hprev : ¬ (s : WithTop ℝ) ≤ (grid δ n : WithTop ℝ) :=
      Nat.find_min hex (by omega)
    have hlt : grid δ n < s := by simpa only [WithTop.coe_le_coe, not_le] using hprev
    rw [hn]
    simp only [grid, Nat.cast_succ] at *
    nlinarith

theorem representative_error {δ : ℝ} (hδ : 0 < δ) (s : WithTop ℝ)
    (hs : s ≠ ⊤) (hpos : 0 ≤ s) :
    0 ≤ (round δ s).untopD 0 - s.untopD 0 ∧
      (round δ s).untopD 0 - s.untopD 0 < δ := by
  have hfinite := (round_ne_top_iff hδ s).mpr hs
  have hle := le_round δ s
  have hlt := round_lt_add hδ s hs hpos
  lift s to ℝ using hs
  lift round δ (s : WithTop ℝ) to ℝ using hfinite with z hz
  simp only [WithTop.untopD_coe, WithTop.coe_le_coe] at hle ⊢
  rw [← WithTop.coe_add, WithTop.coe_lt_coe] at hlt
  constructor <;> linarith

end MathResearchAnalysis.UpperStoppingApprox

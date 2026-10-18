module

public import MathResearchAnalysis.InfiniteGridTranslation
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Basic.Finite.Prod

set_option autoImplicit false

/-!
# Original half-open-square perturbation diameter

Containing squares allow arbitrary integer translations and every natural side
length, including zero and one. No containing square is assumed in the diameter
definition: sets with no finite containing square have infinite diameter.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.PerturbationGeometry

abbrev Site := InfiniteGridModel.Site
abbrev Config := InfiniteGridModel.Config

open InfiniteGridModel InfiniteGridTranslation

def difference (f : Config) (b : Bool) : Set Site := {z | f z ≠ b}

def FinitePerturbation (f : Config) (b : Bool) : Prop := (difference f b).Finite

def Fits (A : Set Site) (L : Nat) : Prop :=
  ∃ a : Site, A ⊆ {z | InsideTranslated L a z}

def diameter (A : Set Site) : ℕ∞ := by
  classical
  exact if h : ∃ L, Fits A L then (Nat.find h : ℕ∞) else ⊤

theorem fits_empty (L : Nat) : Fits ∅ L := ⟨(0, 0), Set.empty_subset _⟩

theorem fits_mono {A : Set Site} {L K : Nat} (hLK : L ≤ K)
    (hA : Fits A L) : Fits A K := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨a, fun z hz => ?_⟩
  have hin := ha hz
  simp only [Set.mem_ofPred_eq, InsideTranslated, Inside, shift] at hin ⊢
  omega

theorem finite_of_fits {A : Set Site} {L : Nat} (hA : Fits A L) : A.Finite := by
  obtain ⟨a, ha⟩ := hA
  refine ((Set.finite_Ico a.1 (a.1 + (L : ℤ))).prod
    (Set.finite_Ico a.2 (a.2 + (L : ℤ)))).subset ?_
  intro z hz
  have hin := ha hz
  simp only [Set.mem_ofPred_eq, InsideTranslated, Inside, shift] at hin
  simp only [Set.mem_prod, Set.mem_Ico]
  omega

theorem exists_fits_of_finite {A : Set Site} (hA : A.Finite) : ∃ L, Fits A L := by
  obtain ⟨r, hr⟩ := (hA.image (fun z => max z.1.natAbs z.2.natAbs)).bddAbove
  refine ⟨2 * r + 1, (-(r : ℤ), -(r : ℤ)), ?_⟩
  intro z hz
  have hbound := hr (Set.mem_image_of_mem (fun z : Site => max z.1.natAbs z.2.natAbs) hz)
  have hx : z.1.natAbs ≤ r := le_trans (le_max_left _ _) hbound
  have hy : z.2.natAbs ≤ r := le_trans (le_max_right _ _) hbound
  have hx₁ := (Int.le_natAbs (a := z.1))
  have hx₂ := (Int.le_natAbs (a := -z.1))
  have hy₁ := (Int.le_natAbs (a := z.2))
  have hy₂ := (Int.le_natAbs (a := -z.2))
  simp only [Int.natAbs_neg] at hx₂ hy₂
  change 0 ≤ z.1 - -(r : ℤ) ∧ z.1 - -(r : ℤ) < ((2 * r + 1 : Nat) : ℤ) ∧
    0 ≤ z.2 - -(r : ℤ) ∧ z.2 - -(r : ℤ) < ((2 * r + 1 : Nat) : ℤ)
  omega

theorem finite_iff_exists_fits (A : Set Site) : A.Finite ↔ ∃ L, Fits A L :=
  ⟨exists_fits_of_finite, fun ⟨_, h⟩ => finite_of_fits h⟩

theorem fits_zero_iff (A : Set Site) : Fits A 0 ↔ A = ∅ := by
  constructor
  · rintro ⟨a, ha⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hin := ha hz
    simp only [Set.mem_ofPred_eq, InsideTranslated, Inside, shift] at hin
    omega
  · rintro rfl
    exact fits_empty 0

theorem diameter_le_nat_iff (A : Set Site) (L : Nat) :
    diameter A ≤ (L : ℕ∞) ↔ Fits A L := by
  classical
  by_cases h : ∃ K, Fits A K
  · simp only [diameter, dite_eq_left h, ENat.natCast_le_natCast]
    exact ⟨fun hKL => fits_mono hKL (Nat.find_spec h), Nat.find_min' h⟩
  · simp only [diameter, dite_eq_right h]
    constructor
    · intro hle
      exact False.elim ((not_le_of_gt (ENat.natCast_lt_top L)) hle)
    · intro hfit
      exact False.elim (h ⟨L, hfit⟩)

theorem diameter_eq_zero_iff (A : Set Site) : diameter A = 0 ↔ A = ∅ := by
  rw [← fits_zero_iff, ← diameter_le_nat_iff]
  exact ⟨fun h => h.le, fun h => le_antisymm h zero_le⟩

theorem diameter_ne_top_iff (A : Set Site) : diameter A ≠ ⊤ ↔ A.Finite := by
  classical
  rw [finite_iff_exists_fits]
  by_cases h : ∃ L, Fits A L
  · simp only [diameter, dite_eq_left h]
    exact ⟨fun _ => h, fun _ => ENat.natCast_ne_top _⟩
  · simp only [diameter, dite_eq_right h]
    exact ⟨fun hne => False.elim (hne rfl), fun he => False.elim (h he)⟩

theorem diameter_minimum {A : Set Site} (hA : A.Finite) :
    ∃ L : Nat, diameter A = (L : ℕ∞) ∧ Fits A L ∧ ∀ K, Fits A K → L ≤ K := by
  classical
  have hex := exists_fits_of_finite hA
  exact ⟨Nat.find hex, by simp only [diameter, dite_eq_left hex],
    Nat.find_spec hex, fun _ hfit => Nat.find_min' hex hfit⟩

theorem diameter_eq_nat_iff (A : Set Site) (L : Nat) :
    diameter A = (L : ℕ∞) ↔ Fits A L ∧ ∀ K, Fits A K → L ≤ K := by
  classical
  constructor
  · intro h
    refine ⟨(diameter_le_nat_iff A L).mp h.le, ?_⟩
    intro K hK
    have hle := (diameter_le_nat_iff A K).mpr hK
    rw [h] at hle
    exact ENat.natCast_le_natCast.mp hle
  · rintro ⟨hL, hmin⟩
    have hex : ∃ K, Fits A K := ⟨L, hL⟩
    have heq : Nat.find hex = L := le_antisymm (Nat.find_min' hex hL)
      (hmin _ (Nat.find_spec hex))
    simp only [diameter, dite_eq_left hex, heq]

/-- The diagonal endpoints prevent fitting a full square in any smaller translate. -/
theorem fits_square_iff (L K : Nat) : Fits {z : Site | Inside L z} K ↔ L ≤ K := by
  constructor
  · rintro ⟨a, ha⟩
    by_cases hL : L = 0
    · omega
    · have hzero : (0, 0) ∈ {z : Site | Inside L z} := by
        simp only [Set.mem_ofPred_eq, Inside]
        omega
      have hlast : ((L : ℤ) - 1, (L : ℤ) - 1) ∈ {z : Site | Inside L z} := by
        simp only [Set.mem_ofPred_eq, Inside]
        omega
      have h₀ := ha hzero
      have h₁ := ha hlast
      simp only [Set.mem_ofPred_eq, InsideTranslated, Inside, shift] at h₀ h₁
      omega
  · intro hLK
    refine ⟨(0, 0), fun z hz => ?_⟩
    simp only [Set.mem_ofPred_eq, Inside] at hz
    simp only [Set.mem_ofPred_eq, InsideTranslated, Inside, shift]
    omega

theorem diameter_square (L : Nat) : diameter {z : Site | Inside L z} = (L : ℕ∞) := by
  rw [diameter_eq_nat_iff]
  exact ⟨(fits_square_iff L L).mpr le_rfl,
    fun K hK => (fits_square_iff L K).mp hK⟩

theorem fits_difference_false_iff (f : Config) (L : Nat) :
    Fits (difference f false) L ↔ ∃ a, SupportedTranslated L a f := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun z hz => ?_⟩
    by_contra hf
    exact hz (ha hf)
  · rintro ⟨a, ha⟩
    refine ⟨a, fun z hz => ?_⟩
    by_contra hin
    exact hz (ha z hin)

theorem finitePerturbation_iff_exists_supported_translated (f : Config) :
    FinitePerturbation f false ↔ ∃ L a, SupportedTranslated L a f := by
  unfold FinitePerturbation
  rw [finite_iff_exists_fits]
  exact exists_congr (fun L => fits_difference_false_iff f L)

theorem original_side_sub_two (N : Nat) (hN : 2 ≤ N) : N - 2 + 2 = N := by omega

end MathResearchAnalysis.PerturbationGeometry


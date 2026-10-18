module

public import MathResearchAnalysis.PerturbationGeometry
public import MathResearchAnalysis.InfiniteGridComplement

set_option autoImplicit false

/-!
# Original perturbation distance and its genuine spatial/background symmetries

The distance to the two homogeneous backgrounds is the minimum of their
extended box diameters. A finite perturbation has a unique background on the
infinite lattice; no finite-distance hypothesis is hidden in the definition.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.PerturbationSymmetry

open PerturbationGeometry InfiniteGridTranslation

abbrev Site := InfiniteGridModel.Site
abbrev Config := InfiniteGridModel.Config

def shiftSet (a : Site) (A : Set Site) : Set Site := (shift a) ⁻¹' A

theorem fits_shift_iff (a : Site) (A : Set Site) (L : Nat) :
    Fits (shiftSet a A) L ↔ Fits A L := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(b.1 - a.1, b.2 - a.2), ?_⟩
    intro z hz
    have he : shift a (z.1 + a.1, z.2 + a.2) = z := by
      apply Prod.ext <;> dsimp [shift] <;> omega
    have hm : (z.1 + a.1, z.2 + a.2) ∈ shiftSet a A := by
      change shift a (z.1 + a.1, z.2 + a.2) ∈ A
      rw [he]
      exact hz
    have h := hb hm
    dsimp [InsideTranslated, InfiniteGridModel.Inside, shift] at h ⊢
    omega
  · rintro ⟨b, hb⟩
    refine ⟨(a.1 + b.1, a.2 + b.2), ?_⟩
    intro z hz
    have h := hb hz
    dsimp [InsideTranslated, InfiniteGridModel.Inside, shift] at h ⊢
    omega

theorem diameter_eq_of_fits_iff (A B : Set Site) (h : ∀ L, Fits A L ↔ Fits B L) :
    diameter A = diameter B := by
  apply le_antisymm
  · cases ht : diameter B using ENat.recTopCoe with
    | top => exact le_top
    | coe L =>
      exact (diameter_le_nat_iff A L).mpr ((h L).mpr
        ((diameter_le_nat_iff B L).mp (by rw [ht])))
  · cases ht : diameter A using ENat.recTopCoe with
    | top => exact le_top
    | coe L =>
      exact (diameter_le_nat_iff B L).mpr ((h L).mp
        ((diameter_le_nat_iff A L).mp (by rw [ht])))

theorem diameter_shift (a : Site) (A : Set Site) : diameter (shiftSet a A) = diameter A :=
  diameter_eq_of_fits_iff _ _ (fits_shift_iff a A)

theorem difference_translate (a : Site) (f : Config) (b : Bool) :
    difference (translate a f) b = shiftSet a (difference f b) := rfl

theorem difference_complement (f : Config) (b : Bool) :
    difference (InfiniteGridComplement.complementConfig f) (!b) = difference f b := by
  ext z
  cases h : f z <;> cases b <;> simp [difference, InfiniteGridComplement.complementConfig, h]

theorem finite_background_unique (f : Config) (h0 : FinitePerturbation f false)
    (h1 : FinitePerturbation f true) : False := by
  have hu : difference f false ∪ difference f true = Set.univ := by
    ext z
    cases h : f z <;> simp [difference, h]
  have hfin : (Set.univ : Set Site).Finite := by
    rw [← hu]
    exact h0.union h1
  exact Set.infinite_univ hfin

theorem opposite_diameter_top (f : Config) (b : Bool) (h : FinitePerturbation f b) :
    diameter (difference f (!b)) = ⊤ := by
  by_contra hne
  have hc := (diameter_ne_top_iff _).mp hne
  cases b with
  | false => exact finite_background_unique f h hc
  | true => exact finite_background_unique f hc h

def distance (f : Config) : ℕ∞ :=
  min (diameter (difference f false)) (diameter (difference f true))

theorem distance_of_finite_background (f : Config) (b : Bool) (h : FinitePerturbation f b) :
    distance f = diameter (difference f b) := by
  cases b with
  | false =>
    have ht := opposite_diameter_top f false h
    simpa only [distance, Bool.not_false, min_eq_left le_top] using
      congrArg (fun t => min (diameter (difference f false)) t) ht
  | true =>
    have ht := opposite_diameter_top f true h
    simpa only [distance, Bool.not_true, min_eq_right le_top] using
      congrArg (fun t => min t (diameter (difference f true))) ht

theorem distance_translate (a : Site) (f : Config) : distance (translate a f) = distance f := by
  simp only [distance, difference_translate, diameter_shift]

theorem distance_complement (f : Config) :
    distance (InfiniteGridComplement.complementConfig f) = distance f := by
  have h0 := difference_complement f true
  have h1 := difference_complement f false
  simp only [Bool.not_true, Bool.not_false] at h0 h1
  simp only [distance, h0, h1, min_comm]

theorem distance_ne_top_iff (f : Config) :
    distance f ≠ ⊤ ↔ FinitePerturbation f false ∨ FinitePerturbation f true := by
  constructor
  · intro h
    by_contra hn
    have h0 : diameter (difference f false) = ⊤ := by
      by_contra h0
      exact hn (Or.inl ((diameter_ne_top_iff _).mp h0))
    have h1 : diameter (difference f true) = ⊤ := by
      by_contra h1
      exact hn (Or.inr ((diameter_ne_top_iff _).mp h1))
    exact h (by simp only [distance, h0, h1, min_self])
  · rintro (h0 | h1)
    · rw [distance_of_finite_background f false h0]
      exact (diameter_ne_top_iff _).mpr h0
    · rw [distance_of_finite_background f true h1]
      exact (diameter_ne_top_iff _).mpr h1

theorem distance_eq_nat_iff (f : Config) (n : Nat) :
    distance f = (n : ℕ∞) ↔ ∃ b : Bool, FinitePerturbation f b ∧ diameter (difference f b) = (n : ℕ∞) := by
  constructor
  · intro h
    have hn : distance f ≠ ⊤ := by rw [h]; exact ENat.natCast_ne_top n
    rcases (distance_ne_top_iff f).mp hn with h0 | h1
    · exact ⟨false, h0, by rw [← distance_of_finite_background f false h0]; exact h⟩
    · exact ⟨true, h1, by rw [← distance_of_finite_background f true h1]; exact h⟩
  · rintro ⟨b, hb, hn⟩
    rw [distance_of_finite_background f b hb, hn]

def squareConfig (N : Nat) : Config := fun z => decide (InfiniteGridModel.Inside N z)

theorem difference_square (N : Nat) :
    difference (squareConfig N) false = {z | InfiniteGridModel.Inside N z} := by
  ext z
  simp [difference, squareConfig]

theorem distance_square (N : Nat) : distance (squareConfig N) = (N : ℕ∞) := by
  have hd : diameter (difference (squareConfig N) false) = (N : ℕ∞) := by
    rw [difference_square]
    exact diameter_square N
  have hf : FinitePerturbation (squareConfig N) false :=
    (diameter_ne_top_iff _).mp (by rw [hd]; exact ENat.natCast_ne_top N)
  rw [distance_of_finite_background _ false hf, hd]

end MathResearchAnalysis.PerturbationSymmetry

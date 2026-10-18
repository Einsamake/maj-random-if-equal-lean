module

public import MathResearchAnalysis.ClippedDiamondGeometry

set_option autoImplicit false

/-!
# Actual orthogonal sections of the clipped integer droplet

Every row and column is computed from the existing clippedDomain. The radius
formula, nonempty-section criterion and interval convexity below hold even at
L = 0. These are deterministic initial-domain facts; they do not assert a
Good contour invariant or preservation under a stochastic dynamics.
-/

@[expose] public section

namespace MathResearchAnalysis.ClippedOrthogonalSections

open ClippedDiamondGeometry

def sectionRadius (L : Nat) (a : Int) : Int :=
  min (L : Int) ((L : Int) + 1 - |a|)

theorem sectionRadius_nonneg (L : Nat) (a : Int) (ha : |a| ≤ (L : Int)) :
    0 ≤ sectionRadius L a := by
  exact le_min (Int.natCast_nonneg L) (by omega)

theorem sectionRadius_le_square (L : Nat) (a : Int) :
    sectionRadius L a ≤ (L : Int) := min_le_left _ _

theorem sectionRadius_le_diamond (L : Nat) (a : Int) :
    sectionRadius L a ≤ (L : Int) + 1 - |a| := min_le_right _ _

theorem sectionRadius_zero (L : Nat) : sectionRadius L 0 = (L : Int) := by
  unfold sectionRadius
  simp only [abs_zero, sub_zero]
  exact min_eq_left (by omega)

theorem sectionRadius_neg (L : Nat) (a : Int) :
    sectionRadius L (-a) = sectionRadius L a := by
  simp only [sectionRadius, abs_neg]

theorem mem_clipped_row_iff (L : Nat) (x y : Int) :
    (x, y) ∈ clippedDomain L ↔
      |y| ≤ (L : Int) ∧ |x| ≤ sectionRadius L y := by
  simp only [mem_clippedDomain, clipped, sectionRadius, le_min_iff]
  omega

theorem mem_clipped_column_iff (L : Nat) (x y : Int) :
    (x, y) ∈ clippedDomain L ↔
      |x| ≤ (L : Int) ∧ |y| ≤ sectionRadius L x := by
  simp only [mem_clippedDomain, clipped, sectionRadius, le_min_iff]
  omega

theorem mem_clipped_row_interval_iff (L : Nat) (x y : Int)
    (hy : |y| ≤ (L : Int)) :
    (x, y) ∈ clippedDomain L ↔
      -sectionRadius L y ≤ x ∧ x ≤ sectionRadius L y := by
  rw [mem_clipped_row_iff]
  simp only [hy, true_and, abs_le]

theorem mem_clipped_column_interval_iff (L : Nat) (x y : Int)
    (hx : |x| ≤ (L : Int)) :
    (x, y) ∈ clippedDomain L ↔
      -sectionRadius L x ≤ y ∧ y ≤ sectionRadius L x := by
  rw [mem_clipped_column_iff]
  simp only [hx, true_and, abs_le]

def horizontalSection (L : Nat) (y : Int) : Finset Int :=
  (Finset.Icc (-(L : Int)) (L : Int)).filter (fun x => (x, y) ∈ clippedDomain L)

def verticalSection (L : Nat) (x : Int) : Finset Int :=
  (Finset.Icc (-(L : Int)) (L : Int)).filter (fun y => (x, y) ∈ clippedDomain L)

theorem mem_horizontalSection (L : Nat) (x y : Int) :
    x ∈ horizontalSection L y ↔ (x, y) ∈ clippedDomain L := by
  simp only [horizontalSection, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have hx := ((mem_clippedDomain L (x, y)).mp h).1
    exact ⟨abs_le.mp hx, h⟩

theorem mem_verticalSection (L : Nat) (x y : Int) :
    y ∈ verticalSection L x ↔ (x, y) ∈ clippedDomain L := by
  simp only [verticalSection, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have hy := ((mem_clippedDomain L (x, y)).mp h).2.1
    exact ⟨abs_le.mp hy, h⟩

theorem horizontalSection_eq_Icc (L : Nat) (y : Int) (hy : |y| ≤ (L : Int)) :
    horizontalSection L y = Finset.Icc (-sectionRadius L y) (sectionRadius L y) := by
  ext x
  rw [mem_horizontalSection, Finset.mem_Icc]
  exact mem_clipped_row_interval_iff L x y hy

theorem verticalSection_eq_Icc (L : Nat) (x : Int) (hx : |x| ≤ (L : Int)) :
    verticalSection L x = Finset.Icc (-sectionRadius L x) (sectionRadius L x) := by
  ext y
  rw [mem_verticalSection, Finset.mem_Icc]
  exact mem_clipped_column_interval_iff L x y hx

theorem vertical_axis_mem_iff (L : Nat) (y : Int) :
    (0, y) ∈ clippedDomain L ↔ |y| ≤ (L : Int) := by
  simp only [mem_clippedDomain, clipped, abs_zero, zero_add]
  omega

theorem horizontal_axis_mem_iff (L : Nat) (x : Int) :
    (x, 0) ∈ clippedDomain L ↔ |x| ≤ (L : Int) := by
  simp only [mem_clippedDomain, clipped, abs_zero, add_zero]
  omega

theorem origin_mem (L : Nat) : (0, 0) ∈ clippedDomain L := by
  rw [vertical_axis_mem_iff]
  exact by simp

theorem horizontalSection_nonempty_iff (L : Nat) (y : Int) :
    (horizontalSection L y).Nonempty ↔ |y| ≤ (L : Int) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ((mem_clipped_row_iff L x y).mp ((mem_horizontalSection L x y).mp hx)).1
  · intro hy
    exact ⟨0, (mem_horizontalSection L 0 y).mpr ((vertical_axis_mem_iff L y).mpr hy)⟩

theorem verticalSection_nonempty_iff (L : Nat) (x : Int) :
    (verticalSection L x).Nonempty ↔ |x| ≤ (L : Int) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ((mem_clipped_column_iff L x y).mp ((mem_verticalSection L x y).mp hy)).1
  · intro hx
    exact ⟨0, (mem_verticalSection L x 0).mpr ((horizontal_axis_mem_iff L x).mpr hx)⟩

theorem horizontalSection_eq_empty_iff (L : Nat) (y : Int) :
    horizontalSection L y = ∅ ↔ ¬ |y| ≤ (L : Int) := by
  rw [← horizontalSection_nonempty_iff, Finset.not_nonempty_iff_eq_empty]

theorem verticalSection_eq_empty_iff (L : Nat) (x : Int) :
    verticalSection L x = ∅ ↔ ¬ |x| ≤ (L : Int) := by
  rw [← verticalSection_nonempty_iff, Finset.not_nonempty_iff_eq_empty]

theorem row_left_endpoint_mem (L : Nat) (y : Int) (hy : |y| ≤ (L : Int)) :
    (-sectionRadius L y, y) ∈ clippedDomain L := by
  rw [mem_clipped_row_iff]
  exact ⟨hy, by rw [abs_neg, abs_of_nonneg (sectionRadius_nonneg L y hy)]⟩

theorem row_right_endpoint_mem (L : Nat) (y : Int) (hy : |y| ≤ (L : Int)) :
    (sectionRadius L y, y) ∈ clippedDomain L := by
  rw [mem_clipped_row_iff]
  exact ⟨hy, by rw [abs_of_nonneg (sectionRadius_nonneg L y hy)]⟩

theorem column_bottom_endpoint_mem (L : Nat) (x : Int) (hx : |x| ≤ (L : Int)) :
    (x, -sectionRadius L x) ∈ clippedDomain L := by
  rw [mem_clipped_column_iff]
  exact ⟨hx, by rw [abs_neg, abs_of_nonneg (sectionRadius_nonneg L x hx)]⟩

theorem column_top_endpoint_mem (L : Nat) (x : Int) (hx : |x| ≤ (L : Int)) :
    (x, sectionRadius L x) ∈ clippedDomain L := by
  rw [mem_clipped_column_iff]
  exact ⟨hx, by rw [abs_of_nonneg (sectionRadius_nonneg L x hx)]⟩

theorem row_interval_convex (L : Nat) (a b x y : Int)
    (ha : (a, y) ∈ clippedDomain L) (hb : (b, y) ∈ clippedDomain L)
    (hax : a ≤ x) (hxb : x ≤ b) : (x, y) ∈ clippedDomain L := by
  have hA := (mem_clipped_row_iff L a y).mp ha
  have hB := (mem_clipped_row_iff L b y).mp hb
  have hAbounds := abs_le.mp hA.2
  have hBbounds := abs_le.mp hB.2
  exact (mem_clipped_row_iff L x y).mpr ⟨hA.1, abs_le.mpr ⟨by omega, by omega⟩⟩

theorem column_interval_convex (L : Nat) (x a b y : Int)
    (ha : (x, a) ∈ clippedDomain L) (hb : (x, b) ∈ clippedDomain L)
    (hay : a ≤ y) (hyb : y ≤ b) : (x, y) ∈ clippedDomain L := by
  have hA := (mem_clipped_column_iff L x a).mp ha
  have hB := (mem_clipped_column_iff L x b).mp hb
  have hAbounds := abs_le.mp hA.2
  have hBbounds := abs_le.mp hB.2
  exact (mem_clipped_column_iff L x y).mpr ⟨hA.1, abs_le.mpr ⟨by omega, by omega⟩⟩

theorem mem_of_abs_coordinates_le {L : Nat} {u v : Site}
    (hu : u ∈ clippedDomain L) (hx : |v.1| ≤ |u.1|) (hy : |v.2| ≤ |u.2|) :
    v ∈ clippedDomain L := by
  rw [mem_clippedDomain] at hu ⊢
  exact ⟨le_trans hx hu.1, le_trans hy hu.2.1,
    le_trans (add_le_add hx hy) hu.2.2⟩

theorem card_horizontalSection (L : Nat) (y : Int) (hy : |y| ≤ (L : Int)) :
    (horizontalSection L y).card = (2 * sectionRadius L y + 1).toNat := by
  rw [horizontalSection_eq_Icc L y hy, Int.card_Icc]
  congr 1
  omega

theorem card_verticalSection (L : Nat) (x : Int) (hx : |x| ≤ (L : Int)) :
    (verticalSection L x).card = (2 * sectionRadius L x + 1).toNat := by
  rw [verticalSection_eq_Icc L x hx, Int.card_Icc]
  congr 1
  omega

end MathResearchAnalysis.ClippedOrthogonalSections

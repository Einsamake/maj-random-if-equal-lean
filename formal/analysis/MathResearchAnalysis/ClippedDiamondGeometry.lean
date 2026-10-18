module

public import MathResearchAnalysis.GridMajorityPeeling
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic

set_option autoImplicit false

/-!
# Finite clipped-diamond blocks in the integer lattice

The domain is the actual integer square of radius `L`, clipped by the diamond
of radius `L+1`. A small northeast block based at a point of the inner band is
contained in that domain and contains at least `L^2 / 1600` sites. These are
deterministic geometry statements; no trajectory or stochastic estimate is
assumed or concluded.
-/

@[expose] public section

namespace MathResearchAnalysis.ClippedDiamondGeometry

abbrev Site := InfiniteGridModel.Site

def clipped (L : ℕ) (z : Site) : Prop :=
  |z.1| ≤ (L : ℤ) ∧ |z.2| ≤ (L : ℤ) ∧ |z.1| + |z.2| ≤ (L : ℤ) + 1

instance clippedDecidable (L : ℕ) (z : Site) : Decidable (clipped L z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def clippedDomain (L : ℕ) : Finset Site :=
  ((Finset.Icc (-(L : ℤ)) L) ×ˢ (Finset.Icc (-(L : ℤ)) L)).filter
    (fun z => |z.1| + |z.2| ≤ (L : ℤ) + 1)

theorem mem_clippedDomain (L : ℕ) (z : Site) :
    z ∈ clippedDomain L ↔ clipped L z := by
  simp only [clippedDomain, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, clipped, abs_le]
  tauto

/-- Integer version of a distance at most `0.9 L + 1` from the origin. -/
def boundaryBand (L : ℕ) (x : Site) : Prop :=
  10 * (|x.1| + |x.2|) ≤ 9 * (L : ℤ) + 10

def blockPoint (x : Site) {m : ℕ} (p : Fin m × Fin m) : Site :=
  (x.1 + ((p.1.val : ℤ) + 1), x.2 + ((p.2.val : ℤ) + 1))

theorem blockPoint_injective (x : Site) (m : ℕ) :
    Function.Injective (blockPoint x (m := m)) := by
  intro p q h
  apply Prod.ext <;> apply Fin.ext
  · have := congrArg Prod.fst h
    simp only [blockPoint] at this
    omega
  · have := congrArg Prod.snd h
    simp only [blockPoint] at this
    omega

def neBlock (L : ℕ) (x : Site) : Finset Site :=
  Finset.univ.image (blockPoint x (m := L / 20))

theorem mem_neBlock (L : ℕ) (x z : Site) :
    z ∈ neBlock L x ↔ ∃ p : Fin (L / 20) × Fin (L / 20), blockPoint x p = z := by
  simp [neBlock]

theorem neBlock_card (L : ℕ) (x : Site) :
    (neBlock L x).card = (L / 20) ^ 2 := by
  rw [neBlock, Finset.card_image_of_injective _ (blockPoint_injective x _)]
  simp [pow_two]

theorem blockPoint_mem_clippedDomain {L : ℕ} (hL : 40 ≤ L)
    {x : Site} (hx : boundaryBand L x) (p : Fin (L / 20) × Fin (L / 20)) :
    blockPoint x p ∈ clippedDomain L := by
  rw [mem_clippedDomain]
  have hm : 20 * (L / 20) ≤ L := Nat.mul_div_le L 20
  have hp : (p.1.val : ℤ) + 1 ≤ (L / 20 : ℕ) := by exact_mod_cast p.1.isLt
  have hq : (p.2.val : ℤ) + 1 ≤ (L / 20 : ℕ) := by exact_mod_cast p.2.isLt
  have hmZ : 20 * (L / 20 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hm
  have hLZ : 40 ≤ (L : ℤ) := by exact_mod_cast hL
  have hp0 : 0 ≤ (p.1.val : ℤ) + 1 := by omega
  have hq0 : 0 ≤ (p.2.val : ℤ) + 1 := by omega
  have hxp := abs_add_le x.1 ((p.1.val : ℤ) + 1)
  have hyq := abs_add_le x.2 ((p.2.val : ℤ) + 1)
  rw [abs_of_nonneg hp0] at hxp
  rw [abs_of_nonneg hq0] at hyq
  have hx0 := abs_nonneg x.1
  have hy0 := abs_nonneg x.2
  unfold clipped blockPoint
  dsimp
  unfold boundaryBand at hx
  constructor
  · omega
  constructor <;> omega

theorem neBlock_subset_clippedDomain {L : ℕ} (hL : 40 ≤ L)
    {x : Site} (hx : boundaryBand L x) : neBlock L x ⊆ clippedDomain L := by
  intro z hz
  obtain ⟨p, rfl⟩ := (mem_neBlock L x z).mp hz
  exact blockPoint_mem_clippedDomain hL hx p

theorem side_le_forty_mul_div_twenty {L : ℕ} (hL : 40 ≤ L) :
    L ≤ 40 * (L / 20) := by
  have hm := Nat.mod_lt L (by omega : 0 < 20)
  have hd := Nat.mod_add_div L 20
  omega

theorem real_sq_div_le_neBlock_card {L : ℕ} (hL : 40 ≤ L) (x : Site) :
    (L : ℝ) ^ 2 / 1600 ≤ ((neBlock L x).card : ℝ) := by
  rw [neBlock_card]
  have hbound : (L : ℝ) ≤ 40 * (L / 20 : ℕ) := by
    exact_mod_cast side_le_forty_mul_div_twenty hL
  have hnonneg : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hsq := mul_self_le_mul_self hnonneg hbound
  push_cast
  nlinarith


/-- Independent sign reflections, preserving the actual integer domain. -/
def reflect (horizontal vertical : Bool) (z : Site) : Site :=
  (if horizontal then -z.1 else z.1, if vertical then -z.2 else z.2)

theorem reflect_involutive (horizontal vertical : Bool) :
    Function.Involutive (reflect horizontal vertical) := by
  intro z
  cases horizontal <;> cases vertical <;> simp [reflect]

theorem reflect_injective (horizontal vertical : Bool) :
    Function.Injective (reflect horizontal vertical) :=
  (reflect_involutive horizontal vertical).injective

theorem clipped_reflect_iff (L : ℕ) (horizontal vertical : Bool) (z : Site) :
    clipped L (reflect horizontal vertical z) ↔ clipped L z := by
  cases horizontal <;> cases vertical <;> simp [reflect, clipped]

theorem boundaryBand_reflect_iff (L : ℕ) (horizontal vertical : Bool) (z : Site) :
    boundaryBand L (reflect horizontal vertical z) ↔ boundaryBand L z := by
  cases horizontal <;> cases vertical <;> simp [reflect, boundaryBand]

/-- A block with either sign in each coordinate, based at `x` itself. -/
def directedBlock (L : ℕ) (x : Site) (horizontal vertical : Bool) : Finset Site :=
  (neBlock L (reflect horizontal vertical x)).image (reflect horizontal vertical)

theorem mem_directedBlock (L : ℕ) (x z : Site) (horizontal vertical : Bool) :
    z ∈ directedBlock L x horizontal vertical ↔
      ∃ p : Fin (L / 20) × Fin (L / 20),
        z = (x.1 + (if horizontal then -((p.1.val : ℤ) + 1) else (p.1.val : ℤ) + 1),
          x.2 + (if vertical then -((p.2.val : ℤ) + 1) else (p.2.val : ℤ) + 1)) := by
  simp only [directedBlock, Finset.mem_image, mem_neBlock]
  constructor
  · rintro ⟨y, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, by cases horizontal <;> cases vertical <;> simp [reflect, blockPoint, add_comm]⟩
  · rintro ⟨p, rfl⟩
    refine ⟨blockPoint (reflect horizontal vertical x) p, ⟨p, rfl⟩, ?_⟩
    cases horizontal <;> cases vertical <;> simp [reflect, blockPoint, add_comm]

theorem directedBlock_card (L : ℕ) (x : Site) (horizontal vertical : Bool) :
    (directedBlock L x horizontal vertical).card = (L / 20) ^ 2 := by
  rw [directedBlock, Finset.card_image_of_injective _ (reflect_injective _ _),
    neBlock_card]

theorem directedBlock_subset_clippedDomain {L : ℕ} (hL : 40 ≤ L)
    {x : Site} (hx : boundaryBand L x) (horizontal vertical : Bool) :
    directedBlock L x horizontal vertical ⊆ clippedDomain L := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  rw [mem_clippedDomain, clipped_reflect_iff]
  rw [← mem_clippedDomain]
  exact neBlock_subset_clippedDomain hL
    ((boundaryBand_reflect_iff L horizontal vertical x).mpr hx) hy

theorem real_sq_div_le_directedBlock_card {L : ℕ} (hL : 40 ≤ L) (x : Site)
    (horizontal vertical : Bool) :
    (L : ℝ) ^ 2 / 1600 ≤ ((directedBlock L x horizontal vertical).card : ℝ) := by
  rw [directedBlock_card, ← neBlock_card L x]
  exact real_sq_div_le_neBlock_card hL x


/-- A unit step toward zero, taking the positive step when already zero. -/
def toward (a : ℤ) : ℤ := if 0 < a then a - 1 else a + 1

def horizontalNeighbor (z : Site) : Site := (toward z.1, z.2)
def verticalNeighbor (z : Site) : Site := (z.1, toward z.2)

private theorem clipped_toward_first {L : ℕ} (hL : 1 ≤ L) (a b : ℤ)
    (h : clipped L (a, b)) : clipped L (toward a, b) := by
  change |a| ≤ (L : ℤ) ∧ |b| ≤ (L : ℤ) ∧ |a| + |b| ≤ (L : ℤ) + 1 at h
  change |toward a| ≤ (L : ℤ) ∧ |b| ≤ (L : ℤ) ∧
    |toward a| + |b| ≤ (L : ℤ) + 1
  rcases h with ⟨ha, hb, hab⟩
  have hLZ : 1 ≤ (L : ℤ) := by exact_mod_cast hL
  by_cases hp : 0 < a
  · have hn : 0 ≤ a - 1 := by omega
    have ha0 : 0 ≤ a := by omega
    simp only [toward, ite_eq_left hp, abs_of_nonneg hn]
    rw [abs_of_nonneg ha0] at ha hab
    exact ⟨by omega, hb, by omega⟩
  · by_cases hz : a = 0
    · subst a
      change (1 : ℤ) ≤ (L : ℤ) ∧ |b| ≤ (L : ℤ) ∧ 1 + |b| ≤ (L : ℤ) + 1
      exact ⟨hLZ, hb, by omega⟩
    · have hn : a + 1 ≤ 0 := by omega
      have ha0 : a ≤ 0 := by omega
      simp only [toward, ite_eq_right hp, abs_of_nonpos hn]
      rw [abs_of_nonpos ha0] at ha hab
      exact ⟨by omega, hb, by omega⟩

theorem horizontalNeighbor_mem_clippedDomain {L : ℕ} (hL : 1 ≤ L)
    {z : Site} (hz : z ∈ clippedDomain L) :
    horizontalNeighbor z ∈ clippedDomain L := by
  rw [mem_clippedDomain] at hz ⊢
  exact clipped_toward_first hL z.1 z.2 hz

theorem verticalNeighbor_mem_clippedDomain {L : ℕ} (hL : 1 ≤ L)
    {z : Site} (hz : z ∈ clippedDomain L) :
    verticalNeighbor z ∈ clippedDomain L := by
  rw [mem_clippedDomain] at hz ⊢
  have hs : clipped L (z.2, z.1) := ⟨hz.2.1, hz.1, by simpa [add_comm] using hz.2.2⟩
  have ht := clipped_toward_first hL z.2 z.1 hs
  exact ⟨ht.2.1, ht.1, by simpa [verticalNeighbor, add_comm] using ht.2.2⟩

theorem horizontalNeighbor_mem_neighbors4 (z : Site) :
    horizontalNeighbor z ∈ GridMajorityPeeling.neighbors4 z := by
  rw [GridMajorityPeeling.mem_neighbors4]
  by_cases hp : 0 < z.1
  · exact Or.inr (Or.inr (Or.inr (by simp [horizontalNeighbor, toward, hp,
      InfiniteGridModel.west])))
  · exact Or.inr (Or.inl (by simp [horizontalNeighbor, toward, hp,
      InfiniteGridModel.east]))

theorem verticalNeighbor_mem_neighbors4 (z : Site) :
    verticalNeighbor z ∈ GridMajorityPeeling.neighbors4 z := by
  rw [GridMajorityPeeling.mem_neighbors4]
  by_cases hp : 0 < z.2
  · exact Or.inr (Or.inr (Or.inl (by simp [verticalNeighbor, toward, hp,
      InfiniteGridModel.south])))
  · exact Or.inl (by simp [verticalNeighbor, toward, hp, InfiniteGridModel.north])

theorem horizontalNeighbor_ne_verticalNeighbor (z : Site) :
    horizontalNeighbor z ≠ verticalNeighbor z := by
  intro h
  have he := congrArg Prod.fst h
  simp only [horizontalNeighbor, verticalNeighbor] at he
  unfold toward at he
  split_ifs at he <;> omega

theorem clippedDomain_degree_ge_two {L : ℕ} (hL : 1 ≤ L)
    {z : Site} (hz : z ∈ clippedDomain L) :
    2 ≤ GridMajorityPeeling.degree4 (clippedDomain L) z := by
  have hsub : {horizontalNeighbor z, verticalNeighbor z} ⊆
      GridMajorityPeeling.neighbors4 z ∩ clippedDomain L := by
    intro y hy
    have hy' : y = horizontalNeighbor z ∨ y = verticalNeighbor z := by simpa using hy
    rcases hy' with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨horizontalNeighbor_mem_neighbors4 z,
        horizontalNeighbor_mem_clippedDomain hL hz⟩
    · exact Finset.mem_inter.mpr ⟨verticalNeighbor_mem_neighbors4 z,
        verticalNeighbor_mem_clippedDomain hL hz⟩
  have hcard := Finset.card_le_card hsub
  simpa [GridMajorityPeeling.degree4, horizontalNeighbor_ne_verticalNeighbor z] using hcard

theorem clippedDomain_stable {L : ℕ} (hL : 1 ≤ L) :
    FiniteMajorityPeeling.Stable GridMajorityPeeling.neighbors4 (clippedDomain L) := by
  rw [FiniteMajorityPeeling.stable_iff]
  exact fun _ hz => clippedDomain_degree_ge_two hL hz

theorem cleanup_clippedDomain {L : ℕ} (hL : 1 ≤ L) :
    GridMajorityPeeling.cleanup (clippedDomain L) = clippedDomain L :=
  FiniteMajorityPeeling.core_eq_self _ (clippedDomain_stable hL)

end MathResearchAnalysis.ClippedDiamondGeometry

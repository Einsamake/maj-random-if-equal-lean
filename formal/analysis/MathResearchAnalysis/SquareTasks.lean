module

public import MathResearchAnalysis.TaskPaths

set_option autoImplicit false

/-!
# Actual finite square-grid task system

The square has side length `n + 2`, so its induced, nonperiodic four-neighbor
graph has no isolated sites. Outside sites are not vertices. Adjacency is
defined by ordinary natural-number coordinates, without wrap-around.

`tasks n c k` is the color updated in the `k`th positive layer (the first
positive layer is indexed by zero here). `c = true` starts with even coordinate
sum, in agreement with the concrete integer-grid color convention.
The core's `phase` denotes the color at its zero-initialization layer: its
positive layer `k + 1` therefore corresponds to `tasks n (!phase) k`.

This module supplies only deterministic geometry and max-plus task structure.
It does not construct clocks, a spin update, or a probability model.
-/

public section

namespace MathResearchAnalysis.SquareTasks

/-- Vertices of the nonperiodic square of side `n + 2`. -/
abbrev Vertex (n : ℕ) := Fin (n + 2) × Fin (n + 2)

/-- Exactly the four unit-coordinate moves whose endpoints stay in the square. -/
@[expose] def Adjacent {n : ℕ} (v u : Vertex n) : Prop :=
  (v.1.val + 1 = u.1.val ∧ v.2 = u.2) ∨
  (u.1.val + 1 = v.1.val ∧ v.2 = u.2) ∨
  (v.1 = u.1 ∧ v.2.val + 1 = u.2.val) ∨
  (v.1 = u.1 ∧ u.2.val + 1 = v.2.val)

instance {n : ℕ} (v u : Vertex n) : Decidable (Adjacent v u) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _)))

/-- Actual finite set of interior four-neighbors. -/
@[expose] def neighbors (n : ℕ) (v : Vertex n) : Finset (Vertex n) :=
  Finset.univ.filter (Adjacent v)

theorem mem_neighbors_iff (n : ℕ) (v u : Vertex n) :
    u ∈ neighbors n v ↔ Adjacent v u := by
  simp [neighbors]

/-- The finite adjacency is literally the restriction of the integer four-neighbor grid. -/
theorem adjacent_iff_integer_unit (n : ℕ) (v u : Vertex n) :
    Adjacent v u ↔
      (((u.1.val : ℤ) - (v.1.val : ℤ) = 1 ∧
        (u.2.val : ℤ) = (v.2.val : ℤ)) ∨
      ((u.1.val : ℤ) - (v.1.val : ℤ) = -1 ∧
        (u.2.val : ℤ) = (v.2.val : ℤ)) ∨
      ((u.1.val : ℤ) = (v.1.val : ℤ) ∧
        (u.2.val : ℤ) - (v.2.val : ℤ) = 1) ∨
      ((u.1.val : ℤ) = (v.1.val : ℤ) ∧
        (u.2.val : ℤ) - (v.2.val : ℤ) = -1)) := by
  simp only [Adjacent, Fin.ext_iff]
  omega

theorem adjacent_symmetric {n : ℕ} {v u : Vertex n} (h : Adjacent v u) :
    Adjacent u v := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl ⟨h.1, h.2.symm⟩)
  · exact Or.inl ⟨h.1, h.2.symm⟩
  · exact Or.inr (Or.inr (Or.inr ⟨h.1.symm, h.2⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨h.1.symm, h.2⟩))

theorem neighbors_symmetric (n : ℕ) (v u : Vertex n) :
    u ∈ neighbors n v ↔ v ∈ neighbors n u := by
  simp only [mem_neighbors_iff]
  exact ⟨adjacent_symmetric, adjacent_symmetric⟩

theorem not_adjacent_self (n : ℕ) (v : Vertex n) : ¬ Adjacent v v := by
  simp [Adjacent]

/-- Even coordinate sum has color `true`, matching the integer-grid convention. -/
@[expose] def colour {n : ℕ} (v : Vertex n) : Bool :=
  decide ((v.1.val + v.2.val) % 2 = 0)

theorem adjacent_sum_step {n : ℕ} {v u : Vertex n} (h : Adjacent v u) :
    v.1.val + v.2.val + 1 = u.1.val + u.2.val ∨
      u.1.val + u.2.val + 1 = v.1.val + v.2.val := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · left; rw [hy]; omega
  · right; rw [hy]; omega
  · left; rw [hx]; omega
  · right; rw [hx]; omega

theorem adjacent_parity {n : ℕ} {v u : Vertex n} (h : Adjacent v u) :
    (v.1.val + v.2.val) % 2 ≠ (u.1.val + u.2.val) % 2 := by
  rcases adjacent_sum_step h with hs | hs <;> omega

theorem adjacent_colour_flip {n : ℕ} {v u : Vertex n} (h : Adjacent v u) :
    colour u = !colour v := by
  have hp := adjacent_parity h
  by_cases hv : (v.1.val + v.2.val) % 2 = 0
  · have hu : (u.1.val + u.2.val) % 2 ≠ 0 := by omega
    simp [colour, hv, hu]
  · have hu : (u.1.val + u.2.val) % 2 = 0 := by omega
    simp [colour, hv, hu]

/-- Clipped candidates are only used to count neighbors; adjacency has no clipping. -/
@[expose] def east {n : ℕ} (v : Vertex n) : Vertex n :=
  (⟨min (v.1.val + 1) (n + 1), by omega⟩, v.2)

@[expose] def west {n : ℕ} (v : Vertex n) : Vertex n :=
  (⟨v.1.val - 1, by have := v.1.isLt; omega⟩, v.2)

@[expose] def north {n : ℕ} (v : Vertex n) : Vertex n :=
  (v.1, ⟨min (v.2.val + 1) (n + 1), by omega⟩)

@[expose] def south {n : ℕ} (v : Vertex n) : Vertex n :=
  (v.1, ⟨v.2.val - 1, by have := v.2.isLt; omega⟩)

theorem adjacent_mem_candidates {n : ℕ} {v u : Vertex n} (h : Adjacent v u) :
    u ∈ ({east v, west v, north v, south v} : Finset (Vertex n)) := by
  have hvx := v.1.isLt
  have hvy := v.2.isLt
  have hux := u.1.isLt
  have huy := u.2.isLt
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have he : u = east v := by
      apply Prod.ext
      · apply Fin.ext
        change u.1.val = min (v.1.val + 1) (n + 1)
        rw [min_eq_left (by omega)]
        omega
      · exact hy.symm
    simp [he]
  · have hw : u = west v := by
      apply Prod.ext
      · apply Fin.ext
        change u.1.val = v.1.val - 1
        omega
      · exact hy.symm
    simp [hw]
  · have hn : u = north v := by
      apply Prod.ext
      · exact hx.symm
      · apply Fin.ext
        change u.2.val = min (v.2.val + 1) (n + 1)
        rw [min_eq_left (by omega)]
        omega
    simp [hn]
  · have hs : u = south v := by
      apply Prod.ext
      · exact hx.symm
      · apply Fin.ext
        change u.2.val = v.2.val - 1
        omega
    simp [hs]

theorem neighbors_card_le_four (n : ℕ) (v : Vertex n) :
    (neighbors n v).card ≤ 4 := by
  calc
    (neighbors n v).card ≤ ({east v, west v, north v, south v} :
        Finset (Vertex n)).card := Finset.card_le_card (by
      intro u hu
      exact adjacent_mem_candidates ((mem_neighbors_iff n v u).mp hu))
    _ ≤ 4 := Finset.card_le_four

theorem neighbors_nonempty (n : ℕ) (v : Vertex n) : (neighbors n v).Nonempty := by
  by_cases h : v.1.val + 1 < n + 2
  · refine ⟨(⟨v.1.val + 1, h⟩, v.2), ?_⟩
    exact (mem_neighbors_iff n v _).mpr (Or.inl ⟨rfl, rfl⟩)
  · have hpos : 0 < v.1.val := by have := v.1.isLt; omega
    refine ⟨west v, ?_⟩
    apply (mem_neighbors_iff n v _).mpr
    exact Or.inr (Or.inl ⟨by change v.1.val - 1 + 1 = v.1.val; omega, rfl⟩)

theorem vertices_card (n : ℕ) : Fintype.card (Vertex n) = (n + 2) ^ 2 := by
  simp [Vertex, pow_two]

/-- Every layer has the opposite checkerboard color to the preceding layer. -/
@[expose] def tasks (n : ℕ) (c : Bool) (k : ℕ) : Finset (Vertex n) :=
  Finset.univ.filter (fun v => (v.1.val + v.2.val + k) % 2 = if c then 0 else 1)

theorem mem_tasks_iff (n : ℕ) (c : Bool) (k : ℕ) (v : Vertex n) :
    v ∈ tasks n c k ↔ (v.1.val + v.2.val + k) % 2 = if c then 0 else 1 := by
  simp [tasks]

theorem mem_tasks_colour (n : ℕ) (c : Bool) (k : ℕ) (v : Vertex n) :
    v ∈ tasks n c k ↔ colour v = (if k % 2 = 0 then c else !c) := by
  rw [mem_tasks_iff]
  cases c <;> by_cases hk : k % 2 = 0 <;> by_cases hv :
    (v.1.val + v.2.val) % 2 = 0 <;> simp [colour, hk, hv] <;> omega

/-- Explicit alignment with a zero-initialized alternating schedule's layer `k + 1`. -/
theorem mem_tasks_positive_layer (n : ℕ) (phase : Bool) (k : ℕ) (v : Vertex n) :
    v ∈ tasks n (!phase) k ↔
      colour v = (if (k + 1) % 2 = 0 then phase else !phase) := by
  rw [mem_tasks_colour]
  by_cases hk : k % 2 = 0
  · have hk' : (k + 1) % 2 ≠ 0 := by omega
    simp [hk, hk']
  · have hk' : (k + 1) % 2 = 0 := by omega
    simp [hk, hk']

theorem tasks_nonempty (n : ℕ) (c : Bool) (k : ℕ) : (tasks n c k).Nonempty := by
  have hzero : (0 : ℕ) < n + 2 := by omega
  have hone : (1 : ℕ) < n + 2 := by omega
  by_cases hk : k % 2 = if c then 0 else 1
  · refine ⟨(⟨0, hzero⟩, ⟨0, hzero⟩), ?_⟩
    simpa only [mem_tasks_iff, Nat.zero_add] using hk
  · refine ⟨(⟨1, hone⟩, ⟨0, hzero⟩), ?_⟩
    rw [mem_tasks_iff]
    cases c <;> simp_all <;> omega

theorem tasks_card_le (n : ℕ) (c : Bool) (k : ℕ) :
    (tasks n c k).card ≤ (n + 2) ^ 2 := by
  calc
    (tasks n c k).card ≤ (Finset.univ : Finset (Vertex n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = (n + 2) ^ 2 := by rw [Finset.card_univ, vertices_card]

theorem successive_tasks_disjoint (n : ℕ) (c : Bool) (k : ℕ) :
    Disjoint (tasks n c k) (tasks n c (k + 1)) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_tasks_iff] at hv hv'
  cases c <;> simp at hv hv' <;> omega

theorem successive_tasks_cover (n : ℕ) (c : Bool) (k : ℕ) :
    tasks n c k ∪ tasks n c (k + 1) = Finset.univ := by
  ext v
  simp only [Finset.mem_union, mem_tasks_iff, Finset.mem_univ]
  cases c <;> simp <;> omega

/-- This actual square supplies a nonempty predecessor set at every vertex. -/
@[expose] def system (n : ℕ) : TaskPaths.System (Vertex n) where
  predecessors := fun _ v => neighbors n v
  nonempty := fun _ v => neighbors_nonempty n v

theorem predecessor_degree (n : ℕ) (k : ℕ) (v : Vertex n) :
    ((system n).predecessors k v).card ≤ 4 := neighbors_card_le_four n v

theorem predecessor_closure (n : ℕ) (c : Bool) (k : ℕ) (v : Vertex n)
    (hv : v ∈ tasks n c (k + 1)) (u : Vertex n)
    (hu : u ∈ (system n).predecessors k v) : u ∈ tasks n c k := by
  rw [mem_tasks_iff] at hv ⊢
  have hadj : Adjacent v u := (mem_neighbors_iff n v u).mp hu
  rcases adjacent_sum_step hadj with hs | hs
  all_goals cases c <;> simp at hv ⊢ <;> omega

theorem successor_coverage (n : ℕ) (c : Bool) (k : ℕ) (u : Vertex n)
    (hu : u ∈ tasks n c k) :
    ∃ v ∈ tasks n c (k + 1), u ∈ (system n).predecessors k v := by
  obtain ⟨v, hv⟩ := neighbors_nonempty n u
  have hadj : Adjacent v u := adjacent_symmetric ((mem_neighbors_iff n u v).mp hv)
  refine ⟨v, ?_, (mem_neighbors_iff n v u).mpr hadj⟩
  rw [mem_tasks_iff] at hu ⊢
  rcases adjacent_sum_step hadj with hs | hs
  all_goals cases c <;> simp at hu ⊢ <;> omega

theorem terminalPaths_inTaskLayers (n : ℕ) (c : Bool) (k : ℕ)
    {p : List (Vertex n)} (hp : p ∈ (system n).terminalPaths (tasks n c k) k) :
    TaskPaths.System.InTaskLayers (tasks n c) p :=
  (system n).terminalPaths_inTaskLayers (tasks n c) (predecessor_closure n c) k hp

theorem terminalPaths_card_le (n : ℕ) (c : Bool) (k : ℕ) :
    ((system n).terminalPaths (tasks n c k) k).card ≤ (n + 2) ^ 2 * 4 ^ k := by
  exact ((system n).terminalPaths_card_le (tasks n c k) 4 (predecessor_degree n) k).trans
    (Nat.mul_le_mul_right _ (tasks_card_le n c k))

theorem prefixMaximum_eq_last (n : ℕ) (c : Bool) (delay : ℕ → Vertex n → ℝ)
    (nonnegative : ∀ k v, 0 ≤ delay k v) (k : ℕ) :
    (system n).prefixMaximum (tasks n c) (tasks_nonempty n c) delay k =
      (system n).terminalMaximum (tasks n c k) (tasks_nonempty n c k) delay k :=
  (system n).prefixMaximum_eq_last (tasks n c) (tasks_nonempty n c)
    delay nonnegative (successor_coverage n c) k

end MathResearchAnalysis.SquareTasks

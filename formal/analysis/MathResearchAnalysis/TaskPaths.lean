module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

set_option autoImplicit false

/-!
# Real max-plus task paths

A level `k` represents `k + 1` positive task layers. Predecessors may vary
with the level. The path list is stored newest first, and may revisit a
vertex. All maxima are actual nonempty finite maxima of real numbers.

The path expansion and degree bound are conclusions proved from the recursive
definitions. No Poisson clocks, stopping times or concrete square grid are
constructed here. Delays may be arbitrary reals for the expansion; their
nonnegativity is only needed to compare different layers.
-/

public section

namespace MathResearchAnalysis.TaskPaths

open scoped BigOperators

universe u

structure System (V : Type u) [DecidableEq V] where
  predecessors : ℕ → V → Finset V
  nonempty : ∀ k v, (predecessors k v).Nonempty

namespace System

variable {V : Type u} [DecidableEq V] (M : System V)

/-- All actual legal paths ending at `v`, stored in reverse layer order. -/
@[expose] def paths : ℕ → V → Finset (List V)
  | 0, v => {[v]}
  | k + 1, v => (M.predecessors k v).biUnion
      (fun u => (paths k u).image (List.cons v))

/-- Logical path predicate independent of the finite enumeration. -/
@[expose] def Legal : ℕ → V → List V → Prop
  | 0, v, p => p = [v]
  | k + 1, v, p => ∃ u ∈ M.predecessors k v,
      ∃ q, Legal k u q ∧ p = v :: q

/-- Every vertex of a reversed path belongs to its chronological task layer. -/
@[expose] def InTaskLayers (tasks : ℕ → Finset V) : List V → Prop
  | [] => True
  | v :: q => v ∈ tasks q.length ∧ InTaskLayers tasks q

theorem mem_paths_iff_legal (k : ℕ) (v : V) (p : List V) :
    p ∈ M.paths k v ↔ M.Legal k v p := by
  induction k generalizing v p with
  | zero => simp [paths, Legal]
  | succ k ih =>
      simp only [paths, Finset.mem_biUnion, Finset.mem_image, Legal]
      constructor
      · rintro ⟨u, hu, q, hq, hp⟩
        exact ⟨u, hu, q, (ih u q).mp hq, hp.symm⟩
      · rintro ⟨u, hu, q, hq, hp⟩
        exact ⟨u, hu, q, (ih u q).mpr hq, hp.symm⟩

theorem paths_nonempty (k : ℕ) (v : V) : (M.paths k v).Nonempty := by
  induction k generalizing v with
  | zero => exact Finset.singleton_nonempty _
  | succ k ih =>
      obtain ⟨u, hu⟩ := M.nonempty k v
      obtain ⟨q, hq⟩ := ih u
      refine ⟨v :: q, Finset.mem_biUnion.mpr ⟨u, hu, ?_⟩⟩
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

theorem path_length (k : ℕ) (v : V) {p : List V}
    (hp : p ∈ M.paths k v) : p.length = k + 1 := by
  induction k generalizing v p with
  | zero =>
      have hp' : p = [v] := by simpa [paths] using hp
      subst p
      rfl
  | succ k ih =>
      rcases Finset.mem_biUnion.mp hp with ⟨u, hu, h⟩
      rcases Finset.mem_image.mp h with ⟨q, hq, rfl⟩
      simp only [List.length_cons, ih u hq]

/-- Predecessor closure makes the enumerated ancestors actual layer tasks. -/
theorem path_inTaskLayers (tasks : ℕ → Finset V)
    (closure : ∀ j v, v ∈ tasks (j + 1) →
      ∀ u ∈ M.predecessors j v, u ∈ tasks j)
    (k : ℕ) (v : V) (hv : v ∈ tasks k) {p : List V}
    (hp : p ∈ M.paths k v) : InTaskLayers tasks p := by
  induction k generalizing v p with
  | zero =>
      have hp' : p = [v] := by simpa [paths] using hp
      subst p
      exact ⟨hv, trivial⟩
  | succ k ih =>
      rcases Finset.mem_biUnion.mp hp with ⟨u, hu, h⟩
      rcases Finset.mem_image.mp h with ⟨q, hq, rfl⟩
      change v ∈ tasks q.length ∧ InTaskLayers tasks q
      rw [M.path_length k u hq]
      exact ⟨hv, ih u (closure k v hv u hu) hq⟩

/-- Indexing by suffix length gives the original task layer, even on revisits. -/
@[expose] def weight (delay : ℕ → V → ℝ) : List V → ℝ
  | [] => 0
  | v :: q => delay q.length v + weight delay q

omit [DecidableEq V] in
/-- The reversed representation is exactly the ordinary forward indexed sum. -/
theorem weight_eq_forward_sum (delay : ℕ → V → ℝ) (p : List V) :
    weight delay p = (p.reverse.mapIdx delay).sum := by
  induction p with
  | nil => simp [weight]
  | cons v q ih =>
      simp only [weight, List.reverse_cons, List.mapIdx_concat,
        List.sum_append, List.sum_cons, List.sum_nil, List.length_reverse, add_zero]
      rw [ih, add_comm]

/-- The actual layered max-plus recurrence, with first layer delay `delay 0`. -/
@[expose] noncomputable def completion (delay : ℕ → V → ℝ) : ℕ → V → ℝ
  | 0, v => delay 0 v
  | k + 1, v => delay (k + 1) v +
      (M.predecessors k v).sup' (M.nonempty k v) (completion delay k)

theorem path_weight_le_completion (delay : ℕ → V → ℝ) (k : ℕ) (v : V)
    {p : List V} (hp : p ∈ M.paths k v) :
    weight delay p ≤ M.completion delay k v := by
  induction k generalizing v p with
  | zero =>
      have hp' : p = [v] := by simpa [paths] using hp
      subst p
      simp [weight, completion]
  | succ k ih =>
      rcases Finset.mem_biUnion.mp hp with ⟨u, hu, h⟩
      rcases Finset.mem_image.mp h with ⟨q, hq, rfl⟩
      rw [weight, M.path_length k u hq]
      change delay (k + 1) v + weight delay q ≤ delay (k + 1) v + _
      exact add_le_add le_rfl ((ih u hq).trans
        (Finset.le_sup' (M.completion delay k) hu))

/-- Every completion value is attained by an enumerated, predetermined path. -/
theorem completion_attained (delay : ℕ → V → ℝ) (k : ℕ) (v : V) :
    ∃ p ∈ M.paths k v, M.completion delay k v = weight delay p := by
  induction k generalizing v with
  | zero => exact ⟨[v], by simp [paths], by simp [completion, weight]⟩
  | succ k ih =>
      obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_sup'
        (M.nonempty k v) (M.completion delay k)
      obtain ⟨q, hq, heq'⟩ := ih u
      refine ⟨v :: q, Finset.mem_biUnion.mpr ⟨u, hu,
        Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩, ?_⟩
      simp only [completion, weight, M.path_length k u hq, heq, heq']

/-- The max-plus/path-maximum identity is proved, not supplied as a hypothesis. -/
theorem completion_eq_path_max (delay : ℕ → V → ℝ) (k : ℕ) (v : V) :
    M.completion delay k v =
      (M.paths k v).sup' (M.paths_nonempty k v) (weight delay) := by
  apply le_antisymm
  · obtain ⟨p, hp, heq⟩ := M.completion_attained delay k v
    rw [heq]
    exact Finset.le_sup' (weight delay) hp
  · exact Finset.sup'_le _ _ (fun p hp => M.path_weight_le_completion delay k v hp)

/-- Counting the actual enumeration; duplicate generated paths only help. -/
theorem paths_card_le (d : ℕ)
    (degree : ∀ k v, (M.predecessors k v).card ≤ d) (k : ℕ) (v : V) :
    (M.paths k v).card ≤ d ^ k := by
  induction k generalizing v with
  | zero => simp [paths]
  | succ k ih =>
      calc
        (M.paths (k + 1) v).card ≤
            (M.predecessors k v).card * d ^ k := by
          apply Finset.card_biUnion_le_card_mul
          intro u hu
          exact (Finset.card_image_le).trans (ih u)
        _ ≤ d * d ^ k := Nat.mul_le_mul_right _ (degree k v)
        _ = d ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Restrict the last layer to a specified finite set of actual tasks. -/
@[expose] def terminalPaths (terminals : Finset V) (k : ℕ) : Finset (List V) :=
  terminals.biUnion (M.paths k)

theorem mem_terminalPaths_iff (terminals : Finset V) (k : ℕ) (p : List V) :
    p ∈ M.terminalPaths terminals k ↔ ∃ v ∈ terminals, M.Legal k v p := by
  simp [terminalPaths, M.mem_paths_iff_legal]

theorem terminalPaths_nonempty (terminals : Finset V) (ht : terminals.Nonempty)
    (k : ℕ) : (M.terminalPaths terminals k).Nonempty := by
  obtain ⟨v, hv⟩ := ht
  obtain ⟨p, hp⟩ := M.paths_nonempty k v
  exact ⟨p, Finset.mem_biUnion.mpr ⟨v, hv, hp⟩⟩

@[expose] noncomputable def terminalMaximum (terminals : Finset V) (ht : terminals.Nonempty)
    (delay : ℕ → V → ℝ) (k : ℕ) : ℝ :=
  terminals.sup' ht (M.completion delay k)

theorem terminalMaximum_eq_path_max (terminals : Finset V) (ht : terminals.Nonempty)
    (delay : ℕ → V → ℝ) (k : ℕ) :
    M.terminalMaximum terminals ht delay k =
      (M.terminalPaths terminals k).sup' (M.terminalPaths_nonempty terminals ht k)
        (weight delay) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro v hv
    obtain ⟨p, hp, heq⟩ := M.completion_attained delay k v
    rw [heq]
    exact Finset.le_sup' (weight delay) (Finset.mem_biUnion.mpr ⟨v, hv, hp⟩)
  · apply Finset.sup'_le
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨v, hv, hpv⟩
    exact (M.path_weight_le_completion delay k v hpv).trans
      (Finset.le_sup' (M.completion delay k) hv)

theorem terminalMaximum_exceeds_iff (terminals : Finset V) (ht : terminals.Nonempty)
    (delay : ℕ → V → ℝ) (k : ℕ) (t : ℝ) :
    t < M.terminalMaximum terminals ht delay k ↔
      ∃ p ∈ M.terminalPaths terminals k, t < weight delay p := by
  rw [M.terminalMaximum_eq_path_max]
  exact Finset.lt_sup'_iff (M.terminalPaths_nonempty terminals ht k)

theorem terminalPaths_card_le (terminals : Finset V) (d : ℕ)
    (degree : ∀ k v, (M.predecessors k v).card ≤ d) (k : ℕ) :
    (M.terminalPaths terminals k).card ≤ terminals.card * d ^ k := by
  apply Finset.card_biUnion_le_card_mul
  intro v hv
  exact M.paths_card_le d degree k v

/-- Every path to a selected final task stays inside the selected task layers. -/
theorem terminalPaths_inTaskLayers (tasks : ℕ → Finset V)
    (closure : ∀ j v, v ∈ tasks (j + 1) →
      ∀ u ∈ M.predecessors j v, u ∈ tasks j)
    (k : ℕ) {p : List V} (hp : p ∈ M.terminalPaths (tasks k) k) :
    InTaskLayers tasks p := by
  rcases Finset.mem_biUnion.mp hp with ⟨v, hv, hpv⟩
  exact M.path_inTaskLayers tasks closure k v hv hpv

/-- Each predecessor finishes no later if delays are nonnegative. -/
theorem predecessor_completion_le (delay : ℕ → V → ℝ)
    (nonnegative : ∀ k v, 0 ≤ delay k v) (k : ℕ) {u v : V}
    (hu : u ∈ M.predecessors k v) :
    M.completion delay k u ≤ M.completion delay (k + 1) v := by
  exact (Finset.le_sup' (M.completion delay k) hu).trans
    (le_add_of_nonneg_left (nonnegative (k + 1) v))

/-- Successor coverage is precisely what makes successive task maxima monotone.
    For a bipartite undirected graph it follows from the absence of isolated sites. -/
theorem terminalMaximum_monotone (tasks : ℕ → Finset V)
    (ht : ∀ k, (tasks k).Nonempty) (delay : ℕ → V → ℝ)
    (nonnegative : ∀ k v, 0 ≤ delay k v)
    (successors : ∀ k u, u ∈ tasks k →
      ∃ v ∈ tasks (k + 1), u ∈ M.predecessors k v) :
    Monotone (fun k => M.terminalMaximum (tasks k) (ht k) delay k) := by
  apply monotone_nat_of_le_succ
  intro k
  apply Finset.sup'_le
  intro u hu
  obtain ⟨v, hv, huv⟩ := successors k u hu
  exact (M.predecessor_completion_le delay nonnegative k huv).trans
    (Finset.le_sup' (M.completion delay (k + 1)) hv)

/-- Maximum over all completed task layers up to `k`, including the last layer. -/
@[expose] noncomputable def prefixMaximum (tasks : ℕ → Finset V)
    (ht : ∀ k, (tasks k).Nonempty) (delay : ℕ → V → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).sup' (by simp)
    (fun j => M.terminalMaximum (tasks j) (ht j) delay j)

theorem prefixMaximum_eq_last (tasks : ℕ → Finset V)
    (ht : ∀ k, (tasks k).Nonempty) (delay : ℕ → V → ℝ)
    (nonnegative : ∀ k v, 0 ≤ delay k v)
    (successors : ∀ k u, u ∈ tasks k →
      ∃ v ∈ tasks (k + 1), u ∈ M.predecessors k v) (k : ℕ) :
    M.prefixMaximum tasks ht delay k = M.terminalMaximum (tasks k) (ht k) delay k := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    exact M.terminalMaximum_monotone tasks ht delay nonnegative successors
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  · exact Finset.le_sup'
      (fun j => M.terminalMaximum (tasks j) (ht j) delay j)
      (Finset.mem_range.mpr (Nat.lt_succ_self k))

section FiniteVertices

variable [Fintype V] [Nonempty V]

/-- All legal paths to the last layer, from every terminal vertex. -/
@[expose] def allPaths (k : ℕ) : Finset (List V) := Finset.univ.biUnion (M.paths k)

omit [Nonempty V] in
theorem mem_allPaths_iff (k : ℕ) (p : List V) :
    p ∈ M.allPaths k ↔ ∃ v, M.Legal k v p := by
  simp [allPaths, M.mem_paths_iff_legal]

theorem allPaths_nonempty (k : ℕ) : (M.allPaths k).Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨p, hp⟩ := M.paths_nonempty k v
  exact ⟨p, Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hp⟩⟩

@[expose] noncomputable def layerMaximum (delay : ℕ → V → ℝ) (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (M.completion delay k)

theorem layerMaximum_eq_path_max (delay : ℕ → V → ℝ) (k : ℕ) :
    M.layerMaximum delay k =
      (M.allPaths k).sup' (M.allPaths_nonempty k) (weight delay) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro v hv
    obtain ⟨p, hp, heq⟩ := M.completion_attained delay k v
    rw [heq]
    exact Finset.le_sup' (weight delay)
      (Finset.mem_biUnion.mpr ⟨v, hv, hp⟩)
  · apply Finset.sup'_le
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨v, hv, hpv⟩
    exact (M.path_weight_le_completion delay k v hpv).trans
      (Finset.le_sup' (M.completion delay k) hv)

theorem layerMaximum_exceeds_iff (delay : ℕ → V → ℝ) (k : ℕ) (t : ℝ) :
    t < M.layerMaximum delay k ↔
      ∃ p ∈ M.allPaths k, t < weight delay p := by
  rw [M.layerMaximum_eq_path_max]
  exact Finset.lt_sup'_iff (M.allPaths_nonempty k)

omit [Nonempty V] in
theorem allPaths_card_le (d : ℕ)
    (degree : ∀ k v, (M.predecessors k v).card ≤ d) (k : ℕ) :
    (M.allPaths k).card ≤ Fintype.card V * d ^ k := by
  calc
    (M.allPaths k).card ≤ Finset.univ.card * d ^ k := by
      apply Finset.card_biUnion_le_card_mul
      intro v hv
      exact M.paths_card_le d degree k v
    _ = Fintype.card V * d ^ k := by rw [Finset.card_univ]

end FiniteVertices

end System
end MathResearchAnalysis.TaskPaths

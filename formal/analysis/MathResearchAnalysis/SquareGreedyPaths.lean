module

public import MathResearchAnalysis.GreedyClockChain
public import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false

/-!
# Finite square paths and actual greedy-clock union bounds

A path contains `r` vertices. Consecutive vertices are equal or ordinary
four-neighbors inside the nonperiodic square. Five directional choices encode
every such path; a direction crossing the boundary stays at the same vertex.
The actual finite family is an image of the finite code space, so repeated
codes can only decrease its cardinality. The clock union bound uses the
proved single-path lower tail and does not require independence between paths.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators Matrix

namespace MathResearchAnalysis.SquareGreedyPaths

abbrev Vertex (n : Nat) := SquareTasks.Vertex n

def Step {n : Nat} (v u : Vertex n) : Prop := v = u ∨ SquareTasks.Adjacent v u

instance {n : Nat} (v u : Vertex n) : Decidable (Step v u) :=
  inferInstanceAs (Decidable (v = u ∨ SquareTasks.Adjacent v u))

def move {n : Nat} (d : Fin 5) (v : Vertex n) : Vertex n :=
  ![v, SquareTasks.east v, SquareTasks.west v, SquareTasks.north v, SquareTasks.south v] d

theorem move_step {n : Nat} (d : Fin 5) (v : Vertex n) : Step v (move d v) := by
  have hx := v.1.isLt
  have hy := v.2.isLt
  fin_cases d <;>
    simp [move, Step, SquareTasks.Adjacent, SquareTasks.east, SquareTasks.west,
      SquareTasks.north, SquareTasks.south, Prod.ext_iff, Fin.ext_iff] <;> omega

theorem step_exists_move {n : Nat} {v u : Vertex n} (h : Step v u) :
    ∃ d : Fin 5, move d v = u := by
  rcases h with h | h
  · exact ⟨0, by simp [move, h]⟩
  · have hc := SquareTasks.adjacent_mem_candidates h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with h | h | h | h
    · exact ⟨1, by simp [move, h]⟩
    · exact ⟨2, by simp [move, h]⟩
    · exact ⟨3, by simp [move, h]⟩
    · exact ⟨4, by simp [move, h]⟩

def walk {n : Nat} (start : Vertex n) (directions : Nat → Fin 5) : Nat → Vertex n
  | 0 => start
  | k + 1 => move (directions k) (walk start directions k)

def directions (r : Nat) (d : Fin (r - 1) → Fin 5) (i : Nat) : Fin 5 :=
  if hi : i < r - 1 then d ⟨i, hi⟩ else 0

def codePath (n r : Nat) (code : Vertex n × (Fin (r - 1) → Fin 5)) : Fin r → Vertex n :=
  fun i => walk code.1 (directions r code.2) i.val

def Legal (n r : Nat) (p : Fin r → Vertex n) : Prop :=
  ∀ i : Nat, ∀ hi : i + 1 < r, Step (p ⟨i, by omega⟩) (p ⟨i + 1, hi⟩)

theorem codePath_legal (n r : Nat) (code : Vertex n × (Fin (r - 1) → Fin 5)) :
    Legal n r (codePath n r code) := by
  intro i hi
  exact move_step (directions r code.2 i) (walk code.1 (directions r code.2) i)

def family (n r : Nat) : Finset (Fin r → Vertex n) :=
  Finset.univ.image (codePath n r)

theorem mem_family_legal (n r : Nat) {p : Fin r → Vertex n} (hp : p ∈ family n r) :
    Legal n r p := by
  rcases Finset.mem_image.mp hp with ⟨code, _, rfl⟩
  exact codePath_legal n r code

theorem legal_mem_family (n r : Nat) (hr : 0 < r) (p : Fin r → Vertex n)
    (hp : Legal n r p) : p ∈ family n r := by
  classical
  let d : Fin (r - 1) → Fin 5 := fun i =>
    Classical.choose (step_exists_move (hp i.val (by have := i.isLt; omega)))
  let code : Vertex n × (Fin (r - 1) → Fin 5) := (p ⟨0, hr⟩, d)
  have hwalk : ∀ i : Nat, ∀ hi : i < r,
      walk code.1 (directions r code.2) i = p ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero => intro hi; rfl
    | succ i ih =>
      intro hi
      have hiprev : i < r := by omega
      have hid : i < r - 1 := by omega
      rw [walk, ih hiprev]
      simp only [code, directions, dite_eq_left hid]
      exact Classical.choose_spec (step_exists_move (hp i (by omega)))
  apply Finset.mem_image.mpr
  refine ⟨code, Finset.mem_univ _, ?_⟩
  funext i
  exact hwalk i.val i.isLt

theorem mem_family_iff_legal (n r : Nat) (hr : 0 < r) (p : Fin r → Vertex n) :
    p ∈ family n r ↔ Legal n r p :=
  ⟨mem_family_legal n r, legal_mem_family n r hr p⟩

theorem family_card_le (n r : Nat) :
    (family n r).card ≤ (n + 2) ^ 2 * 5 ^ (r - 1) := by
  calc
    (family n r).card ≤ (Finset.univ :
      Finset (Vertex n × (Fin (r - 1) → Fin 5))).card := Finset.card_image_le
    _ = (n + 2) ^ 2 * 5 ^ (r - 1) := by
      simp [pow_two]

def origin (n : Nat) : Vertex n := (⟨0, by omega⟩, ⟨0, by omega⟩)

def extend (n r : Nat) (p : Fin r → Vertex n) (i : Nat) : Vertex n :=
  if hi : i < r then p ⟨i, hi⟩ else origin n

theorem extend_eq (n r : Nat) (p : Fin r → Vertex n) (i : Nat) (hi : i < r) :
    extend n r p i = p ⟨i, hi⟩ := by simp only [extend, dite_eq_left hi]

theorem extend_legal (n r : Nat) (p : Fin r → Vertex n) (hp : Legal n r p)
    (i : Nat) (hi : i + 1 < r) : Step (extend n r p i) (extend n r p (i + 1)) := by
  rw [extend_eq n r p i (by omega), extend_eq n r p (i + 1) hi]
  exact hp i hi

theorem chainTime_congr_prefix (n : Nat) (p q : Nat → Vertex n) (r : Nat)
    (h : ∀ i < r, p i = q i) : GreedyClockChain.chainTime p r = GreedyClockChain.chainTime q r := by
  induction r with
  | zero => funext ω; simp only [GreedyClockChain.chainTime_zero]
  | succ r ih =>
    have hprev : GreedyClockChain.chainTime p r = GreedyClockChain.chainTime q r :=
      ih (fun i hi => h i (by omega))
    funext ω
    rw [GreedyClockChain.chainTime_succ, GreedyClockChain.chainTime_succ, hprev, h r (by omega)]

theorem nat_path_covered (n r : Nat) (hr : 0 < r) (p : Nat → Vertex n)
    (hp : ∀ i, i + 1 < r → Step (p i) (p (i + 1))) :
    ∃ q ∈ family n r, ∀ i < r, extend n r q i = p i := by
  let q : Fin r → Vertex n := fun i => p i.val
  refine ⟨q, legal_mem_family n r hr q (fun i hi => hp i hi), ?_⟩
  intro i hi
  exact extend_eq n r q i hi

theorem family_nonempty (n r : Nat) : (family n r).Nonempty := by
  let code : Vertex n × (Fin (r - 1) → Fin 5) := (origin n, fun _ => 0)
  exact ⟨codePath n r code, Finset.mem_image.mpr ⟨code, Finset.mem_univ _, rfl⟩⟩

def fastEvent (n r : Nat) (t : ℝ) : Set (ExponentialClocks.Sample (Vertex n)) :=
  ⋃ p ∈ family n r, {ω | GreedyClockChain.chainTime (extend n r p) r ω ≤ (t : WithTop ℝ)}

theorem fastEvent_measurable (n r : Nat) (t : ℝ) : MeasurableSet (fastEvent n r t) := by
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _hp =>
    (GreedyClockChain.lower_tail_nine (extend n r p) r t).1

/-- Any specified legal sequence whose greedy chain finishes by `t` belongs to the finite union. -/
theorem fastEvent_of_nat_witness (n r : Nat) (hr : 0 < r) (p : Nat → Vertex n)
    (hp : ∀ i, i + 1 < r → Step (p i) (p (i + 1)))
    {t : ℝ}
    (ω : ExponentialClocks.Sample (Vertex n))
    (htime : GreedyClockChain.chainTime p r ω ≤ (t : WithTop ℝ)) :
    ω ∈ fastEvent n r t := by
  obtain ⟨q, hq, hprefix⟩ := nat_path_covered n r hr p hp
  apply Set.mem_iUnion.mpr
  refine ⟨q, Set.mem_iUnion.mpr ⟨hq, ?_⟩⟩
  change GreedyClockChain.chainTime (extend n r q) r ω ≤ (t : WithTop ℝ)
  rw [chainTime_congr_prefix n (extend n r q) p r hprefix]
  exact htime

theorem mem_fastEvent_iff_exists (n r : Nat) (hr : 0 < r) (t : ℝ)
    (ω : ExponentialClocks.Sample (Vertex n)) :
    ω ∈ fastEvent n r t ↔ ∃ p : Nat → Vertex n,
      (∀ i, i + 1 < r → Step (p i) (p (i + 1))) ∧
        GreedyClockChain.chainTime p r ω ≤ (t : WithTop ℝ) := by
  constructor
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨p, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hp, htime⟩
    refine ⟨extend n r p, ?_, htime⟩
    exact extend_legal n r p (mem_family_legal n r hp)
  · rintro ⟨p, hp, htime⟩
    exact fastEvent_of_nat_witness n r hr p hp ω htime

/-- A specified increasing arrival witness gives an early greedy chain and hence finite-union membership. -/
theorem fastEvent_of_arrival_witness (n r : Nat) (hr : 0 < r)
    (p : Nat → Vertex n) (index : Nat → Nat)
    (hp : ∀ i, i + 1 < r → Step (p i) (p (i + 1)))
    (ω : ExponentialClocks.Sample (Vertex n)) {t : ℝ}
    (hstart : 0 < ArrivalFiltration.chronologicalArrival (p 0) (index 0) ω)
    (hstep : ∀ i, i + 1 < r →
      ArrivalFiltration.chronologicalArrival (p i) (index i) ω <
        ArrivalFiltration.chronologicalArrival (p (i + 1)) (index (i + 1)) ω)
    (hlast : ArrivalFiltration.chronologicalArrival (p (r - 1)) (index (r - 1)) ω ≤ t) :
    ω ∈ fastEvent n r t := by
  apply fastEvent_of_nat_witness n r hr p hp ω
  exact (GreedyClockChain.chainTime_le_witness p index r ω hr hstart hstep).trans
    (WithTop.coe_le_coe.mpr hlast)

/-- Empty chains are at time zero; the positive-length estimate is handled separately. -/
theorem fastEvent_zero (n : Nat) (t : ℝ) : fastEvent n 0 t = {_ω | 0 ≤ t} := by
  ext ω
  simp only [fastEvent, Set.mem_iUnion, Set.mem_ofPred_eq, GreedyClockChain.chainTime_zero]
  constructor
  · rintro ⟨p, _hp, ht⟩
    exact_mod_cast ht
  · intro ht
    obtain ⟨p, hp⟩ := family_nonempty n 0
    refine ⟨p, hp, ?_⟩
    exact_mod_cast ht

/-- The single-chain lower tail gives a closed finite union bound, with no inter-path independence. -/
theorem fastEvent_tail (n r : Nat) (t : ℝ) :
    (ExponentialClocks.clockMeasure (Vertex n)).real (fastEvent n r t) ≤
      (((n + 2) ^ 2 : Nat) : ℝ) * (5 : ℝ) ^ (r - 1) *
        Real.exp (9 * t) * ((10 : ℝ)⁻¹) ^ r := by
  have hcard : ((family n r).card : ℝ) ≤
      (((n + 2) ^ 2 : Nat) : ℝ) * (5 : ℝ) ^ (r - 1) := by
    exact_mod_cast family_card_le n r
  calc
    _ ≤ ∑ p ∈ family n r, (ExponentialClocks.clockMeasure (Vertex n)).real
        {ω | GreedyClockChain.chainTime (extend n r p) r ω ≤ (t : WithTop ℝ)} :=
      measureReal_biUnion_finset_le (family n r) _
    _ ≤ ∑ _p ∈ family n r, Real.exp (9 * t) * ((10 : ℝ)⁻¹) ^ r := by
      apply Finset.sum_le_sum
      intro p _hp
      exact (GreedyClockChain.lower_tail_nine (extend n r p) r t).2
    _ = ((family n r).card : ℝ) * Real.exp (9 * t) * ((10 : ℝ)⁻¹) ^ r := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le) (by positivity)

theorem decay_factor_eq (r : Nat) (hr : 0 < r) :
    (5 : ℝ) ^ (r - 1) * ((10 : ℝ)⁻¹) ^ r = (1 / 5 : ℝ) * ((2 : ℝ)⁻¹) ^ r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one]
  have hpow : (5 : ℝ) ^ k * ((10 : ℝ)⁻¹) ^ k = ((2 : ℝ)⁻¹) ^ k := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((5 : ℝ) ^ k * ((10 : ℝ)⁻¹) ^ k) * (10 : ℝ)⁻¹ := by rw [pow_succ]; ring
    _ = ((2 : ℝ)⁻¹) ^ k * (10 : ℝ)⁻¹ := by rw [hpow]
    _ = _ := by rw [pow_succ]; norm_num; ring

/-- For positive length, five spatial choices combine with the ten-fold Laplace factor. -/
theorem fastEvent_half_tail (n r : Nat) (hr : 0 < r) (t : ℝ) :
    MeasurableSet (fastEvent n r t) ∧
      (ExponentialClocks.clockMeasure (Vertex n)).real (fastEvent n r t) ≤
        ((((n + 2) ^ 2 : Nat) : ℝ) / 5) * Real.exp (9 * t) * ((2 : ℝ)⁻¹) ^ r := by
  refine ⟨fastEvent_measurable n r t, (fastEvent_tail n r t).trans_eq ?_⟩
  calc
    _ = (((n + 2) ^ 2 : Nat) : ℝ) * Real.exp (9 * t) *
        ((5 : ℝ) ^ (r - 1) * ((10 : ℝ)⁻¹) ^ r) := by ring
    _ = _ := by rw [decay_factor_eq r hr]; ring

end MathResearchAnalysis.SquareGreedyPaths

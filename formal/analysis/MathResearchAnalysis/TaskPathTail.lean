module

public import MathResearchAnalysis.TaskPaths
public import MathResearchAnalysis.PathTail

set_option autoImplicit false

/-!
# Conditional tails for the recursively defined real task maximum

This connects the actual path enumeration and counting theorem to the
nonnegative conditional-moment theorem. The task recurrence and path counts
are proved in `TaskPaths`; neither is a probability-bound input here.
The single-step conditioning assumptions still need a Poisson model.
-/

public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.TaskPathTail

variable {Ω V : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable [DecidableEq V] [IsProbabilityMeasure μ]

/-- Waits in forward layer order from the reversed path representation.
The values beyond the path length are immaterial. -/
@[expose] def pathWait (delay : Nat → V → Ω → ℝ) : List V → Nat → Ω → ℝ
  | [], _ => fun _ => 0
  | v :: q, i => if i = q.length then delay i v else pathWait delay q i

theorem prefixSum_congr (f g : Nat → Ω → ℝ) (n : Nat)
    (h : ∀ i < n, f i = g i) :
    ConditionalMoment.prefixSum f n = ConditionalMoment.prefixSum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    funext ω
    simp only [ConditionalMoment.prefixSum, hp, h n (Nat.lt_succ_self n)]

omit [DecidableEq V] in
/-- The conditional-moment prefix is the actual task path weight. -/
theorem prefixSum_pathWait (delay : Nat → V → Ω → ℝ) (p : List V) (ω : Ω) :
    ConditionalMoment.prefixSum (pathWait delay p) p.length ω =
      TaskPaths.System.weight (fun i v => delay i v ω) p := by
  induction p with
  | nil => rfl
  | cons v q ih =>
    have hp := prefixSum_congr (pathWait delay (v :: q)) (pathWait delay q) q.length
      (fun i hi => by simp [pathWait, Nat.ne_of_lt hi])
    have hlast : pathWait delay (v :: q) q.length ω = delay q.length v ω := by
      simp only [pathWait, ite_eq_left]
    change ConditionalMoment.prefixSum (pathWait delay (v :: q)) q.length ω +
      pathWait delay (v :: q) q.length ω =
        delay q.length v ω + TaskPaths.System.weight (fun i v => delay i v ω) q
    rw [hp, hlast, ih]
    exact add_comm _ _

section FiniteAllVertices

variable [Fintype V] [Nonempty V]

omit [Nonempty V] in
theorem allPaths_length (M : TaskPaths.System V) (k : Nat) {p : List V}
    (hp : p ∈ M.allPaths k) : p.length = k + 1 := by
  obtain ⟨v, hv⟩ := (M.mem_allPaths_iff k p).mp hp
  exact M.path_length k v ((M.mem_paths_iff_legal k v p).mpr hv)

/-- Conditional moments yield the tail of the recursively defined layer maximum. -/
theorem layer_maximum_tail (M : TaskPaths.System V)
    (delay : Nat → V → Ω → ℝ) (filtration : List V → Filtration Nat mΩ)
    (k : Nat) (θ constant threshold : ℝ) (hθ : 0 < θ)
    (hknown : ∀ p ∈ M.allPaths k, ∀ i < k + 1,
      StronglyMeasurable[filtration p (i + 1)] (pathWait delay p i))
    (hwaitInt : ∀ p ∈ M.allPaths k, ∀ i < k + 1,
      Integrable (fun ω => Real.exp (θ * pathWait delay p i ω)) μ)
    (hconditional : ∀ p ∈ M.allPaths k, ∀ i < k + 1,
      μ[(fun ω => Real.exp (θ * pathWait delay p i ω)) | filtration p i] =ᵐ[μ]
        fun _ => constant) :
    MeasurableSet {ω | threshold < M.layerMaximum (fun i v => delay i v ω) k} ∧
      μ.real {ω | threshold < M.layerMaximum (fun i v => delay i v ω) k} ≤
        ((M.allPaths k).card : ℝ) * constant ^ (k + 1) * Real.exp (-θ * threshold) := by
  have h := PathTail.fixed_paths_maximum_tail (M.allPaths k) (M.allPaths_nonempty k)
    filtration (pathWait delay) (k + 1) θ constant hθ threshold
    hknown hwaitInt hconditional
  have hevents : {ω | threshold < M.layerMaximum (fun i v => delay i v ω) k} =
      {ω | threshold < FiniteTail.finiteMaximum (M.allPaths k) (M.allPaths_nonempty k)
        (fun p => ConditionalMoment.prefixSum (pathWait delay p) (k + 1)) ω} := by
    rw [FiniteTail.maximum_exceeds_eq]
    ext ω
    rw [Set.mem_ofPred_eq, M.layerMaximum_exceeds_iff]
    change (∃ p ∈ M.allPaths k, threshold < TaskPaths.System.weight
      (fun i v => delay i v ω) p) ↔
        ∃ p ∈ M.allPaths k, threshold <
          ConditionalMoment.prefixSum (pathWait delay p) (k + 1) ω
    constructor <;> rintro ⟨p, hp, ht⟩ <;> refine ⟨p, hp, ?_⟩
    · simpa only [← allPaths_length M k hp, prefixSum_pathWait] using ht
    · simpa only [← allPaths_length M k hp, prefixSum_pathWait] using ht
  rw [hevents]
  exact h

/-- The degree count is derived from the actual predecessor sets. -/
theorem degree_half_tail (M : TaskPaths.System V)
    (delay : Nat → V → Ω → ℝ) (filtration : List V → Filtration Nat mΩ)
    (d k : Nat) (degree : ∀ j v, (M.predecessors j v).card ≤ d) (threshold : ℝ)
    (hknown : ∀ p ∈ M.allPaths k, ∀ i < k + 1,
      StronglyMeasurable[filtration p (i + 1)] (pathWait delay p i))
    (hwaitInt : ∀ p ∈ M.allPaths k, ∀ i < k + 1,
      Integrable (fun ω => Real.exp ((1 / 2 : ℝ) * pathWait delay p i ω)) μ)
    (hconditional : ∀ p ∈ M.allPaths k, ∀ i < k + 1,
      μ[(fun ω => Real.exp ((1 / 2 : ℝ) * pathWait delay p i ω)) | filtration p i] =ᵐ[μ]
        fun _ => 2) :
    MeasurableSet {ω | threshold < M.layerMaximum (fun i v => delay i v ω) k} ∧
      μ.real {ω | threshold < M.layerMaximum (fun i v => delay i v ω) k} ≤
        (Fintype.card V : ℝ) * (d : ℝ) ^ k * (2 : ℝ) ^ (k + 1) *
          Real.exp (-threshold / 2) := by
  have h := layer_maximum_tail M delay filtration k (1 / 2) 2 threshold
    (by norm_num) hknown hwaitInt hconditional
  refine ⟨h.1, h.2.trans ?_⟩
  have hcard : ((M.allPaths k).card : ℝ) ≤ (Fintype.card V : ℝ) * (d : ℝ) ^ k := by
    exact_mod_cast M.allPaths_card_le d degree k
  have hexp : -(1 / 2 : ℝ) * threshold = -threshold / 2 := by ring
  rw [hexp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (by positivity)) (Real.exp_pos _).le

end FiniteAllVertices

/-- The version for the actual finite set of tasks in the final layer. -/
theorem terminal_maximum_tail (M : TaskPaths.System V)
    (tasks : Finset V) (ht : tasks.Nonempty)
    (delay : Nat → V → Ω → ℝ) (filtration : List V → Filtration Nat mΩ)
    (k : Nat) (θ constant threshold : ℝ) (hθ : 0 < θ)
    (hknown : ∀ p ∈ M.terminalPaths tasks k, ∀ i < k + 1,
      StronglyMeasurable[filtration p (i + 1)] (pathWait delay p i))
    (hwaitInt : ∀ p ∈ M.terminalPaths tasks k, ∀ i < k + 1,
      Integrable (fun ω => Real.exp (θ * pathWait delay p i ω)) μ)
    (hconditional : ∀ p ∈ M.terminalPaths tasks k, ∀ i < k + 1,
      μ[(fun ω => Real.exp (θ * pathWait delay p i ω)) | filtration p i] =ᵐ[μ]
        fun _ => constant) :
    MeasurableSet {ω | threshold < M.terminalMaximum tasks ht
        (fun i v => delay i v ω) k} ∧
      μ.real {ω | threshold < M.terminalMaximum tasks ht
        (fun i v => delay i v ω) k} ≤
        ((M.terminalPaths tasks k).card : ℝ) * constant ^ (k + 1) *
          Real.exp (-θ * threshold) := by
  have h := PathTail.fixed_paths_maximum_tail (M.terminalPaths tasks k)
    (M.terminalPaths_nonempty tasks ht k) filtration (pathWait delay) (k + 1)
    θ constant hθ threshold hknown hwaitInt hconditional
  have hlength : ∀ p ∈ M.terminalPaths tasks k, p.length = k + 1 := by
    intro p hp
    obtain ⟨v, _, hv⟩ := (M.mem_terminalPaths_iff tasks k p).mp hp
    exact M.path_length k v ((M.mem_paths_iff_legal k v p).mpr hv)
  have hevents : {ω | threshold < M.terminalMaximum tasks ht
      (fun i v => delay i v ω) k} =
      {ω | threshold < FiniteTail.finiteMaximum (M.terminalPaths tasks k)
        (M.terminalPaths_nonempty tasks ht k)
        (fun p => ConditionalMoment.prefixSum (pathWait delay p) (k + 1)) ω} := by
    rw [FiniteTail.maximum_exceeds_eq]
    ext ω
    rw [Set.mem_ofPred_eq, M.terminalMaximum_exceeds_iff]
    change (∃ p ∈ M.terminalPaths tasks k, threshold < TaskPaths.System.weight
      (fun i v => delay i v ω) p) ↔
        ∃ p ∈ M.terminalPaths tasks k, threshold <
          ConditionalMoment.prefixSum (pathWait delay p) (k + 1) ω
    constructor <;> rintro ⟨p, hp, htp⟩ <;> refine ⟨p, hp, ?_⟩
    · simpa only [← hlength p hp, prefixSum_pathWait] using htp
    · simpa only [← hlength p hp, prefixSum_pathWait] using htp
  rw [hevents]
  exact h

/-- Four-neighbor counting is an instance of this actual predecessor-degree bound. -/
theorem terminal_degree_half_tail (M : TaskPaths.System V)
    (tasks : Finset V) (ht : tasks.Nonempty)
    (delay : Nat → V → Ω → ℝ) (filtration : List V → Filtration Nat mΩ)
    (d k : Nat) (degree : ∀ j v, (M.predecessors j v).card ≤ d) (threshold : ℝ)
    (hknown : ∀ p ∈ M.terminalPaths tasks k, ∀ i < k + 1,
      StronglyMeasurable[filtration p (i + 1)] (pathWait delay p i))
    (hwaitInt : ∀ p ∈ M.terminalPaths tasks k, ∀ i < k + 1,
      Integrable (fun ω => Real.exp ((1 / 2 : ℝ) * pathWait delay p i ω)) μ)
    (hconditional : ∀ p ∈ M.terminalPaths tasks k, ∀ i < k + 1,
      μ[(fun ω => Real.exp ((1 / 2 : ℝ) * pathWait delay p i ω)) | filtration p i] =ᵐ[μ]
        fun _ => 2) :
    MeasurableSet {ω | threshold < M.terminalMaximum tasks ht
        (fun i v => delay i v ω) k} ∧
      μ.real {ω | threshold < M.terminalMaximum tasks ht
        (fun i v => delay i v ω) k} ≤
        (tasks.card : ℝ) * (d : ℝ) ^ k * (2 : ℝ) ^ (k + 1) *
          Real.exp (-threshold / 2) := by
  have h := terminal_maximum_tail M tasks ht delay filtration k (1 / 2) 2 threshold
    (by norm_num) hknown hwaitInt hconditional
  refine ⟨h.1, h.2.trans ?_⟩
  have hcard : ((M.terminalPaths tasks k).card : ℝ) ≤
      (tasks.card : ℝ) * (d : ℝ) ^ k := by
    exact_mod_cast M.terminalPaths_card_le tasks d degree k
  have hexp : -(1 / 2 : ℝ) * threshold = -threshold / 2 := by ring
  rw [hexp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (by positivity)) (Real.exp_pos _).le

/-- A bound for all completed task layers follows from proved last-layer domination. -/
theorem prefix_degree_half_tail (M : TaskPaths.System V)
    (tasks : Nat → Finset V) (ht : ∀ j, (tasks j).Nonempty)
    (delay : Nat → V → Ω → ℝ) (filtration : List V → Filtration Nat mΩ)
    (nonnegative : ∀ ω j v, 0 ≤ delay j v ω)
    (successors : ∀ j u, u ∈ tasks j →
      ∃ v ∈ tasks (j + 1), u ∈ M.predecessors j v)
    (d k : Nat) (degree : ∀ j v, (M.predecessors j v).card ≤ d) (threshold : ℝ)
    (hknown : ∀ p ∈ M.terminalPaths (tasks k) k, ∀ i < k + 1,
      StronglyMeasurable[filtration p (i + 1)] (pathWait delay p i))
    (hwaitInt : ∀ p ∈ M.terminalPaths (tasks k) k, ∀ i < k + 1,
      Integrable (fun ω => Real.exp ((1 / 2 : ℝ) * pathWait delay p i ω)) μ)
    (hconditional : ∀ p ∈ M.terminalPaths (tasks k) k, ∀ i < k + 1,
      μ[(fun ω => Real.exp ((1 / 2 : ℝ) * pathWait delay p i ω)) | filtration p i] =ᵐ[μ]
        fun _ => 2) :
    MeasurableSet {ω | threshold < M.prefixMaximum tasks ht
        (fun i v => delay i v ω) k} ∧
      μ.real {ω | threshold < M.prefixMaximum tasks ht
        (fun i v => delay i v ω) k} ≤
        ((tasks k).card : ℝ) * (d : ℝ) ^ k * (2 : ℝ) ^ (k + 1) *
          Real.exp (-threshold / 2) := by
  have hevents : {ω | threshold < M.prefixMaximum tasks ht
      (fun i v => delay i v ω) k} =
      {ω | threshold < M.terminalMaximum (tasks k) (ht k)
        (fun i v => delay i v ω) k} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [M.prefixMaximum_eq_last tasks ht _ (nonnegative ω) successors k]
  rw [hevents]
  exact terminal_degree_half_tail M (tasks k) (ht k) delay filtration d k degree threshold
    hknown hwaitInt hconditional

end MathResearchAnalysis.TaskPathTail

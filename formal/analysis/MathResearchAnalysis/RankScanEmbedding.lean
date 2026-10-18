module

public import MathResearchAnalysis.RankSlotEmbedding
public import Mathlib.Data.List.Flatten
public import Mathlib.Data.Finset.Dedup

set_option autoImplicit false

/-!
# Completing actual rank slots to full color scans

Each actual slot batch is kept as a prefix and completed by the missing sites
of the corresponding full checkerboard color. Positive sorted labels decompose
into their actual slot filters. A bound on the computed source ranks therefore
embeds the actual target site word as a sublist of `2 * q` full color scans.
No sublist conclusion or scan-completion premise is assumed.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.RankScanEmbedding

abbrev Site (n : Nat) := SquareTasks.Vertex n
abbrev Sample (n : Nat) := ExponentialClocks.Sample (Site n)

/-- Actual sites in one rank/color slot, retaining their target order. -/
def slotSites {n : Nat} (ω : Sample n) (t : ℝ) (s : Nat) : List (Site n) :=
  (RankSlotEmbedding.slotBatch ω t s).map (fun a => a.1.1)

/-- Preserve the actual batch as a prefix, then add precisely its missing color sites. -/
def completionBatch {n : Nat} (ω : Sample n) (t : ℝ) (s : Nat) : List (Site n) :=
  slotSites ω t s ++
    (SquareTasks.tasks n true (s - 1)).toList.filter
      (fun v => decide (v ∉ slotSites ω t s))

/-- The first positive slot is true, then false, for a total of `2 * q` slots. -/
def scanWord {n : Nat} (ω : Sample n) (t : ℝ) (q : Nat) : List (Site n) :=
  (List.range (2 * q)).flatMap (fun i => completionBatch ω t (i + 1))

theorem slotSites_nodup {n : Nat} (ω : Sample n) (t : ℝ) (s : Nat) :
    (slotSites ω t s).Nodup :=
  RankSlotEmbedding.slotBatch_sites_nodup ω t s

theorem slotSites_sublist_completionBatch {n : Nat}
    (ω : Sample n) (t : ℝ) (s : Nat) :
    (slotSites ω t s).Sublist (completionBatch ω t s) := by
  exact List.sublist_append_left _ _

theorem completionBatch_nodup {n : Nat} (ω : Sample n) (t : ℝ) (s : Nat) :
    (completionBatch ω t s).Nodup := by
  classical
  refine List.nodup_append.mpr ⟨slotSites_nodup ω t s,
    (Finset.nodup_toList _).filter _, ?_⟩
  intro a ha b hb heq
  have hnot := (List.mem_filter.mp hb).2
  have hnot' : b ∉ slotSites ω t s := by simpa using hnot
  exact hnot' (heq ▸ ha)

theorem mem_slotSites_tasks {n : Nat} (ω : Sample n) (t : ℝ) (s : Nat)
    {v : Site n} (hv : v ∈ slotSites ω t s) :
    v ∈ SquareTasks.tasks n true (s - 1) := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  obtain ⟨ha, hs⟩ := (RankSlotEmbedding.mem_slotBatch_iff ω t s a).mp ha
  have hr := RankSlotEmbedding.source_positive ω t
    ((RankSlotEmbedding.targetLabels_perm ω t).mem_iff.mpr ha)
  rw [SquareTasks.mem_tasks_colour]
  cases hc : SquareTasks.colour a.1.1
  · have hs' : 2 * a.2 = s := by
      simpa [RankSlotEmbedding.labelSlot, RankSlotEmbedding.slot, hc] using hs
    have hp : (s - 1) % 2 ≠ 0 := by omega
    simp [hp]
  · have hs' : 2 * a.2 - 1 = s := by
      simpa [RankSlotEmbedding.labelSlot, RankSlotEmbedding.slot, hc] using hs
    have hp : (s - 1) % 2 = 0 := by omega
    simp [hp]

theorem mem_completionBatch_iff {n : Nat} (ω : Sample n) (t : ℝ) (s : Nat)
    (v : Site n) :
    v ∈ completionBatch ω t s ↔ v ∈ SquareTasks.tasks n true (s - 1) := by
  classical
  simp only [completionBatch, List.mem_append, List.mem_filter,
    Finset.mem_toList, decide_eq_true_eq]
  constructor
  · intro hv
    rcases hv with hv | ⟨hv, _⟩
    · exact mem_slotSites_tasks ω t s hv
    · exact hv
  · intro hv
    by_cases hb : v ∈ slotSites ω t s
    · exact Or.inl hb
    · exact Or.inr ⟨hv, hb⟩

/-- Every completed slot is a full, duplicate-free enumeration of its true color. -/
theorem completionBatch_perm_tasks {n : Nat} (ω : Sample n) (t : ℝ) (s : Nat) :
    (completionBatch ω t s).Perm (SquareTasks.tasks n true (s - 1)).toList := by
  classical
  apply (List.perm_ext_iff_of_nodup (completionBatch_nodup ω t s)
    (Finset.nodup_toList _)).mpr
  intro v
  simpa using mem_completionBatch_iff ω t s v

private theorem sorted_filter_split {α : Type*} (key : α → Nat)
    (l : List α) (sorted : l.Pairwise (fun a b => key a ≤ key b)) (m : Nat) :
    l.filter (fun a => decide (key a ≤ m)) ++
      l.filter (fun a => decide (m < key a)) = l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp sorted
    by_cases h : key a ≤ m
    · simpa [h, show ¬ m < key a by omega] using congrArg (List.cons a) (ih hs)
    · have hrest : ∀ b ∈ rest, m < key b := by
        intro b hb
        have hab := ha b hb
        omega
      have hlow : rest.filter (fun b => decide (key b ≤ m)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        simp only [decide_eq_true_eq]
        have := hrest b hb
        omega
      have hhigh : rest.filter (fun b => decide (m < key b)) = rest := by
        apply List.filter_eq_self.mpr
        intro b hb
        simpa using hrest b hb
      simp [h, show m < key a by omega, hlow, hhigh]

private theorem sorted_bucket_prefix {α : Type*} (key : α → Nat)
    (l : List α) (sorted : l.Pairwise (fun a b => key a ≤ key b))
    (positive : ∀ a ∈ l, 0 < key a) (m : Nat) :
    (List.range m).flatMap (fun i => l.filter (fun a => decide (key a = i + 1))) =
      l.filter (fun a => decide (key a ≤ m)) := by
  induction m with
  | zero =>
    simp only [List.range_zero, List.flatMap_nil]
    symm
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    simp only [decide_eq_true_eq]
    have := positive a ha
    omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih]
    have hs := sorted_filter_split key
      (l.filter (fun a => decide (key a ≤ m + 1)))
      (sorted.filter _) m
    have hlow :
        (l.filter (fun a => decide (key a ≤ m + 1))).filter
          (fun a => decide (key a ≤ m)) = l.filter (fun a => decide (key a ≤ m)) := by
      simp only [List.filter_filter]
      apply List.filter_congr
      intro a _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    have hhigh :
        (l.filter (fun a => decide (key a ≤ m + 1))).filter
          (fun a => decide (m < key a)) = l.filter (fun a => decide (key a = m + 1)) := by
      simp only [List.filter_filter]
      apply List.filter_congr
      intro a _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    rw [hlow, hhigh] at hs
    exact hs

theorem targetLabels_eq_flatMap_slotBatch {n : Nat} (ω : Sample n) (t : ℝ) (q : Nat)
    (hrank : ∀ a ∈ RankSlotEmbedding.source ω t, a.2 ≤ q) :
    RankSlotEmbedding.targetLabels ω t =
      (List.range (2 * q)).flatMap (fun i => RankSlotEmbedding.slotBatch ω t (i + 1)) := by
  have hpositive : ∀ a ∈ RankSlotEmbedding.targetLabels ω t,
      0 < RankSlotEmbedding.labelSlot a := by
    intro a ha
    have hr := RankSlotEmbedding.source_positive ω t
      ((RankSlotEmbedding.targetLabels_perm ω t).mem_iff.mpr ha)
    unfold RankSlotEmbedding.labelSlot RankSlotEmbedding.slot
    split <;> omega
  have hbound : ∀ a ∈ RankSlotEmbedding.targetLabels ω t,
      RankSlotEmbedding.labelSlot a ≤ 2 * q := by
    intro a ha
    have hr := hrank a ((RankSlotEmbedding.targetLabels_perm ω t).mem_iff.mpr ha)
    unfold RankSlotEmbedding.labelSlot RankSlotEmbedding.slot
    split <;> omega
  have hsplit := sorted_bucket_prefix RankSlotEmbedding.labelSlot
    (RankSlotEmbedding.targetLabels ω t) (RankSlotEmbedding.targetLabels_sorted ω t)
    hpositive (2 * q)
  rw [List.filter_eq_self.mpr (fun a ha => by simpa using hbound a ha)] at hsplit
  exact hsplit.symm

theorem target_sites_eq_flatMap_slotSites {n : Nat} (ω : Sample n) (t : ℝ) (q : Nat)
    (hrank : ∀ a ∈ RankSlotEmbedding.source ω t, a.2 ≤ q) :
    (RankSlotEmbedding.target ω t).map Prod.fst =
      (List.range (2 * q)).flatMap (fun i => slotSites ω t (i + 1)) := by
  simp only [RankSlotEmbedding.target, List.map_map]
  rw [targetLabels_eq_flatMap_slotBatch ω t q hrank]
  simp only [List.map_flatMap, slotSites, Function.comp_def]

/-- Actual computed rank bounds supply the scan embedding without a sublist premise. -/
theorem target_sites_sublist_scanWord {n : Nat} (ω : Sample n) (t : ℝ) (q : Nat)
    (hrank : ∀ a ∈ RankSlotEmbedding.source ω t, a.2 ≤ q) :
    ((RankSlotEmbedding.target ω t).map Prod.fst).Sublist (scanWord ω t q) := by
  rw [target_sites_eq_flatMap_slotSites ω t q hrank]
  exact List.Sublist.flatMap_right (List.range (2 * q))
    (fun i _ => slotSites_sublist_completionBatch ω t (i + 1))

end MathResearchAnalysis.RankScanEmbedding

module

public import MathResearchAnalysis.GridMajorityPeeling

set_option autoImplicit false

/-!
# Majority cleanup after actual finite event words

True denotes minus. Every event performs the actual four-neighbour update with
its supplied tie mark. Updates outside the fixed mask are the identity, even
on a state that is not stable. The modified update cleans up only after an
event inside the mask. All comparisons below are deterministic and use the
same ordered event word. No random clock law or contour invariant is asserted.
-/

@[expose] public section

namespace MathResearchAnalysis.DropletModifiedWord

open InfiniteGridModel
open GridMajorityPeeling

abbrev Stable (S : Finset Site) : Prop :=
  FiniteMajorityPeeling.Stable neighbors4 S

def localRule (S : Finset Site) (v : Site) (tie : Bool) : Bool :=
  majority4 (state S (north v)) (state S (east v))
    (state S (south v)) (state S (west v)) tie

def rawStep (S : Finset Site) (v : Site) (tie : Bool) : Finset Site :=
  if localRule S v tie then insert v S else S.erase v

def maskedRawStep (D S : Finset Site) (v : Site) (tie : Bool) : Finset Site :=
  if v ∈ D then rawStep S v tie else S

def modifiedStep (D S : Finset Site) (v : Site) (tie : Bool) : Finset Site :=
  if v ∈ D then cleanup (rawStep S v tie) else S

theorem localRule_eq_update (S : Finset Site) (v : Site) (tie : Bool) (t : Nat) :
    localRule S v tie = InfiniteGridModel.update (fun _ _ => tie) t v (state S) := rfl

theorem state_insert (S : Finset Site) (v : Site) :
    state (insert v S) = Function.update (state S) v true := by
  funext u
  by_cases h : u = v
  · subst u
    simp [state]
  · simp [state, h]

theorem state_rawStep (S : Finset Site) (v : Site) (tie : Bool) :
    state (rawStep S v tie) = Function.update (state S) v (localRule S v tie) := by
  cases h : localRule S v tie <;> simp [rawStep, h, state_erase, state_insert]

theorem rawStep_actual_write (S : Finset Site) (v : Site) (tie : Bool) (t : Nat) :
    state (rawStep S v tie) = Function.update (state S) v
      (InfiniteGridModel.update (fun _ _ => tie) t v (state S)) := by
  rw [state_rawStep, ← localRule_eq_update]

theorem rawStep_actual_marks (S : Finset Site) (v : Site) (marks : Marks) (t : Nat) :
    state (rawStep S v (marks t v)) = Function.update (state S) v
      (InfiniteGridModel.update marks t v (state S)) := state_rawStep S v (marks t v)

theorem mem_rawStep (S : Finset Site) (v u : Site) (tie : Bool) :
    u ∈ rawStep S v tie ↔ if u = v then localRule S v tie = true else u ∈ S := by
  cases h : localRule S v tie <;> by_cases huv : u = v <;>
    simp [rawStep, h, huv]

theorem state_mono {S T : Finset Site} (hST : S ⊆ T) (v : Site) :
    state S v ≤ state T v := by
  by_cases hS : v ∈ S
  · simp [state, hS, hST hS]
  · simp [state, hS]

theorem localRule_mono {S T : Finset Site} (hST : S ⊆ T) (v : Site) (tie : Bool) :
    localRule S v tie ≤ localRule T v tie :=
  majority4_monotone _ _ _ _ _ _ _ _ tie
    (state_mono hST _) (state_mono hST _) (state_mono hST _) (state_mono hST _)

theorem rawStep_mono {S T : Finset Site} (hST : S ⊆ T) (v : Site) (tie : Bool) :
    rawStep S v tie ⊆ rawStep T v tie := by
  intro u hu
  rw [mem_rawStep] at hu ⊢
  by_cases huv : u = v
  · simp only [huv, ite_eq_left] at hu ⊢
    have hm := localRule_mono hST v tie
    rw [hu] at hm
    exact Bool.eq_true_of_true_le hm
  · simpa only [huv, ite_false] using hST (by simpa only [huv, ite_false] using hu)

theorem maskedRawStep_of_not_mem (D S : Finset Site) (v : Site) (tie : Bool)
    (hv : v ∉ D) : maskedRawStep D S v tie = S := by
  simp [maskedRawStep, hv]

theorem modifiedStep_of_not_mem (D S : Finset Site) (v : Site) (tie : Bool)
    (hv : v ∉ D) : modifiedStep D S v tie = S := by
  simp [modifiedStep, hv]

theorem modifiedStep_subset_maskedRawStep (D S : Finset Site) (v : Site) (tie : Bool) :
    modifiedStep D S v tie ⊆ maskedRawStep D S v tie := by
  by_cases hv : v ∈ D
  · simpa only [modifiedStep, maskedRawStep, ite_eq_left hv] using cleanup_subset (rawStep S v tie)
  · simp [modifiedStep, maskedRawStep, hv]

theorem maskedRawStep_mono (D : Finset Site) {S T : Finset Site}
    (hST : S ⊆ T) (v : Site) (tie : Bool) :
    maskedRawStep D S v tie ⊆ maskedRawStep D T v tie := by
  by_cases hv : v ∈ D
  · simpa only [maskedRawStep, ite_eq_left hv] using rawStep_mono hST v tie
  · simpa only [maskedRawStep, ite_eq_right hv] using hST

theorem modifiedStep_mono (D : Finset Site) {S T : Finset Site}
    (hST : S ⊆ T) (v : Site) (tie : Bool) :
    modifiedStep D S v tie ⊆ modifiedStep D T v tie := by
  by_cases hv : v ∈ D
  · simpa only [modifiedStep, ite_eq_left hv] using cleanup_mono (rawStep_mono hST v tie)
  · simpa only [modifiedStep, ite_eq_right hv] using hST

theorem modifiedStep_subset_maskedRawStep_of_subset (D : Finset Site)
    {S T : Finset Site} (hST : S ⊆ T) (v : Site) (tie : Bool) :
    modifiedStep D S v tie ⊆ maskedRawStep D T v tie :=
  Finset.Subset.trans (modifiedStep_subset_maskedRawStep D S v tie)
    (maskedRawStep_mono D hST v tie)

theorem rawStep_subset_insert (S : Finset Site) (v : Site) (tie : Bool) :
    rawStep S v tie ⊆ insert v S := by
  unfold rawStep
  split
  · exact Finset.Subset.refl _
  · exact Finset.Subset.trans (Finset.erase_subset v S) (Finset.subset_insert v S)

theorem maskedRawStep_supported {D S : Finset Site} (hS : S ⊆ D)
    (v : Site) (tie : Bool) : maskedRawStep D S v tie ⊆ D := by
  by_cases hv : v ∈ D
  · simp only [maskedRawStep, ite_eq_left hv]
    exact Finset.Subset.trans (rawStep_subset_insert S v tie)
      (Finset.insert_subset hv hS)
  · simpa only [maskedRawStep, ite_eq_right hv] using hS

theorem modifiedStep_supported {D S : Finset Site} (hS : S ⊆ D)
    (v : Site) (tie : Bool) : modifiedStep D S v tie ⊆ D :=
  Finset.Subset.trans (modifiedStep_subset_maskedRawStep D S v tie)
    (maskedRawStep_supported hS v tie)

theorem modifiedStep_stable (D : Finset Site) {S : Finset Site} (hS : Stable S)
    (v : Site) (tie : Bool) : Stable (modifiedStep D S v tie) := by
  by_cases hv : v ∈ D
  · simpa only [modifiedStep, ite_eq_left hv, cleanup] using
      FiniteMajorityPeeling.stable_core neighbors4 (rawStep S v tie)
  · simpa only [modifiedStep, ite_eq_right hv] using hS

abbrev Event := Site × Bool

def rawWord (D S : Finset Site) : List Event → Finset Site
  | [] => S
  | e :: w => rawWord D (maskedRawStep D S e.1 e.2) w

def modifiedWord (D S : Finset Site) : List Event → Finset Site
  | [] => S
  | e :: w => modifiedWord D (modifiedStep D S e.1 e.2) w

@[simp] theorem rawWord_nil (D S : Finset Site) : rawWord D S [] = S := rfl

@[simp] theorem modifiedWord_nil (D S : Finset Site) : modifiedWord D S [] = S := rfl

theorem rawWord_cons (D S : Finset Site) (e : Event) (w : List Event) :
    rawWord D S (e :: w) = rawWord D (maskedRawStep D S e.1 e.2) w := rfl

theorem modifiedWord_cons (D S : Finset Site) (e : Event) (w : List Event) :
    modifiedWord D S (e :: w) = modifiedWord D (modifiedStep D S e.1 e.2) w := rfl

theorem rawWord_eq_foldl (D S : Finset Site) (w : List Event) :
    rawWord D S w = w.foldl (fun T e => maskedRawStep D T e.1 e.2) S := by
  induction w generalizing S with
  | nil => rfl
  | cons e w ih => exact ih _

theorem modifiedWord_eq_foldl (D S : Finset Site) (w : List Event) :
    modifiedWord D S w = w.foldl (fun T e => modifiedStep D T e.1 e.2) S := by
  induction w generalizing S with
  | nil => rfl
  | cons e w ih => exact ih _

theorem rawWord_append (D S : Finset Site) (w u : List Event) :
    rawWord D S (w ++ u) = rawWord D (rawWord D S w) u := by
  induction w generalizing S with
  | nil => rfl
  | cons e w ih => exact ih _

theorem modifiedWord_append (D S : Finset Site) (w u : List Event) :
    modifiedWord D S (w ++ u) = modifiedWord D (modifiedWord D S w) u := by
  induction w generalizing S with
  | nil => rfl
  | cons e w ih => exact ih _

theorem rawWord_mono (D : Finset Site) {S T : Finset Site} (hST : S ⊆ T)
    (w : List Event) : rawWord D S w ⊆ rawWord D T w := by
  induction w generalizing S T with
  | nil => exact hST
  | cons e w ih => exact ih (maskedRawStep_mono D hST e.1 e.2)

theorem modifiedWord_mono (D : Finset Site) {S T : Finset Site} (hST : S ⊆ T)
    (w : List Event) : modifiedWord D S w ⊆ modifiedWord D T w := by
  induction w generalizing S T with
  | nil => exact hST
  | cons e w ih => exact ih (modifiedStep_mono D hST e.1 e.2)

theorem modifiedWord_subset_rawWord (D : Finset Site) {S T : Finset Site}
    (hST : S ⊆ T) (w : List Event) : modifiedWord D S w ⊆ rawWord D T w := by
  induction w generalizing S T with
  | nil => exact hST
  | cons e w ih => exact ih (modifiedStep_subset_maskedRawStep_of_subset D hST e.1 e.2)

theorem rawWord_supported {D S : Finset Site} (hS : S ⊆ D) (w : List Event) :
    rawWord D S w ⊆ D := by
  induction w generalizing S with
  | nil => exact hS
  | cons e w ih => exact ih (maskedRawStep_supported hS e.1 e.2)

theorem modifiedWord_supported {D S : Finset Site} (hS : S ⊆ D) (w : List Event) :
    modifiedWord D S w ⊆ D :=
  Finset.Subset.trans (modifiedWord_subset_rawWord D (Finset.Subset.refl S) w)
    (rawWord_supported hS w)

theorem modifiedWord_stable (D : Finset Site) {S : Finset Site} (hS : Stable S)
    (w : List Event) : Stable (modifiedWord D S w) := by
  induction w generalizing S with
  | nil => exact hS
  | cons e w ih => exact ih (modifiedStep_stable D hS e.1 e.2)

end MathResearchAnalysis.DropletModifiedWord

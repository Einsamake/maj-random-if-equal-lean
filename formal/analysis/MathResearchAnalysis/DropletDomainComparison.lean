module

public import MathResearchAnalysis.DropletModifiedWord
public import MathResearchAnalysis.ExtendedRecoveryTime

set_option autoImplicit false

/-!
# Different-domain coupling and the first loss of an protected set

True denotes minus. Both processes use exactly the same ordered site/tie events.
The smaller process performs majority cleanup; the larger process performs the
actual raw four-neighbour update. These are deterministic event indices, not
physical clock times. The first loss of an protected set need not be absorbing for
the unfrozen process. Accordingly, only the first-loss time is compared with
the larger process's recovery time; the frozen state is compared only before
that first loss.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.DropletDomainComparison

open InfiniteGridModel GridMajorityPeeling DropletModifiedWord

theorem maskedRawStep_subset_of_domains {D E S T : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (v : Site) (tie : Bool) :
    maskedRawStep D S v tie ⊆ maskedRawStep E T v tie := by
  by_cases hvD : v ∈ D
  · have hvE := hDE hvD
    simpa only [maskedRawStep, ite_eq_left hvD, ite_eq_left hvE] using rawStep_mono hST v tie
  · simp only [maskedRawStep, ite_eq_right hvD]
    by_cases hvE : v ∈ E
    · simp only [ite_eq_left hvE]
      intro u hu
      have huv : u ≠ v := by
        intro huv
        subst u
        exact hvD (hSD hu)
      rw [mem_rawStep]
      simpa only [ite_eq_right huv] using hST hu
    · simpa only [ite_eq_right hvE] using hST

theorem modifiedStep_subset_of_domains {D E S T : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (v : Site) (tie : Bool) :
    modifiedStep D S v tie ⊆ maskedRawStep E T v tie :=
  Finset.Subset.trans (modifiedStep_subset_maskedRawStep D S v tie)
    (maskedRawStep_subset_of_domains hDE hSD hST v tie)

theorem rawWord_subset_of_domains {D E S T : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (w : List Event) :
    rawWord D S w ⊆ rawWord E T w := by
  induction w generalizing S T with
  | nil => exact hST
  | cons e w ih =>
      exact ih (maskedRawStep_supported hSD e.1 e.2)
        (maskedRawStep_subset_of_domains hDE hSD hST e.1 e.2)

theorem modifiedWord_subset_rawWord_of_domains {D E S T : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (w : List Event) :
    modifiedWord D S w ⊆ rawWord E T w := by
  induction w generalizing S T with
  | nil => exact hST
  | cons e w ih =>
      exact ih (modifiedStep_supported hSD e.1 e.2)
        (modifiedStep_subset_of_domains hDE hSD hST e.1 e.2)

theorem protected_missing_of_rawWord_empty {D E S T I : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (hI : I.Nonempty)
    (w : List Event) (hempty : rawWord E T w = ∅) :
    ¬ I ⊆ modifiedWord D S w := by
  intro hIin
  obtain ⟨v, hv⟩ := hI
  have hmem := modifiedWord_subset_rawWord_of_domains hDE hSD hST w (hIin hv)
  simp [hempty] at hmem

theorem rawWord_empty_event_subset_protected_missing_event {D E S T I : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (hI : I.Nonempty) :
    {w : List Event | rawWord E T w = ∅} ⊆ {w | ¬ I ⊆ modifiedWord D S w} := by
  intro w hw
  exact protected_missing_of_rawWord_empty hDE hSD hST hI w hw

def eventPrefix (events : Nat → Event) (n : Nat) : List Event :=
  (List.range n).map events

def rawTrajectory (D S : Finset Site) (events : Nat → Event) (n : Nat) : Finset Site :=
  rawWord D S (eventPrefix events n)

def modifiedTrajectory (D S : Finset Site) (events : Nat → Event) (n : Nat) : Finset Site :=
  modifiedWord D S (eventPrefix events n)

@[simp] theorem eventPrefix_zero (events : Nat → Event) : eventPrefix events 0 = [] := rfl

theorem eventPrefix_succ (events : Nat → Event) (n : Nat) :
    eventPrefix events (n + 1) = eventPrefix events n ++ [events n] := by
  simp [eventPrefix, List.range_succ]

@[simp] theorem rawTrajectory_zero (D S : Finset Site) (events : Nat → Event) :
    rawTrajectory D S events 0 = S := rfl

@[simp] theorem modifiedTrajectory_zero (D S : Finset Site) (events : Nat → Event) :
    modifiedTrajectory D S events 0 = S := rfl

theorem rawTrajectory_succ (D S : Finset Site) (events : Nat → Event) (n : Nat) :
    rawTrajectory D S events (n + 1) =
      maskedRawStep D (rawTrajectory D S events n) (events n).1 (events n).2 := by
  simp [rawTrajectory, eventPrefix_succ, rawWord_append, rawWord_cons]

theorem modifiedTrajectory_succ (D S : Finset Site) (events : Nat → Event) (n : Nat) :
    modifiedTrajectory D S events (n + 1) =
      modifiedStep D (modifiedTrajectory D S events n) (events n).1 (events n).2 := by
  simp [modifiedTrajectory, eventPrefix_succ, modifiedWord_append, modifiedWord_cons]

theorem rawTrajectory_supported {D S : Finset Site} (hSD : S ⊆ D)
    (events : Nat → Event) (n : Nat) : rawTrajectory D S events n ⊆ D :=
  rawWord_supported hSD _

theorem modifiedTrajectory_supported {D S : Finset Site} (hSD : S ⊆ D)
    (events : Nat → Event) (n : Nat) : modifiedTrajectory D S events n ⊆ D :=
  modifiedWord_supported hSD _

theorem modifiedTrajectory_subset_rawTrajectory {D E S T : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T)
    (events : Nat → Event) (n : Nat) :
    modifiedTrajectory D S events n ⊆ rawTrajectory E T events n :=
  modifiedWord_subset_rawWord_of_domains hDE hSD hST _

/-- First event index at which the protected set is no longer wholly minus. -/
def exitTime (D S I : Finset Site) (events : Nat → Event) : ℕ∞ :=
  ExtendedRecoveryTime.time
    (fun n (_ : Unit) => decide (I ⊆ modifiedTrajectory D S events n)) false ()

/-- First event index at which the actual larger raw process is empty. -/
def rawRecoveryIndex (E T : Finset Site) (events : Nat → Event) : ℕ∞ :=
  ExtendedRecoveryTime.time (fun n (_ : Unit) => rawTrajectory E T events n) ∅ ()

theorem exitTime_le_nat_iff (D S I : Finset Site) (events : Nat → Event) (n : Nat) :
    exitTime D S I events ≤ (n : ℕ∞) ↔
      ∃ j ≤ n, ¬ I ⊆ modifiedTrajectory D S events j := by
  simp [exitTime, ExtendedRecoveryTime.time_le_nat_iff]

theorem exitTime_eq_nat_iff (D S I : Finset Site) (events : Nat → Event) (n : Nat) :
    exitTime D S I events = (n : ℕ∞) ↔
      (¬ I ⊆ modifiedTrajectory D S events n) ∧
      ∀ j < n, I ⊆ modifiedTrajectory D S events j := by
  simp [exitTime, ExtendedRecoveryTime.time_eq_nat_iff]

theorem exitTime_eq_top_iff (D S I : Finset Site) (events : Nat → Event) :
    exitTime D S I events = ⊤ ↔ ∀ n, I ⊆ modifiedTrajectory D S events n := by
  simp [exitTime, ExtendedRecoveryTime.time_eq_top_iff]

theorem rawRecoveryIndex_le_nat_iff (E T : Finset Site) (events : Nat → Event) (n : Nat) :
    rawRecoveryIndex E T events ≤ (n : ℕ∞) ↔
      ∃ j ≤ n, rawTrajectory E T events j = ∅ :=
  ExtendedRecoveryTime.time_le_nat_iff _ _ _ _

theorem inner_missing_of_raw_empty {D E S T I : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (hI : I.Nonempty)
    (events : Nat → Event) (n : Nat) (hempty : rawTrajectory E T events n = ∅) :
    ¬ I ⊆ modifiedTrajectory D S events n := by
  intro hIin
  obtain ⟨v, hv⟩ := hI
  have hmem := modifiedTrajectory_subset_rawTrajectory hDE hSD hST events n (hIin hv)
  simp [hempty] at hmem

theorem exitTime_le_of_raw_empty {D E S T I : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (hI : I.Nonempty)
    (events : Nat → Event) (n : Nat) (hempty : rawTrajectory E T events n = ∅) :
    exitTime D S I events ≤ (n : ℕ∞) :=
  (exitTime_le_nat_iff D S I events n).mpr
    ⟨n, le_rfl, inner_missing_of_raw_empty hDE hSD hST hI events n hempty⟩

theorem exitTime_le_rawRecoveryIndex {D E S T I : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (hI : I.Nonempty)
    (events : Nat → Event) :
    exitTime D S I events ≤ rawRecoveryIndex E T events := by
  cases ht : rawRecoveryIndex E T events using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
      have hle : rawRecoveryIndex E T events ≤ (n : ℕ∞) := by rw [ht]
      obtain ⟨j, hjn, hj⟩ := (rawRecoveryIndex_le_nat_iff E T events n).mp hle
      exact le_trans (exitTime_le_of_raw_empty hDE hSD hST hI events j hj)
        (ENat.natCast_le_natCast.mpr hjn)

theorem recovery_event_subset_exit_event {D E S T I : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (hI : I.Nonempty) (n : Nat) :
    {events : Nat → Event | rawRecoveryIndex E T events ≤ (n : ℕ∞)} ⊆
      {events | exitTime D S I events ≤ (n : ℕ∞)} := by
  intro events he
  exact le_trans (exitTime_le_rawRecoveryIndex hDE hSD hST hI events) he

theorem exit_survival_event_subset_recovery_survival_event {D E S T I : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T) (hI : I.Nonempty) (n : Nat) :
    {events : Nat → Event | (n : ℕ∞) < exitTime D S I events} ⊆
      {events | (n : ℕ∞) < rawRecoveryIndex E T events} := by
  intro events he
  exact lt_of_lt_of_le he (exitTime_le_rawRecoveryIndex hDE hSD hST hI events)

/-- Freeze at the first missing-protected-set event; infinity means no freezing. -/
def stoppedTrajectory (D S I : Finset Site) (events : Nat → Event) (n : Nat) : Finset Site :=
  if exitTime D S I events ≤ (n : ℕ∞) then
    modifiedTrajectory D S events (exitTime D S I events).toNat
  else modifiedTrajectory D S events n

theorem stoppedTrajectory_before_exit (D S I : Finset Site) (events : Nat → Event)
    (n : Nat) (hn : (n : ℕ∞) < exitTime D S I events) :
    stoppedTrajectory D S I events n = modifiedTrajectory D S events n := by
  simp only [stoppedTrajectory, ite_eq_right (not_le_of_gt hn)]

theorem stoppedTrajectory_after_exit (D S I : Finset Site) (events : Nat → Event)
    (j n : Nat) (hj : exitTime D S I events = (j : ℕ∞)) (hjn : j ≤ n) :
    stoppedTrajectory D S I events n = modifiedTrajectory D S events j := by
  simp [stoppedTrajectory, hj, hjn]

theorem stoppedTrajectory_frozen (D S I : Finset Site) (events : Nat → Event)
    (j n m : Nat) (hj : exitTime D S I events = (j : ℕ∞)) (hjn : j ≤ n) (hjm : j ≤ m) :
    stoppedTrajectory D S I events n = stoppedTrajectory D S I events m := by
  rw [stoppedTrajectory_after_exit D S I events j n hj hjn,
    stoppedTrajectory_after_exit D S I events j m hj hjm]

theorem stoppedTrajectory_inner_missing_after_exit (D S I : Finset Site)
    (events : Nat → Event) (j n : Nat)
    (hj : exitTime D S I events = (j : ℕ∞)) (hjn : j ≤ n) :
    ¬ I ⊆ stoppedTrajectory D S I events n := by
  rw [stoppedTrajectory_after_exit D S I events j n hj hjn]
  exact ((exitTime_eq_nat_iff D S I events j).mp hj).1

theorem stoppedTrajectory_subset_rawTrajectory_before_exit {D E S T I : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T)
    (events : Nat → Event) (n : Nat) (hn : (n : ℕ∞) < exitTime D S I events) :
    stoppedTrajectory D S I events n ⊆ rawTrajectory E T events n := by
  rw [stoppedTrajectory_before_exit D S I events n hn]
  exact modifiedTrajectory_subset_rawTrajectory hDE hSD hST events n

end MathResearchAnalysis.DropletDomainComparison

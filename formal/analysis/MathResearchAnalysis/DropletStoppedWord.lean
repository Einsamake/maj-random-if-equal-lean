module
public import MathResearchAnalysis.DropletDomainComparison
public import Mathlib.Data.List.GetD
set_option autoImplicit false
/-! Actual first-loss freezing, with possible infinite exit retained. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.DropletStoppedWord
open InfiniteGridModel (Site)
open DropletModifiedWord (Event modifiedStep modifiedWord)
open DropletDomainComparison

def stoppedStep (D I S : Finset Site) (e : Event) : Finset Site :=
  if I ⊆ S then modifiedStep D S e.1 e.2 else S

def stoppedWord (D I S : Finset Site) : List Event → Finset Site
  | [] => S
  | e :: w => stoppedWord D I (stoppedStep D I S e) w

@[simp] theorem stoppedWord_nil (D I S : Finset Site) : stoppedWord D I S [] = S := rfl

theorem stoppedWord_cons (D I S : Finset Site) (e : Event) (w : List Event) :
    stoppedWord D I S (e::w) = stoppedWord D I (stoppedStep D I S e) w := rfl

theorem stoppedWord_append (D I S : Finset Site) (w u : List Event) :
    stoppedWord D I S (w++u) = stoppedWord D I (stoppedWord D I S w) u := by
  induction w generalizing S with
  | nil => rfl
  | cons e w ih => exact ih (stoppedStep D I S e)

theorem stoppedWord_of_missing {D I S : Finset Site} (h : ¬ I ⊆ S) (w : List Event) :
    stoppedWord D I S w = S := by
  induction w with
  | nil => rfl
  | cons e w ih => simpa only [stoppedWord,stoppedStep,ite_eq_right h] using ih

theorem stoppedTrajectory_protected_iff (D S I : Finset Site) (events : Nat → Event) (n : Nat) :
    I ⊆ stoppedTrajectory D S I events n ↔ (n : ℕ∞) < exitTime D S I events := by
  constructor
  · intro h
    by_contra hn
    have hle := le_of_not_gt hn
    have hfin : exitTime D S I events ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hle
    have he := (ENat.natCast_toNat hfin).symm
    have hm := ((exitTime_eq_nat_iff D S I events _).mp he).1
    unfold stoppedTrajectory at h
    rw [ite_eq_left hle] at h
    exact hm h
  · intro hn
    rw [stoppedTrajectory_before_exit D S I events n hn]
    by_contra h
    exact (not_le_of_gt hn) ((exitTime_le_nat_iff D S I events n).mpr ⟨n,le_rfl,h⟩)

theorem stoppedTrajectory_eq_of_le (D S I : Finset Site) (events : Nat → Event) (n : Nat)
    (hn : (n : ℕ∞) ≤ exitTime D S I events) :
    stoppedTrajectory D S I events n = modifiedTrajectory D S events n := by
  by_cases h : exitTime D S I events ≤ (n : ℕ∞)
  · have he := le_antisymm h hn
    simpa only [he,ENat.toNat_natCast] using stoppedTrajectory_after_exit D S I events n n he le_rfl
  · exact stoppedTrajectory_before_exit D S I events n (lt_of_not_ge h)

@[simp] theorem stoppedTrajectory_zero (D S I : Finset Site) (events : Nat → Event) :
    stoppedTrajectory D S I events 0 = S := by
  simpa only [modifiedTrajectory_zero] using stoppedTrajectory_eq_of_le D S I events 0 zero_le

theorem stoppedTrajectory_succ (D S I : Finset Site) (events : Nat → Event) (n : Nat) :
    stoppedTrajectory D S I events (n+1) = stoppedStep D I (stoppedTrajectory D S I events n) (events n) := by
  unfold stoppedStep
  split_ifs with hkeep
  · have hn := (stoppedTrajectory_protected_iff D S I events n).mp hkeep
    have hn1 : ((n+1 : Nat) : ℕ∞) ≤ exitTime D S I events := by
      cases he : exitTime D S I events using ENat.recTopCoe with
      | top => simp
      | coe j =>
        have hj : n < j := by simpa only [he,ENat.natCast_lt_natCast] using hn
        exact_mod_cast (show n+1 ≤ j by omega)
    rw [stoppedTrajectory_eq_of_le D S I events (n+1) hn1,
      stoppedTrajectory_before_exit D S I events n hn,modifiedTrajectory_succ]
  · have hle : exitTime D S I events ≤ (n : ℕ∞) :=
      le_of_not_gt (fun hn => hkeep ((stoppedTrajectory_protected_iff D S I events n).mpr hn))
    cases he : exitTime D S I events using ENat.recTopCoe with
    | top => simp only [he,top_le_iff,ENat.natCast_ne_top] at hle
    | coe j =>
      have hj : j ≤ n := by simpa only [he,ENat.natCast_le_natCast] using hle
      rw [stoppedTrajectory_after_exit D S I events j (n+1) he (by omega),
        stoppedTrajectory_after_exit D S I events j n he hj]

theorem stoppedWord_prefix_eq (D I S : Finset Site) (events : Nat → Event) (n : Nat) :
    stoppedWord D I S (eventPrefix events n) = stoppedTrajectory D S I events n := by
  induction n with
  | zero => simp only [eventPrefix_zero,stoppedWord_nil,stoppedTrajectory_zero]
  | succ n ih =>
    rw [eventPrefix_succ,stoppedWord_append,ih,stoppedWord,stoppedWord,stoppedTrajectory_succ]

theorem eventPrefix_getD (w : List Event) (fallback : Event) :
    eventPrefix (fun n => w.getD n fallback) w.length = w := by
  apply List.ext_getElem
  · simp [eventPrefix]
  · intro i hi1 hi2
    simp only [eventPrefix,List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem _ _ hi2

theorem stoppedWord_eq_stoppedTrajectory (D I S : Finset Site) (w : List Event) (fallback : Event) :
    stoppedWord D I S w = stoppedTrajectory D S I (fun n => w.getD n fallback) w.length := by
  rw [← stoppedWord_prefix_eq,eventPrefix_getD]

theorem eventPrefix_getD_take (w : List Event) (fallback : Event) (k : Nat) (hk : k ≤ w.length) :
    eventPrefix (fun n => w.getD n fallback) k = w.take k := by
  apply List.ext_getElem
  · simpa [eventPrefix,List.length_take] using (Nat.min_eq_left hk).symm
  · intro i hi1 hi2
    simp only [eventPrefix,List.getElem_map,List.getElem_range,List.getElem_take]
    exact List.getD_eq_getElem _ _ (lt_of_lt_of_le (by simpa [eventPrefix] using hi1) hk)

theorem stoppedWord_protected_iff (D I S : Finset Site) (w : List Event) :
    I ⊆ stoppedWord D I S w ↔ ∀ k ≤ w.length, I ⊆ modifiedWord D S (w.take k) := by
  let fallback : Event := ((0,0),false)
  let events : Nat → Event := fun n => w.getD n fallback
  rw [stoppedWord_eq_stoppedTrajectory D I S w fallback,stoppedTrajectory_protected_iff]
  constructor
  · intro hn k hk
    by_contra hm
    have hbad : ¬ I ⊆ modifiedTrajectory D S events k := by
      simpa only [modifiedTrajectory,events,eventPrefix_getD_take w fallback k hk] using hm
    exact (not_le_of_gt hn) ((exitTime_le_nat_iff D S I events w.length).mpr ⟨k,hk,hbad⟩)
  · intro h
    by_contra hn
    obtain ⟨k,hk,hm⟩ := (exitTime_le_nat_iff D S I events w.length).mp (le_of_not_gt hn)
    apply hm
    simpa only [modifiedTrajectory,events,eventPrefix_getD_take w fallback k hk] using h k hk

theorem stoppedWord_missing_iff (D I S : Finset Site) (w : List Event) :
    (¬ I ⊆ stoppedWord D I S w) ↔ ∃ k ≤ w.length, ¬ I ⊆ modifiedWord D S (w.take k) := by
  rw [stoppedWord_protected_iff]
  push Not
  rfl

end MathResearchAnalysis.DropletStoppedWord

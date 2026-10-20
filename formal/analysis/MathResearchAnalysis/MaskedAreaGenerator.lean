module
public import MathResearchAnalysis.ObservedFrozenProcess
public import MathResearchAnalysis.GridPerimeterDynamics
set_option autoImplicit false
/-! Exact finite rate algebra for the actual masked, cleaned and first-loss frozen update. No compensator or physical-time expectation formula is assumed here. Births are counted only inside the actual mask. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MaskedAreaGenerator
open InfiniteGridModel (Site)
open DropletModifiedWord (rawStep modifiedStep localRule)
open DropletStoppedWord (stoppedStep)
open GridMajorityPeeling (degree4)
open scoped BigOperators

def frozenGenerator (D I S : Finset Site) (f : Finset Site → Real) : Real :=
  ∑ v ∈ D, ((f (stoppedStep D I S (v,false)) + f (stoppedStep D I S (v,true))) / 2 - f S)

def rawAreaRate (D S : Finset Site) : Real :=
  ∑ v ∈ D, (((S.card : Real) - (rawStep S v false).card) +
    ((S.card : Real) - (rawStep S v true).card)) / 2

def cleanupRate (D S : Finset Site) : Real :=
  ∑ v ∈ D, ((GridPerimeterDynamics.eventLoss D S (v,false) : Real) +
    (GridPerimeterDynamics.eventLoss D S (v,true) : Real)) / 2

theorem frozenGenerator_of_missing (D I S : Finset Site) (f : Finset Site → Real)
    (h : ¬ I ⊆ S) : frozenGenerator D I S f = 0 := by
  unfold frozenGenerator
  apply Finset.sum_eq_zero
  intro v _
  simp only [stoppedStep,ite_eq_right h]
  ring

theorem modified_card_diff (D S : Finset Site) (v : Site) (b : Bool) (hv : v ∈ D) :
    (S.card : Real) - (modifiedStep D S v b).card =
      ((S.card : Real) - (rawStep S v b).card) + GridPerimeterDynamics.eventLoss D S (v,b) := by
  have hs := Finset.card_le_card (DropletModifiedWord.modifiedStep_subset_maskedRawStep D S v b)
  have hl : (GridPerimeterDynamics.eventLoss D S (v,b) : Real) =
      (DropletModifiedWord.maskedRawStep D S v b).card - (modifiedStep D S v b).card := by
    rw [GridPerimeterDynamics.eventLoss,Nat.cast_sub hs]
  rw [hl,DropletModifiedWord.maskedRawStep,ite_eq_left hv]
  ring

theorem frozen_area_generator (D I S : Finset Site) (h : I ⊆ S) :
    frozenGenerator D I S (fun T => -(T.card : Real)) = rawAreaRate D S + cleanupRate D S := by
  unfold frozenGenerator rawAreaRate cleanupRate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [stoppedStep,ite_eq_left h]
  have hf := modified_card_diff D S v false hv
  have ht := modified_card_diff D S v true hv
  linarith

theorem cleanupRate_nonnegative (D S : Finset Site) : 0 ≤ cleanupRate D S := by
  apply Finset.sum_nonneg
  intro v _
  positivity

theorem raw_card_diff (S : Finset Site) (v : Site) (b : Bool) :
    (S.card : Real) - (rawStep S v b).card =
      if localRule S v b then (if v ∈ S then 0 else -1) else (if v ∈ S then 1 else 0) := by
  cases hb : localRule S v b <;> by_cases hv : v ∈ S
  · have hc : ((S.erase v).card : Real) + 1 = S.card := by exact_mod_cast Finset.card_erase_add_one hv
    simp only [rawStep,hb,Bool.false_eq_true,ite_false,ite_eq_left hv]
    linarith
  · simp [rawStep,hb,hv]
  · simp [rawStep,hb,hv]
  · simp [rawStep,hb,hv]

theorem raw_local_rate (S : Finset Site) (v : Site) :
    (((S.card : Real) - (rawStep S v false).card) +
      ((S.card : Real) - (rawStep S v true).card)) / 2 =
    if v ∈ S then (if degree4 S v < 2 then 1 else if degree4 S v = 2 then 1/2 else 0)
      else (if 2 < degree4 S v then -1 else if degree4 S v = 2 then -1/2 else 0) := by
  rw [raw_card_diff,raw_card_diff]
  have hd := GridMajorityPeeling.degree4_eq_four_inputs S v
  by_cases hlo : degree4 S v < 2
  · have hhi : ¬ 2 < degree4 S v := by omega
    have he : degree4 S v ≠ 2 := by omega
    by_cases hv : v ∈ S <;>
      simp [localRule,InfiniteGridModel.majority4,← hd,hlo,hhi,he,hv]
  · by_cases hhi : 2 < degree4 S v
    · have he : degree4 S v ≠ 2 := by omega
      by_cases hv : v ∈ S <;>
        simp [localRule,InfiniteGridModel.majority4,← hd,hlo,hhi,he,hv]
    · have he : degree4 S v = 2 := by omega
      by_cases hv : v ∈ S <;>
        simp [localRule,InfiniteGridModel.majority4,← hd,he,hv]

theorem rawAreaRate_exact (D S : Finset Site) :
    rawAreaRate D S = ∑ v ∈ D,
      if v ∈ S then (if degree4 S v < 2 then 1 else if degree4 S v = 2 then 1/2 else 0)
        else (if 2 < degree4 S v then -1 else if degree4 S v = 2 then -1/2 else 0) := by
  exact Finset.sum_congr rfl (fun v _ => raw_local_rate S v)

theorem frozen_area_generator_exact (D I S : Finset Site) :
    frozenGenerator D I S (fun T => -(T.card : Real)) =
      if I ⊆ S then rawAreaRate D S + cleanupRate D S else 0 := by
  by_cases h : I ⊆ S
  · rw [ite_eq_left h]
    exact frozen_area_generator D I S h
  · rw [ite_eq_right h]
    exact frozenGenerator_of_missing D I S _ h
theorem sum_indicator_card (D : Finset Site) (P : Site → Prop) [DecidablePred P] :
    (∑ v ∈ D, if P v then (1 : Real) else 0) = ((D.filter P).card : Real) := by
  symm
  rw [Finset.card_eq_sum_ones,Nat.cast_sum,Finset.sum_filter]
  simp only [Nat.cast_one]

theorem rawAreaRate_counts (D S : Finset Site) :
    rawAreaRate D S = ((D.filter (fun v => v ∈ S ∧ degree4 S v < 2)).card : Real) +
      ((D.filter (fun v => v ∈ S ∧ degree4 S v = 2)).card : Real) / 2 -
      ((D.filter (fun v => v ∉ S ∧ 2 < degree4 S v)).card : Real) -
      ((D.filter (fun v => v ∉ S ∧ degree4 S v = 2)).card : Real) / 2 := by
  classical
  calc
    rawAreaRate D S = ∑ v ∈ D,
        ((if v ∈ S ∧ degree4 S v < 2 then (1 : Real) else 0) +
        (if v ∈ S ∧ degree4 S v = 2 then (1 : Real) else 0) / 2 -
        (if v ∉ S ∧ 2 < degree4 S v then (1 : Real) else 0) -
        (if v ∉ S ∧ degree4 S v = 2 then (1 : Real) else 0) / 2) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [raw_local_rate]
      by_cases hlo : degree4 S v < 2
      · have hhi : ¬ 2 < degree4 S v := by omega
        have he : degree4 S v ≠ 2 := by omega
        by_cases hv : v ∈ S <;> simp [hv,hlo,hhi,he]
      · by_cases hhi : 2 < degree4 S v
        · have he : degree4 S v ≠ 2 := by omega
          by_cases hv : v ∈ S <;> simp [hv,hlo,hhi,he]
        · have he : degree4 S v = 2 := by omega
          by_cases hv : v ∈ S <;> norm_num [hv,he]
    _ = _ := by
      simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_div,sum_indicator_card]

def birthIntensity (S : Finset Site) (v : Site) : Real :=
  if 2 < degree4 S v then 1 else if degree4 S v = 2 then 1/2 else 0

theorem birthIntensity_nonnegative (S : Finset Site) (v : Site) : 0 ≤ birthIntensity S v := by
  unfold birthIntensity
  split_ifs <;> norm_num

theorem rawAreaRate_mask_correction {D E S : Finset Site} (hDE : D ⊆ E) (hSD : S ⊆ D) :
    rawAreaRate D S = rawAreaRate E S + ∑ v ∈ E \ D, birthIntensity S v := by
  let f : Site → Real := fun v => (((S.card : Real) - (rawStep S v false).card) +
    ((S.card : Real) - (rawStep S v true).card)) / 2
  have hsum : (∑ v ∈ E \ D, f v) + (∑ v ∈ D, f v) = ∑ v ∈ E, f v := Finset.sum_sdiff hDE
  have houtside : (∑ v ∈ E \ D, f v) = -(∑ v ∈ E \ D, birthIntensity S v) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    have hvS : v ∉ S := fun hs => (Finset.mem_sdiff.mp hv).2 (hSD hs)
    change (((S.card : Real) - (rawStep S v false).card) +
      ((S.card : Real) - (rawStep S v true).card)) / 2 = _
    rw [raw_local_rate,ite_eq_right hvS]
    unfold birthIntensity
    split_ifs <;> ring
  change (∑ v ∈ D, f v) = (∑ v ∈ E, f v) + _
  linarith

theorem rawAreaRate_antitone_mask {D E S : Finset Site} (hDE : D ⊆ E) (hSD : S ⊆ D) :
    rawAreaRate E S ≤ rawAreaRate D S := by
  rw [rawAreaRate_mask_correction hDE hSD]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun v _ => birthIntensity_nonnegative S v)
end MathResearchAnalysis.MaskedAreaGenerator

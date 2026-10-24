module

public import MathResearchAnalysis.MaskedAreaGenerator
public import MathResearchAnalysis.ClippedSquareCoordinates

set_option autoImplicit false

/-!
# The actual forbidden-birth layer and a vanishing boundary weight

For a state inside the clipped domain, a point outside the mask can have two
occupied neighbours only on the next diamond layer. A linearly decreasing
weight therefore cancels the exact masked-versus-expanded raw update term.
No bound on weighted contour drift or a recovery-time estimate is assumed.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ForbiddenBirthControl

open InfiniteGridModel (Site north east south west)
open GridMajorityPeeling (state degree4)
open ClippedDiamondGeometry (clippedDomain)
open scoped BigOperators

def weight (L : Nat) (v : Site) : Real :=
  (L : Real) + 2 - (|v.1| + |v.2| : Int)

theorem occupied_coordinate_bounds {L : Nat} {S : Finset Site}
    (hSD : S ⊆ clippedDomain L) {v : Site} (hv : v ∈ S) :
    |v.1| ≤ (L : Int) ∧ |v.2| ≤ (L : Int) ∧ |v.1| + |v.2| ≤ (L : Int) + 1 :=
  (ClippedDiamondGeometry.mem_clippedDomain L v).mp (hSD hv)

theorem two_neighbours_in_centered_square {L : Nat} {S : Finset Site}
    (hSD : S ⊆ clippedDomain L) (v : Site) (hd : 2 ≤ degree4 S v) :
    |v.1| ≤ (L : Int) ∧ |v.2| ≤ (L : Int) := by
  rcases v with ⟨x,y⟩
  have hb : ∀ z ∈ S, -(L : Int) ≤ z.1 ∧ z.1 ≤ (L : Int) ∧
      -(L : Int) ≤ z.2 ∧ z.2 ≤ (L : Int) := by
    intro z hz
    have h := occupied_coordinate_bounds hSD hz
    have hx := (abs_le.mp h.1)
    have hy := (abs_le.mp h.2.1)
    exact ⟨hx.1,hx.2,hy.1,hy.2⟩
  have hx : -(L : Int) ≤ x ∧ x ≤ (L : Int) := by
    constructor
    · by_contra hh
      have hn : north (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change -(L : Int) ≤ x ∧ _ at h; omega
      have hs : south (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change -(L : Int) ≤ x ∧ _ at h; omega
      have hw : west (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change -(L : Int) ≤ x-1 ∧ _ at h; omega
      rw [GridMajorityPeeling.degree4_eq_four_inputs] at hd
      by_cases he : east (x,y) ∈ S <;> simp [state,hn,hs,hw,he] at hd
    · by_contra hh
      have hn : north (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change _ ∧ x ≤ (L : Int) ∧ _ at h; omega
      have hs : south (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change _ ∧ x ≤ (L : Int) ∧ _ at h; omega
      have he : east (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change _ ∧ x+1 ≤ (L : Int) ∧ _ at h; omega
      rw [GridMajorityPeeling.degree4_eq_four_inputs] at hd
      by_cases hw : west (x,y) ∈ S <;> simp [state,hn,hs,he,hw] at hd
  have hy : -(L : Int) ≤ y ∧ y ≤ (L : Int) := by
    constructor
    · by_contra hh
      have he : east (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change _ ∧ _ ∧ -(L : Int) ≤ y ∧ _ at h; omega
      have hw : west (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change _ ∧ _ ∧ -(L : Int) ≤ y ∧ _ at h; omega
      have hs : south (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change _ ∧ _ ∧ -(L : Int) ≤ y-1 ∧ _ at h; omega
      rw [GridMajorityPeeling.degree4_eq_four_inputs] at hd
      by_cases hn : north (x,y) ∈ S <;> simp [state,hn,hs,he,hw] at hd
    · by_contra hh
      have he : east (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change _ ∧ _ ∧ _ ∧ y ≤ (L : Int) at h; omega
      have hw : west (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change _ ∧ _ ∧ _ ∧ y ≤ (L : Int) at h; omega
      have hn : north (x,y) ∉ S := by
        intro hz; have h := hb _ hz; change _ ∧ _ ∧ _ ∧ y+1 ≤ (L : Int) at h; omega
      rw [GridMajorityPeeling.degree4_eq_four_inputs] at hd
      by_cases hs : south (x,y) ∈ S <;> simp [state,hn,hs,he,hw] at hd
  exact ⟨abs_le.mpr hx,abs_le.mpr hy⟩

theorem positive_degree_diamond_bound {L : Nat} {S : Finset Site}
    (hSD : S ⊆ clippedDomain L) (v : Site) (hd : 0 < degree4 S v) :
    |v.1| + |v.2| ≤ (L : Int) + 2 := by
  have hn : (GridMajorityPeeling.neighbors4 v ∩ S).Nonempty := Finset.card_pos.mp hd
  obtain ⟨u,hu⟩ := hn
  have hs := (occupied_coordinate_bounds hSD (Finset.mem_inter.mp hu).2).2.2
  have hdir := (GridMajorityPeeling.mem_neighbors4 v u).mp (Finset.mem_inter.mp hu).1
  rcases v with ⟨x,y⟩
  change |x| + |y| ≤ (L : Int) + 2
  rcases hdir with h | h | h | h
  · subst u
    change |x| + |y+1| ≤ (L : Int)+1 at hs
    have h := abs_add_le (y+1) (-1 : Int)
    norm_num at h
    omega
  · subst u
    change |x+1| + |y| ≤ (L : Int)+1 at hs
    have h := abs_add_le (x+1) (-1 : Int)
    norm_num at h
    omega
  · subst u
    change |x| + |y-1| ≤ (L : Int)+1 at hs
    have h := abs_add_le (y-1) (1 : Int)
    norm_num at h
    omega
  · subst u
    change |x-1| + |y| ≤ (L : Int)+1 at hs
    have h := abs_add_le (x-1) (1 : Int)
    norm_num at h
    omega

theorem outside_birth_layer {L : Nat} {S : Finset Site}
    (hSD : S ⊆ clippedDomain L) (v : Site) (hv : v ∉ clippedDomain L)
    (hd : 2 ≤ degree4 S v) : |v.1| + |v.2| = (L : Int) + 2 := by
  have hb := two_neighbours_in_centered_square hSD v hd
  have hu := positive_degree_diamond_bound hSD v (by omega)
  have hl : ¬ (|v.1| + |v.2| ≤ (L : Int) + 1) := by
    intro hh
    exact hv ((ClippedDiamondGeometry.mem_clippedDomain L v).mpr ⟨hb.1,hb.2,hh⟩)
  omega

theorem weight_nonnegative_on_domain (L : Nat) (v : Site) (hv : v ∈ clippedDomain L) :
    1 ≤ weight L v := by
  have h := ((ClippedDiamondGeometry.mem_clippedDomain L v).mp hv).2.2
  have hh : ((|v.1| + |v.2| : Int) : Real) ≤ (L : Real) + 1 := by exact_mod_cast h
  unfold weight
  linarith

theorem weight_zero_at_outside_birth {L : Nat} {S : Finset Site}
    (hSD : S ⊆ clippedDomain L) (v : Site) (hv : v ∉ clippedDomain L)
    (hd : 2 ≤ degree4 S v) : weight L v = 0 := by
  have h := outside_birth_layer hSD v hv hd
  unfold weight
  rw [h]
  push_cast
  ring

theorem weighted_forbidden_birth_zero {L : Nat} {S : Finset Site}
    (hSD : S ⊆ clippedDomain L) (v : Site) (hv : v ∉ clippedDomain L) :
    weight L v * MaskedAreaGenerator.birthIntensity S v = 0 := by
  by_cases hd : 2 ≤ degree4 S v
  · rw [weight_zero_at_outside_birth hSD v hv hd,zero_mul]
  · have hlt : degree4 S v < 2 := by omega
    have hne : degree4 S v ≠ 2 := by omega
    simp [MaskedAreaGenerator.birthIntensity,show ¬ 2 < degree4 S v by omega,hne]


def mass (w : Site → Real) (S : Finset Site) : Real := ∑ v ∈ S, w v

def rawWeightedRate (w : Site → Real) (D S : Finset Site) : Real :=
  ∑ v ∈ D, (((mass w S - mass w (DropletModifiedWord.rawStep S v false)) +
    (mass w S - mass w (DropletModifiedWord.rawStep S v true))) / 2)

theorem mass_rawStep_diff (w : Site → Real) (S : Finset Site) (v : Site) (b : Bool) :
    mass w S - mass w (DropletModifiedWord.rawStep S v b) =
      w v * ((S.card : Real) - (DropletModifiedWord.rawStep S v b).card) := by
  rw [MaskedAreaGenerator.raw_card_diff]
  cases hb : DropletModifiedWord.localRule S v b <;> by_cases hv : v ∈ S
  · have hc : mass w (S.erase v) + w v = mass w S := by
      exact Finset.sum_erase_add S w hv
    simp only [DropletModifiedWord.rawStep,hb,Bool.false_eq_true,ite_false,ite_eq_left hv]
    linarith
  · simp [mass,DropletModifiedWord.rawStep,hb,hv]
  · simp [mass,DropletModifiedWord.rawStep,hb,hv]
  · simp [mass,DropletModifiedWord.rawStep,hb,hv]

theorem rawWeightedRate_local (w : Site → Real) (S : Finset Site) (v : Site) :
    ((mass w S - mass w (DropletModifiedWord.rawStep S v false)) +
      (mass w S - mass w (DropletModifiedWord.rawStep S v true))) / 2 =
    w v * ((((S.card : Real) - (DropletModifiedWord.rawStep S v false).card) +
      ((S.card : Real) - (DropletModifiedWord.rawStep S v true).card)) / 2) := by
  rw [mass_rawStep_diff,mass_rawStep_diff]
  ring

theorem rawWeightedRate_mask_correction (w : Site → Real) {D E S : Finset Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) :
    rawWeightedRate w D S = rawWeightedRate w E S +
      ∑ v ∈ E \ D, w v * MaskedAreaGenerator.birthIntensity S v := by
  let f : Site → Real := fun v =>
    ((mass w S - mass w (DropletModifiedWord.rawStep S v false)) +
      (mass w S - mass w (DropletModifiedWord.rawStep S v true))) / 2
  have hsum : (∑ v ∈ E \ D, f v) + (∑ v ∈ D, f v) = ∑ v ∈ E, f v := Finset.sum_sdiff hDE
  have houtside : (∑ v ∈ E \ D, f v) = -(∑ v ∈ E \ D, w v * MaskedAreaGenerator.birthIntensity S v) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    have hvS : v ∉ S := fun hs => (Finset.mem_sdiff.mp hv).2 (hSD hs)
    change ((mass w S - mass w (DropletModifiedWord.rawStep S v false)) +
      (mass w S - mass w (DropletModifiedWord.rawStep S v true))) / 2 = _
    rw [rawWeightedRate_local,MaskedAreaGenerator.raw_local_rate,ite_eq_right hvS]
    unfold MaskedAreaGenerator.birthIntensity
    split_ifs <;> ring
  change (∑ v ∈ D, f v) = (∑ v ∈ E, f v) + _
  linarith

theorem clipped_rawWeightedRate_eq_expanded {L : Nat} {E S : Finset Site}
    (hDE : clippedDomain L ⊆ E) (hSD : S ⊆ clippedDomain L) :
    rawWeightedRate (weight L) (clippedDomain L) S = rawWeightedRate (weight L) E S := by
  rw [rawWeightedRate_mask_correction (weight L) hDE hSD]
  have hz : (∑ v ∈ E \ clippedDomain L, weight L v * MaskedAreaGenerator.birthIntensity S v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact weighted_forbidden_birth_zero hSD v (Finset.mem_sdiff.mp hv).2
  rw [hz,add_zero]

theorem actual_rawWeightedRate_eq_square {L : Nat} (hL : 1 ≤ L) {S : Finset Site}
    (hSD : S ⊆ clippedDomain L) :
    rawWeightedRate (weight L) (clippedDomain L) S =
      rawWeightedRate (weight L) (ClippedSquareCoordinates.centeredSites L) S :=
  clipped_rawWeightedRate_eq_expanded
    (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) hSD

theorem weight_upper_bound (L : Nat) (v : Site) : weight L v ≤ (L : Real) + 2 := by
  have h : 0 ≤ ((|v.1| + |v.2| : Int) : Real) := by positivity
  unfold weight
  linarith

end MathResearchAnalysis.ForbiddenBirthControl

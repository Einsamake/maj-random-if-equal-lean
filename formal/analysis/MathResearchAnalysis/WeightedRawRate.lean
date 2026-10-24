module
public import MathResearchAnalysis.WeightedRawContour
public import MathResearchAnalysis.WeightedReflection
set_option autoImplicit false
/-! Four actual reflected corner/valley charges account for the entire weighted
raw rate. Protected convex geometry supplies the local exclusions; no rate or
four-direction identity is assumed. The resulting O(L) bound is deterministic
for actual supported protected shapes, not yet a physical recovery theorem. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.WeightedRawRate
open InfiniteGridModel (Site north east south west)
open OrthogonalGridConvexity
open ClippedDiamondGeometry (clippedDomain reflect)
open ClippedProtectedGeometry (innerDiamond)
open ProtectedCornerGeometry (mirror mem_mirror)
open GridMajorityPeeling (degree4 state)
open GridCellBoundary (perimeter)
open ForbiddenBirthControl (weight mass rawWeightedRate)
open WeightedRawContour (northwestCorners northwestValleys northwestCharge)

/-- One reflected orientation, expressed at an actual grid site. -/
def northwestScore (L : Nat) (S : Finset Site) (x : Site) : Real :=
  (if x ∈ S ∧ north x ∉ S ∧ west x ∉ S then weight L x else 0) -
    (if x ∉ S ∧ east x ∈ S ∧ south x ∈ S then weight L x else 0)

def booleanScore (r : Real) (a n e s w : Bool) : Real :=
  (if a = true ∧ n = false ∧ w = false then r else 0) -
    (if a = false ∧ e = true ∧ s = true then r else 0)

def booleanRate (r : Real) (a n e s w : Bool) : Real :=
  let k := n.toNat + e.toNat + s.toNat + w.toNat
  r * (if a then (if k < 2 then 1 else if k = 2 then 1/2 else 0)
    else (if 2 < k then -1 else if k = 2 then -1/2 else 0))

/-- Exhaustive finite local classification. Geometry is supplied below, rather
than assuming the complete raw-rate identity. -/
theorem boolean_rate_eq_scores (r : Real) (a n e s w : Bool)
    (hstable : a = true → 2 ≤ n.toNat + e.toNat + s.toNat + w.toNat)
    (hhoriz : a = true → n.toNat + e.toNat + s.toNat + w.toNat = 2 →
      ¬ (e = true ∧ w = true))
    (hvert : a = true → n.toNat + e.toNat + s.toNat + w.toNat = 2 →
      ¬ (n = true ∧ s = true))
    (hvh : a = false → ¬ (e = true ∧ w = true))
    (hvv : a = false → ¬ (n = true ∧ s = true)) :
    2 * booleanRate r a n e s w =
      booleanScore r a n e s w + booleanScore r a s e n w +
      booleanScore r a n w s e + booleanScore r a s w n e := by
  cases a <;> cases n <;> cases e <;> cases s <;> cases w
  all_goals norm_num [booleanRate,booleanScore] at *
  all_goals ring

theorem northwestScore_boolean (L : Nat) (S : Finset Site) (x : Site) :
    northwestScore L S x = booleanScore (weight L x) (state S x)
      (state S (north x)) (state S (east x)) (state S (south x)) (state S (west x)) := by
  simp [northwestScore,booleanScore,state]

theorem state_mirror (horizontal vertical : Bool) (S : Finset Site) (u : Site) :
    state (mirror horizontal vertical S) u = state S (reflect horizontal vertical u) :=
  Bool.decide_congr (mem_mirror horizontal vertical S u)

theorem northwestScore_at_reflect (L : Nat) (horizontal vertical : Bool)
    (S : Finset Site) (x : Site) :
    northwestScore L (mirror horizontal vertical S) (reflect horizontal vertical x) =
      booleanScore (weight L x) (state S x)
        (if vertical then state S (south x) else state S (north x))
        (if horizontal then state S (west x) else state S (east x))
        (if vertical then state S (north x) else state S (south x))
        (if horizontal then state S (east x) else state S (west x)) := by
  have ha : state (mirror horizontal vertical S) (reflect horizontal vertical x) = state S x := by
    rw [state_mirror,ClippedDiamondGeometry.reflect_involutive horizontal vertical x]
  have hn : state (mirror horizontal vertical S) (north (reflect horizontal vertical x)) =
      (if vertical then state S (south x) else state S (north x)) := by
    rw [state_mirror]
    cases horizontal <;> cases vertical
    all_goals apply congrArg (state S)
    all_goals apply Prod.ext <;> dsimp [reflect,north,south] <;> omega
  have he : state (mirror horizontal vertical S) (east (reflect horizontal vertical x)) =
      (if horizontal then state S (west x) else state S (east x)) := by
    rw [state_mirror]
    cases horizontal <;> cases vertical
    all_goals apply congrArg (state S)
    all_goals apply Prod.ext <;> dsimp [reflect,east,west] <;> omega
  have hs : state (mirror horizontal vertical S) (south (reflect horizontal vertical x)) =
      (if vertical then state S (north x) else state S (south x)) := by
    rw [state_mirror]
    cases horizontal <;> cases vertical
    all_goals apply congrArg (state S)
    all_goals apply Prod.ext <;> dsimp [reflect,north,south] <;> omega
  have hw : state (mirror horizontal vertical S) (west (reflect horizontal vertical x)) =
      (if horizontal then state S (east x) else state S (west x)) := by
    rw [state_mirror]
    cases horizontal <;> cases vertical
    all_goals apply congrArg (state S)
    all_goals apply Prod.ext <;> dsimp [reflect,east,west] <;> omega
  rw [northwestScore_boolean,WeightedReflection.weight_reflect,ha,hn,he,hs,hw]

theorem raw_local_boolean (L : Nat) (S : Finset Site) (x : Site) :
    ((mass (weight L) S - mass (weight L) (DropletModifiedWord.rawStep S x false)) +
      (mass (weight L) S - mass (weight L) (DropletModifiedWord.rawStep S x true))) / 2 =
    booleanRate (weight L x) (state S x) (state S (north x)) (state S (east x))
      (state S (south x)) (state S (west x)) := by
  rw [ForbiddenBirthControl.rawWeightedRate_local,MaskedAreaGenerator.raw_local_rate,
    GridMajorityPeeling.degree4_eq_four_inputs]
  by_cases hx : x ∈ S <;> simp [booleanRate,state,hx]

/-- Each permitted fair-tie death or birth contributes to exactly one of the
four orientations, with its correct sign and unchanged physical weight. -/
theorem raw_local_four_orientations {L : Nat} (hL : 2 ≤ L) {S : Finset Site}
    (hshape : ProtectedEvolution.Shape S) (hI : innerDiamond L ⊆ S)
    (hSD : S ⊆ clippedDomain L) (x : Site) :
    2 * (((mass (weight L) S - mass (weight L) (DropletModifiedWord.rawStep S x false)) +
      (mass (weight L) S - mass (weight L) (DropletModifiedWord.rawStep S x true))) / 2) =
      ∑ horizontal : Bool, ∑ vertical : Bool,
        northwestScore L (mirror horizontal vertical S) (reflect horizontal vertical x) := by
  rw [raw_local_boolean]
  have hlocal :
      2 * booleanRate (weight L x) (state S x) (state S (north x)) (state S (east x))
        (state S (south x)) (state S (west x)) =
      booleanScore (weight L x) (state S x) (state S (north x)) (state S (east x))
        (state S (south x)) (state S (west x)) +
      booleanScore (weight L x) (state S x) (state S (south x)) (state S (east x))
        (state S (north x)) (state S (west x)) +
      booleanScore (weight L x) (state S x) (state S (north x)) (state S (west x))
        (state S (south x)) (state S (east x)) +
      booleanScore (weight L x) (state S x) (state S (south x)) (state S (west x))
        (state S (north x)) (state S (east x)) := by
    apply boolean_rate_eq_scores
    · intro hx
      have hxS : x ∈ S := by simpa only [state,decide_eq_true_eq] using hx
      rw [← GridMajorityPeeling.degree4_eq_four_inputs]
      exact (FiniteMajorityPeeling.stable_iff GridMajorityPeeling.neighbors4 S).mp hshape.2.2.2 x hxS
    · intro hx hd
      have hxS : x ∈ S := by simpa only [state,decide_eq_true_eq] using hx
      rw [← GridMajorityPeeling.degree4_eq_four_inputs] at hd
      simpa only [state,decide_eq_true_eq] using
        ProtectedColumnGeometry.protected_no_horizontal_opposites hL hshape.1 hshape.2.1
          hshape.2.2.2 hxS hI hSD hd
    · intro hx hd
      have hxS : x ∈ S := by simpa only [state,decide_eq_true_eq] using hx
      rw [← GridMajorityPeeling.degree4_eq_four_inputs] at hd
      simpa only [state,decide_eq_true_eq] using
        ProtectedColumnGeometry.protected_no_vertical_opposites hL hshape.1 hshape.2.1
          hshape.2.2.2 hxS hI hSD hd
    · intro hx
      have hxS : x ∉ S := by simpa only [state,decide_eq_false_iff_not] using hx
      simpa only [state,decide_eq_true_eq] using ConvexLocalUpdate.vacant_no_east_west hshape.1 hxS
    · intro hx
      have hxS : x ∉ S := by simpa only [state,decide_eq_false_iff_not] using hx
      simpa only [state,decide_eq_true_eq] using ConvexLocalUpdate.vacant_no_north_south hshape.2.1 hxS
  simpa [Fintype.sum_bool,northwestScore_at_reflect,add_assoc,add_comm,add_left_comm] using hlocal

theorem northwestCharge_eq_sum (L : Nat) {E S : Finset Site} (hSE : S ⊆ E) :
    northwestCharge L E S = ∑ x ∈ E, northwestScore L S x := by
  unfold northwestCharge northwestCorners northwestValleys northwestScore
  rw [Finset.sum_filter,Finset.sum_filter,Finset.sum_sub_distrib]
  congr 1
  calc
    _ = ∑ x ∈ S, if x ∈ S ∧ north x ∉ S ∧ west x ∉ S then weight L x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [hx,true_and]
    _ = _ := Finset.sum_subset hSE (fun x _ hx => by simp only [hx,false_and,↓reduceIte])

theorem sum_reflected_northwestScore (L : Nat) (hL : 1 ≤ L) (horizontal vertical : Bool) (S : Finset Site) :
    (∑ x ∈ ClippedSquareCoordinates.centeredSites L,
      northwestScore L (mirror horizontal vertical S) (reflect horizontal vertical x)) =
    ∑ x ∈ ClippedSquareCoordinates.centeredSites L, northwestScore L (mirror horizontal vertical S) x := by
  calc
    _ = ∑ x ∈ mirror horizontal vertical (ClippedSquareCoordinates.centeredSites L),
        northwestScore L (mirror horizontal vertical S) x := by
      unfold mirror
      rw [Finset.sum_image (ClippedDiamondGeometry.reflect_injective _ _).injOn]
    _ = _ := by rw [WeightedReflection.centeredSites_mirror L hL horizontal vertical]

/-- The actual centered square accounts for every reflected corner and valley. -/
theorem actual_raw_four_charges {L : Nat} (hL : 2 ≤ L) {S : Finset Site}
    (hshape : ProtectedEvolution.Shape S) (hI : innerDiamond L ⊆ S)
    (hSD : S ⊆ clippedDomain L) :
    2 * rawWeightedRate (weight L) (ClippedSquareCoordinates.centeredSites L) S =
      ∑ horizontal : Bool, ∑ vertical : Bool,
        northwestCharge L (ClippedSquareCoordinates.centeredSites L) (mirror horizontal vertical S) := by
  classical
  unfold rawWeightedRate
  rw [Finset.mul_sum]
  calc
    _ = ∑ x ∈ ClippedSquareCoordinates.centeredSites L, ∑ horizontal : Bool, ∑ vertical : Bool,
        northwestScore L (mirror horizontal vertical S) (reflect horizontal vertical x) :=
      Finset.sum_congr rfl (fun x _ => raw_local_four_orientations hL hshape hI hSD x)
    _ = ∑ horizontal : Bool, ∑ vertical : Bool, ∑ x ∈ ClippedSquareCoordinates.centeredSites L,
        northwestScore L (mirror horizontal vertical S) (reflect horizontal vertical x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro horizontal _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro horizontal _
      apply Finset.sum_congr rfl
      intro vertical _
      rw [sum_reflected_northwestScore L (by omega : 1 ≤ L)]
      exact (northwestCharge_eq_sum L
        ((WeightedReflection.mirror_subset_clippedDomain L horizontal vertical hSD).trans
          (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L (by omega)))).symm

/-- True interval convexity and support alone supply the physical perimeter
bound; it is not passed in as an unproved dynamical budget. -/
theorem perimeter_le_clipped_square {L : Nat} {S : Finset Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hSD : S ⊆ clippedDomain L) :
    perimeter S ≤ 8 * L + 4 := by
  have hx : S.image Prod.fst ⊆ Finset.Icc (-(L : Int)) (L : Int) := by
    intro x hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr (abs_le.mp (((ClippedDiamondGeometry.mem_clippedDomain L u).mp (hSD hu)).1))
  have hy : S.image Prod.snd ⊆ Finset.Icc (-(L : Int)) (L : Int) := by
    intro y hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_Icc.mpr (abs_le.mp (((ClippedDiamondGeometry.mem_clippedDomain L u).mp (hSD hu)).2.1))
  have hcard : (Finset.Icc (-(L : Int)) (L : Int)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  have hcx := Finset.card_le_card hx
  have hcy := Finset.card_le_card hy
  rw [hcard] at hcx hcy
  rw [OrthogonalPerimeter.perimeter_eq_projection_cards hr hc]
  omega

/-- Four proved NW charge bounds yield the complete weighted raw estimate. -/
theorem actual_raw_le_perimeter {L : Nat} (hL : 2 ≤ L) {S : Finset Site}
    (hshape : ProtectedEvolution.Shape S) (hI : innerDiamond L ⊆ S)
    (hSD : S ⊆ clippedDomain L) :
    rawWeightedRate (weight L) (ClippedSquareCoordinates.centeredSites L) S ≤
      2 * ((L : Real) + 2) + 2 * (perimeter S : Real) := by
  have hcharge (horizontal vertical : Bool) :
      northwestCharge L (ClippedSquareCoordinates.centeredSites L) (mirror horizontal vertical S) ≤
        (L : Real) + 2 + (perimeter S : Real) := by
    have hs := WeightedReflection.shape_mirror horizontal vertical hshape
    simpa only [WeightedReflection.perimeter_mirror] using
      WeightedRawContour.northwestCharge_le L (by omega) hs.2.1 hs.2.2.1
        (WeightedReflection.mirror_subset_clippedDomain L horizontal vertical hSD)
  have hsum : (∑ horizontal : Bool, ∑ vertical : Bool,
      northwestCharge L (ClippedSquareCoordinates.centeredSites L) (mirror horizontal vertical S)) ≤
      4 * ((L : Real) + 2 + (perimeter S : Real)) := by
    simp only [Fintype.sum_bool]
    linarith [hcharge false false,hcharge false true,hcharge true false,hcharge true true]
  rw [← actual_raw_four_charges hL hshape hI hSD] at hsum
  linarith

/-- A fully geometric O(L) bound for the real expanded weighted raw rate. -/
theorem actual_raw_le_linear {L : Nat} (hL : 2 ≤ L) {S : Finset Site}
    (hshape : ProtectedEvolution.Shape S) (hI : innerDiamond L ⊆ S)
    (hSD : S ⊆ clippedDomain L) :
    rawWeightedRate (weight L) (ClippedSquareCoordinates.centeredSites L) S ≤ (18 * L + 12 : Real) := by
  have h := actual_raw_le_perimeter hL hshape hI hSD
  have hp : (perimeter S : Real) ≤ 8 * (L : Real) + 4 := by
    exact_mod_cast perimeter_le_clipped_square hshape.1 hshape.2.1 hSD
  linarith

end MathResearchAnalysis.WeightedRawRate

module

public import MathResearchAnalysis.ClippedSquareCoordinates

set_option autoImplicit false

/-!
# Exact finite-to-centered transport of majority cleanup

The finite graph is the actual nonperiodic square, with the centered map at
parameter 2L-1. Cleanup is computed from the real induced four-neighbour degree.
All event-word identities are deterministic, with the identical supplied ties.
-/

@[expose] public section

namespace MathResearchAnalysis.CenteredPeelingTransport

open InfiniteGridModel




def image (L : Nat) (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))) :
    Finset Site := S.image (ClippedSquareCoordinates.recenter L)

theorem mem_image_recenter (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) :
    ClippedSquareCoordinates.recenter L v ∈ image L S ↔ v ∈ S := by
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
    have huv := ClippedSquareCoordinates.recenter_injective L he
    simpa only [huv] using hu
  · intro h
    exact Finset.mem_image.mpr ⟨v, h, rfl⟩

theorem state_image_recenter (L : Nat) (hL : 1 ≤ L)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))) :
    GridMajorityPeeling.state (image L S) =
      ClippedSquareCoordinates.recenterConfig L (GridMajorityPeeling.finiteState S) := by
  funext z
  by_cases hz : ClippedSquareCoordinates.centeredSquare L z
  · obtain ⟨v, rfl⟩ := (ClippedSquareCoordinates.exists_recenter_iff L hL z).mpr hz
    rw [ClippedSquareCoordinates.recenterConfig_at_vertex]
    simp only [GridMajorityPeeling.state, GridMajorityPeeling.finiteState, mem_image_recenter]
  · rw [ClippedSquareCoordinates.recenterConfig_outside L hL _ z hz]
    have hn : z ∉ image L S := by
      rintro hm
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hm
      exact hz (ClippedSquareCoordinates.recenter_in_square L hL v)
    simp [GridMajorityPeeling.state, hn]

theorem recenter_neighbor_iff (L : Nat)
    (v u : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) :
    ClippedSquareCoordinates.recenter L u ∈
        GridMajorityPeeling.neighbors4 (ClippedSquareCoordinates.recenter L v) ↔
      u ∈ SquareTasks.neighbors (ClippedSquareCoordinates.parameter L) v := by
  simp only [GridMajorityPeeling.mem_neighbors4, SquareTasks.mem_neighbors_iff,
    ClippedSquareCoordinates.recenter, InfiniteGridModel.north, InfiniteGridModel.east,
    InfiniteGridModel.south, InfiniteGridModel.west, Prod.mk.injEq, SquareTasks.Adjacent,
    Fin.ext_iff]
  omega

theorem neighbor_inter_image (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) :
    GridMajorityPeeling.neighbors4 (ClippedSquareCoordinates.recenter L v) ∩ image L S =
      image L (SquareTasks.neighbors (ClippedSquareCoordinates.parameter L) v ∩ S) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hn, hs⟩ := Finset.mem_inter.mp hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨u, Finset.mem_inter.mpr
      ⟨(recenter_neighbor_iff L v u).mp hn, hu⟩, rfl⟩
  · intro hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_inter.mpr
      ⟨(recenter_neighbor_iff L v u).mpr (Finset.mem_inter.mp hu).1,
        Finset.mem_image.mpr ⟨u, (Finset.mem_inter.mp hu).2, rfl⟩⟩

theorem degree4_image_recenter (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) :
    GridMajorityPeeling.degree4 (image L S) (ClippedSquareCoordinates.recenter L v) =
      FiniteMajorityPeeling.degree (SquareTasks.neighbors (ClippedSquareCoordinates.parameter L)) S v := by
  unfold GridMajorityPeeling.degree4 FiniteMajorityPeeling.degree
  rw [neighbor_inter_image]
  exact Finset.card_image_of_injective _ (ClippedSquareCoordinates.recenter_injective L)

theorem prune_image_recenter (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))) :
    FiniteMajorityPeeling.prune GridMajorityPeeling.neighbors4 (image L S) =
      image L (FiniteMajorityPeeling.prune
        (SquareTasks.neighbors (ClippedSquareCoordinates.parameter L)) S) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hs, hd⟩ := (FiniteMajorityPeeling.mem_prune _ _ _).mp hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    refine Finset.mem_image.mpr ⟨v, (FiniteMajorityPeeling.mem_prune _ _ _).mpr ⟨hv, ?_⟩, rfl⟩
    change 2 ≤ GridMajorityPeeling.degree4 _ _ at hd
    rwa [degree4_image_recenter] at hd
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hs, hd⟩ := (FiniteMajorityPeeling.mem_prune _ _ _).mp hv
    apply (FiniteMajorityPeeling.mem_prune _ _ _).mpr
    refine ⟨Finset.mem_image.mpr ⟨v, hs, rfl⟩, ?_⟩
    change 2 ≤ GridMajorityPeeling.degree4 _ _
    rwa [degree4_image_recenter]

theorem iteratePrune_image_recenter (L k : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))) :
    FiniteMajorityPeeling.iteratePrune GridMajorityPeeling.neighbors4 k (image L S) =
      image L (FiniteMajorityPeeling.iteratePrune
        (SquareTasks.neighbors (ClippedSquareCoordinates.parameter L)) k S) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [FiniteMajorityPeeling.iteratePrune_succ, ih, prune_image_recenter,
      FiniteMajorityPeeling.iteratePrune_succ]

theorem image_injective (L : Nat) : Function.Injective (image L) := by
  intro S T h
  ext v
  rw [← mem_image_recenter L S v, ← mem_image_recenter L T v, h]

theorem stable_image_recenter_iff (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))) :
    FiniteMajorityPeeling.Stable GridMajorityPeeling.neighbors4 (image L S) ↔
      FiniteMajorityPeeling.Stable
        (SquareTasks.neighbors (ClippedSquareCoordinates.parameter L)) S := by
  unfold FiniteMajorityPeeling.Stable
  rw [prune_image_recenter]
  exact (image_injective L).eq_iff

theorem delete_image_recenter (L : Nat)
    {S T : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))}
    (h : FiniteMajorityPeeling.Delete
      (SquareTasks.neighbors (ClippedSquareCoordinates.parameter L)) S T) :
    FiniteMajorityPeeling.Delete GridMajorityPeeling.neighbors4 (image L S) (image L T) := by
  obtain ⟨v, hv, hd, rfl⟩ := h
  refine ⟨ClippedSquareCoordinates.recenter L v, (mem_image_recenter L S v).mpr hv, ?_, ?_⟩
  · change GridMajorityPeeling.degree4 _ _ < 2
    rwa [degree4_image_recenter]
  · exact Finset.image_erase (ClippedSquareCoordinates.recenter_injective L) S v

theorem deletes_image_recenter (L : Nat)
    {S T : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))}
    (h : FiniteMajorityPeeling.Deletes
      (SquareTasks.neighbors (ClippedSquareCoordinates.parameter L)) S T) :
    FiniteMajorityPeeling.Deletes GridMajorityPeeling.neighbors4 (image L S) (image L T) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (delete_image_recenter L hstep)
theorem cleanup_image_recenter (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))) :
    GridMajorityPeeling.cleanup (image L S) = image L (GridMajorityPeeling.finiteCleanup S) := by
  have hc := deletes_image_recenter L (GridMajorityPeeling.finiteCleanup_reachable S)
  have hs := (stable_image_recenter_iff L (GridMajorityPeeling.finiteCleanup S)).mpr
    (FiniteMajorityPeeling.stable_core
      (SquareTasks.neighbors (ClippedSquareCoordinates.parameter L)) S)
  have ht := (FiniteMajorityPeeling.terminal_iff_stable GridMajorityPeeling.neighbors4 _).mpr hs
  exact (GridMajorityPeeling.terminal_cleanup_unique hc ht).symm

/-- The actual finite indicator of a configuration, without a support assumption. -/
def occupied {n : Nat} (g : SquareSpin.Config n) : Finset (SquareTasks.Vertex n) :=
  Finset.univ.filter (fun v => g v = true)

theorem finiteState_occupied {n : Nat} (g : SquareSpin.Config n) :
    GridMajorityPeeling.finiteState (occupied g) = g := by
  funext v
  cases h : g v <;> simp [GridMajorityPeeling.finiteState, occupied, h]

theorem occupied_finiteState {n : Nat} (S : Finset (SquareTasks.Vertex n)) :
    occupied (GridMajorityPeeling.finiteState S) = S := by
  ext v
  simp [occupied, GridMajorityPeeling.finiteState]

/-- The finite raw set is computed by the existing actual single-site update. -/
def finiteRawStep {n : Nat} (S : Finset (SquareTasks.Vertex n))
    (v : SquareTasks.Vertex n) (tie : Bool) : Finset (SquareTasks.Vertex n) :=
  occupied (SquareSpin.cellUpdate (GridMajorityPeeling.finiteState S) v tie)

theorem finiteState_finiteRawStep {n : Nat} (S : Finset (SquareTasks.Vertex n))
    (v : SquareTasks.Vertex n) (tie : Bool) :
    GridMajorityPeeling.finiteState (finiteRawStep S v tie) =
      SquareSpin.cellUpdate (GridMajorityPeeling.finiteState S) v tie :=
  finiteState_occupied _

theorem finiteRawStep_eq {n : Nat} (S : Finset (SquareTasks.Vertex n))
    (v : SquareTasks.Vertex n) (tie : Bool) :
    finiteRawStep S v tie =
      if SquareSpin.rule (GridMajorityPeeling.finiteState S) v tie then insert v S else S.erase v := by
  ext u
  by_cases hu : u = v
  · subst u
    cases hr : SquareSpin.rule (GridMajorityPeeling.finiteState S) v tie <;>
      simp [finiteRawStep, occupied, SquareSpin.cellUpdate, hr]
  · cases hr : SquareSpin.rule (GridMajorityPeeling.finiteState S) v tie <;>
      simp [finiteRawStep, occupied, SquareSpin.cellUpdate, hr, hu,
        GridMajorityPeeling.finiteState]

theorem localRule_image_recenter (L : Nat) (hL : 1 ≤ L)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) (tie : Bool) :
    DropletModifiedWord.localRule (image L S) (ClippedSquareCoordinates.recenter L v) tie =
      SquareSpin.rule (GridMajorityPeeling.finiteState S) v tie := by
  rw [DropletModifiedWord.localRule_eq_update _ _ tie 0, state_image_recenter L hL S]
  exact ClippedSquareCoordinates.update_recenterConfig L _ v tie

theorem rawStep_image_recenter (L : Nat) (hL : 1 ≤ L)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) (tie : Bool) :
    DropletModifiedWord.rawStep (image L S) (ClippedSquareCoordinates.recenter L v) tie =
      image L (finiteRawStep S v tie) := by
  rw [DropletModifiedWord.rawStep, localRule_image_recenter L hL S v tie, finiteRawStep_eq]
  cases hr : SquareSpin.rule (GridMajorityPeeling.finiteState S) v tie
  · simp only [Bool.false_eq_true, ↓reduceIte, image,
      Finset.image_erase (ClippedSquareCoordinates.recenter_injective L)]
  · simp only [↓reduceIte, image, Finset.image_insert]

/-- Outside the clipped mask the finite state is unchanged, including if unstable. -/
def finiteModifiedStep (L : Nat)
    (g : SquareSpin.Config (ClippedSquareCoordinates.parameter L))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) (tie : Bool) :
    SquareSpin.Config (ClippedSquareCoordinates.parameter L) :=
  if v ∈ ClippedSquareCoordinates.clippedVertices L then
    GridMajorityPeeling.finiteState
      (GridMajorityPeeling.finiteCleanup (occupied (SquareSpin.cellUpdate g v tie)))
  else g

def finiteModifiedSetStep (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) (tie : Bool) :
    Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) :=
  if v ∈ ClippedSquareCoordinates.clippedVertices L then
    GridMajorityPeeling.finiteCleanup (finiteRawStep S v tie) else S

theorem finiteState_finiteModifiedSetStep (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) (tie : Bool) :
    GridMajorityPeeling.finiteState (finiteModifiedSetStep L S v tie) =
      finiteModifiedStep L (GridMajorityPeeling.finiteState S) v tie := by
  unfold finiteModifiedSetStep finiteModifiedStep finiteRawStep
  split <;> rfl

theorem modifiedStep_image_recenter (L : Nat) (hL : 1 ≤ L)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) (tie : Bool) :
    DropletModifiedWord.modifiedStep (ClippedDiamondGeometry.clippedDomain L)
      (image L S) (ClippedSquareCoordinates.recenter L v) tie =
      image L (finiteModifiedSetStep L S v tie) := by
  by_cases hv : ClippedSquareCoordinates.recenter L v ∈ ClippedDiamondGeometry.clippedDomain L
  · simp only [DropletModifiedWord.modifiedStep, finiteModifiedSetStep,
      ClippedSquareCoordinates.mem_clippedVertices, hv, ite_true]
    rw [rawStep_image_recenter L hL S v tie, cleanup_image_recenter]
  · simp [DropletModifiedWord.modifiedStep, finiteModifiedSetStep,
      ClippedSquareCoordinates.mem_clippedVertices, hv]

theorem recenterConfig_finiteModifiedStep (L : Nat) (hL : 1 ≤ L)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) (tie : Bool) :
    ClippedSquareCoordinates.recenterConfig L
        (finiteModifiedStep L (GridMajorityPeeling.finiteState S) v tie) =
      GridMajorityPeeling.state (DropletModifiedWord.modifiedStep
        (ClippedDiamondGeometry.clippedDomain L) (image L S)
        (ClippedSquareCoordinates.recenter L v) tie) := by
  rw [modifiedStep_image_recenter L hL S v tie,
    state_image_recenter L hL, finiteState_finiteModifiedSetStep]

def finiteModifiedWord (L : Nat)
    (g : SquareSpin.Config (ClippedSquareCoordinates.parameter L)) :
    List (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L) × Bool) →
      SquareSpin.Config (ClippedSquareCoordinates.parameter L)
  | [] => g
  | e :: w => finiteModifiedWord L (finiteModifiedStep L g e.1 e.2) w

def finiteModifiedSetWord (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))) :
    List (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L) × Bool) →
      Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))
  | [] => S
  | e :: w => finiteModifiedSetWord L (finiteModifiedSetStep L S e.1 e.2) w

theorem finiteState_finiteModifiedSetWord (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (w : List (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L) × Bool)) :
    GridMajorityPeeling.finiteState (finiteModifiedSetWord L S w) =
      finiteModifiedWord L (GridMajorityPeeling.finiteState S) w := by
  induction w generalizing S with
  | nil => rfl
  | cons e w ih =>
    change GridMajorityPeeling.finiteState (finiteModifiedSetWord L
      (finiteModifiedSetStep L S e.1 e.2) w) = _
    rw [ih, finiteState_finiteModifiedSetStep]
    rfl

theorem modifiedWord_image_recenter (L : Nat) (hL : 1 ≤ L)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (w : List (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L) × Bool)) :
    DropletModifiedWord.modifiedWord (ClippedDiamondGeometry.clippedDomain L) (image L S)
        (w.map (fun e => (ClippedSquareCoordinates.recenter L e.1, e.2))) =
      image L (finiteModifiedSetWord L S w) := by
  induction w generalizing S with
  | nil => rfl
  | cons e w ih =>
    change DropletModifiedWord.modifiedWord _
      (DropletModifiedWord.modifiedStep _ (image L S)
        (ClippedSquareCoordinates.recenter L e.1) e.2) _ = _
    rw [modifiedStep_image_recenter L hL S e.1 e.2, ih]
    rfl

theorem recenterConfig_finiteModifiedWord (L : Nat) (hL : 1 ≤ L)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (w : List (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L) × Bool)) :
    ClippedSquareCoordinates.recenterConfig L
        (finiteModifiedWord L (GridMajorityPeeling.finiteState S) w) =
      GridMajorityPeeling.state (DropletModifiedWord.modifiedWord
        (ClippedDiamondGeometry.clippedDomain L) (image L S)
        (w.map (fun e => (ClippedSquareCoordinates.recenter L e.1, e.2)))) := by
  rw [modifiedWord_image_recenter L hL S w,
    state_image_recenter L hL, finiteState_finiteModifiedSetWord]

theorem recenterConfig_finiteModifiedWord_config (L : Nat) (hL : 1 ≤ L)
    (g : SquareSpin.Config (ClippedSquareCoordinates.parameter L))
    (w : List (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L) × Bool)) :
    ClippedSquareCoordinates.recenterConfig L (finiteModifiedWord L g w) =
      GridMajorityPeeling.state (DropletModifiedWord.modifiedWord
        (ClippedDiamondGeometry.clippedDomain L) (image L (occupied g))
        (w.map (fun e => (ClippedSquareCoordinates.recenter L e.1, e.2)))) := by
  simpa only [finiteState_occupied] using
    recenterConfig_finiteModifiedWord L hL (occupied g) w

theorem finiteModifiedWord_eq_foldl (L : Nat)
    (g : SquareSpin.Config (ClippedSquareCoordinates.parameter L))
    (w : List (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L) × Bool)) :
    finiteModifiedWord L g w = w.foldl (fun f e => finiteModifiedStep L f e.1 e.2) g := by
  induction w generalizing g with
  | nil => rfl
  | cons e w ih => exact ih _
end MathResearchAnalysis.CenteredPeelingTransport





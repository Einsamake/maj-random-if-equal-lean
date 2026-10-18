module

public import MathResearchAnalysis.SquareGridEmbedding
public import MathResearchAnalysis.InfiniteGridTranslation
public import MathResearchAnalysis.ClippedDiamondGeometry
public import MathResearchAnalysis.DropletModifiedWord

set_option autoImplicit false

/-!
# Centered droplet coordinates and the actual finite square

For L ≥ 1 the centered square [-L,L]² has side 2L+1 and is represented
by the existing finite model with parameter 2L-1, whose side is n+2.
All coordinates, including the exterior, refer to the actual grid embedding.
-/

@[expose] public section

namespace MathResearchAnalysis.ClippedSquareCoordinates

open InfiniteGridModel

def parameter (L : Nat) : Nat := 2 * L - 1

def side (L : Nat) : Nat := 2 * L + 1

def recenter (L : Nat) (v : SquareTasks.Vertex (parameter L)) : Site :=
  ((v.1.val : Int) - L, (v.2.val : Int) - L)

def uncenter (L : Nat) (z : Site) : Site := (z.1 + L, z.2 + L)

def centeredSquare (L : Nat) (z : Site) : Prop := |z.1| ≤ (L : Int) ∧ |z.2| ≤ (L : Int)

theorem parameter_side (L : Nat) (hL : 1 ≤ L) : parameter L + 2 = side L := by
  unfold parameter side
  omega

theorem uncenter_recenter (L : Nat) (v : SquareTasks.Vertex (parameter L)) :
    uncenter L (recenter L v) = SquareGridEmbedding.embed (parameter L) v := by
  apply Prod.ext <;> dsimp [uncenter, recenter, SquareGridEmbedding.embed] <;> omega

theorem recenter_injective (L : Nat) : Function.Injective (recenter L) := by
  intro v w h
  apply SquareGridEmbedding.embed_injective (parameter L)
  have he := congrArg (uncenter L) h
  simpa only [uncenter_recenter] using he

theorem centeredSquare_iff_inside (L : Nat) (z : Site) :
    centeredSquare L z ↔ Inside (side L) (uncenter L z) := by
  simp only [centeredSquare, abs_le, Inside, uncenter, side, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  omega

theorem recenter_in_square (L : Nat) (hL : 1 ≤ L)
    (v : SquareTasks.Vertex (parameter L)) : centeredSquare L (recenter L v) := by
  apply (centeredSquare_iff_inside L _).mpr
  rw [uncenter_recenter, ← parameter_side L hL]
  exact SquareGridEmbedding.embed_inside (parameter L) v

theorem exists_recenter_iff (L : Nat) (hL : 1 ≤ L) (z : Site) :
    (∃ v : SquareTasks.Vertex (parameter L), recenter L v = z) ↔ centeredSquare L z := by
  constructor
  · rintro ⟨v, rfl⟩
    exact recenter_in_square L hL v
  · intro hz
    have hi := (centeredSquare_iff_inside L z).mp hz
    rw [← parameter_side L hL] at hi
    obtain ⟨v, hv⟩ := (SquareGridEmbedding.inside_iff_exists_vertex (parameter L) _).mp hi
    refine ⟨v, ?_⟩
    apply Prod.ext
    · have hx := congrArg Prod.fst hv
      dsimp [SquareGridEmbedding.embed, uncenter, recenter] at *
      omega
    · have hy := congrArg Prod.snd hv
      dsimp [SquareGridEmbedding.embed, uncenter, recenter] at *
      omega

def centeredSites (L : Nat) : Finset Site := Finset.univ.image (recenter L)

theorem mem_centeredSites (L : Nat) (hL : 1 ≤ L) (z : Site) :
    z ∈ centeredSites L ↔ centeredSquare L z := by
  simp only [centeredSites, Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_recenter_iff L hL z

theorem card_centeredSites (L : Nat) (hL : 1 ≤ L) :
    (centeredSites L).card = (side L) ^ 2 := by
  rw [centeredSites, Finset.card_image_of_injective _ (recenter_injective L)]
  simp only [Finset.card_univ, SquareTasks.Vertex, Fintype.card_prod, Fintype.card_fin]
  rw [parameter_side L hL]
  exact (pow_two _).symm

def recenterConfig (L : Nat) (g : SquareSpin.Config (parameter L)) : Config :=
  InfiniteGridTranslation.translate (-(L : Int), -(L : Int))
    (SquareGridEmbedding.extend (parameter L) g)

theorem recenterConfig_at_vertex (L : Nat) (g : SquareSpin.Config (parameter L))
    (v : SquareTasks.Vertex (parameter L)) : recenterConfig L g (recenter L v) = g v := by
  unfold recenterConfig InfiniteGridTranslation.translate
  rw [show InfiniteGridTranslation.shift (-(L : Int), -(L : Int)) (recenter L v) =
      SquareGridEmbedding.embed (parameter L) v by
    apply Prod.ext <;> dsimp [InfiniteGridTranslation.shift, recenter, SquareGridEmbedding.embed] <;> omega]
  exact SquareGridEmbedding.extend_embed (parameter L) g v

theorem recenterConfig_outside (L : Nat) (hL : 1 ≤ L)
    (g : SquareSpin.Config (parameter L)) (z : Site) (hz : ¬ centeredSquare L z) :
    recenterConfig L g z = false := by
  unfold recenterConfig InfiniteGridTranslation.translate
  apply SquareGridEmbedding.extend_outside
  intro hi
  apply hz
  apply (centeredSquare_iff_inside L z).mpr
  rw [← parameter_side L hL]
  have hs : InfiniteGridTranslation.shift (-(L : Int), -(L : Int)) z = uncenter L z := by
    apply Prod.ext <;> dsimp [InfiniteGridTranslation.shift, uncenter] <;> omega
  rwa [hs] at hi

/-- The actual finite vertices whose centered sites lie in the clipped mask. -/
def clippedVertices (L : Nat) : Finset (SquareTasks.Vertex (parameter L)) :=
  Finset.univ.filter (fun v => recenter L v ∈ ClippedDiamondGeometry.clippedDomain L)

theorem mem_clippedVertices (L : Nat) (v : SquareTasks.Vertex (parameter L)) :
    v ∈ clippedVertices L ↔ recenter L v ∈ ClippedDiamondGeometry.clippedDomain L := by
  simp [clippedVertices]

theorem image_clippedVertices (L : Nat) (hL : 1 ≤ L) :
    (clippedVertices L).image (recenter L) = ClippedDiamondGeometry.clippedDomain L := by
  ext z
  constructor
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_clippedVertices L v).mp hv
  · intro hz
    have hc := (ClippedDiamondGeometry.mem_clippedDomain L z).mp hz
    obtain ⟨v, hv⟩ := (exists_recenter_iff L hL z).mpr ⟨hc.1, hc.2.1⟩
    exact Finset.mem_image.mpr ⟨v, (mem_clippedVertices L v).mpr (by simpa only [hv] using hz), hv⟩

theorem clippedDomain_subset_centeredSites (L : Nat) (hL : 1 ≤ L) :
    ClippedDiamondGeometry.clippedDomain L ⊆ centeredSites L := by
  intro z hz
  have hc := (ClippedDiamondGeometry.mem_clippedDomain L z).mp hz
  exact (mem_centeredSites L hL z).mpr ⟨hc.1, hc.2.1⟩

/-- Restrict a finite minus set to the actual centered finite model. -/
def clippedConfig (L : Nat) (S : Finset Site) : SquareSpin.Config (parameter L) :=
  fun v => GridMajorityPeeling.state S (recenter L v)

theorem recenter_clippedConfig (L : Nat) (hL : 1 ≤ L) (S : Finset Site)
    (hS : S ⊆ ClippedDiamondGeometry.clippedDomain L) :
    recenterConfig L (clippedConfig L S) = GridMajorityPeeling.state S := by
  funext z
  by_cases hz : centeredSquare L z
  · obtain ⟨v, rfl⟩ := (exists_recenter_iff L hL z).mpr hz
    rw [recenterConfig_at_vertex]
    rfl
  · rw [recenterConfig_outside L hL _ z hz]
    have hnot : z ∉ S := by
      intro hmem
      have hc := (ClippedDiamondGeometry.mem_clippedDomain L z).mp (hS hmem)
      exact hz ⟨hc.1, hc.2.1⟩
    simp [GridMajorityPeeling.state, hnot]

theorem clippedWord_comparison (L : Nat) {S T : Finset Site} (hST : S ⊆ T)
    (w : List DropletModifiedWord.Event) :
    DropletModifiedWord.modifiedWord (ClippedDiamondGeometry.clippedDomain L) S w ⊆
      DropletModifiedWord.rawWord (ClippedDiamondGeometry.clippedDomain L) T w :=
  DropletModifiedWord.modifiedWord_subset_rawWord _ hST w

theorem modified_clippedWord_finite_representation (L : Nat) (hL : 1 ≤ L)
    (S : Finset Site) (hS : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (w : List DropletModifiedWord.Event) :
    ∃ g : SquareSpin.Config (parameter L),
      recenterConfig L g = GridMajorityPeeling.state
        (DropletModifiedWord.modifiedWord (ClippedDiamondGeometry.clippedDomain L) S w) := by
  refine ⟨clippedConfig L (DropletModifiedWord.modifiedWord (ClippedDiamondGeometry.clippedDomain L) S w), ?_⟩
  exact recenter_clippedConfig L hL _ (DropletModifiedWord.modifiedWord_supported hS w)

theorem raw_clippedWord_finite_representation (L : Nat) (hL : 1 ≤ L)
    (S : Finset Site) (hS : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (w : List DropletModifiedWord.Event) :
    ∃ g : SquareSpin.Config (parameter L),
      recenterConfig L g = GridMajorityPeeling.state
        (DropletModifiedWord.rawWord (ClippedDiamondGeometry.clippedDomain L) S w) := by
  refine ⟨clippedConfig L (DropletModifiedWord.rawWord (ClippedDiamondGeometry.clippedDomain L) S w), ?_⟩
  exact recenter_clippedConfig L hL _ (DropletModifiedWord.rawWord_supported hS w)

theorem initial_clippedWord_stable (L : Nat) (hL : 1 ≤ L)
    (w : List DropletModifiedWord.Event) :
    DropletModifiedWord.Stable (DropletModifiedWord.modifiedWord
      (ClippedDiamondGeometry.clippedDomain L) (ClippedDiamondGeometry.clippedDomain L) w) :=
  DropletModifiedWord.modifiedWord_stable _ (ClippedDiamondGeometry.clippedDomain_stable hL) w

/-- The centered actual four-input rule is the existing finite-square rule. -/
theorem update_recenterConfig (L : Nat) (g : SquareSpin.Config (parameter L))
    (v : SquareTasks.Vertex (parameter L)) (tie : Bool) :
    InfiniteGridModel.update (fun _ _ => tie) 0 (recenter L v) (recenterConfig L g) =
      SquareSpin.rule g v tie := by
  unfold recenterConfig
  change InfiniteGridModel.update
    (InfiniteGridTranslation.translateMarks (-(L : Int), -(L : Int)) (fun _ _ => tie))
    0 (recenter L v) _ = _
  rw [InfiniteGridTranslation.update_translate]
  have hs : InfiniteGridTranslation.shift (-(L : Int), -(L : Int)) (recenter L v) =
      SquareGridEmbedding.embed (parameter L) v := by
    apply Prod.ext <;> dsimp [InfiniteGridTranslation.shift, recenter, SquareGridEmbedding.embed] <;> omega
  rw [hs, SquareGridEmbedding.update_embed]
  rfl

theorem rawStep_clippedConfig (L : Nat) (hL : 1 ≤ L) (S : Finset Site)
    (hS : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (v : SquareTasks.Vertex (parameter L)) (tie : Bool) :
    clippedConfig L (DropletModifiedWord.rawStep S (recenter L v) tie) =
      SquareSpin.cellUpdate (clippedConfig L S) v tie := by
  have hr : DropletModifiedWord.localRule S (recenter L v) tie =
      SquareSpin.rule (clippedConfig L S) v tie := by
    rw [DropletModifiedWord.localRule_eq_update S _ tie 0,
      ← recenter_clippedConfig L hL S hS]
    exact update_recenterConfig L (clippedConfig L S) v tie
  funext u
  change GridMajorityPeeling.state (DropletModifiedWord.rawStep S (recenter L v) tie)
    (recenter L u) = SquareSpin.cellUpdate (clippedConfig L S) v tie u
  rw [DropletModifiedWord.state_rawStep, hr]
  unfold SquareSpin.cellUpdate
  by_cases hu : u = v
  · subst u
    simp
  · have he : recenter L u ≠ recenter L v := fun h => hu (recenter_injective L h)
    simp [Function.update_of_ne hu, Function.update_of_ne he, clippedConfig]

def finiteMaskedRawStep (L : Nat) (g : SquareSpin.Config (parameter L))
    (v : SquareTasks.Vertex (parameter L)) (tie : Bool) : SquareSpin.Config (parameter L) :=
  if v ∈ clippedVertices L then SquareSpin.cellUpdate g v tie else g

theorem maskedRawStep_clippedConfig (L : Nat) (hL : 1 ≤ L) (S : Finset Site)
    (hS : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (v : SquareTasks.Vertex (parameter L)) (tie : Bool) :
    clippedConfig L (DropletModifiedWord.maskedRawStep
      (ClippedDiamondGeometry.clippedDomain L) S (recenter L v) tie) =
      finiteMaskedRawStep L (clippedConfig L S) v tie := by
  by_cases hv : recenter L v ∈ ClippedDiamondGeometry.clippedDomain L
  · simp only [DropletModifiedWord.maskedRawStep,
      finiteMaskedRawStep, mem_clippedVertices, hv, ite_true]
    exact rawStep_clippedConfig L hL S hS v tie
  · simp [DropletModifiedWord.maskedRawStep, finiteMaskedRawStep, mem_clippedVertices, hv]

def finiteRawWord (L : Nat) (g : SquareSpin.Config (parameter L)) :
    List (SquareTasks.Vertex (parameter L) × Bool) → SquareSpin.Config (parameter L)
  | [] => g
  | e :: w => finiteRawWord L (finiteMaskedRawStep L g e.1 e.2) w

theorem rawWord_clippedConfig (L : Nat) (hL : 1 ≤ L) (S : Finset Site)
    (hS : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (w : List (SquareTasks.Vertex (parameter L) × Bool)) :
    clippedConfig L (DropletModifiedWord.rawWord (ClippedDiamondGeometry.clippedDomain L) S
      (w.map (fun e => (recenter L e.1, e.2)))) = finiteRawWord L (clippedConfig L S) w := by
  induction w generalizing S with
  | nil => rfl
  | cons e w ih =>
    change clippedConfig L (DropletModifiedWord.rawWord _
      (DropletModifiedWord.maskedRawStep _ S (recenter L e.1) e.2) _) =
        finiteRawWord L (finiteMaskedRawStep L (clippedConfig L S) e.1 e.2) w
    rw [ih _ (DropletModifiedWord.maskedRawStep_supported hS _ _),
      maskedRawStep_clippedConfig L hL S hS e.1 e.2]

end MathResearchAnalysis.ClippedSquareCoordinates

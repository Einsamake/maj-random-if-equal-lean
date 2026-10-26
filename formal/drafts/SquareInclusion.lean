module
public import MathResearchAnalysis.MixedSquareModel
public import Mathlib.Tactic
set_option autoImplicit false
/-! Coordinate-preserving comparison of two actual finite square updates.
The smaller process has zero boundary; the larger one has the genuine mixed
boundary. Both read four directional inputs with the same tie mark. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.SquareInclusion
open SquareTasks (Vertex)

/-- The canonical bottom-left inclusion preserves both coordinate values. -/
def site {n m : Nat} (hnm : n≤m) (v : Vertex n) : Vertex m :=
  (⟨v.1.val, lt_of_lt_of_le v.1.isLt (Nat.add_le_add_right hnm 2)⟩,
   ⟨v.2.val, lt_of_lt_of_le v.2.isLt (Nat.add_le_add_right hnm 2)⟩)

@[simp] theorem site_fst_val {n m : Nat} (hnm : n≤m) (v : Vertex n) :
    (site hnm v).1.val=v.1.val := rfl

@[simp] theorem site_snd_val {n m : Nat} (hnm : n≤m) (v : Vertex n) :
    (site hnm v).2.val=v.2.val := rfl

theorem site_injective {n m : Nat} (hnm : n≤m) : Function.Injective (site hnm) := by
  intro v w h
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun z : Vertex m => z.1.val) h
  · exact congrArg (fun z : Vertex m => z.2.val) h

/-- The canonical inclusion as a genuine finite-index embedding. -/
def siteEmbedding {n m : Nat} (hnm : n≤m) : Vertex n ↪ Vertex m :=
  ⟨site hnm, site_injective hnm⟩

/-- Site/ring identities retain their ring index under spatial inclusion. -/
def event {n m : Nat} (hnm : n≤m) (e : SquareSpin.Event n) : SquareSpin.Event m :=
  (site hnm e.1,e.2)

theorem event_injective {n m : Nat} (hnm : n≤m) : Function.Injective (event hnm) := by
  intro a b h
  apply Prod.ext
  · exact site_injective hnm (congrArg Prod.fst h)
  · exact congrArg (fun e : SquareSpin.Event m => e.2) h

/-- Comparison is only required at the actual smaller-square cells. -/
def Rel {n m : Nat} (hnm : n≤m) (f : SquareSpin.Config n) (g : SquareSpin.Config m) : Prop :=
  ∀ v, f v ≤ g (site hnm v)

@[simp] theorem embed_site {n m : Nat} (hnm : n≤m) (v : Vertex n) :
    SquareGridEmbedding.embed m (site hnm v)=SquareGridEmbedding.embed n v := rfl

/-- Zero exterior inputs of the smaller square are below every larger input;
inside the smaller square the assumed relation supplies the comparison. -/
theorem extend_le {n m : Nat} (hnm : n≤m) {f : SquareSpin.Config n}
    {g : SquareSpin.Config m} (hrel : Rel hnm f g) :
    SquareGridEmbedding.extend n f ≤ MixedSquareModel.extend m g := by
  intro z
  by_cases hz : InfiniteGridModel.Inside (n+2) z
  · have hzM : InfiniteGridModel.Inside (m+2) z := by
      unfold InfiniteGridModel.Inside at hz ⊢
      omega
    rw [SquareGridEmbedding.extend, dite_eq_left hz,
      MixedSquareModel.extend_inside m g z hzM]
    exact hrel (SquareGridEmbedding.vertexOfInside n z hz)
  · rw [SquareGridEmbedding.extend_outside n f z hz]
    exact Bool.false_le _

/-- Both real four-neighbour update rules are compared with the same mark. -/
theorem rule_le {n m : Nat} (hnm : n≤m) {f : SquareSpin.Config n}
    {g : SquareSpin.Config m} (hrel : Rel hnm f g) (v : Vertex n) (tie : Bool) :
    SquareSpin.rule f v tie ≤ MixedSquareModel.rule g (site hnm v) tie := by
  have he := SquareGridEmbedding.update_embed n (fun _ _ => tie) 0 f v
  change InfiniteGridModel.majority4
    (SquareGridEmbedding.extend n f (InfiniteGridModel.north (SquareGridEmbedding.embed n v)))
    (SquareGridEmbedding.extend n f (InfiniteGridModel.east (SquareGridEmbedding.embed n v)))
    (SquareGridEmbedding.extend n f (InfiniteGridModel.south (SquareGridEmbedding.embed n v)))
    (SquareGridEmbedding.extend n f (InfiniteGridModel.west (SquareGridEmbedding.embed n v))) tie =
      SquareSpin.rule f v tie at he
  rw [←he]
  unfold MixedSquareModel.rule
  rw [embed_site]
  apply InfiniteGridModel.majority4_monotone
  all_goals exact extend_le hnm hrel _

/-- One matched physical event preserves the restriction comparison. -/
theorem cellUpdate_rel {n m : Nat} (hnm : n≤m) {f : SquareSpin.Config n}
    {g : SquareSpin.Config m} (hrel : Rel hnm f g) (v : Vertex n) (tie : Bool) :
    Rel hnm (SquareSpin.cellUpdate f v tie)
      (MixedSquareModel.cellUpdate g (site hnm v) tie) := by
  intro u
  by_cases hu : u=v
  · subst u
    simpa only [SquareSpin.cellUpdate_same, MixedSquareModel.cellUpdate_same] using
      rule_le hnm hrel v tie
  · have hi : site hnm u ≠ site hnm v := fun he => hu (site_injective hnm he)
    simpa only [SquareSpin.cellUpdate_other _ _ _ _ hu,
      MixedSquareModel.cellUpdate_other _ _ _ _ hi] using hrel u

/-- An event outside the embedded small square does not write its restriction. -/
theorem outside_cellUpdate_rel {n m : Nat} (hnm : n≤m) {f : SquareSpin.Config n}
    {g : SquareSpin.Config m} (hrel : Rel hnm f g) (u : Vertex m) (tie : Bool)
    (hout : ∀ v, site hnm v ≠ u) :
    Rel hnm f (MixedSquareModel.cellUpdate g u tie) := by
  intro v
  simpa only [MixedSquareModel.cellUpdate_other _ _ _ _ (hout v)] using hrel v

/-- The maximal larger initial state dominates every smaller initial state. -/
theorem initial_rel_top {n m : Nat} (hnm : n≤m) (f : SquareSpin.Config n) :
    Rel hnm f (fun _ => true) := fun v => Bool.le_true (f v)
end MathResearchAnalysis.SquareInclusion

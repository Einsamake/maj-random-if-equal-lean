module

public import MathResearchAnalysis.SquareGridEmbedding
public import MathResearchAnalysis.EventTrace

set_option autoImplicit false

/-!
# The actual finite square with mixed south/west and north/east boundary

South and west exterior coordinates are fixed to false; the remaining
exterior coordinates are fixed to true. Four nearest neighbours are read,
without a centre vote, and only the selected finite vertex is written.
No probability law, exclusion-process identification or time bound is assumed.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.MixedSquareModel

open InfiniteGridModel (Site)
open SquareTasks (Vertex)

abbrev Config (n : Nat) := SquareSpin.Config n
abbrev Event (n : Nat) := SquareSpin.Event n

/-- Mixed boundary extension, with southwest exterior values taking priority. -/
def extend (n : Nat) (f : Config n) : InfiniteGridModel.Config := fun z =>
  if h : InfiniteGridModel.Inside (n+2) z then
    f (SquareGridEmbedding.vertexOfInside n z h)
  else if z.1 < 0 ∨ z.2 < 0 then false else true

/-- The original four-input majority rule, with the true mixed boundary. -/
def rule {n : Nat} (f : Config n) (v : Vertex n) (tie : Bool) : Bool :=
  InfiniteGridModel.majority4
    (extend n f (InfiniteGridModel.north (SquareGridEmbedding.embed n v)))
    (extend n f (InfiniteGridModel.east (SquareGridEmbedding.embed n v)))
    (extend n f (InfiniteGridModel.south (SquareGridEmbedding.embed n v)))
    (extend n f (InfiniteGridModel.west (SquareGridEmbedding.embed n v))) tie

/-- Read the old state and write exactly one finite vertex. -/
def cellUpdate {n : Nat} (f : Config n) (v : Vertex n) (tie : Bool) : Config n :=
  Function.update f v (rule f v tie)

/-- Marks retain their actual site/ring identities. -/
def updateEvent {n : Nat} (η : Event n → Bool) (e : Event n) (f : Config n) : Config n :=
  cellUpdate f e.1 (η e)

/-- Execute the actual marked events from left to right. -/
def execute {n : Nat} (η : Event n → Bool) (w : List (Event n)) (f : Config n) : Config n :=
  EventTrace.execute (updateEvent η) w f

@[simp] theorem extend_embed (n : Nat) (f : Config n) (v : Vertex n) :
    extend n f (SquareGridEmbedding.embed n v) = f v := by
  unfold extend
  rw [dite_eq_left (SquareGridEmbedding.embed_inside n v)]
  congr 1

theorem extend_inside (n : Nat) (f : Config n) (z : Site)
    (h : InfiniteGridModel.Inside (n+2) z) :
    extend n f z = f (SquareGridEmbedding.vertexOfInside n z h) := by
  simp only [extend, dite_eq_left h]

theorem extend_outside (n : Nat) (f : Config n) (z : Site)
    (h : ¬ InfiniteGridModel.Inside (n+2) z) :
    extend n f z = if z.1 < 0 ∨ z.2 < 0 then false else true := by
  simp only [extend, dite_eq_right h]

theorem extend_low (n : Nat) (f : Config n) (z : Site) (h : z.1 < 0 ∨ z.2 < 0) :
    extend n f z = false := by
  have hn : ¬ InfiniteGridModel.Inside (n+2) z := by
    unfold InfiniteGridModel.Inside
    omega
  simp only [extend_outside n f z hn, ite_eq_left h]

theorem extend_high (n : Nat) (f : Config n) (z : Site)
    (hx : 0 ≤ z.1) (hy : 0 ≤ z.2)
    (h : (n+2 : Int) ≤ z.1 ∨ (n+2 : Int) ≤ z.2) : extend n f z = true := by
  have hn : ¬ InfiniteGridModel.Inside (n+2) z := by
    unfold InfiniteGridModel.Inside
    push_cast
    omega
  rw [extend_outside n f z hn]
  simp only [not_lt.mpr hx, not_lt.mpr hy, or_self, ite_false]

@[simp] theorem extend_west_boundary (n : Nat) (f : Config n) (y : Int) :
    extend n f (-1,y) = false := extend_low n f _ (Or.inl (by norm_num))

@[simp] theorem extend_south_boundary (n : Nat) (f : Config n) (x : Int) :
    extend n f (x,-1) = false := extend_low n f _ (Or.inr (by norm_num))

theorem extend_east_boundary (n : Nat) (f : Config n) (y : Int) (hy : 0 ≤ y) :
    extend n f (n+2,y) = true := by
  exact extend_high n f _ (by omega) hy (Or.inl le_rfl)

theorem extend_north_boundary (n : Nat) (f : Config n) (x : Int) (hx : 0 ≤ x) :
    extend n f (x,n+2) = true := by
  exact extend_high n f _ hx (by omega) (Or.inr le_rfl)

theorem extend_mono {n : Nat} {f g : Config n} (h : f ≤ g) : extend n f ≤ extend n g := by
  intro z
  by_cases hz : InfiniteGridModel.Inside (n+2) z
  · simpa only [extend_inside n f z hz, extend_inside n g z hz] using
      h (SquareGridEmbedding.vertexOfInside n z hz)
  · rw [extend_outside n f z hz, extend_outside n g z hz]

theorem vertexOfInside_mono (n : Nat) {z w : Site}
    (hz : InfiniteGridModel.Inside (n+2) z) (hw : InfiniteGridModel.Inside (n+2) w)
    (hzw : z ≤ w) :
    SquareGridEmbedding.vertexOfInside n z hz ≤ SquareGridEmbedding.vertexOfInside n w hw := by
  change z.1.toNat ≤ w.1.toNat ∧ z.2.toNat ≤ w.2.toNat
  exact ⟨Int.toNat_le_toNat hzw.1, Int.toNat_le_toNat hzw.2⟩

/-- Monotone finite states extend to a genuinely monotone integer-grid state. -/
theorem extend_monotone {n : Nat} {f : Config n} (hf : Monotone f) :
    Monotone (extend n f) := by
  intro z w hzw
  have hx : z.1 ≤ w.1 := hzw.1
  have hy : z.2 ≤ w.2 := hzw.2
  by_cases hz : InfiniteGridModel.Inside (n+2) z
  · by_cases hw : InfiniteGridModel.Inside (n+2) w
    · rw [extend_inside n f z hz, extend_inside n f w hw]
      exact hf (vertexOfInside_mono n hz hw hzw)
    · have hwlow : ¬ (w.1 < 0 ∨ w.2 < 0) := by
        unfold InfiniteGridModel.Inside at hz
        omega
      rw [extend_outside n f w hw, ite_eq_right hwlow]
      exact Bool.le_true _
  · by_cases hw : InfiniteGridModel.Inside (n+2) w
    · have hzlow : z.1 < 0 ∨ z.2 < 0 := by
        unfold InfiniteGridModel.Inside at hz hw
        omega
      rw [extend_low n f z hzlow]
      exact Bool.false_le _
    · rw [extend_outside n f z hz, extend_outside n f w hw]
      by_cases hzl : z.1 < 0 ∨ z.2 < 0
      · rw [ite_eq_left hzl]
        exact Bool.false_le _
      · have hwl : ¬ (w.1 < 0 ∨ w.2 < 0) := by omega
        rw [ite_eq_right hzl, ite_eq_right hwl]

theorem rule_mono_common_mark {n : Nat} {f g : Config n} (h : f ≤ g)
    (v : Vertex n) (tie : Bool) : rule f v tie ≤ rule g v tie := by
  apply InfiniteGridModel.majority4_monotone
  all_goals exact extend_mono h _

@[simp] theorem cellUpdate_same {n : Nat} (f : Config n) (v : Vertex n) (tie : Bool) :
    cellUpdate f v tie v = rule f v tie := by simp [cellUpdate]

theorem cellUpdate_other {n : Nat} (f : Config n) (v u : Vertex n) (tie : Bool)
    (h : u ≠ v) : cellUpdate f v tie u = f u := by simp [cellUpdate,h]

theorem cellUpdate_mono_common_mark {n : Nat} {f g : Config n} (h : f ≤ g)
    (v : Vertex n) (tie : Bool) : cellUpdate f v tie ≤ cellUpdate g v tie := by
  intro u
  by_cases hu : u = v
  · subst u
    simpa only [cellUpdate_same] using rule_mono_common_mark h v tie
  · simpa only [cellUpdate_other f v u tie hu, cellUpdate_other g v u tie hu] using h u

/-- A finite write has exactly its embedded single-site support. -/
theorem extend_cellUpdate_eq_update {n : Nat} (f : Config n) (v : Vertex n) (tie : Bool) :
    extend n (cellUpdate f v tie) = Function.update (extend n f)
      (SquareGridEmbedding.embed n v) (rule f v tie) := by
  funext z
  by_cases hz : InfiniteGridModel.Inside (n+2) z
  · obtain ⟨u,rfl⟩ := (SquareGridEmbedding.inside_iff_exists_vertex n z).mp hz
    by_cases hu : u = v
    · subst u
      simp [cellUpdate]
    · have he : SquareGridEmbedding.embed n u ≠ SquareGridEmbedding.embed n v :=
        fun he => hu (SquareGridEmbedding.embed_injective n he)
      simp only [extend_embed, cellUpdate_other _ _ _ _ hu, Function.update_of_ne he]
  · have he : z ≠ SquareGridEmbedding.embed n v := by
      intro he
      exact hz (he.symm ▸ SquareGridEmbedding.embed_inside n v)
    rw [Function.update_of_ne he, extend_outside n (cellUpdate f v tie) z hz,
      extend_outside n f z hz]

/-- The genuine zero-boundary extension is below the mixed one. -/
theorem zeroBoundary_extend_le {n : Nat} {f g : Config n} (h : f ≤ g) :
    SquareGridEmbedding.extend n f ≤ extend n g := by
  intro z
  by_cases hz : InfiniteGridModel.Inside (n+2) z
  · rw [SquareGridEmbedding.extend, dite_eq_left hz, extend_inside n g z hz]
    exact h _
  · rw [SquareGridEmbedding.extend_outside n f z hz]
    exact Bool.false_le _

theorem zeroBoundary_rule_le {n : Nat} {f g : Config n} (h : f ≤ g)
    (v : Vertex n) (tie : Bool) : SquareSpin.rule f v tie ≤ rule g v tie := by
  have he := SquareGridEmbedding.update_embed n (fun _ _ => tie) 0 f v
  change InfiniteGridModel.majority4
    (SquareGridEmbedding.extend n f (InfiniteGridModel.north (SquareGridEmbedding.embed n v)))
    (SquareGridEmbedding.extend n f (InfiniteGridModel.east (SquareGridEmbedding.embed n v)))
    (SquareGridEmbedding.extend n f (InfiniteGridModel.south (SquareGridEmbedding.embed n v)))
    (SquareGridEmbedding.extend n f (InfiniteGridModel.west (SquareGridEmbedding.embed n v))) tie =
      SquareSpin.rule f v tie at he
  rw [← he]
  apply InfiniteGridModel.majority4_monotone
  all_goals exact zeroBoundary_extend_le h _

theorem zeroBoundary_cellUpdate_le {n : Nat} {f g : Config n} (h : f ≤ g)
    (v : Vertex n) (tie : Bool) : SquareSpin.cellUpdate f v tie ≤ cellUpdate g v tie := by
  intro u
  by_cases hu : u = v
  · subst u
    simpa only [SquareSpin.cellUpdate_same,cellUpdate_same] using zeroBoundary_rule_le h v tie
  · simpa only [SquareSpin.cellUpdate_other _ _ _ _ hu,cellUpdate_other _ _ _ _ hu] using h u

theorem updateEvent_mono {n : Nat} (η : Event n → Bool) (e : Event n)
    {f g : Config n} (h : f ≤ g) : updateEvent η e f ≤ updateEvent η e g :=
  cellUpdate_mono_common_mark h e.1 (η e)

@[simp] theorem execute_nil {n : Nat} (η : Event n → Bool) (f : Config n) :
    execute η [] f = f := rfl

@[simp] theorem execute_cons {n : Nat} (η : Event n → Bool) (e : Event n)
    (w : List (Event n)) (f : Config n) : execute η (e::w) f = execute η w (updateEvent η e f) := rfl

theorem execute_append {n : Nat} (η : Event n → Bool) (w₁ w₂ : List (Event n)) (f : Config n) :
    execute η (w₁++w₂) f = execute η w₂ (execute η w₁ f) :=
  EventTrace.execute_append _ _ _ _

theorem execute_mono {n : Nat} (η : Event n → Bool) (w : List (Event n))
    {f g : Config n} (h : f ≤ g) : execute η w f ≤ execute η w g := by
  induction w generalizing f g with
  | nil => exact h
  | cons e w ih => exact ih (updateEvent_mono η e h)

end MathResearchAnalysis.MixedSquareModel


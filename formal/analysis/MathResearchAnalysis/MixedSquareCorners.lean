module
public import MathResearchAnalysis.MixedSquareModel
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Tactic.ByContra
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchAnalysis.MixedSquareCorners
open InfiniteGridModel

/-- The north and east inputs of an occupied point in an increasing region. -/
theorem true_ne_inputs {g : Config} (hg : Monotone g) {z : Site} (hz : g z = true) :
    g (north z) = true ∧ g (east z) = true := by
  have hn : z ≤ north z := by simp only [north, Prod.le_def]; constructor <;> omega
  have he : z ≤ east z := by simp only [east, Prod.le_def]; constructor <;> omega
  have hgn := hg hn
  have hge := hg he
  rw [hz] at hgn hge
  have hb : ∀ b : Bool, true ≤ b → b = true := by decide
  exact ⟨hb _ hgn,hb _ hge⟩

/-- The south and west inputs of a vacant point in an increasing region. -/
theorem false_sw_inputs {g : Config} (hg : Monotone g) {z : Site} (hz : g z = false) :
    g (south z) = false ∧ g (west z) = false := by
  have hs : south z ≤ z := by simp only [south, Prod.le_def]; constructor <;> omega
  have hw : west z ≤ z := by simp only [west, Prod.le_def]; constructor <;> omega
  have hgs := hg hs
  have hgw := hg hw
  rw [hz] at hgs hgw
  have hb : ∀ b : Bool, b ≤ false → b = false := by decide
  exact ⟨hb _ hgs,hb _ hgw⟩

/-- An occupied monotone cell is deleted exactly at a southwest exposed corner
and with the false tie mark. -/
theorem grid_rule_false_iff_of_true {g : Config} (hg : Monotone g) {z : Site}
    (hz : g z = true) (tie : Bool) :
    majority4 (g (north z)) (g (east z)) (g (south z)) (g (west z)) tie = false ↔
      g (south z) = false ∧ g (west z) = false ∧ tie = false := by
  obtain ⟨hn,he⟩ := true_ne_inputs hg hz
  rw [hn,he]
  cases hs : g (south z) <;> cases hw : g (west z) <;> cases tie <;> decide

/-- A vacant monotone cell is born exactly at a northeast exposed corner
and with the true tie mark. -/
theorem grid_rule_true_iff_of_false {g : Config} (hg : Monotone g) {z : Site}
    (hz : g z = false) (tie : Bool) :
    majority4 (g (north z)) (g (east z)) (g (south z)) (g (west z)) tie = true ↔
      g (north z) = true ∧ g (east z) = true ∧ tie = true := by
  obtain ⟨hs,hw⟩ := false_sw_inputs hg hz
  rw [hs,hw]
  cases hn : g (north z) <;> cases he : g (east z) <;> cases tie <;> decide

theorem strict_above_has_step {z y : Site} (hzy : z ≤ y) (hyz : y ≠ z) :
    north z ≤ y ∨ east z ≤ y := by
  have hx := hzy.1
  have hy := hzy.2
  have hstep : z.1 < y.1 ∨ z.2 < y.2 := by
    by_contra h
    have hsame : y = z := Prod.ext (by omega) (by omega)
    exact hyz hsame
  rcases hstep with h | h
  · right
    simp only [east, Prod.le_def]
    constructor <;> omega
  · left
    simp only [north, Prod.le_def]
    constructor <;> omega

theorem strict_below_has_step {x z : Site} (hxz : x ≤ z) (hne : x ≠ z) :
    x ≤ south z ∨ x ≤ west z := by
  have hx := hxz.1
  have hy := hxz.2
  have hstep : x.1 < z.1 ∨ x.2 < z.2 := by
    by_contra h
    have hsame : x = z := Prod.ext (by omega) (by omega)
    exact hne hsame
  rcases hstep with h | h
  · right
    simp only [west, Prod.le_def]
    constructor <;> omega
  · left
    simp only [south, Prod.le_def]
    constructor <;> omega

/-- A genuine single majority write preserves coordinatewise monotonicity. -/
theorem grid_update_monotone {g : Config} (hg : Monotone g) (z : Site) (tie : Bool) :
    Monotone (Function.update g z
      (majority4 (g (north z)) (g (east z)) (g (south z)) (g (west z)) tie)) := by
  let r := majority4 (g (north z)) (g (east z)) (g (south z)) (g (west z)) tie
  change Monotone (Function.update g z r)
  intro x y hxy
  by_cases hx : x = z
  · subst x
    by_cases hy : y = z
    · subst y
      exact le_refl _
    · rw [Function.update_self, Function.update_of_ne hy]
      cases hr : r with
      | false => simp
      | true =>
        cases hz : g z with
        | true => simpa only [hz] using hg hxy
        | false =>
          have hcorner := (grid_rule_true_iff_of_false hg hz tie).mp hr
          rcases strict_above_has_step hxy hy with hn | he
          · have h := hg hn
            simpa only [hcorner.1] using h
          · have h := hg he
            simpa only [hcorner.2.1] using h
  · by_cases hy : y = z
    · subst y
      rw [Function.update_of_ne hx, Function.update_self]
      cases hr : r with
      | true => simp
      | false =>
        cases hz : g z with
        | false => simpa only [hz] using hg hxy
        | true =>
          have hcorner := (grid_rule_false_iff_of_true hg hz tie).mp hr
          rcases strict_below_has_step hxy hx with hs | hw
          · have h := hg hs
            simpa only [hcorner.1] using h
          · have h := hg hw
            simpa only [hcorner.2.1] using h
    · rw [Function.update_of_ne hx, Function.update_of_ne hy]
      exact hg hxy





/-- Finite cells inherit the actual north/east input values, including the
mixed exterior values, from the monotone full-grid extension. -/
theorem finite_true_ne_inputs {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hv : f v = true) :
    MixedSquareModel.extend n f (north (SquareGridEmbedding.embed n v)) = true ∧
    MixedSquareModel.extend n f (east (SquareGridEmbedding.embed n v)) = true := by
  apply true_ne_inputs (MixedSquareModel.extend_monotone hf)
  simpa only [MixedSquareModel.extend_embed] using hv

theorem finite_false_sw_inputs {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hv : f v = false) :
    MixedSquareModel.extend n f (south (SquareGridEmbedding.embed n v)) = false ∧
    MixedSquareModel.extend n f (west (SquareGridEmbedding.embed n v)) = false := by
  apply false_sw_inputs (MixedSquareModel.extend_monotone hf)
  simpa only [MixedSquareModel.extend_embed] using hv

/-- The precise actual deletion criterion, with its tie mark. -/
theorem rule_false_iff_of_true {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hv : f v = true) (tie : Bool) :
    MixedSquareModel.rule f v tie = false ↔
      MixedSquareModel.extend n f (south (SquareGridEmbedding.embed n v)) = false ∧
      MixedSquareModel.extend n f (west (SquareGridEmbedding.embed n v)) = false ∧ tie = false := by
  exact grid_rule_false_iff_of_true (MixedSquareModel.extend_monotone hf)
    (by simpa only [MixedSquareModel.extend_embed] using hv) tie

/-- The precise actual birth criterion, with its tie mark. -/
theorem rule_true_iff_of_false {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hv : f v = false) (tie : Bool) :
    MixedSquareModel.rule f v tie = true ↔
      MixedSquareModel.extend n f (north (SquareGridEmbedding.embed n v)) = true ∧
      MixedSquareModel.extend n f (east (SquareGridEmbedding.embed n v)) = true ∧ tie = true := by
  exact grid_rule_true_iff_of_false (MixedSquareModel.extend_monotone hf)
    (by simpa only [MixedSquareModel.extend_embed] using hv) tie

/-- Southwest-exposed occupied corner, using the actual mixed boundary. -/
def removable {n : Nat} (f : SquareSpin.Config n) (v : SquareTasks.Vertex n) : Prop :=
  f v = true ∧ MixedSquareModel.extend n f (south (SquareGridEmbedding.embed n v)) = false ∧
    MixedSquareModel.extend n f (west (SquareGridEmbedding.embed n v)) = false

/-- Northeast-exposed vacant corner, using the actual mixed boundary. -/
def addable {n : Nat} (f : SquareSpin.Config n) (v : SquareTasks.Vertex n) : Prop :=
  f v = false ∧ MixedSquareModel.extend n f (north (SquareGridEmbedding.embed n v)) = true ∧
    MixedSquareModel.extend n f (east (SquareGridEmbedding.embed n v)) = true

/-- No other actual single-cell transition is possible in a monotone region. -/
theorem cellUpdate_changes_iff {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (v : SquareTasks.Vertex n) (tie : Bool) :
    MixedSquareModel.cellUpdate f v tie v ≠ f v ↔
      (removable f v ∧ tie = false) ∨ (addable f v ∧ tie = true) := by
  rw [MixedSquareModel.cellUpdate_same]
  cases hv : f v with
  | false =>
    have hc := rule_true_iff_of_false hf hv tie
    have hb : ∀ b : Bool, b ≠ false ↔ b = true := by decide
    rw [hb]
    simpa [removable,addable,hv,and_assoc] using hc
  | true =>
    have hc := rule_false_iff_of_true hf hv tie
    have hb : ∀ b : Bool, b ≠ true ↔ b = false := by decide
    rw [hb]
    simpa [removable,addable,hv,and_assoc] using hc

/-- Genuine finite single-site mixed updates preserve increasing regions. -/
theorem cellUpdate_monotone {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (v : SquareTasks.Vertex n) (tie : Bool) : Monotone (MixedSquareModel.cellUpdate f v tie) := by
  have hg := grid_update_monotone (MixedSquareModel.extend_monotone hf)
    (SquareGridEmbedding.embed n v) tie
  change Monotone (Function.update (MixedSquareModel.extend n f) (SquareGridEmbedding.embed n v)
    (MixedSquareModel.rule f v tie)) at hg
  rw [←MixedSquareModel.extend_cellUpdate_eq_update] at hg
  intro a b hab
  have he : SquareGridEmbedding.embed n a ≤ SquareGridEmbedding.embed n b := by
    constructor
    · change (a.1.val : Int) ≤ (b.1.val : Int)
      exact_mod_cast (show a.1.val ≤ b.1.val from hab.1)
    · change (a.2.val : Int) ≤ (b.2.val : Int)
      exact_mod_cast (show a.2.val ≤ b.2.val from hab.2)
  simpa only [MixedSquareModel.extend_embed] using hg he

/-- Every actual event word preserves the shape, with the original marks. -/
theorem execute_monotone {n : Nat} (η : MixedSquareModel.Event n → Bool)
    (w : List (MixedSquareModel.Event n)) {f : SquareSpin.Config n} (hf : Monotone f) :
    Monotone (MixedSquareModel.execute η w f) := by
  induction w generalizing f with
  | nil => exact hf
  | cons e w ih =>
    rw [MixedSquareModel.execute_cons]
    exact ih (cellUpdate_monotone hf e.1 (η e))

theorem execute_true_monotone {n : Nat} (η : MixedSquareModel.Event n → Bool)
    (w : List (MixedSquareModel.Event n)) :
    Monotone (MixedSquareModel.execute η w (fun _ => true)) :=
  execute_monotone η w (fun _ _ _ => le_refl _)

theorem execute_false_monotone {n : Nat} (η : MixedSquareModel.Event n → Bool)
    (w : List (MixedSquareModel.Event n)) :
    Monotone (MixedSquareModel.execute η w (fun _ => false)) :=
  execute_monotone η w (fun _ _ _ => le_refl _)

end MathResearchAnalysis.MixedSquareCorners


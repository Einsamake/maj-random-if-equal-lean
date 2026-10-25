module

public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Tactic.ByContra

set_option autoImplicit false

/-!
# Actual white-row lengths of monotone Boolean square configurations

Zero rows are genuine finite filters. Their initial-segment description and
reconstruction are proved from monotonicity, including the empty-square case.
This module does not define particles or assume any exclusion-process law.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.YoungRows

/-- Actual false entries in one row. -/
def rowZeros {M : Nat} (f : Fin M × Fin M → Bool) (y : Fin M) : Finset (Fin M) :=
  Finset.univ.filter (fun x => f (x,y) = false)

/-- The actual number of false entries in one row. -/
def rowLength {M : Nat} (f : Fin M × Fin M → Bool) (y : Fin M) : Nat :=
  (rowZeros f y).card

@[simp] theorem mem_rowZeros {M : Nat} (f : Fin M × Fin M → Bool) (x y : Fin M) :
    x ∈ rowZeros f y ↔ f (x,y) = false := by
  simp [rowZeros]

theorem rowLength_le_side {M : Nat} (f : Fin M × Fin M → Bool) (y : Fin M) :
    rowLength f y ≤ M := by
  simpa only [rowLength,rowZeros,Finset.card_univ,Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (Fin M)) (fun x => f (x,y) = false)

theorem rowZeros_antitone {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f)
    {y z : Fin M} (hyz : y ≤ z) : rowZeros f z ⊆ rowZeros f y := by
  intro x hx
  rw [mem_rowZeros] at hx ⊢
  have horder := hf (show (x,y) ≤ (x,z) from ⟨le_rfl,hyz⟩)
  rw [hx] at horder
  have hb : ∀ b : Bool, b ≤ false → b = false := by decide
  exact hb _ horder

theorem rowLength_antitone {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f) :
    Antitone (rowLength f) := by
  intro y z hyz
  exact Finset.card_le_card (rowZeros_antitone hf hyz)

/-- A monotone row is exactly the initial segment of its actual cardinality. -/
theorem false_iff_lt_rowLength {M : Nat} {f : Fin M × Fin M → Bool}
    (hf : Monotone f) (x y : Fin M) :
    f (x,y) = false ↔ x.val < rowLength f y := by
  constructor
  · intro hx
    have hsub : Finset.Iic x ⊆ rowZeros f y := by
      intro u hu
      rw [mem_rowZeros]
      have hux : u ≤ x := Finset.mem_Iic.mp hu
      have horder := hf (show (u,y) ≤ (x,y) from ⟨hux,le_rfl⟩)
      rw [hx] at horder
      have hb : ∀ b : Bool, b ≤ false → b = false := by decide
      exact hb _ horder
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    exact Nat.lt_of_succ_le hcard
  · intro hx
    by_contra hn
    have hxtrue : f (x,y) = true := by cases he : f (x,y) <;> simp_all
    have hsub : rowZeros f y ⊆ Finset.Iio x := by
      intro u hu
      rw [mem_rowZeros] at hu
      rw [Finset.mem_Iio]
      by_contra hux
      have hxu : x ≤ u := le_of_not_gt hux
      have horder := hf (show (x,y) ≤ (u,y) from ⟨hxu,le_rfl⟩)
      simp only [hxtrue,hu] at horder
      exact (show ¬ (true ≤ false) by decide) horder
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    exact Nat.not_lt_of_ge hcard hx

theorem true_iff_rowLength_le {M : Nat} {f : Fin M × Fin M → Bool}
    (hf : Monotone f) (x y : Fin M) :
    f (x,y) = true ↔ rowLength f y ≤ x.val := by
  have hb : ∀ b : Bool, b = true ↔ ¬ b = false := by decide
  rw [hb, false_iff_lt_rowLength hf, not_lt]

/-- The row lengths determine an increasing Boolean configuration uniquely. -/
theorem ext_of_rowLength_eq {M : Nat} {f g : Fin M × Fin M → Bool}
    (hf : Monotone f) (hg : Monotone g) (h : ∀ y, rowLength f y = rowLength g y) : f = g := by
  funext v
  have he : f (v.1,v.2) = false ↔ g (v.1,v.2) = false := by
    rw [false_iff_lt_rowLength hf, false_iff_lt_rowLength hg, h v.2]
  cases hfval : f v <;> cases hgval : g v <;> simp_all

@[simp] theorem rowLength_all_true {M : Nat} (y : Fin M) :
    rowLength (fun _ : Fin M × Fin M => true) y = 0 := by
  simp [rowLength,rowZeros]

@[simp] theorem rowLength_all_false {M : Nat} (y : Fin M) :
    rowLength (fun _ : Fin M × Fin M => false) y = M := by
  simp [rowLength,rowZeros]

/-- A single write leaves every other row's actual zero set unchanged. -/
theorem rowZeros_update_other_row {M : Nat} (f : Fin M × Fin M → Bool)
    (v : Fin M × Fin M) (b : Bool) (y : Fin M) (hy : y ≠ v.2) :
    rowZeros (Function.update f v b) y = rowZeros f y := by
  ext x
  have hxy : (x,y) ≠ v := fun he => hy (congrArg Prod.snd he)
  simp only [mem_rowZeros,Function.update_of_ne hxy]

theorem rowLength_update_other_row {M : Nat} (f : Fin M × Fin M → Bool)
    (v : Fin M × Fin M) (b : Bool) (y : Fin M) (hy : y ≠ v.2) :
    rowLength (Function.update f v b) y = rowLength f y := by
  unfold rowLength
  rw [rowZeros_update_other_row f v b y hy]

end MathResearchAnalysis.YoungRows


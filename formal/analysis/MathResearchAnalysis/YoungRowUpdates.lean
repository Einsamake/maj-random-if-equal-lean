module

public import MathResearchAnalysis.YoungRows
public import MathResearchAnalysis.MixedSquareCorners

set_option autoImplicit false

/-!
# Actual row changes under a single mixed-boundary corner flip

False cells are counted in the original finite row filters. A deletion of a
true corner inserts exactly one column in that row; a birth of a true corner
erases exactly one column. The updated row endpoints follow from the proved
shape invariant, so the formulas include boundary corners without exceptions.
No particle process, probability bound or recovery upper bound is assumed.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.YoungRowUpdates

open YoungRows

/-- A false write inserts its actual column into the affected row filter. -/
theorem rowZeros_write_false {M : Nat} (f : Fin M × Fin M → Bool) (x y : Fin M) :
    rowZeros (Function.update f (x,y) false) y = insert x (rowZeros f y) := by
  ext u
  by_cases hux : u = x
  · subst u
    simp only [mem_rowZeros,Function.update_self,Finset.mem_insert,true_or]
  · have hxy : (u,y) ≠ (x,y) := fun h => hux (congrArg Prod.fst h)
    simp only [mem_rowZeros,Function.update_of_ne hxy,Finset.mem_insert,hux,false_or]

/-- A true write erases its actual column from the affected row filter. -/
theorem rowZeros_write_true {M : Nat} (f : Fin M × Fin M → Bool) (x y : Fin M) :
    rowZeros (Function.update f (x,y) true) y = (rowZeros f y).erase x := by
  ext u
  by_cases hux : u = x
  · subst u
    simp
  · have hxy : (u,y) ≠ (x,y) := fun h => hux (congrArg Prod.fst h)
    rw [mem_rowZeros,Function.update_of_ne hxy,Finset.mem_erase,mem_rowZeros]
    exact ⟨fun h => ⟨hux,h⟩,fun h => h.2⟩

/-- This exact cardinality change needs no shape assumption. -/
theorem rowLength_write_false_of_true {M : Nat} (f : Fin M × Fin M → Bool) (x y : Fin M)
    (hxy : f (x,y) = true) :
    rowLength (Function.update f (x,y) false) y = rowLength f y + 1 := by
  unfold rowLength
  rw [rowZeros_write_false]
  apply Finset.card_insert_of_notMem
  intro hx
  have hfalse := (mem_rowZeros f x y).mp hx
  rw [hxy] at hfalse
  exact Bool.noConfusion hfalse

/-- The plus-one form retains the correct zero-row boundary in Nat. -/
theorem rowLength_write_true_of_false {M : Nat} (f : Fin M × Fin M → Bool) (x y : Fin M)
    (hxy : f (x,y) = false) :
    rowLength (Function.update f (x,y) true) y + 1 = rowLength f y := by
  unfold rowLength
  rw [rowZeros_write_true]
  exact Finset.card_erase_add_one ((mem_rowZeros f x y).mpr hxy)

/-- An actual removable corner, with its false mark, makes exactly this write. -/
theorem removable_cellUpdate_eq {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.removable f v) :
    MixedSquareModel.cellUpdate f v false = Function.update f v false := by
  unfold MixedSquareModel.cellUpdate
  rw [(MixedSquareCorners.rule_false_iff_of_true hf hc.1 false).mpr ⟨hc.2.1,hc.2.2,rfl⟩]

/-- An actual addable corner, with its true mark, makes exactly this write. -/
theorem addable_cellUpdate_eq {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.addable f v) :
    MixedSquareModel.cellUpdate f v true = Function.update f v true := by
  unfold MixedSquareModel.cellUpdate
  rw [(MixedSquareCorners.rule_true_iff_of_false hf hc.1 true).mpr ⟨hc.2.1,hc.2.2,rfl⟩]

theorem removable_rowZeros {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.removable f v) :
    rowZeros (MixedSquareModel.cellUpdate f v false) v.2 = insert v.1 (rowZeros f v.2) := by
  rw [removable_cellUpdate_eq hf hc]
  exact rowZeros_write_false f v.1 v.2

theorem addable_rowZeros {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.addable f v) :
    rowZeros (MixedSquareModel.cellUpdate f v true) v.2 = (rowZeros f v.2).erase v.1 := by
  rw [addable_cellUpdate_eq hf hc]
  exact rowZeros_write_true f v.1 v.2

theorem removable_rowLength {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.removable f v) :
    rowLength (MixedSquareModel.cellUpdate f v false) v.2 = rowLength f v.2 + 1 := by
  rw [removable_cellUpdate_eq hf hc]
  exact rowLength_write_false_of_true f v.1 v.2 hc.1

theorem addable_rowLength {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.addable f v) :
    rowLength (MixedSquareModel.cellUpdate f v true) v.2 + 1 = rowLength f v.2 := by
  rw [addable_cellUpdate_eq hf hc]
  exact rowLength_write_true_of_false f v.1 v.2 hc.1

/-- Every actual single write leaves all other row lengths unchanged. -/
theorem cellUpdate_other_row {n : Nat} (f : SquareSpin.Config n) (v : SquareTasks.Vertex n)
    (tie : Bool) (y : Fin (n+2)) (hy : y ≠ v.2) :
    rowLength (MixedSquareModel.cellUpdate f v tie) y = rowLength f y :=
  YoungRows.rowLength_update_other_row f v (MixedSquareModel.rule f v tie) y hy

/-- The removable cell is exactly the first true entry of its old row. -/
theorem removable_x_eq_rowLength {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.removable f v) :
    v.1.val = rowLength f v.2 := by
  have hold := (true_iff_rowLength_le hf v.1 v.2).mp hc.1
  have hnewMono := MixedSquareCorners.cellUpdate_monotone hf v false
  have hnewVal : MixedSquareModel.cellUpdate f v false v = false := by
    rw [removable_cellUpdate_eq hf hc,Function.update_self]
  have hnew := (false_iff_lt_rowLength hnewMono v.1 v.2).mp hnewVal
  rw [removable_rowLength hf hc] at hnew
  omega

/-- The addable cell is exactly the last false entry of its old row. -/
theorem addable_x_succ_eq_rowLength {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.addable f v) :
    v.1.val + 1 = rowLength f v.2 := by
  have hold := (false_iff_lt_rowLength hf v.1 v.2).mp hc.1
  have hnewMono := MixedSquareCorners.cellUpdate_monotone hf v true
  have hnewVal : MixedSquareModel.cellUpdate f v true v = true := by
    rw [addable_cellUpdate_eq hf hc,Function.update_self]
  have hnew := (true_iff_rowLength_le hnewMono v.1 v.2).mp hnewVal
  have hlength := addable_rowLength hf hc
  omega

end MathResearchAnalysis.YoungRowUpdates


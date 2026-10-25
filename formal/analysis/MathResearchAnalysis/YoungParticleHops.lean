module

public import MathResearchAnalysis.YoungParticles
public import MathResearchAnalysis.MixedSquareCorners

set_option autoImplicit false

/-!
# Every admissible adjacent empty-slot particle hop is a true mixed corner

Both finite-path endpoints and the real four-neighbour mixed boundary are
retained. Vacancy is the actual exclusion-hop condition, not a geometric or
probabilistic premise. No clock or rate identity is asserted in this module.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.YoungParticleHops

open YoungParticles (positionNat)
open YoungRows (rowLength)
open InfiniteGridModel (north east south west)

/-- An empty right target forces a strict white-row gap below, if that row exists. -/
theorem right_hop_south_gap {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f)
    (r : Fin M) (hfree : ∀ s : Fin M, positionNat f s ≠ positionNat f r + 1)
    (y : Fin M) (hy : y.val+1 = r.rev.val) : rowLength f r.rev < rowLength f y := by
  have hyorder : y ≤ r.rev := by change y.val ≤ r.rev.val; omega
  have hl := YoungRows.rowLength_antitone hf hyorder
  by_contra hn
  have heq : rowLength f y = rowLength f r.rev := by omega
  have hr := r.isLt
  have hyr := y.isLt
  have hrr := Fin.val_rev r
  have hpos : positionNat f y.rev = positionNat f r+1 := by
    unfold positionNat
    rw [Fin.rev_rev,Fin.val_rev]
    omega
  exact hfree y.rev hpos

/-- The finite right endpoint and actual vacant target rule out a full row. -/
theorem right_hop_rowLength_lt_side {M : Nat} {f : Fin M × Fin M → Bool}
    (hf : Monotone f) (r : Fin M) (hend : positionNat f r+1 < 2*M)
    (hfree : ∀ s : Fin M, positionNat f s ≠ positionNat f r+1) : rowLength f r.rev < M := by
  have hl := YoungRows.rowLength_le_side f r.rev
  have hr := r.isLt
  have hrr := Fin.val_rev r
  by_cases hy0 : r.rev.val = 0
  · unfold positionNat at hend
    omega
  · let y : Fin M := ⟨r.rev.val-1,by have h := r.rev.isLt; omega⟩
    have hy : y.val+1 = r.rev.val := by dsimp [y]; omega
    exact (right_hop_south_gap hf r hfree y hy).trans_le (YoungRows.rowLength_le_side f y)

/-- An empty left target forces a strict white-row gap above, if that row exists. -/
theorem left_hop_north_gap {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f)
    (r : Fin M) (hfree : ∀ s : Fin M, positionNat f s+1 ≠ positionNat f r)
    (y : Fin M) (hy : r.rev.val+1 = y.val) : rowLength f y < rowLength f r.rev := by
  have hyorder : r.rev ≤ y := by change r.rev.val ≤ y.val; omega
  have hl := YoungRows.rowLength_antitone hf hyorder
  by_contra hn
  have heq : rowLength f y = rowLength f r.rev := by omega
  have hr := r.isLt
  have hyr := y.isLt
  have hrr := Fin.val_rev r
  have hpos : positionNat f y.rev+1 = positionNat f r := by
    unfold positionNat
    rw [Fin.rev_rev,Fin.val_rev]
    omega
  exact hfree y.rev hpos

/-- The finite left endpoint and actual vacant target rule out an empty row. -/
theorem left_hop_rowLength_pos {M : Nat} {f : Fin M × Fin M → Bool}
    (hf : Monotone f) (r : Fin M) (hstart : 0 < positionNat f r)
    (hfree : ∀ s : Fin M, positionNat f s+1 ≠ positionNat f r) : 0 < rowLength f r.rev := by
  have hr := r.isLt
  have hrr := Fin.val_rev r
  by_cases hy : r.rev.val+1 < M
  · let y : Fin M := ⟨r.rev.val+1,hy⟩
    have hgap := left_hop_north_gap hf r hfree y (by rfl)
    omega
  · unfold positionNat at hstart
    omega

/-- An exact row endpoint and a strict southern gap give the actual mixed corner. -/
theorem removable_of_row_lengths {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (x y : Fin (n+2)) (hx : x.val = rowLength f y)
    (hbelow : ∀ z : Fin (n+2), z.val+1 = y.val → x.val < rowLength f z) :
    MixedSquareCorners.removable f (x,y) := by
  refine ⟨(YoungRows.true_iff_rowLength_le hf x y).mpr (by omega),?_,?_⟩
  · by_cases hy0 : y.val = 0
    · apply MixedSquareModel.extend_low n f _
      right
      dsimp [south,SquareGridEmbedding.embed]
      omega
    · let z : Fin (n+2) := ⟨y.val-1,by have h := y.isLt; omega⟩
      have hz : z.val+1 = y.val := by dsimp [z]; omega
      have he : south (SquareGridEmbedding.embed n (x,y)) = SquareGridEmbedding.embed n (x,z) := by
        apply Prod.ext
        · rfl
        · dsimp [south,SquareGridEmbedding.embed,z]
          omega
      rw [he,MixedSquareModel.extend_embed]
      exact (YoungRows.false_iff_lt_rowLength hf x z).mpr (hbelow z hz)
  · by_cases hx0 : x.val = 0
    · apply MixedSquareModel.extend_low n f _
      left
      dsimp [west,SquareGridEmbedding.embed]
      omega
    · let u : Fin (n+2) := ⟨x.val-1,by have h := x.isLt; omega⟩
      have he : west (SquareGridEmbedding.embed n (x,y)) = SquareGridEmbedding.embed n (u,y) := by
        apply Prod.ext
        · dsimp [west,SquareGridEmbedding.embed,u]
          omega
        · rfl
      rw [he,MixedSquareModel.extend_embed]
      apply (YoungRows.false_iff_lt_rowLength hf u y).mpr
      dsimp [u]
      omega

/-- The last white entry and a strict northern gap give the actual mixed corner. -/
theorem addable_of_row_lengths {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (x y : Fin (n+2)) (hx : x.val+1 = rowLength f y)
    (habove : ∀ z : Fin (n+2), y.val+1 = z.val → rowLength f z ≤ x.val) :
    MixedSquareCorners.addable f (x,y) := by
  refine ⟨(YoungRows.false_iff_lt_rowLength hf x y).mpr (by omega),?_,?_⟩
  · by_cases hy : y.val+1 < n+2
    · let z : Fin (n+2) := ⟨y.val+1,hy⟩
      have he : north (SquareGridEmbedding.embed n (x,y)) = SquareGridEmbedding.embed n (x,z) := by
        apply Prod.ext
        · rfl
        · dsimp [north,SquareGridEmbedding.embed,z]
      rw [he,MixedSquareModel.extend_embed]
      exact (YoungRows.true_iff_rowLength_le hf x z).mpr (habove z rfl)
    · apply MixedSquareModel.extend_high n f _
      · dsimp [north,SquareGridEmbedding.embed]; omega
      · dsimp [north,SquareGridEmbedding.embed]; omega
      · right
        dsimp [north,SquareGridEmbedding.embed]
        omega
  · by_cases hxlt : x.val+1 < n+2
    · let u : Fin (n+2) := ⟨x.val+1,hxlt⟩
      have he : east (SquareGridEmbedding.embed n (x,y)) = SquareGridEmbedding.embed n (u,y) := by
        apply Prod.ext
        · dsimp [east,SquareGridEmbedding.embed,u]
        · rfl
      rw [he,MixedSquareModel.extend_embed]
      apply (YoungRows.true_iff_rowLength_le hf u y).mpr
      dsimp [u]
      omega
    · apply MixedSquareModel.extend_high n f _
      · dsimp [east,SquareGridEmbedding.embed]; omega
      · dsimp [east,SquareGridEmbedding.embed]; omega
      · left
        dsimp [east,SquareGridEmbedding.embed]
        omega

/-- Every legal right hop is covered by a genuine occupied corner of the square. -/
theorem right_hop_has_removable {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (r : Fin (n+2)) (hend : positionNat f r+1 < 2*(n+2))
    (hfree : ∀ s : Fin (n+2), positionNat f s ≠ positionNat f r+1) :
    ∃ v : SquareTasks.Vertex n, v.2 = r.rev ∧ v.1.val = rowLength f r.rev ∧
      MixedSquareCorners.removable f v := by
  let x : Fin (n+2) := ⟨rowLength f r.rev,right_hop_rowLength_lt_side hf r hend hfree⟩
  refine ⟨(x,r.rev),rfl,rfl,?_⟩
  apply removable_of_row_lengths hf x r.rev rfl
  intro z hz
  exact right_hop_south_gap hf r hfree z hz

/-- Every legal left hop is covered by a genuine vacant corner of the square. -/
theorem left_hop_has_addable {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (r : Fin (n+2)) (hstart : 0 < positionNat f r)
    (hfree : ∀ s : Fin (n+2), positionNat f s+1 ≠ positionNat f r) :
    ∃ v : SquareTasks.Vertex n, v.2 = r.rev ∧ v.1.val+1 = rowLength f r.rev ∧
      MixedSquareCorners.addable f v := by
  have hpos := left_hop_rowLength_pos hf r hstart hfree
  have hbound := YoungRows.rowLength_le_side f r.rev
  let x : Fin (n+2) := ⟨rowLength f r.rev-1,by omega⟩
  have hx : x.val+1 = rowLength f r.rev := by dsimp [x]; omega
  refine ⟨(x,r.rev),rfl,hx,?_⟩
  apply addable_of_row_lengths hf x r.rev hx
  intro z hz
  have hgap := left_hop_north_gap hf r hfree z hz
  omega

end MathResearchAnalysis.YoungParticleHops



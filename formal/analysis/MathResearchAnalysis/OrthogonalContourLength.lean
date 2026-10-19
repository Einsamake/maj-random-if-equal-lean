module
public import MathResearchAnalysis.OrthogonalBoundaryCurve
public import MathResearchAnalysis.GridContourLength
set_option autoImplicit false
/-! Full Euclidean extended variation of the actual general contour; every monotone finite partition is covered by eVariationOn. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.OrthogonalContourLength
open GridCellBoundary GridBoundarySegments OrthogonalBoundaryCycle OrthogonalBoundaryPolygon OrthogonalBoundaryCurve
open GridContourLength (EuclideanPlane unitEuclidean unitSegment unitSegment_isometry isometry_variation)
open scoped BigOperators
def unitTrace (R : Region) (n : Nat) (t : Real) : EuclideanPlane := unitEuclidean (trace R n t)

theorem unitTrace_piece (R : Region) (i : Index R) :
    Set.EqOn (unitTrace R (perimeter R.val))
      (fun t => unitSegment (facetAt R i).val (t - (i.val : Real)))
      (Set.Icc (i.val : Real) ((i.val : Real) + 1)) := by
  intro t ht
  have h := trace_piece_final R i (t - (i.val : Real))
    (sub_nonneg.mpr ht.1) (by linarith [ht.2])
  have ht' : (i.val : Real) + (t - (i.val : Real)) = t := by ring
  rw [ht'] at h
  exact congrArg unitEuclidean h

theorem unitTrace_piece_variation (R : Region) (i : Index R) :
    eVariationOn (unitTrace R (perimeter R.val))
      (Set.Icc (i.val : Real) ((i.val : Real) + 1)) = 1 := by
  rw [eVariationOn.congr (unitTrace_piece R i)]
  have htranslation : Isometry (fun t : Real => t - (i.val : Real)) := by
    apply Isometry.of_dist_eq
    intro t u
    simp only [Real.dist_eq]
    congr 1
    ring
  have hiso : Isometry (fun t : Real => unitSegment (facetAt R i).val (t - (i.val : Real))) :=
    (unitSegment_isometry _).comp htranslation
  rw [isometry_variation _ hiso]
  norm_num

theorem unitTrace_length (R : Region) :
    eVariationOn (unitTrace R (perimeter R.val))
      (Set.Icc 0 ((perimeter R.val : Nat) : Real)) = (perimeter R.val : Nat) := by
  calc
    _ = ∑ i ∈ Finset.range (perimeter R.val),
        eVariationOn (unitTrace R (perimeter R.val)) (Set.Icc (i : Real) ((i+1 : Nat) : Real)) := by
      have h := eVariationOn.sum' (unitTrace R (perimeter R.val))
        (I := fun n : Nat => (n : Real)) (by intro a b hab; change (a : Real) ≤ (b : Real); exact_mod_cast hab)
        (n := perimeter R.val)
      simpa only [Nat.cast_zero] using h.symm
    _ = ∑ i ∈ Finset.range (perimeter R.val), (1 : ENNReal) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := unitTrace_piece_variation R ⟨i, Finset.mem_range.mp hi⟩
      simpa only [Nat.cast_add, Nat.cast_one] using h
    _ = (perimeter R.val : Nat) := by simp

end MathResearchAnalysis.OrthogonalContourLength

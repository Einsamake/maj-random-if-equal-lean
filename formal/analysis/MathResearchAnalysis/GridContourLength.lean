module

public import MathResearchAnalysis.ClippedBoundaryCurve
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.EMetricSpace.BoundedVariation

set_option autoImplicit false

/-!
# Euclidean arc length of the actual unit-cell contour

The target is the genuine Euclidean two-dimensional norm, not the product
maximum metric. Each actual unit side is an isometry from its real parameter.
The extended variation (the supremum over all monotone finite partitions) is
then added over every actual side of the explicit traversal.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.GridContourLength

open GridCellBoundary GridBoundarySegments ClippedBoundaryCycle ClippedBoundaryPolygon
open ClippedBoundaryCurve

abbrev EuclideanPlane := EuclideanSpace Real (Fin 2)

def unitEuclidean (p : Plane) : EuclideanPlane := !₂[p.1/2, p.2/2]

def unitSegment (e : HalfEdge) (t : Real) : EuclideanPlane :=
  unitEuclidean (segmentPoint e t)

def unitTrace (L n : Nat) (t : Real) : EuclideanPlane := unitEuclidean (trace L n t)

theorem unitEuclidean_dist_sq (p q : Plane) :
    dist (unitEuclidean p) (unitEuclidean q) ^ 2 =
      (p.1/2 - q.1/2)^2 + (p.2/2 - q.2/2)^2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [unitEuclidean, Real.dist_eq]

theorem unitSegment_isometry (e : HalfEdge) : Isometry (unitSegment e) := by
  apply Isometry.of_dist_eq
  intro t u
  have hsq : dist (unitSegment e t) (unitSegment e u)^2 = (t-u)^2 := by
    rw [unitSegment, unitSegment, unitEuclidean_dist_sq]
    rcases e with ⟨v,d⟩
    fin_cases d <;> simp only [segmentPoint_north, segmentPoint_east,
      segmentPoint_south, segmentPoint_west] <;> ring
  rw [Real.dist_eq]
  nlinarith [dist_nonneg (x := unitSegment e t) (y := unitSegment e u),
    abs_nonneg (t-u), sq_abs (t-u)]

theorem isometry_variation (f : Real → EuclideanPlane) (hf : Isometry f) (a b : Real) :
    eVariationOn f (Set.Icc a b) = ENNReal.ofReal (b-a) := by
  rw [← eVariationOn_id_Icc a b]
  simp only [eVariationOn, hf.edist_eq, id_eq]

theorem unitTrace_piece (L : Nat) (i : Index L) :
    Set.EqOn (unitTrace L (8 * L + 4))
      (fun t => unitSegment (facetAt L i).val (t - (i.val : Real)))
      (Set.Icc (i.val : Real) ((i.val : Real) + 1)) := by
  intro t ht
  have h := trace_piece_final L i (t - (i.val : Real))
    (sub_nonneg.mpr ht.1) (by linarith [ht.2])
  have ht' : (i.val : Real) + (t - (i.val : Real)) = t := by ring
  rw [ht'] at h
  exact congrArg unitEuclidean h

theorem unitTrace_piece_variation (L : Nat) (i : Index L) :
    eVariationOn (unitTrace L (8 * L + 4))
      (Set.Icc (i.val : Real) ((i.val : Real) + 1)) = 1 := by
  rw [eVariationOn.congr (unitTrace_piece L i)]
  have htranslation : Isometry (fun t : Real => t - (i.val : Real)) := by
    apply Isometry.of_dist_eq
    intro t u
    simp only [Real.dist_eq]
    congr 1
    ring
  have hiso : Isometry (fun t : Real => unitSegment (facetAt L i).val (t - (i.val : Real))) :=
    (unitSegment_isometry _).comp htranslation
  rw [isometry_variation _ hiso]
  norm_num

theorem unitTrace_length (L : Nat) :
    eVariationOn (unitTrace L (8 * L + 4))
      (Set.Icc 0 ((8 * L + 4 : Nat) : Real)) = (8 * L + 4 : Nat) := by
  calc
    _ = ∑ i ∈ Finset.range (8 * L + 4),
        eVariationOn (unitTrace L (8 * L + 4)) (Set.Icc (i : Real) ((i+1 : Nat) : Real)) := by
      have h := eVariationOn.sum' (unitTrace L (8 * L + 4))
        (I := fun n : Nat => (n : Real)) (by intro a b hab; change (a : Real) ≤ (b : Real); exact_mod_cast hab)
        (n := 8 * L + 4)
      simpa only [Nat.cast_zero] using h.symm
    _ = ∑ i ∈ Finset.range (8 * L + 4), (1 : ENNReal) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := unitTrace_piece_variation L ⟨i, Finset.mem_range.mp hi⟩
      simpa only [Nat.cast_add, Nat.cast_one] using h
    _ = (8 * L + 4 : Nat) := by simp

end MathResearchAnalysis.GridContourLength

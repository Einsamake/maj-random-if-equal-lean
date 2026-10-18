module

public import MathResearchAnalysis.ClippedBoundaryIncidence
public import MathResearchAnalysis.ClippedBoundaryConnectivity
public import MathResearchAnalysis.GridBoundaryPermutation

set_option autoImplicit false

/-!
# One orbit covering the entire actual initial boundary

The successor permutation is constructed from the actual source and target
maps. Every half-edge is moved, all actual half-edges lie in the same orbit,
and its order is the actual facet count. This is a discrete single-contour
certificate, not yet the frontier/continuous simple-curve bridge.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClippedBoundaryCycle

open GridCellBoundary ClippedBoundaryPerimeter

abbrev Edges (L : Nat) := GridBoundaryPermutation.Edges (ClippedDiamondGeometry.clippedDomain L)

def successor (L : Nat) : Equiv.Perm (Edges L) :=
  GridBoundaryPermutation.succPerm _ (ClippedBoundaryIncidence.no_checkerboard L)

def anchor (L : Nat) : Edges L :=
  ⟨facet L (0, 0), facet_mem_boundary L (0, 0)
    ((mem_facetIndices L (0, 0)).mpr (by simp))⟩

theorem successor_source (L : Nat) (e : Edges L) :
    source (successor L e).val = target e.val :=
  GridBoundaryPermutation.source_succ _ _ e

theorem successor_ne_self (L : Nat) (e : Edges L) : successor L e ≠ e :=
  GridBoundaryPermutation.succ_ne_self _ _ e

theorem sameCycle_of_boundary_path (L : Nat) (e f : HalfEdge)
    (he : e ∈ boundary (ClippedDiamondGeometry.clippedDomain L))
    (hf : f ∈ boundary (ClippedDiamondGeometry.clippedDomain L))
    (h : ClippedBoundaryConnectivity.Path L e f) :
    (successor L).SameCycle ⟨e, he⟩ ⟨f, hf⟩ := by
  revert hf
  induction h with
  | refl =>
      intro hf
      exact Equiv.Perm.SameCycle.refl _ _
  | @tail b c hab hbc ih =>
      intro hf
      exact (ih hbc.1).trans
        (GridBoundaryPermutation.sameCycle_of_touch _
          (ClippedBoundaryIncidence.no_checkerboard L)
          (e := ⟨b, hbc.1⟩) (f := ⟨c, hf⟩) hbc.2.2)

/-- All actual boundary facets belong to the orbit, including any proposed fixed point. -/
theorem sameCycle_all (L : Nat) (hL : 1 ≤ L) (e f : Edges L) :
    (successor L).SameCycle e f :=
  sameCycle_of_boundary_path L e.val f.val e.property f.property
    (ClippedBoundaryConnectivity.boundary_path_between L hL e.val f.val e.property f.property)

theorem isCycle (L : Nat) (hL : 1 ≤ L) : (successor L).IsCycle :=
  ⟨anchor L, successor_ne_self L _, fun {e} _ => sameCycle_all L hL _ e⟩

theorem support_eq_univ (L : Nat) : (successor L).support = Finset.univ := by
  ext e
  simp [Equiv.Perm.mem_support, successor_ne_self]

theorem card_edges (L : Nat) : Fintype.card (Edges L) = 8 * L + 4 := by
  change Fintype.card ↥(boundary (ClippedDiamondGeometry.clippedDomain L)) = _
  rw [Fintype.card_coe, boundary_card]
  omega

theorem orderOf_successor (L : Nat) (hL : 1 ≤ L) :
    orderOf (successor L) = 8 * L + 4 := by
  rw [(isCycle L hL).orderOf, support_eq_univ, Finset.card_univ, card_edges]

theorem exists_bounded_pow (L : Nat) (hL : 1 ≤ L) (e f : Edges L) :
    ∃ n < 8 * L + 4, ((successor L) ^ n) e = f := by
  have h := (sameCycle_all L hL e f).exists_pow_eq'
  rwa [orderOf_successor L hL] at h

/-- The cycle enumerates every real facet exactly once before returning. -/
theorem enumeration_bijective (L : Nat) (hL : 1 ≤ L) (e : Edges L) :
    Function.Bijective (fun n : Fin (8 * L + 4) => ((successor L) ^ n.val) e) := by
  constructor
  · intro i j hij
    apply Fin.ext
    have hp : (successor L) ^ i.val = (successor L) ^ j.val :=
      (isCycle L hL).pow_eq_pow_iff.mpr ⟨e, successor_ne_self L e, hij⟩
    apply pow_injOn_Iio_orderOf (x := successor L)
    · change i.val < orderOf (successor L)
      rw [orderOf_successor L hL]
      exact i.isLt
    · change j.val < orderOf (successor L)
      rw [orderOf_successor L hL]
      exact j.isLt
    · exact hp
  · intro f
    obtain ⟨n, hn, hnf⟩ := exists_bounded_pow L hL e f
    exact ⟨⟨n, hn⟩, hnf⟩

theorem vertex_enumeration_injective (L : Nat) (hL : 1 ≤ L) (e : Edges L) :
    Function.Injective (fun n : Fin (8 * L + 4) =>
      source (((successor L) ^ n.val) e).val) := by
  intro i j hij
  have heq := ClippedBoundaryIncidence.source_injective_on_boundary L
    (((successor L) ^ i.val) e).property
    (((successor L) ^ j.val) e).property hij
  exact (enumeration_bijective L hL e).1 (Subtype.ext heq)

theorem returns_after_perimeter (L : Nat) (hL : 1 ≤ L) (e : Edges L) :
    ((successor L) ^ (8 * L + 4)) e = e := by
  rw [← orderOf_successor L hL, pow_orderOf_eq_one]
  rfl

theorem consecutive_endpoints (L : Nat) (e : Edges L) (n : Nat) :
    source (((successor L) ^ (n + 1)) e).val =
      target (((successor L) ^ n) e).val := by
  simpa only [pow_succ', Equiv.Perm.mul_apply] using
    successor_source L (((successor L) ^ n) e)

end MathResearchAnalysis.ClippedBoundaryCycle

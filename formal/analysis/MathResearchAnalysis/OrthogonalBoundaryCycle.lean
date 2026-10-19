module
public import MathResearchAnalysis.OrthogonalBoundaryConnectivity
set_option autoImplicit false
/-! A genuine single successor cycle for finite nonempty column-convex connected regions with no checkerboard vertices. The input subtype stores only discrete shape conditions; the single orbit and its enumeration are proved. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.OrthogonalBoundaryCycle
open GridCellBoundary
open OrthogonalGridConvexity

abbrev Region := {S : Finset Site // ColumnConvex S ∧ FourConnected S ∧
  GridBoundaryIncidence.NoCheckerboard S ∧ S.Nonempty}

def ofOrthogonal (S : Finset Site) (hr : RowConvex S) (hc : ColumnConvex S)
    (hconn : FourConnected S) (hne : S.Nonempty) : Region :=
  ⟨S,hc,hconn,rowConvex_fourConnected_noCheckerboard S hr hconn,hne⟩

abbrev Edges (R : Region) := GridBoundaryPermutation.Edges R.val

def successor (R : Region) : Equiv.Perm (Edges R) :=
  GridBoundaryPermutation.succPerm R.val R.property.2.2.1

theorem boundary_nonempty (R : Region) : (boundary R.val).Nonempty := by
  obtain ⟨v,hv⟩ := R.property.2.2.2
  obtain ⟨u,hu,_⟩ := OrthogonalPerimeter.north_endpoint_exists R.val (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  exact ⟨(u,0),(mem_boundary_north R.val u).mpr (Finset.mem_filter.mp hu)⟩

def anchor (R : Region) : Edges R := ⟨(boundary_nonempty R).choose,(boundary_nonempty R).choose_spec⟩

theorem perimeter_pos (R : Region) : 0 < perimeter R.val := Finset.card_pos.mpr (boundary_nonempty R)

theorem successor_source (R : Region) (e : Edges R) :
    source (successor R e).val = target e.val := GridBoundaryPermutation.source_succ _ _ e

theorem successor_ne_self (R : Region) (e : Edges R) : successor R e ≠ e :=
  GridBoundaryPermutation.succ_ne_self _ _ e

theorem sameCycle_of_boundary_path (R : Region) (e f : HalfEdge)
    (he : e ∈ boundary R.val) (hf : f ∈ boundary R.val)
    (h : OrthogonalBoundaryConnectivity.Path R.val e f) :
    (successor R).SameCycle ⟨e,he⟩ ⟨f,hf⟩ := by
  revert hf
  induction h with
  | refl => intro hf; exact Equiv.Perm.SameCycle.refl _ _
  | @tail b c hab hbc ih =>
    intro hf
    exact (ih hbc.1).trans (GridBoundaryPermutation.sameCycle_of_touch _ R.property.2.2.1
      (e := ⟨b,hbc.1⟩) (f := ⟨c,hf⟩) hbc.2.2)

theorem sameCycle_all (R : Region) (e f : Edges R) : (successor R).SameCycle e f :=
  sameCycle_of_boundary_path R e.val f.val e.property f.property
    (OrthogonalBoundaryConnectivity.boundary_path_between R.property.1 R.property.2.1 e.property f.property)

theorem isCycle (R : Region) : (successor R).IsCycle :=
  ⟨anchor R,successor_ne_self R _,fun {e} _ => sameCycle_all R _ e⟩

theorem support_eq_univ (R : Region) : (successor R).support = Finset.univ := by
  ext e
  simp [Equiv.Perm.mem_support,successor_ne_self]

theorem card_edges (R : Region) : Fintype.card (Edges R) = perimeter R.val := Fintype.card_coe _

theorem orderOf_successor (R : Region) : orderOf (successor R) = perimeter R.val := by
  rw [(isCycle R).orderOf,support_eq_univ,Finset.card_univ,card_edges]

theorem exists_bounded_pow (R : Region) (e f : Edges R) :
    ∃ n < perimeter R.val, ((successor R)^n) e = f := by
  have h := (sameCycle_all R e f).exists_pow_eq'
  rwa [orderOf_successor R] at h

theorem enumeration_bijective (R : Region) (e : Edges R) :
    Function.Bijective (fun n : Fin (perimeter R.val) => ((successor R)^n.val) e) := by
  constructor
  · intro i j hij
    apply Fin.ext
    have hp : (successor R)^i.val = (successor R)^j.val :=
      (isCycle R).pow_eq_pow_iff.mpr ⟨e,successor_ne_self R e,hij⟩
    exact pow_injOn_Iio_orderOf (x := successor R)
      (by change i.val < orderOf (successor R); rw [orderOf_successor R]; exact i.isLt)
      (by change j.val < orderOf (successor R); rw [orderOf_successor R]; exact j.isLt) hp
  · intro f
    obtain ⟨n,hn,hnf⟩ := exists_bounded_pow R e f
    exact ⟨⟨n,hn⟩,hnf⟩

theorem vertex_enumeration_injective (R : Region) (e : Edges R) :
    Function.Injective (fun n : Fin (perimeter R.val) => source (((successor R)^n.val) e).val) := by
  intro i j hij
  have heq := (GridBoundaryPermutation.source_eq_source_iff R.val R.property.2.2.1 _ _).mp hij
  exact (enumeration_bijective R e).1 heq

theorem returns_after_perimeter (R : Region) (e : Edges R) :
    ((successor R)^(perimeter R.val)) e = e := by
  rw [← orderOf_successor R,pow_orderOf_eq_one]
  rfl

theorem consecutive_endpoints (R : Region) (e : Edges R) (n : Nat) :
    source (((successor R)^(n+1)) e).val = target (((successor R)^n) e).val := by
  simpa only [pow_succ',Equiv.Perm.mul_apply] using successor_source R (((successor R)^n) e)
end MathResearchAnalysis.OrthogonalBoundaryCycle

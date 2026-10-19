module

public import MathResearchAnalysis.OrthogonalBoundaryPolygon
public import MathResearchAnalysis.ClippedBoundaryCurve
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

/-!
# Continuous simple traversal of every actual general boundary segment

The finite polygon is traversed by an explicitly glued piecewise affine map.
The map is continuous, closes after the actual perimeter, and is injective on
its half-open parameter interval. The occupied-region frontier identification
is a separate result and is not assumed here.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.OrthogonalBoundaryCurve

open GridCellBoundary GridBoundarySegments OrthogonalBoundaryCycle OrthogonalBoundaryPolygon

abbrev edgeAt (R : Region) (n : Nat) : Edges R := ((successor R) ^ n) (anchor R)

def pointAt (R : Region) (n : Nat) : Plane := realSite (source (edgeAt R n).val)

def trace (R : Region) : Nat → Real → Plane
  | 0, _ => pointAt R 0
  | n + 1, t => if t ≤ (n : Real) then trace R n t
      else segmentPoint (edgeAt R n).val (t - (n : Real))

theorem trace_endpoint (R : Region) (n : Nat) : trace R n (n : Real) = pointAt R n := by
  cases n with
  | zero => rfl
  | succ n =>
      have hlt : (n : Real) < ((n + 1 : Nat) : Real) := by exact_mod_cast Nat.lt_succ_self n
      rw [trace, ite_eq_right (not_le.mpr hlt)]
      have hsub : ((n + 1 : Nat) : Real) - (n : Real) = 1 := by push_cast; ring
      rw [hsub, segmentPoint_one]
      exact congrArg realSite (consecutive_endpoints R (anchor R) n).symm

theorem trace_of_le (R : Region) {n m : Nat} (hnm : n ≤ m) {t : Real}
    (ht : t ≤ (n : Real)) : trace R m t = trace R n t := by
  induction m with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      rfl
  | succ m ih =>
      by_cases hn : n ≤ m
      · have hle : t ≤ (m : Real) := ht.trans (by exact_mod_cast hn)
        rw [trace, ite_eq_left hle]
        exact ih hn
      · have hn : n = m + 1 := by omega
        subst n
        rfl

theorem trace_piece (R : Region) (n : Nat) {t : Real} (ht : (n : Real) ≤ t) :
    trace R (n + 1) t = segmentPoint (edgeAt R n).val (t - (n : Real)) := by
  rw [trace]
  split_ifs with h
  · have heq : t = (n : Real) := le_antisymm h ht
    subst t
    rw [trace_endpoint, sub_self, segmentPoint_zero]
    rfl
  · rfl

theorem trace_piece_final (R : Region) (i : Index R) (u : Real)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    trace R (perimeter R.val) ((i.val : Real) + u) = segmentPoint (facetAt R i).val u := by
  rw [trace_of_le R (n := i.val + 1) (m := perimeter R.val) (by omega)
    (by push_cast; linarith)]
  rw [trace_piece R i.val (by linarith)]
  have hsub : (i.val : Real) + u - (i.val : Real) = u := by ring
  rw [hsub]
  rfl

theorem continuous_trace (R : Region) (n : Nat) : Continuous (trace R n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have hc : Continuous (fun t : Real => segmentPoint (edgeAt R n).val (t - (n : Real))) := by
        unfold segmentPoint
        fun_prop
      apply ih.if_le hc continuous_id continuous_const
      intro t ht
      change t = (n : Real) at ht
      subst t
      rw [trace_endpoint, sub_self, segmentPoint_zero]
      rfl

theorem trace_start (R : Region) (n : Nat) : trace R n 0 = pointAt R 0 := by
  rw [trace_of_le R (n := 0) (m := n) (Nat.zero_le n) (by norm_num)]
  rfl

theorem trace_closed (R : Region)  :
    trace R (perimeter R.val) (perimeter R.val : Nat) = trace R (perimeter R.val) 0 := by
  rw [trace_endpoint, trace_start]
  unfold pointAt edgeAt
  rw [returns_after_perimeter R]
  rfl

theorem exists_piece (R : Region) {t : Real} (ht : t ∈ Set.Ico 0 ((perimeter R.val : Nat) : Real)) :
    ∃ i : Index R, ∃ u : Real, 0 ≤ u ∧ u < 1 ∧ t = (i.val : Real) + u := by
  have hn : Nat.floor t < perimeter R.val := (Nat.floor_lt ht.1).mpr ht.2
  refine ⟨⟨Nat.floor t, hn⟩, t - (Nat.floor t : Real), ?_, ?_, ?_⟩
  · exact sub_nonneg.mpr (Nat.floor_le ht.1)
  · have h := Nat.lt_floor_add_one t
    linarith
  · dsimp
    ring

theorem trace_injective_Ico (R : Region)  :
    Set.InjOn (trace R (perimeter R.val)) (Set.Ico 0 ((perimeter R.val : Nat) : Real)) := by
  intro t ht s hs heq
  obtain ⟨i, u, hu0, hu1, rfl⟩ := exists_piece R ht
  obtain ⟨j, v, hv0, hv1, rfl⟩ := exists_piece R hs
  rw [trace_piece_final R i u hu0 hu1.le,
    trace_piece_final R j v hv0 hv1.le] at heq
  by_cases hij : i = j
  · subst j
    have huv := ClippedBoundaryCurve.segmentPoint_injective (facetAt R i).val heq
    rw [huv]
  · have hne : (facetAt R i).val ≠ (facetAt R j).val := by
      intro h
      exact hij ((facetAt_bijective R).1 (Subtype.ext h))
    have h := boundary_segments_intersect_only_endpoints
      (facetAt R i).property (facetAt R j).property hne
      (p := segmentPoint (facetAt R i).val u)
      ⟨u, hu0, hu1.le, rfl⟩ ⟨v, hv0, hv1.le, heq⟩
    have hu : u = 0 := by
      rcases h.1 with h | h
      · exact ClippedBoundaryCurve.segmentPoint_injective _ (h.trans (segmentPoint_zero _).symm)
      · have h' : u = 1 := ClippedBoundaryCurve.segmentPoint_injective _ (h.trans (segmentPoint_one _).symm)
        exact False.elim (hu1.ne h')
    have hv : v = 0 := by
      rcases h.2 with h | h
      · exact ClippedBoundaryCurve.segmentPoint_injective _ (heq.symm.trans (h.trans (segmentPoint_zero _).symm))
      · have h' : v = 1 := ClippedBoundaryCurve.segmentPoint_injective _
          (heq.symm.trans (h.trans (segmentPoint_one _).symm))
        exact False.elim (hv1.ne h')
    have hvertices : vertex R i = vertex R j := by
      simpa only [hu, hv, segmentPoint_zero, vertex] using heq
    exact False.elim (hij (vertex_injective R hvertices))

theorem trace_image (R : Region)  :
    trace R (perimeter R.val) '' Set.Icc 0 ((perimeter R.val : Nat) : Real) =
      (polygon R).boundary Real := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    apply (OrthogonalBoundaryPolygon.mem_boundary_iff R _).mpr
    by_cases heq : t = ((perimeter R.val : Nat) : Real)
    · subst t
      rw [trace_closed R, trace_start]
      exact ⟨(anchor R).val, (anchor R).property, source_mem_closedSegment _⟩
    · obtain ⟨i, u, hu0, hu1, rfl⟩ := exists_piece R ⟨ht.1, lt_of_le_of_ne ht.2 heq⟩
      rw [trace_piece_final R i u hu0 hu1.le]
      exact ⟨(facetAt R i).val, (facetAt R i).property, u, hu0, hu1.le, rfl⟩
  · intro hp
    obtain ⟨e, he, u, hu0, hu1, rfl⟩ :=
      (OrthogonalBoundaryPolygon.mem_boundary_iff R p).mp hp
    obtain ⟨i, hi⟩ := (facetAt_bijective R).2 ⟨e, he⟩
    have hie : (facetAt R i).val = e := congrArg Subtype.val hi
    refine ⟨(i.val : Real) + u, ⟨by positivity, ?_⟩, ?_⟩
    · have hiR : (i.val : Real) + 1 ≤ ((perimeter R.val : Nat) : Real) := by
        exact_mod_cast i.isLt
      linarith
    · rw [trace_piece_final R i u hu0 hu1, hie]

/-- Traversal normalized to the usual unit parameter interval. -/
def curve (R : Region) (t : Real) : Plane :=
  trace R (perimeter R.val) (((perimeter R.val : Nat) : Real) * t)

theorem continuous_curve (R : Region) : Continuous (curve R) :=
  (continuous_trace R _).comp (continuous_const.mul continuous_id)

theorem curve_closed (R : Region)  : curve R 1 = curve R 0 := by
  simp only [curve, mul_one, mul_zero]
  exact trace_closed R

theorem curve_injective_Ico (R : Region)  :
    Set.InjOn (curve R) (Set.Ico 0 1) := by
  intro t ht s hs heq
  have hM : 0 < ((perimeter R.val : Nat) : Real) := by exact_mod_cast perimeter_pos R
  have hmul := trace_injective_Ico R
    ⟨mul_nonneg hM.le ht.1, by nlinarith [ht.2]⟩
    ⟨mul_nonneg hM.le hs.1, by nlinarith [hs.2]⟩ heq
  exact (mul_left_cancel₀ hM.ne') hmul

theorem curve_image (R : Region)  :
    curve R '' Set.Icc 0 1 = (polygon R).boundary Real := by
  rw [← trace_image R]
  ext p
  have hM : 0 < ((perimeter R.val : Nat) : Real) := by exact_mod_cast perimeter_pos R
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨((perimeter R.val : Nat) : Real) * t, ?_, rfl⟩
    exact ⟨mul_nonneg hM.le ht.1, by nlinarith [ht.2]⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t / ((perimeter R.val : Nat) : Real),
      ⟨div_nonneg ht.1 hM.le, (div_le_one hM).mpr ht.2⟩, ?_⟩
    simp only [curve, mul_div_cancel₀ t hM.ne']

end MathResearchAnalysis.OrthogonalBoundaryCurve

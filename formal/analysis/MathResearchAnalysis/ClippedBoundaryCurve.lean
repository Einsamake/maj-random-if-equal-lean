module

public import MathResearchAnalysis.ClippedBoundaryPolygon
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

/-!
# Continuous traversal of every actual initial boundary segment

The finite polygon is traversed by an explicitly glued piecewise affine map.
The map is continuous, closes after the actual perimeter, and is injective on
its half-open parameter interval. The occupied-region frontier identification
is a separate result and is not assumed here.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClippedBoundaryCurve

open GridCellBoundary GridBoundarySegments ClippedBoundaryCycle ClippedBoundaryPolygon

abbrev edgeAt (L n : Nat) : Edges L := ((successor L) ^ n) (anchor L)

def pointAt (L n : Nat) : Plane := realSite (source (edgeAt L n).val)

def trace (L : Nat) : Nat → Real → Plane
  | 0, _ => pointAt L 0
  | n + 1, t => if t ≤ (n : Real) then trace L n t
      else segmentPoint (edgeAt L n).val (t - (n : Real))

theorem segmentPoint_injective (e : HalfEdge) : Function.Injective (segmentPoint e) := by
  rcases e with ⟨v, d⟩
  fin_cases d
  · intro t u h
    have hx := congrArg Prod.fst h
    simp only [segmentPoint_north] at hx
    linarith
  · intro t u h
    have hy := congrArg Prod.snd h
    simp only [segmentPoint_east] at hy
    linarith
  · intro t u h
    have hx := congrArg Prod.fst h
    simp only [segmentPoint_south] at hx
    linarith
  · intro t u h
    have hy := congrArg Prod.snd h
    simp only [segmentPoint_west] at hy
    linarith

theorem trace_endpoint (L n : Nat) : trace L n (n : Real) = pointAt L n := by
  cases n with
  | zero => rfl
  | succ n =>
      have hlt : (n : Real) < ((n + 1 : Nat) : Real) := by exact_mod_cast Nat.lt_succ_self n
      rw [trace, ite_eq_right (not_le.mpr hlt)]
      have hsub : ((n + 1 : Nat) : Real) - (n : Real) = 1 := by push_cast; ring
      rw [hsub, segmentPoint_one]
      exact congrArg realSite (consecutive_endpoints L (anchor L) n).symm

theorem trace_of_le (L : Nat) {n m : Nat} (hnm : n ≤ m) {t : Real}
    (ht : t ≤ (n : Real)) : trace L m t = trace L n t := by
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

theorem trace_piece (L n : Nat) {t : Real} (ht : (n : Real) ≤ t) :
    trace L (n + 1) t = segmentPoint (edgeAt L n).val (t - (n : Real)) := by
  rw [trace]
  split_ifs with h
  · have heq : t = (n : Real) := le_antisymm h ht
    subst t
    rw [trace_endpoint, sub_self, segmentPoint_zero]
    rfl
  · rfl

theorem trace_piece_final (L : Nat) (i : Index L) (u : Real)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    trace L (8 * L + 4) ((i.val : Real) + u) = segmentPoint (facetAt L i).val u := by
  rw [trace_of_le L (n := i.val + 1) (m := 8 * L + 4) (by omega)
    (by push_cast; linarith)]
  rw [trace_piece L i.val (by linarith)]
  have hsub : (i.val : Real) + u - (i.val : Real) = u := by ring
  rw [hsub]
  rfl

theorem continuous_trace (L n : Nat) : Continuous (trace L n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have hc : Continuous (fun t : Real => segmentPoint (edgeAt L n).val (t - (n : Real))) := by
        unfold segmentPoint
        fun_prop
      apply ih.if_le hc continuous_id continuous_const
      intro t ht
      change t = (n : Real) at ht
      subst t
      rw [trace_endpoint, sub_self, segmentPoint_zero]
      rfl

theorem trace_start (L n : Nat) : trace L n 0 = pointAt L 0 := by
  rw [trace_of_le L (n := 0) (m := n) (Nat.zero_le n) (by norm_num)]
  rfl

theorem trace_closed (L : Nat) (hL : 1 ≤ L) :
    trace L (8 * L + 4) (8 * L + 4 : Nat) = trace L (8 * L + 4) 0 := by
  rw [trace_endpoint, trace_start]
  unfold pointAt edgeAt
  rw [returns_after_perimeter L hL]
  rfl

theorem exists_piece (L : Nat) {t : Real} (ht : t ∈ Set.Ico 0 ((8 * L + 4 : Nat) : Real)) :
    ∃ i : Index L, ∃ u : Real, 0 ≤ u ∧ u < 1 ∧ t = (i.val : Real) + u := by
  have hn : Nat.floor t < 8 * L + 4 := (Nat.floor_lt ht.1).mpr ht.2
  refine ⟨⟨Nat.floor t, hn⟩, t - (Nat.floor t : Real), ?_, ?_, ?_⟩
  · exact sub_nonneg.mpr (Nat.floor_le ht.1)
  · have h := Nat.lt_floor_add_one t
    linarith
  · dsimp
    ring

theorem trace_injective_Ico (L : Nat) (hL : 1 ≤ L) :
    Set.InjOn (trace L (8 * L + 4)) (Set.Ico 0 ((8 * L + 4 : Nat) : Real)) := by
  intro t ht s hs heq
  obtain ⟨i, u, hu0, hu1, rfl⟩ := exists_piece L ht
  obtain ⟨j, v, hv0, hv1, rfl⟩ := exists_piece L hs
  rw [trace_piece_final L i u hu0 hu1.le,
    trace_piece_final L j v hv0 hv1.le] at heq
  by_cases hij : i = j
  · subst j
    have huv := segmentPoint_injective (facetAt L i).val heq
    rw [huv]
  · have hne : (facetAt L i).val ≠ (facetAt L j).val := by
      intro h
      exact hij ((facetAt_bijective L hL).1 (Subtype.ext h))
    have h := boundary_segments_intersect_only_endpoints
      (facetAt L i).property (facetAt L j).property hne
      (p := segmentPoint (facetAt L i).val u)
      ⟨u, hu0, hu1.le, rfl⟩ ⟨v, hv0, hv1.le, heq⟩
    have hu : u = 0 := by
      rcases h.1 with h | h
      · exact segmentPoint_injective _ (h.trans (segmentPoint_zero _).symm)
      · have h' : u = 1 := segmentPoint_injective _ (h.trans (segmentPoint_one _).symm)
        exact False.elim (hu1.ne h')
    have hv : v = 0 := by
      rcases h.2 with h | h
      · exact segmentPoint_injective _ (heq.symm.trans (h.trans (segmentPoint_zero _).symm))
      · have h' : v = 1 := segmentPoint_injective _
          (heq.symm.trans (h.trans (segmentPoint_one _).symm))
        exact False.elim (hv1.ne h')
    have hvertices : vertex L i = vertex L j := by
      simpa only [hu, hv, segmentPoint_zero, vertex] using heq
    exact False.elim (hij (vertex_injective L hL hvertices))

theorem trace_image (L : Nat) (hL : 1 ≤ L) :
    trace L (8 * L + 4) '' Set.Icc 0 ((8 * L + 4 : Nat) : Real) =
      (polygon L).boundary Real := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    apply (ClippedBoundaryPolygon.mem_boundary_iff L hL _).mpr
    by_cases heq : t = ((8 * L + 4 : Nat) : Real)
    · subst t
      rw [trace_closed L hL, trace_start]
      exact ⟨(anchor L).val, (anchor L).property, source_mem_closedSegment _⟩
    · obtain ⟨i, u, hu0, hu1, rfl⟩ := exists_piece L ⟨ht.1, lt_of_le_of_ne ht.2 heq⟩
      rw [trace_piece_final L i u hu0 hu1.le]
      exact ⟨(facetAt L i).val, (facetAt L i).property, u, hu0, hu1.le, rfl⟩
  · intro hp
    obtain ⟨e, he, u, hu0, hu1, rfl⟩ :=
      (ClippedBoundaryPolygon.mem_boundary_iff L hL p).mp hp
    obtain ⟨i, hi⟩ := (facetAt_bijective L hL).2 ⟨e, he⟩
    have hie : (facetAt L i).val = e := congrArg Subtype.val hi
    refine ⟨(i.val : Real) + u, ⟨by positivity, ?_⟩, ?_⟩
    · have hiR : (i.val : Real) + 1 ≤ ((8 * L + 4 : Nat) : Real) := by
        exact_mod_cast i.isLt
      linarith
    · rw [trace_piece_final L i u hu0 hu1, hie]

/-- Traversal normalized to the usual unit parameter interval. -/
def curve (L : Nat) (t : Real) : Plane :=
  trace L (8 * L + 4) (((8 * L + 4 : Nat) : Real) * t)

theorem continuous_curve (L : Nat) : Continuous (curve L) :=
  (continuous_trace L _).comp (continuous_const.mul continuous_id)

theorem curve_closed (L : Nat) (hL : 1 ≤ L) : curve L 1 = curve L 0 := by
  simp only [curve, mul_one, mul_zero]
  exact trace_closed L hL

theorem curve_injective_Ico (L : Nat) (hL : 1 ≤ L) :
    Set.InjOn (curve L) (Set.Ico 0 1) := by
  intro t ht s hs heq
  have hM : 0 < ((8 * L + 4 : Nat) : Real) := by positivity
  have hmul := trace_injective_Ico L hL
    ⟨mul_nonneg hM.le ht.1, by nlinarith [ht.2]⟩
    ⟨mul_nonneg hM.le hs.1, by nlinarith [hs.2]⟩ heq
  exact (mul_left_cancel₀ hM.ne') hmul

theorem curve_image (L : Nat) (hL : 1 ≤ L) :
    curve L '' Set.Icc 0 1 = (polygon L).boundary Real := by
  rw [← trace_image L hL]
  ext p
  have hM : 0 < ((8 * L + 4 : Nat) : Real) := by positivity
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨((8 * L + 4 : Nat) : Real) * t, ?_, rfl⟩
    exact ⟨mul_nonneg hM.le ht.1, by nlinarith [ht.2]⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t / ((8 * L + 4 : Nat) : Real),
      ⟨div_nonneg ht.1 hM.le, (div_le_one hM).mpr ht.2⟩, ?_⟩
    simp only [curve, mul_div_cancel₀ t hM.ne']

end MathResearchAnalysis.ClippedBoundaryCurve

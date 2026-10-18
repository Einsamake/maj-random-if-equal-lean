module

public import MathResearchAnalysis.GridBoundaryIncidence
public import Mathlib.GroupTheory.Perm.Cycle.Basic

set_option autoImplicit false

/-!
# The genuine boundary successor permutation

For a finite occupied set with the explicit local NoCheckerboard property,
the proved one-in/one-out counts make source and target bijections between
actual boundary half-edges and actual boundary vertices. Their composition
is the successor permutation. Shared-endpoint paths stay within its orbits.
No connectedness or single-orbit conclusion is assumed or asserted.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.GridBoundaryPermutation

open GridCellBoundary GridBoundaryIncidence

abbrev Edges (S : Finset Site) := {e : HalfEdge // e ∈ boundary S}
abbrev Vertices (S : Finset Site) := {p : Site // p ∈ vertices S}

def sourceVertex (S : Finset Site) (e : Edges S) : Vertices S :=
  ⟨source e.val, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩)⟩

def targetVertex (S : Finset Site) (e : Edges S) : Vertices S :=
  ⟨target e.val, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩)⟩

theorem sourceVertex_bijective (S : Finset Site) (hnc : NoCheckerboard S) :
    Function.Bijective (sourceVertex S) := by
  constructor
  · intro e f h
    have hc := (vertex_incidence_one S hnc (source e.val) (sourceVertex S e).property).1
    have he : e.val ∈ outgoing S (source e.val) :=
      (mem_outgoing _ _ _).mpr ⟨e.property, rfl⟩
    have hf : f.val ∈ outgoing S (source e.val) :=
      (mem_outgoing _ _ _).mpr ⟨f.property, (congrArg Subtype.val h).symm⟩
    exact Subtype.ext ((Finset.card_le_one_iff.mp (le_of_eq hc)) he hf)
  · intro p
    have hc := (vertex_incidence_one S hnc p.val p.property).1
    have hn : (outgoing S p.val).Nonempty :=
      Finset.card_pos.mp (by rw [hc]; decide)
    obtain ⟨e, he⟩ := hn
    obtain ⟨heb, hep⟩ := (mem_outgoing S p.val e).mp he
    exact ⟨⟨e, heb⟩, Subtype.ext hep⟩

theorem targetVertex_bijective (S : Finset Site) (hnc : NoCheckerboard S) :
    Function.Bijective (targetVertex S) := by
  constructor
  · intro e f h
    have hc := (vertex_incidence_one S hnc (target e.val) (targetVertex S e).property).2
    have he : e.val ∈ incoming S (target e.val) :=
      (mem_incoming _ _ _).mpr ⟨e.property, rfl⟩
    have hf : f.val ∈ incoming S (target e.val) :=
      (mem_incoming _ _ _).mpr ⟨f.property, (congrArg Subtype.val h).symm⟩
    exact Subtype.ext ((Finset.card_le_one_iff.mp (le_of_eq hc)) he hf)
  · intro p
    have hc := (vertex_incidence_one S hnc p.val p.property).2
    have hn : (incoming S p.val).Nonempty :=
      Finset.card_pos.mp (by rw [hc]; decide)
    obtain ⟨e, he⟩ := hn
    obtain ⟨heb, hep⟩ := (mem_incoming S p.val e).mp he
    exact ⟨⟨e, heb⟩, Subtype.ext hep⟩

def sourceEquiv (S : Finset Site) (hnc : NoCheckerboard S) : Edges S ≃ Vertices S :=
  Equiv.ofBijective (sourceVertex S) (sourceVertex_bijective S hnc)

def targetEquiv (S : Finset Site) (hnc : NoCheckerboard S) : Edges S ≃ Vertices S :=
  Equiv.ofBijective (targetVertex S) (targetVertex_bijective S hnc)

def succPerm (S : Finset Site) (hnc : NoCheckerboard S) : Equiv.Perm (Edges S) :=
  (targetEquiv S hnc).trans (sourceEquiv S hnc).symm

@[simp] theorem sourceEquiv_apply (S : Finset Site) (hnc : NoCheckerboard S) (e : Edges S) :
    (sourceEquiv S hnc e).val = source e.val := rfl

@[simp] theorem targetEquiv_apply (S : Finset Site) (hnc : NoCheckerboard S) (e : Edges S) :
    (targetEquiv S hnc e).val = target e.val := rfl

theorem source_succ (S : Finset Site) (hnc : NoCheckerboard S) (e : Edges S) :
    source (succPerm S hnc e).val = target e.val := by
  exact congrArg Subtype.val ((sourceEquiv S hnc).apply_symm_apply (targetEquiv S hnc e))

theorem target_pred (S : Finset Site) (hnc : NoCheckerboard S) (e : Edges S) :
    target ((succPerm S hnc).symm e).val = source e.val := by
  exact congrArg Subtype.val ((targetEquiv S hnc).apply_symm_apply (sourceEquiv S hnc e))

theorem succ_ne_self (S : Finset Site) (hnc : NoCheckerboard S) (e : Edges S) :
    succPerm S hnc e ≠ e := by
  intro h
  have he := source_succ S hnc e
  rw [h] at he
  exact source_ne_target e.val he

theorem pred_ne_self (S : Finset Site) (hnc : NoCheckerboard S) (e : Edges S) :
    (succPerm S hnc).symm e ≠ e := by
  intro h
  have he := target_pred S hnc e
  rw [h] at he
  exact source_ne_target e.val he.symm

theorem source_eq_source_iff (S : Finset Site) (hnc : NoCheckerboard S) (e f : Edges S) :
    source e.val = source f.val ↔ e = f := by
  constructor
  · intro h
    exact (sourceVertex_bijective S hnc).1 (Subtype.ext h)
  · rintro rfl
    rfl

theorem target_eq_target_iff (S : Finset Site) (hnc : NoCheckerboard S) (e f : Edges S) :
    target e.val = target f.val ↔ e = f := by
  constructor
  · intro h
    exact (targetVertex_bijective S hnc).1 (Subtype.ext h)
  · rintro rfl
    rfl

/-- The actual undirected relation of sharing a geometric endpoint. -/
def Touch (S : Finset Site) (e f : Edges S) : Prop :=
  source e.val = source f.val ∨ source e.val = target f.val ∨
    target e.val = source f.val ∨ target e.val = target f.val

theorem touch_refl (S : Finset Site) (e : Edges S) : Touch S e e := Or.inl rfl

theorem touch_symm (S : Finset Site) (e f : Edges S) : Touch S e f ↔ Touch S f e := by
  unfold Touch
  tauto

theorem touch_iff (S : Finset Site) (hnc : NoCheckerboard S) (e f : Edges S) :
    Touch S e f ↔ e = f ∨ succPerm S hnc e = f ∨ succPerm S hnc f = e := by
  constructor
  · intro h
    rcases h with h | h | h | h
    · exact Or.inl ((source_eq_source_iff S hnc e f).mp h)
    · exact Or.inr (Or.inr ((source_eq_source_iff S hnc _ _).mp
        ((source_succ S hnc f).trans h.symm)))
    · exact Or.inr (Or.inl ((source_eq_source_iff S hnc _ _).mp
        ((source_succ S hnc e).trans h)))
    · exact Or.inl ((target_eq_target_iff S hnc e f).mp h)
  · intro h
    rcases h with h | h | h
    · subst f
      exact Or.inl rfl
    · subst f
      exact Or.inr (Or.inr (Or.inl (source_succ S hnc e).symm))
    · subst e
      exact Or.inr (Or.inl (source_succ S hnc f))

theorem sameCycle_of_touch (S : Finset Site) (hnc : NoCheckerboard S)
    {e f : Edges S} (h : Touch S e f) : (succPerm S hnc).SameCycle e f := by
  rcases (touch_iff S hnc e f).mp h with h | h | h
  · subst f
    exact Equiv.Perm.SameCycle.refl _ _
  · subst f
    exact (Equiv.Perm.SameCycle.refl (succPerm S hnc) e).apply_right
  · subst e
    exact ((Equiv.Perm.SameCycle.refl (succPerm S hnc) f).apply_right).symm

theorem sameCycle_of_touch_path (S : Finset Site) (hnc : NoCheckerboard S)
    {e f : Edges S} (h : Relation.ReflTransGen (Touch S) e f) :
    (succPerm S hnc).SameCycle e f := by
  induction h with
  | refl => exact Equiv.Perm.SameCycle.refl _ _
  | tail _ hstep ih => exact ih.trans (sameCycle_of_touch S hnc hstep)

end MathResearchAnalysis.GridBoundaryPermutation

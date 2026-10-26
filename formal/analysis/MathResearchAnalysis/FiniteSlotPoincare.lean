module
public import MathResearchAnalysis.FinitePathPoincare
public import Mathlib.Tactic
set_option autoImplicit false
/-! The finite-slot path and the Nat-indexed path have exactly the same
vertices and adjacent bonds. Zero extension is used only outside the path. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.FiniteSlotPoincare
open scoped BigOperators

def pathEdges (n : Nat) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1.val+1=e.2.val)

def extend {n : Nat} (u : Fin n → Real) (i : Nat) : Real :=
  if h : i<n then u ⟨i,h⟩ else 0

@[simp] theorem extend_fin {n : Nat} (u : Fin n → Real) (i : Fin n) :
    extend u i.val = u i := by simp [extend]

theorem sum_extend (n : Nat) (u : Fin n → Real) :
    (∑ i ∈ Finset.range n, extend u i) = ∑ i : Fin n, u i := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp

theorem squareMass_extend (n : Nat) (u : Fin n → Real) :
    FinitePathPoincare.squareMass n (extend u) = ∑ i : Fin n, (u i)^2 := by
  unfold FinitePathPoincare.squareMass
  rw [← Fin.sum_univ_eq_sum_range]
  simp

theorem energy_extend (n : Nat) (u : Fin n → Real) :
    FinitePathPoincare.energy n (extend u) =
      ∑ e ∈ pathEdges n, (u e.1-u e.2)^2 := by
  unfold FinitePathPoincare.energy
  refine Finset.sum_bij (fun k hk =>
    (⟨k, by have := Finset.mem_range.mp hk; omega⟩,
     ⟨k+1, by have := Finset.mem_range.mp hk; omega⟩)) ?_ ?_ ?_ ?_
  · intro k hk
    simp [pathEdges]
  · intro k hk l hl he
    exact congrArg (fun e : Fin n × Fin n => e.1.val) he
  · intro e he
    have heq : e.1.val+1=e.2.val := (Finset.mem_filter.mp he).2
    refine ⟨e.1.val, Finset.mem_range.mpr (by omega), ?_⟩
    apply Prod.ext
    · rfl
    · apply Fin.ext
      exact heq
  · intro k hk
    have hk0 : k<n := by have := Finset.mem_range.mp hk; omega
    have hk1 : k+1<n := by have := Finset.mem_range.mp hk; omega
    simp only [extend, dite_eq_left hk0, dite_eq_left hk1]
    ring

/-- The actual n-slot path has the same explicit n² Poincare constant. -/
theorem poincare (n : Nat) (u : Fin n → Real) (hzero : (∑ i : Fin n, u i)=0) :
    (∑ i : Fin n, (u i)^2) ≤ (n : Real)^2 *
      ∑ e ∈ pathEdges n, (u e.1-u e.2)^2 := by
  have h := FinitePathPoincare.poincare n (extend u) (by rw [sum_extend, hzero])
  rwa [squareMass_extend, energy_extend] at h
end MathResearchAnalysis.FiniteSlotPoincare

module
public import MathResearchAnalysis.PositivePartSquare
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Tactic
set_option autoImplicit false
/-! A finite cooperative comparison proved by positive-part square energy.
Every listed action is a genuine finite permutation. No maximum derivative,
Gronwall norm comparison, stochastic law or covariance sign is assumed.
Actual moment derivatives must discharge this deterministic lemma separately. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.FinitePermutationComparison
open Set
open scoped BigOperators
variable {V K : Type*} [Fintype V]

def rate (E : Finset K) (σ : K → Equiv V V) (f : V → Real) (i : V) : Real :=
  ∑ e ∈ E, (f (σ e i)-f i)/2

def energy (f : V → Real) : Real := ∑ i : V, PositivePartSquare.square (f i)

theorem permutation_flux_nonpos (σ : Equiv V V) (f : V → Real) :
    (∑ i : V, 2*max (f i) 0*(f (σ i)-f i)) ≤ 0 := by
  calc
    _ ≤ ∑ i : V, (PositivePartSquare.square (f (σ i))-PositivePartSquare.square (f i)) :=
      Finset.sum_le_sum (fun i _ => PositivePartSquare.supporting_inequality (f i) (f (σ i)))
    _ = 0 := by rw [Finset.sum_sub_distrib, Equiv.sum_comp σ (fun x => PositivePartSquare.square (f x)), sub_self]

theorem rate_flux_nonpos (E : Finset K) (σ : K → Equiv V V) (f : V → Real) :
    (∑ i : V, 2*max (f i) 0*rate E σ f i) ≤ 0 := by
  unfold rate
  simp_rw [Finset.mul_sum, ← mul_div_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_nonpos
  intro e _
  rw [← Finset.sum_div]
  exact div_nonpos_of_nonpos_of_nonneg (permutation_flux_nonpos (σ e) f) (by norm_num)

theorem energy_nonneg (f : V → Real) : 0 ≤ energy f :=
  Finset.sum_nonneg (fun i _ => PositivePartSquare.square_nonneg (f i))

theorem source_derivative_nonpos (E : Finset K) (σ : K → Equiv V V)
    (f source : V → Real) (hs : ∀ i, 0 ≤ source i) :
    (∑ i : V, 2*max (f i) 0*(rate E σ f i-source i)) ≤ 0 := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hsource : 0 ≤ ∑ i : V, 2*max (f i) 0*source i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) (hs i))
  exact sub_nonpos.mpr ((rate_flux_nonpos E σ f).trans hsource)

theorem hasDerivAt_energy (E : Finset K) (σ : K → Equiv V V)
    (c source : Real → V → Real) (t : Real)
    (hc : ∀ i, HasDerivAt (fun s => c s i) (rate E σ (c t) i-source t i) t) :
    HasDerivAt (fun s => energy (c s))
      (∑ i : V, 2*max (c t i) 0*(rate E σ (c t) i-source t i)) t :=
  HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => by
    simpa only [Function.comp_def] using
      (PositivePartSquare.hasDerivAt_square (c t i)).comp t (hc i))

/-- A nonnegative forcing subtracted from the cooperative permutation rate
preserves nonpositivity. Only actual component continuity and actual derivative
equations are inputs; no comparison assertion is assumed. -/
theorem nonpos (E : Finset K) (σ : K → Equiv V V)
    (c source : Real → V → Real)
    (hc : ∀ i, ContinuousOn (fun t => c t i) (Ici 0))
    (hd : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => c s i) (rate E σ (c t) i-source t i) t)
    (hs : ∀ t : Real, 0<t → ∀ i, 0 ≤ source t i)
    (hzero : ∀ i, c 0 i ≤ 0) (t : Real) (ht : 0 ≤ t) (i : V) : c t i ≤ 0 := by
  classical
  have hcont : ContinuousOn (fun s => energy (c s)) (Ici (0 : Real)) :=
    continuousOn_finsetSum _ (fun j _ => PositivePartSquare.square_continuous.comp_continuousOn (hc j))
  have hmono : AntitoneOn (fun s => energy (c s)) (Ici (0 : Real)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hcont
      (f' := fun s => ∑ j : V, 2*max (c s j) 0*(rate E σ (c s) j-source s j))
    · intro s hsmem
      have hspos : 0 < s := by simpa only [interior_Ici,mem_Ioi] using hsmem
      exact (hasDerivAt_energy E σ c source s (hd s hspos)).hasDerivWithinAt
    · intro s hsmem
      have hspos : 0 < s := by simpa only [interior_Ici,mem_Ioi] using hsmem
      exact source_derivative_nonpos E σ (c s) (source s) (hs s hspos)
  have he0 : energy (c 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact (PositivePartSquare.square_eq_zero_iff _).mpr (hzero j)
  have he : energy (c t) ≤ 0 := by
    simpa only [he0] using hmono (show (0 : Real) ∈ Ici 0 from le_rfl) ht ht
  have hi : PositivePartSquare.square (c t i) ≤ energy (c t) :=
    Finset.single_le_sum (fun j _ => PositivePartSquare.square_nonneg (c t j)) (Finset.mem_univ i)
  exact (PositivePartSquare.square_eq_zero_iff _).mp
    (le_antisymm (hi.trans he) (PositivePartSquare.square_nonneg _))
end MathResearchAnalysis.FinitePermutationComparison

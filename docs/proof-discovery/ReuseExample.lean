module
public import MathResearchAnalysis.FinitePermutationComparison
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic

set_option autoImplicit false

/-! A teaching reuse outside the sealed formal source set.
Three deterministic cells exchange with a directed cyclic neighbour at rate
one half, and receive ordered external forcing. Actual differentiable flows
are inputs: existence, a new stochastic model, or a real-world application
are not asserted. A second example shows why permutation reindexing matters.
-/
@[expose] public noncomputable section
namespace ProofDiscovery.ReuseExample
open Set
open scoped BigOperators
open MathResearchAnalysis

def shiftRate (x : Fin 3 → Real) (i : Fin 3) : Real :=
  (x (finRotate 3 i)-x i)/2

/-- Ordered initial values and forcing preserve order for two actual flows.
The new work here is instantiation, not a new comparison principle. -/
theorem three_cell_order
    (u v f g : Real → Fin 3 → Real)
    (hcu : ∀ i, ContinuousOn (fun t => u t i) (Ici 0))
    (hcv : ∀ i, ContinuousOn (fun t => v t i) (Ici 0))
    (hu : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => u s i) (shiftRate (u t) i+f t i) t)
    (hv : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => v s i) (shiftRate (v t) i+g t i) t)
    (hfg : ∀ t : Real, 0<t → ∀ i, f t i≤g t i)
    (hzero : ∀ i, u 0 i≤v 0 i)
    (t : Real) (ht : 0≤t) (i : Fin 3) : u t i≤v t i := by
  have hd : ∀ s : Real, 0<s → ∀ j,
      HasDerivAt (fun r => u r j-v r j)
        (FinitePermutationComparison.rate ({()} : Finset Unit)
          (fun _ => finRotate 3) (fun k => u s k-v s k) j-(g s j-f s j)) s := by
    intro s hs j
    have he : FinitePermutationComparison.rate ({()} : Finset Unit)
        (fun _ => finRotate 3) (fun k => u s k-v s k) j-(g s j-f s j) =
        (shiftRate (u s) j+f s j)-(shiftRate (v s) j+g s j) := by
      simp only [FinitePermutationComparison.rate, Finset.sum_singleton, shiftRate]
      ring
    rw [he]
    exact (hu s hs j).sub (hv s hs j)
  have h := FinitePermutationComparison.nonpos ({()} : Finset Unit)
    (fun _ => finRotate 3) (fun s j => u s j-v s j) (fun s j => g s j-f s j)
    (fun j => (hcu j).sub (hcv j)) hd
    (fun s hs j => sub_nonneg.mpr (hfg s hs j))
    (fun j => sub_nonpos.mpr (hzero j)) t ht i
  exact sub_nonpos.mp h

def badMap (_ : Fin 2) : Fin 2 := 1

/-- Dropping bijectivity invalidates the particular unweighted energy-flux
inequality. This does NOT disprove general cooperative comparison. -/
theorem nonbijective_flux_positive :
    0 < ∑ i : Fin 2, 2*max ((![1,2] : Fin 2 → Real) i) 0 *
      ((![1,2] : Fin 2 → Real) (badMap i)-(![1,2] : Fin 2 → Real) i) := by
  norm_num [Fin.sum_univ_two, badMap]

end ProofDiscovery.ReuseExample

#print axioms ProofDiscovery.ReuseExample.three_cell_order
#print axioms ProofDiscovery.ReuseExample.nonbijective_flux_positive

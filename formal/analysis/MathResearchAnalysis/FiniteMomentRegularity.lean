module

public import MathResearchAnalysis.FiniteExclusionGenerator
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

/-!
# Noncircular regularity of finite moment integral systems

Compact-time integrability first gives continuity of every moment component.
Only then is continuity of the finite linear right-hand side derived, and FTC
supplies its derivative at strictly positive physical times. No ODE,
continuity, or differentiability is assumed for the component system itself.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.FiniteMomentRegularity

open MeasureTheory Set
open scoped Topology BigOperators

/-- A true compact-time Ioc integral representation gives continuity on [0,infinity). -/
theorem continuousOn_of_integral_eq (u f : Real → Real) (u0 : Real)
    (hint : ∀ T : NNReal, IntegrableOn f (Ioc 0 (T : Real)))
    (heq : ∀ T : NNReal, u (T : Real) = u0+∫ s : Real in Ioc 0 (T : Real), f s) :
    ContinuousOn u (Ici 0) := by
  intro t ht
  change (0 : Real) ≤ t at ht
  let T : NNReal := ⟨t+1,by linarith [ht]⟩
  have hi : IntegrableOn f (Icc 0 (T : Real)) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr (hint T)
  have hp : ContinuousOn (fun x : Real => u0+∫ s : Real in Ioc 0 x, f s) (Icc 0 (T : Real)) :=
    continuousOn_const.add (intervalIntegral.continuousOn_primitive hi)
  have hu : ContinuousOn u (Icc 0 (T : Real)) := hp.congr (fun x hx => heq ⟨x,hx.1⟩)
  have htT : t < (T : Real) := by change t < t+1; linarith
  have hmem : Icc 0 (T : Real) ∈ 𝓝[Ici 0] t := by
    change (Ici 0 ∩ Iic (T : Real)) ∈ 𝓝[Ici 0] t
    exact Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds htT))
  exact (hu t ⟨ht,htT.le⟩).mono_of_mem_nhdsWithin hmem

/-- FTC is applied only after continuity of the actual integrand is known. -/
theorem hasDerivAt_of_integral_eq (u f : Real → Real) (u0 : Real)
    (hint : ∀ T : NNReal, IntegrableOn f (Ioc 0 (T : Real)))
    (heq : ∀ T : NNReal, u (T : Real) = u0+∫ s : Real in Ioc 0 (T : Real), f s)
    (hf : ContinuousOn f (Ici 0)) (t : Real) (ht : 0 < t) : HasDerivAt u (f t) t := by
  have hi : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr (hint ⟨t,ht.le⟩)
  have hfpos : ContinuousOn f (Ioi 0) := hf.mono Ioi_subset_Ici_self
  have hm : StronglyMeasurableAtFilter f (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hfpos t ht
  have hc : ContinuousAt f t := hf.continuousAt (Ici_mem_nhds ht)
  have hd : HasDerivAt (fun x => u0+∫ s : Real in (0 : Real)..x, f s) (f t) t :=
    (intervalIntegral.integral_hasDerivAt_right hi hm hc).const_add u0
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  rw [intervalIntegral.integral_of_le hx.le]
  exact heq ⟨x,hx.le⟩

universe v
variable {V : Type v} [DecidableEq V]

/-- Finite one-index swap sums preserve componentwise continuity. -/
theorem oneParticle_continuousOn (E : Finset (V × V)) (u : Real → V → Real)
    (hu : ∀ i : V, ContinuousOn (fun t => u t i) (Ici 0)) (i : V) :
    ContinuousOn (fun t => FiniteExclusionGenerator.oneParticle E (u t) i) (Ici 0) := by
  unfold FiniteExclusionGenerator.oneParticle
  exact continuousOn_finsetSum E (fun e _ => ((hu _).sub (hu _)).div_const 2)

/-- Finite simultaneous two-index swap sums preserve componentwise continuity. -/
theorem twoParticle_continuousOn (E : Finset (V × V)) (u : Real → V → V → Real)
    (hu : ∀ i j : V, ContinuousOn (fun t => u t i j) (Ici 0)) (i j : V) :
    ContinuousOn (fun t => FiniteExclusionGenerator.twoParticle E (u t) i j) (Ici 0) := by
  unfold FiniteExclusionGenerator.twoParticle
  exact continuousOn_finsetSum E (fun e _ => ((hu _ _).sub (hu _ _)).div_const 2)

/-- Component continuity follows from the integral system and its real compact-time integrability. -/
theorem oneParticle_system_continuous (E : Finset (V × V)) (u : Real → V → Real) (u0 : V → Real)
    (hint : ∀ (T : NNReal) (i : V), IntegrableOn
      (fun s => FiniteExclusionGenerator.oneParticle E (u s) i) (Ioc 0 (T : Real)))
    (heq : ∀ (T : NNReal) (i : V), u (T : Real) i = u0 i+
      ∫ s : Real in Ioc 0 (T : Real), FiniteExclusionGenerator.oneParticle E (u s) i) :
    ∀ i : V, ContinuousOn (fun t => u t i) (Ici 0) := by
  intro i
  exact continuousOn_of_integral_eq _ _ (u0 i) (fun T => hint T i) (fun T => heq T i)

/-- The actual integral-system right side becomes continuous after, not before, the moments. -/
theorem oneParticle_system_rhs_continuous (E : Finset (V × V)) (u : Real → V → Real) (u0 : V → Real)
    (hint : ∀ (T : NNReal) (i : V), IntegrableOn
      (fun s => FiniteExclusionGenerator.oneParticle E (u s) i) (Ioc 0 (T : Real)))
    (heq : ∀ (T : NNReal) (i : V), u (T : Real) i = u0 i+
      ∫ s : Real in Ioc 0 (T : Real), FiniteExclusionGenerator.oneParticle E (u s) i) (i : V) :
    ContinuousOn (fun t => FiniteExclusionGenerator.oneParticle E (u t) i) (Ici 0) :=
  oneParticle_continuousOn E u (oneParticle_system_continuous E u u0 hint heq) i

/-- The one-point ODE is derived from the integral equations with no regularity premise. -/
theorem oneParticle_system_hasDerivAt (E : Finset (V × V)) (u : Real → V → Real) (u0 : V → Real)
    (hint : ∀ (T : NNReal) (i : V), IntegrableOn
      (fun s => FiniteExclusionGenerator.oneParticle E (u s) i) (Ioc 0 (T : Real)))
    (heq : ∀ (T : NNReal) (i : V), u (T : Real) i = u0 i+
      ∫ s : Real in Ioc 0 (T : Real), FiniteExclusionGenerator.oneParticle E (u s) i)
    (t : Real) (ht : 0 < t) (i : V) :
    HasDerivAt (fun s => u s i) (FiniteExclusionGenerator.oneParticle E (u t) i) t :=
  hasDerivAt_of_integral_eq _ _ (u0 i) (fun T => hint T i) (fun T => heq T i)
    (oneParticle_system_rhs_continuous E u u0 hint heq i) t ht

/-- Two-point continuity likewise follows from its genuine integral system. -/
theorem twoParticle_system_continuous (E : Finset (V × V)) (u : Real → V → V → Real)
    (u0 : V → V → Real)
    (hint : ∀ (T : NNReal) (i j : V), IntegrableOn
      (fun s => FiniteExclusionGenerator.twoParticle E (u s) i j) (Ioc 0 (T : Real)))
    (heq : ∀ (T : NNReal) (i j : V), u (T : Real) i j = u0 i j+
      ∫ s : Real in Ioc 0 (T : Real), FiniteExclusionGenerator.twoParticle E (u s) i j) :
    ∀ i j : V, ContinuousOn (fun t => u t i j) (Ici 0) := by
  intro i j
  exact continuousOn_of_integral_eq _ _ (u0 i j) (fun T => hint T i j) (fun T => heq T i j)

theorem twoParticle_system_rhs_continuous (E : Finset (V × V)) (u : Real → V → V → Real)
    (u0 : V → V → Real)
    (hint : ∀ (T : NNReal) (i j : V), IntegrableOn
      (fun s => FiniteExclusionGenerator.twoParticle E (u s) i j) (Ioc 0 (T : Real)))
    (heq : ∀ (T : NNReal) (i j : V), u (T : Real) i j = u0 i j+
      ∫ s : Real in Ioc 0 (T : Real), FiniteExclusionGenerator.twoParticle E (u s) i j) (i j : V) :
    ContinuousOn (fun t => FiniteExclusionGenerator.twoParticle E (u t) i j) (Ici 0) :=
  twoParticle_continuousOn E u (twoParticle_system_continuous E u u0 hint heq) i j

/-- The true two-point ODE is derived without assuming component continuity or an ODE. -/
theorem twoParticle_system_hasDerivAt (E : Finset (V × V)) (u : Real → V → V → Real)
    (u0 : V → V → Real)
    (hint : ∀ (T : NNReal) (i j : V), IntegrableOn
      (fun s => FiniteExclusionGenerator.twoParticle E (u s) i j) (Ioc 0 (T : Real)))
    (heq : ∀ (T : NNReal) (i j : V), u (T : Real) i j = u0 i j+
      ∫ s : Real in Ioc 0 (T : Real), FiniteExclusionGenerator.twoParticle E (u s) i j)
    (t : Real) (ht : 0 < t) (i j : V) :
    HasDerivAt (fun s => u s i j) (FiniteExclusionGenerator.twoParticle E (u t) i j) t :=
  hasDerivAt_of_integral_eq _ _ (u0 i j) (fun T => hint T i j) (fun T => heq T i j)
    (twoParticle_system_rhs_continuous E u u0 hint heq i j) t ht

end MathResearchAnalysis.FiniteMomentRegularity


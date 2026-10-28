module
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.CommonSubmeasureBound
open MeasureTheory Set

theorem abs_event_gap_le_missing_mass {α : Type*} [MeasurableSpace α]
    (mu nu gamma : Measure α) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hgmu : gamma≤mu) (hgnu : gamma≤nu) (s : Set α) (hs : MeasurableSet s) :
    |mu.real s-nu.real s|≤1-gamma.real univ := by
  letI : IsFiniteMeasure gamma := isFiniteMeasure_of_le mu hgmu
  have hms := measureReal_add_measureReal_compl (μ:=mu) hs
  have hns := measureReal_add_measureReal_compl (μ:=nu) hs
  have hgs := measureReal_add_measureReal_compl (μ:=gamma) hs
  simp only [probReal_univ] at hms hns
  have h1 : gamma.real s≤mu.real s :=
    ENNReal.toReal_mono (measure_ne_top mu s) ((Measure.le_iff.mp hgmu) s hs)
  have h2 : gamma.real s≤nu.real s :=
    ENNReal.toReal_mono (measure_ne_top nu s) ((Measure.le_iff.mp hgnu) s hs)
  have h3 : gamma.real sᶜ≤mu.real sᶜ :=
    ENNReal.toReal_mono (measure_ne_top mu sᶜ) ((Measure.le_iff.mp hgmu) sᶜ hs.compl)
  have h4 : gamma.real sᶜ≤nu.real sᶜ :=
    ENNReal.toReal_mono (measure_ne_top nu sᶜ) ((Measure.le_iff.mp hgnu) sᶜ hs.compl)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem abs_event_gap_le_of_common_mass {α : Type*} [MeasurableSpace α]
    (mu nu gamma : Measure α) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hgmu : gamma≤mu) (hgnu : gamma≤nu) (delta : Real)
    (hmass : 1-gamma.real univ≤delta) (s : Set α) (hs : MeasurableSet s) :
    |mu.real s-nu.real s|≤delta :=
  le_trans (abs_event_gap_le_missing_mass mu nu gamma hgmu hgnu s hs) hmass

theorem conv_mono_right (kappa rho sigma : Measure Real) [SFinite sigma]
    (h : rho≤sigma) : kappa∗rho≤kappa∗sigma := by
  exact Measure.map_mono (Measure.prod_mono le_rfl h) (by fun_prop)

theorem conv_mass (mu nu : Measure Real) [SFinite nu] :
    (mu∗nu) univ=mu univ*nu univ := by
  change ((mu.prod nu).map (fun x : Real×Real => x.1+x.2)) univ=_
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ]
  rw [← univ_prod_univ, Measure.prod_prod]

theorem real_conv_mass (mu nu : Measure Real) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    (mu∗nu).real univ=mu.real univ*nu.real univ := by
  change ENNReal.toReal ((mu∗nu) univ)=_
  rw [conv_mass,ENNReal.toReal_mul]
  rfl

end MathExploration.CommonSubmeasureBound
#print axioms MathExploration.CommonSubmeasureBound.abs_event_gap_le_missing_mass
#print axioms MathExploration.CommonSubmeasureBound.abs_event_gap_le_of_common_mass
#print axioms MathExploration.CommonSubmeasureBound.conv_mono_right
#print axioms MathExploration.CommonSubmeasureBound.conv_mass
#print axioms MathExploration.CommonSubmeasureBound.real_conv_mass

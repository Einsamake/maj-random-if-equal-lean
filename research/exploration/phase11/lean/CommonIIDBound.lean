module
public import CommonSubmeasureBound
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.CommonIIDBound
open MeasureTheory Set

noncomputable def iid (n : Nat) (mu : Measure Real) : Measure (Fin n → Real) :=
  Measure.pi (fun _ : Fin n => mu)

noncomputable def commonIID (n : Nat) (gamma : Measure Real) : Measure (Fin n → Real) :=
  iid n gamma

instance iid_isProbabilityMeasure (n : Nat) (mu : Measure Real) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (iid n mu) := by
  unfold iid
  infer_instance

theorem pi_mono {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (rho sigma : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (rho i)] (h : ∀ i, rho i ≤ sigma i) :
    Measure.pi rho ≤ Measure.pi sigma := by
  have ho : (Measure.pi rho).toOuterMeasure ≤
      OuterMeasure.pi (fun i => (sigma i).toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro t _
    change (Measure.pi rho) (Set.pi univ t) ≤ _
    rw [Measure.pi_pi]
    exact Finset.prod_le_prod fun i _ => (Measure.le_iff'.mp (h i)) (t i)
  apply Measure.le_iff.mpr
  intro s hs
  calc
    (Measure.pi rho) s ≤ OuterMeasure.pi (fun i => (sigma i).toOuterMeasure) s := ho s
    _ = (Measure.pi sigma) s := by
      rw [Measure.pi, toMeasure_apply _ _ hs]

theorem commonIID_le (n : Nat) (mu gamma : Measure Real) [IsProbabilityMeasure mu]
    (hgmu : gamma ≤ mu) : commonIID n gamma ≤ iid n mu := by
  letI : IsFiniteMeasure gamma := isFiniteMeasure_of_le mu hgmu
  exact pi_mono (fun _ : Fin n => gamma) (fun _ : Fin n => mu) (fun _ => hgmu)

theorem iid_mass (n : Nat) (gamma : Measure Real) [IsFiniteMeasure gamma] :
    (iid n gamma) univ = (gamma univ)^n := by
  unfold iid
  rw [Measure.pi_univ]
  simp

theorem commonIID_real_mass (n : Nat) (gamma : Measure Real) [IsFiniteMeasure gamma] :
    (commonIID n gamma).real univ = (gamma.real univ)^n := by
  change ENNReal.toReal ((iid n gamma) univ) = _
  rw [iid_mass, ENNReal.toReal_pow]
  rfl

theorem common_mass_nonneg (gamma : Measure Real) : 0 ≤ gamma.real univ :=
  ENNReal.toReal_nonneg

theorem common_mass_le_one (mu gamma : Measure Real) [IsProbabilityMeasure mu]
    (hgmu : gamma ≤ mu) : gamma.real univ ≤ 1 := by
  calc
    gamma.real univ ≤ mu.real univ :=
      ENNReal.toReal_mono (measure_ne_top mu univ) ((Measure.le_iff'.mp hgmu) univ)
    _ = 1 := probReal_univ

theorem abs_product_event_gap_le_missing_mass (n : Nat) (mu nu gamma : Measure Real)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hgmu : gamma ≤ mu) (hgnu : gamma ≤ nu)
    (s : Set (Fin n → Real)) (hs : MeasurableSet s) :
    |(iid n mu).real s - (iid n nu).real s| ≤ 1 - (gamma.real univ)^n := by
  letI : IsFiniteMeasure gamma := isFiniteMeasure_of_le mu hgmu
  have h := CommonSubmeasureBound.abs_event_gap_le_missing_mass
    (iid n mu) (iid n nu) (commonIID n gamma)
    (commonIID_le n mu gamma hgmu) (commonIID_le n nu gamma hgnu) s hs
  rw [commonIID_real_mass] at h
  exact h

theorem abs_product_event_gap_le_of_common_mass (n : Nat) (mu nu gamma : Measure Real)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hgmu : gamma ≤ mu) (hgnu : gamma ≤ nu) (c : Real) (hc : gamma.real univ = c)
    (s : Set (Fin n → Real)) (hs : MeasurableSet s) :
    |(iid n mu).real s - (iid n nu).real s| ≤ 1 - c^n := by
  simpa only [hc] using abs_product_event_gap_le_missing_mass n mu nu gamma hgmu hgnu s hs

theorem one_sub_pow_le_mul_one_sub (n : Nat) (c : Real) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    1 - c^n ≤ (n : Real) * (1 - c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : c^n ≤ 1 := pow_le_one₀ hc0 hc1
    have hnonneg : 0 ≤ 1-c := sub_nonneg.mpr hc1
    have hterm : c^n*(1-c) ≤ 1-c := by nlinarith
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem abs_product_event_gap_le_linear_missing_mass (n : Nat) (mu nu gamma : Measure Real)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hgmu : gamma ≤ mu) (hgnu : gamma ≤ nu)
    (s : Set (Fin n → Real)) (hs : MeasurableSet s) :
    |(iid n mu).real s - (iid n nu).real s| ≤ (n : Real) * (1 - gamma.real univ) :=
  le_trans (abs_product_event_gap_le_missing_mass n mu nu gamma hgmu hgnu s hs)
    (one_sub_pow_le_mul_one_sub n (gamma.real univ)
      (common_mass_nonneg gamma) (common_mass_le_one mu gamma hgmu))

end MathExploration.CommonIIDBound
#print axioms MathExploration.CommonIIDBound.iid
#print axioms MathExploration.CommonIIDBound.commonIID
#print axioms MathExploration.CommonIIDBound.iid_isProbabilityMeasure
#print axioms MathExploration.CommonIIDBound.pi_mono
#print axioms MathExploration.CommonIIDBound.commonIID_le
#print axioms MathExploration.CommonIIDBound.iid_mass
#print axioms MathExploration.CommonIIDBound.commonIID_real_mass
#print axioms MathExploration.CommonIIDBound.common_mass_nonneg
#print axioms MathExploration.CommonIIDBound.common_mass_le_one
#print axioms MathExploration.CommonIIDBound.abs_product_event_gap_le_missing_mass
#print axioms MathExploration.CommonIIDBound.abs_product_event_gap_le_of_common_mass
#print axioms MathExploration.CommonIIDBound.one_sub_pow_le_mul_one_sub
#print axioms MathExploration.CommonIIDBound.abs_product_event_gap_le_linear_missing_mass

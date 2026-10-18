module

public import MathResearchAnalysis.InfiniteGridTranslationLaw
public import MathResearchAnalysis.InfiniteGridComplement
public import MathResearchAnalysis.PerturbationGeometry

set_option autoImplicit false

/-!
# First recovery to the two homogeneous configurations

The original target consists of the two constant configurations. This is its
actual first-hit time on the infinite independent fair-mark field, retaining
infinity if no hit occurs. Membership is measurable on the countable lattice;
neither finite recovery nor a finite containing square enters the definition.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.HomogeneousRecoveryTime

abbrev Site := InfiniteGridModel.Site
abbrev Config := InfiniteGridModel.Config
abbrev Sample := InfiniteGridRandomDynamics.Sample
abbrev zeroConfig : Config := fun _ => false
abbrev oneConfig : Config := fun _ => true

def Homogeneous (f : Config) : Prop := f = zeroConfig ∨ f = oneConfig

theorem measurableSet_homogeneous : MeasurableSet {f : Config | Homogeneous f} := by
  change MeasurableSet ({zeroConfig} ∪ {oneConfig})
  exact (measurableSet_singleton _).union (measurableSet_singleton _)

def hitState (initial : Config) (t : Nat) (η : Sample) : Bool := by
  classical
  exact if Homogeneous (InfiniteGridRandomDynamics.synchronous initial t η) then false else true

theorem hitState_eq_false_iff (initial : Config) (t : Nat) (η : Sample) :
    hitState initial t η = false ↔
      Homogeneous (InfiniteGridRandomDynamics.synchronous initial t η) := by
  classical
  simp [hitState]

theorem hitState_measurable (initial : Config) (t : Nat) :
    Measurable (hitState initial t) := by
  classical
  exact Measurable.ite
    ((InfiniteGridRandomDynamics.synchronous_measurable initial t) measurableSet_homogeneous)
    measurable_const measurable_const

def synchronous (initial : Config) : Sample → ℕ∞ :=
  ExtendedRecoveryTime.time (hitState initial) false

theorem synchronous_measurable (initial : Config) : Measurable (synchronous initial) :=
  ExtendedRecoveryTime.time_measurable _ _ (hitState_measurable initial)

theorem synchronous_le_nat_iff (initial : Config) (η : Sample) (t : Nat) :
    synchronous initial η ≤ (t : ℕ∞) ↔
      ∃ s ≤ t, Homogeneous (InfiniteGridRandomDynamics.synchronous initial s η) := by
  simp only [synchronous, ExtendedRecoveryTime.time_le_nat_iff, hitState_eq_false_iff]

theorem synchronous_eq_top_iff (initial : Config) (η : Sample) :
    synchronous initial η = ⊤ ↔
      ∀ t, ¬Homogeneous (InfiniteGridRandomDynamics.synchronous initial t η) := by
  simp only [synchronous, ExtendedRecoveryTime.time_eq_top_iff]
  apply forall_congr'
  intro t
  exact not_congr (hitState_eq_false_iff initial t η)

theorem synchronous_one_persists (initial : Config) (η : Sample) {s t : Nat}
    (hst : s ≤ t) (hs : InfiniteGridRandomDynamics.synchronous initial s η = oneConfig) :
    InfiniteGridRandomDynamics.synchronous initial t η = oneConfig := by
  induction t, hst using Nat.le_induction with
  | base => exact hs
  | succ t _ ih =>
    change InfiniteGridModel.synchronous (InfiniteGridRandomDynamics.marks η) initial (t + 1) = _
    rw [InfiniteGridModel.synchronous_succ]
    change InfiniteGridModel.synchronous (InfiniteGridRandomDynamics.marks η) initial t =
      oneConfig at ih
    funext v
    simp only [ih, InfiniteGridModel.update,
      oneConfig, InfiniteGridModel.majority4_one]

theorem synchronous_homogeneous_persists (initial : Config) (η : Sample) {s t : Nat}
    (hst : s ≤ t) (hs : Homogeneous (InfiniteGridRandomDynamics.synchronous initial s η)) :
    Homogeneous (InfiniteGridRandomDynamics.synchronous initial t η) := by
  rcases hs with hs | hs
  · exact Or.inl (InfiniteGridRecoveryTime.synchronous_absorbing initial η hst hs)
  · exact Or.inr (synchronous_one_persists initial η hst hs)

theorem synchronous_absorbing (initial : Config) :
    ExtendedRecoveryTime.Absorbing (hitState initial) false := by
  intro η s t hst hs
  exact (hitState_eq_false_iff initial t η).mpr
    (synchronous_homogeneous_persists initial η hst
      ((hitState_eq_false_iff initial s η).mp hs))

theorem synchronous_le_nat_iff_current (initial : Config) (η : Sample) (t : Nat) :
    synchronous initial η ≤ (t : ℕ∞) ↔
      Homogeneous (InfiniteGridRandomDynamics.synchronous initial t η) := by
  exact (ExtendedRecoveryTime.time_le_nat_iff_of_absorbing _ _
    (synchronous_absorbing initial) η t).trans (hitState_eq_false_iff initial t η)

theorem synchronous_tail_iff (initial : Config) (η : Sample) (t : Nat) :
    (t : ℕ∞) < synchronous initial η ↔
      ¬Homogeneous (InfiniteGridRandomDynamics.synchronous initial t η) := by
  simpa only [not_le] using not_congr (synchronous_le_nat_iff_current initial η t)

theorem synchronous_eq_zero_of_homogeneous (initial : Config) (h : Homogeneous initial)
    (η : Sample) : synchronous initial η = 0 := by
  apply le_antisymm _ zero_le
  exact (synchronous_le_nat_iff initial η 0).mpr ⟨0, le_rfl, h⟩

theorem synchronous_eq_zero_iff (initial : Config) (η : Sample) :
    synchronous initial η = 0 ↔ Homogeneous initial := by
  constructor
  · intro h
    exact (synchronous_le_nat_iff_current initial η 0).mp (by rw [h]; rfl)
  · exact fun h => synchronous_eq_zero_of_homogeneous initial h η

theorem supported_not_one (L : Nat) (state : Config)
    (hSupport : InfiniteGridModel.Supported L state) : state ≠ oneConfig := by
  intro h
  have hout : ¬InfiniteGridModel.Inside L ((L : Int), 0) := by
    simp only [InfiniteGridModel.Inside]
    omega
  have hv := hSupport ((L : Int), 0) hout
  rw [h] at hv
  exact Bool.noConfusion hv

theorem synchronous_ne_one_of_supported (L : Nat) (initial : Config)
    (hSupport : InfiniteGridModel.Supported L initial) (t : Nat) (η : Sample) :
    InfiniteGridRandomDynamics.synchronous initial t η ≠ oneConfig :=
  supported_not_one L _ (InfiniteGridModel.synchronous_supported
    (InfiniteGridRandomDynamics.marks η) L initial hSupport t)

theorem synchronous_eq_zero_background (L : Nat) (initial : Config)
    (hSupport : InfiniteGridModel.Supported L initial) (η : Sample) :
    synchronous initial η = InfiniteGridRecoveryTime.synchronous initial η := by
  apply RecoveryTimeTransport.time_eq_of_zero_iff (hitState initial)
    (InfiniteGridRandomDynamics.synchronous initial) false zeroConfig η
  intro t
  rw [hitState_eq_false_iff]
  exact or_iff_left (synchronous_ne_one_of_supported L initial hSupport t η)

theorem synchronous_supported_translated (L : Nat) (a : Site) (initial : Config)
    (hSupport : InfiniteGridTranslation.SupportedTranslated L a initial)
    (t : Nat) (η : Sample) : InfiniteGridTranslation.SupportedTranslated L a
      (InfiniteGridRandomDynamics.synchronous initial t η) := by
  have hnorm : InfiniteGridModel.Supported L
      (InfiniteGridTranslation.translate (-a.1, -a.2) initial) := by
    apply (InfiniteGridTranslation.supported_translate_iff L a _).mp
    simpa only [InfiniteGridTranslation.translate_translate_neg] using hSupport
  have hsp := InfiniteGridModel.synchronous_supported
    (InfiniteGridTranslation.translateMarks (-a.1, -a.2)
      (InfiniteGridRandomDynamics.marks η)) L _ hnorm t
  rw [InfiniteGridTranslation.synchronous_translate] at hsp
  have hback := (InfiniteGridTranslation.supported_translate_iff L a _).mpr hsp
  simpa only [InfiniteGridTranslation.translate_translate_neg,
    InfiniteGridRandomDynamics.synchronous] using hback

theorem supported_translated_not_one (L : Nat) (a : Site) (state : Config)
    (hSupport : InfiniteGridTranslation.SupportedTranslated L a state) :
    state ≠ oneConfig := by
  intro h
  have hout : ¬InfiniteGridTranslation.InsideTranslated L a (a.1 + (L : Int), a.2) := by
    simp only [InfiniteGridTranslation.InsideTranslated, InfiniteGridModel.Inside,
      InfiniteGridTranslation.shift]
    omega
  have hv := hSupport (a.1 + (L : Int), a.2) hout
  rw [h] at hv
  exact Bool.noConfusion hv

theorem synchronous_ne_one_of_supported_translated (L : Nat) (a : Site)
    (initial : Config) (hSupport : InfiniteGridTranslation.SupportedTranslated L a initial)
    (t : Nat) (η : Sample) :
    InfiniteGridRandomDynamics.synchronous initial t η ≠ oneConfig :=
  supported_translated_not_one L a _
    (synchronous_supported_translated L a initial hSupport t η)

theorem synchronous_eq_zero_background_translated (L : Nat) (a : Site) (initial : Config)
    (hSupport : InfiniteGridTranslation.SupportedTranslated L a initial) (η : Sample) :
    synchronous initial η = InfiniteGridRecoveryTime.synchronous initial η := by
  apply RecoveryTimeTransport.time_eq_of_zero_iff (hitState initial)
    (InfiniteGridRandomDynamics.synchronous initial) false zeroConfig η
  intro t
  rw [hitState_eq_false_iff]
  exact or_iff_left (synchronous_ne_one_of_supported_translated L a initial hSupport t η)

theorem synchronous_ne_one_of_finitePerturbation (initial : Config)
    (h : PerturbationGeometry.FinitePerturbation initial false) (t : Nat) (η : Sample) :
    InfiniteGridRandomDynamics.synchronous initial t η ≠ oneConfig := by
  obtain ⟨L, a, hSupport⟩ :=
    (PerturbationGeometry.finitePerturbation_iff_exists_supported_translated initial).mp h
  exact synchronous_ne_one_of_supported_translated L a initial hSupport t η

theorem synchronous_eq_zero_background_of_finitePerturbation (initial : Config)
    (h : PerturbationGeometry.FinitePerturbation initial false) (η : Sample) :
    synchronous initial η = InfiniteGridRecoveryTime.synchronous initial η := by
  obtain ⟨L, a, hSupport⟩ :=
    (PerturbationGeometry.finitePerturbation_iff_exists_supported_translated initial).mp h
  exact synchronous_eq_zero_background_translated L a initial hSupport η

theorem homogeneous_translate_iff (a : Site) (state : Config) :
    Homogeneous (InfiniteGridTranslation.translate a state) ↔ Homogeneous state := by
  constructor
  · rintro (h | h)
    · left
      have hi := congrArg (InfiniteGridTranslation.translate (-a.1, -a.2)) h
      rw [InfiniteGridTranslation.translate_neg_translate] at hi
      exact hi
    · right
      have hi := congrArg (InfiniteGridTranslation.translate (-a.1, -a.2)) h
      rw [InfiniteGridTranslation.translate_neg_translate] at hi
      exact hi
  · rintro (rfl | rfl) <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem synchronous_translate_eq (a : Site) (initial : Config) (η : Sample) :
    synchronous (InfiniteGridTranslation.translate a initial)
        (InfiniteGridTranslationLaw.translateSample a η) = synchronous initial η := by
  apply RecoveryTimeTransport.time_eq_of_zero_iff
    (fun t ξ => hitState (InfiniteGridTranslation.translate a initial) t
      (InfiniteGridTranslationLaw.translateSample a ξ)) (hitState initial) false false η
  intro t
  rw [hitState_eq_false_iff, hitState_eq_false_iff,
    InfiniteGridTranslationLaw.synchronous_translate, homogeneous_translate_iff]

theorem synchronous_translate_map (a : Site) (initial : Config) :
    Measure.map (synchronous (InfiniteGridTranslation.translate a initial))
        InfiniteGridRandomDynamics.measure =
      Measure.map (synchronous initial) InfiniteGridRandomDynamics.measure := by
  conv_lhs => rw [← InfiniteGridTranslationLaw.translateSample_map_measure a]
  rw [Measure.map_map (synchronous_measurable _)
    (InfiniteGridTranslationLaw.translateSample_measurable a)]
  congr 1
  exact funext (synchronous_translate_eq a initial)

theorem complement_involutive (state : Config) :
    InfiniteGridComplement.complementConfig (InfiniteGridComplement.complementConfig state) =
      state := by
  funext v
  simp only [InfiniteGridComplement.complementConfig, Bool.not_not]

theorem homogeneous_complement_iff (state : Config) :
    Homogeneous (InfiniteGridComplement.complementConfig state) ↔ Homogeneous state := by
  have hi : ∀ f : Config, Homogeneous f →
      Homogeneous (InfiniteGridComplement.complementConfig f) := by
    intro f hf
    rcases hf with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  constructor
  · intro h
    simpa only [complement_involutive] using hi _ h
  · exact hi state

theorem synchronous_complement_eq (initial : Config) (η : Sample) :
    synchronous (InfiniteGridComplement.complementConfig initial)
        (InfiniteGridComplement.complementSample η) = synchronous initial η := by
  apply RecoveryTimeTransport.time_eq_of_zero_iff
    (fun t ξ => hitState (InfiniteGridComplement.complementConfig initial) t
      (InfiniteGridComplement.complementSample ξ)) (hitState initial) false false η
  intro t
  rw [hitState_eq_false_iff, hitState_eq_false_iff,
    InfiniteGridComplement.random_synchronous_complement, homogeneous_complement_iff]

theorem synchronous_complement_map (initial : Config) :
    Measure.map (synchronous (InfiniteGridComplement.complementConfig initial))
        InfiniteGridRandomDynamics.measure =
      Measure.map (synchronous initial) InfiniteGridRandomDynamics.measure := by
  have hm : Measure.map InfiniteGridComplement.complementSample
      InfiniteGridRandomDynamics.measure = InfiniteGridRandomDynamics.measure :=
    InfiniteGridComplement.complementSample_map InfiniteGridRandomDynamics.Event
  conv_lhs => rw [← hm]
  rw [Measure.map_map (synchronous_measurable _)
    (InfiniteGridComplement.complementSample_measurable _)]
  congr 1
  exact funext (synchronous_complement_eq initial)

theorem complement_finitePerturbation (initial : Config)
    (h : PerturbationGeometry.FinitePerturbation initial true) :
    PerturbationGeometry.FinitePerturbation
      (InfiniteGridComplement.complementConfig initial) false := by
  have heq : PerturbationGeometry.difference
      (InfiniteGridComplement.complementConfig initial) false =
      PerturbationGeometry.difference initial true := by
    ext v
    cases hv : initial v <;>
      simp [PerturbationGeometry.difference, InfiniteGridComplement.complementConfig, hv]
  change (PerturbationGeometry.difference
    (InfiniteGridComplement.complementConfig initial) false).Finite
  rw [heq]
  exact h

theorem synchronous_ne_zero_of_finitePerturbation (initial : Config)
    (h : PerturbationGeometry.FinitePerturbation initial true) (t : Nat) (η : Sample) :
    InfiniteGridRandomDynamics.synchronous initial t η ≠ zeroConfig := by
  intro hz
  have hn := synchronous_ne_one_of_finitePerturbation
    (InfiniteGridComplement.complementConfig initial) (complement_finitePerturbation initial h)
    t (InfiniteGridComplement.complementSample η)
  apply hn
  rw [InfiniteGridComplement.random_synchronous_complement, hz]
  rfl

theorem synchronous_eq_one_background_of_finitePerturbation (initial : Config)
    (h : PerturbationGeometry.FinitePerturbation initial true) (η : Sample) :
    synchronous initial η = InfiniteGridComplement.targetOneSynchronous initial η := by
  calc
    synchronous initial η =
        synchronous (InfiniteGridComplement.complementConfig initial)
          (InfiniteGridComplement.complementSample η) :=
      (synchronous_complement_eq initial η).symm
    _ = InfiniteGridRecoveryTime.synchronous (InfiniteGridComplement.complementConfig initial)
          (InfiniteGridComplement.complementSample η) :=
      synchronous_eq_zero_background_of_finitePerturbation _
        (complement_finitePerturbation initial h) _
    _ = InfiniteGridComplement.targetOneSynchronous initial η :=
      (InfiniteGridComplement.targetOneSynchronous_eq_zero_complement initial η).symm

theorem synchronous_eq_background_of_finitePerturbation (initial : Config) (background : Bool)
    (h : PerturbationGeometry.FinitePerturbation initial background) (η : Sample) :
    synchronous initial η = ExtendedRecoveryTime.time
      (InfiniteGridRandomDynamics.synchronous initial) (fun _ => background) η := by
  cases background with
  | false => exact synchronous_eq_zero_background_of_finitePerturbation initial h η
  | true => exact synchronous_eq_one_background_of_finitePerturbation initial h η

end MathResearchAnalysis.HomogeneousRecoveryTime

module
public import CoordinateResponseOrder
public import GeneralTankCdf
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.RateBoxMaximum
open MeasureTheory ProbabilityTheory Set
open MathExploration.TankResponse

structure RateParams where
  a : Real
  b : Real
  e : Real
  f : Real

structure RateBox where
  aLo : Real
  aHi : Real
  bLo : Real
  bHi : Real
  eLo : Real
  eHi : Real
  fLo : Real
  fHi : Real
  aLo_pos : 0 < aLo
  bLo_pos : 0 < bLo
  eLo_nonneg : 0 ≤ eLo
  fLo_nonneg : 0 ≤ fLo
  exitLo_pos : 0 < eLo + fLo
  a_nonempty : aLo ≤ aHi
  b_nonempty : bLo ≤ bHi
  e_nonempty : eLo ≤ eHi
  f_nonempty : fLo ≤ fHi

def allowedRates (K : RateBox) : Set RateParams :=
  {p | K.aLo ≤ p.a ∧ p.a ≤ K.aHi ∧ K.bLo ≤ p.b ∧ p.b ≤ K.bHi ∧
    K.eLo ≤ p.e ∧ p.e ≤ K.eHi ∧ K.fLo ≤ p.f ∧ p.f ≤ K.fHi}

def fStar (B E flo F : Real) : Real := if E ≤ B then F else flo

def corner (K : RateBox) : RateParams :=
  ⟨K.aHi, K.bHi, K.eHi, fStar K.bHi K.eHi K.fLo K.fHi⟩

theorem corner_mem (K : RateBox) : corner K ∈ allowedRates K := by
  by_cases h : K.eHi ≤ K.bHi
  · simp only [allowedRates, mem_setOf_eq, corner, fStar, if_pos h]
    exact ⟨K.a_nonempty, le_rfl, K.b_nonempty, le_rfl,
      K.e_nonempty, le_rfl, K.f_nonempty, le_rfl⟩
  · simp only [allowedRates, mem_setOf_eq, corner, fStar, if_neg h]
    exact ⟨K.a_nonempty, le_rfl, K.b_nonempty, le_rfl,
      K.e_nonempty, le_rfl, le_rfl, K.f_nonempty⟩

theorem allowed_valid (K : RateBox) (p : RateParams) (hp : p ∈ allowedRates K) :
    0 < p.a ∧ 0 < p.b ∧ 0 ≤ p.e ∧ 0 ≤ p.f ∧ 0 < p.e + p.f := by
  rcases hp with ⟨ha, _, hb, _, he, _, hf, _⟩
  exact ⟨lt_of_lt_of_le K.aLo_pos ha, lt_of_lt_of_le K.bLo_pos hb,
    le_trans K.eLo_nonneg he, le_trans K.fLo_nonneg hf,
    lt_of_lt_of_le K.exitLo_pos (add_le_add he hf)⟩

theorem x2_le_corner (K : RateBox) (p : RateParams) (hp : p ∈ allowedRates K)
    (t : Real) (ht : 0 ≤ t) :
    x2 p.a p.b p.e p.f t ≤ x2 (corner K).a (corner K).b (corner K).e (corner K).f t := by
  have hv := allowed_valid K p hp
  have haHi : 0 ≤ K.aHi := le_trans hv.1.le hp.2.1
  calc
    x2 p.a p.b p.e p.f t ≤ x2 K.aHi p.b p.e p.f t :=
      x2_mono_a p.a K.aHi p.b p.e p.f hv.2.1.le hv.2.2.1 hv.2.2.2.1 hp.2.1 t ht
    _ ≤ x2 K.aHi K.bHi p.e p.f t :=
      x2_mono_b K.aHi p.b K.bHi p.e p.f haHi hv.2.2.2.1 hp.2.2.2.1 t ht
    _ ≤ x2 K.aHi K.bHi K.eHi p.f t :=
      x2_mono_e K.aHi K.bHi p.e K.eHi p.f haHi hv.2.2.2.1 hp.2.2.2.2.2.1 t ht
    _ ≤ x2 (corner K).a (corner K).b (corner K).e (corner K).f t := by
      by_cases h : K.eHi ≤ K.bHi
      · simp only [corner, fStar, if_pos h]
        exact x2_mono_f_of_e_le_b K.aHi K.bHi K.eHi p.f K.fHi haHi h
          hp.2.2.2.2.2.2.2 t ht
      · simp only [corner, fStar, if_neg h]
        exact x2_antitone_f_of_b_le_e K.aHi K.bHi K.eHi K.fLo p.f haHi
          (le_of_lt (lt_of_not_ge h)) hp.2.2.2.2.2.2.1 t ht

abbrev Allowed (K : RateBox) := {p : RateParams // p ∈ allowedRates K}

def selected (K : RateBox) : Allowed K := ⟨corner K, corner_mem K⟩

def actualLaw (K : RateBox) (p : Allowed K) : Measure BranchedLaw.Sample :=
  BranchedLaw.law p.1.a p.1.b p.1.e p.1.f
    (allowed_valid K p.1 p.2).2.2.1 (allowed_valid K p.1 p.2).2.2.2.1
    (allowed_valid K p.1 p.2).2.2.2.2

def actualTotalMeasure (K : RateBox) (p : Allowed K) : Measure Real :=
  BranchedLaw.totalMeasure p.1.a p.1.b p.1.e p.1.f
    (allowed_valid K p.1 p.2).2.2.1 (allowed_valid K p.1 p.2).2.2.2.1
    (allowed_valid K p.1 p.2).2.2.2.2

theorem actualLaw_probability (K : RateBox) (p : Allowed K) :
    IsProbabilityMeasure (actualLaw K p) := by
  exact BranchedLaw.law_probability p.1.a p.1.b p.1.e p.1.f
    (allowed_valid K p.1 p.2).1 (allowed_valid K p.1 p.2).2.1
    (allowed_valid K p.1 p.2).2.2.1 (allowed_valid K p.1 p.2).2.2.2.1
    (allowed_valid K p.1 p.2).2.2.2.2

theorem actualTotalMeasure_probability (K : RateBox) (p : Allowed K) :
    IsProbabilityMeasure (actualTotalMeasure K p) := by
  exact BranchedLaw.totalMeasure_probability p.1.a p.1.b p.1.e p.1.f
    (allowed_valid K p.1 p.2).1 (allowed_valid K p.1 p.2).2.1
    (allowed_valid K p.1 p.2).2.2.1 (allowed_valid K p.1 p.2).2.2.2.1
    (allowed_valid K p.1 p.2).2.2.2.2

def cdfValue (K : RateBox) (p : Allowed K) (t : Real) : Real :=
  cdf (actualTotalMeasure K p) t

def eventValue (K : RateBox) (p : Allowed K) (t : Real) : Real :=
  (actualLaw K p).real {ω | BranchedLaw.total ω ≤ t}

def cdfValues (K : RateBox) (t : Real) : Set Real :=
  Set.range (fun p : Allowed K => cdfValue K p t)

def eventValues (K : RateBox) (t : Real) : Set Real :=
  Set.range (fun p : Allowed K => eventValue K p t)

theorem cdfValue_eq_x2 (K : RateBox) (p : Allowed K) (t : Real) (ht : 0 ≤ t) :
    cdfValue K p t = x2 p.1.a p.1.b p.1.e p.1.f t := by
  exact GeneralTankCdf.cdf_totalMeasure_eq_x2 p.1.a p.1.b p.1.e p.1.f
    (allowed_valid K p.1 p.2).1 (allowed_valid K p.1 p.2).2.1
    (allowed_valid K p.1 p.2).2.2.1 (allowed_valid K p.1 p.2).2.2.2.1
    (allowed_valid K p.1 p.2).2.2.2.2 t ht

theorem eventValue_eq_x2 (K : RateBox) (p : Allowed K) (t : Real) (ht : 0 ≤ t) :
    eventValue K p t = x2 p.1.a p.1.b p.1.e p.1.f t := by
  exact GeneralTankCdf.total_event_eq_x2 p.1.a p.1.b p.1.e p.1.f
    (allowed_valid K p.1 p.2).1 (allowed_valid K p.1 p.2).2.1
    (allowed_valid K p.1 p.2).2.2.1 (allowed_valid K p.1 p.2).2.2.2.1
    (allowed_valid K p.1 p.2).2.2.2.2 t ht

theorem selected_cdf_isGreatest (K : RateBox) (t : Real) (ht : 0 ≤ t) :
    IsGreatest (cdfValues K t) (cdfValue K (selected K) t) := by
  constructor
  · exact ⟨selected K, rfl⟩
  · intro y hy
    rcases hy with ⟨p, rfl⟩
    rw [cdfValue_eq_x2 K p t ht, cdfValue_eq_x2 K (selected K) t ht]
    exact x2_le_corner K p.1 p.2 t ht

theorem selected_event_isGreatest (K : RateBox) (t : Real) (ht : 0 ≤ t) :
    IsGreatest (eventValues K t) (eventValue K (selected K) t) := by
  constructor
  · exact ⟨selected K, rfl⟩
  · intro y hy
    rcases hy with ⟨p, rfl⟩
    rw [eventValue_eq_x2 K p t ht, eventValue_eq_x2 K (selected K) t ht]
    exact x2_le_corner K p.1 p.2 t ht

theorem selected_maximizes_all_times (K : RateBox) :
    ∀ t : Real, 0 ≤ t →
      IsGreatest (cdfValues K t) (cdfValue K (selected K) t) ∧
      IsGreatest (eventValues K t) (eventValue K (selected K) t) := by
  intro t ht
  exact ⟨selected_cdf_isGreatest K t ht, selected_event_isGreatest K t ht⟩

end MathExploration.RateBoxMaximum
#print axioms MathExploration.RateBoxMaximum.RateParams
#print axioms MathExploration.RateBoxMaximum.RateBox
#print axioms MathExploration.RateBoxMaximum.allowedRates
#print axioms MathExploration.RateBoxMaximum.fStar
#print axioms MathExploration.RateBoxMaximum.corner
#print axioms MathExploration.RateBoxMaximum.corner_mem
#print axioms MathExploration.RateBoxMaximum.allowed_valid
#print axioms MathExploration.RateBoxMaximum.x2_le_corner
#print axioms MathExploration.RateBoxMaximum.Allowed
#print axioms MathExploration.RateBoxMaximum.selected
#print axioms MathExploration.RateBoxMaximum.actualLaw
#print axioms MathExploration.RateBoxMaximum.actualTotalMeasure
#print axioms MathExploration.RateBoxMaximum.actualLaw_probability
#print axioms MathExploration.RateBoxMaximum.actualTotalMeasure_probability
#print axioms MathExploration.RateBoxMaximum.cdfValue
#print axioms MathExploration.RateBoxMaximum.eventValue
#print axioms MathExploration.RateBoxMaximum.cdfValues
#print axioms MathExploration.RateBoxMaximum.eventValues
#print axioms MathExploration.RateBoxMaximum.cdfValue_eq_x2
#print axioms MathExploration.RateBoxMaximum.eventValue_eq_x2
#print axioms MathExploration.RateBoxMaximum.selected_cdf_isGreatest
#print axioms MathExploration.RateBoxMaximum.selected_event_isGreatest
#print axioms MathExploration.RateBoxMaximum.selected_maximizes_all_times
#print axioms MathExploration.RateBoxMaximum.RateParams.mk
#print axioms MathExploration.RateBoxMaximum.RateParams.a
#print axioms MathExploration.RateBoxMaximum.RateParams.b
#print axioms MathExploration.RateBoxMaximum.RateParams.e
#print axioms MathExploration.RateBoxMaximum.RateParams.f
#print axioms MathExploration.RateBoxMaximum.RateBox.mk
#print axioms MathExploration.RateBoxMaximum.RateBox.aLo
#print axioms MathExploration.RateBoxMaximum.RateBox.aHi
#print axioms MathExploration.RateBoxMaximum.RateBox.bLo
#print axioms MathExploration.RateBoxMaximum.RateBox.bHi
#print axioms MathExploration.RateBoxMaximum.RateBox.eLo
#print axioms MathExploration.RateBoxMaximum.RateBox.eHi
#print axioms MathExploration.RateBoxMaximum.RateBox.fLo
#print axioms MathExploration.RateBoxMaximum.RateBox.fHi
#print axioms MathExploration.RateBoxMaximum.RateBox.aLo_pos
#print axioms MathExploration.RateBoxMaximum.RateBox.bLo_pos
#print axioms MathExploration.RateBoxMaximum.RateBox.eLo_nonneg
#print axioms MathExploration.RateBoxMaximum.RateBox.fLo_nonneg
#print axioms MathExploration.RateBoxMaximum.RateBox.exitLo_pos
#print axioms MathExploration.RateBoxMaximum.RateBox.a_nonempty
#print axioms MathExploration.RateBoxMaximum.RateBox.b_nonempty
#print axioms MathExploration.RateBoxMaximum.RateBox.e_nonempty
#print axioms MathExploration.RateBoxMaximum.RateBox.f_nonempty

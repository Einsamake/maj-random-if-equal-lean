module

public import MathResearchAnalysis.MixedClockDynkin

set_option autoImplicit false

/-!
# True one- and two-point moments of the mixed clock process

Every expectation uses the actual mixed endpoint under the original marked
clock law. Boolean bounds prove sample integrability before finite sums are
exchanged with expectations. Dynkin then gives the physical-time moment
integral equations, with the already identified rate-one-half path operator.
No moment equation, exclusion law, covariance sign or ODE is a premise.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.MixedClockMoments

open MeasureTheory Set
open DropletClockLaw (Sample Config)
open ClippedSquareCoordinates (parameter)
open MixedExclusionGenerator (Slot slotState pathEdges)
open FiniteExclusionGenerator (density oneParticle twoParticle)

/-- Actual slot occupation at elapsed real time, including the total-word fallback. -/
def occupation (L : Nat) (initial : Config L) (t : Real) (z : Sample L) :
    Slot (parameter L) → Bool :=
  slotState (MixedSquareClockLaw.endpoint (parameter L) t initial z)

/-- The real first moment under the original clock/mark product measure. -/
def rho (L : Nat) (initial : Config L) (t : Real) (i : Slot (parameter L)) : Real :=
  ∫ z : Sample L, density (occupation L initial t z) i ∂ClockWordMarks.measure (parameter L)

/-- The real simultaneous two-point moment; the same actual sample supplies both factors. -/
def g (L : Nat) (initial : Config L) (t : Real) (i j : Slot (parameter L)) : Real :=
  ∫ z : Sample L, density (occupation L initial t z) i*density (occupation L initial t z) j
    ∂ClockWordMarks.measure (parameter L)

theorem density_bounds {V : Type*} (η : V → Bool) (i : V) :
    0 ≤ density η i ∧ density η i ≤ 1 := by
  cases h : η i <;> simp [density,h]

/-- The bounds are pointwise Boolean facts, independent of shape or any clock event. -/
theorem occupation_density_bounds (L : Nat) (initial : Config L) (t : Real)
    (i : Slot (parameter L)) (z : Sample L) :
    0 ≤ density (occupation L initial t z) i ∧ density (occupation L initial t z) i ≤ 1 := by
  cases h : occupation L initial t z i <;> simp [density,h]

theorem occupation_product_bounds (L : Nat) (initial : Config L) (t : Real)
    (i j : Slot (parameter L)) (z : Sample L) :
    0 ≤ density (occupation L initial t z) i*density (occupation L initial t z) j ∧
      density (occupation L initial t z) i*density (occupation L initial t z) j ≤ 1 := by
  have hi := occupation_density_bounds L initial t i z
  have hj := occupation_density_bounds L initial t j z
  exact ⟨mul_nonneg hi.1 hj.1, by nlinarith⟩

theorem density_measurable (L : Nat) (initial : Config L) (t : Real) (i : Slot (parameter L)) :
    Measurable (fun z : Sample L => density (occupation L initial t z) i) := by
  have hF : Measurable (fun f : Config L => density (slotState f) i) := measurable_of_countable _
  exact hF.comp (MixedSquareClockLaw.endpoint_measurable (parameter L) t initial)

theorem density_integrable (L : Nat) (initial : Config L) (t : Real) (i : Slot (parameter L)) :
    Integrable (fun z : Sample L => density (occupation L initial t z) i)
      (ClockWordMarks.measure (parameter L)) := by
  apply (integrable_const (1 : Real)).mono' (density_measurable L initial t i).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have hb := occupation_density_bounds L initial t i z
  simpa only [Pi.mul_apply,Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2

theorem density_product_integrable (L : Nat) (initial : Config L) (t : Real)
    (i j : Slot (parameter L)) :
    Integrable (fun z : Sample L => density (occupation L initial t z) i*density (occupation L initial t z) j)
      (ClockWordMarks.measure (parameter L)) := by
  apply (integrable_const (1 : Real)).mono'
    ((density_measurable L initial t i).mul (density_measurable L initial t j)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have hb := occupation_product_bounds L initial t i j z
  simpa only [Pi.mul_apply,Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2

theorem rho_nonneg (L : Nat) (initial : Config L) (t : Real) (i : Slot (parameter L)) :
    0 ≤ rho L initial t i :=
  integral_nonneg (fun z => (occupation_density_bounds L initial t i z).1)

theorem rho_le_one (L : Nat) (initial : Config L) (t : Real) (i : Slot (parameter L)) :
    rho L initial t i ≤ 1 := by
  calc
    _ ≤ ∫ _z : Sample L, (1 : Real) ∂ClockWordMarks.measure (parameter L) :=
      integral_mono (density_integrable L initial t i) (integrable_const _)
        (fun z => (occupation_density_bounds L initial t i z).2)
    _ = _ := by simp

theorem g_nonneg (L : Nat) (initial : Config L) (t : Real) (i j : Slot (parameter L)) :
    0 ≤ g L initial t i j :=
  integral_nonneg (fun z => (occupation_product_bounds L initial t i j z).1)

theorem g_le_one (L : Nat) (initial : Config L) (t : Real) (i j : Slot (parameter L)) :
    g L initial t i j ≤ 1 := by
  calc
    _ ≤ ∫ _z : Sample L, (1 : Real) ∂ClockWordMarks.measure (parameter L) :=
      integral_mono (density_product_integrable L initial t i j) (integrable_const _)
        (fun z => (occupation_product_bounds L initial t i j z).2)
    _ = _ := by simp

theorem g_symm (L : Nat) (initial : Config L) (t : Real) (i j : Slot (parameter L)) :
    g L initial t i j = g L initial t j i := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)

theorem g_diagonal_eq_rho (L : Nat) (initial : Config L) (t : Real) (i : Slot (parameter L)) :
    g L initial t i i = rho L initial t i := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  cases h : occupation L initial t z i <;> simp [density,h]

/-- Original clocks have no event at time zero on one full-probability set. -/
theorem occupation_zero_ae (L : Nat) (initial : Config L) :
    ∀ᵐ z ∂ClockWordMarks.measure (parameter L), occupation L initial 0 z = slotState initial := by
  filter_upwards [ActualPreState.marked_all_events_positive_ae L] with z hz
  unfold occupation MixedSquareClockLaw.endpoint
  rw [ClockWordConsistency.word_zero_of_positive z.1 hz]
  rfl

theorem rho_zero_eq_initial (L : Nat) (initial : Config L) (i : Slot (parameter L)) :
    rho L initial 0 i = density (slotState initial) i := by
  calc
    _ = ∫ _z : Sample L, density (slotState initial) i ∂ClockWordMarks.measure (parameter L) :=
      integral_congr_ae ((occupation_zero_ae L initial).mono (fun _ hz => by rw [hz]))
    _ = _ := by simp

theorem g_zero_eq_initial (L : Nat) (initial : Config L) (i j : Slot (parameter L)) :
    g L initial 0 i j = density (slotState initial) i*density (slotState initial) j := by
  calc
    _ = ∫ _z : Sample L, density (slotState initial) i*density (slotState initial) j
        ∂ClockWordMarks.measure (parameter L) :=
      integral_congr_ae ((occupation_zero_ae L initial).mono (fun _ hz => by rw [hz]))
    _ = _ := by simp

/-- Every finite edge term is integrable before passing its sum through expectation. -/
theorem expected_oneParticle (L : Nat) (initial : Config L) (t : Real) (i : Slot (parameter L)) :
    (∫ z : Sample L, oneParticle (pathEdges (parameter L)) (density (occupation L initial t z)) i
      ∂ClockWordMarks.measure (parameter L)) =
      oneParticle (pathEdges (parameter L)) (rho L initial t) i := by
  unfold oneParticle
  rw [integral_finsetSum _ (fun e _ =>
    ((density_integrable L initial t (Equiv.swap e.1 e.2 i)).sub
      (density_integrable L initial t i)).div_const 2)]
  apply Finset.sum_congr rfl
  intro e he
  rw [integral_div,integral_sub (density_integrable L initial t (Equiv.swap e.1 e.2 i))
    (density_integrable L initial t i)]
  rfl

/-- Both factors use the same sample; only linearity of the finite two-index
operator is used, never independence of the particle occupations. -/
theorem expected_twoParticle (L : Nat) (initial : Config L) (t : Real) (i j : Slot (parameter L)) :
    (∫ z : Sample L, twoParticle (pathEdges (parameter L))
      (fun a b => density (occupation L initial t z) a*density (occupation L initial t z) b) i j
      ∂ClockWordMarks.measure (parameter L)) =
      twoParticle (pathEdges (parameter L)) (g L initial t) i j := by
  unfold twoParticle
  rw [integral_finsetSum _ (fun e _ =>
    ((density_product_integrable L initial t (Equiv.swap e.1 e.2 i) (Equiv.swap e.1 e.2 j)).sub
      (density_product_integrable L initial t i j)).div_const 2)]
  apply Finset.sum_congr rfl
  intro e he
  rw [integral_div,integral_sub
    (density_product_integrable L initial t (Equiv.swap e.1 e.2 i) (Equiv.swap e.1 e.2 j))
    (density_product_integrable L initial t i j)]
  rfl

theorem rho_rhs_integrable (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (T : NNReal) (i : Slot (parameter L)) :
    Integrable (fun u : Real => oneParticle (pathEdges (parameter L)) (rho L initial u) i)
      ((volume : Measure Real).restrict (Ioc 0 (T : Real))) := by
  apply (MixedClockDynkin.generator_time_mean_integrable L initial hinit (fun η => density η i) T).congr
  apply Filter.Eventually.of_forall
  intro u
  simpa only [occupation,FiniteExclusionGenerator.generator_density] using expected_oneParticle L initial u i

theorem g_rhs_integrable (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (T : NNReal) (i j : Slot (parameter L)) :
    Integrable (fun u : Real => twoParticle (pathEdges (parameter L)) (g L initial u) i j)
      ((volume : Measure Real).restrict (Ioc 0 (T : Real))) := by
  apply (MixedClockDynkin.generator_time_mean_integrable L initial hinit
    (fun η => density η i*density η j) T).congr
  apply Filter.Eventually.of_forall
  intro u
  simpa only [occupation,FiniteExclusionGenerator.generator_density_product] using expected_twoParticle L initial u i j

/-- The genuine physical-time first-moment integral equation. -/
theorem rho_integral (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (T : NNReal) (i : Slot (parameter L)) :
    rho L initial (T : Real) i = rho L initial 0 i +
      ∫ u : Real in Ioc 0 (T : Real), oneParticle (pathEdges (parameter L)) (rho L initial u) i := by
  have h := MixedClockDynkin.expected_observable_dynkin L initial hinit (fun η => density η i) T
  change rho L initial (T : Real) i = density (slotState initial) i +
    ∫ u : Real in Ioc 0 (T : Real), ∫ z : Sample L,
      FiniteExclusionGenerator.generator (pathEdges (parameter L)) (fun η => density η i)
        (occupation L initial u z) ∂ClockWordMarks.measure (parameter L) at h
  simp_rw [FiniteExclusionGenerator.generator_density,expected_oneParticle] at h
  rw [rho_zero_eq_initial]
  exact h

/-- The genuine simultaneous two-point integral equation, including equal indices. -/
theorem g_integral (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (T : NNReal) (i j : Slot (parameter L)) :
    g L initial (T : Real) i j = g L initial 0 i j +
      ∫ u : Real in Ioc 0 (T : Real), twoParticle (pathEdges (parameter L)) (g L initial u) i j := by
  have h := MixedClockDynkin.expected_observable_dynkin L initial hinit
    (fun η => density η i*density η j) T
  change g L initial (T : Real) i j = density (slotState initial) i*density (slotState initial) j +
    ∫ u : Real in Ioc 0 (T : Real), ∫ z : Sample L,
      FiniteExclusionGenerator.generator (pathEdges (parameter L)) (fun η => density η i*density η j)
        (occupation L initial u z) ∂ClockWordMarks.measure (parameter L) at h
  simp_rw [FiniteExclusionGenerator.generator_density_product,expected_twoParticle] at h
  rw [g_zero_eq_initial]
  exact h

end MathResearchAnalysis.MixedClockMoments


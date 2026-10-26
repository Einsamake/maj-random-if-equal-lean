module

public import MathResearchAnalysis.MixedClockCovariance
public import Mathlib.Probability.Moments.Variance

set_option autoImplicit false

/-!
# Actual right-half count and its variance under the original marked clock law

The count is the sum of the actual Boolean occupations in the right half of
its finite path. Integrability precedes each exchange with a finite sum. The
second moment uses the same sample twice: diagonal terms are Bernoulli first
moments, and only distinct indices use the proved nonpositive covariance.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.MixedRightCountMoments

open MeasureTheory Set
open DropletClockLaw (Sample Config)
open ClippedSquareCoordinates (parameter)
open MixedExclusionGenerator (Slot slotState)
open FiniteExclusionGenerator (density)
open MixedClockMoments (occupation rho g)

/-- The right half has precisely one slot for each physical row. -/
def rightSlots (M : Nat) : Finset (Fin (2*M)) :=
  Finset.univ.filter (fun i => M ≤ i.val)

theorem rightSlots_card (M : Nat) : (rightSlots M).card = M := by
  classical
  calc
    _ = (Finset.univ : Finset (Fin M)).card := by
      apply Finset.card_bij (fun i hi =>
        (⟨i.val-M,by have h := (Finset.mem_filter.mp hi).2; omega⟩ : Fin M))
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj he
        have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        have hval := congrArg Fin.val he
        change i.val-M = j.val-M at hval
        apply Fin.ext
        omega
      · intro j hj
        refine ⟨⟨M+j.val,by omega⟩,?_,?_⟩
        · simp [rightSlots]
        · apply Fin.ext
          simp
    _ = M := Finset.card_fin M

/-- A real-valued count on the actual sample, with the original clock law. -/
def count (L : Nat) (initial : Config L) (t : Real) (z : Sample L) : Real :=
  ∑ i ∈ rightSlots (parameter L+2), density (occupation L initial t z) i

/-- Its true expectation, rather than the square root of a second moment. -/
def mean (L : Nat) (initial : Config L) (t : Real) : Real :=
  ∫ z : Sample L, count L initial t z ∂ClockWordMarks.measure (parameter L)

/-- The centered second moment under the same original probability measure. -/
def variance (L : Nat) (initial : Config L) (t : Real) : Real :=
  ∫ z : Sample L, (count L initial t z-mean L initial t)^2
    ∂ClockWordMarks.measure (parameter L)

theorem count_measurable (L : Nat) (initial : Config L) (t : Real) :
    Measurable (count L initial t) := by
  exact Finset.measurable_sum _ fun i _ => MixedClockMoments.density_measurable L initial t i

theorem count_integrable (L : Nat) (initial : Config L) (t : Real) :
    Integrable (count L initial t) (ClockWordMarks.measure (parameter L)) :=
  integrable_finsetSum _ (fun i _ => MixedClockMoments.density_integrable L initial t i)

theorem count_nonneg (L : Nat) (initial : Config L) (t : Real) (z : Sample L) :
    0 ≤ count L initial t z :=
  Finset.sum_nonneg (fun i _ => (MixedClockMoments.occupation_density_bounds L initial t i z).1)

theorem count_le_side (L : Nat) (initial : Config L) (t : Real) (z : Sample L) :
    count L initial t z ≤ (parameter L+2 : Real) := by
  calc
    _ ≤ ∑ _i ∈ rightSlots (parameter L+2), (1 : Real) :=
      Finset.sum_le_sum (fun i _ => (MixedClockMoments.occupation_density_bounds L initial t i z).2)
    _ = _ := by simp [rightSlots_card]

/-- The literal occupation sum equals the existing labelled-row count, on every
sample and every time; monotonicity is supplied by actual update invariance. -/
theorem count_eq_rightCount (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (z : Sample L) :
    count L initial t z =
      (YoungParticles.rightCount (MixedSquareClockLaw.endpoint (parameter L) t initial z) : Real) := by
  classical
  let f := MixedSquareClockLaw.endpoint (parameter L) t initial z
  have hf : Monotone f := MixedSquareClockLaw.endpoint_monotone_shape _ t initial hinit z
  rw [YoungParticleMoves.rightCount_eq_rightSlotCard hf]
  unfold count occupation
  change (∑ i ∈ rightSlots (parameter L+2), density (slotState f) i) = _
  calc
    _ = ∑ i ∈ rightSlots (parameter L+2),
        if i ∈ YoungParticles.particles f then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hm : i ∈ YoungParticles.particles f <;> simp [density,slotState,hm]
    _ = _ := by
      rw [Finset.sum_boole]
      norm_cast
      congr 1
      ext i
      simp [rightSlots,and_comm]

theorem mean_eq_sum_rho (L : Nat) (initial : Config L) (t : Real) :
    mean L initial t = ∑ i ∈ rightSlots (parameter L+2), rho L initial t i := by
  unfold mean count
  exact integral_finsetSum _ (fun i _ => MixedClockMoments.density_integrable L initial t i)

theorem count_square_eq_sum_products (L : Nat) (initial : Config L) (t : Real)
    (z : Sample L) :
    (count L initial t z)^2 = ∑ i ∈ rightSlots (parameter L+2),
      ∑ j ∈ rightSlots (parameter L+2),
        density (occupation L initial t z) i*density (occupation L initial t z) j := by
  unfold count
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.mul_sum _ _ _

theorem count_square_integrable (L : Nat) (initial : Config L) (t : Real) :
    Integrable (fun z => (count L initial t z)^2) (ClockWordMarks.measure (parameter L)) := by
  have h := integrable_finsetSum (rightSlots (parameter L+2)) (fun i _ =>
    integrable_finsetSum (rightSlots (parameter L+2)) (fun j _ =>
      MixedClockMoments.density_product_integrable L initial t i j))
  exact h.congr (Filter.Eventually.of_forall (fun z => (count_square_eq_sum_products L initial t z).symm))

theorem second_moment_eq_sum_g (L : Nat) (initial : Config L) (t : Real) :
    (∫ z : Sample L, (count L initial t z)^2 ∂ClockWordMarks.measure (parameter L)) =
      ∑ i ∈ rightSlots (parameter L+2), ∑ j ∈ rightSlots (parameter L+2), g L initial t i j := by
  calc
    _ = ∫ z : Sample L, ∑ i ∈ rightSlots (parameter L+2), ∑ j ∈ rightSlots (parameter L+2),
        density (occupation L initial t z) i*density (occupation L initial t z) j
        ∂ClockWordMarks.measure (parameter L) :=
      integral_congr_ae (Filter.Eventually.of_forall (count_square_eq_sum_products L initial t))
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => MixedClockMoments.density_product_integrable L initial t i j))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum _ (fun j _ => MixedClockMoments.density_product_integrable L initial t i j)

theorem centered_square_integrable (L : Nat) (initial : Config L) (t : Real) :
    Integrable (fun z => (count L initial t z-mean L initial t)^2)
      (ClockWordMarks.measure (parameter L)) := by
  have h := ((count_square_integrable L initial t).sub
    ((count_integrable L initial t).const_mul (2*mean L initial t))).add
      (integrable_const ((mean L initial t)^2))
  apply h.congr
  exact Filter.Eventually.of_forall (fun z => by dsimp; ring)

theorem variance_eq_second_moment_sub_square (L : Nat) (initial : Config L) (t : Real) :
    variance L initial t =
      (∫ z : Sample L, (count L initial t z)^2 ∂ClockWordMarks.measure (parameter L)) -
        (mean L initial t)^2 := by
  unfold variance
  calc
    _ = ∫ z : Sample L, ((count L initial t z)^2 -
        (2*mean L initial t)*count L initial t z) + (mean L initial t)^2
        ∂ClockWordMarks.measure (parameter L) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    _ = _ := by
      rw [integral_add (f := fun z : Sample L => (count L initial t z)^2 -
          (2*mean L initial t)*count L initial t z)
        (g := fun _ : Sample L => (mean L initial t)^2)
        ((count_square_integrable L initial t).sub
          ((count_integrable L initial t).const_mul (2*mean L initial t))) (integrable_const _),
        integral_sub (f := fun z : Sample L => (count L initial t z)^2)
          (g := fun z : Sample L => (2*mean L initial t)*count L initial t z)
          (count_square_integrable L initial t)
          ((count_integrable L initial t).const_mul (2*mean L initial t)), integral_const_mul]
      change _ - (2*mean L initial t)*mean L initial t + _ = _
      simp only [integral_const,probReal_univ,one_smul]
      ring

/-- Off-diagonal terms use the actual covariance theorem; the diagonal remains
its Bernoulli variance instead of being falsely treated as nonpositive. -/
theorem second_moment_le_mean_square_add_bernoulli (L : Nat) (initial : Config L)
    (hinit : Monotone initial) (t : Real) (ht : 0 ≤ t) :
    (∫ z : Sample L, (count L initial t z)^2 ∂ClockWordMarks.measure (parameter L)) ≤
      (mean L initial t)^2 + ∑ i ∈ rightSlots (parameter L+2),
        rho L initial t i*(1-rho L initial t i) := by
  classical
  rw [second_moment_eq_sum_g,mean_eq_sum_rho]
  calc
    _ ≤ ∑ i ∈ rightSlots (parameter L+2), ∑ j ∈ rightSlots (parameter L+2),
        (rho L initial t i*rho L initial t j +
          if i=j then rho L initial t i*(1-rho L initial t i) else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i=j
      · subst j
        rw [MixedClockMoments.g_diagonal_eq_rho]
        simp only [ite_true]
        nlinarith
      · simpa only [ite_eq_right hij,add_zero] using
          MixedClockCovariance.offdiag_moment_le_product L initial hinit t ht i j hij
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · rw [pow_two,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mul_sum _ _ _).symm
      · apply Finset.sum_congr rfl
        intro i hi
        simp [Finset.sum_ite_eq,hi]

theorem variance_le_bernoulli_sum (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (ht : 0 ≤ t) :
    variance L initial t ≤ ∑ i ∈ rightSlots (parameter L+2),
      rho L initial t i*(1-rho L initial t i) := by
  rw [variance_eq_second_moment_sub_square]
  linarith [second_moment_le_mean_square_add_bernoulli L initial hinit t ht]

/-- The actual right-half count has variance at most M/4; this is not an
independence assertion about the occupied slots. -/
theorem variance_le_side_quarter (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (ht : 0 ≤ t) : variance L initial t ≤ (parameter L+2 : Real)/4 := by
  calc
    _ ≤ ∑ i ∈ rightSlots (parameter L+2), rho L initial t i*(1-rho L initial t i) :=
      variance_le_bernoulli_sum L initial hinit t ht
    _ ≤ ∑ _i ∈ rightSlots (parameter L+2), (1/4 : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [sq_nonneg (rho L initial t i-1/2)]
    _ = _ := by simp [rightSlots_card]; ring

/-- The actual count lies in L2 under the original probability law. -/
theorem count_memLp_two (L : Nat) (initial : Config L) (t : Real) :
    MemLp (count L initial t) 2 (ClockWordMarks.measure (parameter L)) :=
  (memLp_two_iff_integrable_sq (count_measurable L initial t).aestronglyMeasurable).2
    (count_square_integrable L initial t)

/-- Our displayed centered integral is exactly Mathlib's genuine variance. -/
theorem variance_eq_standard (L : Nat) (initial : Config L) (t : Real) :
    variance L initial t =
      ProbabilityTheory.variance (count L initial t) (ClockWordMarks.measure (parameter L)) := by
  symm
  exact ProbabilityTheory.variance_eq_integral (count_measurable L initial t).aemeasurable

theorem standard_variance_le_side_quarter (L : Nat) (initial : Config L)
    (hinit : Monotone initial) (t : Real) (ht : 0 ≤ t) :
    ProbabilityTheory.variance (count L initial t) (ClockWordMarks.measure (parameter L)) ≤
      (parameter L+2 : Real)/4 := by
  rw [←variance_eq_standard]
  exact variance_le_side_quarter L initial hinit t ht

end MathResearchAnalysis.MixedRightCountMoments

module
public import MathResearchAnalysis.FinitePermutationComparison
public import MathResearchAnalysis.ScalarHeatDecay
public import Mathlib.Tactic

set_option autoImplicit false

/-! Independent extension of the frozen finite-permutation comparison tool.
Nonnegative directed weights need not be symmetric, balanced or permutations.
The column-minus-row sum bound controls positive-part energy growth;
an exponential factor is enough for order preservation from zero energy.
These are classical cooperative-system facts, not a novelty assertion.
-/
@[expose] public noncomputable section
namespace MathExploration.DirectedNetworkComparison
open Set
open scoped BigOperators
open MathResearchAnalysis
variable {V : Type*} [Fintype V]

def rate (a : V → V → Real) (x : V → Real) (i : V) : Real :=
  ∑ j : V, a i j * (x j-x i)

def imbalance (a : V → V → Real) (i : V) : Real :=
  (∑ j : V, a j i)-(∑ j : V, a i j)

def energy (x : V → Real) : Real := ∑ i : V, PositivePartSquare.square (x i)

def leakedRate (a : V → V → Real) (d : V → Real) (x : V → Real) (i : V) : Real :=
  rate a x i-d i*x i

theorem sum_edge_difference (a : V → V → Real) (x : V → Real) :
    (∑ i : V, ∑ j : V, a i j *
      (PositivePartSquare.square (x j)-PositivePartSquare.square (x i))) =
    ∑ i : V, imbalance a i * PositivePartSquare.square (x i) := by
  classical
  calc
    _ = (∑ i : V, ∑ j : V, a i j*PositivePartSquare.square (x j)) -
        (∑ i : V, ∑ j : V, a i j*PositivePartSquare.square (x i)) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ j : V, (∑ i : V, a i j)*PositivePartSquare.square (x j)) -
        (∑ i : V, (∑ j : V, a i j)*PositivePartSquare.square (x i)) := by
      congr 1
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      unfold imbalance
      ring

theorem rate_flux_le_imbalance (a : V → V → Real) (ha : ∀ i j, 0≤a i j)
    (x : V → Real) :
    (∑ i : V, 2*max (x i) 0*rate a x i) ≤
      ∑ i : V, imbalance a i*PositivePartSquare.square (x i) := by
  classical
  calc
    _ = ∑ i : V, ∑ j : V, a i j*(2*max (x i) 0*(x j-x i)) := by
      unfold rate
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i : V, ∑ j : V, a i j*
        (PositivePartSquare.square (x j)-PositivePartSquare.square (x i)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (PositivePartSquare.supporting_inequality (x i) (x j)) (ha i j)
    _ = _ := sum_edge_difference a x

theorem rate_flux_le_energy (a : V → V → Real) (ha : ∀ i j, 0≤a i j)
    (K : Real) (hK : ∀ i, imbalance a i≤K) (x : V → Real) :
    (∑ i : V, 2*max (x i) 0*rate a x i) ≤ K*energy x := by
  apply (rate_flux_le_imbalance a ha x).trans
  calc
    _ ≤ ∑ i : V, K*PositivePartSquare.square (x i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hK i)
        (PositivePartSquare.square_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem max_mul_self (r : Real) : max r 0*r=PositivePartSquare.square r := by
  by_cases h : 0≤r
  · simp [PositivePartSquare.square, max_eq_left h, pow_two]
  · simp [PositivePartSquare.square, max_eq_right (le_of_not_ge h)]

theorem leaked_source_flux_le (a : V → V → Real) (ha : ∀ i j, 0≤a i j)
    (d : V → Real) (hd : ∀ i, 0≤d i) (K : Real) (hK : ∀ i, imbalance a i≤K)
    (x s : V → Real) (hs : ∀ i, 0≤s i) :
    (∑ i : V, 2*max (x i) 0*(leakedRate a d x i-s i)) ≤ K*energy x := by
  apply le_trans _ (rate_flux_le_energy a ha K hK x)
  apply Finset.sum_le_sum
  intro i _
  have hleak : 0≤2*d i*PositivePartSquare.square (x i) :=
    mul_nonneg (mul_nonneg (by norm_num) (hd i)) (PositivePartSquare.square_nonneg _)
  have hsource : 0≤2*max (x i) 0*s i :=
    mul_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) (hs i)
  have he : 2*max (x i) 0*(leakedRate a d x i-s i) =
      2*max (x i) 0*rate a x i - 2*d i*PositivePartSquare.square (x i) -
        2*max (x i) 0*s i := by
    unfold leakedRate
    rw [← max_mul_self]
    ring
  rw [he]
  linarith

theorem energy_nonneg (x : V → Real) : 0≤energy x :=
  Finset.sum_nonneg (fun _i _ => PositivePartSquare.square_nonneg _)

theorem nonpos (a : V → V → Real) (ha : ∀ i j, 0≤a i j)
    (d : V → Real) (hd : ∀ i, 0≤d i) (K : Real) (hK : ∀ i, imbalance a i≤K)
    (c s : Real → V → Real)
    (hc : ∀ i, ContinuousOn (fun t => c t i) (Ici 0))
    (hder : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun u => c u i) (leakedRate a d (c t) i-s t i) t)
    (hs : ∀ t : Real, 0<t → ∀ i, 0≤s t i)
    (hzero : ∀ i, c 0 i≤0) (t : Real) (ht : 0≤t) (i : V) : c t i≤0 := by
  classical
  let derivE := fun t => ∑ j : V, 2*max (c t j) 0*(leakedRate a d (c t) j-s t j)
  have hcont : ContinuousOn (fun u => energy (c u)) (Ici (0 : Real)) :=
    continuousOn_finsetSum _ (fun j _ => PositivePartSquare.square_continuous.comp_continuousOn (hc j))
  have hEder : ∀ u : Real, 0<u → HasDerivAt (fun v => energy (c v)) (derivE u) u := by
    intro u hu
    apply HasDerivAt.fun_sum (u := Finset.univ)
    intro j _
    simpa only [Function.comp_def] using
      (PositivePartSquare.hasDerivAt_square (c u j)).comp u (hder u hu j)
  have hinequality : ∀ u : Real, 0<u → derivE u+(-K)*energy (c u)≤0 := by
    intro u hu
    have h := leaked_source_flux_le a ha d hd K hK (c u) (s u) (hs u hu)
    change derivE u≤K*energy (c u) at h
    linarith
  have he0 : energy (c 0)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact (PositivePartSquare.square_eq_zero_iff _).mpr (hzero j)
  have hbound := ScalarHeatDecay.exponential_decay (fun u => energy (c u)) derivE (-K)
    hcont hEder hinequality t ht
  rw [he0,zero_mul] at hbound
  have hsingle : PositivePartSquare.square (c t i)≤energy (c t) :=
    Finset.single_le_sum (fun j _ => PositivePartSquare.square_nonneg _) (Finset.mem_univ i)
  exact (PositivePartSquare.square_eq_zero_iff _).mp
    (le_antisymm (hsingle.trans hbound) (PositivePartSquare.square_nonneg _))

theorem imbalance_le_total (a : V → V → Real) (ha : ∀ i j, 0≤a i j) (j : V) :
    imbalance a j ≤ ∑ i : V, ∑ k : V, a i k := by
  classical
  have hr : 0≤∑ k : V, a j k := Finset.sum_nonneg (fun k _ => ha j k)
  have hcol : (∑ i : V, a i j)≤∑ i : V, ∑ k : V, a i k :=
    Finset.sum_le_sum (fun i _ => Finset.single_le_sum (fun k _ => ha i k) (Finset.mem_univ j))
  unfold imbalance
  linarith

theorem order (a : V → V → Real) (ha : ∀ i j, 0≤a i j)
    (d : V → Real) (hd : ∀ i, 0≤d i)
    (u v f g : Real → V → Real)
    (hcu : ∀ i, ContinuousOn (fun t => u t i) (Ici 0))
    (hcv : ∀ i, ContinuousOn (fun t => v t i) (Ici 0))
    (hu : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun r => u r i) (leakedRate a d (u t) i+f t i) t)
    (hv : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun r => v r i) (leakedRate a d (v t) i+g t i) t)
    (hfg : ∀ t : Real, 0<t → ∀ i, f t i≤g t i)
    (hzero : ∀ i, u 0 i≤v 0 i) (t : Real) (ht : 0≤t) (i : V) : u t i≤v t i := by
  have hder : ∀ r : Real, 0<r → ∀ j,
      HasDerivAt (fun s => u s j-v s j)
        (leakedRate a d (fun k => u r k-v r k) j-(g r j-f r j)) r := by
    intro r hr j
    have he : leakedRate a d (fun k => u r k-v r k) j-(g r j-f r j) =
        (leakedRate a d (u r) j+f r j)-(leakedRate a d (v r) j+g r j) := by
      unfold leakedRate rate
      simp_rw [show ∀ k, a j k*((u r k-v r k)-(u r j-v r j)) =
        a j k*(u r k-u r j)-a j k*(v r k-v r j) from fun k => by ring]
      rw [Finset.sum_sub_distrib]
      ring
    rw [he]
    exact (hu r hr j).sub (hv r hr j)
  exact sub_nonpos.mp (nonpos a ha d hd _ (imbalance_le_total a ha)
    (fun r j => u r j-v r j) (fun r j => g r j-f r j)
    (fun j => (hcu j).sub (hcv j)) hder (fun r hr j => sub_nonneg.mpr (hfg r hr j))
    (fun j => sub_nonpos.mpr (hzero j)) t ht i)

end MathExploration.DirectedNetworkComparison


namespace MathExploration.ThreeTankCertificate
open Set
open MathExploration.DirectedNetworkComparison

/-! Ideal constant-volume completely mixed tanks. Volumes are 8,3,2;
water flows 0->1 at 6, 0->2 at 2, 1->2 at 6, inlet to0 and outlet from2 at8.
Input is inlet concentration; each state coordinate is concentration, not mass.
Theorems certify any given differentiable solution. General ODE existence and
real apparatus validation are outside this result. -/

def weights (i j : Fin 3) : Real :=
  if i=1 ∧ j=0 then 2 else if i=2 ∧ j=0 then 1 else if i=2 ∧ j=1 then 3 else 0

def leakage (i : Fin 3) : Real := if i=0 then 1 else 0

def inlet (u : Real → Real) (t : Real) (i : Fin 3) : Real := if i=0 then u t else 0

def stepEnvelope (t : Real) : Fin 3 → Real :=
  ![1-Real.exp (-t),
    1-2*Real.exp (-t)+Real.exp (-2*t),
    1-(7/3 : Real)*Real.exp (-t)+(3/2 : Real)*Real.exp (-2*t)-
      (1/6 : Real)*Real.exp (-4*t)]

theorem weights_nonneg (i j : Fin 3) : 0≤weights i j := by
  unfold weights
  split_ifs <;> norm_num

theorem leakage_nonneg (i : Fin 3) : 0≤leakage i := by
  unfold leakage
  split_ifs <;> norm_num

theorem leakedRate_components (x : Fin 3 → Real) :
    leakedRate weights leakage x 0 = -x 0 ∧
    leakedRate weights leakage x 1 = 2*(x 0-x 1) ∧
    leakedRate weights leakage x 2 = (x 0-x 2)+3*(x 1-x 2) := by
  norm_num [leakedRate, rate, weights, leakage, Fin.sum_univ_three]

theorem exp_negative_mul_deriv (k t : Real) :
    HasDerivAt (fun s : Real => Real.exp (-k*s))
      ((-k)*Real.exp (-k*t)) t := by
  simpa only [id_eq, mul_one, mul_comm] using (((hasDerivAt_id t).const_mul (-k)).exp)

theorem stepEnvelope_hasDerivAt (t : Real) (i : Fin 3) :
    HasDerivAt (fun s => stepEnvelope s i)
      (leakedRate weights leakage (stepEnvelope t) i+inlet (fun _ => 1) t i) t := by
  have h1 : HasDerivAt (fun s : Real => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using exp_negative_mul_deriv 1 t
  have h2 := exp_negative_mul_deriv 2 t
  have h4 := exp_negative_mul_deriv 4 t
  fin_cases i
  · change HasDerivAt (fun s => 1-Real.exp (-s)) _ t
    convert (hasDerivAt_const t (1 : Real)).sub h1 using 1
    norm_num [leakedRate, rate, weights, leakage, stepEnvelope, inlet, Fin.sum_univ_three]
  · change HasDerivAt (fun s => 1-2*Real.exp (-s)+Real.exp (-2*s)) _ t
    convert ((hasDerivAt_const t (1 : Real)).sub (h1.const_mul 2)).add h2 using 1
    norm_num [leakedRate, rate, weights, leakage, stepEnvelope, inlet, Fin.sum_univ_three]; ring
  · change HasDerivAt (fun s => 1-(7/3 : Real)*Real.exp (-s)+
      (3/2 : Real)*Real.exp (-2*s)-(1/6 : Real)*Real.exp (-4*s)) _ t
    convert (((hasDerivAt_const t (1 : Real)).sub (h1.const_mul (7/3))).add
      (h2.const_mul (3/2))).sub (h4.const_mul (1/6)) using 1
    norm_num [leakedRate, rate, weights, leakage, stepEnvelope, inlet, Fin.sum_univ_three]; ring

theorem stepEnvelope_zero (i : Fin 3) : stepEnvelope 0 i=0 := by
  fin_cases i <;> norm_num [stepEnvelope]

theorem stepEnvelope_continuousOn (i : Fin 3) :
    ContinuousOn (fun t => stepEnvelope t i) (Ici 0) :=
  (continuous_iff_continuousAt.mpr (fun t =>
    (stepEnvelope_hasDerivAt t i).continuousAt)).continuousOn

theorem stepEnvelope_log_two :
    stepEnvelope (Real.log 2) 2 = (19/96 : Real) := by
  have h1 : Real.exp (-(Real.log 2)) = (1/2 : Real) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real)<2)]
    norm_num
  have h2 : Real.exp (-2*Real.log 2) = (1/4 : Real) := by
    rw [show (-2 : Real)*Real.log 2 = -Real.log 2 + -Real.log 2 by ring,
      Real.exp_add,h1]
    norm_num
  have h4 : Real.exp (-4*Real.log 2) = (1/16 : Real) := by
    rw [show (-4 : Real)*Real.log 2 = -2*Real.log 2 + -2*Real.log 2 by ring,
      Real.exp_add,h2]
    norm_num
  change 1-(7/3 : Real)*Real.exp (-Real.log 2)+(3/2 : Real)*Real.exp (-2*Real.log 2)-
    (1/6 : Real)*Real.exp (-4*Real.log 2) = (19/96 : Real)
  rw [h1,h2,h4]
  norm_num

/-- Every differentiable trajectory driven by any pointwise bounded inlet,
starting at zero, is bounded by the explicit unit-step solution. -/
theorem solution_upper (x : Real → Fin 3 → Real) (u : Real → Real)
    (hc : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hx : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => x s i) (leakedRate weights leakage (x t) i+inlet u t i) t)
    (hu : ∀ t : Real, 0<t → u t≤1)
    (hz : ∀ i, x 0 i=0) (t : Real) (ht : 0≤t) (i : Fin 3) :
    x t i≤stepEnvelope t i := by
  apply order weights weights_nonneg leakage leakage_nonneg
    x stepEnvelope (inlet u) (inlet (fun _ => 1)) hc stepEnvelope_continuousOn hx
    (fun s _ j => stepEnvelope_hasDerivAt s j) _ _ t ht i
  · intro s hs j
    by_cases hj : j=0
    · simpa [inlet,hj] using hu s hs
    · simp [inlet,hj]
  · intro j
    rw [hz,stepEnvelope_zero]

theorem solution_nonneg (x : Real → Fin 3 → Real) (u : Real → Real)
    (hc : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hx : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => x s i) (leakedRate weights leakage (x t) i+inlet u t i) t)
    (hu : ∀ t : Real, 0<t → 0≤u t)
    (hz : ∀ i, x 0 i=0) (t : Real) (ht : 0≤t) (i : Fin 3) : 0≤x t i := by
  apply order weights weights_nonneg leakage leakage_nonneg
    (fun _ _ => 0) x (inlet (fun _ => 0)) (inlet u)
    (fun _ => continuousOn_const) hc _ hx _ _ t ht i
  · intro s _ j
    simpa [leakedRate, rate, inlet] using hasDerivAt_const s (0 : Real)
  · intro s hs j
    by_cases hj : j=0
    · simpa [inlet,hj] using hu s hs
    · simp [inlet,hj]
  · intro j
    rw [hz]

/-- Exact attainable worst-inlet upper bound at time log 2, not a fit to data. -/
theorem outlet_at_log_two_le (x : Real → Fin 3 → Real) (u : Real → Real)
    (hc : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hx : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => x s i) (leakedRate weights leakage (x t) i+inlet u t i) t)
    (hu : ∀ t : Real, 0<t → u t≤1) (hz : ∀ i, x 0 i=0) :
    x (Real.log 2) 2 ≤ (19/96 : Real) := by
  have h := solution_upper x u hc hx hu hz (Real.log 2)
    (Real.log_nonneg (by norm_num : (1 : Real)≤2)) 2
  simpa only [stepEnvelope_log_two] using h

/-- Non-balanced mixing can increase the unweighted squared norm even when
all physical water volumes stay constant. It does not invalidate comparison. -/
theorem unweighted_energy_can_increase :
    (∑ i : Fin 3, 2*max ((![5,4,2] : Fin 3 → Real) i) 0*
      leakedRate weights leakage (![5,4,2]) i) = 2 := by
  norm_num [leakedRate, rate, weights, leakage, Fin.sum_univ_three]

end MathExploration.ThreeTankCertificate

#print axioms MathExploration.DirectedNetworkComparison.rate
#print axioms MathExploration.DirectedNetworkComparison.imbalance
#print axioms MathExploration.DirectedNetworkComparison.energy
#print axioms MathExploration.DirectedNetworkComparison.leakedRate
#print axioms MathExploration.DirectedNetworkComparison.sum_edge_difference
#print axioms MathExploration.DirectedNetworkComparison.rate_flux_le_imbalance
#print axioms MathExploration.DirectedNetworkComparison.rate_flux_le_energy
#print axioms MathExploration.DirectedNetworkComparison.max_mul_self
#print axioms MathExploration.DirectedNetworkComparison.leaked_source_flux_le
#print axioms MathExploration.DirectedNetworkComparison.energy_nonneg
#print axioms MathExploration.DirectedNetworkComparison.nonpos
#print axioms MathExploration.DirectedNetworkComparison.imbalance_le_total
#print axioms MathExploration.DirectedNetworkComparison.order
#print axioms MathExploration.ThreeTankCertificate.weights
#print axioms MathExploration.ThreeTankCertificate.leakage
#print axioms MathExploration.ThreeTankCertificate.inlet
#print axioms MathExploration.ThreeTankCertificate.stepEnvelope
#print axioms MathExploration.ThreeTankCertificate.weights_nonneg
#print axioms MathExploration.ThreeTankCertificate.leakage_nonneg
#print axioms MathExploration.ThreeTankCertificate.leakedRate_components
#print axioms MathExploration.ThreeTankCertificate.exp_negative_mul_deriv
#print axioms MathExploration.ThreeTankCertificate.stepEnvelope_hasDerivAt
#print axioms MathExploration.ThreeTankCertificate.stepEnvelope_zero
#print axioms MathExploration.ThreeTankCertificate.stepEnvelope_continuousOn
#print axioms MathExploration.ThreeTankCertificate.stepEnvelope_log_two
#print axioms MathExploration.ThreeTankCertificate.solution_upper
#print axioms MathExploration.ThreeTankCertificate.solution_nonneg
#print axioms MathExploration.ThreeTankCertificate.outlet_at_log_two_le
#print axioms MathExploration.ThreeTankCertificate.unweighted_energy_can_increase

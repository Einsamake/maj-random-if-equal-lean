module
public import MathResearchAnalysis.GreedyClockChain
set_option autoImplicit false
/-! A closed bound for actual site arrival counts, reusing the established greedy-chain Laplace estimate along a constant site path. No Poisson-count law or compensator is assumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ClockArrivalCountTail
open MeasureTheory
variable {V : Type*} [DecidableEq V] [Countable V]

theorem constant_chain_le_arrival_ae (v : V) (k : Nat) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V,
      GreedyClockChain.chainTime (fun _ => v) (k+1) ω ≤
        (ArrivalFiltration.chronologicalArrival v k ω : WithTop Real) := by
  filter_upwards [ArrivalFiltration.chronologicalArrival_eq_raw_ae (V := V),
    ExponentialClocks.all_gaps_positive_ae (V := V)] with ω heq hpos
  have hm : StrictMono (fun j => ArrivalFiltration.chronologicalArrival v j ω) := by
    intro i j hij
    simpa only [heq v] using (ExponentialClocks.arrival_strictMono v ω (hpos v)) hij
  have hstart : 0 < ArrivalFiltration.chronologicalArrival v 0 ω := by
    rw [heq v 0]
    simpa only [ExponentialClocks.arrival,zero_add,Finset.sum_range_one] using hpos v 0
  simpa only [id_eq,Nat.add_sub_cancel_right] using
    GreedyClockChain.chainTime_le_witness (fun _ => v) id (k+1) ω (by omega) hstart
      (fun i _ => hm (Nat.lt_succ_self i))

theorem arrival_event_subset_chain_ae (v : V) (k : Nat) (t : Real) :
    {ω | ArrivalFiltration.chronologicalArrival v k ω ≤ t} ≤ᵐ[ExponentialClocks.clockMeasure V]
      {ω | GreedyClockChain.chainTime (fun _ => v) (k+1) ω ≤ (t : WithTop Real)} := by
  filter_upwards [constant_chain_le_arrival_ae v k] with ω hω
  intro ht
  exact hω.trans (WithTop.coe_le_coe.mpr ht)

theorem arrival_measureReal_le (v : V) (k : Nat) (t : Real) :
    (ExponentialClocks.clockMeasure V).real {ω | ArrivalFiltration.chronologicalArrival v k ω ≤ t} ≤
      Real.exp t * ((2 : Real)⁻¹)^(k+1) := by
  calc
    _ ≤ (ExponentialClocks.clockMeasure V).real
        {ω | GreedyClockChain.chainTime (fun _ => v) (k+1) ω ≤ (t : WithTop Real)} :=
      ENNReal.toReal_mono (by finiteness) (measure_mono_ae (arrival_event_subset_chain_ae v k t))
    _ ≤ _ := by
      simpa only [one_mul,show (1+1 : Real)=2 by norm_num] using
        (GreedyClockChain.lower_tail (fun _ => v) (k+1) t 1 (by norm_num)).2

theorem arrival_measure_le (v : V) (k : Nat) (t : Real) :
    ExponentialClocks.clockMeasure V {ω | ArrivalFiltration.chronologicalArrival v k ω ≤ t} ≤
      ENNReal.ofReal (Real.exp t) * ((2 : ENNReal)⁻¹)^(k+1) := by
  have h := ENNReal.ofReal_le_ofReal (arrival_measureReal_le v k t)
  rw [ofReal_measureReal] at h
  convert h using 1
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num
end MathResearchAnalysis.ClockArrivalCountTail

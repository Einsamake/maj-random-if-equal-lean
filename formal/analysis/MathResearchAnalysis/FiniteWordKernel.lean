module

public import MathResearchAnalysis.ClockExecutionLaw
public import MathResearchAnalysis.ZeroTemperature
public import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

/-!
# The actual finite fair-mark execution kernel

Finite independent fair mark integration is identified with the concrete
majority-word mean and with the finite zero-temperature limit. Event lists
passed to `freshRun` are newest first, hence the site word is reversed.
The fair expectation recurrence is proved from the constructed product
measure; it is not an additional hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MathResearchAnalysis.FiniteWordKernel

abbrev Event (n : ℕ) := SquareSpin.Event n
abbrev Config (n : ℕ) := SquareSpin.Config n

theorem integral_fair (g : Bool → ℝ) :
    ∫ b, g b ∂FairMarks.fair = (g true + g false) / 2 := by
  have hhalf : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [FairMarks.fair, integral_add_measure
      (Integrable.of_finite.smul_measure hhalf) (Integrable.of_finite.smul_measure hhalf),
    integral_smul_measure, integral_smul_measure]
  simp only [integral_dirac, smul_eq_mul, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat]
  ring

theorem splitVector_symm (r : ℕ) (b : Bool) (ξ : Fin r → Bool) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Bool) 0).symm (b, ξ) =
      Fin.cons b ξ := by
  change @Fin.insertNth r (fun _ : Fin (r + 1) => Bool) 0 b ξ = _
  exact Fin.insertNth_zero' b ξ

/-- The real finite-product decomposition, with the first coordinate integrated last. -/
theorem integral_vector_succ (r : ℕ) (g : (Fin (r + 1) → Bool) → ℝ) :
    ∫ ξ, g ξ ∂FairMarks.vectorMeasure (r + 1) =
      ∫ ξ, (g (Fin.cons true ξ) + g (Fin.cons false ξ)) / 2
        ∂FairMarks.vectorMeasure r := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Bool) 0
  have hp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (r + 1) => FairMarks.fair) (0 : Fin (r + 1))
  have hmap : ∫ ξ, g ξ ∂Measure.pi (fun _ : Fin (r + 1) => FairMarks.fair) =
      ∫ z : Bool × (Fin r → Bool), g (e.symm z)
        ∂FairMarks.fair.prod (Measure.pi (fun _ : Fin r => FairMarks.fair)) := by
    simpa only [e, MeasurableEquiv.symm_apply_apply] using
      hp.integral_comp' (fun z => g (e.symm z))
  simp only [FairMarks.vectorMeasure, FairMarks.markMeasure, Measure.infinitePi_eq_pi]
  rw [hmap, integral_prod_symm _ Integrable.of_finite]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    change (∫ b, g (e.symm (b, ξ)) ∂FairMarks.fair) = _
    rw [integral_fair]
    simp only [e, splitVector_symm]

theorem freshMarks_cons_head {n : ℕ} (e : Event n) (rest : List (Event n))
    (ξ : Fin (e :: rest).length → Bool) :
    ClockExecutionLaw.freshMarks (e :: rest) ξ e = ξ 0 := by
  simp only [ClockExecutionLaw.freshMarks, List.mem_cons_self, dite_true,
    List.idxOf_cons_self]
  rfl

theorem freshMarks_cons_tail {n : ℕ} (e : Event n) (rest : List (Event n))
    (unique : (e :: rest).Nodup) (ξ : Fin (e :: rest).length → Bool)
    (a : Event n) (ha : a ∈ rest) :
    ClockExecutionLaw.freshMarks (e :: rest) ξ a =
      ClockExecutionLaw.freshMarks rest (fun i => ξ i.succ) a := by
  have hne : e ≠ a := by
    intro heq
    exact (List.nodup_cons.mp unique).1 (heq ▸ ha)
  simp only [ClockExecutionLaw.freshMarks,
    dite_eq_left (List.mem_cons_of_mem e ha), dite_eq_left ha, List.idxOf_cons_ne rest hne]
  rfl

/-- Fresh-run recursion derived from identity marks and the actual execution function. -/
theorem freshRun_cons {n : ℕ} (e : Event n) (rest : List (Event n))
    (unique : (e :: rest).Nodup) (ξ : Fin (e :: rest).length → Bool) (f : Config n) :
    ClockExecutionLaw.freshRun (e :: rest) ξ f =
      SquareSpin.cellUpdate (ClockExecutionLaw.freshRun rest (fun i => ξ i.succ) f)
        e.1 (ξ 0) := by
  have hmarks := MarkedEventTrace.execute_eq_of_marks_agree
    (ClockExecutionLaw.freshMarks (e :: rest) ξ)
    (ClockExecutionLaw.freshMarks rest (fun i => ξ i.succ)) rest.reverse
    (fun a ha => freshMarks_cons_tail e rest unique ξ a (List.mem_reverse.mp ha)) f
  change EventTrace.execute
      (SquareSpin.updateEvent (ClockExecutionLaw.freshMarks (e :: rest) ξ))
      (e :: rest).reverse f = _
  rw [List.reverse_cons, EventTrace.execute_append]
  change SquareSpin.cellUpdate
    (MarkedEventTrace.execute (ClockExecutionLaw.freshMarks (e :: rest) ξ) rest.reverse f)
      e.1 (ClockExecutionLaw.freshMarks (e :: rest) ξ e) = _
  rw [hmarks, freshMarks_cons_head]
  rfl

theorem coldWord_append {n : ℕ} (first second : List (SquareTasks.Vertex n))
    (φ : Config n → ℝ) (f : Config n) :
    ZeroTemperature.coldWord (first ++ second) φ f =
      ZeroTemperature.coldWord first (ZeroTemperature.coldWord second φ) f := by
  induction first generalizing f with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.cons_append, ZeroTemperature.coldWord, ZeroTemperature.coldStep, ih]

/-- Integration of genuine independent fair event marks is the cold finite-word kernel. -/
theorem integral_freshRun_eq_coldWord {n : ℕ} (events : List (Event n))
    (unique : events.Nodup) (φ : Config n → ℝ) (f : Config n) :
    (∫ ξ, φ (ClockExecutionLaw.freshRun events ξ f) ∂FairMarks.vectorMeasure events.length) =
      ZeroTemperature.coldWord (events.reverse.map Prod.fst) φ f := by
  revert unique φ f
  induction events with
  | nil =>
    intro _ φ f
    simp only [ClockExecutionLaw.freshRun, List.reverse_nil, MarkedEventTrace.execute,
      EventTrace.execute_nil, List.length_nil, integral_const, probReal_univ,
      one_smul, List.map_nil, ZeroTemperature.coldWord]
  | cons e rest ih =>
    intro unique φ f
    have hrest := (List.nodup_cons.mp unique).2
    change (∫ ξ : Fin (rest.length + 1) → Bool,
      φ (ClockExecutionLaw.freshRun (e :: rest) ξ f)
        ∂FairMarks.vectorMeasure (rest.length + 1)) = _
    rw [integral_vector_succ rest.length]
    have hpoint (ξ : Fin rest.length → Bool) :
        (φ (ClockExecutionLaw.freshRun (e :: rest) (Fin.cons true ξ) f) +
          φ (ClockExecutionLaw.freshRun (e :: rest) (Fin.cons false ξ) f)) / 2 =
        ZeroTemperature.coldStep e.1 φ (ClockExecutionLaw.freshRun rest ξ f) := by
      rw [freshRun_cons e rest unique, freshRun_cons e rest unique]
      simp only [Fin.cons_zero, Fin.cons_succ, ZeroTemperature.coldStep_eq_actual_majority]
    simp_rw [hpoint]
    rw [ih hrest]
    simp only [List.reverse_cons, List.map_append, List.map_singleton, coldWord_append,
      ZeroTemperature.coldWord]

theorem integral_freshRun_eq_actualMajorityWordMean {n : ℕ} (events : List (Event n))
    (unique : events.Nodup) (φ : Config n → ℝ) (f : Config n) :
    (∫ ξ, φ (ClockExecutionLaw.freshRun events ξ f) ∂FairMarks.vectorMeasure events.length) =
      ZeroTemperature.actualMajorityWordMean (events.reverse.map Prod.fst) φ f := by
  rw [integral_freshRun_eq_coldWord events unique,
    ZeroTemperature.coldWord_eq_actualMajorityWordMean]

/-- Chronological event-word formulation; `freshRun` receives its newest-first reversal. -/
theorem chronological_fair_execution_mean {n : ℕ} (word : List (Event n))
    (unique : word.Nodup) (φ : Config n → ℝ) (f : Config n) :
    (∫ ξ, φ (ClockExecutionLaw.freshRun word.reverse ξ f)
      ∂FairMarks.vectorMeasure word.reverse.length) =
      ZeroTemperature.actualMajorityWordMean (word.map Prod.fst) φ f := by
  simpa only [List.reverse_reverse] using integral_freshRun_eq_actualMajorityWordMean
    word.reverse (List.nodup_reverse.mpr unique) φ f

/-- The same identity expressed directly for the actual finite execution measure. -/
theorem freshExecutionLaw_integral {n : ℕ} (events : List (Event n))
    (unique : events.Nodup) (φ : Config n → ℝ) (f : Config n) :
    (∫ g, φ g ∂ClockExecutionLaw.freshExecutionLaw events f) =
      ZeroTemperature.actualMajorityWordMean (events.reverse.map Prod.fst) φ f := by
  rw [ClockExecutionLaw.freshExecutionLaw,
    integral_map (ClockExecutionLaw.freshRun_measurable events f).aemeasurable
      (measurable_of_countable φ).aestronglyMeasurable]
  exact integral_freshRun_eq_actualMajorityWordMean events unique φ f

theorem finite_word_zero_temperature_actual_integral {n : ℕ}
    (events : List (Event n)) (unique : events.Nodup) (φ : Config n → ℝ) (f : Config n) :
    Tendsto (fun β => ZeroTemperature.warmWord β (events.reverse.map Prod.fst) φ f) atTop
      (𝓝 (∫ ξ, φ (ClockExecutionLaw.freshRun events ξ f)
        ∂FairMarks.vectorMeasure events.length)) := by
  rw [integral_freshRun_eq_coldWord events unique]
  exact ZeroTemperature.finite_word_zero_temperature _ φ f

end MathResearchAnalysis.FiniteWordKernel

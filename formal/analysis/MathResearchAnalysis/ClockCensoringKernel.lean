module

public import MathResearchAnalysis.ClockEndpointMean
public import MathResearchAnalysis.ClockSelectedWord
public import MathResearchAnalysis.SquarePWCensoring

set_option autoImplicit false

/-!
# Censoring the actual clock word down to completed checkerboard layers

The deleted word is the genuine chronological selected-clock subword. Its
identity-marked execution equals the layer execution by the established clock
readiness theorem. Integrating those actual independent identity marks gives
equality of the corresponding cold kernels. The layer site's word is
deterministic, even though its site/ring identities depend on the clocks.

The final comparison starts from the top configuration and uses only clock
regularity, actual layer completion by the time bound, and monotonicity of the
test function. A sublist, conflict order, censoring bound, or mark law is not
supplied as a theorem hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.ClockCensoringKernel

abbrev Site (n : ℕ) := SquareTasks.Vertex n
abbrev Event (n : ℕ) := SquareSpin.Event n
abbrev Config (n : ℕ) := SquareSpin.Config n
abbrev Sample (n : ℕ) := ClockSelectedWord.Sample n

/-- The fixed scan of the sites of the positive task layers `1, ..., k + 1`. -/
def layerSites (n : ℕ) (c : Bool) (k : ℕ) : List (Site n) :=
  (ClockSelectedWord.layerTasks n c k).map Prod.snd

/-- Selecting an arrival index never changes the task's site. -/
theorem layerWord_sites (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n) :
    (ClockSelectedWord.layerWord n c k ω).map Prod.fst = layerSites n c k := by
  simp only [ClockSelectedWord.layerWord, List.map_map, layerSites,
    Function.comp_def, ClockEventOrder.eventId]

/-- Pointwise marked execution equality gives equality of actual cold kernels.
Only distinctness of the event identities is needed for the fair-mark bridge. -/
theorem coldWord_eq_of_marked_execute_eq {n : ℕ}
    (first second : List (Event n)) (first_unique : first.Nodup)
    (second_unique : second.Nodup)
    (execute_eq : ∀ (η : Event n → Bool) (initial : Config n),
      MarkedEventTrace.execute η first initial =
        MarkedEventTrace.execute η second initial)
    (φ : Config n → ℝ) (initial : Config n) :
    ZeroTemperature.coldWord (first.map Prod.fst) φ initial =
      ZeroTemperature.coldWord (second.map Prod.fst) φ initial := by
  rw [← ClockEndpointMean.integral_marked_execute_eq_coldWord first first_unique,
    ← ClockEndpointMean.integral_marked_execute_eq_coldWord second second_unique]
  apply integral_congr_ae
  exact ae_of_all _ fun η => congrArg φ (execute_eq η initial)

/-- Every completed genuine selected-clock subword has the fixed layer kernel. -/
theorem coldWord_selectedChrono_eq_layerSites (n : ℕ) (c : Bool) (k : ℕ)
    (ω : Sample n) (hω : ClockSelectedWord.Regular n ω) (t : ℝ)
    (hmax : ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ))
    (φ : Config n → ℝ) (initial : Config n) :
    ZeroTemperature.coldWord
        ((ClockSelectedWord.selectedChrono n c k ω t).map Prod.fst) φ initial =
      ZeroTemperature.coldWord (layerSites n c k) φ initial := by
  rw [← layerWord_sites n c k ω]
  apply coldWord_eq_of_marked_execute_eq _ _
    (ClockSelectedWord.selectedChrono_nodup n c k ω t)
    (ClockSelectedWord.layerWord_nodup n c k ω hω.1)
  exact fun η initial =>
    ClockSelectedWord.execute_selectedChrono_eq_layerWord n c k ω hω t hmax η initial

/-- Actual clock-wise censoring from the top configuration to all completed
selected task layers, with no sublist, ordering, or probability-law inputs. -/
theorem coldWord_clock_le_layerSites (n : ℕ) (c : Bool) (k : ℕ)
    (ω : Sample n) (hω : ClockSelectedWord.Regular n ω) (t : ℝ)
    (hmax : ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ))
    (φ : Config n → ℝ) (hφ : Monotone φ) :
    ZeroTemperature.coldWord ((ClockEventWord.word ω t).reverse.map Prod.fst)
        φ (SquarePWMeasure.topConfig n) ≤
      ZeroTemperature.coldWord (layerSites n c k) φ (SquarePWMeasure.topConfig n) := by
  have h := SquarePWCensoring.actualMajorityWordMean_censoring
    ((ClockSelectedWord.selectedChrono_sublist n c k ω t).map Prod.fst) φ hφ
  rw [← ZeroTemperature.coldWord_eq_actualMajorityWordMean,
    ← ZeroTemperature.coldWord_eq_actualMajorityWordMean,
    coldWord_selectedChrono_eq_layerSites n c k ω hω t hmax] at h
  exact h

/-- A common probability-one event supports every layer, time bound, and
increasing test function in the actual clock-wise deletion comparison. -/
theorem coldWord_clock_le_layerSites_ae (n : ℕ) (c : Bool) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (Site n),
      ∀ (k : ℕ) (t : ℝ),
        ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ) →
        ∀ (φ : Config n → ℝ), Monotone φ →
          ZeroTemperature.coldWord ((ClockEventWord.word ω t).reverse.map Prod.fst)
              φ (SquarePWMeasure.topConfig n) ≤
            ZeroTemperature.coldWord (layerSites n c k) φ (SquarePWMeasure.topConfig n) := by
  filter_upwards [ClockSelectedWord.regular_ae n] with ω hω
  exact fun k t hmax φ hφ => coldWord_clock_le_layerSites n c k ω hω t hmax φ hφ

end MathResearchAnalysis.ClockCensoringKernel

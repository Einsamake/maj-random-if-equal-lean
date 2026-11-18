module
public import MathResearchAnalysis.ClockRestrictedExecution
public import MathResearchAnalysis.ClockEndpointSurvival
public import MathResearchAnalysis.SquareRecoveryTime
public import MathResearchAnalysis.OriginalRecoveryProfile
public import MathResearchAnalysis.ExtendedTailLower
public import MathResearchAnalysis.SyncLowerScale
public import Mathlib.Tactic

set_option autoImplicit false

/-! The C1 reduction from odd-square clock tails to synchronous tails.
The two clock estimates taken from CMST appear as a theorem argument. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ClockLiteratureTransfer
open MeasureTheory Set
open SquareTasks (Vertex)
open SquareInclusion (site Rel)
open ClockSampleRestriction (projectSample projectMarks eventι)
open ClockRecoveryComparison (clockProbability)

private theorem extend_le {n m : Nat} (hnm : n ≤ m)
    {f : SquareSpin.Config n} {g : SquareSpin.Config m} (hfg : Rel hnm f g) :
    SquareGridEmbedding.extend n f ≤ SquareGridEmbedding.extend m g := by
  intro z
  by_cases hz : InfiniteGridModel.Inside (n + 2) z
  · have hzM : InfiniteGridModel.Inside (m + 2) z := by
      unfold InfiniteGridModel.Inside at hz ⊢
      omega
    rw [SquareGridEmbedding.extend, dite_eq_left hz,
      SquareGridEmbedding.extend, dite_eq_left hzM]
    exact hfg (SquareGridEmbedding.vertexOfInside n z hz)
  · rw [SquareGridEmbedding.extend_outside n f z hz]
    exact Bool.false_le _

private theorem cellUpdate_rel {n m : Nat} (hnm : n ≤ m)
    {f : SquareSpin.Config n} {g : SquareSpin.Config m} (hfg : Rel hnm f g)
    (v : Vertex n) (b : Bool) :
    Rel hnm (SquareSpin.cellUpdate f v b) (SquareSpin.cellUpdate g (site hnm v) b) := by
  intro w
  by_cases hw : w = v
  · subst w
    simp only [SquareSpin.cellUpdate_same]
    have hsmall := SquareGridEmbedding.update_embed n (fun _ _ => b) 0 f v
    have hlarge := SquareGridEmbedding.update_embed m (fun _ _ => b) 0 g (site hnm v)
    simp only [SquareGridEmbedding.restrictMarks] at hsmall hlarge
    rw [← hsmall, ← hlarge, SquareInclusion.embed_site]
    unfold InfiniteGridModel.update
    apply InfiniteGridModel.majority4_monotone
    all_goals exact extend_le hnm hfg _
  · have hw' : site hnm w ≠ site hnm v := fun h => hw (SquareInclusion.site_injective hnm h)
    simpa only [SquareSpin.cellUpdate_other _ _ _ _ hw,
      SquareSpin.cellUpdate_other _ _ _ _ hw'] using hfg w

private theorem endpoint_rel {n m : Nat} (hnm : n ≤ m)
    (f : SquareSpin.Config n) (g : SquareSpin.Config m) (hfg : Rel hnm f g)
    (z : ClockWordMarks.Sample m) (t : ℝ) (hgood : ClockEventWord.Good z.1 t) :
    Rel hnm (ClockExecutionLaw.endpoint n t f (projectSample (site hnm) z))
      (ClockExecutionLaw.endpoint m t g z) := by
  apply ClockRestrictedExecution.execute_related_of_filter_map (eventι (site hnm))
    (ClockWordRestriction.retained (site hnm))
    (SquareSpin.updateEvent (projectMarks (site hnm) z.2)) (SquareSpin.updateEvent z.2)
  · intro e a b hab
    exact cellUpdate_rel hnm hab e.1 (z.2 (eventι (site hnm) e))
  · intro e he a b hab v
    simpa only [SquareSpin.updateEvent, SquareSpin.cellUpdate_other _ _ _ _
      (ClockRestrictedExecution.outside_site_of_not_retained (site hnm) e he v)] using hab v
  · exact ClockWordRestriction.reverse_word_map_eq_filter
      (site hnm) (SquareInclusion.site_injective hnm) z.1 t hgood
  · exact hfg

/-- Zero-boundary clock survival is monotone in the square side. -/
theorem clockProbability_mono (t : ℝ) : Monotone (fun n => clockProbability n t) := by
  intro n m hnm
  let f := SquarePWMeasure.topConfig n
  let g := SquarePWMeasure.topConfig m
  let A : Set (ClockWordMarks.Sample n) :=
    {z | ClockExecutionLaw.endpoint n t f z ≠ fun _ => false}
  have hA : MeasurableSet A :=
    ((ClockExecutionLaw.endpoint_measurable n t f) (measurableSet_singleton _)).compl
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  change ClockWordMarks.measure n A ≤ _
  rw [← ClockSampleRestriction.projectSample_map (site hnm) (SquareInclusion.site_injective hnm),
    Measure.map_apply (ClockSampleRestriction.projectSample_measurable (site hnm)) hA]
  apply measure_mono_ae
  filter_upwards [ClockEndpointSurvival.sample_good_ae m] with z hz
  intro hne hzero
  apply hne
  funext v
  have hle := endpoint_rel hnm f g (SquareInclusion.initial_rel_top hnm f) z t (hz t) v
  change ClockExecutionLaw.endpoint m t g z = (fun _ => false) at hzero
  rw [hzero] at hle
  exact le_antisymm hle (Bool.false_le _)

/-- Radii bracketing the actual side n+2 by odd sides. -/
def lowerRadius (n : Nat) : Nat := (n + 1) / 2

def upperRadius (n : Nat) : Nat := (n + 2) / 2

theorem odd_parameters_bracket (n : Nat) (hn : 2 ≤ n) :
    1 ≤ lowerRadius n ∧
    ClippedSquareCoordinates.parameter (lowerRadius n) ≤ n ∧
    n ≤ ClippedSquareCoordinates.parameter (upperRadius n) := by
  unfold lowerRadius upperRadius ClippedSquareCoordinates.parameter
  omega

def syncTail (n k : Nat) : ℝ :=
  (SquareRandomDynamics.measure n).real
    {η | (k : ℕ∞) < SquareRecoveryTime.synchronous n (SquarePWMeasure.topConfig n) η}

def error (n k : Nat) : ℝ :=
  (6 / 5 : ℝ) * (n + 2 : ℝ)^2 * ((2 : ℝ)⁻¹)^(k + 1)

/-- The tail inequalities on odd squares furnished by CMST Theorem 2 after
identifying the clock law. Here L is the radius and the side is 2*L+1. -/
def OddClockWindow (c γ : ℝ) : Prop :=
  ∀ L : Nat, 1 ≤ L →
    (∀ t : ℝ, 0 ≤ t → t < c * (L : ℝ)^2 →
      1 - Real.exp (-γ * L) ≤ clockProbability (ClippedSquareCoordinates.parameter L) t) ∧
    (∀ t : ℝ, (L : ℝ)^2 / c ≤ t →
      clockProbability (ClippedSquareCoordinates.parameter L) t ≤ Real.exp (-γ * L))

/-- Both scheduling inequalities for every side n+2, with their separate errors. -/
theorem transfer (n kLower kUpper : Nat) (hn : 2 ≤ n) (c γ : ℝ) (hwindow : OddClockWindow c γ)
    (hearly : SchedulingFailure.time kLower < c * (lowerRadius n : ℝ)^2)
    (hlate : (upperRadius n : ℝ)^2 / c ≤ SchedulingFailure.time kUpper) :
    1 - Real.exp (-γ * lowerRadius n) - error n kLower ≤ syncTail n kLower ∧
    syncTail n (2 * SchedulingFailure.rankThreshold kUpper + 1) ≤
      2 * Real.exp (-γ * upperRadius n) + 2 * error n kUpper := by
  obtain ⟨hlo, hnlo, hnhi⟩ := odd_parameters_bracket n hn
  have hhi : 1 ≤ upperRadius n := by unfold upperRadius; omega
  have h1 := (hwindow (lowerRadius n) hlo).1 (SchedulingFailure.time kLower)
    (SchedulingFailure.time_positive kLower).le hearly
  have h2 := (hwindow (upperRadius n) hhi).2 (SchedulingFailure.time kUpper) hlate
  have h3 := clockProbability_mono (SchedulingFailure.time kLower) hnlo
  have h4 := clockProbability_mono (SchedulingFailure.time kUpper) hnhi
  have hbLower := (SquareRecoveryTime.two_way_clock_tail n false kLower).1
  have hbUpper := (SquareRecoveryTime.two_way_clock_tail n false kUpper).2
  constructor
  · change _ ≤ syncTail n kLower + error n kLower at hbLower
    linarith
  · change syncTail n (2 * SchedulingFailure.rankThreshold kUpper + 1) ≤ _ + 2 * error n kUpper at hbUpper
    linarith

/-- The paper's floor and ceiling choices, once both unrounded indices exceed
the side. The strict lower time avoids the closed CMST lower endpoint. -/
theorem exists_comparison_rounds (n : Nat) (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c)
    (hLower : (n + 2 : ℝ) ≤ c * (lowerRadius n : ℝ)^2 / (2 * (8 * Real.log 2)))
    (hUpper : (n + 2 : ℝ) ≤ (upperRadius n : ℝ)^2 / c / (8 * Real.log 2)) :
    ∃ kLower kUpper : Nat, n + 2 ≤ kLower + 1 ∧ n + 2 ≤ kUpper + 1 ∧
      SchedulingFailure.time kLower < c * (lowerRadius n : ℝ)^2 ∧
      (upperRadius n : ℝ)^2 / c ≤ SchedulingFailure.time kUpper := by
  let a := 8 * Real.log 2
  let u := c * (lowerRadius n : ℝ)^2
  let v := (upperRadius n : ℝ)^2 / c
  have ha : 0 < a := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hRadius := (odd_parameters_bracket n hn).1
  have hu : 0 < u := mul_pos hc (sq_pos_of_pos (by exact_mod_cast (show 0 < lowerRadius n by omega)))
  have hx : (n + 2 : ℝ) ≤ u / (2 * a) := hLower
  have hy : (n + 2 : ℝ) ≤ v / a := hUpper
  let kLower := ⌊u / (2 * a)⌋₊ - 1
  let kUpper := ⌈v / a⌉₊ - 1
  have hFloor : n + 2 ≤ ⌊u / (2 * a)⌋₊ := Nat.le_floor (by push_cast; exact hx)
  have hCeil : n + 2 ≤ ⌈v / a⌉₊ := by
    exact_mod_cast (hy.trans (Nat.le_ceil (v / a)))
  have hLowerEq : kLower + 1 = ⌊u / (2 * a)⌋₊ := by
    unfold kLower
    omega
  have hUpperEq : kUpper + 1 = ⌈v / a⌉₊ := by
    unfold kUpper
    omega
  refine ⟨kLower, kUpper, by rwa [hLowerEq], by rwa [hUpperEq], ?_, ?_⟩
  · change a * ((kLower + 1 : Nat) : ℝ) < u
    rw [hLowerEq]
    have hle := mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity : 0 ≤ u / (2 * a))) ha.le
    have hhalf : a * (u / (2 * a)) = u / 2 := by field_simp
    rw [hhalf] at hle
    exact hle.trans_lt (by linarith)
  · change v ≤ a * ((kUpper + 1 : Nat) : ℝ)
    rw [hUpperEq]
    have hle := mul_le_mul_of_nonneg_left (Nat.le_ceil (v / a)) ha.le
    have hv : a * (v / a) = v := by field_simp
    rwa [hv] at hle


private theorem error_le_eighth (n k : Nat) (hn : 16 ≤ n + 2) (hk : n + 2 ≤ k + 1) :
    error n k ≤ 1 / 8 := by
  have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hk
  have hsize := SyncLowerScale.square_exponential_bound (n + 2) hn
  push_cast at hsize
  unfold error
  apply (mul_le_mul_of_nonneg_left hp (by positivity)).trans
  rw [inv_pow, ← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^(n+2))).mpr
  linarith [sq_nonneg ((n : ℝ) + 2)]

private theorem tau_le_two_blocks (N b : Nat) (hN : 2 ≤ N) (hb : 0 < b)
    (hhalf : syncTail (N - 2) b ≤ 1 / 2) :
    OriginalRecoveryProfile.tau N ≤ 2 * (b : ENNReal) := by
  rw [OriginalRecoveryProfile.tau_eq_normalizedTau N hN]
  apply iSup_le
  intro g
  apply iSup_le
  intro _
  apply ExtendedBlockTail.lintegral_le_two_blocks (SquareRandomDynamics.measure (N - 2))
    (SquareRecoveryTime.synchronous (N - 2) g) (SquareRecoveryTime.synchronous_measurable _ _) b hb
  intro j
  have hp := SquareRandomRestart.recovery_block_le_pow (N - 2) g b j
  have hr := hp.trans (pow_le_pow_left₀ measureReal_nonneg hhalf j)
  have h := ENNReal.ofReal_le_ofReal hr
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
    show ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num] using h

private theorem tau_ge_half_rounds (N k : Nat) (hN : 2 ≤ N)
    (hhalf : (1 / 2 : ℝ) ≤ syncTail (N - 2) k) :
    ENNReal.ofReal ((k : ℝ) / 2) ≤ OriginalRecoveryProfile.tau N := by
  let n := N - 2
  let g := SquarePWMeasure.topConfig n
  let μ := SquareRandomDynamics.measure n
  let T := SquareRecoveryTime.synchronous n g
  have hp : ENNReal.ofReal (1 / 2) ≤ μ {z | (k : ℕ∞) < T z} :=
    (ENNReal.ofReal_le_ofReal hhalf).trans
      (le_of_eq (ofReal_measureReal (measure_ne_top μ _)))
  have hdist := OriginalRecoveryProfile.distance_extend_top n
  have hs : n + 2 = N := by dsimp [n]; omega
  rw [hs] at hdist
  calc
    _ = (k : ENNReal) * ENNReal.ofReal (1 / 2) := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
      norm_num
    _ ≤ (k : ENNReal) * μ {z | (k : ℕ∞) < T z} := mul_le_mul_right hp _
    _ ≤ OriginalRecoveryProfile.finiteExpected n g :=
      ExtendedTailLower.tail_mul_le_expectation μ T (SquareRecoveryTime.synchronous_measurable n g) k
    _ = OriginalRecoveryProfile.expectedRecovery (SquareGridEmbedding.extend n g) :=
      (OriginalRecoveryProfile.expectedRecovery_finite_square n g).symm
    _ ≤ _ := OriginalRecoveryProfile.expectedRecovery_le_tau N _ hdist

private theorem radius_bounds (n : Nat) (hn : 2 ≤ n) :
    (n + 2 : ℝ) / 4 ≤ lowerRadius n ∧
      (lowerRadius n : ℝ) ≤ upperRadius n ∧ (upperRadius n : ℝ) ≤ (n + 2 : ℝ) / 2 := by
  have h₁ : n + 2 ≤ 4 * lowerRadius n := by unfold lowerRadius; omega
  have h₂ : lowerRadius n ≤ upperRadius n := by unfold lowerRadius upperRadius; omega
  have h₃ : 2 * upperRadius n ≤ n + 2 := by unfold upperRadius; omega
  have h₁r : (n : ℝ) + 2 ≤ 4 * (lowerRadius n : ℝ) := by exact_mod_cast h₁
  have h₃r : 2 * (upperRadius n : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast h₃
  exact ⟨by linarith, by exact_mod_cast h₂, by linarith⟩

/-- CMST's odd-square window implies the original exact-size quadratic
expected recovery profile, with both directions valid in extended expectation. -/
theorem tau_theta_of_odd_clock_window (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ)
    (hwindow : OddClockWindow c γ) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N →
      ENNReal.ofReal (A * (N : ℝ)^2) ≤ OriginalRecoveryProfile.tau N ∧
      OriginalRecoveryProfile.tau N ≤ ENNReal.ofReal (B * (N : ℝ)^2) := by
  let a := 8 * Real.log 2
  have ha : 0 < a := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  obtain ⟨N₀, h₀⟩ := exists_nat_ge (max (16 : ℝ) (max (64 * a / c)
    (max (16 * c * a) (4 * Real.log 8 / γ))))
  rw [max_le_iff, max_le_iff, max_le_iff] at h₀
  refine ⟨c / (128 * a), 128 / (c * a) + 514, by positivity, by positivity, N₀, ?_⟩
  intro N hN
  have hNr : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h16 : 16 ≤ N := by exact_mod_cast (h₀.1.trans hNr)
  let n := N - 2
  have hs : n + 2 = N := by dsimp [n]; omega
  have hsr : (n : ℝ) + 2 = (N : ℝ) := by exact_mod_cast hs
  have hn : 2 ≤ n := by omega
  obtain ⟨hlo, hr, hhi⟩ := radius_bounds n hn
  rw [hsr] at hlo hhi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hloSq : ((N : ℝ)/4)^2 ≤ (lowerRadius n : ℝ)^2 := by
    exact pow_le_pow_left₀ (by positivity) hlo _
  have hupSq : ((N : ℝ)/4)^2 ≤ (upperRadius n : ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) (hlo.trans hr) _
  have hhiSq : (upperRadius n : ℝ)^2 ≤ ((N : ℝ)/2)^2 :=
    pow_le_pow_left₀ (by positivity) hhi _
  have hcN := (div_le_iff₀ hc).mp (h₀.2.1.trans hNr)
  have hcaN := h₀.2.2.1.trans hNr
  have hγN := (div_le_iff₀ hγ).mp (h₀.2.2.2.trans hNr)
  let x := c * (lowerRadius n : ℝ)^2 / (2 * a)
  let y := (upperRadius n : ℝ)^2 / c / a
  have hx : 2 * (N : ℝ) ≤ x := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
    have hp := mul_le_mul_of_nonneg_right hcN hNpos.le
    have hq := mul_le_mul_of_nonneg_left hloSq hc.le
    nlinarith only [hp, hq]
  have hy : (N : ℝ) ≤ y := by
    apply (le_div_iff₀ ha).mpr
    apply (le_div_iff₀ hc).mpr
    have hp := mul_le_mul_of_nonneg_right hcaN hNpos.le
    nlinarith only [hp, hupSq]
  let k := ⌊x⌋₊ - 1
  let l := ⌈y⌉₊ - 1
  let b := 2 * SchedulingFailure.rankThreshold l + 1
  have hfloor : N ≤ ⌊x⌋₊ := Nat.le_floor (by linarith)
  have hceil : N ≤ ⌈y⌉₊ := by exact_mod_cast hy.trans (Nat.le_ceil y)
  have hk : k + 1 = ⌊x⌋₊ := by dsimp [k]; omega
  have hl : l + 1 = ⌈y⌉₊ := by dsimp [l]; omega
  have hxpos : 0 < x := by linarith
  have hkTime : SchedulingFailure.time k < c * (lowerRadius n : ℝ)^2 := by
    change a * ((k + 1 : Nat) : ℝ) < _
    rw [hk]
    have hm := mul_le_mul_of_nonneg_left (Nat.floor_le hxpos.le) ha.le
    have he : a * x = c * (lowerRadius n : ℝ)^2 / 2 := by dsimp [x]; field_simp
    rw [he] at hm
    exact hm.trans_lt (by nlinarith [mul_pos hc (sq_pos_of_pos (show (0 : ℝ) < lowerRadius n by linarith))])
  have hlTime : (upperRadius n : ℝ)^2 / c ≤ SchedulingFailure.time l := by
    change _ ≤ a * ((l + 1 : Nat) : ℝ)
    rw [hl]
    have hm := mul_le_mul_of_nonneg_left (Nat.le_ceil y) ha.le
    have he : a * y = (upperRadius n : ℝ)^2 / c := by dsimp [y]; field_simp
    rwa [he] at hm
  have hexp : Real.exp (-γ * lowerRadius n) ≤ 1 / 8 := by
    have hh := mul_le_mul_of_nonneg_left hlo hγ.le
    have he : -γ * (lowerRadius n : ℝ) ≤ -Real.log 8 := by nlinarith only [hh, hγN]
    exact (Real.exp_le_exp.mpr he).trans_eq (by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 8)]; norm_num)
  have hexp' : Real.exp (-γ * upperRadius n) ≤ 1 / 8 :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hr (by linarith))).trans hexp
  have heK := error_le_eighth n k (by omega) (by omega)
  have heL := error_le_eighth n l (by omega) (by omega)
  obtain ⟨pK, pL⟩ := transfer n k l hn c γ hwindow hkTime hlTime
  have hlow : (1 / 2 : ℝ) ≤ syncTail n k := by linarith
  have hupp : syncTail n b ≤ 1 / 2 := by dsimp [b]; linarith
  have hkLower : c / (128 * a) * (N : ℝ)^2 ≤ (k : ℝ) / 2 := by
    have hcast : ((k : ℝ) + 1) = (⌊x⌋₊ : ℝ) := by exact_mod_cast hk
    have hfl := Nat.lt_floor_add_one x
    have hbig : 4 ≤ x := by
      have hn16 : (16 : ℝ) ≤ N := by exact_mod_cast h16
      linarith
    have hkx : x / 2 ≤ (k : ℝ) := by linarith
    have hxEq : (2 * a) * x = c * (lowerRadius n : ℝ)^2 := by dsimp [x]; field_simp
    have hm := mul_le_mul_of_nonneg_left hloSq hc.le
    have hkm := mul_le_mul_of_nonneg_left hkx (show 0 ≤ 2 * a by positivity)
    have hgoal : c * (N : ℝ)^2 ≤ ((k : ℝ) / 2) * (128 * a) := by
      nlinarith only [hkm, hxEq, hm]
    simpa only [div_mul_eq_mul_div] using
      (div_le_iff₀ (show 0 < 128 * a by positivity)).mpr hgoal
  have hbUpper : 2 * (b : ℝ) ≤ (128 / (c * a) + 514) * (N : ℝ)^2 := by
    have hceil' := Nat.ceil_lt_add_one (show 0 ≤ y by positivity)
    have hcst : ((l : ℝ) + 1) = (⌈y⌉₊ : ℝ) := by exact_mod_cast hl
    have hbEq : (b : ℝ) = 256 * ((l : ℝ) + 1) + 1 := by
      dsimp [b, SchedulingFailure.rankThreshold]
      push_cast
      ring
    have hyBound : y ≤ (N : ℝ)^2 / (4 * (c * a)) := by
      dsimp [y]
      rw [div_div]
      have h : (N : ℝ)^2 / (4 * (c * a)) = ((N : ℝ)^2 / 4) / (c * a) := by ring
      rw [h]
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < c * a)).mpr
      nlinarith only [hhiSq]
    have hN1 : (1 : ℝ) ≤ (N : ℝ)^2 := by
      have hn16 : (16 : ℝ) ≤ N := by exact_mod_cast h16
      nlinarith only [hn16, sq_nonneg ((N : ℝ) - 1)]
    have he : (128 / (c * a)) * (N : ℝ)^2 = 512 * ((N : ℝ)^2 / (4 * (c * a))) := by ring
    nlinarith only [hbEq, hceil', hcst, hyBound, hN1, he]
  constructor
  · exact (ENNReal.ofReal_le_ofReal hkLower).trans (tau_ge_half_rounds N k (by omega) hlow)
  · have h := tau_le_two_blocks N b (by omega) (by dsimp [b]; omega) hupp
    apply h.trans
    rw [show (2 * (b : ENNReal)) = ENNReal.ofReal (2 * (b : ℝ)) by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]; norm_num]
    exact ENNReal.ofReal_le_ofReal hbUpper

end MathResearchAnalysis.ClockLiteratureTransfer

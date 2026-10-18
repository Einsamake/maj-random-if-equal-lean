module

public import MathResearchAnalysis.SquareSpin
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic

set_option autoImplicit false

/-!
# Zero-temperature limit of actual finite square heat-bath words

The local field includes the four fixed boundary inputs. The finite-temperature
heat-bath probability converges to the fair-tie majority probability. Products
of finitely many actual one-site kernels converge on every real test function.
This does not supply the Peres--Winkler censoring inequality or CMST theorem.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace MathResearchAnalysis.ZeroTemperature

abbrev Config (n : Nat) := SquareSpin.Config n
abbrev Site (n : Nat) := SquareTasks.Vertex n

def field {n : Nat} (f : Config n) (v : Site n) : ℝ := 2 * (SquareSpin.ones f v : ℝ) - 4

def warmProbability (β h : ℝ) : ℝ := (1 + Real.exp ((-2 * h) * β))⁻¹

def coldProbability (h : ℝ) : ℝ := if 0 < h then 1 else if h < 0 then 0 else 1 / 2

theorem warmProbability_pos (β h : ℝ) : 0 < warmProbability β h := by
  exact inv_pos.mpr (by positivity)

theorem warmProbability_lt_one (β h : ℝ) : warmProbability β h < 1 := by
  unfold warmProbability
  exact (inv_lt_one₀ (by positivity)).mpr (by linarith [Real.exp_pos ((-2 * h) * β)])

theorem warmProbability_zero_temperature (h : ℝ) :
    Tendsto (fun β => warmProbability β h) atTop (𝓝 (coldProbability h)) := by
  rcases lt_trichotomy 0 h with hp | hz | hn
  · have hc : -2 * h < 0 := by linarith
    have he : Tendsto (fun β : ℝ => Real.exp ((-2 * h) * β)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc)
    have hi := (tendsto_const_nhds.add he).inv₀ (show (1 : ℝ) + 0 ≠ 0 by norm_num)
    simpa only [warmProbability, coldProbability, ite_eq_left hp, add_zero, inv_one] using hi
  · subst h
    convert (tendsto_const_nhds :
      Tendsto (fun _β : ℝ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2))) using 1 <;>
      norm_num [warmProbability, coldProbability]
  · have hc : 0 < -2 * h := by linarith
    have he : Tendsto (fun β : ℝ => Real.exp ((-2 * h) * β)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc)
    have hd : Tendsto (fun β : ℝ => 1 + Real.exp ((-2 * h) * β)) atTop atTop := by
      simpa only [add_comm] using he.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
    have hi := tendsto_inv_atTop_zero.comp hd
    simpa only [Function.comp_def, warmProbability, coldProbability,
      ite_eq_right (not_lt.mpr hn.le), ite_eq_left hn] using hi

theorem field_pos_iff {n : Nat} (f : Config n) (v : Site n) :
    0 < field f v ↔ 2 < SquareSpin.ones f v := by
  unfold field
  constructor
  · intro h
    have h' : (2 : ℝ) < (SquareSpin.ones f v : ℝ) := by linarith
    exact_mod_cast h'
  · intro h
    have h' : (2 : ℝ) < (SquareSpin.ones f v : ℝ) := by exact_mod_cast h
    linarith

theorem field_neg_iff {n : Nat} (f : Config n) (v : Site n) :
    field f v < 0 ↔ SquareSpin.ones f v < 2 := by
  unfold field
  constructor
  · intro h
    have h' : (SquareSpin.ones f v : ℝ) < 2 := by linarith
    exact_mod_cast h'
  · intro h
    have h' : (SquareSpin.ones f v : ℝ) < 2 := by exact_mod_cast h
    linarith

def warmStep {n : Nat} (β : ℝ) (v : Site n) (φ : Config n → ℝ) (f : Config n) : ℝ :=
  warmProbability β (field f v) * φ (Function.update f v true) +
    (1 - warmProbability β (field f v)) * φ (Function.update f v false)

def coldStep {n : Nat} (v : Site n) (φ : Config n → ℝ) (f : Config n) : ℝ :=
  coldProbability (field f v) * φ (Function.update f v true) +
    (1 - coldProbability (field f v)) * φ (Function.update f v false)

/-- The limiting kernel is exactly the actual rule averaged over a fair tie mark. -/
theorem coldStep_eq_actual_majority {n : Nat} (v : Site n) (φ : Config n → ℝ)
    (f : Config n) :
    coldStep v φ f =
      (φ (SquareSpin.cellUpdate f v true) + φ (SquareSpin.cellUpdate f v false)) / 2 := by
  rcases lt_trichotomy 2 (SquareSpin.ones f v) with hp | hz | hn
  · have hf := (field_pos_iff f v).mpr hp
    simp only [coldStep, coldProbability, ite_eq_left hf, one_mul, sub_self, zero_mul, add_zero,
      SquareSpin.cellUpdate, SquareSpin.rule_of_gt_two f v true hp,
      SquareSpin.rule_of_gt_two f v false hp]
    ring
  · have hf : field f v = 0 := by unfold field; rw [← hz]; norm_num
    simp only [coldStep, coldProbability, hf, lt_self_iff_false, ite_false,
      SquareSpin.cellUpdate, SquareSpin.rule_of_eq_two f v true hz.symm,
      SquareSpin.rule_of_eq_two f v false hz.symm]
    ring
  · have hf := (field_neg_iff f v).mpr hn
    simp only [coldStep, coldProbability, ite_eq_right (not_lt.mpr hf.le), ite_eq_left hf, zero_mul,
      sub_zero, one_mul, zero_add, SquareSpin.cellUpdate,
      SquareSpin.rule_of_lt_two f v true hn, SquareSpin.rule_of_lt_two f v false hn]
    ring

def warmWord {n : Nat} (β : ℝ) : List (Site n) → (Config n → ℝ) → Config n → ℝ
  | [], φ, f => φ f
  | v :: rest, φ, f => warmStep β v (warmWord β rest φ) f

def coldWord {n : Nat} : List (Site n) → (Config n → ℝ) → Config n → ℝ
  | [], φ, f => φ f
  | v :: rest, φ, f => coldStep v (coldWord rest φ) f

def actualMajorityWordMean {n : Nat} : List (Site n) → (Config n → ℝ) → Config n → ℝ
  | [], φ, f => φ f
  | v :: rest, φ, f =>
      (actualMajorityWordMean rest φ (SquareSpin.cellUpdate f v true) +
        actualMajorityWordMean rest φ (SquareSpin.cellUpdate f v false)) / 2

theorem coldWord_eq_actualMajorityWordMean {n : Nat} (word : List (Site n))
    (φ : Config n → ℝ) (f : Config n) :
    coldWord word φ f = actualMajorityWordMean word φ f := by
  induction word generalizing f with
  | nil => rfl
  | cons v rest ih =>
    rw [coldWord, coldStep_eq_actual_majority]
    simp only [actualMajorityWordMean, ih]

/-- Every fixed finite product of the genuine one-site heat-bath kernels converges. -/
theorem finite_word_zero_temperature {n : Nat} (word : List (Site n))
    (φ : Config n → ℝ) (f : Config n) :
    Tendsto (fun β => warmWord β word φ f) atTop (𝓝 (coldWord word φ f)) := by
  induction word generalizing f with
  | nil => exact tendsto_const_nhds
  | cons v rest ih =>
    exact ((warmProbability_zero_temperature (field f v)).mul
      (ih (Function.update f v true))).add
      ((tendsto_const_nhds.sub (warmProbability_zero_temperature (field f v))).mul
        (ih (Function.update f v false)))

theorem finite_word_limit_actual_majority {n : Nat} (word : List (Site n))
    (φ : Config n → ℝ) (f : Config n) :
    Tendsto (fun β => warmWord β word φ f) atTop
      (𝓝 (actualMajorityWordMean word φ f)) := by
  rw [← coldWord_eq_actualMajorityWordMean]
  exact finite_word_zero_temperature word φ f

end MathResearchAnalysis.ZeroTemperature

module

public import MathResearchAnalysis.InfiniteGridModel
public import Mathlib.Logic.Function.Basic

set_option autoImplicit false

public section

/-!
# Translation of the actual integer-grid dynamics

States and the complete deterministic mark field are translated together.
An odd lattice translation reverses checkerboard colour and its initialization
phase. These are pathwise identities, without a probability law or any
assumption of finite recovery.
-/

namespace MathResearchAnalysis.InfiniteGridTranslation

open InfiniteGridModel BipartiteDynamics

/-- Pull back a lattice coordinate by the translation vector. -/
@[expose] def shift (a z : Site) : Site := (z.1 - a.1, z.2 - a.2)

@[expose] def translate (a : Site) (f : Config) : Config := fun z => f (shift a z)

@[expose] def translateMarks (a : Site) (marks : Marks) : Marks :=
  fun t z => marks t (shift a z)

theorem shift_north (a z : Site) : shift a (north z) = north (shift a z) := by
  apply Prod.ext
  · rfl
  · dsimp [shift, north]; omega

theorem shift_east (a z : Site) : shift a (east z) = east (shift a z) := by
  apply Prod.ext
  · dsimp [shift, east]; omega
  · rfl

theorem shift_south (a z : Site) : shift a (south z) = south (shift a z) := by
  apply Prod.ext
  · rfl
  · dsimp [shift, south]; omega

theorem shift_west (a z : Site) : shift a (west z) = west (shift a z) := by
  apply Prod.ext
  · dsimp [shift, west]; omega
  · rfl

/-- The four actual inputs and the tie mark are shifted by the same vector. -/
theorem update_translate (a : Site) (marks : Marks) (t : Nat) (z : Site)
    (f : Config) :
    update (translateMarks a marks) t z (translate a f) =
      update marks t (shift a z) f := by
  simp only [update, translate, translateMarks, shift_north, shift_east,
    shift_south, shift_west]

/-- Whole configurations agree at every time, for any fixed mark field. -/
theorem synchronous_translate (a : Site) (marks : Marks) (initial : Config)
    (t : Nat) :
    synchronous (translateMarks a marks) (translate a initial) t =
      translate a (synchronous marks initial t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [synchronous_succ, ih]
    funext z
    exact update_translate a marks (t + 1) z (synchronous marks initial t)

private theorem shift_neg_shift (a z : Site) :
    shift a (shift (-a.1, -a.2) z) = z := by
  apply Prod.ext <;> dsimp [shift] <;> omega

private theorem neg_shift_shift (a z : Site) :
    shift (-a.1, -a.2) (shift a z) = z := by
  apply Prod.ext <;> dsimp [shift] <;> omega

theorem translate_neg_translate (a : Site) (f : Config) :
    translate (-a.1, -a.2) (translate a f) = f := by
  funext z
  exact congrArg f (shift_neg_shift a z)

theorem translate_translate_neg (a : Site) (f : Config) :
    translate a (translate (-a.1, -a.2) f) = f := by
  funext z
  exact congrArg f (neg_shift_shift a z)

/-- Translation has the explicit inverse given by the negative vector. -/
theorem translate_bijective (a : Site) : Function.Bijective (translate a) := by
  constructor
  · intro f g h
    have hinv := congrArg (translate (-a.1, -a.2)) h
    simpa only [translate_neg_translate] using hinv
  · intro f
    exact ⟨translate (-a.1, -a.2) f, translate_translate_neg a f⟩

@[simp] theorem translate_zero (a : Site) : translate a zeroState = zeroState := rfl

theorem translate_eq_zero_iff (a : Site) (f : Config) :
    translate a f = zeroState ↔ f = zeroState := by
  constructor
  · intro h
    have hinv := congrArg (translate (-a.1, -a.2)) h
    simpa only [translate_neg_translate, translate_zero] using hinv
  · rintro rfl
    exact translate_zero a

/-- Even translations preserve colour; odd translations reverse it. -/
theorem colour_shift (a z : Site) :
    colour (shift a z) = if colour a then colour z else !(colour z) := by
  by_cases ha : (a.1 + a.2) % 2 = 0 <;>
    by_cases hz : (z.1 + z.2) % 2 = 0
  · have hs : ((z.1 - a.1) + (z.2 - a.2)) % 2 = 0 := by omega
    simp [colour, shift, ha, hz, hs]
  · have hs : ((z.1 - a.1) + (z.2 - a.2)) % 2 ≠ 0 := by omega
    simp [colour, shift, ha, hz, hs]
  · have hs : ((z.1 - a.1) + (z.2 - a.2)) % 2 ≠ 0 := by omega
    simp [colour, shift, ha, hz, hs]
  · have hs : ((z.1 - a.1) + (z.2 - a.2)) % 2 = 0 := by omega
    simp [colour, shift, ha, hz, hs]

/-- Initialization phase must reverse exactly at odd translations. -/
@[expose] def translatePhase (a : Site) (phase : Bool) : Bool :=
  if colour a then phase else !phase

theorem activeColour_translatePhase (a : Site) (phase : Bool) (t : Nat) :
    activeColour (translatePhase a phase) t =
      translatePhase a (activeColour phase t) := by
  cases h : colour a <;> simp [translatePhase, h, activeColour_complement]

private theorem colour_eq_active_translate (a z : Site) (phase : Bool) (t : Nat) :
    (colour z = activeColour (translatePhase a phase) t) ↔
      colour (shift a z) = activeColour phase t := by
  rw [colour_shift, activeColour_translatePhase]
  cases h : colour a <;> cases colour z <;>
    cases activeColour phase t <;> simp [translatePhase, h]

/-- Checkerboard translation includes the required parity-dependent phase. -/
theorem alternating_translate (a : Site) (marks : Marks) (initial : Config)
    (phase : Bool) (t : Nat) :
    alternating (translateMarks a marks) (translate a initial)
        (translatePhase a phase) t =
      translate a (alternating marks initial phase t) := by
  cases t with
  | zero => rfl
  | succ t =>
    funext z
    rw [splitting_succ, synchronous_translate, synchronous_translate]
    change (if colour z = activeColour (translatePhase a phase) (t + 1) then
      synchronous marks initial (t + 1) (shift a z)
      else synchronous marks initial t (shift a z)) =
      alternating marks initial phase (t + 1) (shift a z)
    rw [splitting_succ]
    simp only [colour_eq_active_translate]

@[expose] def InsideTranslated (L : Nat) (a z : Site) : Prop :=
  Inside L (shift a z)

@[expose] def SupportedTranslated (L : Nat) (a : Site) (f : Config) : Prop :=
  ∀ z, ¬InsideTranslated L a z → f z = false

theorem supported_translate_iff (L : Nat) (a : Site) (f : Config) :
    SupportedTranslated L a (translate a f) ↔ Supported L f := by
  constructor
  · intro h z hz
    have hs := h (shift (-a.1, -a.2) z)
    have hout : ¬InsideTranslated L a (shift (-a.1, -a.2) z) := by
      simpa only [InsideTranslated, shift_neg_shift] using hz
    simpa only [translate, shift_neg_shift] using hs hout
  · intro h z hz
    exact h (shift a z) hz

/-- The actual synchronous evolution keeps the translated containing square. -/
theorem synchronous_supported_translated (a : Site) (marks : Marks) (L : Nat)
    (initial : Config) (hSupport : Supported L initial) (t : Nat) :
    SupportedTranslated L a
      (synchronous (translateMarks a marks) (translate a initial) t) := by
  rw [synchronous_translate, supported_translate_iff]
  exact synchronous_supported marks L initial hSupport t

theorem alternating_supported_translated (a : Site) (marks : Marks) (L : Nat)
    (initial : Config) (hSupport : Supported L initial) (phase : Bool) (t : Nat) :
    SupportedTranslated L a
      (alternating (translateMarks a marks) (translate a initial)
        (translatePhase a phase) t) := by
  rw [alternating_translate, supported_translate_iff]
  exact alternating_supported marks L initial hSupport phase t

end MathResearchAnalysis.InfiniteGridTranslation

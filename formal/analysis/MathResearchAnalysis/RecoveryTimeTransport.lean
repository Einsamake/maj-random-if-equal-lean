module

public import MathResearchAnalysis.ExtendedRecoveryTime

set_option autoImplicit false

/-!
# Transport of actual extended first-hit times

Equality of zero events at every time transports the first hit, including
infinite times. No absorption, finite-hitting witness or probability law is
needed for these deterministic statements.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.RecoveryTimeTransport

universe u v w

variable {Ω : Type u} {A : Type v} {B : Type w}

theorem time_le_time_of_zero_imp (X : Nat → Ω → A) (Y : Nat → Ω → B)
    (a : A) (b : B) (ω : Ω) (h : ∀ t, Y t ω = b → X t ω = a) :
    ExtendedRecoveryTime.time X a ω ≤ ExtendedRecoveryTime.time Y b ω := by
  cases ht : ExtendedRecoveryTime.time Y b ω using ENat.recTopCoe with
  | top => exact le_top
  | coe t =>
    have hle : ExtendedRecoveryTime.time Y b ω ≤ (t : ℕ∞) := by rw [ht]
    obtain ⟨s, hst, hs⟩ := (ExtendedRecoveryTime.time_le_nat_iff Y b ω t).mp hle
    exact (ExtendedRecoveryTime.time_le_nat_iff X a ω t).mpr ⟨s, hst, h s hs⟩

theorem time_eq_of_zero_iff (X : Nat → Ω → A) (Y : Nat → Ω → B)
    (a : A) (b : B) (ω : Ω) (h : ∀ t, X t ω = a ↔ Y t ω = b) :
    ExtendedRecoveryTime.time X a ω = ExtendedRecoveryTime.time Y b ω := by
  exact le_antisymm (time_le_time_of_zero_imp X Y a b ω (fun t => (h t).mpr))
    (time_le_time_of_zero_imp Y X b a ω (fun t => (h t).mp))

end MathResearchAnalysis.RecoveryTimeTransport

import Std

/-!
The actual four-neighbour rule, with a fixed tie mark.  The tie mark is a Bool,
so these are deterministic pathwise facts, not claims about a probability law.
-/

namespace MathResearch.Majority

def update (north east south west tie : Bool) : Bool :=
  let ones := north.toNat + east.toNat + south.toNat + west.toNat
  if 2 < ones then true else if ones < 2 then false else tie

theorem zero_fixed (tie : Bool) : update false false false false tie = false := by
  rfl

theorem one_fixed (tie : Bool) : update true true true true tie = true := by
  rfl

/-- At most one nonzero neighbour cannot create a nonzero site. -/
theorem at_most_one :
    ∀ north east south west tie : Bool,
      north.toNat + east.toNat + south.toNat + west.toNat ≤ 1 →
      update north east south west tie = false := by
  decide

/-- Monotonicity of the actual rule for a common deterministic tie mark. -/
theorem monotone_common_mark :
    ∀ n e s w n' e' s' w' tie : Bool,
      n ≤ n' → e ≤ e' → s ≤ s' → w ≤ w' →
      update n e s w tie ≤ update n' e' s' w' tie := by
  decide

end MathResearch.Majority

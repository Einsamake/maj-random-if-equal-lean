module
public import MathResearchAnalysis.MixedRightCountMoments
public import Mathlib.Tactic
set_option autoImplicit false
/-! An actual right-half particle count controls a whole southwest square.
A false cell is white. This is a fixed-time local assertion; the auxiliary
mixed-boundary all-white configuration is not claimed to be absorbing. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MixedLocalClearing
open DropletClockLaw (Config Sample)
open ClippedSquareCoordinates (parameter)

/-- All actual cells of the southwest side-N block are white. -/
def localWhite {M : Nat} (N : Nat) (f : Fin M × Fin M → Bool) : Prop :=
  ∀ v, v.1.val<N → v.2.val<N → f v=false

/-- Monotonicity propagates a white diagonal corner to its entire southwest
block. The count itself supplies the necessary side bound N≤M. -/
theorem localWhite_of_le_rightCount {M : Nat} {f : Fin M × Fin M → Bool}
    (hf : Monotone f) (N : Nat) (hcount : N ≤ YoungParticles.rightCount f) :
    localWhite N f := by
  have hNM : N≤M := hcount.trans (YoungParticles.rightCount_le_side f)
  by_cases hN : N=0
  · subst N
    intro v hv
    omega
  · have hNpos : 1≤N := by omega
    let d : Fin M := ⟨N-1,by omega⟩
    have hd : f (d,d)=false :=
      (YoungParticles.diagonal_false_iff_le_rightCount hf N hNpos hNM).2 hcount
    intro v hvx hvy
    have hvd : v ≤ (d,d) := by
      constructor
      · change v.1.val ≤ N-1
        omega
      · change v.2.val ≤ N-1
        omega
    have h := hf hvd
    rw [hd] at h
    have hb : ∀ b : Bool, b ≤ false → b=false := by decide
    exact hb _ h

/-- For a block inside the square the count threshold is also necessary.
The side condition keeps the requested block inside the available square. -/
theorem localWhite_iff_le_rightCount {M : Nat} {f : Fin M × Fin M → Bool}
    (hf : Monotone f) (N : Nat) (hNM : N≤M) :
    localWhite N f ↔ N ≤ YoungParticles.rightCount f := by
  constructor
  · intro hw
    by_cases hN : N=0
    · subst N
      exact Nat.zero_le _
    · have hNpos : 1≤N := by omega
      apply (YoungParticles.diagonal_false_iff_le_rightCount hf N hNpos hNM).1
      exact hw (⟨N-1,by omega⟩,⟨N-1,by omega⟩) (by simp; omega) (by simp; omega)
  · exact localWhite_of_le_rightCount hf N

/-- The count and the state are from the same original-law clock sample.
No cross-size clock restriction, stopping rule, or absorption is assumed. -/
theorem endpoint_localWhite_of_count_le (L : Nat) (initial : Config L)
    (hinit : Monotone initial) (t : Real) (z : Sample L) (N : Nat)
    (hcount : (N : Real) ≤ MixedRightCountMoments.count L initial t z) :
    localWhite N (MixedSquareClockLaw.endpoint (parameter L) t initial z) := by
  rw [MixedRightCountMoments.count_eq_rightCount L initial hinit t z] at hcount
  apply localWhite_of_le_rightCount
    (MixedSquareClockLaw.endpoint_monotone_shape _ t initial hinit z) N
  exact_mod_cast hcount

end MathResearchAnalysis.MixedLocalClearing

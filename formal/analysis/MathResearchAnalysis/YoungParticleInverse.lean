module

public import MathResearchAnalysis.YoungParticles

set_option autoImplicit false

/-!
# A genuine inverse for the finite ordered-particle encoding

Every strictly increasing list of M slots in a path of length 2M reconstructs
one coordinate-monotone square state. Bounds and order are proved by finite
interval injections, not supplied as extra reconstruction assumptions.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.YoungParticleInverse

theorem position_lower_bound {M : Nat} (p : Fin M → Fin (2*M)) (hp : StrictMono p)
    (r : Fin M) : r.val ≤ (p r).val := by
  have hs : (Finset.Iic r).image p ⊆ Finset.Iic (p r) := by
    intro z hz
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_Iic.mpr (hp.monotone (Finset.mem_Iic.mp hs))
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hp.injective,Fin.card_Iic,Fin.card_Iic] at hc
  omega

theorem position_upper_bound {M : Nat} (p : Fin M → Fin (2*M)) (hp : StrictMono p)
    (r : Fin M) : (p r).val ≤ r.val+M := by
  have hs : (Finset.Ioi r).image p ⊆ Finset.Ioi (p r) := by
    intro z hz
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_Ioi.mpr (hp (Finset.mem_Ioi.mp hs))
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hp.injective,Fin.card_Ioi,Fin.card_Ioi] at hc
  have hr := r.isLt
  have hpbound := (p r).isLt
  omega

/-- Increasing distinct slots force their displacement from the label to increase. -/
theorem offset_monotone {M : Nat} (p : Fin M → Fin (2*M)) (hp : StrictMono p) :
    Monotone (fun r => (p r).val-r.val) := by
  intro r s hrs
  have hs : (Finset.Icc r s).image p ⊆ Finset.Icc (p r) (p s) := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    have huu := Finset.mem_Icc.mp hu
    exact Finset.mem_Icc.mpr ⟨hp.monotone huu.1,hp.monotone huu.2⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hp.injective,Fin.card_Icc,Fin.card_Icc] at hc
  have hnat : r.val ≤ s.val := hrs
  have hpnat : (p r).val ≤ (p s).val := hp.monotone hrs
  have hr := position_lower_bound p hp r
  have ht := position_lower_bound p hp s
  change (p r).val-r.val ≤ (p s).val-s.val
  omega

/-- Reconstruct the true/false row from an actual integer threshold. -/
def fromRows {M : Nat} (lengths : Fin M → Nat) : Fin M × Fin M → Bool :=
  fun v => decide (lengths v.2 ≤ v.1.val)

theorem fromRows_false_iff {M : Nat} (lengths : Fin M → Nat) (x y : Fin M) :
    fromRows lengths (x,y) = false ↔ x.val < lengths y := by
  simp [fromRows,not_le]

theorem fromRows_monotone {M : Nat} (lengths : Fin M → Nat) (ha : Antitone lengths) :
    Monotone (fromRows lengths) := by
  intro a b hab
  have hrow := ha hab.2
  have hx : a.1.val ≤ b.1.val := hab.1
  by_cases hs : lengths a.2 ≤ a.1.val
  · have ht : lengths b.2 ≤ b.1.val := le_trans hrow (le_trans hs hx)
    simp [fromRows,hs,ht]
  · simp [fromRows,hs]

/-- The threshold counts are proved even when a row fills the entire side. -/
theorem rowLength_fromRows {M : Nat} (lengths : Fin M → Nat)
    (hb : ∀ y, lengths y ≤ M) (y : Fin M) :
    YoungRows.rowLength (fromRows lengths) y = lengths y := by
  classical
  by_cases hk : lengths y < M
  · let k : Fin M := ⟨lengths y,hk⟩
    have hs : YoungRows.rowZeros (fromRows lengths) y = Finset.Iio k := by
      ext x
      simp only [YoungRows.mem_rowZeros,fromRows_false_iff,Finset.mem_Iio]
      rfl
    rw [YoungRows.rowLength,hs,Fin.card_Iio]
  · have he : lengths y = M := le_antisymm (hb y) (Nat.le_of_not_gt hk)
    have hs : YoungRows.rowZeros (fromRows lengths) y = Finset.univ := by
      ext x
      simp only [YoungRows.mem_rowZeros,fromRows_false_iff,Finset.mem_univ,iff_true]
      simpa only [he] using x.isLt
    rw [YoungRows.rowLength,hs,Finset.card_univ,Fintype.card_fin,he]

theorem fromRows_actual_eq {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f) :
    fromRows (YoungRows.rowLength f) = f := by
  funext v
  cases hv : f v with
  | false =>
    have h := (YoungRows.false_iff_lt_rowLength hf v.1 v.2).mp hv
    simpa only [hv] using (fromRows_false_iff (YoungRows.rowLength f) v.1 v.2).mpr h
  | true =>
    have h := (YoungRows.true_iff_rowLength_le hf v.1 v.2).mp hv
    simp [fromRows,h]

/-- The inverse row length, without silently replacing truncated subtraction. -/
def decodedRow {M : Nat} (p : Fin M → Fin (2*M)) (y : Fin M) : Nat :=
  (p y.rev).val-y.rev.val

theorem decodedRow_le_side {M : Nat} (p : Fin M → Fin (2*M)) (hp : StrictMono p) :
    ∀ y, decodedRow p y ≤ M := by
  intro y
  have hu := position_upper_bound p hp y.rev
  unfold decodedRow
  omega

theorem decodedRow_antitone {M : Nat} (p : Fin M → Fin (2*M)) (hp : StrictMono p) :
    Antitone (decodedRow p) := by
  intro y z hyz
  exact offset_monotone p hp (Fin.rev_le_rev.mpr hyz)

/-- Decode every ordered M-particle configuration into its actual square state. -/
def decode {M : Nat} (p : Fin M → Fin (2*M)) : Fin M × Fin M → Bool :=
  fromRows (decodedRow p)

theorem decode_monotone {M : Nat} (p : Fin M → Fin (2*M)) (hp : StrictMono p) :
    Monotone (decode p) :=
  fromRows_monotone _ (decodedRow_antitone p hp)

theorem rowLength_decode {M : Nat} (p : Fin M → Fin (2*M)) (hp : StrictMono p)
    (y : Fin M) : YoungRows.rowLength (decode p) y = decodedRow p y :=
  rowLength_fromRows _ (decodedRow_le_side p hp) y

theorem decodedRow_particle {M : Nat} (f : Fin M × Fin M → Bool) (y : Fin M) :
    decodedRow (YoungParticles.particle f) y = YoungRows.rowLength f y := by
  simp [decodedRow,YoungParticles.particle_val,YoungParticles.positionNat]

theorem decode_particle {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f) :
    decode (YoungParticles.particle f) = f := by
  have he : decodedRow (YoungParticles.particle f) = YoungRows.rowLength f := by
    funext y
    exact decodedRow_particle f y
  unfold decode
  rw [he]
  exact fromRows_actual_eq hf

theorem particle_decode {M : Nat} (p : Fin M → Fin (2*M)) (hp : StrictMono p) :
    YoungParticles.particle (decode p) = p := by
  funext r
  apply Fin.ext
  change r.val+YoungRows.rowLength (decode p) r.rev = (p r).val
  rw [rowLength_decode p hp]
  simp only [decodedRow,Fin.rev_rev]
  have h := position_lower_bound p hp r
  omega

/-- A genuine two-sided equivalence; M=0 is covered by the same construction. -/
def encodingEquiv (M : Nat) :
    {f : Fin M × Fin M → Bool // Monotone f} ≃
      {p : Fin M → Fin (2*M) // StrictMono p} where
  toFun f := ⟨YoungParticles.particle f.1,YoungParticles.particle_strictMono f.2⟩
  invFun p := ⟨decode p.1,decode_monotone p.1 p.2⟩
  left_inv f := Subtype.ext (decode_particle f.2)
  right_inv p := Subtype.ext (particle_decode p.1 p.2)

end MathResearchAnalysis.YoungParticleInverse


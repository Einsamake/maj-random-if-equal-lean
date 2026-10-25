module

public import MathResearchAnalysis.YoungRows
public import Mathlib.Data.Fin.Rev

set_option autoImplicit false

/-!
# Actual finite particle positions encoded by monotone white row lengths

Labels and positions use zero-based finite coordinates. A false cell is white.
The particle in reversed row r.rev is at r + that row's actual white length.
No inverse encoding, clock law, generator or probability bound is assumed.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.YoungParticles

/-- The actual natural-number position of the particle labelled r. -/
def positionNat {M : Nat} (f : Fin M × Fin M → Bool) (r : Fin M) : Nat :=
  r.val + YoungRows.rowLength f r.rev

theorem positionNat_lt_twice {M : Nat} (f : Fin M × Fin M → Bool) (r : Fin M) :
    positionNat f r < 2*M := by
  have hr := r.isLt
  have hl := YoungRows.rowLength_le_side f r.rev
  unfold positionNat
  omega

/-- A position in the real finite path of exactly 2M slots. -/
def particle {M : Nat} (f : Fin M × Fin M → Bool) (r : Fin M) : Fin (2*M) :=
  ⟨positionNat f r, positionNat_lt_twice f r⟩

@[simp] theorem particle_val {M : Nat} (f : Fin M × Fin M → Bool) (r : Fin M) :
    (particle f r).val = positionNat f r := rfl

theorem positionNat_strictMono {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f) :
    StrictMono (positionNat f) := by
  intro r s hrs
  have hrev : s.rev ≤ r.rev := Fin.rev_le_rev.mpr hrs.le
  have hl := YoungRows.rowLength_antitone hf hrev
  have hrs' : r.val < s.val := hrs
  unfold positionNat
  omega

theorem particle_strictMono {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f) :
    StrictMono (particle f) := by
  intro r s hrs
  exact positionNat_strictMono hf hrs

theorem particle_injective {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f) :
    Function.Injective (particle f) := (particle_strictMono hf).injective

/-- No configuration information is lost by the labelled particle positions. -/
theorem encoding_injective {M : Nat} {f g : Fin M × Fin M → Bool}
    (hf : Monotone f) (hg : Monotone g) (h : particle f = particle g) : f = g := by
  apply YoungRows.ext_of_rowLength_eq hf hg
  intro y
  have he := congrArg (fun p : Fin M → Fin (2*M) => (p y.rev).val) h
  simp only [particle_val,positionNat,Fin.rev_rev] at he
  exact Nat.add_left_cancel he

/-- Actual occupied slots, not a separate particle-configuration premise. -/
def particles {M : Nat} (f : Fin M × Fin M → Bool) : Finset (Fin (2*M)) :=
  Finset.univ.image (particle f)

theorem particles_card {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f) :
    (particles f).card = M := by
  rw [particles,Finset.card_image_of_injective _ (particle_injective hf)]
  simp

@[simp] theorem particle_all_true {M : Nat} (r : Fin M) :
    (particle (fun _ : Fin M × Fin M => true) r).val = r.val := by
  simp [particle,positionNat]

@[simp] theorem particle_all_false {M : Nat} (r : Fin M) :
    (particle (fun _ : Fin M × Fin M => false) r).val = r.val+M := by
  simp [particle,positionNat]

/-- The all-true initial square gives precisely the left M slots. -/
theorem mem_particles_all_true {M : Nat} (s : Fin (2*M)) :
    s ∈ particles (fun _ : Fin M × Fin M => true) ↔ s.val < M := by
  constructor
  · intro hs
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hs
    have he := congrArg Fin.val hr
    rw [particle_all_true] at he
    exact he ▸ r.isLt
  · intro hs
    refine Finset.mem_image.mpr ⟨⟨s.val,hs⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    simp only [particle_all_true]

/-- The all-false square gives precisely the right M slots. -/
theorem mem_particles_all_false {M : Nat} (s : Fin (2*M)) :
    s ∈ particles (fun _ : Fin M × Fin M => false) ↔ M ≤ s.val := by
  constructor
  · intro hs
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hs
    have he := congrArg Fin.val hr
    rw [particle_all_false] at he
    omega
  · intro hs
    have hslt := s.isLt
    have hsub : s.val-M < M := by omega
    refine Finset.mem_image.mpr ⟨⟨s.val-M,hsub⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    simp only [particle_all_false]
    omega

/-- Number of actual labelled particles in the right half. -/
def rightCount {M : Nat} (f : Fin M × Fin M → Bool) : Nat :=
  (Finset.univ.filter (fun r : Fin M => M ≤ positionNat f r)).card

/-- The actual false diagonal cells. -/
def diagonalZeros {M : Nat} (f : Fin M × Fin M → Bool) : Finset (Fin M) :=
  Finset.univ.filter (fun d => f (d,d) = false)

theorem rightCount_le_side {M : Nat} (f : Fin M × Fin M → Bool) : rightCount f ≤ M := by
  simpa only [rightCount,Finset.card_univ,Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (Fin M)) (fun r => M ≤ positionNat f r)

theorem right_particle_iff_diagonal_false {M : Nat} {f : Fin M × Fin M → Bool}
    (hf : Monotone f) (r : Fin M) :
    M ≤ positionNat f r ↔ f (r.rev,r.rev) = false := by
  rw [YoungRows.false_iff_lt_rowLength hf]
  have hr := r.isLt
  rw [Fin.val_rev]
  unfold positionNat
  omega

/-- Reversing row labels counts exactly the actual white diagonal cells. -/
theorem rightCount_eq_diagonal_card {M : Nat} {f : Fin M × Fin M → Bool}
    (hf : Monotone f) : rightCount f = (diagonalZeros f).card := by
  apply Finset.card_bij (fun r _ => r.rev)
  · intro r hr
    have hm := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(right_particle_iff_diagonal_false hf r).mp hm⟩
  · intro r hr s hs he
    exact Fin.rev_injective he
  · intro d hd
    have hm := (Finset.mem_filter.mp hd).2
    refine ⟨d.rev,?_,Fin.rev_rev d⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    apply (right_particle_iff_diagonal_false hf d.rev).mpr
    simpa only [Fin.rev_rev] using hm

/-- The diagonal test has the exact strict threshold, without Nat subtraction. -/
theorem diagonal_false_iff_lt_rightCount {M : Nat} {f : Fin M × Fin M → Bool}
    (hf : Monotone f) (d : Fin M) : f (d,d) = false ↔ d.val < rightCount f := by
  have hdiag : Monotone (fun v : Fin M × Fin M => f (v.1,v.1)) := by
    intro a b hab
    exact hf ⟨hab.1,hab.1⟩
  have h := YoungRows.false_iff_lt_rowLength hdiag d d
  change f (d,d) = false ↔ d.val < (diagonalZeros f).card at h
  rw [rightCount_eq_diagonal_card hf]
  exact h

/-- The human side-N statement requires 1 <= N <= M. -/
theorem diagonal_false_iff_le_rightCount {M : Nat} {f : Fin M × Fin M → Bool}
    (hf : Monotone f) (N : Nat) (hN : 1 ≤ N) (hNM : N ≤ M) :
    f (⟨N-1,by omega⟩,⟨N-1,by omega⟩) = false ↔ N ≤ rightCount f := by
  rw [diagonal_false_iff_lt_rightCount hf]
  change N-1 < rightCount f ↔ N ≤ rightCount f
  omega

end MathResearchAnalysis.YoungParticles

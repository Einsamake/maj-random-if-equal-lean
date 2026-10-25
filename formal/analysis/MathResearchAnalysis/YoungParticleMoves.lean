module

public import MathResearchAnalysis.YoungParticles
public import MathResearchAnalysis.YoungRowUpdates
public import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

/-!
# Actual corner flips move one labelled particle to an adjacent vacant slot

The changed label is the reversed row. Both adjacency and vacancy are derived
from the true cell update and the proved row/shape invariants. These are
finite deterministic identities, with no assumed particle law or flip rate.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.YoungParticleMoves

open YoungParticles

/-- Every other labelled particle is unchanged by an actual single write. -/
theorem positionNat_cellUpdate_other {n : Nat} (f : SquareSpin.Config n)
    (v : SquareTasks.Vertex n) (tie : Bool) (r : Fin (n+2)) (hr : r ≠ v.2.rev) :
    positionNat (MixedSquareModel.cellUpdate f v tie) r = positionNat f r := by
  have hrow : r.rev ≠ v.2 := by
    intro he
    apply hr
    simpa only [Fin.rev_rev] using congrArg Fin.rev he
  unfold positionNat
  rw [YoungRowUpdates.cellUpdate_other_row f v tie r.rev hrow]

theorem particle_cellUpdate_other {n : Nat} (f : SquareSpin.Config n)
    (v : SquareTasks.Vertex n) (tie : Bool) (r : Fin (n+2)) (hr : r ≠ v.2.rev) :
    particle (MixedSquareModel.cellUpdate f v tie) r = particle f r := by
  apply Fin.ext
  exact positionNat_cellUpdate_other f v tie r hr

/-- Deleting a true corner moves its own labelled particle one slot right. -/
theorem removable_positionNat {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.removable f v) :
    positionNat (MixedSquareModel.cellUpdate f v false) v.2.rev =
      positionNat f v.2.rev + 1 := by
  simp only [positionNat,Fin.rev_rev,YoungRowUpdates.removable_rowLength hf hc]
  omega

/-- Birthing a true corner moves its own labelled particle one slot left. -/
theorem addable_positionNat {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.addable f v) :
    positionNat (MixedSquareModel.cellUpdate f v true) v.2.rev + 1 =
      positionNat f v.2.rev := by
  simp only [positionNat,Fin.rev_rev]
  have h := YoungRowUpdates.addable_rowLength hf hc
  omega

theorem removable_new_ne_old {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.removable f v) :
    particle (MixedSquareModel.cellUpdate f v false) v.2.rev ≠ particle f v.2.rev := by
  intro he
  have hv := congrArg Fin.val he
  have hm := removable_positionNat hf hc
  simp only [particle_val] at hv
  omega

theorem addable_new_ne_old {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.addable f v) :
    particle (MixedSquareModel.cellUpdate f v true) v.2.rev ≠ particle f v.2.rev := by
  intro he
  have hv := congrArg Fin.val he
  have hm := addable_positionNat hf hc
  simp only [particle_val] at hv
  omega

/-- New-state injectivity and unchanged other labels force actual old vacancy. -/
theorem new_vacant_of_single_label {M : Nat} (f g : Fin M × Fin M → Bool)
    (hg : Monotone g) (r₀ : Fin M)
    (hother : ∀ r : Fin M, r ≠ r₀ → particle g r = particle f r)
    (hne : particle g r₀ ≠ particle f r₀) : particle g r₀ ∉ particles f := by
  intro hm
  obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hm
  by_cases he : r = r₀
  · subst r
    exact hne hr.symm
  · have hnew : particle g r = particle g r₀ := (hother r he).trans hr
    exact he (particle_injective hg hnew)

/-- The right destination is vacant before the actual flip, not a premise. -/
theorem removable_new_vacant {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.removable f v) :
    particle (MixedSquareModel.cellUpdate f v false) v.2.rev ∉ particles f :=
  new_vacant_of_single_label f _ (MixedSquareCorners.cellUpdate_monotone hf v false) v.2.rev
    (particle_cellUpdate_other f v false) (removable_new_ne_old hf hc)

/-- The left destination is vacant before the actual flip, not a premise. -/
theorem addable_new_vacant {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.addable f v) :
    particle (MixedSquareModel.cellUpdate f v true) v.2.rev ∉ particles f :=
  new_vacant_of_single_label f _ (MixedSquareCorners.cellUpdate_monotone hf v true) v.2.rev
    (particle_cellUpdate_other f v true) (addable_new_ne_old hf hc)

/-- A single changed label has exactly the stated effect on its occupied set. -/
theorem particles_eq_insert_erase_of_single_label {M : Nat} (f g : Fin M × Fin M → Bool)
    (hf : Monotone f) (r₀ : Fin M)
    (hother : ∀ r : Fin M, r ≠ r₀ → particle g r = particle f r) :
    particles g = insert (particle g r₀) ((particles f).erase (particle f r₀)) := by
  ext s
  simp only [particles,Finset.mem_insert,Finset.mem_erase,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨r,hr⟩
    by_cases he : r = r₀
    · subst r
      exact Or.inl hr.symm
    · have hold : particle f r = s := (hother r he).symm.trans hr
      exact Or.inr ⟨fun hs => he (particle_injective hf (hold.trans hs)),r,hold⟩
  · rintro (hs | ⟨hs,r,hr⟩)
    · exact ⟨r₀,hs.symm⟩
    · have he : r ≠ r₀ := by
        intro he
        subst r
        exact hs hr.symm
      exact ⟨r,(hother r he).trans hr⟩

theorem removable_particles_eq_insert_erase {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (_hc : MixedSquareCorners.removable f v) :
    particles (MixedSquareModel.cellUpdate f v false) =
      insert (particle (MixedSquareModel.cellUpdate f v false) v.2.rev)
        ((particles f).erase (particle f v.2.rev)) :=
  particles_eq_insert_erase_of_single_label f _ hf v.2.rev (particle_cellUpdate_other f v false)

theorem addable_particles_eq_insert_erase {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (_hc : MixedSquareCorners.addable f v) :
    particles (MixedSquareModel.cellUpdate f v true) =
      insert (particle (MixedSquareModel.cellUpdate f v true) v.2.rev)
        ((particles f).erase (particle f v.2.rev)) :=
  particles_eq_insert_erase_of_single_label f _ hf v.2.rev (particle_cellUpdate_other f v true)


/-- The labelled right-half count equals the number of occupied right slots. -/
theorem rightCount_eq_rightSlotCard {M : Nat} {f : Fin M × Fin M → Bool} (hf : Monotone f) :
    rightCount f = ((particles f).filter (fun s : Fin (2*M) => M ≤ s.val)).card := by
  unfold rightCount
  apply Finset.card_bij (fun r _ => particle f r)
  · intro r hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩,?_⟩
    exact (Finset.mem_filter.mp hr).2
  · intro r hr t ht he
    exact particle_injective hf he
  · intro s hs
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
    refine ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hr⟩
    have hpos := (Finset.mem_filter.mp hs).2
    rw [←hr] at hpos
    exact hpos

/-- Swapping an occupied slot with a vacant one is precisely erase then insert. -/
theorem finset_image_swap {α : Type*} [DecidableEq α] (S : Finset α) (a b : α)
    (ha : a ∈ S) (hb : b ∉ S) :
    S.image (Equiv.swap a b) = insert b (S.erase a) := by
  have hba : b ≠ a := fun h => hb (h.symm ▸ ha)
  have he := Equiv.image_swap_of_mem_of_notMem (s := (S : Set α)) ha hb
  apply Finset.coe_injective
  rw [Finset.coe_image,he]
  ext s
  by_cases hs : s = a
  · subst s
    simp [Ne.symm hba]
  · simp [hs]

/-- The actual right corner flip is a swap of adjacent occupied/vacant slots. -/
theorem removable_particles_eq_image_swap {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.removable f v) :
    particles (MixedSquareModel.cellUpdate f v false) =
      (particles f).image (Equiv.swap (particle f v.2.rev)
        (particle (MixedSquareModel.cellUpdate f v false) v.2.rev)) := by
  rw [removable_particles_eq_insert_erase hf hc]
  exact (finset_image_swap _ _ _
    (Finset.mem_image.mpr ⟨v.2.rev,Finset.mem_univ _,rfl⟩)
    (removable_new_vacant hf hc)).symm

/-- The actual left corner flip is a swap of adjacent occupied/vacant slots. -/
theorem addable_particles_eq_image_swap {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : MixedSquareCorners.addable f v) :
    particles (MixedSquareModel.cellUpdate f v true) =
      (particles f).image (Equiv.swap (particle f v.2.rev)
        (particle (MixedSquareModel.cellUpdate f v true) v.2.rev)) := by
  rw [addable_particles_eq_insert_erase hf hc]
  exact (finset_image_swap _ _ _
    (Finset.mem_image.mpr ⟨v.2.rev,Finset.mem_univ _,rfl⟩)
    (addable_new_vacant hf hc)).symm

end MathResearchAnalysis.YoungParticleMoves


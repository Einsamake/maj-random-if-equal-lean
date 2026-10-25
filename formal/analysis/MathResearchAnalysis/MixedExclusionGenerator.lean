module

public import MathResearchAnalysis.YoungParticleHops
public import MathResearchAnalysis.YoungParticleMoves
public import MathResearchAnalysis.FiniteExclusionGenerator
public import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Exact finite mixed-square generator under the actual particle encoding

Every unequal adjacent path bond is counted exactly once, through a unique
actual mixed corner. The original fair two-mark single-cell generator thus
has coefficient one half per bond. This is finite generator algebra only:
no process law, compensator, moment ODE or time bound is asserted.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.MixedExclusionGenerator

open scoped BigOperators
open YoungParticles
open MixedSquareCorners (removable addable)
open FiniteExclusionGenerator (swapConfig generator)

abbrev Slot (n : Nat) := Fin (2*(n+2))

def slotState {n : Nat} (f : SquareSpin.Config n) : Slot n → Bool :=
  fun s => decide (s ∈ particles f)

def pathEdges (n : Nat) : Finset (Slot n × Slot n) :=
  Finset.univ.filter (fun e => e.1.val+1 = e.2.val)

def active {n : Nat} (f : SquareSpin.Config n) (v : SquareTasks.Vertex n) : Prop :=
  removable f v ∨ addable f v

instance active_decidable {n : Nat} (f : SquareSpin.Config n) (v : SquareTasks.Vertex n) : Decidable (active f v) := by
  unfold active removable addable
  infer_instance

def corners {n : Nat} (f : SquareSpin.Config n) : Finset (SquareTasks.Vertex n) := by
  classical
  exact Finset.univ.filter (active f)

/-- The bond is always oriented left to right, whichever corner is active. -/
def bond {n : Nat} (f : SquareSpin.Config n) (v : SquareTasks.Vertex n) : Slot n × Slot n :=
  if f v then
    (particle f v.2.rev,particle (MixedSquareModel.cellUpdate f v false) v.2.rev)
  else
    (particle (MixedSquareModel.cellUpdate f v true) v.2.rev,particle f v.2.rev)

def unequalEdges {n : Nat} (f : SquareSpin.Config n) : Finset (Slot n × Slot n) :=
  (pathEdges n).filter (fun e => slotState f e.1 ≠ slotState f e.2)

@[simp] theorem slotState_true_iff {n : Nat} (f : SquareSpin.Config n) (s : Slot n) :
    slotState f s = true ↔ s ∈ particles f := by simp [slotState]

@[simp] theorem slotState_false_iff {n : Nat} (f : SquareSpin.Config n) (s : Slot n) :
    slotState f s = false ↔ s ∉ particles f := by simp [slotState]

theorem old_particle_mem {n : Nat} (f : SquareSpin.Config n) (r : Fin (n+2)) :
    particle f r ∈ particles f := Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩

theorem slotState_eq_swap_of_particles {n : Nat} (f g : SquareSpin.Config n) (a b : Slot n)
    (h : particles g = (particles f).image (Equiv.swap a b)) :
    slotState g = swapConfig (slotState f) a b := by
  funext s
  apply Bool.decide_congr
  rw [h]
  constructor
  · rintro hs
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hs
    have he' : t = Equiv.swap a b s := by
      simpa only [Equiv.swap_apply_self] using congrArg (Equiv.swap a b) he
    exact he' ▸ ht
  · intro hs
    exact Finset.mem_image.mpr ⟨Equiv.swap a b s,hs,Equiv.swap_apply_self a b s⟩

theorem bond_of_removable {n : Nat} {f : SquareSpin.Config n} {v : SquareTasks.Vertex n}
    (hc : removable f v) : bond f v =
      (particle f v.2.rev,particle (MixedSquareModel.cellUpdate f v false) v.2.rev) := by
  simp [bond,hc.1]

theorem bond_of_addable {n : Nat} {f : SquareSpin.Config n} {v : SquareTasks.Vertex n}
    (hc : addable f v) : bond f v =
      (particle (MixedSquareModel.cellUpdate f v true) v.2.rev,particle f v.2.rev) := by
  simp [bond,hc.1]

/-- Each actual corner maps to one existing unequal adjacent path bond. -/
theorem bond_mem_unequalEdges {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : active f v) : bond f v ∈ unequalEdges f := by
  classical
  rcases hc with hc | hc
  · rw [bond_of_removable hc]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · exact (YoungParticleMoves.removable_positionNat hf hc).symm
    · have ho := (slotState_true_iff f _).mpr (old_particle_mem f v.2.rev)
      have hn := (slotState_false_iff f _).mpr (YoungParticleMoves.removable_new_vacant hf hc)
      rw [ho,hn]
      decide
  · rw [bond_of_addable hc]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · exact YoungParticleMoves.addable_positionNat hf hc
    · have hn := (slotState_false_iff f _).mpr (YoungParticleMoves.addable_new_vacant hf hc)
      have ho := (slotState_true_iff f _).mpr (old_particle_mem f v.2.rev)
      rw [hn,ho]
      decide

theorem removable_eq_of_row_eq {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v w : SquareTasks.Vertex n} (hv : removable f v) (hw : removable f w) (hy : v.2 = w.2) : v = w := by
  apply Prod.ext
  · apply Fin.ext
    have hvx := YoungRowUpdates.removable_x_eq_rowLength hf hv
    have hwx := YoungRowUpdates.removable_x_eq_rowLength hf hw
    rw [hy] at hvx
    omega
  · exact hy

theorem addable_eq_of_row_eq {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v w : SquareTasks.Vertex n} (hv : addable f v) (hw : addable f w) (hy : v.2 = w.2) : v = w := by
  apply Prod.ext
  · apply Fin.ext
    have hvx := YoungRowUpdates.addable_x_succ_eq_rowLength hf hv
    have hwx := YoungRowUpdates.addable_x_succ_eq_rowLength hf hw
    rw [hy] at hvx
    omega
  · exact hy

/-- No two distinct actual corners pay for the same unequal bond. -/
theorem bond_injective_on_corners {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v w : SquareTasks.Vertex n} (hv : active f v) (hw : active f w)
    (he : bond f v = bond f w) : v = w := by
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · rw [bond_of_removable hv,bond_of_removable hw] at he
    have hold := congrArg Prod.fst he
    have hlabel := particle_injective hf hold
    exact removable_eq_of_row_eq hf hv hw (Fin.rev_injective hlabel)
  · rw [bond_of_removable hv,bond_of_addable hw] at he
    have hold := congrArg Prod.fst he
    exact False.elim (YoungParticleMoves.addable_new_vacant hf hw (Eq.mp (congrArg (fun s : Slot n => s ∈ particles f) hold) (old_particle_mem f v.2.rev)))
  · rw [bond_of_addable hv,bond_of_removable hw] at he
    have hold := congrArg Prod.snd he
    exact False.elim (YoungParticleMoves.removable_new_vacant hf hw (Eq.mp (congrArg (fun s : Slot n => s ∈ particles f) hold) (old_particle_mem f v.2.rev)))
  · rw [bond_of_addable hv,bond_of_addable hw] at he
    have hold := congrArg Prod.snd he
    have hlabel := particle_injective hf hold
    exact addable_eq_of_row_eq hf hv hw (Fin.rev_injective hlabel)

/-- Every unequal adjacent bond is covered by an actual corner, in the correct orientation. -/
theorem bond_surjective_unequalEdges {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (e : Slot n × Slot n) (he : e ∈ unequalEdges f) :
    ∃ v : SquareTasks.Vertex n, v ∈ corners f ∧ bond f v = e := by
  classical
  have hE := (Finset.mem_filter.mp he).1
  have hneq := (Finset.mem_filter.mp he).2
  have hadj := (Finset.mem_filter.mp hE).2
  by_cases hleft : slotState f e.1 = true
  · have hright : slotState f e.2 = false := by
      cases hr : slotState f e.2 <;> simp_all
    have hold := (slotState_true_iff f _).mp hleft
    have hvac := (slotState_false_iff f _).mp hright
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hold
    have hrval := congrArg Fin.val hr
    simp only [particle_val] at hrval
    have hend : positionNat f r+1 < 2*(n+2) := by have h := e.2.isLt; omega
    have hfree : ∀ s : Fin (n+2), positionNat f s ≠ positionNat f r+1 := by
      intro s hs
      apply hvac
      apply Finset.mem_image.mpr
      refine ⟨s,Finset.mem_univ _,?_⟩
      apply Fin.ext
      simp only [particle_val]
      omega
    obtain ⟨v,hy,hx,hc⟩ := YoungParticleHops.right_hop_has_removable hf r hend hfree
    have ha : particle f v.2.rev = e.1 := by rw [hy,Fin.rev_rev]; exact hr
    have hb : particle (MixedSquareModel.cellUpdate f v false) v.2.rev = e.2 := by
      apply Fin.ext
      have hm := YoungParticleMoves.removable_positionNat hf hc
      have haval := congrArg Fin.val ha
      simp only [particle_val] at haval ⊢
      omega
    refine ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl hc⟩,?_⟩
    rw [bond_of_removable hc,ha,hb]
  · have hleft' : slotState f e.1 = false := by cases hl : slotState f e.1 <;> simp_all
    have hright : slotState f e.2 = true := by cases hr : slotState f e.2 <;> simp_all
    have hold := (slotState_true_iff f _).mp hright
    have hvac := (slotState_false_iff f _).mp hleft'
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hold
    have hrval := congrArg Fin.val hr
    simp only [particle_val] at hrval
    have hstart : 0 < positionNat f r := by omega
    have hfree : ∀ s : Fin (n+2), positionNat f s+1 ≠ positionNat f r := by
      intro s hs
      apply hvac
      apply Finset.mem_image.mpr
      refine ⟨s,Finset.mem_univ _,?_⟩
      apply Fin.ext
      simp only [particle_val]
      omega
    obtain ⟨v,hy,hx,hc⟩ := YoungParticleHops.left_hop_has_addable hf r hstart hfree
    have hb : particle f v.2.rev = e.2 := by rw [hy,Fin.rev_rev]; exact hr
    have ha : particle (MixedSquareModel.cellUpdate f v true) v.2.rev = e.1 := by
      apply Fin.ext
      have hm := YoungParticleMoves.addable_positionNat hf hc
      have hbval := congrArg Fin.val hb
      simp only [particle_val] at hbval ⊢
      omega
    refine ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr hc⟩,?_⟩
    rw [bond_of_addable hc,ha,hb]

/-- The old spin as tie mark leaves a monotone region unchanged. -/
theorem cellUpdate_same_mark {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (v : SquareTasks.Vertex n) : MixedSquareModel.cellUpdate f v (f v) = f := by
  have hval : MixedSquareModel.cellUpdate f v (f v) v = f v := by
    by_contra hn
    rcases (MixedSquareCorners.cellUpdate_changes_iff hf v (f v)).mp hn with h | h
    · exact Bool.noConfusion (h.1.1.symm.trans h.2)
    · exact Bool.noConfusion (h.1.1.symm.trans h.2)
  funext u
  by_cases hu : u = v
  · subst u
    exact hval
  · exact MixedSquareModel.cellUpdate_other f v u (f v) hu

theorem cellUpdate_eq_of_inactive {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (v : SquareTasks.Vertex n) (tie : Bool) (hn : ¬ active f v) : MixedSquareModel.cellUpdate f v tie = f := by
  have hval : MixedSquareModel.cellUpdate f v tie v = f v := by
    by_contra hne
    rcases (MixedSquareCorners.cellUpdate_changes_iff hf v tie).mp hne with h | h
    · exact hn (Or.inl h.1)
    · exact hn (Or.inr h.1)
  funext u
  by_cases hu : u = v
  · subst u
    exact hval
  · exact MixedSquareModel.cellUpdate_other f v u tie hu

/-- The changing mark is the actual pullback by the unique active bond swap. -/
theorem active_slotState_update {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    {v : SquareTasks.Vertex n} (hc : active f v) :
    slotState (MixedSquareModel.cellUpdate f v (! f v)) =
      swapConfig (slotState f) (bond f v).1 (bond f v).2 := by
  rcases hc with hc | hc
  · simp only [hc.1,Bool.not_true,bond_of_removable hc]
    exact slotState_eq_swap_of_particles f _ _ _ (YoungParticleMoves.removable_particles_eq_image_swap hf hc)
  · simp only [hc.1,Bool.not_false,bond_of_addable hc]
    have h := slotState_eq_swap_of_particles f _ _ _ (YoungParticleMoves.addable_particles_eq_image_swap hf hc)
    simpa only [swapConfig,Equiv.swap_comm] using h

/-- The fair two-mark contribution is zero or exactly one half of the actual swap difference. -/
theorem local_fair_contribution {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (F : (Slot n → Bool) → Real) (v : SquareTasks.Vertex n) :
    (F (slotState (MixedSquareModel.cellUpdate f v false))+
      F (slotState (MixedSquareModel.cellUpdate f v true)))/2-F (slotState f) =
      if active f v then (F (swapConfig (slotState f) (bond f v).1 (bond f v).2)-F (slotState f))/2 else 0 := by
  classical
  by_cases hc : active f v
  · rw [ite_eq_left hc]
    have hswap := active_slotState_update hf hc
    have hstay := cellUpdate_same_mark hf v
    cases hv : f v
    · simp only [hv,Bool.not_false] at hswap hstay
      rw [hstay,hswap]
      ring
    · simp only [hv,Bool.not_true] at hswap hstay
      rw [hstay,hswap]
      ring
  · rw [ite_eq_right hc,cellUpdate_eq_of_inactive hf v false hc,cellUpdate_eq_of_inactive hf v true hc]
    ring

/-- The genuine mixed cell generator is the finite path exclusion generator,
with exactly one listing and rate one half per adjacent bond. -/
theorem actual_generator_eq_exclusion {n : Nat} {f : SquareSpin.Config n} (hf : Monotone f)
    (F : (Slot n → Bool) → Real) :
    (∑ v : SquareTasks.Vertex n,
      ((F (slotState (MixedSquareModel.cellUpdate f v false))+
        F (slotState (MixedSquareModel.cellUpdate f v true)))/2-F (slotState f))) =
      generator (pathEdges n) F (slotState f) := by
  classical
  have hc : (∑ v : SquareTasks.Vertex n,
      ((F (slotState (MixedSquareModel.cellUpdate f v false))+
        F (slotState (MixedSquareModel.cellUpdate f v true)))/2-F (slotState f))) =
      ∑ v ∈ corners f, (F (swapConfig (slotState f) (bond f v).1 (bond f v).2)-F (slotState f))/2 := by
    unfold corners
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    exact local_fair_contribution hf F v
  have hb : (∑ v ∈ corners f,
      (F (swapConfig (slotState f) (bond f v).1 (bond f v).2)-F (slotState f))/2) =
      ∑ e ∈ unequalEdges f, (F (swapConfig (slotState f) e.1 e.2)-F (slotState f))/2 := by
    apply Finset.sum_bij (fun v _ => bond f v)
    · intro v hv
      exact bond_mem_unequalEdges hf (Finset.mem_filter.mp hv).2
    · intro v hv w hw he
      exact bond_injective_on_corners hf (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2 he
    · intro e he
      obtain ⟨v,hv,heq⟩ := bond_surjective_unequalEdges hf e he
      exact ⟨v,hv,heq⟩
    · intro v hv
      rfl
  have hu : generator (pathEdges n) F (slotState f) =
      ∑ e ∈ unequalEdges f, (F (swapConfig (slotState f) e.1 e.2)-F (slotState f))/2 := by
    unfold generator unequalEdges
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hne : slotState f e.1 ≠ slotState f e.2
    · rw [ite_eq_left hne]
    · rw [ite_eq_right hne]
      have heq : slotState f e.1 = slotState f e.2 := not_not.mp hne
      have hswap : swapConfig (slotState f) e.1 e.2 = slotState f :=
        funext (Equiv.apply_swap_eq_self heq)
      rw [hswap]
      ring
  exact hc.trans (hb.trans hu.symm)

end MathResearchAnalysis.MixedExclusionGenerator



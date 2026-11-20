module
public import EarliestAtom
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.ForcedCorners
open MathResearchAnalysis InfiniteGridModel MeasureTheory
open PerturbationSymmetry (squareConfig)
open Earliest (margin depth lastRound survives_to_depth)
open scoped ENNReal

def coord (N : ℕ) (b : Bool) (x : ℤ) := if b then (N : ℤ)-1-x else x
def site (N : ℕ) (b c : Bool) (x y : ℤ) : Site := (coord N b x,coord N c y)
abbrev state (N : ℕ) (η : InfiniteGridRandomDynamics.Sample) (t : ℕ) :=
  InfiniteGridRandomDynamics.synchronous (squareConfig N) t η

private theorem reflected_step (N : ℕ) (η : InfiniteGridRandomDynamics.Sample) (b c : Bool) (t : ℕ) (x y : ℤ) :
    state N η (t+1) (site N b c x y) = majority4
      (state N η t (site N b c x (y+1))) (state N η t (site N b c (x+1) y))
      (state N η t (site N b c x (y-1))) (state N η t (site N b c (x-1) y))
      (η (site N b c x y,t+1)) := by
  change update _ _ _ _ = _
  cases b <;> cases c <;> simp [update,site,coord,north,south,east,west,InfiniteGridRandomDynamics.marks,
    majority4,sub_eq_add_neg,add_comm,add_left_comm,add_assoc,state,InfiniteGridRandomDynamics.synchronous]

def gone (N : ℕ) (η : InfiniteGridRandomDynamics.Sample) (b c : Bool) (x y : ℕ) :=
  state N η (x+y+1) (site N b c x y) = false

private theorem inward_depth {N h x y : ℕ} (hn : 2*h ≤ N) (hx : x<h) (hy : y<h) (b c : Bool) :
    (Inside N (site N b c x ((y:ℤ)+1)) ∧ (x+y : ℕ) ≤ depth N (site N b c x ((y:ℤ)+1))) ∧
    (Inside N (site N b c ((x:ℤ)+1) y) ∧ (x+y : ℕ) ≤ depth N (site N b c ((x:ℤ)+1) y)) := by
  cases b <;> cases c <;> dsimp [Inside,site,coord,depth,margin] <;> omega

private theorem two_force : ∀ s w z : Bool, majority4 true true s w z = false → z=false ∧ s=false ∧ w=false := by decide

theorem force_step {N h x y : ℕ} {η : InfiniteGridRandomDynamics.Sample} {b c : Bool}
    (hn : 2*h ≤ N) (hx : x<h) (hy : y<h) (hg : gone N η b c x y) :
    η (site N b c x y,x+y+1) = false ∧
    state N η (x+y) (site N b c x ((y : ℤ)-1)) = false ∧
    state N η (x+y) (site N b c ((x : ℤ)-1) y) = false := by
  unfold gone at hg
  rw [reflected_step] at hg
  obtain ⟨⟨hnin,hnd⟩,⟨hein,hed⟩⟩ := inward_depth hn hx hy b c
  rw [show state N η (x+y) (site N b c x ((y:ℤ)+1)) = true from survives_to_depth N _ _ _ hnin hnd,
    show state N η (x+y) (site N b c ((x:ℤ)+1) y) = true from survives_to_depth N _ _ _ hein hed] at hg
  exact two_force _ _ _ hg

theorem force_rectangle {N h I J : ℕ} {η : InfiniteGridRandomDynamics.Sample} {b c : Bool}
    (hn : 2*h ≤ N) (hi : I<h) (hj : J<h) (hg : gone N η b c I J)
    {x y : ℕ} (hx : x ≤ I) (hy : y ≤ J) : η (site N b c x y,x+y+1) = false := by
  have row : gone N η b c x J := by
    induction I,hx using Nat.le_induction with
    | base => exact hg
    | succ i hxi ih =>
      apply ih (by omega)
      have a := (force_step hn hi hj hg).2.2
      simpa [gone,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a
  have col : gone N η b c x y := by
    clear hg
    induction J,hy using Nat.le_induction with
    | base => exact row
    | succ j hyj ih =>
      apply ih (by omega)
      have a := (force_step hn (by omega : x<h) hj row).2.1
      simpa [gone,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a
  exact (force_step hn (by omega : x<h) (by omega : y<h) col).1

def quadrantMarks (N h : ℕ) (b c : Bool) : Finset InfiniteGridRandomDynamics.Event :=
  ((Finset.range h) ×ˢ (Finset.range h)).image (fun p => (site N b c p.1 p.2,p.1+p.2+1))

theorem quadrant_card (N h : ℕ) (b c : Bool) : (quadrantMarks N h b c).card = h^2 := by
  unfold quadrantMarks
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_product,pow_two]
  · rintro ⟨x,y⟩ ⟨u,v⟩ he
    have he1 := congrArg (fun e : InfiniteGridRandomDynamics.Event => e.1.1) he
    have he2 := congrArg (fun e : InfiniteGridRandomDynamics.Event => e.1.2) he
    cases b <;> cases c <;> dsimp [site,coord] at he1 he2 <;> congr 1 <;> omega

def allZero (s : Finset InfiniteGridRandomDynamics.Event) : Set InfiniteGridRandomDynamics.Sample :=
  Set.pi (s : Set InfiniteGridRandomDynamics.Event) (fun _ => {false})

theorem zero_mass (s : Finset InfiniteGridRandomDynamics.Event) :
    InfiniteGridRandomDynamics.measure (allZero s) = ((2 : ℝ≥0∞)⁻¹)^s.card := by
  unfold InfiniteGridRandomDynamics.measure FairMarks.markMeasure allZero
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [FairMarks.fair_singleton]

theorem tip_forces_quadrant {N l : ℕ} {η : InfiniteGridRandomDynamics.Sample} {b c : Bool}
    (hn : 2*(l+1) ≤ N) (hg : gone N η b c l l) : η ∈ allZero (quadrantMarks N (l+1) b c) := by
  intro e he
  obtain ⟨⟨x,y⟩,hp,rfl⟩ := Finset.mem_image.mp he
  have hx := Finset.mem_range.mp (Finset.mem_product.mp hp).1
  have hy := Finset.mem_range.mp (Finset.mem_product.mp hp).2
  exact force_rectangle hn (by omega : l<l+1) (by omega : l<l+1) hg (by omega : x≤l) (by omega : y≤l)

end MathResearchLower.ForcedCorners

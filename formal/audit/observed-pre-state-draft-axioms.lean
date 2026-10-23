module
public import MathResearchAnalysis.ObservedFrozenProcess
public import MathResearchAnalysis.PredictableClockSigma
public import MathResearchAnalysis.ProtectedAreaPotential
set_option autoImplicit false
/-! A representative of the state immediately before physical time. Its graph
is defined using only rational observations strictly before time. The graph is
predictable and single-valued on every sample, including exceptional samples.
No claim connecting it with actual event words is assumed here. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ObservedPreState
open MeasureTheory Set
open DropletClockLaw (Sample Event)
open InfiniteGridModel (Site)

def graph (L : Nat) (D I S T : Finset Site) : Set (NNReal × Sample L) :=
  {p | ∃ q : Rat, 0 ≤ q ∧ (q : Real) < (p.1 : Real) ∧
    ∀ r : Rat, q < r → (r : Real) < (p.1 : Real) →
      ObservedFrozenProcess.state L D I S (r : Real) p.2 = T}

theorem rational_future_eq (L : Nat) (q : Rat) (hq : 0 ≤ q)
    (E : Set (Sample L)) :
    {p : NNReal × Sample L | (q : Real) < (p.1 : Real) ∧ p.2 ∈ E} =
      Ioi (Real.toNNReal (q : Real)) ×ˢ E := by
  ext p
  simp only [mem_ofPred_eq, mem_prod, mem_Ioi]
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by exact_mod_cast hq)]

theorem rational_future_measurable (L : Nat) (D I S T : Finset Site)
    (r : Rat) (hr : 0 ≤ r) :
    MeasurableSet[(RationalProtectedExit.nnHistory L).predictable]
      {p : NNReal × Sample L | (r : Real) < (p.1 : Real) ∧
        ObservedFrozenProcess.state L D I S (r : Real) p.2 ≠ T} := by
  change MeasurableSet[(RationalProtectedExit.nnHistory L).predictable]
    {p : NNReal × Sample L | (r : Real) < (p.1 : Real) ∧
      p.2 ∈ {z : Sample L | ObservedFrozenProcess.state L D I S (r : Real) z ≠ T}}
  rw [rational_future_eq L r hr]
  apply measurableSet_predictable_Ioi_prod
  change MeasurableSet[MarkedClockFiltration.history L (Real.toNNReal (r : Real) : Real)]
    {z : Sample L | ObservedFrozenProcess.state L D I S (r : Real) z ≠ T}
  rw [Real.coe_toNNReal _ (by exact_mod_cast hr)]
  exact (ObservedFrozenProcess.state_fiber_measurable L D I S (r : Real) T).compl

theorem graph_measurable (L : Nat) (D I S T : Finset Site) :
    MeasurableSet[(RationalProtectedExit.nnHistory L).predictable] (graph L D I S T) := by
  classical
  let : MeasurableSpace (NNReal × Sample L) := (RationalProtectedExit.nnHistory L).predictable
  have heq : graph L D I S T = ⋃ q : Rat, ⋃ hq : 0 ≤ q,
      (Ioi (Real.toNNReal (q : Real)) ×ˢ (univ : Set (Sample L))) ∩
      ⋂ r : Rat, if q < r then
        {p : NNReal × Sample L | (r : Real) < (p.1 : Real) ∧
          ObservedFrozenProcess.state L D I S (r : Real) p.2 ≠ T}ᶜ else univ := by
    ext p
    simp only [graph,mem_ofPred_eq,mem_iUnion,mem_inter_iff,mem_prod,mem_univ,and_true,
      mem_Ioi,mem_iInter]
    constructor
    · rintro ⟨q,hq,hqt,hstate⟩
      refine ⟨q,hq,?_,?_⟩
      · rw [← NNReal.coe_lt_coe,Real.coe_toNNReal _ (by exact_mod_cast hq)]
        exact hqt
      · intro r
        by_cases hqr : q < r
        · simp only [hqr,ite_true,mem_compl_iff,mem_ofPred_eq]
          rintro ⟨hrt,hne⟩
          exact hne (hstate r hqr hrt)
        · simp only [hqr,ite_false,mem_univ]
    · rintro ⟨q,hq,hqt,hstate⟩
      refine ⟨q,hq,?_,?_⟩
      · rw [← NNReal.coe_lt_coe,Real.coe_toNNReal _ (by exact_mod_cast hq)] at hqt
        exact hqt
      · intro r hqr hrt
        have hs := hstate r
        simp only [hqr,ite_true,mem_compl_iff,mem_ofPred_eq] at hs
        by_contra hne
        exact hs ⟨hrt,hne⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro hq
  apply (measurableSet_predictable_Ioi_prod (𝓕 := RationalProtectedExit.nnHistory L)
    (i := Real.toNNReal (q : Real)) MeasurableSet.univ).inter
  apply MeasurableSet.iInter
  intro r
  split_ifs with hqr
  · exact (rational_future_measurable L D I S T r (le_trans hq (le_of_lt hqr))).compl
  · exact MeasurableSet.univ

theorem graph_unique (L : Nat) (D I S : Finset Site) (t : NNReal) (z : Sample L)
    (T U : Finset Site) (hT : (t,z) ∈ graph L D I S T)
    (hU : (t,z) ∈ graph L D I S U) : T = U := by
  rcases hT with ⟨q,hq,hqt,hT⟩
  rcases hU with ⟨s,hs,hst,hU⟩
  obtain ⟨r,hr,hrt⟩ := exists_rat_btwn (max_lt hqt hst)
  have hqr : q < r := by exact_mod_cast lt_of_le_of_lt (le_max_left (q : Real) (s : Real)) hr
  have hsr : s < r := by exact_mod_cast lt_of_le_of_lt (le_max_right (q : Real) (s : Real)) hr
  exact (hT r hqr hrt).symm.trans (hU r hsr hrt)

def beforeState (L : Nat) (D I S : Finset Site) (t : NNReal) (z : Sample L) : Finset Site := by
  classical
  exact if h : ∃ T, (t,z) ∈ graph L D I S T then h.choose else S

theorem state_eq_of_graph (L : Nat) (D I S : Finset Site) (t : NNReal) (z : Sample L)
    (T : Finset Site) (hT : (t,z) ∈ graph L D I S T) : beforeState L D I S t z = T := by
  classical
  have hex : ∃ U, (t,z) ∈ graph L D I S U := ⟨T,hT⟩
  simp only [beforeState,dite_eq_left hex]
  exact graph_unique L D I S t z _ T hex.choose_spec hT

theorem state_eq_iff (L : Nat) (D I S : Finset Site) (t : NNReal) (z : Sample L) (T : Finset Site) :
    beforeState L D I S t z = T ↔ (t,z) ∈ graph L D I S T ∨
      (¬ (∃ U, (t,z) ∈ graph L D I S U)) ∧ S = T := by
  classical
  by_cases hex : ∃ U, (t,z) ∈ graph L D I S U
  · have hg : (t,z) ∈ graph L D I S (beforeState L D I S t z) := by
      simpa only [beforeState,dite_eq_left hex] using hex.choose_spec
    exact ⟨fun h => Or.inl (h ▸ hg),fun h => h.elim
      (state_eq_of_graph L D I S t z T) (fun h => False.elim (h.1 hex))⟩
  · simp only [beforeState,dite_eq_right hex]
    constructor
    · exact fun h => Or.inr ⟨hex,h⟩
    · rintro (h | h)
      · exact False.elim (hex ⟨T,h⟩)
      · exact h.2

theorem state_fiber_measurable (L : Nat) (D I S T : Finset Site) :
    MeasurableSet[(RationalProtectedExit.nnHistory L).predictable]
      {p : NNReal × Sample L | beforeState L D I S p.1 p.2 = T} := by
  let : MeasurableSpace (NNReal × Sample L) := (RationalProtectedExit.nnHistory L).predictable
  have heq : {p : NNReal × Sample L | beforeState L D I S p.1 p.2 = T} = graph L D I S T ∪
      (⋃ U : Finset Site, graph L D I S U)ᶜ ∩ {p : NNReal × Sample L | S = T} := by
    ext p
    simp only [mem_ofPred_eq,state_eq_iff,mem_union,mem_inter_iff,mem_compl_iff,mem_iUnion]
  rw [heq]
  exact (graph_measurable L D I S T).union
    ((MeasurableSet.iUnion fun U => graph_measurable L D I S U).compl.inter (MeasurableSet.const _))

theorem state_measurable (L : Nat) (D I S : Finset Site) :
    @Measurable (NNReal × Sample L) (Finset Site) (RationalProtectedExit.nnHistory L).predictable
      ObservedFrozenProcess.stateSpace (fun p => beforeState L D I S p.1 p.2) := by
  let : MeasurableSpace (NNReal × Sample L) := (RationalProtectedExit.nnHistory L).predictable
  let : MeasurableSpace (Finset Site) := ObservedFrozenProcess.stateSpace
  exact measurable_to_countable' fun T => state_fiber_measurable L D I S T

theorem observable_measurable (L : Nat) (D I S : Finset Site)
    {α : Type*} [MeasurableSpace α] (f : Finset Site → α) :
    @Measurable (NNReal × Sample L) α (RationalProtectedExit.nnHistory L).predictable
      inferInstance (fun p => f (beforeState L D I S p.1 p.2)) := by
  let : MeasurableSpace (Finset Site) := ObservedFrozenProcess.stateSpace
  have hf : Measurable f := fun _ _ => trivial
  exact hf.comp (state_measurable L D I S)

theorem state_zero (L : Nat) (D I S : Finset Site) (z : Sample L) :
    beforeState L D I S 0 z = S := by
  classical
  have hnone : ¬ ∃ T, ((0 : NNReal),z) ∈ graph L D I S T := by
    rintro ⟨T,q,hq,hlt,hstate⟩
    have hqreal : (0 : Real) ≤ (q : Real) := by exact_mod_cast hq
    exact (not_lt_of_ge hqreal) hlt
  simp only [beforeState,dite_eq_right hnone]

theorem graph_supported (L : Nat) (D I : Finset Site) {S : Finset Site}
    (hS : S ⊆ D) (t : NNReal) (z : Sample L) (T : Finset Site)
    (hT : (t,z) ∈ graph L D I S T) : T ⊆ D := by
  rcases hT with ⟨q,hq,hqt,hstate⟩
  obtain ⟨r,hqr,hrt⟩ := exists_rat_btwn hqt
  have hqr' : q < r := by exact_mod_cast hqr
  rw [← hstate r hqr' hrt]
  exact ProtectedAreaPotential.observed_state_supported L hS (r : Real) z

theorem state_supported (L : Nat) (D I : Finset Site) {S : Finset Site}
    (hS : S ⊆ D) (t : NNReal) (z : Sample L) : beforeState L D I S t z ⊆ D := by
  classical
  by_cases hex : ∃ T, (t,z) ∈ graph L D I S T
  · exact graph_supported L D I hS t z _
      (by simpa only [beforeState,dite_eq_left hex] using hex.choose_spec)
  · simpa only [beforeState,dite_eq_right hex] using hS
end MathResearchAnalysis.ObservedPreState

#print axioms MathResearchAnalysis.ObservedPreState.graph
#print axioms MathResearchAnalysis.ObservedPreState.rational_future_eq
#print axioms MathResearchAnalysis.ObservedPreState.rational_future_measurable
#print axioms MathResearchAnalysis.ObservedPreState.graph_measurable
#print axioms MathResearchAnalysis.ObservedPreState.graph_unique
#print axioms MathResearchAnalysis.ObservedPreState.beforeState
#print axioms MathResearchAnalysis.ObservedPreState.state_eq_of_graph
#print axioms MathResearchAnalysis.ObservedPreState.state_eq_iff
#print axioms MathResearchAnalysis.ObservedPreState.state_fiber_measurable
#print axioms MathResearchAnalysis.ObservedPreState.state_measurable
#print axioms MathResearchAnalysis.ObservedPreState.observable_measurable
#print axioms MathResearchAnalysis.ObservedPreState.state_zero
#print axioms MathResearchAnalysis.ObservedPreState.graph_supported
#print axioms MathResearchAnalysis.ObservedPreState.state_supported

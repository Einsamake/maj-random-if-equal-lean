module
public import MathResearchAnalysis.GridPhysicalRegion
public import MathResearchAnalysis.OrthogonalGridConvexity
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Order.Basic
set_option autoImplicit false
/-! Next-stage topological connectivity from actual four-neighbour occupied paths.
This is not a Jordan-boundary or arc-length theorem. -/
@[expose] public section
namespace MathResearchAnalysis.GridRegionConnectivity
open GridCellBoundary (Site)
open InfiniteGridModel (north east south west)
open GridPhysicalRegion
open OrthogonalGridConvexity

theorem unitCell_isConnected (v : Site) : IsConnected (unitCell v) := by
  rw [unitCell_eq_prod]
  exact (isConnected_Icc (by linarith : (v.1 : Real)-1/2 ≤ (v.1 : Real)+1/2)).prod
    (isConnected_Icc (by linarith : (v.2 : Real)-1/2 ≤ (v.2 : Real)+1/2))

theorem neighbor_unitCells_inter_nonempty {v u : Site}
    (h : u ∈ GridMajorityPeeling.neighbors4 v) : (unitCell v ∩ unitCell u).Nonempty := by
  rcases (GridMajorityPeeling.mem_neighbors4 v u).mp h with rfl | rfl | rfl | rfl
  · refine ⟨((v.1 : Real),(v.2 : Real)+1/2),?_,?_⟩
    all_goals
      dsimp [unitCell,north]
      push_cast
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · refine ⟨((v.1 : Real)+1/2,(v.2 : Real)),?_,?_⟩
    all_goals
      dsimp [unitCell,east]
      push_cast
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · refine ⟨((v.1 : Real),(v.2 : Real)-1/2),?_,?_⟩
    all_goals
      dsimp [unitCell,south]
      push_cast
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · refine ⟨((v.1 : Real)-1/2,(v.2 : Real)),?_,?_⟩
    all_goals
      dsimp [unitCell,west]
      push_cast
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem unitRegion_isPreconnected {S : Finset Site} (hconn : FourConnected S) :
    IsPreconnected (unitRegion S) := by
  have hchain : ∀ u ∈ (S : Set Site), ∀ v ∈ (S : Set Site),
      Relation.ReflTransGen (fun a b : Site => (unitCell a ∩ unitCell b).Nonempty ∧ a ∈ (S : Set Site)) u v := by
    intro u hu v hv
    have hp := hconn u hu v hv
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact (ih hs.1).tail ⟨neighbor_unitCells_inter_nonempty hs.2.2,hs.1⟩
  exact IsPreconnected.biUnion_of_reflTransGen
    (fun v _ => (unitCell_isConnected v).isPreconnected) hchain

theorem unitRegion_isConnected {S : Finset Site} (hne : S.Nonempty) (hconn : FourConnected S) :
    IsConnected (unitRegion S) := by
  obtain ⟨v,hv⟩ := hne
  have hc : ((v.1 : Real),(v.2 : Real)) ∈ unitCell v := by
    dsimp [unitCell]
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  exact ⟨⟨_,(mem_unitRegion S _).mpr ⟨v,hv,hc⟩⟩,unitRegion_isPreconnected hconn⟩

end MathResearchAnalysis.GridRegionConnectivity

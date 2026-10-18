module

public import MathResearchAnalysis.ConvexLocalUpdate

set_option autoImplicit false

/-!
# Actual tie births preserve orthogonal interval convexity and stability

An empty site with degree two in a row- and column-convex set has one occupied
horizontal neighbour and one occupied vertical neighbour. Inserting this site
extends each affected integer interval by at most one. Every pre-existing
occupied vertex does not lose occupied neighbours, so a stable set stays stable and the actual
majority cleanup is the identity. Connectivity is proved using occupied grid
paths. No geometric Good invariant or probability estimate is assumed.
-/

@[expose] public section

namespace MathResearchAnalysis.ConvexBirthUpdate

open GridCellBoundary (Site)
open InfiniteGridModel (north east south west)
open GridMajorityPeeling (neighbors4 degree4 cleanup)
open OrthogonalGridConvexity
open DropletModifiedWord (Stable rawStep modifiedStep localRule)

/-- Filling a missing integer immediately adjacent to an interval keeps it an interval. -/
theorem int_interval_insert_of_adjacent {P : Int → Prop} {c : Int}
    (hconv : ∀ a b x : Int, P a → P b → a ≤ x → x ≤ b → P x)
    (hadj : P (c - 1) ∨ P (c + 1)) :
    ∀ a b x : Int, (a = c ∨ P a) → (b = c ∨ P b) →
      a ≤ x → x ≤ b → x = c ∨ P x := by
  intro a b x ha hb hax hxb
  by_cases hxc : x = c
  · exact Or.inl hxc
  · right
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · omega
    · rcases hadj with hadj | hadj
      · exact hconv (c - 1) b x hadj hb (by omega) hxb
      · exact hconv (c + 1) b x hadj hb (by omega) hxb
    · rcases hadj with hadj | hadj
      · exact hconv a (c - 1) x ha hadj hax (by omega)
      · exact hconv a (c + 1) x ha hadj hax (by omega)
    · exact hconv a b x ha hb hax hxb

theorem rowConvex_insert_of_horizontal {S : Finset Site} {v : Site}
    (hrow : RowConvex S) (hadj : east v ∈ S ∨ west v ∈ S) :
    RowConvex (insert v S) := by
  rcases v with ⟨vx, vy⟩
  intro a b x y ha hb hax hxb
  by_cases hy : y = vy
  · subst y
    have hp : (vx - 1, vy) ∈ S ∨ (vx + 1, vy) ∈ S := by
      simpa only [east, west, Or.comm] using hadj
    have hc := int_interval_insert_of_adjacent
      (P := fun q => (q, vy) ∈ S) (c := vx)
      (fun a b x ha hb hax hxb => hrow a b x vy ha hb hax hxb) hp
    simpa only [Finset.mem_insert, Prod.mk.injEq, and_true] using
      hc a b x (by simpa only [Finset.mem_insert, Prod.mk.injEq, and_true] using ha)
        (by simpa only [Finset.mem_insert, Prod.mk.injEq, and_true] using hb) hax hxb
  · have hne : ∀ q : Int, (q, y) ≠ (vx, vy) := by
      intro q h
      exact hy (congrArg Prod.snd h)
    simp only [Finset.mem_insert, hne, false_or] at ha hb ⊢
    exact hrow a b x y ha hb hax hxb

theorem columnConvex_insert_of_vertical {S : Finset Site} {v : Site}
    (hcol : ColumnConvex S) (hadj : north v ∈ S ∨ south v ∈ S) :
    ColumnConvex (insert v S) := by
  rcases v with ⟨vx, vy⟩
  intro x a b y ha hb hay hyb
  by_cases hx : x = vx
  · subst x
    have hp : (vx, vy - 1) ∈ S ∨ (vx, vy + 1) ∈ S := by
      simpa only [north, south, Or.comm] using hadj
    have hc := int_interval_insert_of_adjacent
      (P := fun q => (vx, q) ∈ S) (c := vy)
      (fun a b y ha hb hay hyb => hcol vx a b y ha hb hay hyb) hp
    simpa only [Finset.mem_insert, Prod.mk.injEq, true_and] using
      hc a b y (by simpa only [Finset.mem_insert, Prod.mk.injEq, true_and] using ha)
        (by simpa only [Finset.mem_insert, Prod.mk.injEq, true_and] using hb) hay hyb
  · have hne : ∀ q : Int, (x, q) ≠ (vx, vy) := by
      intro q h
      exact hx (congrArg Prod.fst h)
    simp only [Finset.mem_insert, hne, false_or] at ha hb ⊢
    exact hcol x a b y ha hb hay hyb

theorem vacant_degree_two_orthogonal_neighbors {S : Finset Site} {v : Site}
    (hrow : RowConvex S) (hcol : ColumnConvex S) (hv : v ∉ S)
    (hdeg : degree4 S v = 2) :
    (east v ∈ S ∨ west v ∈ S) ∧ (north v ∈ S ∨ south v ∈ S) := by
  have hns := ConvexLocalUpdate.vacant_no_north_south hcol hv
  have hew := ConvexLocalUpdate.vacant_no_east_west hrow hv
  rw [GridMajorityPeeling.degree4_eq_four_inputs] at hdeg
  by_cases hn : north v ∈ S <;> by_cases he : east v ∈ S <;>
    by_cases hs : south v ∈ S <;> by_cases hw : west v ∈ S
  all_goals simp_all [GridMajorityPeeling.state]

theorem stable_insert_of_degree_ge_two {S : Finset Site} {v : Site}
    (hst : Stable S) (hdeg : 2 ≤ degree4 S v) : Stable (insert v S) := by
  apply (FiniteMajorityPeeling.stable_iff neighbors4 (insert v S)).mpr
  intro u hu
  have hmono := FiniteMajorityPeeling.degree_mono neighbors4
    (Finset.subset_insert v S) u
  rcases Finset.mem_insert.mp hu with rfl | hu
  · exact le_trans hdeg hmono
  · exact le_trans ((FiniteMajorityPeeling.stable_iff neighbors4 S).mp hst u hu) hmono

theorem cleanup_insert_of_stable_degree_ge_two {S : Finset Site} {v : Site}
    (hst : Stable S) (hdeg : 2 ≤ degree4 S v) :
    cleanup (insert v S) = insert v S :=
  FiniteMajorityPeeling.core_eq_self neighbors4 (stable_insert_of_degree_ge_two hst hdeg)

theorem neighbors4_symmetric {u v : Site} (h : v ∈ neighbors4 u) :
    u ∈ neighbors4 v := by
  rcases (GridMajorityPeeling.mem_neighbors4 u v).mp h with hn | he | hs | hw
  · rw [GridMajorityPeeling.mem_neighbors4, hn]
    exact Or.inr (Or.inr (Or.inl (by simp [north, south])))
  · rw [GridMajorityPeeling.mem_neighbors4, he]
    exact Or.inr (Or.inr (Or.inr (by simp [east, west])))
  · rw [GridMajorityPeeling.mem_neighbors4, hs]
    exact Or.inl (by simp [south, north])
  · rw [GridMajorityPeeling.mem_neighbors4, hw]
    exact Or.inr (Or.inl (by simp [west, east]))

theorem path_mono {S T : Finset Site} (hST : S ⊆ T) {u v : Site}
    (hp : Path S u v) : Path T u v := by
  apply Relation.ReflTransGen.mono (r := InternalStep S) (p := InternalStep T) ?_ u v hp
  intro a b hab
  exact ⟨hST hab.1, hST hab.2.1, hab.2.2⟩

theorem fourConnected_insert_of_neighbor {S : Finset Site} {v w : Site}
    (hconn : FourConnected S) (hw : w ∈ S) (hvw : w ∈ neighbors4 v) :
    FourConnected (insert v S) := by
  have hsub := Finset.subset_insert v S
  have hnew : v ∈ insert v S := Finset.mem_insert_self v S
  have hwnew := hsub hw
  have hpvw : Path (insert v S) v w :=
    Relation.ReflTransGen.single ⟨hnew, hwnew, hvw⟩
  have hpwv : Path (insert v S) w v :=
    Relation.ReflTransGen.single ⟨hwnew, hnew, neighbors4_symmetric hvw⟩
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with hav | ha <;>
    rcases Finset.mem_insert.mp hb with hbv | hb
  · rw [hav, hbv]
  · rw [hav]
    exact hpvw.trans (path_mono hsub (hconn w hw b hb))
  · rw [hbv]
    exact (path_mono hsub (hconn a ha w hw)).trans hpwv
  · exact path_mono hsub (hconn a ha b hb)

theorem vacant_degree_two_insert_rowConvex {S : Finset Site} {v : Site}
    (hrow : RowConvex S) (hcol : ColumnConvex S) (hv : v ∉ S)
    (hdeg : degree4 S v = 2) : RowConvex (insert v S) :=
  rowConvex_insert_of_horizontal hrow
    (vacant_degree_two_orthogonal_neighbors hrow hcol hv hdeg).1

theorem vacant_degree_two_insert_columnConvex {S : Finset Site} {v : Site}
    (hrow : RowConvex S) (hcol : ColumnConvex S) (hv : v ∉ S)
    (hdeg : degree4 S v = 2) : ColumnConvex (insert v S) :=
  columnConvex_insert_of_vertical hcol
    (vacant_degree_two_orthogonal_neighbors hrow hcol hv hdeg).2

theorem vacant_degree_two_insert_fourConnected {S : Finset Site} {v : Site}
    (hrow : RowConvex S) (hcol : ColumnConvex S) (hv : v ∉ S)
    (hdeg : degree4 S v = 2) (hconn : FourConnected S) :
    FourConnected (insert v S) := by
  rcases (vacant_degree_two_orthogonal_neighbors hrow hcol hv hdeg).1 with he | hw
  · exact fourConnected_insert_of_neighbor hconn he
      ((GridMajorityPeeling.mem_neighbors4 v (east v)).mpr (Or.inr (Or.inl rfl)))
  · exact fourConnected_insert_of_neighbor hconn hw
      ((GridMajorityPeeling.mem_neighbors4 v (west v)).mpr (Or.inr (Or.inr (Or.inr rfl))))

/-- The new site's two coordinates already occur among old occupied sites. -/
theorem vacant_degree_two_coordinate_witnesses {S : Finset Site} {v : Site}
    (hrow : RowConvex S) (hcol : ColumnConvex S) (hv : v ∉ S)
    (hdeg : degree4 S v = 2) :
    (∃ u ∈ S, u.1 = v.1) ∧ (∃ u ∈ S, u.2 = v.2) := by
  obtain ⟨hh, hvv⟩ := vacant_degree_two_orthogonal_neighbors hrow hcol hv hdeg
  constructor
  · rcases hvv with hn | hs
    · exact ⟨north v, hn, rfl⟩
    · exact ⟨south v, hs, rfl⟩
  · rcases hh with he | hw
    · exact ⟨east v, he, rfl⟩
    · exact ⟨west v, hw, rfl⟩

theorem vacant_degree_two_insert_image_fst {S : Finset Site} {v : Site}
    (hrow : RowConvex S) (hcol : ColumnConvex S) (hv : v ∉ S)
    (hdeg : degree4 S v = 2) :
    (insert v S).image Prod.fst = S.image Prod.fst := by
  obtain ⟨u, hu, heq⟩ := (vacant_degree_two_coordinate_witnesses hrow hcol hv hdeg).1
  rw [Finset.image_insert]
  exact Finset.insert_eq_of_mem (Finset.mem_image.mpr ⟨u, hu, heq⟩)

theorem vacant_degree_two_insert_image_snd {S : Finset Site} {v : Site}
    (hrow : RowConvex S) (hcol : ColumnConvex S) (hv : v ∉ S)
    (hdeg : degree4 S v = 2) :
    (insert v S).image Prod.snd = S.image Prod.snd := by
  obtain ⟨u, hu, heq⟩ := (vacant_degree_two_coordinate_witnesses hrow hcol hv hdeg).2
  rw [Finset.image_insert]
  exact Finset.insert_eq_of_mem (Finset.mem_image.mpr ⟨u, hu, heq⟩)

theorem rawStep_eq_insert_of_birth {S : Finset Site} {v : Site} {tie : Bool}
    (hbirth : localRule S v tie = true) : rawStep S v tie = insert v S := by
  simp only [rawStep, hbirth, ite_true]

theorem modifiedStep_eq_insert_of_vacant_birth {D S : Finset Site} {v : Site}
    {tie : Bool} (hrow : RowConvex S) (hcol : ColumnConvex S)
    (hst : Stable S) (hv : v ∉ S) (hvD : v ∈ D)
    (hbirth : localRule S v tie = true) : modifiedStep D S v tie = insert v S := by
  have hdeg := ((ConvexLocalUpdate.vacant_localRule_true_iff tie hrow hcol hv).mp hbirth).1
  rw [modifiedStep, ite_eq_left hvD, rawStep_eq_insert_of_birth hbirth]
  exact cleanup_insert_of_stable_degree_ge_two hst (by omega)

theorem actual_vacant_birth_preserves {D S : Finset Site} {v : Site} {tie : Bool}
    (hrow : RowConvex S) (hcol : ColumnConvex S) (hst : Stable S)
    (hconn : FourConnected S) (hv : v ∉ S) (hvD : v ∈ D)
    (hbirth : localRule S v tie = true) :
    modifiedStep D S v tie = insert v S ∧
      RowConvex (modifiedStep D S v tie) ∧
      ColumnConvex (modifiedStep D S v tie) ∧
      Stable (modifiedStep D S v tie) ∧
      FourConnected (modifiedStep D S v tie) := by
  have hdeg := ((ConvexLocalUpdate.vacant_localRule_true_iff tie hrow hcol hv).mp hbirth).1
  have heq := modifiedStep_eq_insert_of_vacant_birth hrow hcol hst hv hvD hbirth
  refine ⟨heq, ?_⟩
  rw [heq]
  exact ⟨vacant_degree_two_insert_rowConvex hrow hcol hv hdeg,
    vacant_degree_two_insert_columnConvex hrow hcol hv hdeg,
    stable_insert_of_degree_ge_two hst (by omega),
    vacant_degree_two_insert_fourConnected hrow hcol hv hdeg hconn⟩

end MathResearchAnalysis.ConvexBirthUpdate

module

public import MathResearchAnalysis.SquareTasks
public import Mathlib.Data.Bool.Basic

set_option autoImplicit false

/-!
# Actual zero-boundary square-spin updates

Every site has four directional inputs. A missing neighbor is fixed to false,
so it contributes zero to `ones`; the threshold is always two, including at
edges and corners. This is not majority among only the interior neighbors.
The deterministic event update reads the mark of its actual event identity.
-/

public section

namespace MathResearchAnalysis.SquareSpin

open SquareTasks

abbrev Config (n : ℕ) := Vertex n → Bool
abbrev Event (n : ℕ) := Vertex n × ℕ

/-- Number of true inputs among the four directions, with outside inputs zero. -/
@[expose] def ones {n : ℕ} (f : Config n) (v : Vertex n) : ℕ :=
  ∑ u ∈ neighbors n v, (f u).toNat

/-- East input, fixed to zero when the directional move exits the square. -/
@[expose] def eastInput {n : ℕ} (f : Config n) (v : Vertex n) : Bool :=
  if v.1.val + 1 < n + 2 then f (east v) else false

/-- West input, fixed to zero when the directional move exits the square. -/
@[expose] def westInput {n : ℕ} (f : Config n) (v : Vertex n) : Bool :=
  if 0 < v.1.val then f (west v) else false

/-- North input, fixed to zero when the directional move exits the square. -/
@[expose] def northInput {n : ℕ} (f : Config n) (v : Vertex n) : Bool :=
  if v.2.val + 1 < n + 2 then f (north v) else false

/-- South input, fixed to zero when the directional move exits the square. -/
@[expose] def southInput {n : ℕ} (f : Config n) (v : Vertex n) : Bool :=
  if 0 < v.2.val then f (south v) else false

/-- The finite-neighbor sum is exactly the four directional zero-boundary inputs. -/
theorem ones_eq_four_inputs {n : ℕ} (f : Config n) (v : Vertex n) :
    ones f v = (eastInput f v).toNat + (westInput f v).toNat +
      (northInput f v).toNat + (southInput f v).toNat := by
  have he (u : Vertex n) :
      (v.1.val + 1 = u.1.val ∧ v.2 = u.2) ↔
        u = east v ∧ v.1.val + 1 < n + 2 := by
    have hv := v.1.isLt
    have hu := u.1.isLt
    simp only [east, Prod.ext_iff, Fin.ext_iff]
    omega
  have hw (u : Vertex n) :
      (u.1.val + 1 = v.1.val ∧ v.2 = u.2) ↔
        u = west v ∧ 0 < v.1.val := by
    simp only [west, Prod.ext_iff, Fin.ext_iff]
    omega
  have hn (u : Vertex n) :
      (v.1 = u.1 ∧ v.2.val + 1 = u.2.val) ↔
        u = north v ∧ v.2.val + 1 < n + 2 := by
    have hv := v.2.isLt
    have hu := u.2.isLt
    simp only [north, Prod.ext_iff, Fin.ext_iff]
    omega
  have hs (u : Vertex n) :
      (v.1 = u.1 ∧ u.2.val + 1 = v.2.val) ↔
        u = south v ∧ 0 < v.2.val := by
    simp only [south, Prod.ext_iff, Fin.ext_iff]
    omega
  have hsplit (u : Vertex n) :
      (if Adjacent v u then (f u).toNat else 0) =
        (if v.1.val + 1 = u.1.val ∧ v.2 = u.2 then (f u).toNat else 0) +
        (if u.1.val + 1 = v.1.val ∧ v.2 = u.2 then (f u).toNat else 0) +
        (if v.1 = u.1 ∧ v.2.val + 1 = u.2.val then (f u).toNat else 0) +
        (if v.1 = u.1 ∧ u.2.val + 1 = v.2.val then (f u).toNat else 0) := by
    simp only [Adjacent, Fin.ext_iff]
    split_ifs <;> omega
  unfold ones neighbors
  rw [Finset.sum_filter]
  simp_rw [hsplit, he, hw, hn, hs]
  simp only [Finset.sum_add_distrib]
  by_cases he' : v.1.val + 1 < n + 2 <;>
    by_cases hw' : 0 < v.1.val <;>
    by_cases hn' : v.2.val + 1 < n + 2 <;>
    by_cases hs' : 0 < v.2.val <;>
    simp [eastInput, westInput, northInput, southInput, he', hw', hn', hs']

/-- Strict four-input majority, using the supplied event mark only at a tie. -/
@[expose] def rule {n : ℕ} (f : Config n) (v : Vertex n) (tie : Bool) : Bool :=
  if 2 < ones f v then true else if ones f v < 2 then false else tie

/-- A single write, after evaluating the actual rule in the old configuration. -/
@[expose] def cellUpdate {n : ℕ} (f : Config n) (v : Vertex n) (tie : Bool) : Config n :=
  Function.update f v (rule f v tie)

/-- Marks are indexed by actual site/ring identities, rather than word positions. -/
@[expose] def updateEvent {n : ℕ} (η : Event n → Bool) (e : Event n)
    (f : Config n) : Config n :=
  cellUpdate f e.1 (η e)

/-- Same-site and adjacent-site events are the explicit conflicts. -/
@[expose] def Conflict {n : ℕ} (a b : Event n) : Prop :=
  a.1 = b.1 ∨ Adjacent a.1 b.1

theorem conflict_symmetric {n : ℕ} {a b : Event n} (h : Conflict a b) :
    Conflict b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (adjacent_symmetric h)

theorem not_conflict_iff {n : ℕ} (a b : Event n) :
    ¬ Conflict a b ↔ a.1 ≠ b.1 ∧ ¬ Adjacent a.1 b.1 := by
  simp [Conflict]

theorem ones_reads_only {n : ℕ} {f g : Config n} (v : Vertex n)
    (h : ∀ u, Adjacent v u → f u = g u) : ones f v = ones g v := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [h u ((mem_neighbors_iff n v u).mp hu)]

theorem rule_reads_only {n : ℕ} {f g : Config n} (v : Vertex n) (tie : Bool)
    (h : ∀ u, Adjacent v u → f u = g u) : rule f v tie = rule g v tie := by
  simp only [rule, ones_reads_only v h]

theorem ones_le_four {n : ℕ} (f : Config n) (v : Vertex n) : ones f v ≤ 4 := by
  calc
    ones f v ≤ ∑ _u ∈ neighbors n v, 1 :=
      Finset.sum_le_sum fun u _ => Bool.toNat_le (f u)
    _ = (neighbors n v).card := by simp
    _ ≤ 4 := neighbors_card_le_four n v

theorem ones_mono {n : ℕ} {f g : Config n} (h : f ≤ g) (v : Vertex n) :
    ones f v ≤ ones g v := by
  exact Finset.sum_le_sum fun u _ => Bool.toNat_le_toNat (h u)

@[simp] theorem ones_zero {n : ℕ} (v : Vertex n) :
    ones (fun _ => false) v = 0 := by simp [ones]

@[simp] theorem rule_zero {n : ℕ} (v : Vertex n) (tie : Bool) :
    rule (fun _ => false) v tie = false := by simp [rule]

theorem rule_of_lt_two {n : ℕ} (f : Config n) (v : Vertex n) (tie : Bool)
    (h : ones f v < 2) : rule f v tie = false := by
  simp [rule, h, show ¬ 2 < ones f v by omega]

theorem rule_of_gt_two {n : ℕ} (f : Config n) (v : Vertex n) (tie : Bool)
    (h : 2 < ones f v) : rule f v tie = true := by simp [rule, h]

theorem rule_of_eq_two {n : ℕ} (f : Config n) (v : Vertex n) (tie : Bool)
    (h : ones f v = 2) : rule f v tie = tie := by simp [rule, h]

theorem rule_mono_common_mark {n : ℕ} {f g : Config n} (h : f ≤ g)
    (v : Vertex n) (tie : Bool) : rule f v tie ≤ rule g v tie := by
  have hs := ones_mono h v
  unfold rule
  split_ifs <;> simp_all <;> omega

@[simp] theorem cellUpdate_same {n : ℕ} (f : Config n) (v : Vertex n) (tie : Bool) :
    cellUpdate f v tie v = rule f v tie := by simp [cellUpdate]

theorem cellUpdate_other {n : ℕ} (f : Config n) (v u : Vertex n) (tie : Bool)
    (h : u ≠ v) : cellUpdate f v tie u = f u := by simp [cellUpdate, h]

@[simp] theorem cellUpdate_zero {n : ℕ} (v : Vertex n) (tie : Bool) :
    cellUpdate (fun _ => false) v tie = (fun _ => false) := by
  funext u
  by_cases h : u = v <;> simp [cellUpdate, h]

theorem cellUpdate_mono_common_mark {n : ℕ} {f g : Config n} (h : f ≤ g)
    (v : Vertex n) (tie : Bool) : cellUpdate f v tie ≤ cellUpdate g v tie := by
  intro u
  by_cases hu : u = v
  · subst u
    simpa only [cellUpdate_same] using rule_mono_common_mark h v tie
  · simpa only [cellUpdate_other f v u tie hu, cellUpdate_other g v u tie hu] using h u

theorem rule_eq_after_nonadjacent_update {n : ℕ} (f : Config n)
    (v u : Vertex n) (tie mark : Bool) (h : ¬ Adjacent v u) :
    rule (cellUpdate f u mark) v tie = rule f v tie := by
  apply rule_reads_only
  intro w hw
  exact cellUpdate_other f u w mark (by intro he; subst w; exact h hw)

theorem cellUpdate_commute {n : ℕ} (f : Config n) (v u : Vertex n)
    (tie mark : Bool) (hne : v ≠ u) (hadj : ¬ Adjacent v u) :
    cellUpdate (cellUpdate f v tie) u mark =
      cellUpdate (cellUpdate f u mark) v tie := by
  have hrev : ¬ Adjacent u v := fun h => hadj (adjacent_symmetric h)
  funext w
  by_cases hwv : w = v
  · subst w
    rw [cellUpdate_other _ u v mark hne, cellUpdate_same, cellUpdate_same,
      rule_eq_after_nonadjacent_update f v u tie mark hadj]
  · by_cases hwu : w = u
    · subst w
      rw [cellUpdate_same, cellUpdate_other _ v u tie hne.symm, cellUpdate_same,
        rule_eq_after_nonadjacent_update f u v mark tie hrev]
    · rw [cellUpdate_other _ u w mark hwu, cellUpdate_other _ v w tie hwv,
        cellUpdate_other _ v w tie hwv, cellUpdate_other _ u w mark hwu]

theorem updateEvent_commute {n : ℕ} (η : Event n → Bool) {a b : Event n}
    (h : ¬ Conflict a b) (f : Config n) :
    updateEvent η b (updateEvent η a f) = updateEvent η a (updateEvent η b f) := by
  exact cellUpdate_commute f a.1 b.1 (η a) (η b)
    ((not_conflict_iff a b).mp h).1 ((not_conflict_iff a b).mp h).2

@[simp] theorem updateEvent_zero {n : ℕ} (η : Event n → Bool) (e : Event n) :
    updateEvent η e (fun _ => false) = (fun _ => false) := by simp [updateEvent]

theorem updateEvent_mono {n : ℕ} (η : Event n → Bool) (e : Event n)
    {f g : Config n} (h : f ≤ g) : updateEvent η e f ≤ updateEvent η e g :=
  cellUpdate_mono_common_mark h e.1 (η e)

/-- All sites read the same old configuration, with one supplied mark per site. -/
@[expose] def synchronousStep {n : ℕ} (f : Config n) (marks : Vertex n → Bool) :
    Config n := fun v => rule f v (marks v)

/-- The selected checkerboard color updates simultaneously; the other color waits. -/
@[expose] def checkerboardStep {n : ℕ} (f : Config n) (colour : Bool)
    (marks : Vertex n → Bool) : Config n :=
  fun v => if SquareTasks.colour v = colour then rule f v (marks v) else f v

@[simp] theorem synchronousStep_zero {n : ℕ} (marks : Vertex n → Bool) :
    synchronousStep (fun _ => false) marks = (fun _ => false) := by
  funext v
  exact rule_zero v (marks v)

theorem synchronousStep_mono {n : ℕ} {f g : Config n} (h : f ≤ g)
    (marks : Vertex n → Bool) : synchronousStep f marks ≤ synchronousStep g marks :=
  fun v => rule_mono_common_mark h v (marks v)

@[simp] theorem checkerboardStep_zero {n : ℕ} (colour : Bool)
    (marks : Vertex n → Bool) :
    checkerboardStep (fun _ => false) colour marks = (fun _ => false) := by
  funext v
  simp [checkerboardStep]

theorem checkerboardStep_mono {n : ℕ} {f g : Config n} (h : f ≤ g)
    (colour : Bool) (marks : Vertex n → Bool) :
    checkerboardStep f colour marks ≤ checkerboardStep g colour marks := by
  intro v
  unfold checkerboardStep
  split_ifs
  · exact rule_mono_common_mark h v (marks v)
  · exact h v

/-- Two different sites in one color class satisfy the proved commutation law. -/
theorem cellUpdate_commute_same_colour {n : ℕ} (f : Config n) (v u : Vertex n)
    (tie mark : Bool) (hne : v ≠ u) (hcolour : colour v = colour u) :
    cellUpdate (cellUpdate f v tie) u mark =
      cellUpdate (cellUpdate f u mark) v tie := by
  apply cellUpdate_commute f v u tie mark hne
  intro hadj
  have hflip := adjacent_colour_flip hadj
  rw [← hcolour] at hflip
  cases hcv : colour v <;> simp [hcv] at hflip

end MathResearchAnalysis.SquareSpin

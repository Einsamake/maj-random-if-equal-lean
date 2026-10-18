module

public import MathResearchAnalysis.ClockReadiness

set_option autoImplicit false

/-!
# Actual selected-clock conflict order and event identity

The task times are the constructed extended clock times of `ClockReadiness`,
not prescribed natural-number times. The proved common full-measure event of
finite readiness gives strict neighboring-layer order. Actual square geometry
then gives even same-site and odd neighboring-site order.

Selected positive layer `j` consists of `tasks n c (j - 1)`. Each finite
selected completion is identified with its genuine clock arrival index.
Different selected tasks have different `(site, arrival-index)` identifiers.
This does not assert that all arrivals at different sites have distinct times,
and proves no distribution or independence of selected heat-bath marks.
-/

public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.ClockEventOrder

abbrev Sample (n : ℕ) := ExponentialClocks.Sample (SquareTasks.Vertex n)

abbrev completion (n : ℕ) := ClockReadiness.completion (SquareTasks.system n)
abbrev ready (n : ℕ) := ClockReadiness.ready (SquareTasks.system n)

/-- One common full-measure event, rather than separately chosen task exceptions. -/
@[expose] def Regular (n : ℕ) (ω : Sample n) : Prop :=
  (∀ j v, completion n j v ω ≠ ⊤) ∧ (∀ j v, ready n j v ω ≠ ⊤)

theorem regular_ae (n : ℕ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n), Regular n ω :=
  ClockReadiness.square_all_times_finite_ae n

/-- The first positive layer is `j = 1`; initialization is never selected. -/
@[expose] def Selected (n : ℕ) (c : Bool) (j : ℕ) (v : SquareTasks.Vertex n) : Prop :=
  0 < j ∧ v ∈ SquareTasks.tasks n c (j - 1)

theorem predecessor_lt (n : ℕ) (ω : Sample n) (hω : Regular n ω) (j : ℕ)
    {u v : SquareTasks.Vertex n} (hu : u ∈ SquareTasks.neighbors n v) :
    completion n j u ω < completion n (j + 1) v ω :=
  (ClockReadiness.predecessor_completion_le_ready (SquareTasks.system n) j v u hu ω).trans_lt
    (ClockReadiness.ready_lt_completion (SquareTasks.system n) j v ω (hω.2 j v))

theorem same_site_two_steps (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    (v : SquareTasks.Vertex n) (j : ℕ) :
    completion n j v ω < completion n (j + 2) v ω := by
  obtain ⟨w, hw⟩ := SquareTasks.neighbors_nonempty n v
  have hv := (SquareTasks.neighbors_symmetric n v w).mp hw
  have hfirst := predecessor_lt n ω hω j hv
  have hsecond := predecessor_lt n ω hω (j + 1) hw
  simpa only [Nat.add_assoc] using hfirst.trans hsecond

theorem same_site_even_gap (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    (v : SquareTasks.Vertex n) (j k : ℕ) :
    completion n j v ω < completion n (j + 2 * (k + 1)) v ω := by
  induction k with
  | zero => simpa using same_site_two_steps n ω hω v j
  | succ k ih =>
    have hnext := same_site_two_steps n ω hω v (j + 2 * (k + 1))
    have heq : j + 2 * ((k + 1) + 1) = (j + 2 * (k + 1)) + 2 := by omega
    rw [heq]
    exact ih.trans hnext

theorem same_site_even_order (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    (v : SquareTasks.Vertex n) {a b : ℕ} (hab : a < b)
    (heven : (b - a) % 2 = 0) : completion n a v ω < completion n b v ω := by
  have hb : b = a + 2 * (((b - a) / 2 - 1) + 1) := by omega
  rw [hb]
  exact same_site_even_gap n ω hω v a ((b - a) / 2 - 1)

theorem neighbor_odd_gap (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    {u v : SquareTasks.Vertex n} (hu : u ∈ SquareTasks.neighbors n v) (j k : ℕ) :
    completion n j u ω < completion n (j + 2 * k + 1) v ω := by
  cases k with
  | zero => simpa using predecessor_lt n ω hω j hu
  | succ k =>
    have hfirst := predecessor_lt n ω hω j hu
    have hsecond := same_site_even_gap n ω hω v (j + 1) k
    have heq : j + 2 * (k + 1) + 1 = (j + 1) + 2 * (k + 1) := by omega
    rw [heq]
    exact hfirst.trans hsecond

theorem neighbor_odd_order (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    {u v : SquareTasks.Vertex n} (hu : u ∈ SquareTasks.neighbors n v)
    {a b : ℕ} (hab : a < b) (hodd : (b - a) % 2 = 1) :
    completion n a u ω < completion n b v ω := by
  have hb : b = a + 2 * ((b - a) / 2) + 1 := by omega
  rw [hb]
  exact neighbor_odd_gap n ω hω hu a ((b - a) / 2)

theorem selected_same_site_even (n : ℕ) (c : Bool) {a b : ℕ}
    {v : SquareTasks.Vertex n} (ha : Selected n c a v) (hb : Selected n c b v) :
    (b - a) % 2 = 0 := by
  have hA := (SquareTasks.mem_tasks_iff n c (a - 1) v).mp ha.2
  have hB := (SquareTasks.mem_tasks_iff n c (b - 1) v).mp hb.2
  have ha0 := ha.1
  have hb0 := hb.1
  omega

theorem selected_neighbor_odd (n : ℕ) (c : Bool) {a b : ℕ}
    {u v : SquareTasks.Vertex n} (ha : Selected n c a u) (hb : Selected n c b v)
    (hu : u ∈ SquareTasks.neighbors n v) (hab : a < b) : (b - a) % 2 = 1 := by
  have hA := (SquareTasks.mem_tasks_iff n c (a - 1) u).mp ha.2
  have hB := (SquareTasks.mem_tasks_iff n c (b - 1) v).mp hb.2
  have ha0 := ha.1
  have hb0 := hb.1
  have hs := SquareTasks.adjacent_sum_step ((SquareTasks.mem_neighbors_iff n v u).mp hu)
  rcases hs with hs | hs <;> omega

theorem selected_conflict_order (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    (c : Bool) {a b : ℕ} {u v : SquareTasks.Vertex n}
    (ha : Selected n c a u) (hb : Selected n c b v) (hab : a < b)
    (hconflict : u = v ∨ u ∈ SquareTasks.neighbors n v) :
    completion n a u ω < completion n b v ω := by
  rcases hconflict with hsame | hu
  · subst u
    exact same_site_even_order n ω hω v hab (selected_same_site_even n c ha hb)
  · exact neighbor_odd_order n ω hω hu hab (selected_neighbor_odd n c ha hb hu hab)

/-- Every neighboring-layer dependency is strictly chronological almost surely. -/
theorem predecessor_lt_ae (n : ℕ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ j (u v : SquareTasks.Vertex n), u ∈ SquareTasks.neighbors n v →
        completion n j u ω < completion n (j + 1) v ω :=
  (regular_ae n).mono (fun ω hω j _ _ hu => predecessor_lt n ω hω j hu)

/-- All selected conflicts preserve logical task order on one full-measure set. -/
theorem selected_conflict_order_ae (n : ℕ) (c : Bool) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ (a b : ℕ) (u v : SquareTasks.Vertex n), Selected n c a u → Selected n c b v →
        a < b → (u = v ∨ u ∈ SquareTasks.neighbors n v) →
          completion n a u ω < completion n b v ω :=
  (regular_ae n).mono (fun ω hω _ _ _ _ ha hb hab hc =>
    selected_conflict_order n ω hω c ha hb hab hc)

theorem selected_same_layer_no_neighbor (n : ℕ) (c : Bool) {a : ℕ}
    {u v : SquareTasks.Vertex n} (ha : Selected n c a u) (hb : Selected n c a v) :
    u ∉ SquareTasks.neighbors n v := by
  intro hu
  have hA := (SquareTasks.mem_tasks_iff n c (a - 1) u).mp ha.2
  have hB := (SquareTasks.mem_tasks_iff n c (a - 1) v).mp hb.2
  have hs := SquareTasks.adjacent_sum_step ((SquareTasks.mem_neighbors_iff n v u).mp hu)
  rcases hs with hs | hs <;> omega

theorem selected_conflict_order_iff (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    (c : Bool) {a b : ℕ} {u v : SquareTasks.Vertex n}
    (ha : Selected n c a u) (hb : Selected n c b v)
    (hconflict : u = v ∨ u ∈ SquareTasks.neighbors n v) :
    completion n a u ω < completion n b v ω ↔ a < b := by
  constructor
  · intro htime
    by_cases hab : a = b
    · subst b
      rcases hconflict with hsame | hu
      · subst u
        exact False.elim ((lt_irrefl _) htime)
      · exact False.elim (selected_same_layer_no_neighbor n c ha hb hu)
    · rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact hlt
      · have hreverse : completion n b v ω < completion n a u ω := by
          apply selected_conflict_order n ω hω c hb ha hgt
          rcases hconflict with hsame | hu
          · exact Or.inl hsame.symm
          · exact Or.inr ((SquareTasks.neighbors_symmetric n v u).mp hu)
        exact False.elim ((not_lt_of_ge hreverse.le) htime)
  · exact fun hab => selected_conflict_order n ω hω c ha hb hab hconflict

theorem selected_conflict_order_iff_ae (n : ℕ) (c : Bool) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ (a b : ℕ) (u v : SquareTasks.Vertex n), Selected n c a u → Selected n c b v →
        (u = v ∨ u ∈ SquareTasks.neighbors n v) →
          (completion n a u ω < completion n b v ω ↔ a < b) :=
  (regular_ae n).mono (fun ω hω _ _ _ _ ha hb hc =>
    selected_conflict_order_iff n ω hω c ha hb hc)

theorem same_site_two_steps_ae (n : ℕ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ j (v : SquareTasks.Vertex n), completion n j v ω < completion n (j + 2) v ω :=
  (regular_ae n).mono (fun ω hω j v => same_site_two_steps n ω hω v j)

theorem same_site_even_order_ae (n : ℕ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ (a b : ℕ) (v : SquareTasks.Vertex n), a < b → (b - a) % 2 = 0 →
        completion n a v ω < completion n b v ω :=
  (regular_ae n).mono (fun ω hω _ _ v hab heven => same_site_even_order n ω hω v hab heven)

theorem neighbor_odd_order_ae (n : ℕ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ (a b : ℕ) (u v : SquareTasks.Vertex n), u ∈ SquareTasks.neighbors n v →
        a < b → (b - a) % 2 = 1 → completion n a u ω < completion n b v ω :=
  (regular_ae n).mono (fun ω hω _ _ _ _ hu hab hodd =>
    neighbor_odd_order n ω hω hu hab hodd)

theorem selected_same_site_time_ne (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    (c : Bool) {a b : ℕ} {v : SquareTasks.Vertex n}
    (ha : Selected n c a v) (hb : Selected n c b v) (hab : a ≠ b) :
    completion n a v ω ≠ completion n b v ω := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact (selected_conflict_order n ω hω c ha hb hlt (Or.inl rfl)).ne
  · exact (selected_conflict_order n ω hω c hb ha hgt (Or.inl rfl)).ne.symm

/-- The real site's actual arrival index; meaningful on positive finite tasks. -/
@[expose] def eventIndex (n : ℕ) (j : ℕ) (v : SquareTasks.Vertex n) (ω : Sample n) : ℕ :=
  ExtendedNextRing.selectedIndex (ArrivalFiltration.chronologicalArrival v) (ready n (j - 1) v) ω

@[expose] def eventId (n : ℕ) (j : ℕ) (v : SquareTasks.Vertex n) (ω : Sample n) :
    SquareTasks.Vertex n × ℕ := (v, eventIndex n j v ω)

theorem completion_eq_selected_arrival (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    (j : ℕ) (v : SquareTasks.Vertex n) (hj : 0 < j) :
    completion n j v ω =
      (ArrivalFiltration.chronologicalArrival v (eventIndex n j v ω) ω : WithTop ℝ) := by
  cases j with
  | zero => omega
  | succ j =>
    exact ExtendedNextRing.after_eq_selected_arrival (ArrivalFiltration.chronologicalArrival v)
      (ready n j v) ω (hω.1 (j + 1) v)

theorem selected_same_site_index_lt (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    (c : Bool) {a b : ℕ} {v : SquareTasks.Vertex n}
    (ha : Selected n c a v) (hb : Selected n c b v) (hab : a < b) :
    eventIndex n a v ω < eventIndex n b v ω := by
  have htime := selected_conflict_order n ω hω c ha hb hab (Or.inl rfl)
  rw [completion_eq_selected_arrival n ω hω a v ha.1,
    completion_eq_selected_arrival n ω hω b v hb.1] at htime
  by_contra hnot
  have hle := ArrivalFiltration.chronologicalArrival_monotone v ω (Nat.le_of_not_gt hnot)
  exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hle)) htime

theorem selected_same_site_index_ne (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    (c : Bool) {a b : ℕ} {v : SquareTasks.Vertex n}
    (ha : Selected n c a v) (hb : Selected n c b v) (hab : a ≠ b) :
    eventIndex n a v ω ≠ eventIndex n b v ω := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact (selected_same_site_index_lt n ω hω c ha hb hlt).ne
  · exact (selected_same_site_index_lt n ω hω c hb ha hgt).ne.symm

theorem distinct_selected_eventId (n : ℕ) (ω : Sample n) (hω : Regular n ω)
    (c : Bool) {a b : ℕ} {u v : SquareTasks.Vertex n}
    (ha : Selected n c a u) (hb : Selected n c b v) (htasks : (a, u) ≠ (b, v)) :
    eventId n a u ω ≠ eventId n b v ω := by
  intro heq
  have huv : u = v := congrArg Prod.fst heq
  subst u
  have hab : a ≠ b := by intro hab; exact htasks (by rw [hab])
  exact selected_same_site_index_ne n ω hω c ha hb hab (congrArg Prod.snd heq)

/-- Actual `(site, arrival-index)` identifiers of distinct selected tasks never repeat a.e. -/
theorem distinct_selected_eventId_ae (n : ℕ) (c : Bool) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ (a b : ℕ) (u v : SquareTasks.Vertex n), Selected n c a u → Selected n c b v →
        (a, u) ≠ (b, v) → eventId n a u ω ≠ eventId n b v ω :=
  (regular_ae n).mono (fun ω hω _ _ _ _ ha hb hd =>
    distinct_selected_eventId n ω hω c ha hb hd)

theorem selected_same_site_time_ne_ae (n : ℕ) (c : Bool) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ (a b : ℕ) (v : SquareTasks.Vertex n), Selected n c a v → Selected n c b v →
        a ≠ b → completion n a v ω ≠ completion n b v ω :=
  (regular_ae n).mono (fun ω hω _ _ _ ha hb hd =>
    selected_same_site_time_ne n ω hω c ha hb hd)

/-- The selected identifier is an event of the original exponential stream a.e. -/
theorem selected_completion_eq_raw_arrival_ae (n : ℕ) (c : Bool) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ (j : ℕ) (v : SquareTasks.Vertex n), Selected n c j v →
        completion n j v ω =
          (ExponentialClocks.arrival v (eventIndex n j v ω) ω : WithTop ℝ) := by
  filter_upwards [regular_ae n,
    ArrivalFiltration.chronologicalArrival_eq_raw_ae (V := SquareTasks.Vertex n)] with ω hω heq
  intro j v hj
  rw [completion_eq_selected_arrival n ω hω j v hj.1, heq v (eventIndex n j v ω)]

end MathResearchAnalysis.ClockEventOrder

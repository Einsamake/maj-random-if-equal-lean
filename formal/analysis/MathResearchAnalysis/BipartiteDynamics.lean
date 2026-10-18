module

public import Std

set_option autoImplicit false

public section

/-!
# Deterministic bipartite synchronous / alternating dynamics

This is an explicit source migration of core MathResearch/Dynamics.lean from
the Lean 4.35.0 core project into the Lean 4.35.0-rc4 analysis project.
No core olean or cross-compiler import is used. The deterministic statements
and the time/phase conventions are retained.

This module proves the pathwise splitting lemma.  All random marks, if any,
are already fixed and incorporated into `update`.  There are no probability,
expectation, Ising, or asymptotic claims in this module.

The model assumes that an update at a vertex reads only the opposite colour
and that the all-false configuration is absorbing.  Neither finiteness of the
vertex type nor a particular graph or neighbourhood is required.
-/

namespace MathResearchAnalysis.BipartiteDynamics

universe u

abbrev State (V : Type u) := V → Bool

@[expose] def zeroState {V : Type u} : State V := fun _ => false

@[expose] def IsZero {V : Type u} (state : State V) : Prop :=
  ∀ v, state v = false

structure BipartiteSystem (V : Type u) where
  colour : V → Bool
  update : Nat → V → State V → Bool
  opposite_local : ∀ (t : Nat) (v : V) (s r : State V),
    (∀ w, colour w ≠ colour v → s w = r w) →
    update t v s = update t v r
  zero_update : ∀ (t : Nat) (v : V), update t v zeroState = false

/-- At step `t + 1`, chain `c` updates the opposite of its step-`t` colour.
    Thus its first update colour is `!c`, as in `colour(v) + t = c mod 2`. -/
@[expose] def activeColour (c : Bool) : Nat → Bool
  | 0 => c
  | t + 1 => !(activeColour c t)

@[simp] theorem activeColour_zero (c : Bool) : activeColour c 0 = c := rfl

@[simp] theorem activeColour_succ (c : Bool) (t : Nat) :
    activeColour c (t + 1) = !(activeColour c t) := rfl

theorem activeColour_complement (c : Bool) (t : Nat) :
    activeColour (!c) t = !(activeColour c t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [activeColour, ih]

/-- Explicit parity formula, keeping phase at initialization rather than first update. -/
theorem activeColour_eq_parity (c : Bool) (t : Nat) :
    activeColour c t = if t % 2 = 0 then c else !c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [activeColour_succ, ih]
    by_cases ht : t % 2 = 0
    · have ht' : (t + 1) % 2 ≠ 0 := by omega
      simp [ht, ht']
    · have ht' : (t + 1) % 2 = 0 := by omega
      simp [ht, ht']

private theorem bool_eq_of_ne_not {b a : Bool} (h : b ≠ !a) : b = a := by
  cases b <;> cases a <;> simp_all

private theorem bool_eq_not_of_ne {b a : Bool} (h : b ≠ a) : b = !a := by
  cases b <;> cases a <;> simp_all

namespace BipartiteSystem

variable {V : Type u} (M : BipartiteSystem V)

/-- All sites update simultaneously; the update producing time `t + 1`
    receives mark/time index `t + 1`. -/
@[expose] def synchronous (initial : State V) : Nat → State V
  | 0 => initial
  | t + 1 => fun v => M.update (t + 1) v (synchronous initial t)

/-- One colour updates per slot. Both chains use the same fixed update
    function at the same site and time. -/
@[expose] def alternating (initial : State V) (c : Bool) : Nat → State V
  | 0 => initial
  | t + 1 => fun v =>
    if M.colour v = activeColour c (t + 1) then
      M.update (t + 1) v (alternating initial c t)
    else alternating initial c t v

/-- The precise splitting identity, indexed without truncated subtraction. -/
theorem splitting_succ (initial : State V) (c : Bool) :
    ∀ (t : Nat) (v : V),
      M.alternating initial c (t + 1) v =
        if M.colour v = activeColour c (t + 1) then
          M.synchronous initial (t + 1) v
        else M.synchronous initial t v := by
  intro t
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    change
      (if M.colour v = activeColour c ((t + 1) + 1) then
        M.update ((t + 1) + 1) v (M.alternating initial c (t + 1))
      else M.alternating initial c (t + 1) v) =
      (if M.colour v = activeColour c ((t + 1) + 1) then
        M.update ((t + 1) + 1) v (M.synchronous initial (t + 1))
      else M.synchronous initial (t + 1) v)
    by_cases hv : M.colour v = activeColour c ((t + 1) + 1)
    · rw [ite_eq_left hv, ite_eq_left hv]
      apply M.opposite_local
      intro w hw
      have hv' : M.colour v = !(activeColour c (t + 1)) := hv
      rw [hv'] at hw
      have hw' : M.colour w = activeColour c (t + 1) :=
        bool_eq_of_ne_not hw
      rw [ih w, ite_eq_left hw']
    · rw [ite_eq_right hv, ite_eq_right hv]
      have hv' : M.colour v ≠ !(activeColour c (t + 1)) := hv
      have hv'' : M.colour v = activeColour c (t + 1) :=
        bool_eq_of_ne_not hv'
      rw [ih v, ite_eq_left hv'']

/-- At every positive time, the active colour stores synchronous time `t`
    and the inactive colour stores synchronous time `t - 1`. -/
theorem splitting (initial : State V) (c : Bool) (t : Nat) (ht : 1 ≤ t)
    (v : V) :
    M.alternating initial c t v =
      if M.colour v = activeColour c t then M.synchronous initial t v
      else M.synchronous initial (t - 1) v := by
  cases t with
  | zero => omega
  | succ t => simpa using M.splitting_succ initial c t v

theorem active_value (initial : State V) (c : Bool) (t : Nat) (ht : 1 ≤ t)
    (v : V) (hv : M.colour v = activeColour c t) :
    M.alternating initial c t v = M.synchronous initial t v := by
  rw [M.splitting initial c t ht v, ite_eq_left hv]

theorem inactive_value (initial : State V) (c : Bool) (t : Nat) (ht : 1 ≤ t)
    (v : V) (hv : M.colour v ≠ activeColour c t) :
    M.alternating initial c t v = M.synchronous initial (t - 1) v := by
  rw [M.splitting initial c t ht v, ite_eq_right hv]

theorem synchronous_zero_step (initial : State V) (t : Nat)
    (hz : IsZero (M.synchronous initial t)) :
    IsZero (M.synchronous initial (t + 1)) := by
  intro v
  change M.update (t + 1) v (M.synchronous initial t) = false
  have hs : M.synchronous initial t = zeroState := funext hz
  rw [hs]
  exact M.zero_update (t + 1) v

theorem alternating_zero_step (initial : State V) (c : Bool) (t : Nat)
    (hz : IsZero (M.alternating initial c t)) :
    IsZero (M.alternating initial c (t + 1)) := by
  intro v
  change
    (if M.colour v = activeColour c (t + 1) then
      M.update (t + 1) v (M.alternating initial c t)
    else M.alternating initial c t v) = false
  have hs : M.alternating initial c t = zeroState := funext hz
  by_cases hc : M.colour v = activeColour c (t + 1)
  · rw [ite_eq_left hc, hs]
    exact M.zero_update (t + 1) v
  · rw [ite_eq_right hc]
    exact hz v

private theorem zero_persists (trajectory : Nat → State V)
    (step : ∀ t, IsZero (trajectory t) → IsZero (trajectory (t + 1)))
    {t s : Nat} (hz : IsZero (trajectory t)) (hle : t ≤ s) :
    IsZero (trajectory s) := by
  induction s with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    exact hz
  | succ s ih =>
    by_cases ht : t ≤ s
    · exact step s (ih ht)
    · have hts : t = s + 1 := by omega
      subst t
      exact hz

theorem synchronous_zero_persists (initial : State V) {t s : Nat}
    (hz : IsZero (M.synchronous initial t)) (hle : t ≤ s) :
    IsZero (M.synchronous initial s) :=
  zero_persists (M.synchronous initial) (M.synchronous_zero_step initial) hz hle

theorem alternating_zero_persists (initial : State V) (c : Bool) {t s : Nat}
    (hz : IsZero (M.alternating initial c t)) (hle : t ≤ s) :
    IsZero (M.alternating initial c s) :=
  zero_persists (M.alternating initial c) (M.alternating_zero_step initial c) hz hle

/-- If the synchronous chain is zero at `t`, each alternating chain is zero
    by `t + 1`, including the boundary case `t = 0`. -/
theorem synchronous_zero_implies_alternating_next_zero
    (initial : State V) (c : Bool) (t : Nat)
    (hz : IsZero (M.synchronous initial t)) :
    IsZero (M.alternating initial c (t + 1)) := by
  intro v
  rw [M.splitting_succ initial c t v]
  by_cases hc : M.colour v = activeColour c (t + 1)
  · rw [ite_eq_left hc]
    exact M.synchronous_zero_step initial t hz v
  · rw [ite_eq_right hc]
    exact hz v

/-- If both alternating chains are zero at a common time, the synchronous
    chain is already zero at that time. -/
theorem both_alternating_zero_implies_synchronous_zero
    (initial : State V) (t : Nat)
    (hf : IsZero (M.alternating initial false t))
    (ht : IsZero (M.alternating initial true t)) :
    IsZero (M.synchronous initial t) := by
  cases t with
  | zero => exact hf
  | succ t =>
    intro v
    by_cases hc : M.colour v = activeColour false (t + 1)
    · have h := hf v
      rw [M.splitting_succ initial false t v, ite_eq_left hc] at h
      exact h
    · have hc' : M.colour v = activeColour true (t + 1) := by
        change M.colour v = activeColour (!false) (t + 1)
        rw [activeColour_complement]
        exact bool_eq_not_of_ne hc
      have h := ht v
      rw [M.splitting_succ initial true t v, ite_eq_left hc'] at h
      exact h

/-- Eventual absorption is equivalent for synchronous dynamics and the
    pair of alternating dynamics. No finiteness is asserted unconditionally. -/
theorem eventually_zero_iff (initial : State V) :
    (∃ t, IsZero (M.synchronous initial t)) ↔
      (∃ t, IsZero (M.alternating initial false t)) ∧
      (∃ t, IsZero (M.alternating initial true t)) := by
  constructor
  · intro h
    obtain ⟨t, hz⟩ := h
    exact ⟨⟨t + 1, M.synchronous_zero_implies_alternating_next_zero initial false t hz⟩,
      ⟨t + 1, M.synchronous_zero_implies_alternating_next_zero initial true t hz⟩⟩
  · intro h
    obtain ⟨⟨tf, hf⟩, ⟨tt, ht⟩⟩ := h
    refine ⟨max tf tt, M.both_alternating_zero_implies_synchronous_zero initial (max tf tt) ?_ ?_⟩
    · exact M.alternating_zero_persists initial false hf (Nat.le_max_left tf tt)
    · exact M.alternating_zero_persists initial true ht (Nat.le_max_right tf tt)

end BipartiteSystem

/-- An explicit first-zero-time contract; existence must be proved or supplied. -/
@[expose] def FirstZero {V : Type u} (trajectory : Nat → State V) (t : Nat) : Prop :=
  IsZero (trajectory t) ∧ ∀ s, IsZero (trajectory s) → t ≤ s

private theorem least_nat_bounded (P : Nat → Prop) :
    ∀ n, (∃ k, k ≤ n ∧ P k) → ∃ k, P k ∧ ∀ m, P m → k ≤ m := by
  classical
  intro n
  induction n with
  | zero =>
    intro h
    obtain ⟨k, hk, hp⟩ := h
    have hk0 : k = 0 := by omega
    subst k
    exact ⟨0, hp, fun m _ => Nat.zero_le m⟩
  | succ n ih =>
    intro h
    by_cases he : ∃ k, k ≤ n ∧ P k
    · exact ih he
    · obtain ⟨k, hk, hp⟩ := h
      have hkn : ¬k ≤ n := fun hle => he ⟨k, hle, hp⟩
      refine ⟨k, hp, ?_⟩
      intro m hm
      by_cases hkm : k ≤ m
      · exact hkm
      · exact False.elim (he ⟨m, by omega, hm⟩)

theorem firstZero_exists {V : Type u} (trajectory : Nat → State V)
    (h : ∃ t, IsZero (trajectory t)) : ∃ t, FirstZero trajectory t := by
  obtain ⟨n, hn⟩ := h
  exact least_nat_bounded (fun t => IsZero (trajectory t)) n ⟨n, Nat.le_refl n, hn⟩

/-- The finite first-zero time, defined only when a finite zero time exists. -/
@[expose] noncomputable def firstZero {V : Type u} (trajectory : Nat → State V)
    (h : ∃ t, IsZero (trajectory t)) : Nat :=
  Classical.choose (firstZero_exists trajectory h)

theorem firstZero_spec {V : Type u} (trajectory : Nat → State V)
    (h : ∃ t, IsZero (trajectory t)) :
    FirstZero trajectory (firstZero trajectory h) :=
  Classical.choose_spec (firstZero_exists trajectory h)

namespace BipartiteSystem

variable {V : Type u} (M : BipartiteSystem V)

/-- Pathwise absorption-time comparison: `T ≤ max τ₀ τ₁ ≤ T + 1`.
    The hypotheses describe finite first-zero times, not probabilistic claims. -/
theorem absorption_times (initial : State V) {T tf tt : Nat}
    (hT : FirstZero (M.synchronous initial) T)
    (hf : FirstZero (M.alternating initial false) tf)
    (ht : FirstZero (M.alternating initial true) tt) :
    T ≤ max tf tt ∧ max tf tt ≤ T + 1 := by
  constructor
  · apply hT.2
    apply M.both_alternating_zero_implies_synchronous_zero initial (max tf tt)
    · exact M.alternating_zero_persists initial false hf.1 (Nat.le_max_left tf tt)
    · exact M.alternating_zero_persists initial true ht.1 (Nat.le_max_right tf tt)
  · have hfb : tf ≤ T + 1 := hf.2 (T + 1)
      (M.synchronous_zero_implies_alternating_next_zero initial false T hT.1)
    have htb : tt ≤ T + 1 := ht.2 (T + 1)
      (M.synchronous_zero_implies_alternating_next_zero initial true T hT.1)
    exact Nat.max_le.mpr ⟨hfb, htb⟩

theorem firstZero_bracket (initial : State V)
    (hT : ∃ t, IsZero (M.synchronous initial t))
    (hf : ∃ t, IsZero (M.alternating initial false t))
    (ht : ∃ t, IsZero (M.alternating initial true t)) :
    firstZero (M.synchronous initial) hT ≤
        max (firstZero (M.alternating initial false) hf)
          (firstZero (M.alternating initial true) ht) ∧
      max (firstZero (M.alternating initial false) hf)
        (firstZero (M.alternating initial true) ht) ≤
          firstZero (M.synchronous initial) hT + 1 :=
  M.absorption_times initial
    (firstZero_spec (M.synchronous initial) hT)
    (firstZero_spec (M.alternating initial false) hf)
    (firstZero_spec (M.alternating initial true) ht)

/-- A finite synchronous absorption witness is enough to obtain all three
    finite first-zero times and the one-slot bracket. -/
theorem finite_absorption_comparison (initial : State V)
    (h : ∃ t, IsZero (M.synchronous initial t)) :
    ∃ T tf tt,
      FirstZero (M.synchronous initial) T ∧
      FirstZero (M.alternating initial false) tf ∧
      FirstZero (M.alternating initial true) tt ∧
      T ≤ max tf tt ∧ max tf tt ≤ T + 1 := by
  obtain ⟨hf, ht⟩ := (M.eventually_zero_iff initial).mp h
  obtain ⟨T, hT⟩ := firstZero_exists (M.synchronous initial) h
  obtain ⟨tf, htf⟩ := firstZero_exists (M.alternating initial false) hf
  obtain ⟨tt, htt⟩ := firstZero_exists (M.alternating initial true) ht
  obtain ⟨hl, hu⟩ := M.absorption_times initial hT htf htt
  exact ⟨T, tf, tt, hT, htf, htt, hl, hu⟩

end BipartiteSystem
end MathResearchAnalysis.BipartiteDynamics


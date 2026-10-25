module
public import MathResearchAnalysis.EventTrace
public import Mathlib.Tactic
set_option autoImplicit false
/-! Signed observable telescoping for an arbitrary deterministic update
machine on a finite strictly time-ordered identity word. The word is newest
first, so the genuine chronological execution reverses it exactly once. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MachineTraceTelescope
universe u v
variable {Label : Type u} {A : Type v}

theorem telescope (time : Label → Real) (update : Label → A → A)
    (F : A → Real) (initial : A) (w : List Label)
    (hw : w.Pairwise (fun a b => time b < time a)) :
    F (EventTrace.execute update w.reverse initial) - F initial =
    (w.map (fun e =>
      F (update e (EventTrace.execute update
        (w.filter (fun f => decide (time f < time e))).reverse initial)) -
      F (EventTrace.execute update
        (w.filter (fun f => decide (time f < time e))).reverse initial))).sum := by
  classical
  induction w with
  | nil => simp
  | cons e w ih =>
    obtain ⟨he, hw⟩ := List.pairwise_cons.mp hw
    have hfilter : (e :: w).filter (fun f => decide (time f < time e)) = w := by
      simp only [List.filter_cons, lt_self_iff_false, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      exact List.filter_eq_self.mpr (fun f hf => decide_eq_true (he f hf))
    have htail : w.map (fun f =>
        F (update f (EventTrace.execute update
          ((e :: w).filter (fun g => decide (time g < time f))).reverse initial)) -
        F (EventTrace.execute update
          ((e :: w).filter (fun g => decide (time g < time f))).reverse initial)) =
      w.map (fun f =>
        F (update f (EventTrace.execute update
          (w.filter (fun g => decide (time g < time f))).reverse initial)) -
        F (EventTrace.execute update
          (w.filter (fun g => decide (time g < time f))).reverse initial)) := by
      apply List.map_congr_left
      intro f hf
      have hnot : ¬ time e < time f := not_lt_of_gt (he f hf)
      simp only [List.filter_cons, decide_eq_false hnot, Bool.false_eq_true, ↓reduceIte]
    rw [List.reverse_cons, EventTrace.execute_append, EventTrace.execute_cons,
      EventTrace.execute_nil, List.map_cons, List.sum_cons, hfilter, htail, ← ih hw]
    ring
end MathResearchAnalysis.MachineTraceTelescope

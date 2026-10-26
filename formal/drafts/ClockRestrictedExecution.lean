module

public import MathResearchAnalysis.ClockWordRestriction
public import MathResearchAnalysis.MarkedEventTrace
public import MathResearchAnalysis.MixedSquareModel
public import MathResearchAnalysis.SquareInclusion

set_option autoImplicit false

/-!
# Relating a restricted execution to its genuine larger marked event word

The generic induction executes each retained event on both machines and every
outside event on the larger machine alone. The finite relation's single-step
conditions are structural hypotheses of the generic lemma. Actual square
geometry discharges them in the concrete square comparison below.
The original event identity supplies both marks, with no mark resampling.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClockRestrictedExecution

open SquareTasks (Vertex)
open ClockWordMarks (Event)
open ClockSampleRestriction (eventι projectMarks)
open ClockWordRestriction (retained)

universe u v w x

/-- A filtered larger word and its smaller preimage execute in lockstep on
retained events. The smaller state stays fixed on outside events. -/
theorem execute_related_of_filter_map {SmallEvent : Type u} {BigEvent : Type v}
    {SmallState : Type w} {BigState : Type x}
    (eventMap : SmallEvent → BigEvent) (keep : BigEvent → Bool)
    (smallStep : SmallEvent → SmallState → SmallState)
    (bigStep : BigEvent → BigState → BigState) (R : SmallState → BigState → Prop)
    (hinside : ∀ e a b, R a b → R (smallStep e a) (bigStep (eventMap e) b))
    (houtside : ∀ e, keep e = false → ∀ a b, R a b → R a (bigStep e b))
    (smallWord : List SmallEvent) (bigWord : List BigEvent)
    (hwords : smallWord.map eventMap = bigWord.filter keep)
    (a : SmallState) (b : BigState) (hrel : R a b) :
    R (EventTrace.execute smallStep smallWord a) (EventTrace.execute bigStep bigWord b) := by
  induction bigWord generalizing smallWord a b with
  | nil =>
    have hnil : smallWord = [] := by simpa only [List.filter_nil,List.map_eq_nil_iff] using hwords
    subst smallWord
    exact hrel
  | cons e bigWord ih =>
    cases hkeep : keep e with
    | false =>
      have htail : smallWord.map eventMap = bigWord.filter keep := by
        simpa only [List.filter_cons,hkeep,Bool.false_eq_true,ite_false] using hwords
      exact ih smallWord htail a (bigStep e b) (houtside e hkeep a b hrel)
    | true =>
      cases smallWord with
      | nil =>
        simp only [List.map_nil,List.filter_cons,hkeep,ite_true] at hwords
        cases hwords
      | cons smallEvent smallWord =>
        have hcons : eventMap smallEvent :: smallWord.map eventMap = e :: bigWord.filter keep := by
          simpa only [List.map_cons,List.filter_cons,hkeep,ite_true] using hwords
        obtain ⟨heq,htail⟩ := List.cons.inj hcons
        simp only [EventTrace.execute_cons]
        apply ih smallWord htail (smallStep smallEvent a) (bigStep e b)
        simpa only [heq] using hinside smallEvent a b hrel

/-- The literal retained event test excludes exactly sites outside the site
injection. This inference preserves the ring index and needs no inverse map. -/
theorem outside_site_of_not_retained {n m : Nat} (ι : Vertex n → Vertex m)
    (e : Event m) (he : retained ι e = false) : ∀ v : Vertex n, ι v ≠ e.1 := by
  intro v hv
  have hmem : e ∈ Set.range (eventι ι) :=
    ⟨(v,e.2),Prod.ext hv rfl⟩
  have htrue := (ClockWordRestriction.retained_eq_true_iff ι e).2 hmem
  rw [he] at htrue
  exact Bool.false_ne_true htrue

/-- Concrete zero-boundary and mixed-boundary executions use the same mark at
each retained original identity. Only the finite single-step compatibility
conditions remain generic; no probabilistic conclusion is supplied. -/
theorem original_mixed_execute_related {n m : Nat} (ι : Vertex n → Vertex m)
    (R : SquareSpin.Config n → MixedSquareModel.Config m → Prop)
    (hinside : ∀ v tie f g, R f g →
      R (SquareSpin.cellUpdate f v tie) (MixedSquareModel.cellUpdate g (ι v) tie))
    (houtside : ∀ u tie f g, (∀ v, ι v ≠ u) → R f g →
      R f (MixedSquareModel.cellUpdate g u tie))
    (η : Event m → Bool) (smallWord : List (Event n)) (bigWord : List (Event m))
    (hwords : smallWord.map (eventι ι) = bigWord.filter (retained ι))
    (f : SquareSpin.Config n) (g : MixedSquareModel.Config m) (hrel : R f g) :
    R (MarkedEventTrace.execute (projectMarks ι η) smallWord f)
      (MixedSquareModel.execute η bigWord g) := by
  apply execute_related_of_filter_map (eventι ι) (retained ι)
    (SquareSpin.updateEvent (projectMarks ι η)) (MixedSquareModel.updateEvent η) R
    (fun e a b hab => hinside e.1 (η (eventι ι e)) a b hab)
    (fun e he a b hab => houtside e.1 (η e) a b
      (outside_site_of_not_retained ι e he) hab)
    smallWord bigWord hwords f g hrel

/-- Actual square geometry discharges every single-step compatibility input.
The final finite-word comparison retains only the exact word-filter identity
and the initial restriction relation, not an assumed process domination. -/
theorem square_execute_rel {n m : Nat} (hnm : n ≤ m)
    (η : Event m → Bool) (smallWord : List (Event n)) (bigWord : List (Event m))
    (hwords : smallWord.map (eventι (SquareInclusion.site hnm)) =
      bigWord.filter (retained (SquareInclusion.site hnm)))
    (f : SquareSpin.Config n) (g : MixedSquareModel.Config m)
    (hrel : SquareInclusion.Rel hnm f g) :
    SquareInclusion.Rel hnm
      (MarkedEventTrace.execute (projectMarks (SquareInclusion.site hnm) η) smallWord f)
      (MixedSquareModel.execute η bigWord g) :=
  original_mixed_execute_related (SquareInclusion.site hnm) (SquareInclusion.Rel hnm)
    (fun v tie _ _ hfg => SquareInclusion.cellUpdate_rel hnm hfg v tie)
    (fun u tie _ _ hout hfg => SquareInclusion.outside_cellUpdate_rel hnm hfg u tie hout)
    η smallWord bigWord hwords f g hrel

end MathResearchAnalysis.ClockRestrictedExecution

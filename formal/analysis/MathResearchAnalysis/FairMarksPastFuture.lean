module

public import MathResearchAnalysis.FairMarksTransport

set_option autoImplicit false

/-!
# The used positive past and the complete fresh future fair-mark field

The observed past at time `s` consists of slots `1, ..., s`. The reindexed
future keeps the unused time-zero slot at zero and sends positive slots to
`s+1, s+2, ...`. Its entire field therefore has the original product law and
is independent of the whole used past, even for infinite site types.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace MathResearchAnalysis.FairMarksPastFuture

variable {I : Type*}

def pastIndex (s : Nat) (p : I × Fin s) : I × Nat := (p.1, p.2.val + 1)

def futureIndex (s : Nat) (p : I × Nat) : I × Nat :=
  (p.1, if p.2 = 0 then 0 else s + p.2)

def past (s : Nat) (η : FairMarks.Sample (I × Nat)) : (I × Fin s) → Bool :=
  FairMarksTransport.pullback (pastIndex s) η

def future (s : Nat) (η : FairMarks.Sample (I × Nat)) : FairMarks.Sample (I × Nat) :=
  FairMarksTransport.pullback (futureIndex s) η

theorem futureIndex_injective (s : Nat) : Function.Injective (futureIndex (I := I) s) := by
  rintro ⟨v, j⟩ ⟨w, k⟩ h
  have hv : v = w := congrArg Prod.fst h
  have ht : (if j = 0 then 0 else s + j) = (if k = 0 then 0 else s + k) :=
    congrArg Prod.snd h
  have hj : j = k := by
    split_ifs at ht <;> omega
  exact Prod.ext hv hj

theorem past_measurable (s : Nat) : Measurable (past (I := I) s) :=
  FairMarksTransport.pullback_measurable (pastIndex s)

theorem future_measurable (s : Nat) : Measurable (future (I := I) s) :=
  FairMarksTransport.pullback_measurable (futureIndex s)

theorem map_future (s : Nat) :
    Measure.map (future (I := I) s) (FairMarks.markMeasure (I × Nat)) =
      FairMarks.markMeasure (I × Nat) :=
  FairMarksTransport.map_pullback (futureIndex s) (futureIndex_injective s)

theorem past_future_indices_disjoint (s : Nat) :
    Disjoint (Set.range (pastIndex (I := I) s)) (Set.range (futureIndex (I := I) s)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨⟨v, j⟩, hp⟩ ⟨⟨w, k⟩, hf⟩
  have ht : j.val + 1 = (if k = 0 then 0 else s + k) :=
    congrArg Prod.snd (hp.trans hf.symm)
  have hj := j.isLt
  split_ifs at ht; omega

theorem past_future_independent (s : Nat) :
    IndepFun (past (I := I) s) (future (I := I) s) (FairMarks.markMeasure (I × Nat)) := by
  let P := Set.range (pastIndex (I := I) s)
  let F := Set.range (futureIndex (I := I) s)
  have hind : IndepFun (fun η : FairMarks.Sample (I × Nat) => fun i : P => η i.1)
      (fun η : FairMarks.Sample (I × Nat) => fun i : F => η i.1)
      (FairMarks.markMeasure (I × Nat)) :=
    (FairMarks.marks_independent (I := I × Nat)).indepFun_set P F
      (past_future_indices_disjoint s) (fun i => measurable_pi_apply i)
  let readPast : (P → Bool) → (I × Fin s) → Bool :=
    fun ξ p => ξ ⟨pastIndex s p, Set.mem_range_self p⟩
  let readFuture : (F → Bool) → (I × Nat) → Bool :=
    fun ξ p => ξ ⟨futureIndex s p, Set.mem_range_self p⟩
  have hmPast : Measurable readPast :=
    measurable_pi_iff.mpr fun p =>
      measurable_pi_apply (⟨pastIndex s p, Set.mem_range_self p⟩ : P)
  have hmFuture : Measurable readFuture :=
    measurable_pi_iff.mpr fun p =>
      measurable_pi_apply (⟨futureIndex s p, Set.mem_range_self p⟩ : F)
  exact hind.comp hmPast hmFuture

end MathResearchAnalysis.FairMarksPastFuture

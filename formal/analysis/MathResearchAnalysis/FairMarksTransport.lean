module

public import MathResearchAnalysis.FairMarks

set_option autoImplicit false

/-!
# Transport of the complete independent fair-mark field

Restricting a fair Bernoulli product field along any injective map of its
indices preserves its full product law. The index types need no measurable
space or countability assumption. This includes infinite subfields, rather
than only finite collections of marks.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace MathResearchAnalysis.FairMarksTransport

variable {I J : Type*}

def pullback (f : J → I) (η : FairMarks.Sample I) : FairMarks.Sample J :=
  fun j => η (f j)

theorem pullback_measurable (f : J → I) : Measurable (pullback f) :=
  measurable_pi_iff.mpr fun j => measurable_pi_apply (f j)

theorem map_pullback (f : J → I) (hf : Function.Injective f) :
    Measure.map (pullback f) (FairMarks.markMeasure I) = FairMarks.markMeasure J := by
  exact Measure.map_infinitePi_infinitePi_of_inj hf

theorem pullback_hasLaw (f : J → I) (hf : Function.Injective f) :
    HasLaw (pullback f) (FairMarks.markMeasure J) (FairMarks.markMeasure I) where
  aemeasurable := (pullback_measurable f).aemeasurable
  map_eq := map_pullback f hf

end MathResearchAnalysis.FairMarksTransport

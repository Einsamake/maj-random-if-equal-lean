module

public import MathResearchAnalysis.PerturbationSymmetry
public import MathResearchAnalysis.SquareGridEmbedding

set_option autoImplicit false

/-!
# Exact finite-square representatives of original finite perturbations

Every initial state at original perturbation distance exactly `N ≥ 2` is a
translate of a zero-extended finite pattern or its spin complement. The
pattern itself still has distance exactly `N`. The finite implementation
parameter is `N - 2`, because its square has side `N - 2 + 2 = N`.

This geometric reduction does not select the full-square initial state and
does not assert an expectation or a recovery-time probability bound.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.PerturbationNormalization

open InfiniteGridModel InfiniteGridTranslation InfiniteGridComplement
open PerturbationGeometry PerturbationSymmetry

abbrev Site := InfiniteGridModel.Site
abbrev Config := InfiniteGridModel.Config

/-- Move a containing square's lower-left corner to the origin. -/
def normalize (a : Site) (f : Config) : Config := translate (-a.1, -a.2) f

theorem translate_normalize (a : Site) (f : Config) :
    translate a (normalize a f) = f := translate_translate_neg a f

theorem normalize_supported (N : Nat) (a : Site) (f : Config)
    (h : SupportedTranslated N a f) : Supported N (normalize a f) := by
  apply (supported_translate_iff N a (normalize a f)).mp
  rw [translate_normalize]
  exact h

/-- A genuine finite pattern represents every zero-background state fitting a square. -/
theorem exists_square_of_fits_false (N : Nat) (hN : 2 ≤ N) (f : Config)
    (h : Fits (difference f false) N) :
    ∃ a : Site, ∃ g : SquareSpin.Config (N - 2),
      f = translate a (SquareGridEmbedding.extend (N - 2) g) := by
  obtain ⟨a, ha⟩ := (fits_difference_false_iff f N).mp h
  have hs : Supported (N - 2 + 2) (normalize a f) := by
    rw [original_side_sub_two N hN]
    exact normalize_supported N a f ha
  refine ⟨a, SquareGridEmbedding.restrict (N - 2) (normalize a f), ?_⟩
  rw [SquareGridEmbedding.extend_restrict (N - 2) (normalize a f) hs]
  exact (translate_normalize a f).symm

theorem complement_complement (f : Config) :
    complementConfig (complementConfig f) = f := by
  funext z
  simp only [complementConfig, Bool.not_not]

theorem complement_translate (a : Site) (f : Config) :
    complementConfig (translate a f) = translate a (complementConfig f) := rfl

/-- Exact-distance reduction for both homogeneous backgrounds, with no worst-state premise. -/
theorem exists_normal_form_exact (N : Nat) (hN : 2 ≤ N) (f : Config)
    (hDistance : distance f = (N : ℕ∞)) :
    ∃ a : Site, ∃ b : Bool, ∃ g : SquareSpin.Config (N - 2),
      f = translate a (if b then complementConfig (SquareGridEmbedding.extend (N - 2) g)
        else SquareGridEmbedding.extend (N - 2) g) ∧
      distance (SquareGridEmbedding.extend (N - 2) g) = (N : ℕ∞) := by
  obtain ⟨b, _, hdiam⟩ := (distance_eq_nat_iff f N).mp hDistance
  cases b with
  | false =>
    have hfit := (diameter_le_nat_iff (difference f false) N).mp hdiam.le
    obtain ⟨a, g, hf⟩ := exists_square_of_fits_false N hN f hfit
    refine ⟨a, false, g, ?_, ?_⟩
    · exact hf
    · calc
        distance (SquareGridEmbedding.extend (N - 2) g) =
            distance (translate a (SquareGridEmbedding.extend (N - 2) g)) :=
          (distance_translate a _).symm
        _ = distance f := congrArg distance hf.symm
        _ = (N : ℕ∞) := hDistance
  | true =>
    have hcomp : difference (complementConfig f) false = difference f true := by
      simpa only [Bool.not_true] using difference_complement f true
    have hfit : Fits (difference (complementConfig f) false) N := by
      rw [hcomp]
      exact (diameter_le_nat_iff (difference f true) N).mp hdiam.le
    obtain ⟨a, g, hf⟩ := exists_square_of_fits_false N hN (complementConfig f) hfit
    refine ⟨a, true, g, ?_, ?_⟩
    · have he := congrArg complementConfig hf
      simpa only [complement_complement, complement_translate, ↓reduceIte] using he
    · calc
        distance (SquareGridEmbedding.extend (N - 2) g) =
            distance (translate a (SquareGridEmbedding.extend (N - 2) g)) :=
          (distance_translate a _).symm
        _ = distance (complementConfig f) := congrArg distance hf.symm
        _ = distance f := distance_complement f
        _ = (N : ℕ∞) := hDistance

end MathResearchAnalysis.PerturbationNormalization

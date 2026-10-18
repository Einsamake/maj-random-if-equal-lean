module

public import MathResearchAnalysis.PerturbationNormalization
public import MathResearchAnalysis.HomogeneousRecoveryTime

set_option autoImplicit false

/-!
# Exact recovery at original perturbation diameter one

A singleton half-open containing square has only one lattice site. Its four
neighbours are zero, while all exterior outputs remain zero by the already
proved containing-square invariant. Translation and simultaneous state/mark
complement extend the statement to both finite-perturbation backgrounds.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.SmallDiameterRecovery

open InfiniteGridModel InfiniteGridTranslation InfiniteGridComplement
open PerturbationGeometry PerturbationSymmetry

abbrev Config := InfiniteGridModel.Config
abbrev Sample := InfiniteGridRandomDynamics.Sample
abbrev Site := InfiniteGridModel.Site
abbrev Marks := InfiniteGridModel.Marks
abbrev zeroConfig : Config := fun _ => false

theorem synchronous_one_zero_of_supported (marks : Marks) (initial : Config)
    (hSupport : Supported 1 initial) : synchronous marks initial 1 = zeroConfig := by
  have hsp := synchronous_supported marks 1 initial hSupport 1
  funext z
  by_cases hz : Inside 1 z
  · have hz0 : z = (0, 0) := by
      apply Prod.ext <;> dsimp [Inside] at hz <;> omega
    subst z
    have hn : initial (north (0, 0)) = false :=
      hSupport _ (by simp only [Inside, north]; omega)
    have he : initial (east (0, 0)) = false :=
      hSupport _ (by simp only [Inside, east]; omega)
    have hs : initial (south (0, 0)) = false :=
      hSupport _ (by simp only [Inside, south]; omega)
    have hw : initial (west (0, 0)) = false :=
      hSupport _ (by simp only [Inside, west]; omega)
    change update marks 1 (0, 0) initial = false
    simp only [update, hn, he, hs, hw, majority4_zero]
  · exact hsp z hz

theorem synchronous_one_zero_of_supported_translated (marks : Marks) (a : Site)
    (initial : Config) (hSupport : SupportedTranslated 1 a initial) :
    synchronous marks initial 1 = zeroConfig := by
  have hnorm := PerturbationNormalization.normalize_supported 1 a initial hSupport
  have hzero := synchronous_one_zero_of_supported
    (translateMarks (-a.1, -a.2) marks) _ hnorm
  change synchronous (translateMarks (-a.1, -a.2) marks)
    (translate (-a.1, -a.2) initial) 1 = zeroConfig at hzero
  rw [synchronous_translate] at hzero
  exact (translate_eq_zero_iff (-a.1, -a.2) _).mp hzero

theorem synchronous_one_homogeneous_of_distance_one (initial : Config)
    (hDistance : distance initial = (1 : ℕ∞)) (η : Sample) :
    HomogeneousRecoveryTime.Homogeneous
      (InfiniteGridRandomDynamics.synchronous initial 1 η) := by
  obtain ⟨b, _, hdiam⟩ := (distance_eq_nat_iff initial 1).mp hDistance
  cases b with
  | false =>
    obtain ⟨a, ha⟩ := (fits_difference_false_iff initial 1).mp
      ((diameter_le_nat_iff _ 1).mp hdiam.le)
    exact Or.inl (synchronous_one_zero_of_supported_translated
      (InfiniteGridRandomDynamics.marks η) a initial ha)
  | true =>
    have hc : difference (complementConfig initial) false = difference initial true := by
      simpa only [Bool.not_true] using difference_complement initial true
    have hfit : Fits (difference (complementConfig initial) false) 1 := by
      rw [hc]
      exact (diameter_le_nat_iff _ 1).mp hdiam.le
    obtain ⟨a, ha⟩ := (fits_difference_false_iff (complementConfig initial) 1).mp hfit
    have hz := synchronous_one_zero_of_supported_translated
      (complementMarks (InfiniteGridRandomDynamics.marks η)) a (complementConfig initial) ha
    rw [synchronous_complement] at hz
    exact (HomogeneousRecoveryTime.homogeneous_complement_iff _).mp (Or.inl hz)

private theorem distance_constant (b : Bool) : distance (fun _ => b) = 0 := by
  have he : difference (fun _ => b) b = ∅ := by
    ext z
    simp only [difference, Set.mem_ofPred_eq, ne_eq, not_true_eq_false,
      Set.mem_empty_iff_false]
  have hf : FinitePerturbation (fun _ => b) b := by
    unfold FinitePerturbation
    rw [he]
    exact Set.finite_empty
  rw [distance_of_finite_background _ b hf]
  exact (diameter_eq_zero_iff _).mpr he

theorem distance_one_not_homogeneous (initial : Config)
    (hDistance : distance initial = (1 : ℕ∞)) :
    ¬ HomogeneousRecoveryTime.Homogeneous initial := by
  rintro (rfl | rfl)
  · have hzero := distance_constant false
    rw [hzero] at hDistance
    exact zero_ne_one hDistance
  · have hzero := distance_constant true
    rw [hzero] at hDistance
    exact zero_ne_one hDistance

theorem synchronous_eq_one_of_distance_one (initial : Config)
    (hDistance : distance initial = (1 : ℕ∞)) (η : Sample) :
    HomogeneousRecoveryTime.synchronous initial η = 1 := by
  change ExtendedRecoveryTime.time (HomogeneousRecoveryTime.hitState initial) false η =
    ((1 : Nat) : ℕ∞)
  rw [ExtendedRecoveryTime.time_eq_nat_iff]
  constructor
  · exact (HomogeneousRecoveryTime.hitState_eq_false_iff initial 1 η).mpr
      (synchronous_one_homogeneous_of_distance_one initial hDistance η)
  · intro s hs hhit
    have hs0 : s = 0 := by omega
    subst s
    exact distance_one_not_homogeneous initial hDistance
      ((HomogeneousRecoveryTime.hitState_eq_false_iff initial 0 η).mp hhit)

end MathResearchAnalysis.SmallDiameterRecovery

module
public import UniformLower
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Packing
open MathResearchAnalysis MeasureTheory
open PerturbationSymmetry (squareConfig)
open scoped ENNReal

abbrev cdf (N k : ℕ) : ℝ := InfiniteGridRandomDynamics.measure.real
  {η | InfiniteGridRecoveryTime.synchronous (squareConfig N) η ≤ (k : ℕ∞)}

theorem cdf_add_survival (N k : ℕ) : cdf N k + survival N k = 1 := by
  have he (η) := HomogeneousRecoveryTime.synchronous_eq_zero_background N (squareConfig N)
    (OriginalQuadraticLower.square_supported_mono (le_refl N)) η
  simp only [cdf,survival,he]
  let E := {η | (k : ℕ∞) < InfiniteGridRecoveryTime.synchronous (squareConfig N) η}
  have h : {η | InfiniteGridRecoveryTime.synchronous (squareConfig N) η ≤ (k : ℕ∞)} = Eᶜ := by
    ext; simp [E]
  rw [h, measureReal_compl (InfiniteGridRecoveryTime.measurableSet_synchronous_tail _ _)]
  simp

private theorem grid_state_mono {f g : InfiniteGridModel.Config} (h : f ≤ g)
    (η : InfiniteGridRandomDynamics.Sample) (k : ℕ) :
    InfiniteGridRandomDynamics.synchronous f k η ≤ InfiniteGridRandomDynamics.synchronous g k η := by
  induction k with
  | zero => exact h
  | succ k ih =>
    intro v
    apply InfiniteGridModel.majority4_monotone <;> apply ih

abbrev Block (d : ℕ) := Fin d × Fin d

def event {d : ℕ} (n : ℕ) (p : Block d × SquareSpin.Event n) : InfiniteGridRandomDynamics.Event :=
  (((p.1.1.val*(n+2)+p.2.1.1.val : ℕ), (p.1.2.val*(n+2)+p.2.1.2.val : ℕ)),p.2.2)

private theorem digits {a b x y m : ℕ} (hx : x < m) (hy : y < m)
    (h : a*m+x = b*m+y) : a=b ∧ x=y := by
  have ordered (u v i j : ℕ) (hi : i < m) (hh : u*m+i = v*m+j) : v ≤ u := by
    by_contra! hlt
    have hstep := Nat.mul_le_mul_right m (show u+1 ≤ v from hlt)
    rw [Nat.add_mul,one_mul] at hstep
    omega
  have hab := le_antisymm (ordered b a y x hy h.symm) (ordered a b x y hx h)
  exact ⟨hab, by simpa [hab] using h⟩

theorem event_injective (d n : ℕ) : Function.Injective (event (d := d) n) := by
  rintro ⟨⟨a,b⟩,⟨⟨x,y⟩,t⟩⟩ ⟨⟨c,e⟩,⟨⟨z,w⟩,u⟩⟩ h
  have hx := congrArg (fun p : InfiniteGridRandomDynamics.Event => p.1.1) h
  have hy := congrArg (fun p : InfiniteGridRandomDynamics.Event => p.1.2) h
  have ht := congrArg (fun p : InfiniteGridRandomDynamics.Event => p.2) h
  simp only [event,Nat.cast_inj] at hx hy
  obtain ⟨ha,hxz⟩ := digits x.isLt z.isLt hx
  obtain ⟨hb,hyw⟩ := digits y.isLt w.isLt hy
  exact Prod.ext (Prod.ext (Fin.ext ha) (Fin.ext hb))
    (Prod.ext (Prod.ext (Fin.ext hxz) (Fin.ext hyw)) ht)

def blocks (d n : ℕ) (η : InfiniteGridRandomDynamics.Sample) (b : Block d) :
    SquareRandomDynamics.Sample n := fun e => η (event n (b,e))

theorem blocks_measurable (d n : ℕ) : Measurable (blocks d n) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem blocks_map (d n : ℕ) : InfiniteGridRandomDynamics.measure.map (blocks d n) =
    Measure.pi (fun _ : Block d => SquareRandomDynamics.measure n) := by
  let c := MeasurableEquiv.curry (Block d) (SquareSpin.Event n) Bool
  have hf : blocks d n = c ∘ FairMarksTransport.pullback (event (d := d) n) := rfl
  rw [hf,InfiniteGridRandomDynamics.measure,← Measure.map_map c.measurable (FairMarksTransport.pullback_measurable _),
    FairMarksTransport.map_pullback _ (event_injective d n)]
  exact (Measure.infinitePi_map_curry (fun (_ : Block d) (_ : SquareSpin.Event n) => FairMarks.fair)).trans
    (Measure.infinitePi_eq_pi _)

private theorem restricted_time_le {N d n : ℕ} (hfit : d*(n+2) ≤ N)
    (b : Block d) (η : InfiniteGridRandomDynamics.Sample) (k : ℕ)
    (hzero : InfiniteGridRecoveryTime.synchronous (squareConfig N) η ≤ (k : ℕ∞)) :
    SquareRecoveryTime.synchronous n (SquarePWMeasure.topConfig n) (blocks d n η b) ≤ (k : ℕ∞) := by
  let a : InfiniteGridModel.Site := (-(b.1.val*(n+2) : ℕ), -(b.2.val*(n+2) : ℕ))
  let ξ := InfiniteGridTranslationLaw.translateSample a η
  have he : SquareGridLaw.restrictSample n ξ = blocks d n η b := by
    funext e
    apply congrArg η
    apply Prod.ext
    · apply Prod.ext <;> dsimp [ξ,a,InfiniteGridTranslationLaw.eventShift,InfiniteGridTranslation.shift,
        SquareGridLaw.eventEmbedding,SquareGridEmbedding.embed,event] <;> ring
    · rfl
  have hmono : squareConfig (n+2) ≤ InfiniteGridTranslation.translate a (squareConfig N) := by
    intro v
    apply Bool.le_iff_imp.mpr
    simp only [squareConfig,InfiniteGridTranslation.translate,decide_eq_true_eq]
    intro hv
    have hx := Nat.mul_le_mul_right (n+2) (show b.1.val+1 ≤ d from b.1.isLt)
    have hy := Nat.mul_le_mul_right (n+2) (show b.2.val+1 ≤ d from b.2.isLt)
    rw [Nat.add_mul,one_mul] at hx hy
    have hx' : (b.1.val*(n+2) : ℕ)+(n+2) ≤ N := hx.trans hfit
    have hy' : (b.2.val*(n+2) : ℕ)+(n+2) ≤ N := hy.trans hfit
    have hxInt : (b.1.val : ℤ)*((n : ℤ)+2)+(n+2) ≤ N := by exact_mod_cast hx'
    have hyInt : (b.2.val : ℤ)*((n : ℤ)+2)+(n+2) ≤ N := by exact_mod_cast hy'
    have hxpos : (0 : ℤ) ≤ (b.1.val : ℤ)*((n : ℤ)+2) := by positivity
    have hypos : (0 : ℤ) ≤ (b.2.val : ℤ)*((n : ℤ)+2) := by positivity
    dsimp [InfiniteGridModel.Inside,InfiniteGridTranslation.shift,a] at hv ⊢
    omega
  rw [← he,← SquareGridLaw.synchronous_recovery_eq,OriginalQuadraticLower.extend_top_eq_square,
    InfiniteGridRecoveryTime.synchronous_le_nat_iff]
  have hg := grid_state_mono hmono ξ k
  have hbig := (InfiniteGridRecoveryTime.synchronous_le_nat_iff _ _ _).mp hzero
  rw [InfiniteGridTranslationLaw.synchronous_translate, hbig] at hg
  exact funext fun v => Bool.eq_false_iff.mpr fun h => by
    have hle := hg v
    rw [h] at hle
    exact (by decide : ¬ true ≤ false) hle

/-- Multiplicative lower-tail estimate for the original synchronous grid; side lengths count sites. -/
theorem packed_cdf {N d n : ℕ} (hfit : d*(n+2) ≤ N) (k : ℕ) :
    cdf N k ≤ (cdf (n+2) k)^(d^2) := by
  classical
  let E := {ξ | SquareRecoveryTime.synchronous n (SquarePWMeasure.topConfig n) ξ ≤ (k : ℕ∞)}
  have hE : MeasurableSet E := ExtendedRecoveryTime.measurableSet_time_le_nat
    (SquareRandomDynamics.synchronous n (SquarePWMeasure.topConfig n)) (SquareRandomComparison.zeroConfig n)
    (SquareRandomDynamics.synchronous_measurable _ _) k
  let R := Set.univ.pi (fun _ : Block d => E)
  have hR : MeasurableSet R := MeasurableSet.pi (Set.to_countable _) fun _ _ => hE
  have hsub : {η | InfiniteGridRecoveryTime.synchronous (squareConfig N) η ≤ (k : ℕ∞)} ⊆
      (blocks d n) ⁻¹' R := by
    intro η hη b _
    exact restricted_time_le hfit b η k hη
  have hrect : InfiniteGridRandomDynamics.measure ((blocks d n) ⁻¹' R) =
      ((SquareRandomDynamics.measure n) E)^(d^2) := by
    rw [← Measure.map_apply (blocks_measurable d n) hR,blocks_map,Measure.pi_pi]
    simp [Fintype.card_prod,pow_two]
  have hsingle : (SquareRandomDynamics.measure n).real E = cdf (n+2) k := by
    change _ = InfiniteGridRandomDynamics.measure.real _
    rw [← OriginalQuadraticLower.extend_top_eq_square n]
    simp_rw [SquareGridLaw.synchronous_recovery_eq]
    exact (SquareGridLaw.restrictSample_real_preimage n E hE).symm
  calc
    _ ≤ InfiniteGridRandomDynamics.measure.real ((blocks d n) ⁻¹' R) := measureReal_mono hsub
    _ = ((SquareRandomDynamics.measure n).real E)^(d^2) := by
      simp only [Measure.real,hrect,ENNReal.toReal_pow]
    _ = _ := by rw [hsingle]

end MathResearchLower.Packing

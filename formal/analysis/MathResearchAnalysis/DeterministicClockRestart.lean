module
public import MathResearchAnalysis.ClockEndpointSurvival
public import MathResearchAnalysis.ClockCounting
public import MathResearchAnalysis.ExponentialMemoryless
public import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false

/-! Deterministic-time restart for the actual marked exponential clock sample. -/
@[expose] public noncomputable section

namespace MathResearchAnalysis.DeterministicClockRestart
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open ClockWordMarks (Site Event Sample)

private theorem split_product {I J K α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (j : J → I) (k : K → I)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hd : Disjoint (range j) (range k)) :
    (Measure.infinitePi (fun _ : I => ν)).map
        (fun ω => (fun a => ω (j a), fun b => ω (k b))) =
      (Measure.infinitePi fun _ : J => ν).prod (Measure.infinitePi fun _ : K => ν) := by
  let μ := Measure.infinitePi (fun _ : I => ν)
  have hi : iIndepFun (fun i (ω : I → α) => ω i) μ :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have h := hi.indepFun_set (range j) (range k) hd (fun i => measurable_pi_apply i)
  let jl (a : J) : range j := ⟨j a, mem_range_self a⟩
  let kr (b : K) : range k := ⟨k b, mem_range_self b⟩
  have hp := h.comp
    (show Measurable (fun (ω : range j → α) a => ω (jl a)) from
      measurable_pi_iff.mpr (fun a => measurable_pi_apply (jl a)))
    (show Measurable (fun (ω : range k → α) b => ω (kr b)) from
      measurable_pi_iff.mpr (fun b => measurable_pi_apply (kr b)))
  have hJ : Measurable (fun (ω : I → α) (a : J) => ω (j a)) :=
    measurable_pi_iff.mpr (fun a => measurable_pi_apply (j a))
  have hK : Measurable (fun (ω : I → α) (b : K) => ω (k b)) :=
    measurable_pi_iff.mpr (fun b => measurable_pi_apply (k b))
  have hm := hp.map_prod_eq_prod_map_map hJ.aemeasurable hK.aemeasurable
  change μ.map (fun ω => (fun a => ω (j a), fun b => ω (k b))) =
    (μ.map (fun ω a => ω (j a))).prod (μ.map (fun ω b => ω (k b))) at hm
  rw [hm, Measure.map_infinitePi_infinitePi_of_inj hj, Measure.map_infinitePi_infinitePi_of_inj hk]

private theorem shuffle_prod {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (α : Measure A) (β : Measure B) (γ : Measure C) (δ : Measure D)
    [IsFiniteMeasure α] [IsFiniteMeasure β] [IsFiniteMeasure γ] [IsFiniteMeasure δ] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((α.prod β).prod (γ.prod δ)) ((α.prod γ).prod (β.prod δ)) := by
  have h₁ := measurePreserving_prodAssoc α β (γ.prod δ)
  have h₂ := (MeasurePreserving.id α).prod
    ((measurePreserving_prodAssoc β γ δ).symm MeasurableEquiv.prodAssoc)
  have h₃ := (MeasurePreserving.id α).prod
    ((Measure.measurePreserving_swap (μ := β) (ν := γ)).prod (MeasurePreserving.id δ))
  have h₄ := (MeasurePreserving.id α).prod (measurePreserving_prodAssoc γ β δ)
  have h₅ := (measurePreserving_prodAssoc α γ (β.prod δ)).symm MeasurableEquiv.prodAssoc
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

abbrev Prefix {n : Nat} (k : Site n → Nat) := {e : Event n // e.2 < k e.1}
abbrev Past {n : Nat} (k : Site n → Nat) := (Prefix k → ℝ) × (Prefix k → Bool)

private def futureId {n : Nat} (k : Site n → Nat) (e : Event n) : Event n :=
  (e.1, k e.1 + e.2)

private theorem futureId_injective {n : Nat} (k : Site n → Nat) :
    Function.Injective (futureId k) := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  have hv := congrArg Prod.fst h
  change v = w at hv
  subst w
  have hi := congrArg Prod.snd h
  change k v + i = k v + j at hi
  congr 1
  omega

private theorem prefix_future_disjoint {n : Nat} (k : Site n → Nat) :
    Disjoint (range (Subtype.val : Prefix k → Event n)) (range (futureId k)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  have hl := a.2
  rw [← hb] at hl
  exact (not_lt_of_ge (Nat.le_add_right _ _)) hl

private def pastMeasure {n : Nat} (k : Site n → Nat) : Measure (Past k) :=
  (Measure.infinitePi (fun _ : Prefix k => expMeasure 1)).prod (FairMarks.markMeasure (Prefix k))

private def splitSample {n : Nat} (k : Site n → Nat) (z : Sample n) : Past k × Sample n :=
  ((fun e => z.1 e.1, fun e => z.2 e.1),
    (fun e => z.1 (futureId k e), fun e => z.2 (futureId k e)))

private theorem splitSample_measurable {n : Nat} (k : Site n → Nat) :
    Measurable (splitSample k) := by unfold splitSample; fun_prop

private theorem splitSample_map {n : Nat} (k : Site n → Nat) :
    (ClockWordMarks.measure n).map (splitSample k) =
      (pastMeasure k).prod (ClockWordMarks.measure n) := by
  let G := ExponentialClocks.clockMeasure (Site n)
  let M := FairMarks.markMeasure (Event n)
  let g (ω : ExponentialClocks.Sample (Site n)) :=
    (fun e : Prefix k => ω e.1, fun e => ω (futureId k e))
  let m (η : Event n → Bool) :=
    (fun e : Prefix k => η e.1, fun e => η (futureId k e))
  let Gp := Measure.infinitePi (fun _ : Prefix k => expMeasure 1)
  let Mp := FairMarks.markMeasure (Prefix k)
  have hg : G.map g = Gp.prod G :=
    split_product (expMeasure 1) Subtype.val (futureId k) Subtype.val_injective
      (futureId_injective k) (prefix_future_disjoint k)
  have hm : M.map m = Mp.prod M :=
    split_product FairMarks.fair Subtype.val (futureId k) Subtype.val_injective
      (futureId_injective k) (prefix_future_disjoint k)
  have p := shuffle_prod Gp G Mp M
  change (G.prod M).map (splitSample k) = _
  rw [show splitSample k = (fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))) ∘ Prod.map g m from rfl,
    ← Measure.map_map p.measurable (by dsimp [g, m, Prod.map]; fun_prop),
    ← Measure.map_prod_map G M (by dsimp [g]; fun_prop) (by dsimp [m]; fun_prop), hg, hm]
  exact p.map_eq


private def headSplit {V : Type*} (ω : ExponentialClocks.Sample V) :
    (V → ℝ) × ExponentialClocks.Sample V :=
  (fun v => ω (v, 0), fun e => ω (e.1, e.2 + 1))

private def joinGaps {V : Type*} (p : (V → ℝ) × ExponentialClocks.Sample V) :
    ExponentialClocks.Sample V := fun e =>
  match e.2 with
  | 0 => p.1 e.1
  | j + 1 => p.2 (e.1, j)

private theorem headSplit_measurable {V : Type*} : Measurable (@headSplit V) := by
  unfold headSplit
  fun_prop

private theorem joinGaps_measurable {V : Type*} : Measurable (@joinGaps V) := by
  apply measurable_pi_iff.mpr
  rintro ⟨v, j⟩
  cases j
  · exact (measurable_pi_apply v).comp measurable_fst
  · exact (measurable_pi_apply _).comp measurable_snd

private theorem headSplit_map {V : Type*} [Fintype V] :
    (ExponentialClocks.clockMeasure V).map headSplit =
      (Measure.pi (fun _ : V => expMeasure 1)).prod (ExponentialClocks.clockMeasure V) := by
  rw [← Measure.infinitePi_eq_pi]
  refine split_product (expMeasure 1) (fun v : V => (v, 0))
    (fun e : V × Nat => (e.1, e.2 + 1)) ?_ ?_ ?_
  · exact fun _ _ h => congrArg Prod.fst h
  · rintro ⟨v, i⟩ ⟨w, j⟩ h
    simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at h
    exact Prod.ext h.1 h.2
  · apply Set.disjoint_left.mpr
    rintro _ ⟨v, rfl⟩ ⟨⟨w, j⟩, h⟩
    exact Nat.succ_ne_zero j (congrArg Prod.snd h)

private theorem joinGaps_map {V : Type*} [Fintype V] :
    ((Measure.pi (fun _ : V => expMeasure 1)).prod (ExponentialClocks.clockMeasure V)).map
      joinGaps = ExponentialClocks.clockMeasure V := by
  rw [← headSplit_map, Measure.map_map joinGaps_measurable headSplit_measurable]
  have h : @joinGaps V ∘ headSplit = id := by
    funext ω e
    obtain ⟨v, j⟩ := e
    cases j <;> rfl
  rw [h, Measure.map_id]

private def survives {V : Type*} (a : V → ℝ) : Set (ExponentialClocks.Sample V) :=
  {ω | ∀ v, a v < ω (v, 0)}

private def shiftGaps {V : Type*} (a : V → ℝ) (ω : ExponentialClocks.Sample V) :
    ExponentialClocks.Sample V := fun e =>
  if e.2 = 0 then ω e - a e.1 else ω e

private theorem shiftGaps_measurable {V : Type*} :
    Measurable (fun (p : (V → ℝ) × ExponentialClocks.Sample V) => shiftGaps p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro e
  by_cases he : e.2 = 0 <;> simp only [shiftGaps, he, ite_true, ite_false] <;> fun_prop

private def mass {V : Type*} [Fintype V] (a : V → ℝ) : ENNReal :=
  ∏ v, ENNReal.ofReal (Real.exp (-a v))

private theorem shift_head_map {V : Type*} [Fintype V] (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    ((Measure.pi (fun _ : V => expMeasure 1)).restrict (univ.pi (fun v => Ioi (a v)))).map
      (fun (x : V → ℝ) v => x v - a v) =
      mass a • Measure.pi (fun _ : V => expMeasure 1) := by
  rw [Measure.restrict_pi_pi, Measure.pi_map_pi (f := fun v (x : ℝ) => x - a v)
    (fun v => (measurable_id.sub_const (a v)).aemeasurable)]
  simp_rw [ExponentialMemoryless.shifted_restricted_measure (ha _)]
  letI (i : V) : IsFiniteMeasure (ENNReal.ofReal (Real.exp (-a i)) • expMeasure 1) :=
    ⟨by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact ENNReal.ofReal_lt_top⟩
  apply Measure.pi_eq
  intro t ht
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, mass, Finset.prod_mul_distrib]

private theorem shift_gap_map {V : Type*} [Fintype V] (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    ((ExponentialClocks.clockMeasure V).restrict (survives a)).map (shiftGaps a) =
      mass a • ExponentialClocks.clockMeasure V := by
  let A : Set (V → ℝ) := univ.pi (fun v => Ioi (a v))
  let f : (V → ℝ) → (V → ℝ) := fun x v => x v - a v
  have hA : MeasurableSet A := MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hs : survives a = headSplit ⁻¹' (A ×ˢ univ) := by
    ext ω
    simp [survives, A, headSplit, Set.mem_pi]
  have hg : shiftGaps a = (joinGaps ∘ Prod.map f id) ∘ headSplit := by
    funext ω e
    obtain ⟨v, j⟩ := e
    cases j <;> simp [shiftGaps, joinGaps, headSplit, f, Function.comp_def]
  rw [hg, hs, ← Measure.map_map ((joinGaps_measurable.comp (hf.prodMap measurable_id))) headSplit_measurable,
    ← Measure.restrict_map headSplit_measurable (hA.prod MeasurableSet.univ),
    headSplit_map, ← Measure.prod_restrict, Measure.restrict_univ,
    ← Measure.map_map joinGaps_measurable (hf.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id, shift_head_map a ha,
    Measure.prod_smul_left, Measure.map_smul _ joinGaps_measurable.aemeasurable, joinGaps_map]

private def shiftSample {n : Nat} (a : Site n → ℝ) (z : Sample n) : Sample n :=
  (shiftGaps a z.1, z.2)

private theorem shiftSample_measurable {n : Nat} :
    Measurable (fun (p : (Site n → ℝ) × Sample n) => shiftSample p.1 p.2) := by
  unfold shiftSample
  exact (shiftGaps_measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
    (measurable_snd.comp measurable_snd)

private theorem shift_sample_measure {n : Nat} (a : Site n → ℝ) (ha : ∀ v, 0 ≤ a v)
    (B : Set (Sample n)) (hB : MeasurableSet B) :
    ClockWordMarks.measure n ((survives a ×ˢ univ) ∩ shiftSample a ⁻¹' B) =
      mass a * ClockWordMarks.measure n B := by
  have hf : Measurable (shiftGaps a) :=
    shiftGaps_measurable.comp (measurable_const.prodMk measurable_id)
  have hshift : Measurable (shiftSample a) :=
    shiftSample_measurable.comp (measurable_const.prodMk measurable_id)
  have he : ((ClockWordMarks.measure n).restrict (survives a ×ˢ univ)).map (shiftSample a) =
      mass a • ClockWordMarks.measure n := by
    unfold ClockWordMarks.measure
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    change (Measure.map (Prod.map (shiftGaps a) id) _) = _
    rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id,
      shift_gap_map a ha, Measure.prod_smul_left]
  have h := congrArg (fun μ : Measure (Sample n) => μ B) he
  rw [Measure.map_apply hshift hB, Measure.restrict_apply (hshift hB), Measure.smul_apply,
    smul_eq_mul, inter_comm] at h
  exact h


private theorem slice_product_factor {P : Type*} [MeasurableSpace P] {n : Nat}
    (μ : Measure P) (a : P → Site n → ℝ) (ha : Measurable a)
    (A : Set P) (hA : MeasurableSet A) (hpos : ∀ p ∈ A, ∀ v, 0 ≤ a p v)
    (B : Set (Sample n)) (hB : MeasurableSet B) :
    (μ.prod (ClockWordMarks.measure n))
      {p | p.1 ∈ A ∧ p.2.1 ∈ survives (a p.1) ∧ shiftSample (a p.1) p.2 ∈ B} =
    (μ.prod (ClockWordMarks.measure n)) {p | p.1 ∈ A ∧ p.2.1 ∈ survives (a p.1)} *
      ClockWordMarks.measure n B := by
  classical
  let q (p : P) := if p ∈ A then mass (a p) else 0
  have hq : Measurable q := by
    change Measurable (A.indicator (fun p => mass (a p)))
    apply Measurable.indicator _ hA
    unfold mass
    apply Finset.measurable_prod
    intro v _
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_pi_apply v).comp ha).neg)
  have hsurv : MeasurableSet {p : P × Sample n | p.2.1 ∈ survives (a p.1)} := by
    change MeasurableSet {p : P × Sample n | ∀ v, a p.1 v < p.2.1 (v, 0)}
    rw [show {p : P × Sample n | ∀ v, a p.1 v < p.2.1 (v, 0)} =
      ⋂ v, {p | a p.1 v < p.2.1 (v, 0)} by ext; simp]
    exact MeasurableSet.iInter fun v => measurableSet_lt
      ((measurable_pi_apply v).comp (ha.comp measurable_fst))
      ((measurable_pi_apply (v, 0)).comp (measurable_fst.comp measurable_snd))
  have hshift : Measurable (fun p : P × Sample n => shiftSample (a p.1) p.2) :=
    shiftSample_measurable.comp ((ha.comp measurable_fst).prodMk measurable_snd)
  let S (B : Set (Sample n)) : Set (P × Sample n) :=
    {p | p.1 ∈ A ∧ p.2.1 ∈ survives (a p.1) ∧ shiftSample (a p.1) p.2 ∈ B}
  have hS (B : Set (Sample n)) (hB : MeasurableSet B) : MeasurableSet (S B) :=
    (measurable_fst hA).inter (hsurv.inter (hshift hB))
  have hfactor (B : Set (Sample n)) (hB : MeasurableSet B) :
      (μ.prod (ClockWordMarks.measure n)) (S B) =
        (∫⁻ p, q p ∂μ) * ClockWordMarks.measure n B := by
    rw [Measure.prod_apply (hS B hB), ← lintegral_mul_const _ hq]
    apply lintegral_congr
    intro p
    by_cases hp : p ∈ A
    · have hset : Prod.mk p ⁻¹' S B = (survives (a p) ×ˢ univ) ∩ shiftSample (a p) ⁻¹' B := by
        ext z
        simp [S, hp]
      rw [hset, shift_sample_measure _ (hpos p hp) B hB]
      simp [q, hp]
    · have hset : Prod.mk p ⁻¹' S B = ∅ := by ext; simp [S, hp]
      simp [hset, q, hp]
  have hfull := hfactor univ MeasurableSet.univ
  simp only [measure_univ, mul_one] at hfull
  have hu : S univ = {p | p.1 ∈ A ∧ p.2.1 ∈ survives (a p.1)} := by ext; simp [S]
  rw [← hu, hfull]
  exact hfactor B hB

private def fillGaps {n : Nat} {k : Site n → Nat} (p : Past k) :
    ExponentialClocks.Sample (Site n) := fun e =>
  if h : e.2 < k e.1 then p.1 ⟨e,h⟩ else 0

private def fillMarks {n : Nat} {k : Site n → Nat} (p : Past k) : Event n → Bool := fun e =>
  if h : e.2 < k e.1 then p.2 ⟨e,h⟩ else false

private theorem fillGaps_measurable {n : Nat} (k : Site n → Nat) : Measurable (@fillGaps n k) := by
  apply measurable_pi_iff.mpr
  intro e
  by_cases h : e.2 < k e.1
  · have he : (fun p : Past k => fillGaps p e) = (fun p => p.1 ⟨e,h⟩) := by
      funext p
      exact dite_eq_left h
    rw [he]
    exact (measurable_pi_apply (⟨e,h⟩ : Prefix k)).comp measurable_fst
  · have he : (fun p : Past k => fillGaps p e) = (fun _ => (0 : ℝ)) := by
      funext p
      exact dite_eq_right h
    rw [he]
    exact measurable_const

private theorem fillMarks_measurable {n : Nat} (k : Site n → Nat) : Measurable (@fillMarks n k) := by
  apply measurable_pi_iff.mpr
  intro e
  by_cases h : e.2 < k e.1
  · have he : (fun p : Past k => fillMarks p e) = (fun p => p.2 ⟨e,h⟩) := by
      funext p
      exact dite_eq_left h
    rw [he]
    exact (measurable_pi_apply (⟨e,h⟩ : Prefix k)).comp measurable_snd
  · have he : (fun p : Past k => fillMarks p e) = (fun _ => false) := by
      funext p
      exact dite_eq_right h
    rw [he]
    exact measurable_const

private def last {n : Nat} {k : Site n → Nat} (p : Past k) (v : Site n) : ℝ :=
  ∑ j ∈ Finset.range (k v), fillGaps p (v, j)

private theorem last_measurable {n : Nat} (k : Site n → Nat) (v : Site n) :
    Measurable (fun p : Past k => last p v) :=
  Finset.measurable_sum _ (fun j _ => (measurable_pi_apply (v,j)).comp (fillGaps_measurable k))

private def delay {n : Nat} {k : Site n → Nat} (s : ℝ) (p : Past k) (v : Site n) : ℝ :=
  s - last p v

private theorem delay_measurable {n : Nat} (k : Site n → Nat) (s : ℝ) :
    Measurable (@delay n k s) :=
  measurable_pi_iff.mpr (fun v => measurable_const.sub (last_measurable k v))

private def countSlice {n : Nat} (s : ℝ) (k : Site n → Nat) : Set (Sample n) :=
  {z | ∀ v, ClockCounting.clockCount v s z.1 = (k v : ℕ∞)}

private theorem countSlice_measurable {n : Nat} (s : ℝ) (k : Site n → Nat) :
    MeasurableSet (countSlice s k) := by
  have h : countSlice s k =
      ⋂ v, {z : Sample n | ClockCounting.clockCount v s z.1 = (k v : ℕ∞)} := by
    ext z
    simp [countSlice]
  rw [h]
  exact MeasurableSet.iInter fun v =>
    ((ClockCounting.clockCount_measurable v s).comp measurable_fst) (measurableSet_singleton _)

private theorem slice_count_condition {n : Nat} (s : ℝ) (hs : 0 ≤ s) (k : Site n → Nat)
    (z : Sample n) (hraw : ∀ e, ClockEventWord.eventTime z.1 e = ExponentialClocks.arrival e.1 e.2 z.1) :
    z ∈ countSlice s k ↔
      (∀ v, 0 ≤ delay s (splitSample k z).1 v) ∧
        (splitSample k z).2.1 ∈ survives (delay s (splitSample k z).1) := by
  have hlast (v : Site n) : last (splitSample k z).1 v = ∑ j ∈ Finset.range (k v), z.1 (v,j) := by
    unfold last
    apply Finset.sum_congr rfl
    intro j hj
    simp [fillGaps, splitSample, Finset.mem_range.mp hj]
  constructor
  all_goals
    simp only [countSlice, Set.mem_ofPred_eq, survives, delay]
  · intro h
    constructor
    · intro v
      rw [sub_nonneg, hlast]
      cases hk : k v with
      | zero => simp [hs]
      | succ j =>
        change ExponentialClocks.arrival v j z.1 ≤ s
        rw [← hraw (v,j)]
        exact (ClockCounting.clockCount_succ_le_iff v s z.1 j).mp (by rw [h v, hk])
    · intro v
      rw [hlast]
      have hnext := (ClockCounting.clockCount_lt_succ_iff v s z.1 (k v)).mp (by rw [h v]; exact_mod_cast Nat.lt_succ_self _)
      change s < ClockEventWord.eventTime z.1 (v,k v) at hnext
      rw [hraw, ExponentialClocks.arrival, Finset.sum_range_succ] at hnext
      change s - (∑ j ∈ Finset.range (k v), z.1 (v,j)) < z.1 (v,k v)
      exact sub_lt_iff_lt_add.mpr (by simpa [ExponentialClocks.gap, add_comm] using hnext)
  · rintro ⟨hp, hf⟩ v
    have hnext : s < ClockEventWord.eventTime z.1 (v,k v) := by
      rw [hraw, ExponentialClocks.arrival, Finset.sum_range_succ]
      have hh := hf v
      rw [hlast] at hh
      change s - (∑ j ∈ Finset.range (k v), z.1 (v,j)) < z.1 (v,k v) at hh
      simpa [ExponentialClocks.gap, add_comm] using sub_lt_iff_lt_add.mp hh
    have ht := (ClockCounting.clockCount_lt_succ_iff v s z.1 (k v)).mpr hnext
    have hle : (k v : ℕ∞) ≤ ClockCounting.clockCount v s z.1 := by
      cases hk : k v with
      | zero => simp
      | succ j =>
        apply (ClockCounting.clockCount_succ_le_iff v s z.1 j).mpr
        change ClockEventWord.eventTime z.1 (v,j) ≤ s
        rw [hraw]
        have h := hp v
        rw [sub_nonneg, hlast, hk] at h
        exact h
    exact le_antisymm (ENat.lt_natCast_add_one_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using ht)) hle


private instance prefixFintype {n : Nat} (k : Site n → Nat) : Fintype (Prefix k) :=
  Fintype.ofEquiv (Σ v : Site n, Fin (k v))
    ⟨fun p => ⟨(p.1,p.2.val),p.2.isLt⟩, fun e => ⟨e.1.1,⟨e.1.2,e.2⟩⟩,
      fun ⟨_,_⟩ => rfl, fun ⟨⟨_,_⟩,_⟩ => rfl⟩

private def beforeTime {n : Nat} {k : Site n → Nat} (p : Past k) (e : Prefix k) : ℝ :=
  ExponentialClocks.arrival e.1.1 e.1.2 (fillGaps p)

private def pastList {n : Nat} {k : Site n → Nat} (p : Past k) : List (Prefix k) :=
  (Finset.univ : Finset (Prefix k)).toList.mergeSort (fun a b => decide (beforeTime p b ≤ beforeTime p a))

private theorem pastList_measurable {n : Nat} (k : Site n → Nat) :
    Measurable (fun p : Past k => (pastList p).map Subtype.val) := by
  let sort : (Prefix k → Prefix k → Bool) → List (Event n) :=
    fun cmp => ((Finset.univ : Finset (Prefix k)).toList.mergeSort cmp).map Subtype.val
  have hm (e : Prefix k) : Measurable (fun p : Past k => beforeTime p e) :=
    (ExponentialClocks.arrival_measurable e.1.1 e.1.2).comp (fillGaps_measurable k)
  apply (measurable_of_countable sort).comp
  apply measurable_pi_iff.mpr
  intro a
  apply measurable_pi_iff.mpr
  intro b
  apply measurable_to_bool
  simpa only [Set.preimage, mem_singleton_iff, decide_eq_true_eq] using
    measurableSet_le (hm b) (hm a)

private def pastState {n : Nat} {k : Site n → Nat} (g : SquareSpin.Config n) (p : Past k) :
    SquareSpin.Config n :=
  MarkedEventTrace.execute (fillMarks p) ((pastList p).map Subtype.val).reverse g

private theorem pastState_measurable {n : Nat} (k : Site n → Nat) (g : SquareSpin.Config n) :
    Measurable (@pastState n k g) := by
  have hrun : Measurable (fun z : List (Event n) × (Event n → Bool) =>
      MarkedEventTrace.execute z.2 z.1.reverse g) :=
    measurable_from_prod_countable_right fun events => ClockExecutionLaw.fixedRun_measurable events g
  exact hrun.comp ((pastList_measurable k).prodMk (fillMarks_measurable k))

private theorem prefix_iff {n : Nat} (s : ℝ) {k : Site n → Nat}
    {z : Sample n} (hk : z ∈ countSlice s k) (e : Event n) :
    ClockEventWord.eventTime z.1 e ≤ s ↔ e.2 < k e.1 := by
  have h := ClockCounting.clockCount_succ_le_iff e.1 s z.1 e.2
  rw [show ClockCounting.clockCount e.1 s z.1 = (k e.1 : ℕ∞) from hk e.1] at h
  change _ ↔ ClockEventWord.eventTime z.1 e ≤ s at h
  rw [← h]
  exact_mod_cast (Nat.succ_le_iff (n := k e.1) (m := e.2))

private theorem pastState_eq {n : Nat} (s : ℝ) (k : Site n → Nat)
    (g : SquareSpin.Config n) (z : Sample n) (hk : z ∈ countSlice s k)
    (hgood : ClockEventWord.Good z.1 s)
    (hraw : ∀ e, ClockEventWord.eventTime z.1 e = ExponentialClocks.arrival e.1 e.2 z.1) :
    pastState g (splitSample k z).1 = ClockExecutionLaw.endpoint n s g z := by
  let p := (splitSample k z).1
  have ht (e : Prefix k) : beforeTime p e = ClockEventWord.eventTime z.1 e.1 := by
    rw [hraw]
    unfold beforeTime ExponentialClocks.arrival
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < k e.1.1 := lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) e.2
    simp [ExponentialClocks.gap, fillGaps, p, splitSample, hj']
  have hperm : (pastList p).Perm ((Finset.univ : Finset (Prefix k)).toList) :=
    List.mergeSort_perm _ _
  have hpN : ((pastList p).map Subtype.val).Nodup :=
    (hperm.nodup_iff.mpr (Finset.nodup_toList _)).map Subtype.val_injective
  have hmem (e : Event n) : e ∈ (pastList p).map Subtype.val ↔ e ∈ ClockEventWord.word z.1 s := by
    rw [List.mem_map, ClockEventWord.word_mem_iff _ _ hgood, ClockEventWord.eventSet,
      Set.mem_ofPred_eq, prefix_iff s hk e]
    constructor
    · rintro ⟨a, _, ha⟩
      exact ha ▸ a.2
    · intro he
      exact ⟨⟨e,he⟩, hperm.mem_iff.mpr (by simp), rfl⟩
  have hsort₀ : (pastList p).Pairwise (fun a b => beforeTime p b ≤ beforeTime p a) := by
    unfold pastList
    simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
      (le := fun a b : Prefix k => decide (beforeTime p b ≤ beforeTime p a))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact hbc.trans hab)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
      ((Finset.univ : Finset (Prefix k)).toList)
  have hsort : ((pastList p).map Subtype.val).Pairwise
      (fun a b => ClockEventWord.eventTime z.1 b ≤ ClockEventWord.eventTime z.1 a) := by
    rw [List.pairwise_map]
    simpa only [ht] using hsort₀
  have heq : (pastList p).map Subtype.val = ClockEventWord.word z.1 s :=
    List.Perm.eq_of_pairwise
      (fun a b _ _ hab hba => hgood.2 (le_antisymm hba hab))
      hsort (ClockEventWord.word_decreasing _ _)
      ((List.perm_ext_iff_of_nodup hpN (ClockEventWord.word_nodup _ _)).mpr hmem)
  change MarkedEventTrace.execute (fillMarks p) ((pastList p).map Subtype.val).reverse g = _
  rw [heq]
  apply MarkedEventTrace.execute_eq_of_marks_agree
  intro e he
  have hlt := (prefix_iff s hk e).mp ((ClockEventWord.word_mem_iff _ _ hgood e).mp (List.mem_reverse.mp he))
  simp [fillMarks, p, splitSample, hlt]

private def fresh {n : Nat} (s : ℝ) (k : Site n → Nat) (z : Sample n) : Sample n :=
  shiftSample (delay s (splitSample k z).1) (splitSample k z).2

private theorem fresh_measurable {n : Nat} (s : ℝ) (k : Site n → Nat) :
    Measurable (fresh s k) :=
  shiftSample_measurable.comp (((delay_measurable k s).comp
    (measurable_fst.comp (splitSample_measurable k))).prodMk
    (measurable_snd.comp (splitSample_measurable k)))

private structure Regular {n : Nat} (z : Sample n) : Prop where
  positive : ∀ v j, 0 < z.1 (v,j)
  good : ∀ t, ClockEventWord.Good z.1 t
  finite : ∀ v t, ClockCounting.clockCount v t z.1 < ⊤

private theorem regular_ae (n : Nat) : ∀ᵐ z ∂ClockWordMarks.measure n, Regular z := by
  have h : ∀ᵐ ω ∂ExponentialClocks.clockMeasure (Site n),
      (∀ v j, 0 < ω (v,j)) ∧ (∀ t, ClockEventWord.Good ω t) ∧
        (∀ v t, ClockCounting.clockCount v t ω < ⊤) := by
    filter_upwards [ExponentialClocks.all_gaps_positive_ae (V := Site n),
      ClockEventWord.good_ae (V := Site n), ClockCounting.clockCount_finite_ae (V := Site n)]
      with ω h₁ h₂ h₃
    exact ⟨h₁,h₂,h₃⟩
  exact ((Measure.quasiMeasurePreserving_fst (μ := ExponentialClocks.clockMeasure (Site n))
    (ν := FairMarks.markMeasure (Event n))).ae h).mono
      (fun _ h' => ⟨h'.1,h'.2.1,h'.2.2⟩)

private theorem eventTime_of_positive {V : Type*} {ω : ExponentialClocks.Sample V}
    (hp : ∀ v j, 0 < ω (v,j)) (e : V × Nat) :
    ClockEventWord.eventTime ω e = ExponentialClocks.arrival e.1 e.2 ω := by
  unfold ClockEventWord.eventTime ArrivalFiltration.chronologicalArrival ExponentialClocks.arrival
  exact Finset.sum_congr rfl fun j _ => max_eq_left (hp e.1 j).le

private theorem fresh_eventTime {n : Nat} {s : ℝ} (hs : 0 ≤ s)
    {k : Site n → Nat} {z : Sample n} (hz : Regular z) (hk : z ∈ countSlice s k)
    (e : Event n) :
    ClockEventWord.eventTime (fresh s k z).1 e =
      ClockEventWord.eventTime z.1 (futureId k e) - s := by
  have hraw := eventTime_of_positive hz.positive
  have hnext := ((slice_count_condition s hs k z hraw).mp hk).2
  have hpos (v : Site n) (j : Nat) : 0 < (fresh s k z).1 (v,j) := by
    cases j with
    | zero =>
      exact sub_pos.mpr (hnext v)
    | succ j =>
      exact hz.positive v (k v + (j + 1))
  rw [eventTime_of_positive hpos, hraw]
  obtain ⟨v,j⟩ := e
  change ExponentialClocks.arrival v j (fresh s k z).1 =
    ExponentialClocks.arrival v (k v + j) z.1 - s
  induction j with
  | zero =>
    have hfirst : ExponentialClocks.arrival v 0 (fresh s k z).1 =
        z.1 (v,k v) - (s - last (splitSample k z).1 v) := by
      simp [ExponentialClocks.arrival, ExponentialClocks.gap, fresh, shiftSample,
        shiftGaps, delay, splitSample, futureId]
    rw [hfirst, Nat.add_zero]
    unfold ExponentialClocks.arrival
    rw [Finset.sum_range_succ]
    have hh : (∑ j ∈ Finset.range (k v), fillGaps (splitSample k z).1 (v,j)) =
        ∑ j ∈ Finset.range (k v), z.1 (v,j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [fillGaps, splitSample, Finset.mem_range.mp hj]
    unfold last
    rw [hh]
    simp only [ExponentialClocks.gap]
    ring
  | succ j ih =>
    rw [show k v + (j + 1) = (k v + j) + 1 by omega, ExponentialClocks.arrival_succ,
      ExponentialClocks.arrival_succ, ih]
    have hh : ExponentialClocks.gap v (j+1) (fresh s k z).1 =
        ExponentialClocks.gap v (k v+j+1) z.1 := by
      simp [ExponentialClocks.gap, fresh, shiftSample, shiftGaps, splitSample, futureId, Nat.add_assoc]
    rw [hh]
    ring

private theorem endpoint_concat {n : Nat} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    {k : Site n → Nat} {z : Sample n} (hz : Regular z) (hk : z ∈ countSlice s k)
    (g : SquareSpin.Config n) :
    ClockExecutionLaw.endpoint n (s+t) g z =
      ClockExecutionLaw.endpoint n t (ClockExecutionLaw.endpoint n s g z) (fresh s k z) := by
  classical
  let w := ClockEventWord.word z.1 (s+t)
  let p := ClockEventWord.word z.1 s
  let f := fresh s k z
  let q := ClockEventWord.word f.1 t
  have hfin : ClockEventWord.Good f.1 t := by
    constructor
    · apply ((hz.good (s+t)).1.preimage (futureId_injective k).injOn).subset
      intro e he
      change _ ≤ t at he
      change ClockEventWord.eventTime z.1 (futureId k e) ≤ s+t
      rw [fresh_eventTime hs hz hk e] at he
      linarith
    · intro e e' h
      apply futureId_injective k
      apply (hz.good (s+t)).2
      change ClockEventWord.eventTime (fresh s k z).1 e =
        ClockEventWord.eventTime (fresh s k z).1 e' at h
      rw [fresh_eventTime hs hz hk, fresh_eventTime hs hz hk] at h
      linarith
  have hsuffix (e : Event n) : e ∈ q.reverse.map (futureId k) ↔
      s < ClockEventWord.eventTime z.1 e ∧ ClockEventWord.eventTime z.1 e ≤ s+t := by
    rw [List.mem_map]
    constructor
    · rintro ⟨a,ha,rfl⟩
      have hh := (ClockEventWord.word_mem_iff _ _ hfin a).mp (List.mem_reverse.mp ha)
      change ClockEventWord.eventTime (fresh s k z).1 a ≤ t at hh
      rw [fresh_eventTime hs hz hk a] at hh
      exact ⟨lt_of_not_ge (fun h =>
        (not_lt_of_ge (Nat.le_add_right _ _)) ((prefix_iff s hk (futureId k a)).mp h)), by linarith⟩
    · rintro ⟨h₁,h₂⟩
      have hk' : k e.1 ≤ e.2 := Nat.le_of_not_gt (fun h => (not_le_of_gt h₁) ((prefix_iff s hk e).mpr h))
      let a : Event n := (e.1,e.2-k e.1)
      have ha : futureId k a = e := by
        apply Prod.ext
        · rfl
        · change k e.1 + (e.2 - k e.1) = e.2
          omega
      refine ⟨a,List.mem_reverse.mpr ((ClockEventWord.word_mem_iff _ _ hfin a).mpr ?_),ha⟩
      change ClockEventWord.eventTime (fresh s k z).1 a ≤ t
      rw [fresh_eventTime hs hz hk, ha]
      linarith
  have hpair : (p.reverse ++ q.reverse.map (futureId k)).Pairwise
      (fun a b => ClockEventWord.eventTime z.1 a < ClockEventWord.eventTime z.1 b) := by
    apply List.pairwise_append.mpr
    refine ⟨ClockEventWord.word_reverse_strictly_increasing _ _, ?_, ?_⟩
    · rw [List.pairwise_map]
      apply (ClockEventWord.word_reverse_strictly_increasing f.1 t).imp
      intro a b hab
      change ClockEventWord.eventTime (fresh s k z).1 a <
        ClockEventWord.eventTime (fresh s k z).1 b at hab
      rw [fresh_eventTime hs hz hk, fresh_eventTime hs hz hk] at hab
      linarith
    · intro a ha b hb
      have hh := (ClockEventWord.word_mem_iff _ _ (hz.good s) a).mp (List.mem_reverse.mp ha)
      exact (show ClockEventWord.eventTime z.1 a ≤ s from hh).trans_lt ((hsuffix b).mp hb).1
  have hnodup : (p.reverse ++ q.reverse.map (futureId k)).Nodup :=
    hpair.imp (fun h => ne_of_apply_ne _ (ne_of_lt h))
  have hmem (e : Event n) : e ∈ p.reverse ++ q.reverse.map (futureId k) ↔ e ∈ w.reverse := by
    rw [List.mem_append, hsuffix, List.mem_reverse, List.mem_reverse,
      ClockEventWord.word_mem_iff _ _ (hz.good s), ClockEventWord.word_mem_iff _ _ (hz.good (s+t))]
    change (ClockEventWord.eventTime z.1 e ≤ s ∨ s < ClockEventWord.eventTime z.1 e ∧
      ClockEventWord.eventTime z.1 e ≤ s + t) ↔ ClockEventWord.eventTime z.1 e ≤ s + t
    constructor
    · rintro (h | ⟨_,h⟩)
      · exact h.trans (le_add_of_nonneg_right ht)
      · exact h
    · intro h
      by_cases hh : ClockEventWord.eventTime z.1 e ≤ s
      · exact Or.inl hh
      · exact Or.inr ⟨lt_of_not_ge hh,h⟩
  have heq : p.reverse ++ q.reverse.map (futureId k) = w.reverse :=
    List.Perm.eq_of_pairwise (fun a b _ _ h₁ h₂ => False.elim ((not_lt_of_gt h₁) h₂))
      hpair (ClockEventWord.word_reverse_strictly_increasing _ _)
      ((List.perm_ext_iff_of_nodup hnodup (List.nodup_reverse.mpr (ClockEventWord.word_nodup _ _))).mpr hmem)
  have hrun (l : List (Event n)) (cfg : SquareSpin.Config n) :
      MarkedEventTrace.execute z.2 (l.map (futureId k)) cfg =
        MarkedEventTrace.execute f.2 l cfg := by
    induction l generalizing cfg with
    | nil => rfl
    | cons e l ih =>
      change MarkedEventTrace.execute z.2 (l.map (futureId k))
          (SquareSpin.updateEvent z.2 (futureId k e) cfg) =
        MarkedEventTrace.execute f.2 l (SquareSpin.updateEvent f.2 e cfg)
      exact ih _
  change MarkedEventTrace.execute z.2 w.reverse g =
    MarkedEventTrace.execute f.2 q.reverse (MarkedEventTrace.execute z.2 p.reverse g)
  rw [← heq]
  unfold MarkedEventTrace.execute
  rw [EventTrace.execute_append]
  exact hrun _ _


private theorem joint_on_slice {n : Nat} (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (k : Site n → Nat) (g f : SquareSpin.Config n) (B : Set (SquareSpin.Config n))
    (hB : MeasurableSet B) :
    ClockWordMarks.measure n (countSlice s k ∩
      {z | ClockExecutionLaw.endpoint n s g z = f ∧ ClockExecutionLaw.endpoint n (s+t) g z ∈ B}) =
    ClockWordMarks.measure n (countSlice s k ∩ {z | ClockExecutionLaw.endpoint n s g z = f}) *
      ClockWordMarks.measure n {z | ClockExecutionLaw.endpoint n t f z ∈ B} := by
  let A : Set (Past k) := {p | (∀ v, 0 ≤ delay s p v) ∧ pastState g p = f}
  let C : Set (Sample n) := {z | ClockExecutionLaw.endpoint n t f z ∈ B}
  let D : Set (Past k × Sample n) := {p | p.1 ∈ A ∧ p.2.1 ∈ survives (delay s p.1)}
  let E : Set (Past k × Sample n) :=
    {p | p.1 ∈ A ∧ p.2.1 ∈ survives (delay s p.1) ∧ shiftSample (delay s p.1) p.2 ∈ C}
  have hA : MeasurableSet A := by
    apply MeasurableSet.inter
    · change MeasurableSet {p : Past k | ∀ v, 0 ≤ delay s p v}
      rw [show {p : Past k | ∀ v, 0 ≤ delay s p v} =
        ⋂ v, {p | 0 ≤ delay s p v} by ext; simp]
      exact MeasurableSet.iInter fun v =>
        measurableSet_le measurable_const ((measurable_pi_apply v).comp (delay_measurable k s))
    · exact pastState_measurable k g (measurableSet_singleton f)
  have hC : MeasurableSet C := ClockExecutionLaw.endpoint_measurable n t f hB
  have hcut : MeasurableSet {p : Past k × Sample n | p.2.1 ∈ survives (delay s p.1)} := by
    change MeasurableSet {p : Past k × Sample n | ∀ v, delay s p.1 v < p.2.1 (v,0)}
    rw [show {p : Past k × Sample n | ∀ v, delay s p.1 v < p.2.1 (v,0)} =
      ⋂ v, {p | delay s p.1 v < p.2.1 (v,0)} by ext; simp]
    exact MeasurableSet.iInter fun v => measurableSet_lt
      ((measurable_pi_apply v).comp ((delay_measurable k s).comp measurable_fst))
      ((measurable_pi_apply (v,0)).comp (measurable_fst.comp measurable_snd))
  have hD : MeasurableSet D := (measurable_fst hA).inter hcut
  have hE : MeasurableSet E := (measurable_fst hA).inter (hcut.inter
    ((shiftSample_measurable.comp (((delay_measurable k s).comp measurable_fst).prodMk
      measurable_snd)) hC))
  have hD' : countSlice s k ∩ {z | ClockExecutionLaw.endpoint n s g z = f}
      =ᵐ[ClockWordMarks.measure n] splitSample k ⁻¹' D := by
    filter_upwards [regular_ae n] with z hz
    apply propext
    have hc := slice_count_condition s hs k z (eventTime_of_positive hz.positive)
    change (z ∈ countSlice s k ∧ ClockExecutionLaw.endpoint n s g z = f) ↔
      (((∀ v, 0 ≤ delay s (splitSample k z).1 v) ∧ pastState g (splitSample k z).1 = f) ∧
        (splitSample k z).2.1 ∈ survives (delay s (splitSample k z).1))
    constructor
    · rintro ⟨hk,hf⟩
      exact ⟨⟨(hc.mp hk).1,(pastState_eq s k g z hk (hz.good s)
        (eventTime_of_positive hz.positive)).trans hf⟩,(hc.mp hk).2⟩
    · rintro ⟨⟨ha, hf⟩, hcut⟩
      have hk := hc.mpr ⟨ha,hcut⟩
      exact ⟨hk, (pastState_eq s k g z hk (hz.good s) (eventTime_of_positive hz.positive)).symm.trans hf⟩
  have hE' : countSlice s k ∩
      {z | ClockExecutionLaw.endpoint n s g z = f ∧ ClockExecutionLaw.endpoint n (s+t) g z ∈ B}
      =ᵐ[ClockWordMarks.measure n] splitSample k ⁻¹' E := by
    filter_upwards [regular_ae n,hD'] with z hz hd
    apply propext
    have hd' := Iff.of_eq hd
    constructor
    · rintro ⟨hk,hf,hB⟩
      have hd'' := hd'.mp ⟨hk,hf⟩
      have hh := endpoint_concat hs ht hz hk g
      rw [hf] at hh
      exact ⟨hd''.1,hd''.2, by
        change ClockExecutionLaw.endpoint n t f (fresh s k z) ∈ B
        rwa [← hh]⟩
    · intro he
      have hh : z ∈ splitSample k ⁻¹' D := ⟨he.1,he.2.1⟩
      have hg := hd'.mpr hh
      refine ⟨hg.1,hg.2,?_⟩
      rw [endpoint_concat hs ht hz hg.1, hg.2]
      exact he.2.2
  rw [measure_congr hD', measure_congr hE', ← Measure.map_apply (splitSample_measurable k) hD,
    ← Measure.map_apply (splitSample_measurable k) hE, splitSample_map]
  exact slice_product_factor (pastMeasure k) (delay s) (delay_measurable k s)
    A hA (fun _ hp => hp.1) C hC

private theorem sum_countSlices {n : Nat} (s : ℝ) (A : Set (Sample n)) (hA : MeasurableSet A) :
    (∑' k : Site n → Nat, ClockWordMarks.measure n (countSlice s k ∩ A)) =
      ClockWordMarks.measure n A := by
  have hd : Pairwise (fun k l : Site n → Nat => Disjoint (countSlice s k ∩ A) (countSlice s l ∩ A)) := by
    intro k l hkl
    refine Set.disjoint_left.mpr ?_
    intro z hk hl
    apply hkl
    funext v
    exact_mod_cast ((hk.1 v).symm.trans (hl.1 v))
  rw [← measure_iUnion hd (fun k => (countSlice_measurable s k).inter hA)]
  apply measure_congr
  filter_upwards [regular_ae n] with z hz
  apply propext
  simp only [mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨_,_,ha⟩
    exact ha
  · intro ha
    refine ⟨fun v => (ClockCounting.clockCount v s z.1).toNat, ?_, ha⟩
    intro v
    exact (ENat.natCast_toNat (hz.finite v s).ne).symm

/-- At a deterministic time, the original marked-clock endpoint has the
transition law obtained by resuming from its current configuration. -/
theorem endpoint_joint {n : Nat} (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (g f : SquareSpin.Config n) (B : Set (SquareSpin.Config n)) (hB : MeasurableSet B) :
    ClockWordMarks.measure n
      {z | ClockExecutionLaw.endpoint n s g z = f ∧ ClockExecutionLaw.endpoint n (s+t) g z ∈ B} =
    ClockWordMarks.measure n {z | ClockExecutionLaw.endpoint n s g z = f} *
      ClockWordMarks.measure n {z | ClockExecutionLaw.endpoint n t f z ∈ B} := by
  have hf : MeasurableSet {z | ClockExecutionLaw.endpoint n s g z = f} :=
    ClockExecutionLaw.endpoint_measurable n s g (measurableSet_singleton _)
  have hjoined : MeasurableSet {z | ClockExecutionLaw.endpoint n s g z = f ∧
      ClockExecutionLaw.endpoint n (s+t) g z ∈ B} :=
    hf.inter (ClockExecutionLaw.endpoint_measurable n (s+t) g hB)
  rw [← sum_countSlices s _ hjoined, ← sum_countSlices s _ hf, ← ENNReal.tsum_mul_right]
  exact tsum_congr (fun k => joint_on_slice s t hs ht k g f B hB)

/-- Finite-state form of the deterministic clock restart. -/
theorem endpoint_probability {n : Nat} (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (g : SquareSpin.Config n) (B : Set (SquareSpin.Config n)) (hB : MeasurableSet B) :
    (ClockWordMarks.measure n).real {z | ClockExecutionLaw.endpoint n (s+t) g z ∈ B} =
      ∑ f : SquareSpin.Config n,
        (ClockWordMarks.measure n).real {z | ClockExecutionLaw.endpoint n s g z = f} *
          (ClockWordMarks.measure n).real {z | ClockExecutionLaw.endpoint n t f z ∈ B} := by
  let E (f : SquareSpin.Config n) : Set (Sample n) :=
    {z | ClockExecutionLaw.endpoint n s g z = f ∧ ClockExecutionLaw.endpoint n (s+t) g z ∈ B}
  have hE (f : SquareSpin.Config n) : MeasurableSet (E f) :=
    (ClockExecutionLaw.endpoint_measurable n s g (measurableSet_singleton _)).inter
      (ClockExecutionLaw.endpoint_measurable n (s+t) g hB)
  have hdisj : Pairwise (fun f f' => Disjoint (E f) (E f')) := by
    intro f f' hne
    exact Set.disjoint_left.mpr (fun _ hf hf' => hne (hf.1.symm.trans hf'.1))
  have hcover : {z : Sample n | ClockExecutionLaw.endpoint n (s+t) g z ∈ B} = ⋃ f, E f := by
    ext z
    simp [E]
  rw [hcover, measureReal_iUnion_fintype hdisj hE]
  apply Finset.sum_congr rfl
  intro f _
  change (ClockWordMarks.measure n (E f)).toReal = _
  rw [show ClockWordMarks.measure n (E f) = _ from endpoint_joint s t hs ht g f B hB,
    ENNReal.toReal_mul]
  rfl

end MathResearchAnalysis.DeterministicClockRestart

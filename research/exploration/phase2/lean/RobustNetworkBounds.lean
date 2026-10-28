module
public import DirectedNetworkComparison
public import Mathlib.Tactic

set_option autoImplicit false

/-! Classical finite Metzler comparison and interval-matrix certificates.
The phase1 source and original main theorem remain unchanged. Solutions are
given continuous functions with the displayed classical derivatives; no ODE
existence, arbitrary measurable-input solution or real-device claim is made.
-/
@[expose] public noncomputable section
namespace MathExploration.RobustNetworkBounds
open Set
open scoped BigOperators
open MathExploration.DirectedNetworkComparison
variable {V : Type*} [Fintype V] [DecidableEq V]

def linear (B : V → V → Real) (x : V → Real) (i : V) : Real := ∑ j : V, B i j*x j
def Metzler (B : V → V → Real) : Prop := ∀ i j, i≠j → 0≤B i j
def offDiag (B : V → V → Real) (i j : V) : Real := if i=j then 0 else B i j
def row (B : V → V → Real) (i : V) : Real := ∑ j : V, B i j
def rowBound (B : V → V → Real) : Real := ∑ i : V, |row B i|

omit [Fintype V] in
theorem offDiag_nonneg (B : V → V → Real) (hB : Metzler B) (i j : V) :
    0≤offDiag B i j := by
  by_cases hij : i=j
  · simp [offDiag,hij]
  · simpa [offDiag,hij] using hB i j hij

omit [DecidableEq V] in
theorem row_le_bound (B : V → V → Real) (i : V) : row B i≤rowBound B := by
  exact (le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (row B j)) (Finset.mem_univ i))

theorem linear_eq_rate (B : V → V → Real) (x : V → Real) (i : V) :
    linear B x i = rate (offDiag B) x i + row B i*x i := by
  have hr : rate (offDiag B) x i = ∑ j : V, B i j*(x j-x i) := by
    unfold rate
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i=j
    · subst j
      simp [offDiag]
    · simp [offDiag,h]
  rw [hr]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul]
  unfold linear row
  ring

omit [DecidableEq V] in
theorem rate_scale (a : V → V → Real) (r : Real) (x : V → Real) (i : V) :
    rate a (fun j => r*x j) i = r*rate a x i := by
  unfold rate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq V] in
theorem linear_sub (B : V → V → Real) (x y : V → Real) (i : V) :
    linear B (fun j => x j-y j) i=linear B x i-linear B y i := by
  unfold linear
  simp_rw [mul_sub,Finset.sum_sub_distrib]

omit [DecidableEq V] in
theorem linear_mono_matrix (B C : V → V → Real) (hBC : ∀ i j, B i j≤C i j)
    (x : V → Real) (hx : ∀ i, 0≤x i) (i : V) : linear B x i≤linear C x i := by
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hBC i j) (hx j))

theorem metzler_nonpos (B : V → V → Real) (hB : Metzler B)
    (c s : Real → V → Real)
    (hc : ∀ i, ContinuousOn (fun t => c t i) (Ici 0))
    (hd : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun r => c r i) (linear B (c t) i-s t i) t)
    (hs : ∀ t : Real, 0<t → ∀ i, 0≤s t i)
    (hz : ∀ i, c 0 i≤0) (t : Real) (ht : 0≤t) (i : V) : c t i≤0 := by
  let R := rowBound B
  let q := fun t : Real => Real.exp (-R*t)
  let z := fun t j => q t*c t j
  let d := fun j => R-row B j
  have hdpos : ∀ j, 0≤d j := fun j => sub_nonneg.mpr (row_le_bound B j)
  have hq (r : Real) : HasDerivAt q ((-R)*q r) r := by
    simpa only [q,id_eq,mul_one,one_mul,mul_comm] using (((hasDerivAt_id r).const_mul (-R)).exp)
  have hzc : ∀ j, ContinuousOn (fun r => z r j) (Ici 0) := by
    intro j
    exact ((continuous_iff_continuousAt.mpr (fun r => (hq r).continuousAt)).continuousOn).mul (hc j)
  have hzd : ∀ r : Real, 0<r → ∀ j,
      HasDerivAt (fun u => z u j)
        (leakedRate (offDiag B) d (z r) j-q r*s r j) r := by
    intro r hr j
    have h := (hq r).mul (hd r hr j)
    have he : leakedRate (offDiag B) d (z r) j-q r*s r j =
        ((-R)*q r)*c r j+q r*(linear B (c r) j-s r j) := by
      unfold leakedRate
      change rate (offDiag B) (fun k => q r*c r k) j-
        (R-row B j)*(q r*c r j)-q r*s r j = _
      rw [rate_scale,linear_eq_rate]
      ring
    rw [he]
    exact h
  have hzn : z t i≤0 := nonpos (offDiag B) (offDiag_nonneg B hB) d hdpos _
    (imbalance_le_total _ (offDiag_nonneg B hB)) z (fun r j => q r*s r j)
    hzc hzd (fun r hr j => mul_nonneg (Real.exp_nonneg _) (hs r hr j))
    (fun j => by simpa [z,q] using hz j) t ht i
  exact (mul_le_mul_iff_of_pos_left (Real.exp_pos (-R*t))).mp (by simpa [z,q] using hzn)

/-- Differential subsolutions suffice: the missing drift is a nonnegative
source, so the desired comparison is not a supplied premise. -/
theorem differential_comparison (B : V → V → Real) (hB : Metzler B)
    (x y dx dy : Real → V → Real)
    (hcx : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hcy : ∀ i, ContinuousOn (fun t => y t i) (Ici 0))
    (hdx : ∀ t : Real, 0<t → ∀ i, HasDerivAt (fun r => x r i) (dx t i) t)
    (hdy : ∀ t : Real, 0<t → ∀ i, HasDerivAt (fun r => y r i) (dy t i) t)
    (hineq : ∀ t : Real, 0<t → ∀ i,
      dx t i-dy t i ≤ linear B (fun j => x t j-y t j) i)
    (hz : ∀ i, x 0 i≤y 0 i) (t : Real) (ht : 0≤t) (i : V) : x t i≤y t i := by
  let s := fun t i => linear B (fun j => x t j-y t j) i-(dx t i-dy t i)
  have hd : ∀ r : Real, 0<r → ∀ j,
      HasDerivAt (fun u => x u j-y u j)
        (linear B (fun k => x r k-y r k) j-s r j) r := by
    intro r hr j
    have he : linear B (fun k => x r k-y r k) j-s r j = dx r j-dy r j := by
      dsimp [s]
      ring
    rw [he]
    exact (hdx r hr j).sub (hdy r hr j)
  exact sub_nonpos.mp (metzler_nonpos B hB (fun r j => x r j-y r j) s
    (fun j => (hcx j).sub (hcy j)) hd (fun r hr j => sub_nonneg.mpr (hineq r hr j))
    (fun j => sub_nonpos.mpr (hz j)) t ht i)

theorem positive_solution (B : V → V → Real) (hB : Metzler B)
    (x f : Real → V → Real)
    (hc : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hd : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun r => x r i) (linear B (x t) i+f t i) t)
    (hf : ∀ t : Real, 0<t → ∀ i, 0≤f t i)
    (hz : ∀ i, 0≤x 0 i) (t : Real) (ht : 0≤t) (i : V) : 0≤x t i := by
  apply differential_comparison B hB (fun _ _ => 0) x (fun _ _ => 0)
    (fun r j => linear B (x r) j+f r j) (fun _ => continuousOn_const) hc
    (fun r _ _ => hasDerivAt_const r 0) hd _ hz t ht i
  intro r hr j
  have he : linear B (fun k => (0 : Real)-x r k) j = -linear B (x r) j := by
    unfold linear
    simp [Finset.sum_neg_distrib]
  rw [he]
  linarith [hf r hr j]

/-- A fixed matrix interval yields a correct (possibly conservative) upper
barrier. Actual matrix and input bounds are structural data, not the target. -/
theorem interval_upper (M H : V → V → Real) (hM : Metzler M) (hH : Metzler H)
    (hMH : ∀ i j, M i j≤H i j) (x y f g : Real → V → Real)
    (hcx : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hcy : ∀ i, ContinuousOn (fun t => y t i) (Ici 0))
    (hdx : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun r => x r i) (linear M (x t) i+f t i) t)
    (hdy : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun r => y r i) (linear H (y t) i+g t i) t)
    (hf : ∀ t : Real, 0<t → ∀ i, 0≤f t i)
    (hfg : ∀ t : Real, 0<t → ∀ i, f t i≤g t i)
    (hx0 : ∀ i, 0≤x 0 i) (hxy0 : ∀ i, x 0 i≤y 0 i)
    (t : Real) (ht : 0≤t) (i : V) : x t i≤y t i := by
  apply differential_comparison H hH x y
    (fun r j => linear M (x r) j+f r j) (fun r j => linear H (y r) j+g r j)
    hcx hcy hdx hdy _ hxy0 t ht i
  intro r hr j
  rw [linear_sub]
  have h := linear_mono_matrix M H hMH (x r)
    (positive_solution M hM x f hcx hdx hf hx0 r hr.le) j
  linarith [hfg r hr j]

theorem interval_lower (L M : V → V → Real) (hL : Metzler L) (hM : Metzler M)
    (hLM : ∀ i j, L i j≤M i j) (y x g f : Real → V → Real)
    (hcy : ∀ i, ContinuousOn (fun t => y t i) (Ici 0))
    (hcx : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hdy : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun r => y r i) (linear L (y t) i+g t i) t)
    (hdx : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun r => x r i) (linear M (x t) i+f t i) t)
    (hf : ∀ t : Real, 0<t → ∀ i, 0≤f t i)
    (hgf : ∀ t : Real, 0<t → ∀ i, g t i≤f t i)
    (hx0 : ∀ i, 0≤x 0 i) (hyx0 : ∀ i, y 0 i≤x 0 i)
    (t : Real) (ht : 0≤t) (i : V) : y t i≤x t i := by
  apply differential_comparison L hL y x
    (fun r j => linear L (y r) j+g r j) (fun r j => linear M (x r) j+f r j)
    hcy hcx hdy hdx _ hyx0 t ht i
  intro r hr j
  rw [linear_sub]
  have h := linear_mono_matrix L M hLM (x r)
    (positive_solution M hM x f hcx hdx hf hx0 r hr.le) j
  linarith [hgf r hr j]

end MathExploration.RobustNetworkBounds

#print axioms MathExploration.RobustNetworkBounds.linear
#print axioms MathExploration.RobustNetworkBounds.Metzler
#print axioms MathExploration.RobustNetworkBounds.offDiag
#print axioms MathExploration.RobustNetworkBounds.row
#print axioms MathExploration.RobustNetworkBounds.rowBound
#print axioms MathExploration.RobustNetworkBounds.offDiag_nonneg
#print axioms MathExploration.RobustNetworkBounds.row_le_bound
#print axioms MathExploration.RobustNetworkBounds.linear_eq_rate
#print axioms MathExploration.RobustNetworkBounds.rate_scale
#print axioms MathExploration.RobustNetworkBounds.linear_sub
#print axioms MathExploration.RobustNetworkBounds.linear_mono_matrix
#print axioms MathExploration.RobustNetworkBounds.metzler_nonpos
#print axioms MathExploration.RobustNetworkBounds.differential_comparison
#print axioms MathExploration.RobustNetworkBounds.positive_solution
#print axioms MathExploration.RobustNetworkBounds.interval_upper
#print axioms MathExploration.RobustNetworkBounds.interval_lower

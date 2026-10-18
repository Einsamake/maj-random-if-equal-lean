module

public import MathResearchAnalysis.FiniteWordKernel
public import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false

/-!
# Order independence of actual same-colour scan kernels

Within a checkerboard layer, actual updates at distinct sites commute.
The independent fair-mark average therefore depends only on the layer's
site multiset. A duplicate-free complete layer can use any enumeration,
including an enumeration chosen from a clock sample.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.SquareScanKernel

abbrev Site (n : ℕ) := SquareTasks.Vertex n
abbrev Config (n : ℕ) := SquareSpin.Config n

def taskWord (n : ℕ) (c : Bool) (k : ℕ) : List (Site n) :=
  (SquareTasks.tasks n c k).toList

def taskMean (n : ℕ) (c : Bool) (k : ℕ) (φ : Config n → ℝ) (f : Config n) : ℝ :=
  ZeroTemperature.coldWord (taskWord n c k) φ f

def scanWord (n : ℕ) (c : Bool) (first count : ℕ) : List (Site n) :=
  (List.range count).flatMap (fun j => taskWord n c (first + j))

def scanMean (n : ℕ) (c : Bool) (first count : ℕ)
    (φ : Config n → ℝ) (f : Config n) : ℝ :=
  ZeroTemperature.coldWord (scanWord n c first count) φ f

/-- Commutation is derived by averaging the four actual common-mark executions. -/
theorem coldStep_commute_same_colour {n : ℕ} (v u : Site n)
    (hne : v ≠ u) (hc : SquareTasks.colour v = SquareTasks.colour u)
    (φ : Config n → ℝ) (f : Config n) :
    ZeroTemperature.coldStep v (ZeroTemperature.coldStep u φ) f =
      ZeroTemperature.coldStep u (ZeroTemperature.coldStep v φ) f := by
  simp only [ZeroTemperature.coldStep_eq_actual_majority]
  rw [SquareSpin.cellUpdate_commute_same_colour f v u true true hne hc,
    SquareSpin.cellUpdate_commute_same_colour f v u true false hne hc,
    SquareSpin.cellUpdate_commute_same_colour f v u false true hne hc,
    SquareSpin.cellUpdate_commute_same_colour f v u false false hne hc]
  ring

theorem coldWord_eq_foldr {n : ℕ} (word : List (Site n)) (φ : Config n → ℝ) :
    ZeroTemperature.coldWord word φ =
      word.foldr (fun v ψ => ZeroTemperature.coldStep v ψ) φ := by
  induction word with
  | nil => rfl
  | cons v rest ih =>
    change ZeroTemperature.coldStep v (ZeroTemperature.coldWord rest φ) = _
    rw [ih]
    rfl

/-- Even repeated same-colour sites can be permuted: their identical operators commute. -/
theorem coldWord_eq_of_perm_same_colour {n : ℕ} {word other : List (Site n)}
    (hp : word.Perm other) (c : Bool)
    (hc : ∀ v ∈ word, SquareTasks.colour v = c)
    (φ : Config n → ℝ) (f : Config n) :
    ZeroTemperature.coldWord word φ f = ZeroTemperature.coldWord other φ f := by
  have hfold := hp.foldr_eq' (f := fun v ψ => ZeroTemperature.coldStep v ψ)
    (fun x hx y hy ψ => by
      funext g
      by_cases hxy : x = y
      · subst y
        rfl
      · exact coldStep_commute_same_colour y x (Ne.symm hxy)
          ((hc y hy).trans (hc x hx).symm) ψ g) φ
  exact congrFun ((coldWord_eq_foldr word φ).trans
    (hfold.trans (coldWord_eq_foldr other φ).symm)) f

theorem coldWord_eq_of_nodup_same_members {n : ℕ} {word other : List (Site n)}
    (hw : word.Nodup) (ho : other.Nodup)
    (members : ∀ v, v ∈ word ↔ v ∈ other) (c : Bool)
    (hc : ∀ v ∈ word, SquareTasks.colour v = c)
    (φ : Config n → ℝ) (f : Config n) :
    ZeroTemperature.coldWord word φ f = ZeroTemperature.coldWord other φ f :=
  coldWord_eq_of_perm_same_colour
    ((List.perm_ext_iff_of_nodup hw ho).mpr members) c hc φ f

theorem actualMean_eq_of_perm_same_colour {n : ℕ} {word other : List (Site n)}
    (hp : word.Perm other) (c : Bool)
    (hc : ∀ v ∈ word, SquareTasks.colour v = c)
    (φ : Config n → ℝ) (f : Config n) :
    ZeroTemperature.actualMajorityWordMean word φ f =
      ZeroTemperature.actualMajorityWordMean other φ f := by
  rw [← ZeroTemperature.coldWord_eq_actualMajorityWordMean,
    ← ZeroTemperature.coldWord_eq_actualMajorityWordMean]
  exact coldWord_eq_of_perm_same_colour hp c hc φ f

/-- A complete layer can use any duplicate-free enumeration of its actual sites. -/
theorem coldWord_eq_taskMean {n : ℕ} (c : Bool) (k : ℕ) (word : List (Site n))
    (unique : word.Nodup)
    (members : ∀ v, v ∈ word ↔ v ∈ SquareTasks.tasks n c k)
    (φ : Config n → ℝ) (f : Config n) :
    ZeroTemperature.coldWord word φ f = taskMean n c k φ f := by
  have hnodup : (taskWord n c k).Nodup := Finset.nodup_toList _
  have hp : word.Perm (taskWord n c k) :=
    (List.perm_ext_iff_of_nodup unique hnodup).mpr (fun v => by
      simpa only [taskWord, Finset.mem_toList] using members v)
  exact coldWord_eq_of_perm_same_colour hp (if k % 2 = 0 then c else !c)
    (fun v hv => (SquareTasks.mem_tasks_colour n c k v).mp ((members v).mp hv)) φ f

theorem coldWord_flatMap_congr {n : ℕ} (indices : List ℕ)
    (left right : ℕ → List (Site n))
    (h : ∀ j ∈ indices, ∀ (φ : Config n → ℝ) (f : Config n),
      ZeroTemperature.coldWord (left j) φ f = ZeroTemperature.coldWord (right j) φ f)
    (φ : Config n → ℝ) (f : Config n) :
    ZeroTemperature.coldWord (indices.flatMap left) φ f =
      ZeroTemperature.coldWord (indices.flatMap right) φ f := by
  induction indices generalizing φ f with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.flatMap_cons, FiniteWordKernel.coldWord_append]
    rw [h j (by simp)]
    apply congrArg (fun ψ => ZeroTemperature.coldWord (right j) ψ f)
    funext g
    exact ih (fun k hk => h k (List.mem_cons_of_mem j hk)) φ g

/-- Every slot may choose its own enumeration, while sites may recur in later slots. -/
theorem coldWord_scan_eq_scanMean {n : ℕ} (c : Bool) (first count : ℕ)
    (layers : ℕ → List (Site n))
    (unique : ∀ j < count, (layers (first + j)).Nodup)
    (members : ∀ j < count, ∀ v,
      v ∈ layers (first + j) ↔ v ∈ SquareTasks.tasks n c (first + j))
    (φ : Config n → ℝ) (f : Config n) :
    ZeroTemperature.coldWord
        ((List.range count).flatMap (fun j => layers (first + j))) φ f =
      scanMean n c first count φ f := by
  exact coldWord_flatMap_congr (List.range count) _ _
    (fun j hj ψ g => coldWord_eq_taskMean c (first + j) _
      (unique j (List.mem_range.mp hj)) (members j (List.mem_range.mp hj)) ψ g) φ f

theorem actualMean_scan_eq_scanMean {n : ℕ} (c : Bool) (first count : ℕ)
    (layers : ℕ → List (Site n))
    (unique : ∀ j < count, (layers (first + j)).Nodup)
    (members : ∀ j < count, ∀ v,
      v ∈ layers (first + j) ↔ v ∈ SquareTasks.tasks n c (first + j))
    (φ : Config n → ℝ) (f : Config n) :
    ZeroTemperature.actualMajorityWordMean
        ((List.range count).flatMap (fun j => layers (first + j))) φ f =
      scanMean n c first count φ f := by
  rw [← ZeroTemperature.coldWord_eq_actualMajorityWordMean]
  exact coldWord_scan_eq_scanMean c first count layers unique members φ f

end MathResearchAnalysis.SquareScanKernel

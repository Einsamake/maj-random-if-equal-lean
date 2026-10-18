module

public import MathResearchAnalysis.InfiniteGridModel
public import MathResearchAnalysis.SquareDynamics

set_option autoImplicit false

/-!
# Exact embedding of the zero-boundary square into the integer grid

The square has side `n + 2`. Extension reads a finite coordinate only after
checking both integer coordinates lie in the square. Exterior values are
false. The full-configuration trajectory identities use the proved support
invariance of the actual four-input rule, including all exterior sites.
Marks and checkerboard phases are kept samplewise, without any probability
or finite-absorption assumption.
-/

public section

namespace MathResearchAnalysis.SquareGridEmbedding

open SquareTasks

abbrev Site := InfiniteGridModel.Site
abbrev Config := InfiniteGridModel.Config

/-- Origin-preserving inclusion into the integer lattice. -/
@[expose] def embed (n : ℕ) (v : Vertex n) : Site :=
  ((v.1.val : ℤ), (v.2.val : ℤ))

/-- The finite vertex associated with an integer point already proved inside. -/
@[expose] def vertexOfInside (n : ℕ) (z : Site)
    (h : InfiniteGridModel.Inside (n + 2) z) : Vertex n :=
  (⟨z.1.toNat, by unfold InfiniteGridModel.Inside at h; omega⟩,
    ⟨z.2.toNat, by unfold InfiniteGridModel.Inside at h; omega⟩)

/-- Restriction to the actual finite vertices. -/
@[expose] def restrict (n : ℕ) (f : Config) : SquareSpin.Config n :=
  fun v => f (embed n v)

/-- Zero extension. Negative coordinates are rejected before `Int.toNat`. -/
@[expose] def extend (n : ℕ) (g : SquareSpin.Config n) : Config :=
  fun z => if h : InfiniteGridModel.Inside (n + 2) z then g (vertexOfInside n z h)
    else false

/-- All positive and unused zero time slots are restricted by the same inclusion. -/
@[expose] def restrictMarks (n : ℕ) (marks : InfiniteGridModel.Marks) :
    SquareDynamics.Marks n := fun t v => marks t (embed n v)

theorem embed_injective (n : ℕ) : Function.Injective (embed n) := by
  intro v w h
  apply Prod.ext <;> apply Fin.ext
  · have hx := congrArg Prod.fst h
    simp only [embed] at hx
    omega
  · have hy := congrArg Prod.snd h
    simp only [embed] at hy
    omega

theorem embed_inside (n : ℕ) (v : Vertex n) :
    InfiniteGridModel.Inside (n + 2) (embed n v) := by
  have hx := v.1.isLt
  have hy := v.2.isLt
  simp only [InfiniteGridModel.Inside, embed]
  omega

theorem embed_vertexOfInside (n : ℕ) (z : Site)
    (h : InfiniteGridModel.Inside (n + 2) z) :
    embed n (vertexOfInside n z h) = z := by
  unfold InfiniteGridModel.Inside at h
  apply Prod.ext <;> simp only [embed, vertexOfInside] <;> omega

theorem inside_iff_exists_vertex (n : ℕ) (z : Site) :
    InfiniteGridModel.Inside (n + 2) z ↔ ∃ v : Vertex n, embed n v = z := by
  constructor
  · intro h
    exact ⟨vertexOfInside n z h, embed_vertexOfInside n z h⟩
  · rintro ⟨v, rfl⟩
    exact embed_inside n v

@[simp] theorem extend_embed (n : ℕ) (g : SquareSpin.Config n) (v : Vertex n) :
    extend n g (embed n v) = g v := by
  unfold extend
  rw [dite_eq_left (embed_inside n v)]
  congr 1

theorem extend_outside (n : ℕ) (g : SquareSpin.Config n) (z : Site)
    (h : ¬ InfiniteGridModel.Inside (n + 2) z) : extend n g z = false := by
  simp only [extend, dite_eq_right h]

theorem extend_supported (n : ℕ) (g : SquareSpin.Config n) :
    InfiniteGridModel.Supported (n + 2) (extend n g) := by
  intro z hz
  exact extend_outside n g z hz

@[simp] theorem restrict_extend (n : ℕ) (g : SquareSpin.Config n) :
    restrict n (extend n g) = g := by
  funext v
  exact extend_embed n g v

theorem extend_restrict (n : ℕ) (f : Config)
    (h : InfiniteGridModel.Supported (n + 2) f) : extend n (restrict n f) = f := by
  funext z
  by_cases hz : InfiniteGridModel.Inside (n + 2) z
  · simp only [extend, dite_eq_left hz, restrict, embed_vertexOfInside]
  · rw [extend_outside n (restrict n f) z hz, h z hz]

theorem eq_extend_of_supported (n : ℕ) (f : Config) (g : SquareSpin.Config n)
    (h : InfiniteGridModel.Supported (n + 2) f)
    (he : ∀ v, f (embed n v) = g v) : f = extend n g := by
  calc
    f = extend n (restrict n f) := (extend_restrict n f h).symm
    _ = extend n g := congrArg (extend n) (funext he)

@[simp] theorem extend_zero (n : ℕ) :
    extend n (fun _ => false) = (fun _ => false) := by
  funext z
  simp only [extend]
  split <;> rfl

theorem extend_eq_zero_iff (n : ℕ) (g : SquareSpin.Config n) :
    extend n g = (fun _ => false) ↔ g = (fun _ => false) := by
  constructor
  · intro h
    have he := congrArg (restrict n) h
    rw [restrict_extend] at he
    exact he
  · rintro rfl
    exact extend_zero n

theorem extend_north (n : ℕ) (g : SquareSpin.Config n) (v : Vertex n) :
    extend n g (InfiniteGridModel.north (embed n v)) = SquareSpin.northInput g v := by
  by_cases h : v.2.val + 1 < n + 2
  · have he : InfiniteGridModel.north (embed n v) = embed n (north v) := by
      have hx := v.1.isLt
      simp only [InfiniteGridModel.north, embed, north, Prod.mk.injEq]
      constructor
      · trivial
      · rw [min_eq_left (by omega)]
        omega
    rw [he, extend_embed]
    simp only [SquareSpin.northInput, ite_eq_left h]
  · rw [extend_outside n g _ (by
        have hx := v.1.isLt
        have hy := v.2.isLt
        simp only [InfiniteGridModel.Inside, InfiniteGridModel.north, embed]
        omega)]
    simp only [SquareSpin.northInput, ite_eq_right h]

theorem extend_east (n : ℕ) (g : SquareSpin.Config n) (v : Vertex n) :
    extend n g (InfiniteGridModel.east (embed n v)) = SquareSpin.eastInput g v := by
  by_cases h : v.1.val + 1 < n + 2
  · have he : InfiniteGridModel.east (embed n v) = embed n (east v) := by
      have hy := v.2.isLt
      simp only [InfiniteGridModel.east, embed, east, Prod.mk.injEq]
      constructor
      · rw [min_eq_left (by omega)]
        omega
      · trivial
    rw [he, extend_embed]
    simp only [SquareSpin.eastInput, ite_eq_left h]
  · rw [extend_outside n g _ (by
        have hx := v.1.isLt
        have hy := v.2.isLt
        simp only [InfiniteGridModel.Inside, InfiniteGridModel.east, embed]
        omega)]
    simp only [SquareSpin.eastInput, ite_eq_right h]

theorem extend_south (n : ℕ) (g : SquareSpin.Config n) (v : Vertex n) :
    extend n g (InfiniteGridModel.south (embed n v)) = SquareSpin.southInput g v := by
  by_cases h : 0 < v.2.val
  · have he : InfiniteGridModel.south (embed n v) = embed n (south v) := by
      simp only [InfiniteGridModel.south, embed, south, Prod.mk.injEq]
      exact ⟨True.intro, by omega⟩
    rw [he, extend_embed]
    simp only [SquareSpin.southInput, ite_eq_left h]
  · rw [extend_outside n g _ (by
        simp only [InfiniteGridModel.Inside, InfiniteGridModel.south, embed]
        omega)]
    simp only [SquareSpin.southInput, ite_eq_right h]

theorem extend_west (n : ℕ) (g : SquareSpin.Config n) (v : Vertex n) :
    extend n g (InfiniteGridModel.west (embed n v)) = SquareSpin.westInput g v := by
  by_cases h : 0 < v.1.val
  · have he : InfiniteGridModel.west (embed n v) = embed n (west v) := by
      simp only [InfiniteGridModel.west, embed, west, Prod.mk.injEq]
      exact ⟨by omega, True.intro⟩
    rw [he, extend_embed]
    simp only [SquareSpin.westInput, ite_eq_left h]
  · rw [extend_outside n g _ (by
        simp only [InfiniteGridModel.Inside, InfiniteGridModel.west, embed]
        omega)]
    simp only [SquareSpin.westInput, ite_eq_right h]

theorem update_embed (n : ℕ) (marks : InfiniteGridModel.Marks) (t : ℕ)
    (g : SquareSpin.Config n) (v : Vertex n) :
    InfiniteGridModel.update marks t (embed n v) (extend n g) =
      SquareSpin.rule g v (restrictMarks n marks t v) := by
  unfold InfiniteGridModel.update InfiniteGridModel.majority4
  rw [extend_north, extend_east, extend_south, extend_west]
  unfold SquareSpin.rule
  rw [SquareSpin.ones_eq_four_inputs]
  have hs : (SquareSpin.northInput g v).toNat + (SquareSpin.eastInput g v).toNat +
      (SquareSpin.southInput g v).toNat + (SquareSpin.westInput g v).toNat =
      (SquareSpin.eastInput g v).toNat + (SquareSpin.westInput g v).toNat +
      (SquareSpin.northInput g v).toNat + (SquareSpin.southInput g v).toNat := by omega
  simp only [hs, restrictMarks]

theorem colour_embed (n : ℕ) (v : Vertex n) :
    InfiniteGridModel.colour (embed n v) = SquareTasks.colour v := by
  unfold InfiniteGridModel.colour SquareTasks.colour embed
  congr 1
  apply propext
  omega

theorem synchronous_extend (n : ℕ) (marks : InfiniteGridModel.Marks)
    (g : SquareSpin.Config n) (t : ℕ) :
    InfiniteGridModel.synchronous marks (extend n g) t =
      extend n (SquareDynamics.synchronous (restrictMarks n marks) g t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    apply eq_extend_of_supported n _ _
      (InfiniteGridModel.synchronous_supported marks (n + 2) (extend n g)
        (extend_supported n g) (t + 1))
    intro v
    change InfiniteGridModel.update marks (t + 1) (embed n v)
        (InfiniteGridModel.synchronous marks (extend n g) t) =
      SquareSpin.rule (SquareDynamics.synchronous (restrictMarks n marks) g t) v
        (restrictMarks n marks (t + 1) v)
    rw [ih, update_embed]

theorem alternating_extend (n : ℕ) (marks : InfiniteGridModel.Marks)
    (g : SquareSpin.Config n) (phase : Bool) (t : ℕ) :
    InfiniteGridModel.alternating marks (extend n g) phase t =
      extend n (SquareDynamics.alternating (restrictMarks n marks) g phase t) := by
  apply eq_extend_of_supported n _ _
    (InfiniteGridModel.alternating_supported marks (n + 2) (extend n g)
      (extend_supported n g) phase t)
  intro v
  cases t with
  | zero => exact (extend_embed n g v)
  | succ t =>
    rw [InfiniteGridModel.splitting_succ,
      SquareDynamics.splitting_succ]
    rw [colour_embed, synchronous_extend, synchronous_extend,
      extend_embed, extend_embed]

theorem synchronous_supported_initial (n : ℕ) (marks : InfiniteGridModel.Marks)
    (f : Config) (h : InfiniteGridModel.Supported (n + 2) f) (t : ℕ) :
    InfiniteGridModel.synchronous marks f t =
      extend n (SquareDynamics.synchronous (restrictMarks n marks) (restrict n f) t) := by
  calc
    InfiniteGridModel.synchronous marks f t =
        InfiniteGridModel.synchronous marks (extend n (restrict n f)) t :=
      congrArg (fun a => InfiniteGridModel.synchronous marks a t) (extend_restrict n f h).symm
    _ = _ := synchronous_extend n marks (restrict n f) t

theorem alternating_supported_initial (n : ℕ) (marks : InfiniteGridModel.Marks)
    (f : Config) (h : InfiniteGridModel.Supported (n + 2) f) (phase : Bool) (t : ℕ) :
    InfiniteGridModel.alternating marks f phase t =
      extend n (SquareDynamics.alternating (restrictMarks n marks) (restrict n f) phase t) := by
  calc
    InfiniteGridModel.alternating marks f phase t =
        InfiniteGridModel.alternating marks (extend n (restrict n f)) phase t :=
      congrArg (fun a => InfiniteGridModel.alternating marks a phase t) (extend_restrict n f h).symm
    _ = _ := alternating_extend n marks (restrict n f) phase t

end MathResearchAnalysis.SquareGridEmbedding

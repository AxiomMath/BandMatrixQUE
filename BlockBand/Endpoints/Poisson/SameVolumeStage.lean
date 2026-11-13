module

public import BlockBand.Endpoints.Poisson.SequentialCollarsFull
public import BlockBand.Endpoints.Poisson.PoissonEndpointDefs

/-!
# Same-volume comparison: the stage statistics and the telescope

* `svStageLog`, `svStageStat`: the source-centred real logarithm `B_κ(e)` (the positive log
  increment) for the stage matrix of stage `S` of pairing `π`, at the energy `e = E + x/Λ` with
  matched leads `z = z_b(e)` (`boundaryZ`) and the physical source `κ = δW²/Λ` (so
  `κ/W² = δ/Λ`), and its integral `(πδ)⁻¹ ∫ f(x) B_κ(E + x/Λ) dx` against `f`.
* `sv_telescope`, `sv_stageStat_box_univ`: telescope each pairing to the common fully matched
  model and add the at most `2m` stage differences. The fully matched
  final models agree by `final_models_agree`.
* `sv_stageStat_empty`: at the empty stage the stage statistic is the positive log statistic
  `positiveLogStatistic` of the Hermitian part of the pairing with absorber `P_C`.
* `sv_measurable_stageStat`: measurability in the Gaussian coordinates.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers (boundaryZ matchedA)

section Stage

variable {m n W : ℕ} [NeZero n] (L : Fin m → ℕ)

/-- The positive log increment `B_κ(e)` for the stage matrix of stage `S`, pairing `π`
(base block `0`, buffer `buf`): `log (|det H_κ| / |det H_0|)` at `e = E + x/Λ`, `z = z_b(e)`,
with the physical source `κ = δW²/Λ`. -/
def svStageLog (π : Pairing) (S : Finset (Fin m)) (b E Λ δ : ℝ) (buf : ℕ) (x : ℝ)
    (ω : RingCoords n W) : ℝ :=
  Real.log (‖(stageMatrix L 0 π S (E + x / Λ) (boundaryZ b (E + x / Λ)) buf
      (δ * (W : ℝ) ^ 2 / Λ) ω).det‖ /
    ‖(stageMatrix L 0 π S (E + x / Λ) (boundaryZ b (E + x / Λ)) buf 0 ω).det‖)

/-- The stage statistic `(πδ)⁻¹ ∫ f(x) B_κ(E + x/Λ) dx` (same normalization as
`positiveLogStatistic`). -/
def svStageStat (π : Pairing) (S : Finset (Fin m)) (b E Λ δ : ℝ) (buf : ℕ) (f : ℝ → ℝ)
    (ω : RingCoords n W) : ℝ :=
  (Real.pi * δ)⁻¹ * ∫ x, f x * svStageLog L π S b E Λ δ buf x ω

/-- The fully matched final models of the two pairings have the same stage statistic. -/
theorem sv_stageStat_box_univ (hL : IsCollarLayout n L) (b E Λ δ : ℝ) (buf : ℕ) (f : ℝ → ℝ)
    (ω : RingCoords n W) :
    svStageStat L .box Finset.univ b E Λ δ buf f ω =
      svStageStat L .cyclic Finset.univ b E Λ δ buf f ω := by
  unfold svStageStat svStageLog
  simp_rw [final_models_agree hL, Matrix.det_submatrix_equiv_self]

/-!
### The removal order and the telescope
-/

/-- The first `t` collars `{k | k < t}` (the stage after `t` removals in increasing order). -/
def svStages (m t : ℕ) : Finset (Fin m) := Finset.univ.filter (fun k => k.val < t)

theorem sv_stages_zero : svStages m 0 = ∅ := by
  ext k; simp [svStages]

theorem sv_stages_self : svStages m m = Finset.univ := by
  ext k; simp [svStages]

theorem sv_stages_succ (k : Fin m) : svStages m (k.val + 1) = insert k (svStages m k.val) := by
  ext i
  simp only [svStages, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext h)
  · rintro (rfl | h) <;> omega

theorem sv_not_mem_stages (k : Fin m) : k ∉ svStages m k.val := by
  simp [svStages]

/-- **The telescope** over the `m` removals in increasing order. -/
theorem sv_telescope (g : Finset (Fin m) → ℝ) :
    g ∅ - g Finset.univ =
      ∑ k : Fin m, (g (svStages m k.val) - g (insert k (svStages m k.val))) := by
  have h : ∀ k : Fin m, g (svStages m k.val) - g (insert k (svStages m k.val)) =
      (fun t => g (svStages m t) - g (svStages m (t + 1))) k.val := by
    intro k; simp only [sv_stages_succ]
  rw [Finset.sum_congr rfl fun k _ => h k,
    Fin.sum_univ_eq_sum_range (fun t => g (svStages m t) - g (svStages m (t + 1))),
    Finset.sum_range_sub', sv_stages_zero, sv_stages_self]

/-- **Both pairings telescoped to the common fully matched model**: the
difference of the empty-stage statistics is the sum of the `2m` stage differences. -/
theorem sv_stageStat_empty_sub (hL : IsCollarLayout n L) (b E Λ δ : ℝ) (buf : ℕ) (f : ℝ → ℝ)
    (ω : RingCoords n W) :
    svStageStat L .cyclic ∅ b E Λ δ buf f ω - svStageStat L .box ∅ b E Λ δ buf f ω =
      ∑ k : Fin m, (svStageStat L .cyclic (svStages m k.val) b E Λ δ buf f ω -
          svStageStat L .cyclic (insert k (svStages m k.val)) b E Λ δ buf f ω) -
        ∑ k : Fin m, (svStageStat L .box (svStages m k.val) b E Λ δ buf f ω -
          svStageStat L .box (insert k (svStages m k.val)) b E Λ δ buf f ω) := by
  rw [← sv_telescope (fun S => svStageStat L .cyclic S b E Λ δ buf f ω),
    ← sv_telescope (fun S => svStageStat L .box S b E Λ δ buf f ω),
    sv_stageStat_box_univ L hL]
  ring

/-!
### The empty stage
-/

open Classical in
/-- The absorber projector `P_C` of the source blocks `C = InSource` on all ring sites. -/
def svSourceProj (s : ZMod n) (buf : ℕ) : Matrix (RingSite n W) (RingSite n W) ℂ :=
  diagonal fun x => if InSource L s buf x.1 then 1 else 0

omit [NeZero n] in
theorem sv_not_isMatched_empty (s : ZMod n) (p : ZMod n) : ¬ IsMatched L s ∅ p := by
  simp [IsMatched]

omit [NeZero n] in
theorem sv_not_isDeleted_empty (s : ZMod n) (p : ZMod n) : ¬ IsDeleted L s ∅ p := by
  simp [IsDeleted]

omit [NeZero n] in
/-- At the empty stage the stage matrix is `H_π - e + i(κ/W²)P_C`, with `H_π` the Hermitian part
of pairing `π` at `e = 0`. -/
theorem sv_stageFull_empty (π : Pairing) (s : ZMod n) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) :
    stageFull L s π ∅ e z buf κ ω =
      stageHerm L s π ∅ 0 0 ω - ((e : ℝ) : ℂ) • (1 : Matrix (RingSite n W) (RingSite n W) ℂ) +
        (((κ / (W : ℝ) ^ 2 : ℝ) : ℂ) * Complex.I) • svSourceProj L s buf := by
  ext x y
  have hM := sv_not_isMatched_empty L s
  simp only [stageFull, stageHerm, stageAbsorption, svSourceProj, hM, ite_false, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul,
    Prod.ext_iff]
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;> simp [h1, h2]
  all_goals (split_ifs <;> push_cast <;> ring)

theorem sv_stageMatrix_empty_det (π : Pairing) (s : ZMod n) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) :
    (stageMatrix L s π ∅ e z buf κ ω).det = (stageFull L s π ∅ e z buf κ ω).det := by
  have : stageMatrix L s π ∅ e z buf κ ω =
      (stageFull L s π ∅ e z buf κ ω).submatrix
        (Equiv.subtypeUnivEquiv fun x => sv_not_isDeleted_empty L s x.1)
        (Equiv.subtypeUnivEquiv fun x => sv_not_isDeleted_empty L s x.1) := rfl
  rw [this, Matrix.det_submatrix_equiv_self]

/-- **The empty stage is a positive log statistic**: for `W ≠ 0`,
`svStageStat π ∅ = 𝓡_δ(H_π; f)` with absorber `P_C`, `H_π` the Hermitian part of pairing `π`. -/
theorem sv_stageStat_empty (π : Pairing) (b E Λ δ : ℝ) (buf : ℕ) (f : ℝ → ℝ)
    (ω : RingCoords n W) (hW : W ≠ 0) :
    svStageStat L π ∅ b E Λ δ buf f ω =
      positiveLogStatistic (stageHerm L 0 π ∅ 0 0 ω) E Λ δ (svSourceProj L 0 buf) f := by
  unfold svStageStat svStageLog positiveLogStatistic
  congr 2
  funext x
  have hW' : ((W : ℝ) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hW)
  have hκ : δ * (W : ℝ) ^ 2 / Λ / (W : ℝ) ^ 2 = δ / Λ := by
    field_simp
  rw [sv_stageMatrix_empty_det, sv_stageMatrix_empty_det, sv_stageFull_empty, sv_stageFull_empty,
    hκ, zero_div]
  rfl

omit [NeZero n] in
/-- The cyclic Hermitian part at the empty stage is the ring matrix (`n ≥ 3`). -/
theorem sv_stageHerm_cyclic_empty (hn : 3 ≤ n) (s : ZMod n) (ω : RingCoords n W) :
    stageHerm L s .cyclic ∅ 0 0 ω = ringMatrix ω := by
  have h10 : (1 : ZMod n) ≠ 0 := by
    intro h
    have : ((1 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  have h20 : (2 : ZMod n) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd two_pos this) (by omega)
  have h1 : ∀ p q : ZMod n, p + 1 = q → p = q → False := fun p q h h' =>
    h10 (by linear_combination h - h')
  have h2 : ∀ p q : ZMod n, p + 1 = q → q + 1 = p → False := fun p q h h' =>
    h20 (by linear_combination h + h')
  ext x y
  have hM := sv_not_isMatched_empty L s
  simp only [stageHerm, bondTarget, hM, ite_false, ringMatrix, Complex.ofReal_zero, ite_self,
    sub_zero]
  by_cases hd : x.1 = y.1
  · have hb1 : ¬ x.1 + 1 = y.1 := fun h => h1 _ _ h hd
    have hb2 : ¬ y.1 + 1 = x.1 := fun h => h1 _ _ h hd.symm
    simp only [eq_false hb1, eq_false hb2, add_zero, eq_true hd, ite_true, ite_false]
  · by_cases hf : x.1 + 1 = y.1
    · have hb2 : ¬ y.1 + 1 = x.1 := fun h => h2 _ _ hf h
      simp only [eq_true hf, eq_false hb2, eq_false hd, eq_true hf.symm, zero_add, add_zero,
        ite_true, ite_false]
    · have hf' : ¬ y.1 = x.1 + 1 := fun h => hf h.symm
      by_cases hr : y.1 + 1 = x.1
      · simp only [eq_false hf, eq_true hr, eq_false hd, eq_false hf', eq_true hr.symm, zero_add,
          ite_true, ite_false]
      · have hr' : ¬ x.1 = y.1 + 1 := fun h => hr h.symm
        simp only [eq_false hf, eq_false hr, eq_false hd, eq_false hf', eq_false hr', add_zero,
          ite_false]

/-!
### Measurability
-/

theorem sv_measurable_matchedA : Measurable matchedA := by
  have : matchedA = fun E : ℝ => ((-E / 2 : ℝ) : ℂ) +
      ((-Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I := by
    funext E; apply Complex.ext <;> simp [matchedA]
  rw [this]
  fun_prop

theorem sv_measurable_boundaryZ (b : ℝ) : Measurable (boundaryZ b) := by
  have hA := sv_measurable_matchedA
  unfold boundaryZ
  exact hA.inv.add (measurable_const.mul hA)

omit [NeZero n] in
/-- The stage matrix with energy and lead parameter depending measurably on a real parameter is
jointly measurable. -/
theorem sv_measurable_stageFull_param (π : Pairing) (S : Finset (Fin m)) (s : ZMod n)
    (buf : ℕ) (κ : ℝ) {g : ℝ → ℝ} {zf : ℝ → ℂ} (hg : Measurable g) (hz : Measurable zf) :
    Measurable (fun q : RingCoords n W × ℝ => stageFull L s π S (g q.2) (zf q.2) buf κ q.1) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [stageFull, stageHerm, stageAbsorption, Matrix.add_apply, Matrix.diagonal_apply]
  have h1 : ∀ p a b, Measurable fun q : RingCoords n W × ℝ => q.1.1 p a b :=
    fun p a b => (Matrix.measurable_apply).comp ((measurable_pi_apply p).comp
      (measurable_fst.comp measurable_fst))
  have h2 : ∀ p a b, Measurable fun q : RingCoords n W × ℝ => q.1.2 p a b :=
    fun p a b => (Matrix.measurable_apply).comp ((measurable_pi_apply p).comp
      (measurable_snd.comp measurable_fst))
  have hgc : Measurable fun q : RingCoords n W × ℝ => ((g q.2 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hg.comp measurable_snd)
  have hre : Measurable fun q : RingCoords n W × ℝ => (((zf q.2).re : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Complex.measurable_re.comp (hz.comp measurable_snd))
  have him : Measurable fun q : RingCoords n W × ℝ => (((zf q.2).im : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Complex.measurable_im.comp (hz.comp measurable_snd))
  refine Measurable.add (Measurable.add (Measurable.add ?_ ?_) ?_) ?_ <;>
    split_ifs <;>
    first
    | exact measurable_const
    | exact hre
    | exact (h1 _ _ _).sub hgc
    | exact (h1 _ _ _).sub measurable_const
    | exact h2 _ _ _
    | exact continuous_star.measurable.comp (h2 _ _ _)
    | exact him.mul measurable_const

theorem sv_measurable_det_stageMatrix_param (π : Pairing) (S : Finset (Fin m)) (s : ZMod n)
    (buf : ℕ) (κ : ℝ) {g : ℝ → ℝ} {zf : ℝ → ℂ} (hg : Measurable g) (hz : Measurable zf) :
    Measurable (fun q : RingCoords n W × ℝ =>
      ‖(stageMatrix L s π S (g q.2) (zf q.2) buf κ q.1).det‖) := by
  have hF := sv_measurable_stageFull_param (W := W) L π S s buf κ hg hz
  have hsub : Measurable (fun q : RingCoords n W × ℝ =>
      stageMatrix L s π S (g q.2) (zf q.2) buf κ q.1) :=
    Measurable.of_eval_matrix _ fun x y => hF.eval_matrix (i := x.1) (j := y.1)
  exact continuous_norm.measurable.comp ((continuous_id.matrix_det).measurable.comp hsub)

/-- The stage statistic is a measurable function of the Gaussian coordinates. -/
theorem sv_measurable_stageStat (π : Pairing) (S : Finset (Fin m)) (b E Λ δ : ℝ) (buf : ℕ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (svStageStat (n := n) (W := W) L π S b E Λ δ buf f) := by
  have hg : Measurable fun x : ℝ => E + x / Λ := by fun_prop
  have hz : Measurable fun x : ℝ => boundaryZ b (E + x / Λ) :=
    (sv_measurable_boundaryZ b).comp hg
  have hA := sv_measurable_det_stageMatrix_param (W := W) L π S (0 : ZMod n) buf (δ * (W : ℝ) ^ 2 / Λ) hg hz
  have hB := sv_measurable_det_stageMatrix_param (W := W) L π S (0 : ZMod n) buf 0 hg hz
  have hl := Real.measurable_log.comp (hA.div hB)
  have hm : Measurable (fun q : RingCoords n W × ℝ =>
      f q.2 * svStageLog L π S b E Λ δ buf q.2 q.1) :=
    (hf.measurable.comp measurable_snd).mul hl
  unfold svStageStat
  exact ((hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable).const_mul _

end Stage

end BlockBand.Endpoints

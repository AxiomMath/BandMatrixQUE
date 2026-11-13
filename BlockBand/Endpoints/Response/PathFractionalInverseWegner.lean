module

public import BlockBand.Endpoints.Response.PathFractionalInverseDisk
public import BlockBand.Endpoints.Poisson.BlockModelCount

/-!
# Fractional inverse moments of deformed block GUE matrices at real energy

Law: a block model `M : Inputs.BlockModel k W` (`H = D + ⊕_j A_j` on `Fin k × Fin W`, `N = kW`)
with independent `GUE_W(c/W)` blocks independent of `(D, Y)` (`BlockModel.IsIndependent c`); no
norm bound on the Hermitian deformation `D`. The input is `Inputs.ConditionalBlockGUECount`, through
`blockModel_count_le`.

* `vecNormSq_le_of_eigenvalues`, `norm_inv_le_of_eigenvalues`: for Hermitian `Y` with
  all eigenvalues `|λ_j| ≥ a > 0` and real `δ`, `‖(Y + iδ)⁻¹‖ ≤ a⁻¹` (Euclidean operator norm).
* `meas_lt_norm_inv_le`: the tail `P{x < ‖(H + iδ)⁻¹‖} ≤ C/√c · N · 2/x`.
* `lintegral_rpow_le_of_tail`: the layer-cake integration of a tail `≤ min(1, L/x)`:
  `E X^s ≤ L^s/(1-s)`.
* `blockModel_lintegral_norm_inv_rpow_le`: `E ‖(H + iδ)⁻¹‖^s ≤ (K/√c · kW)^s/(1-s)`,
  `K = 2C` (`C` the constant of `blockModel_count_le`),
  uniformly in `k`, `W ≥ 1`, `c > 0`, the model, the real height `δ` and `0 < s < 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix Complex MeasureTheory ProbabilityTheory Set Filter
open BlockBand.Internal.Contracts.Inputs BlockBand.Foundations.Spectral
open scoped Matrix.Norms.L2Operator ComplexConjugate ENNReal NNReal

/-!
### Spectral lower bound
-/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem vecNormSq_unitary_mulVec {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (x : n → ℂ) :
    vecNormSq (U *ᵥ x) = vecNormSq x := by
  have h := star_dotProduct_gram_mulVec U x
  have hU' : Uᴴ * U = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hU
    rwa [star_eq_conjTranspose] at this
  rw [hU', one_mulVec, star_dotProduct_self] at h
  exact_mod_cast h.symm

/-- For Hermitian `Y` with all eigenvalues `|λ_j| ≥ a` and real `δ`:
`a² |v|² ≤ |(Y + iδ) v|²`. -/
theorem vecNormSq_le_of_eigenvalues {Y : Matrix n n ℂ} (hY : Y.IsHermitian) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : ∀ j, a ≤ |hY.eigenvalues j|) (δ : ℝ) (v : n → ℂ) :
    a ^ 2 * vecNormSq v ≤ vecNormSq ((Y + ((δ : ℂ) * I) • 1) *ᵥ v) := by
  set U : Matrix n n ℂ := (hY.eigenvectorUnitary : Matrix n n ℂ)
  have hUu : U ∈ unitaryGroup n ℂ := hY.eigenvectorUnitary.2
  have hsU : star U ∈ unitaryGroup n ℂ := Unitary.star_mem hUu
  have hUs : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hUu
  set d : n → ℂ := fun j => (hY.eigenvalues j : ℂ) + (δ : ℂ) * I
  have hdec : Y + ((δ : ℂ) * I) • 1 = U * Matrix.diagonal d * star U := by
    conv_lhs => rw [hY.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    have : Matrix.diagonal d =
        Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) + ((δ : ℂ) * I) • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [d]
      · simp [hij]
    rw [this, mul_add, add_mul, mul_smul_comm, mul_one, smul_mul_assoc, hUs]
  rw [hdec, ← mulVec_mulVec, ← mulVec_mulVec, vecNormSq_unitary_mulVec hUu]
  set w := star U *ᵥ v
  have hw : vecNormSq w = vecNormSq v := vecNormSq_unitary_mulVec hsU v
  rw [← hw]
  simp only [vecNormSq, mulVec_diagonal, norm_mul, mul_pow, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have h1 : a ^ 2 ≤ |hY.eigenvalues j| ^ 2 := pow_le_pow_left₀ ha0 (ha j) 2
  have h2 : |hY.eigenvalues j| ^ 2 ≤ ‖d j‖ ^ 2 := by
    rw [sq_abs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [d, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    nlinarith [sq_nonneg δ]
  exact h1.trans h2

/-- A matrix with `c² |v|² ≤ |A v|²` (`c > 0`) is invertible with `‖A⁻¹‖ ≤ c⁻¹`. -/
theorem isUnit_norm_inv_le_of_lower {A : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (hlow : ∀ v, c ^ 2 * vecNormSq v ≤ vecNormSq (A *ᵥ v)) : IsUnit A ∧ ‖A⁻¹‖ ≤ c⁻¹ := by
  have hinj : Function.Injective A.mulVec := by
    intro v w hvw
    have h0 : A *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
    have h1 := hlow (v - w)
    rw [h0] at h1
    have h2 : vecNormSq (0 : n → ℂ) = 0 := by simp [vecNormSq]
    rw [h2] at h1
    have h3 : vecNormSq (v - w) = 0 :=
      le_antisymm (by nlinarith [vecNormSq_nonneg (v - w), pow_pos hc 2]) (vecNormSq_nonneg _)
    exact sub_eq_zero.1 (vecNormSq_eq_zero h3)
  have hA : IsUnit A := mulVec_injective_iff_isUnit.1 hinj
  refine ⟨hA, l2_opNorm_le_of_vecNormSq (inv_nonneg.2 hc.le) fun u => ?_⟩
  have hd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  have hu : A *ᵥ (A⁻¹ *ᵥ u) = u := by rw [mulVec_mulVec, mul_nonsing_inv A hd, one_mulVec]
  have := hlow (A⁻¹ *ᵥ u)
  rw [hu] at this
  rw [inv_pow, le_inv_mul_iff₀ (by positivity)]
  exact this

/-- `‖(Y + iδ)⁻¹‖ ≤ a⁻¹` when every eigenvalue of the Hermitian `Y` has `|λ_j| ≥ a > 0`. -/
theorem norm_inv_le_of_eigenvalues {Y : Matrix n n ℂ} (hY : Y.IsHermitian) {a : ℝ} (ha0 : 0 < a)
    (ha : ∀ j, a ≤ |hY.eigenvalues j|) (δ : ℝ) : ‖(Y + ((δ : ℂ) * I) • 1)⁻¹‖ ≤ a⁻¹ :=
  (isUnit_norm_inv_le_of_lower ha0 (vecNormSq_le_of_eigenvalues hY ha0.le ha δ)).2

end Spectral

/-!
### Measurability
-/

theorem pfi_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun M : Matrix ι ι ℂ => M⁻¹) := by
  have : (fun M : Matrix ι ι ℂ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (measurable_inv.comp (continuous_id.matrix_det).measurable).smul
    (continuous_id.matrix_adjugate).measurable

/-- The block-diagonal matrix `⊕_j A_j` on `Fin k × Fin W` (as in `BlockModel.blockSum`). -/
def blockSumOf {k W : ℕ} (A : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  fun x y => if x.1 = y.1 then A x.1 x.2 y.2 else 0

theorem measurable_blockSumOf {k W : ℕ} :
    Measurable (blockSumOf (k := k) (W := W)) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  unfold blockSumOf
  by_cases h : x.1 = y.1
  · simp only [h, ite_true]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
  · simp only [h, ite_false]
    exact measurable_const

theorem blockSumOf_isHermitian {k W : ℕ} {A : Fin k → Matrix (Fin W) (Fin W) ℂ}
    (hA : ∀ j, (A j).IsHermitian) : (blockSumOf A).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, blockSumOf]
  by_cases h : x.1 = y.1
  · rw [ite_eq_left h.symm, ite_eq_left h]
    have := congrFun (congrFun (hA y.1).eq x.2) y.2
    rw [conjTranspose_apply] at this
    rw [h]; exact this
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, star_zero]

theorem BlockModel.H_eq_blockSumOf {k W : ℕ} (M : BlockModel k W) (w : M.Ω) :
    M.H w = M.D w + blockSumOf (M.A w) := rfl

theorem pfi_measurable_blockModel_H {k W : ℕ} (M : BlockModel k W) : Measurable M.H := by
  have : M.H = fun w => M.D w + blockSumOf (M.A w) := rfl
  rw [this]
  exact M.measurable_D.add (measurable_blockSumOf.comp M.measurable_A)

/-!
### The tail bound
-/

/-- An eigenvalue of `H` in `[-a, a]` is counted by the increasing-eigenvalue count. -/
theorem one_le_count_of_eigenvalue {k W : ℕ} {H : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ}
    (hH : H.IsHermitian) {a : ℝ} {j : Fin k × Fin W} (hj : |hH.eigenvalues j| < a) :
    1 ≤ (Finset.univ.filter fun i => increasingEigenvalue hH i ∈ Icc (-a) a).card := by
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  push Not
  refine ⟨((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).rev, Finset.mem_univ _, ?_⟩
  have he : increasingEigenvalue hH ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).rev =
      hH.eigenvalues j := by
    simp [increasingEigenvalue, Matrix.IsHermitian.eigenvalues]
  rw [he, mem_Icc]
  constructor <;> linarith [abs_lt.1 hj]

/-- Wegner tail (the first factorial moment of the eigenvalue count): for `x > 0`,
`P{x < ‖(H + iδ)⁻¹‖} ≤ C/√c · kW · (2/x)`. -/
theorem meas_lt_norm_inv_le {C : ℝ} {k W : ℕ} {c : ℝ} (M : BlockModel k W)
    (hcount : ∀ a b : ℝ, a ≤ b → Integrable (fun w => ((Finset.univ.filter fun i =>
        increasingEigenvalue (BlockModelCount.isHermitian_H M w) i ∈ Icc a b).card : ℝ)) M.P ∧
      (∫ w, ((Finset.univ.filter fun i =>
        increasingEigenvalue (BlockModelCount.isHermitian_H M w) i ∈ Icc a b).card : ℝ) ∂M.P) ≤
        C / Real.sqrt c * ((k * W : ℕ) : ℝ) * (b - a))
    (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    M.P {w | x < ‖(M.H w + ((δ : ℂ) * I) • 1)⁻¹‖} ≤
      ENNReal.ofReal (C / Real.sqrt c * ((k * W : ℕ) : ℝ) * (2 / x)) := by
  set a := 1 / x with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨hint, hle⟩ := hcount (-a) a (by linarith)
  set f := fun w => ((Finset.univ.filter fun i =>
    increasingEigenvalue (BlockModelCount.isHermitian_H M w) i ∈ Icc (-a) a).card : ℝ)
  have hsub : {w | x < ‖(M.H w + ((δ : ℂ) * I) • 1)⁻¹‖} ⊆ {w | 1 ≤ f w} := by
    intro w hw
    simp only [mem_ofPred_eq] at hw ⊢
    by_contra hf
    have hall : ∀ j, a ≤ |(BlockModelCount.isHermitian_H M w).eigenvalues j| := by
      intro j
      by_contra hj
      push Not at hj
      exact hf (Nat.one_le_cast.2 (one_le_count_of_eigenvalue _ hj))
    have := norm_inv_le_of_eigenvalues (BlockModelCount.isHermitian_H M w) ha0 hall δ
    rw [ha, one_div, inv_inv] at this
    linarith
  have hf0 : ∀ w, 0 ≤ f w := fun w => Nat.cast_nonneg _
  calc M.P {w | x < ‖(M.H w + ((δ : ℂ) * I) • 1)⁻¹‖} ≤ M.P {w | 1 ≤ f w} := measure_mono hsub
    _ ≤ ∫⁻ w, ENNReal.ofReal (f w) ∂M.P := by
        calc M.P {w | 1 ≤ f w} = ∫⁻ w, {w | 1 ≤ f w}.indicator 1 w ∂M.P := by
              rw [lintegral_indicator_one₀]
              exact (hint.aestronglyMeasurable.aemeasurable.nullMeasurable measurableSet_Ici)
          _ ≤ _ := lintegral_mono fun w => by
              by_cases h : 1 ≤ f w
              · simp only [indicator_of_mem (show w ∈ {w | 1 ≤ f w} from h), Pi.one_apply]
                exact ENNReal.one_le_ofReal.2 h
              · simp only [indicator_of_notMem (show w ∉ {w | 1 ≤ f w} from h)]
                exact zero_le
    _ = ENNReal.ofReal (∫ w, f w ∂M.P) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hle.trans_eq (by rw [ha]; ring))

/-!
### Layer-cake integration of the tail
-/

/-- Tail integration. If `X ≥ 0` is measurable and `P{t < X} ≤ L/t` for every `t > 0`
(`L ≥ 0`, `P` a probability), then `E X^s ≤ L^s/(1-s)` for `0 < s < 1`. -/
theorem lintegral_rpow_le_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX0 : ∀ w, 0 ≤ X w) (hXm : Measurable X) {L : ℝ}
    (hL : 0 ≤ L) (htail : ∀ t : ℝ, 0 < t → P {w | t < X w} ≤ ENNReal.ofReal (L / t))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∫⁻ w, ENNReal.ofReal (X w ^ s) ∂P ≤ ENNReal.ofReal (L ^ s / (1 - s)) := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul P (ae_of_all _ hX0) hXm.aemeasurable hs0]
  rcases hL.eq_or_lt with hL0 | hLpos
  · -- `L = 0`: the tail vanishes
    have h0 : ∫⁻ t in Ioi (0 : ℝ), P {a | t < X a} * ENNReal.ofReal (t ^ (s - 1)) = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun t ht => by
        have := htail t ht
        rw [← hL0, zero_div, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at this
        rw [this, zero_mul]]
      exact lintegral_zero
    rw [h0, mul_zero]
    exact zero_le
  -- split `Ioi 0 = Ioc 0 L ∪ Ioi L`
  have hfirst : ∫⁻ t in Ioc (0 : ℝ) L, P {a | t < X a} * ENNReal.ofReal (t ^ (s - 1)) ≤
      ENNReal.ofReal (L ^ s / s) := by
    calc ∫⁻ t in Ioc (0 : ℝ) L, P {a | t < X a} * ENNReal.ofReal (t ^ (s - 1))
        ≤ ∫⁻ t in Ioc (0 : ℝ) L, ENNReal.ofReal (t ^ (s - 1)) := by
          refine lintegral_mono fun t => ?_
          calc P {a | t < X a} * ENNReal.ofReal (t ^ (s - 1))
              ≤ 1 * ENNReal.ofReal (t ^ (s - 1)) := by gcongr; exact prob_le_one
            _ = _ := one_mul _
      _ = ENNReal.ofReal (∫ t in Ioc (0 : ℝ) L, t ^ (s - 1)) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            exact Real.rpow_nonneg ht.1.le _
      _ = ENNReal.ofReal (L ^ s / s) := by
          rw [← intervalIntegral.integral_of_le hL, integral_rpow (Or.inl (by linarith))]
          simp [Real.zero_rpow hs0.ne']
  have hsecond : ∫⁻ t in Ioi L, P {a | t < X a} * ENNReal.ofReal (t ^ (s - 1)) ≤
      ENNReal.ofReal (L ^ s / (1 - s)) := by
    calc ∫⁻ t in Ioi L, P {a | t < X a} * ENNReal.ofReal (t ^ (s - 1))
        ≤ ∫⁻ t in Ioi L, ENNReal.ofReal (L * t ^ (s - 2)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := hLpos.trans ht
          calc P {a | t < X a} * ENNReal.ofReal (t ^ (s - 1))
              ≤ ENNReal.ofReal (L / t) * ENNReal.ofReal (t ^ (s - 1)) := by
                gcongr; exact htail t ht0
            _ = ENNReal.ofReal (L * t ^ (s - 2)) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                have : t ^ (s - 1) = t * t ^ (s - 2) := by
                  rw [show s - 1 = 1 + (s - 2) by ring, Real.rpow_add ht0, Real.rpow_one]
                rw [this]
                field_simp
      _ = ENNReal.ofReal (∫ t in Ioi L, L * t ^ (s - 2)) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact (integrableOn_Ioi_rpow_of_lt (by linarith) hLpos).const_mul L
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact mul_nonneg hL (Real.rpow_nonneg (hLpos.trans ht).le _)
      _ = ENNReal.ofReal (L ^ s / (1 - s)) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hLpos]
          congr 1
          have h1 : L * L ^ (s - 2 + 1) = L ^ s := by
            rw [show s - 2 + 1 = s - 1 by ring, mul_comm, ← Real.rpow_add_one hLpos.ne']
            ring_nf
          have h2 : (s - 2 + 1) = -(1 - s) := by ring
          rw [mul_div_assoc', mul_neg, h1, h2, neg_div_neg_eq]
  calc ENNReal.ofReal s * ∫⁻ t in Ioi (0 : ℝ), P {a | t < X a} * ENNReal.ofReal (t ^ (s - 1))
      ≤ ENNReal.ofReal s * (ENNReal.ofReal (L ^ s / s) + ENNReal.ofReal (L ^ s / (1 - s))) := by
        gcongr
        rw [← Ioc_union_Ioi_eq_Ioi hL]
        exact (lintegral_union_le _ _ _).trans (add_le_add hfirst hsecond)
    _ = ENNReal.ofReal (L ^ s / (1 - s)) := by
        rw [← ENNReal.ofReal_add (by positivity) (div_nonneg (by positivity) (by linarith)),
          ← ENNReal.ofReal_mul hs0.le]
        congr 1
        have : (1 - s) ≠ 0 := by linarith
        field_simp
        ring

/-!
### The fractional inverse moment
-/

/-- **Fractional inverse moment of a deformed block GUE matrix at real energy.** Assume
`Inputs.ConditionalBlockGUECount`. There is an absolute `C > 0` such
that for all `k`, `W ≥ 1`, `c > 0`, every block model `M` with independent `GUE_W(c/W)`
blocks independent of `(D, Y)`, every real height `δ` and `0 < s < 1`:
`E ‖(H + iδ)⁻¹‖^s ≤ (C/√c · kW)^s / (1 - s)` (Euclidean operator norm, lower integral).
The deformation `D` is arbitrary Hermitian (no norm bound).
-/
theorem blockModel_lintegral_norm_inv_rpow_le (hCount : ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k W : ℕ), 0 < W → ∀ (c : ℝ), 0 < c →
      ∀ M : BlockModel k W, M.IsIndependent c → ∀ (δ s : ℝ), 0 < s → s < 1 →
        ∫⁻ w, ENNReal.ofReal (‖(M.H w + ((δ : ℂ) * I) • 1)⁻¹‖ ^ s) ∂M.P ≤
          ENNReal.ofReal ((C / Real.sqrt c * ((k * W : ℕ) : ℝ)) ^ s / (1 - s)) := by
  obtain ⟨C₀, hC₀, hmain⟩ := BlockModelCount.blockModel_count_le hCount
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro k W hW c hc M hM δ s hs0 hs1
  have hX : Measurable (fun w => ‖(M.H w + ((δ : ℂ) * I) • 1)⁻¹‖) :=
    continuous_norm.measurable.comp (pfi_measurable_inv.comp
      ((pfi_measurable_blockModel_H M).add_const _))
  refine lintegral_rpow_le_of_tail (fun w => norm_nonneg _) hX (by positivity) (fun t ht => ?_)
    hs0 hs1
  refine (meas_lt_norm_inv_le M (hmain k W hW c hc M hM) δ ht).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

end BlockBand.Endpoints

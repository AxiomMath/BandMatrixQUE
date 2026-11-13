module

public import BlockBand.DeterminantScore.WeightedTraceSmoothed
public import BlockBand.LocalWindow.Statements

/-!
# The local window for the unbounded observable `K₀`

The eigenvector quadratic form `u*K₀u` is compared with the window centre by applying the local
window to a smooth cutoff of `K₀`.

* `cutoffFn y = y χ(y)`, `χ` a `ContDiffBump` (`χ = 1` on `[-1/2, 1/2]`, support in `(-1, 1)`), and
  its dilation `dilatedCutoff L x = cutoffFn (x/L)`, so `L · dilatedCutoff L (K₀) = K_{0,L}`.
* `isSpectralTest_dilatedCutoff`: for each derivative order `k` there is `K_f` with
  `IsSpectralTest k K_f (dilatedCutoff L)` for every `L ≥ 1` (dilations do not increase derivative
  bounds); hence `isWindowObservable_cutoff`: `(ω, E) ↦ dilatedCutoff L (K₀(E))` is an
  `IsWindowObservable` of class (b).
* `quad_specFun`: `u*φ(K)u = Σⱼ φ(μⱼ)|(U*u)ⱼ|²`.
* `eth_unbounded` (deterministic part of the unbounded-observable bound): if `A = K₀ + G` with
  `‖G‖ ≤ C_G`, `Au = λu`, `|λ| ≤ 1`, `u` unit, the shift `z = λ + s m_E(λ)` satisfies
  `Im z ≥ 1/C₀`, `|z| ≤ C₀`, and the local window holds for `dilatedCutoff L (K₀)` with error `e`,
  then `|u*K₀u - j_{K₀}(E,λ)| ≤ (2/L)(1 + C_G)² + L e + (2s/L)(2 + 2C₀⁴)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeightedTrace

open Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.DeterminantScore.ScoreUnsmoothing BlockBand.LocalWindow
open scoped ComplexConjugate Matrix.Norms.L2Operator ContDiff

/-!
## The cutoff
-/

/-- The bump `χ`: `1` on `[-1/2, 1/2]`, supported in `(-1, 1)`. -/
def cutoffBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- `f(y) = y χ(y)`. -/
def cutoffFn (y : ℝ) : ℝ := y * cutoffBump y

/-- `f_L(x) = f(x/L)`, so that `L f_L(K₀) = K₀ χ(K₀/L) = K_{0,L}`. -/
def dilatedCutoff (L x : ℝ) : ℝ := cutoffFn (L⁻¹ * x)

theorem cutoffBump_eq_zero {y : ℝ} (hy : 1 ≤ |y|) : cutoffBump y = 0 :=
  cutoffBump.zero_of_le_dist (by show (1 : ℝ) ≤ dist y 0; simpa [Real.dist_eq] using hy)

theorem cutoffBump_eq_one {y : ℝ} (hy : |y| ≤ 1 / 2) : cutoffBump y = 1 :=
  cutoffBump.one_of_mem_closedBall (by
    show dist y 0 ≤ 1 / 2; simpa [Real.dist_eq] using hy)

theorem contDiff_cutoffFn : ContDiff ℝ ∞ cutoffFn :=
  contDiff_id.mul cutoffBump.contDiff

theorem abs_cutoffFn_le (y : ℝ) : |cutoffFn y| ≤ 1 := by
  unfold cutoffFn
  rw [abs_mul, abs_of_nonneg cutoffBump.nonneg]
  by_cases hy : 1 ≤ |y|
  · rw [cutoffBump_eq_zero hy]; norm_num
  · rw [not_le] at hy
    nlinarith [cutoffBump.nonneg (x := y), cutoffBump.le_one (x := y), abs_nonneg y]

theorem hasCompactSupport_cutoffFn : HasCompactSupport cutoffFn := by
  have : cutoffFn = (fun y : ℝ => y) * (cutoffBump : ℝ → ℝ) := rfl
  rw [this]
  exact cutoffBump.hasCompactSupport.mul_left

/-- Every derivative of `f` up to order `k` is bounded. -/
theorem cutoffFn_deriv_bound (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ k, ∀ x, |iteratedDeriv j cutoffFn x| ≤ K := by
  have hb : ∀ j : ℕ, ∃ C : ℝ, ∀ x, |iteratedDeriv j cutoffFn x| ≤ C := fun j => by
    have hc : Continuous (iteratedFDeriv ℝ j cutoffFn) :=
      contDiff_cutoffFn.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨C, hC⟩ := (hasCompactSupport_cutoffFn.iteratedFDeriv j).exists_bound_of_continuous hc
    exact ⟨C, fun x => by
      rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hC x⟩
  choose C hC using hb
  refine ⟨∑ j ∈ Finset.range (k + 1), |C j|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro j hj x
  calc |iteratedDeriv j cutoffFn x| ≤ |C j| := (hC j x).trans (le_abs_self _)
    _ ≤ _ := Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem dilatedCutoff_eq_zero {L x : ℝ} (hL : 0 < L) (hx : L ≤ |x|) : dilatedCutoff L x = 0 := by
  unfold dilatedCutoff cutoffFn
  rw [cutoffBump_eq_zero, mul_zero]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hL), ← div_eq_inv_mul, le_div_iff₀ hL]; linarith

theorem dilatedCutoff_eq {L x : ℝ} (hL : 0 < L) (hx : |x| ≤ L / 2) :
    L * dilatedCutoff L x = x := by
  unfold dilatedCutoff cutoffFn
  rw [cutoffBump_eq_one, mul_one, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hL), ← div_eq_inv_mul, div_le_iff₀ hL]; linarith

/-- **The dilated cutoff is a bounded smooth spectral test**, uniformly in `L ≥ 1`. -/
theorem isSpectralTest_dilatedCutoff (k : ℕ) :
    ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ L : ℝ, 1 ≤ L → IsSpectralTest k Kf (dilatedCutoff L) := by
  obtain ⟨K, hK0, hK⟩ := cutoffFn_deriv_bound k
  refine ⟨K, hK0, fun L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  have hfun : dilatedCutoff L = fun x => cutoffFn (L⁻¹ * x) := rfl
  refine ⟨?_, fun x => abs_cutoffFn_le _, ?_, ⟨0, 0, ?_, ?_⟩⟩
  · rw [hfun]; exact contDiff_cutoffFn.comp (contDiff_const.mul contDiff_id)
  · intro j hj x
    rw [hfun, iteratedDeriv_comp_const_mul (contDiff_infty.mp contDiff_cutoffFn j)]
    simp only
    rw [abs_mul]
    have h1 : |L⁻¹ ^ j| ≤ 1 := by
      rw [abs_pow, abs_of_pos (inv_pos.mpr hL0)]
      exact pow_le_one₀ (inv_nonneg.mpr hL0.le) (inv_le_one_of_one_le₀ hL)
    calc |L⁻¹ ^ j| * |iteratedDeriv j cutoffFn (L⁻¹ * x)| ≤ 1 * K :=
          mul_le_mul h1 (hK j hj _) (abs_nonneg _) zero_le_one
      _ = K := one_mul K
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop L] with x hx
    rw [dilatedCutoff_eq_zero hL0 (hx.trans (le_abs_self x))]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_atBot (-L)] with x hx
    rw [dilatedCutoff_eq_zero hL0 (by rw [abs_of_neg (by linarith)]; linarith)]

/-- `(ω, E) ↦ f_L(K₀(E))` is a window observable of class (b). -/
theorem isWindowObservable_cutoff {p : BlockBand.Parameters} {i : ZMod p.n} {k : ℕ} {Kf L : ℝ}
    (h : IsSpectralTest k Kf (dilatedCutoff L)) :
    IsWindowObservable p i k Kf (fun om E => spectralFn (dilatedCutoff L) (schurK0 p i om E)) :=
  Or.inr ⟨dilatedCutoff L, h, fun _ _ => rfl⟩

/-!
## Spectral quadratic forms
-/

section Spectral

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quad_specFun (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (φ : ℝ → ℝ) (u : ι → ℂ) :
    star u ⬝ᵥ (specFun U μ (fun x => (φ x : ℂ)) *ᵥ u) =
      ((∑ j, φ (μ j) * ‖(star (U : Matrix ι ι ℂ) *ᵥ u) j‖ ^ 2 : ℝ) : ℂ) := by
  set w := star (U : Matrix ι ι ℂ) *ᵥ u with hw
  have hsw : star w = star u ᵥ* (U : Matrix ι ι ℂ) := by
    rw [hw, star_mulVec, star_eq_conjTranspose, conjTranspose_conjTranspose]
  unfold specFun
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← hsw, ← hw]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]; ring

theorem cfc_eq_specFun {K : Matrix ι ι ℂ} (hK : K.IsHermitian) (f : ℝ → ℝ) :
    spectralFn f K = specFun hK.eigenvectorUnitary hK.eigenvalues (fun x => (f x : ℂ)) := by
  unfold spectralFn
  simp only [hK, ↓reduceDIte]
  rfl

theorem specFun_ofReal_id {K : Matrix ι ι ℂ} (hK : K.IsHermitian) :
    K = specFun hK.eigenvectorUnitary hK.eigenvalues (fun x => ((x : ℝ) : ℂ)) :=
  (specFun_id _ _ (eq_eigenvectorUnitary_decomp hK)).symm

/-- `Γ = s (X*X)⁻¹`, `X = K - z`, is the spectral function `s/|x - z|²` for `Im z ≠ 0`. -/
theorem gamma_eq_specFun {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) :
    (s : ℂ) • ((K - z • 1)ᴴ * (K - z • 1))⁻¹ = specFun hK.eigenvectorUnitary hK.eigenvalues
      (fun x => ((s / Complex.normSq ((x : ℂ) - z) : ℝ) : ℂ)) := by
  set U := hK.eigenvectorUnitary
  set μ := hK.eigenvalues
  have hX : K - z • 1 = specFun U μ (fun x => (x : ℂ) - z) := by
    conv_lhs => rw [specFun_ofReal_id hK]
    rw [← specFun_const U μ z, specFun_sub]
  have hne : ∀ x : ℝ, Complex.normSq ((x : ℂ) - z) ≠ 0 := fun x h => by
    rw [Complex.normSq_eq_zero, sub_eq_zero] at h
    apply hz; rw [← h]; simp
  have hXX : (K - z • 1)ᴴ * (K - z • 1) =
      specFun U μ (fun x => ((Complex.normSq ((x : ℂ) - z) : ℝ) : ℂ)) := by
    rw [hX, ← star_eq_conjTranspose, star_specFun, specFun_mul]
    congr 1; funext x
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  have hinv : ((K - z • 1)ᴴ * (K - z • 1))⁻¹ =
      specFun U μ (fun x => ((1 / Complex.normSq ((x : ℂ) - z) : ℝ) : ℂ)) := by
    apply Matrix.inv_eq_right_inv
    rw [hXX, specFun_mul]
    have e : (fun x : ℝ => ((Complex.normSq ((x : ℂ) - z) : ℝ) : ℂ) *
        ((1 / Complex.normSq ((x : ℂ) - z) : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
      funext x; rw [← Complex.ofReal_mul, mul_one_div_cancel (hne x), Complex.ofReal_one]
    rw [e, specFun_const, one_smul]
  rw [hinv, specFun_smul]
  congr 1; funext x
  rw [← Complex.ofReal_mul]; congr 1; ring

/-- `x²/|x - z|² ≤ 2 + 2(Re z)²/(Im z)²`. -/
theorem sq_div_normSq_le (x : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    x ^ 2 / Complex.normSq ((x : ℂ) - z) ≤ 2 + 2 * z.re ^ 2 / z.im ^ 2 := by
  have hn : Complex.normSq ((x : ℂ) - z) = (x - z.re) ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have hi : 0 < z.im ^ 2 := by positivity
  have hpos : 0 < (x - z.re) ^ 2 + z.im ^ 2 := by positivity
  rw [hn, div_le_iff₀ hpos]
  have h1 : 2 * z.re ^ 2 / z.im ^ 2 * z.im ^ 2 = 2 * z.re ^ 2 := by field_simp
  have h2 : 0 ≤ 2 * z.re ^ 2 / z.im ^ 2 * (x - z.re) ^ 2 := by positivity
  nlinarith [sq_nonneg (x - 2 * z.re)]

end Spectral

/-!
## The ETH for the unbounded deformation
-/

theorem windowCenter_sub {p : BlockBand.Parameters} {i : ZMod p.n} (B₁ B₂ K : PairMatrix p i)
    (s lam : ℝ) :
    windowCenter p i (B₁ - B₂) K s lam = windowCenter p i B₁ K s lam - windowCenter p i B₂ K s lam := by
  unfold windowCenter
  rw [Matrix.sub_mul, trace_sub, Complex.sub_re]; ring

theorem windowCenter_smul {p : BlockBand.Parameters} {i : ZMod p.n} (c : ℝ) (B K : PairMatrix p i)
    (s lam : ℝ) :
    windowCenter p i ((c : ℂ) • B) K s lam = c * windowCenter p i B K s lam := by
  unfold windowCenter
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]; ring

/-- **Unbounded-observable bound** (deterministic part): under the window error `e` for
`dilatedCutoff L (K₀)`, `|u*K₀u - j_{K₀}(E,λ)| ≤ (2/L)(1 + C_G)² + L e + (2s/L)(2 + 2C₀⁴)`. -/
theorem eth_unbounded {p : BlockBand.Parameters} {i : ZMod p.n} {K G A : PairMatrix p i}
    (hK : K.IsHermitian) (hAK : A = K + G) {CG C₀ L s lam e : ℝ} (hG : ‖G‖ ≤ CG)
    (hL : 1 ≤ L) (hs : 0 ≤ s) (hC₀ : 0 < C₀)
    (hzi : C₀⁻¹ ≤ ((lam : ℂ) + (s : ℂ) * pairDyson p i K s lam).im)
    (hzn : ‖(lam : ℂ) + (s : ℂ) * pairDyson p i K s lam‖ ≤ C₀) (hlam : |lam| ≤ 1)
    {u : PairSite p i → ℂ} (hu : star u ⬝ᵥ u = 1) (hAu : A *ᵥ u = (lam : ℂ) • u)
    (hwin : |(star u ⬝ᵥ (spectralFn (dilatedCutoff L) K *ᵥ u)).re -
      windowCenter p i (spectralFn (dilatedCutoff L) K) K s lam| ≤ e) :
    ‖star u ⬝ᵥ (K *ᵥ u) - ((windowCenter p i K K s lam : ℝ) : ℂ)‖ ≤
      2 / L * (1 + CG) ^ 2 + L * e + 2 * s / L * (2 + 2 * C₀ ^ 4) := by
  have hL0 : 0 < L := by linarith
  set U := hK.eigenvectorUnitary
  set μ := hK.eigenvalues
  set w := star (U : Matrix (PairSite p i) (PairSite p i) ℂ) *ᵥ u
  set z := (lam : ℂ) + (s : ℂ) * pairDyson p i K s lam with hz
  have hzim : 0 < z.im := lt_of_lt_of_le (inv_pos.mpr hC₀) hzi
  set h : ℝ → ℝ := fun x => x - L * dilatedCutoff L x with hh
  have hhb : ∀ x, |h x| ≤ 2 / L * x ^ 2 := fun x => by
    show |x - L * dilatedCutoff L x| ≤ 2 / L * x ^ 2
    by_cases hx : |x| ≤ L / 2
    · rw [dilatedCutoff_eq hL0 hx, sub_self, abs_zero]; positivity
    · rw [not_le] at hx
      have hLf : L * dilatedCutoff L x = x * cutoffBump (L⁻¹ * x) := by
        unfold dilatedCutoff cutoffFn
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hL0.ne', one_mul]
      have h1 : |x - L * dilatedCutoff L x| ≤ |x| := by
        rw [hLf, show x - x * cutoffBump (L⁻¹ * x) = x * (1 - cutoffBump (L⁻¹ * x)) by ring,
          abs_mul, abs_of_nonneg (sub_nonneg.mpr cutoffBump.le_one)]
        nlinarith [cutoffBump.nonneg (x := L⁻¹ * x), abs_nonneg x]
      have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      rw [hx2, div_mul_eq_mul_div, le_div_iff₀ hL0]
      nlinarith [abs_nonneg x]
  -- spectral forms
  have hKs := specFun_ofReal_id hK
  have hB := cfc_eq_specFun hK (dilatedCutoff L)
  have qK := quad_specFun U μ (fun x => x) u
  have qB : star u ⬝ᵥ (specFun U μ (fun x => ((dilatedCutoff L x : ℝ) : ℂ)) *ᵥ u) =
      ((∑ j, dilatedCutoff L (μ j) * ‖w j‖ ^ 2 : ℝ) : ℂ) := quad_specFun U μ (dilatedCutoff L) u
  have qK2 := quad_specFun U μ (fun x => x ^ 2) u
  have qK' : star u ⬝ᵥ (K *ᵥ u) = ((∑ j, μ j * ‖w j‖ ^ 2 : ℝ) : ℂ) := by
    have := quad_specFun U μ (fun x => x) u
    rwa [← hKs] at this
  -- ‖Ku‖² ≤ (1 + CG)²
  have hKu : ∑ j, μ j ^ 2 * ‖w j‖ ^ 2 ≤ (1 + CG) ^ 2 := by
    have hKK : K * K = specFun U μ (fun x => (((fun x : ℝ => x ^ 2) x : ℝ) : ℂ)) := by
      rw [show specFun U μ (fun x => (((fun x : ℝ => x ^ 2) x : ℝ) : ℂ)) =
          specFun U μ (fun x => ((x : ℝ) : ℂ)) * specFun U μ (fun x => ((x : ℝ) : ℂ)) by
        rw [specFun_mul]; congr 1; funext x; push_cast; ring, ← hKs]
    have e1 : star (K *ᵥ u) ⬝ᵥ (K *ᵥ u) = ((∑ j, μ j ^ 2 * ‖w j‖ ^ 2 : ℝ) : ℂ) := by
      rw [star_mulVec, ← dotProduct_mulVec, hK.eq, mulVec_mulVec, hKK, qK2]
    have hKu' : K *ᵥ u = (lam : ℂ) • u - G *ᵥ u := by
      rw [← hAu, hAK, add_mulVec]; abel
    set y : EuclideanSpace ℂ (PairSite p i) := WithLp.toLp 2 (K *ᵥ u)
    have hu1 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (PairSite p i))‖ = 1 := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
      have := congrArg Complex.re hu
      simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
        Complex.conj_mul', Complex.one_re] at this
      rw [← this]
      refine Finset.sum_congr rfl fun a _ => ?_
      norm_cast
    have hGu : ‖(WithLp.toLp 2 (G *ᵥ u) : EuclideanSpace ℂ (PairSite p i))‖ ≤ CG := by
      have := G.l2_opNorm_mulVec (WithLp.toLp 2 u)
      rw [hu1, mul_one] at this
      exact this.trans hG
    have hy : ‖y‖ ≤ 1 + CG := by
      have : y = (lam : ℂ) • (WithLp.toLp 2 u : EuclideanSpace ℂ (PairSite p i)) -
          (WithLp.toLp 2 (G *ᵥ u) : EuclideanSpace ℂ (PairSite p i)) := by
        simp only [y, hKu', WithLp.toLp_sub, WithLp.toLp_smul]
      rw [this]
      have h1 : ‖(lam : ℂ) • (WithLp.toLp 2 u : EuclideanSpace ℂ (PairSite p i))‖ ≤ 1 := by
        rw [norm_smul, hu1, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hlam
      exact (norm_sub_le _ _).trans (by linarith)
    have e2 : (star (K *ᵥ u) ⬝ᵥ (K *ᵥ u)).re = ‖y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.conj_mul']
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [y]
      norm_cast
    have := congrArg Complex.re e1
    rw [Complex.ofReal_re, e2] at this
    rw [← this]
    exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  -- the quadratic tail
  have htail : |∑ j, h (μ j) * ‖w j‖ ^ 2| ≤ 2 / L * (1 + CG) ^ 2 := by
    calc |∑ j, h (μ j) * ‖w j‖ ^ 2| ≤ ∑ j, |h (μ j)| * ‖w j‖ ^ 2 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun j _ => by rw [abs_mul, abs_of_nonneg (sq_nonneg ‖w j‖)]
      _ ≤ ∑ j, 2 / L * μ j ^ 2 * ‖w j‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hhb _) (by positivity)
      _ = 2 / L * ∑ j, μ j ^ 2 * ‖w j‖ ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hKu (by positivity)
  -- the centre tail
  have hΓ : windowGamma p i K s lam = specFun U μ
      (fun x => ((s / Complex.normSq ((x : ℂ) - z) : ℝ) : ℂ)) := by
    unfold windowGamma
    exact gamma_eq_specFun hK hzim.ne' s
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := card_pairSite_real
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hcen : |windowCenter p i (K - (L : ℂ) • spectralFn (dilatedCutoff L) K) K s lam| ≤
      2 * s / L * (2 + 2 * C₀ ^ 4) := by
    have hhK : K - (L : ℂ) • spectralFn (dilatedCutoff L) K = specFun U μ (fun x => ((h x : ℝ) : ℂ)) := by
      rw [hB, show specFun U μ (fun x => ((h x : ℝ) : ℂ)) = specFun U μ (fun x => ((x : ℝ) : ℂ)) -
          (L : ℂ) • specFun U μ (fun x => ((dilatedCutoff L x : ℝ) : ℂ)) by
        rw [specFun_smul, specFun_sub]; congr 1; funext x; simp [hh], ← hKs]
    unfold windowCenter
    rw [hhK, hΓ, specFun_mul, trace_specFun]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
    have hzr : z.re ^ 2 / z.im ^ 2 ≤ C₀ ^ 4 := by
      have h1 : z.re ^ 2 ≤ C₀ ^ 2 := by
        have := Complex.abs_re_le_norm z
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (this.trans hzn) 2
      have h2 : C₀⁻¹ ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ (by positivity) hzi 2
      rw [div_le_iff₀ (by positivity)]
      have : C₀ ^ 4 * C₀⁻¹ ^ 2 = C₀ ^ 2 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ C₀ ^ 4)]
    have hterm : ∀ j, |h (μ j) * (s / Complex.normSq ((μ j : ℂ) - z))| ≤
        2 / L * s * (2 + 2 * C₀ ^ 4) := fun j => by
      have hn : 0 < Complex.normSq ((μ j : ℂ) - z) := by
        rw [Complex.normSq_pos, sub_ne_zero]; intro h0; have := congrArg Complex.im h0
        simp at this; linarith
      rw [abs_mul, abs_of_nonneg (div_nonneg hs hn.le)]
      have hq := sq_div_normSq_le (μ j) hzim.ne'
      calc |h (μ j)| * (s / Complex.normSq ((μ j : ℂ) - z))
          ≤ 2 / L * μ j ^ 2 * (s / Complex.normSq ((μ j : ℂ) - z)) :=
            mul_le_mul_of_nonneg_right (hhb _) (div_nonneg hs hn.le)
        _ = 2 / L * s * (μ j ^ 2 / Complex.normSq ((μ j : ℂ) - z)) := by ring
        _ ≤ 2 / L * s * (2 + 2 * z.re ^ 2 / z.im ^ 2) := by gcongr
        _ ≤ 2 / L * s * (2 + 2 * C₀ ^ 4) := by
            gcongr
            rw [mul_div_assoc]; linarith
    have hsum : |∑ j, h (μ j) * (s / Complex.normSq ((μ j : ℂ) - z))| ≤
        ∑ _j : PairSite p i, 2 / L * s * (2 + 2 * C₀ ^ 4) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hsum
    rw [abs_mul, abs_of_pos (by positivity)]
    calc (2 * (p.W : ℝ))⁻¹ * |∑ j, h (μ j) * (s / Complex.normSq ((μ j : ℂ) - z))|
        ≤ (2 * (p.W : ℝ))⁻¹ * (2 * p.W * (2 / L * s * (2 + 2 * C₀ ^ 4))) := by gcongr
      _ = _ := by field_simp
  -- assemble
  have hsplit : star u ⬝ᵥ (K *ᵥ u) - ((windowCenter p i K K s lam : ℝ) : ℂ) =
      (((∑ j, h (μ j) * ‖w j‖ ^ 2) + L * ((star u ⬝ᵥ (spectralFn (dilatedCutoff L) K *ᵥ u)).re -
        windowCenter p i (spectralFn (dilatedCutoff L) K) K s lam) -
        windowCenter p i (K - (L : ℂ) • spectralFn (dilatedCutoff L) K) K s lam : ℝ) : ℂ) := by
    rw [windowCenter_sub, windowCenter_smul, qK']
    rw [hB, qB, Complex.ofReal_re, ← Complex.ofReal_sub]
    congr 1
    simp only [hh, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  rw [hsplit, Complex.norm_real, Real.norm_eq_abs]
  have h2 : |L * ((star u ⬝ᵥ (spectralFn (dilatedCutoff L) K *ᵥ u)).re -
      windowCenter p i (spectralFn (dilatedCutoff L) K) K s lam)| ≤ L * e := by
    rw [abs_mul, abs_of_pos hL0]; exact mul_le_mul_of_nonneg_left hwin hL0.le
  calc _ ≤ |∑ j, h (μ j) * ‖w j‖ ^ 2| + |L * ((star u ⬝ᵥ (spectralFn (dilatedCutoff L) K *ᵥ u)).re -
        windowCenter p i (spectralFn (dilatedCutoff L) K) K s lam)| +
        |windowCenter p i (K - (L : ℂ) • spectralFn (dilatedCutoff L) K) K s lam| := by
        have := abs_sub (∑ j, h (μ j) * ‖w j‖ ^ 2 + L * ((star u ⬝ᵥ
          (spectralFn (dilatedCutoff L) K *ᵥ u)).re -
          windowCenter p i (spectralFn (dilatedCutoff L) K) K s lam))
          (windowCenter p i (K - (L : ℂ) • spectralFn (dilatedCutoff L) K) K s lam)
        have := abs_add_le (∑ j, h (μ j) * ‖w j‖ ^ 2) (L * ((star u ⬝ᵥ
          (spectralFn (dilatedCutoff L) K *ᵥ u)).re -
          windowCenter p i (spectralFn (dilatedCutoff L) K) K s lam))
        linarith
    _ ≤ _ := by linarith

end BlockBand.DeterminantScore.WeightedTrace

module

public import BlockBand.Layers.ComparisonBranch
public import BlockBand.Layers.MeanEquations
public import BlockBand.Layers.TraceCovariance
public import BlockBand.Layers.GaussianAbsorption

/-!
# Signs, bounds and residuals of the layer means

Law: `layerLaw W b σ` (fresh `A_a ~ GUE_W(c/W)`, `c = 1 - 2b`, bonds `Gin(b/W)`), deterministic
Hermitian `X`, real `E`; `𝒢 = layerResolvent σ E z X ω`. Norms: `ℓ²` operator norm on matrices,
sup norm on `Fin 2 → ℂ`.

* `lct_im_diag` (deterministic, every sample with Hermitian blocks, every `z`):
  `Im 𝒢_xx = -Im z Σ_{p port} |𝒢_{x p}|²`, from `𝒢 - 𝒢* = 𝒢 (𝒢⁻¹* - 𝒢⁻¹) 𝒢*` and
  `𝒢⁻¹* - 𝒢⁻¹ = (z̄ - z) P_ports` (the sign of `-Im 𝒢 ≥ 0`). If the layer matrix is
  singular, `𝒢 = 0` and both sides vanish.
* Corollaries: `Im g_a(𝒢) ≤ 0`, `Im g_{port j}(𝒢) ≤ 0` for `Im z ≥ 0`, and the deterministic port
  bound `|g_{port j}(𝒢)| ≤ (Im z)⁻¹` for `Im z > 0`; for the means
  (`lct_im_meanA_nonpos`, `lct_im_meanP_nonpos`, `lct_norm_meanP_le`), a.s. (GUE blocks are
  Hermitian a.s., `lct_ae_blocks_isHermitian`).
* `lct_norm_meanA_le`: `|ḡ_a| ≤ K` from `(E‖𝒢‖) ≤ K` (absorber moment `p = 1`).
* `lct_cov_one_letter`: the one-letter covariance bound `‖Cov(W⁻¹Tr P𝒢, Q𝒢)‖ ≤ C W⁻²` for
  `‖P‖, ‖Q‖ ≤ 1` (`TraceMatrixContract.covariance` with `L = 1`, `K = 1`, through
  `traceCovariance_holds`).
* `lct_norm_residTop_le`: the physical residual `R_phys = meqResidTop` has norm
  `≤ (#blocks + #blocks·#ports) B` when every covariance in it has norm `≤ B`.
* `lct_norm_shifted_inv_le`: `‖(H - diag σ)⁻¹‖ ≤ y⁻¹` for `H` Hermitian, `-Im σ ≥ y > 0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. The imaginary part of the diagonal of `𝒢`
-/

section Pointwise

variable {W : ℕ} {σ : LayerShape}

/-- The top block `diag(A_a) - E - X` is Hermitian for Hermitian blocks and Hermitian `X`. -/
theorem lct_top_isHermitian (E : ℝ) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) {A : Fin σ.blocks → Matrix (Fin W) (Fin W) ℂ}
    (hA : ∀ j, (A j).IsHermitian) :
    (blockDiag A - (E : ℂ) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X).IsHermitian := by
  refine ((blockDiag_isHermitian hA).sub ?_).sub hX
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

/-- `𝒢⁻¹* - 𝒢⁻¹ = diag(0, (z̄ - z))`. -/
theorem lct_layerMatrix_conj_sub (E : ℝ) (z : ℂ) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) (ω : LayerSample W σ) (hA : ∀ j, (ω.1 j).IsHermitian) :
    (layerMatrix σ E z X ω)ᴴ - layerMatrix σ E z X ω =
      diagonal (Sum.elim (fun _ => (0 : ℂ)) (fun _ => conj z - z)) := by
  have hT := lct_top_isHermitian E hX hA
  unfold layerMatrix
  rw [fromBlocks_conjTranspose, hT.eq, conjTranspose_conjTranspose, conjTranspose_smul,
    conjTranspose_one]
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [fromBlocks, diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- **Imaginary part of the diagonal of `𝒢`**: for a sample with Hermitian blocks,
`Im 𝒢_xx = -Im z Σ_{p port} |𝒢_{x,p}|²` (deterministic; trivially true if the layer matrix is
singular, where `𝒢 = 0`). -/
theorem lct_im_diag (E : ℝ) (z : ℂ) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) (ω : LayerSample W σ) (hA : ∀ j, (ω.1 j).IsHermitian)
    (x : LayerSite W σ) :
    (layerResolvent σ E z X ω x x).im =
      -(z.im * ∑ p : PortSite W σ, ‖layerResolvent σ E z X ω x (Sum.inr p)‖ ^ 2) := by
  set L := layerMatrix σ E z X ω with hLdef
  set G := layerResolvent σ E z X ω with hGdef
  have hGL : G = L⁻¹ := rfl
  by_cases hL : IsUnit L.det
  swap
  · have h0 : G = 0 := by rw [hGL]; exact Matrix.nonsing_inv_apply_not_isUnit _ hL
    simp [h0]
  have h1 : G * L = 1 := by rw [hGL]; exact Matrix.nonsing_inv_mul _ hL
  have hid : G - Gᴴ = G * (Lᴴ - L) * Gᴴ := by
    have e1 : G * Lᴴ * Gᴴ = G := by
      rw [Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one, Matrix.mul_one]
    have e2 : G * L * Gᴴ = Gᴴ := by rw [h1, Matrix.one_mul]
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [lct_layerMatrix_conj_sub E z hX ω hA] at hid
  have hxx := congrFun (congrFun hid x) x
  rw [Matrix.sub_apply, Matrix.mul_apply] at hxx
  simp only [mul_diagonal, conjTranspose_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    mul_zero, zero_mul, Finset.sum_const_zero, zero_add] at hxx
  have hterm : ∀ p : PortSite W σ, G x (Sum.inr p) * (conj z - z) * star (G x (Sum.inr p)) =
      (conj z - z) * ((‖G x (Sum.inr p)‖ ^ 2 : ℝ) : ℂ) := by
    intro p
    rw [Complex.star_def, mul_right_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    ring
  simp only [hterm] at hxx
  have him := congrArg Complex.im hxx
  rw [← Finset.mul_sum, Complex.sub_im, Complex.star_def, Complex.conj_im] at him
  rw [← Complex.ofReal_sum, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero,
    zero_add] at him
  rw [Complex.sub_im, Complex.conj_im] at him
  linarith

/-- `Im 𝒢_xx ≤ 0` for `Im z ≥ 0`. -/
theorem lct_im_diag_nonpos (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : ∀ j, (ω.1 j).IsHermitian) (x : LayerSite W σ) :
    (layerResolvent σ E z X ω x x).im ≤ 0 := by
  rw [lct_im_diag E z hX ω hA x, neg_nonpos]
  exact mul_nonneg hz (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Port diagonal entries: `|𝒢_pp| ≤ (Im z)⁻¹` for `Im z > 0`. -/
theorem lct_norm_port_diag_le (E : ℝ) {z : ℂ} (hz : 0 < z.im)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : ∀ j, (ω.1 j).IsHermitian) (p : PortSite W σ) :
    ‖layerResolvent σ E z X ω (Sum.inr p) (Sum.inr p)‖ ≤ (z.im)⁻¹ := by
  set g := layerResolvent σ E z X ω (Sum.inr p) (Sum.inr p) with hg
  have h1 := lct_im_diag E z hX ω hA (Sum.inr p)
  have hsq : ‖g‖ ^ 2 ≤ ∑ q : PortSite W σ,
      ‖layerResolvent σ E z X ω (Sum.inr p) (Sum.inr q)‖ ^ 2 :=
    Finset.single_le_sum (f := fun q : PortSite W σ =>
      ‖layerResolvent σ E z X ω (Sum.inr p) (Sum.inr q)‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ p)
  have h2 : z.im * ‖g‖ ^ 2 ≤ ‖g‖ := by
    have h3 := mul_le_mul_of_nonneg_left hsq hz.le
    have h4 : -g.im ≤ ‖g‖ := (neg_le_abs _).trans (Complex.abs_im_le_norm _)
    rw [← hg] at h1
    linarith
  rcases eq_or_lt_of_le (norm_nonneg g) with h0 | h0
  · rw [← h0]; exact inv_nonneg.mpr hz.le
  have h5 : z.im * ‖g‖ ≤ 1 := by
    have : z.im * ‖g‖ * ‖g‖ ≤ 1 * ‖g‖ := by nlinarith
    exact le_of_mul_le_mul_right this h0
  calc ‖g‖ = (z.im)⁻¹ * (z.im * ‖g‖) := by field_simp
    _ ≤ (z.im)⁻¹ * 1 := mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr hz.le)
    _ = (z.im)⁻¹ := mul_one _

theorem lct_im_normalized_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ((W : ℂ)⁻¹ * ∑ i ∈ s, f i).im = (W : ℝ)⁻¹ * ∑ i ∈ s, (f i).im := by
  rw [show (W : ℂ)⁻¹ = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul,
    Complex.im_sum]

/-- `Im g_a(𝒢) ≤ 0` for `Im z ≥ 0`. -/
theorem lct_im_physBlockTrace_nonpos (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : ∀ j, (ω.1 j).IsHermitian) (a : Fin σ.blocks) :
    (physBlockTrace (layerResolvent σ E z X ω) a).im ≤ 0 := by
  unfold physBlockTrace
  rw [lct_im_normalized_sum]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (Finset.sum_nonpos fun α _ => lct_im_diag_nonpos E hz hX ω hA _)

/-- `Im g_{port j}(𝒢) ≤ 0` for `Im z ≥ 0`. -/
theorem lct_im_portBlockTrace_nonpos (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : ∀ j, (ω.1 j).IsHermitian) (j : Fin σ.ports) :
    (portBlockTrace (layerResolvent σ E z X ω) j).im ≤ 0 := by
  unfold portBlockTrace
  rw [lct_im_normalized_sum]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (Finset.sum_nonpos fun α _ => lct_im_diag_nonpos E hz hX ω hA _)

/-- **Deterministic port bound** `|g_{port j}(𝒢)| ≤ (Im z)⁻¹` for `Im z > 0`. -/
theorem lct_norm_portBlockTrace_le (E : ℝ) {z : ℂ} (hz : 0 < z.im)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : ∀ j, (ω.1 j).IsHermitian) (j : Fin σ.ports) :
    ‖portBlockTrace (layerResolvent σ E z X ω) j‖ ≤ (z.im)⁻¹ := by
  unfold portBlockTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero, mul_zero]
    exact inv_nonneg.mpr hz.le
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ‖∑ α : Fin W, layerResolvent σ E z X ω (Sum.inr (j, α)) (Sum.inr (j, α))‖ ≤
      W * (z.im)⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α : Fin W, ‖layerResolvent σ E z X ω (Sum.inr (j, α)) (Sum.inr (j, α))‖
        ≤ ∑ _α : Fin W, (z.im)⁻¹ :=
          Finset.sum_le_sum fun α _ => lct_norm_port_diag_le E hz hX ω hA _
      _ = W * (z.im)⁻¹ := by simp
  calc (W : ℝ)⁻¹ * ‖∑ α : Fin W, layerResolvent σ E z X ω (Sum.inr (j, α)) (Sum.inr (j, α))‖
      ≤ (W : ℝ)⁻¹ * (W * (z.im)⁻¹) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (z.im)⁻¹ := by field_simp

end Pointwise

/-!
## 2. The means
-/

section Means

variable {W : ℕ} {b : ℝ} {σ : LayerShape}

/-- GUE blocks are Hermitian `layerLaw`-almost surely. -/
theorem lct_ae_blocks_isHermitian (W : ℕ) (b : ℝ) (σ : LayerShape) :
    ∀ᵐ ω ∂layerLaw W b σ, ∀ j, (ω.1 j).IsHermitian := by
  rw [absn_layerLaw_eq]
  exact (Measure.quasiMeasurePreserving_fst).ae
    (ae_blocks_isHermitian σ.blocks W (Real.toNNReal ((1 - 2 * b) / W)))

theorem lct_im_integral_nonpos {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f : Ω → ℂ}
    (hf : ∀ᵐ ω ∂ν, (f ω).im ≤ 0) : (∫ ω, f ω ∂ν).im ≤ 0 := by
  by_cases hi : Integrable f ν
  · have h := (Complex.imCLM.integral_comp_comm hi)
    simp only [Complex.imCLM_apply] at h
    rw [← h]
    exact integral_nonpos_of_ae hf
  · rw [integral_undef hi, Complex.zero_im]

/-- `Im ḡ_a ≤ 0` for the physical layer means. -/
theorem lct_im_meanA_nonpos (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (a : Fin σ.blocks) :
    (meqMeanA (layerLaw W b σ) (layerResolvent σ E z X) a).im ≤ 0 := by
  refine lct_im_integral_nonpos ?_
  filter_upwards [lct_ae_blocks_isHermitian W b σ] with ω hω
  exact lct_im_physBlockTrace_nonpos E hz hX ω hω a

/-- `Im ḡ_{port j} ≤ 0` for the port layer means. -/
theorem lct_im_meanP_nonpos (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (j : Fin σ.ports) :
    (meqMeanP (layerLaw W b σ) (layerResolvent σ E z X) j).im ≤ 0 := by
  refine lct_im_integral_nonpos ?_
  filter_upwards [lct_ae_blocks_isHermitian W b σ] with ω hω
  exact lct_im_portBlockTrace_nonpos E hz hX ω hω j

/-- **Deterministic bound on the port means**: `|ḡ_{port j}| ≤ (Im z)⁻¹`, every `W`. -/
theorem lct_norm_meanP_le (E : ℝ) {z : ℂ} (hz : 0 < z.im)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (j : Fin σ.ports) :
    ‖meqMeanP (layerLaw W b σ) (layerResolvent σ E z X) j‖ ≤ (z.im)⁻¹ := by
  have h := norm_integral_le_of_norm_le_const (μ := layerLaw W b σ)
    (f := fun ω => portBlockTrace (layerResolvent σ E z X ω) j) (C := (z.im)⁻¹) (by
      filter_upwards [lct_ae_blocks_isHermitian W b σ] with ω hω
      exact lct_norm_portBlockTrace_le E hz hX ω hω j)
  rwa [probReal_univ, mul_one] at h

/-- **Bound on the physical means** from the first absorber moment: `E‖𝒢‖ ≤ K` gives
`|ḡ_a| ≤ K`. -/
theorem lct_norm_meanA_le {E : ℝ} {z : ℂ} {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} {K : ℝ}
    (hK0 : 0 ≤ K) (hK : eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal 1) (layerLaw W b σ) ≤
      ENNReal.ofReal K) (a : Fin σ.blocks) :
    ‖meqMeanA (layerLaw W b σ) (layerResolvent σ E z X) a‖ ≤ K := by
  rw [ENNReal.ofReal_one] at hK
  have hmem : MemLp (fun ω => ‖layerResolvent σ E z X ω‖) 1 (layerLaw W b σ) :=
    memLp_iff.mpr (lt_of_le_of_lt hK ENNReal.ofReal_lt_top)
  have hint : Integrable (fun ω => ‖layerResolvent σ E z X ω‖) (layerLaw W b σ) :=
    memLp_one_iff_integrable.mp hmem
  have hI : ∫ ω, ‖layerResolvent σ E z X ω‖ ∂layerLaw W b σ ≤ K := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => norm_nonneg _)
      hmem.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal hK0 ?_
    rw [eLpNorm_one_eq_lintegral_enorm hmem.aestronglyMeasurable] at hK
    refine le_trans (le_of_eq ?_) hK
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (norm_nonneg _)]
  calc ‖meqMeanA (layerLaw W b σ) (layerResolvent σ E z X) a‖
      ≤ ∫ ω, ‖physBlockTrace (layerResolvent σ E z X ω) a‖ ∂layerLaw W b σ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖layerResolvent σ E z X ω‖ ∂layerLaw W b σ :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hint
          (ae_of_all _ fun ω => meq_norm_physBlockTrace_le _ a)
    _ ≤ K := hI

end Means

/-!
## 3. Norm lemmas
-/

section Norms

/-- `‖1‖ ≤ 1` for the `ℓ²` operator norm (no nonemptiness needed). -/
theorem lct_norm_one_le {n : Type*} [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← diagonal_one, l2_opNorm_diagonal]
  exact pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun _ => by simp

/-- `|W⁻¹ Tr N_ii| ≤ ‖N‖` for a two-block matrix. -/
theorem lct_norm_blockTrace_le {k W : ℕ} (N : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)
    (i : Fin k) : ‖blockTrace N i‖ ≤ ‖N‖ := by
  unfold blockTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ‖∑ α : Fin W, N (i, α) (i, α)‖ ≤ W * ‖N‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α : Fin W, ‖N (i, α) (i, α)‖ ≤ ∑ _α : Fin W, ‖N‖ :=
          Finset.sum_le_sum fun α _ => tfl_entry_le N _ _
      _ = W * ‖N‖ := by simp
  calc (W : ℝ)⁻¹ * ‖∑ α : Fin W, N (i, α) (i, α)‖ ≤ (W : ℝ)⁻¹ * (W * ‖N‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖N‖ := by field_simp

/-- `‖M₁₁‖ ≤ ‖M‖` (compression by the coordinate inclusion). -/
theorem lct_norm_toBlocks11_le {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : ‖M.toBlocks₁₁‖ ≤ ‖M‖ := by
  set J : Matrix n (n ⊕ m) ℂ := Matrix.of fun x y => if y = Sum.inl x then 1 else 0 with hJ
  have hJJ : J * Jᴴ = 1 := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [conjTranspose_apply, hJ, Matrix.of_apply, Sum.inl.injEq, reduceCtorEq, ite_false,
      star_zero, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply]
    rw [Finset.sum_eq_single y]
    · by_cases h : x = y <;> simp [h, eq_comm]
    · intro c _ hc; simp [hc]
    · simp
  have hJn : ‖J‖ ≤ 1 := by
    have h1 : ‖Jᴴ‖ * ‖Jᴴ‖ = ‖(Jᴴ)ᴴ * Jᴴ‖ := (l2_opNorm_conjTranspose_mul_self Jᴴ).symm
    rw [conjTranspose_conjTranspose, hJJ, l2_opNorm_conjTranspose] at h1
    have h2 := lct_norm_one_le (n := n)
    have h0 := norm_nonneg J
    nlinarith
  have heq : M.toBlocks₁₁ = J * M * Jᴴ := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply, hJ, Matrix.of_apply,
      Sum.inl.injEq, reduceCtorEq, ite_false, star_zero, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, toBlocks₁₁]
    simp [Finset.sum_ite_eq, eq_comm]
  rw [heq]
  calc ‖J * M * Jᴴ‖ ≤ ‖J‖ * ‖M‖ * ‖Jᴴ‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖M‖ * 1 := by
        rw [l2_opNorm_conjTranspose]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hJn (norm_nonneg _)) hJn (norm_nonneg _)
          (by positivity)
    _ = ‖M‖ := by ring

/-- **Shifted inverse bound**: `H` Hermitian, `-Im σ_p ≥ y > 0`: `‖(H - diag σ)⁻¹‖ ≤ y⁻¹`. -/
theorem lct_norm_shifted_inv_le {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hH : H.IsHermitian) (σ : n → ℂ) {y : ℝ} (hy : 0 < y) (hσ : ∀ p, y ≤ -(σ p).im) :
    ‖(H - diagonal σ)⁻¹‖ ≤ y⁻¹ := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hy.le) fun v => ?_
  change ‖toEuclideanLin (H - diagonal σ)⁻¹ v‖ ≤ y⁻¹ * ‖v‖
  have h := cmp_mulVec_le H hH σ hy hσ (WithLp.ofLp v)
  have e1 : ‖toEuclideanLin (H - diagonal σ)⁻¹ v‖ ^ 2 =
      cmpSq ((H - diagonal σ)⁻¹ *ᵥ WithLp.ofLp v) := by
    rw [EuclideanSpace.norm_sq_eq, cmpSq]
    rfl
  have e2 : ‖v‖ ^ 2 = cmpSq (WithLp.ofLp v) := by
    rw [EuclideanSpace.norm_sq_eq, cmpSq]
  rw [← e1, ← e2] at h
  have h0 := norm_nonneg (toEuclideanLin (H - diagonal σ)⁻¹ v)
  have hv := norm_nonneg v
  rw [le_inv_mul_iff₀ hy]
  nlinarith [sq_nonneg (y * ‖toEuclideanLin (H - diagonal σ)⁻¹ v‖ - ‖v‖),
    sq_nonneg (y * ‖toEuclideanLin (H - diagonal σ)⁻¹ v‖ + ‖v‖)]

end Norms

/-!
## 4. One-letter covariances and the residuals
-/

section Residuals

variable {W : ℕ} {σ : LayerShape}

/-- `g_a(M) = W⁻¹ Tr (P_a M)`. -/
theorem lct_phys_eq_trace (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (a : Fin σ.blocks) :
    physBlockTrace M a = (W : ℂ)⁻¹ * (meqPhysProj a * M).trace := by
  rw [meq_physBlockTrace_eq_word, ← meq_mul_eq_wordEval]

/-- `g_{port j}(M) = W⁻¹ Tr (Q_j M)`. -/
theorem lct_port_eq_trace (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (j : Fin σ.ports) :
    portBlockTrace M j = (W : ℂ)⁻¹ * (meqPortProj j * M).trace := by
  rw [meq_portBlockTrace_eq_word, ← meq_mul_eq_wordEval]

theorem lct_norm_vec_two_le {P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hP : ‖P‖ ≤ 1) :
    ∀ j : Fin 2, ‖(![P, 1] : Fin 2 → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) j‖ ≤ 1 := by
  intro j
  fin_cases j
  · exact hP
  · exact lct_norm_one_le

/-- **One-letter covariance bound** (`TraceMatrixContract.covariance` with `L = 1`, `K = 1`, via
`traceCovariance_holds`): `‖Cov(W⁻¹ Tr P𝒢, Q𝒢)‖ ≤ C W⁻²` for `‖P‖, ‖Q‖ ≤ 1`, `W ≥ W₀`. -/
theorem lct_cov_one_letter (habs : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {η₀ M : ℝ} (hη : 0 < η₀) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
      ∀ P Q : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 →
        ‖meqCov (layerLaw W b σ)
            (fun ω => (W : ℂ)⁻¹ * (P * layerResolvent σ E z X ω).trace)
            (fun ω => Q * layerResolvent σ E z X ω)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₀, h⟩ := traceCovariance_holds habs b hb0 hb1 η₀ M hη 1 1
  refine ⟨max C 0, W₀, le_max_right _ _, ?_⟩
  intro W hW hWW σ X hX E z hz hzM P Q hP hQ
  have h1 := (h W hW hWW σ X hX E z hz hzM 1 1 le_rfl le_rfl (fun _ => false) ![P, 1]
    (fun _ => false) ![Q, 1] (lct_norm_vec_two_le hP) (lct_norm_vec_two_le hQ)).2.2.2
  simp only [← meq_mul_eq_wordEval] at h1
  exact h1.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))

/-- The covariances of the physical residual, as normalized traces of one-letter words. -/
theorem lct_cov_phys_eq {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (a : Fin σ.blocks)
    (U : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    meqCov ν (fun ω => physBlockTrace (G ω) a) U =
      meqCov ν (fun ω => (W : ℂ)⁻¹ * (meqPhysProj a * G ω).trace) U := by
  simp only [lct_phys_eq_trace]

theorem lct_cov_port_eq {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (j : Fin σ.ports)
    (U : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    meqCov ν (fun ω => portBlockTrace (G ω) j) U =
      meqCov ν (fun ω => (W : ℂ)⁻¹ * (meqPortProj j * G ω).trace) U := by
  simp only [lct_port_eq_trace]

theorem lct_norm_meqInc_le (a : Fin σ.blocks) (j : Fin σ.ports) : ‖meqInc σ a j‖ ≤ 1 := by
  unfold meqInc; split_ifs <;> simp

/-- **Physical residual bound**: if every covariance entering `R_phys` has norm `≤ B`, then
`‖R_phys‖ ≤ (#blocks + #blocks·#ports) B` (`0 ≤ b ≤ 1/2`, `c = 1 - 2b`). -/
theorem lct_norm_residTop_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {B : ℝ}
    (h1 : ∀ a, ‖meqCov ν (fun ω => physBlockTrace (G ω) a) (fun ω => meqPhysProj a * G ω)‖ ≤ B)
    (h2 : ∀ a j,
      ‖meqCov ν (fun ω => portBlockTrace (G ω) j) (fun ω => meqPhysProj a * G ω)‖ ≤ B) :
    ‖meqResidTop ν (1 - 2 * (b : ℂ)) b G‖ ≤ (σ.blocks + σ.blocks * σ.ports : ℕ) * B := by
  have hc : ‖(1 - 2 * (b : ℂ))‖ ≤ 1 := by
    rw [show (1 - 2 * (b : ℂ)) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    linarith
  have hbn : ∀ a j, ‖(b : ℂ) * meqInc σ a j‖ ≤ 1 := fun a j => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]
    have := lct_norm_meqInc_le a j
    have := norm_nonneg (meqInc σ a j)
    nlinarith
  refine (lct_norm_toBlocks11_le _).trans ?_
  refine (norm_add_le _ _).trans ?_
  have hA : ‖∑ a, (1 - 2 * (b : ℂ)) • meqCov ν (fun ω => physBlockTrace (G ω) a)
      (fun ω => meqPhysProj a * G ω)‖ ≤ σ.blocks * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖(1 - 2 * (b : ℂ)) • meqCov ν (fun ω => physBlockTrace (G ω) a)
          (fun ω => meqPhysProj a * G ω)‖ ≤ ∑ _a : Fin σ.blocks, B := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_smul]
          have := norm_nonneg (meqCov ν (fun ω => physBlockTrace (G ω) a)
            (fun ω => meqPhysProj a * G ω))
          nlinarith [h1 a, norm_nonneg (1 - 2 * (b : ℂ))]
      _ = σ.blocks * B := by simp
  have hP : ‖∑ a, ∑ j, ((b : ℂ) * meqInc σ a j) • meqCov ν (fun ω => portBlockTrace (G ω) j)
      (fun ω => meqPhysProj a * G ω)‖ ≤ (σ.blocks * σ.ports : ℕ) * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖∑ j, ((b : ℂ) * meqInc σ a j) • meqCov ν (fun ω => portBlockTrace (G ω) j)
          (fun ω => meqPhysProj a * G ω)‖ ≤ ∑ _a : Fin σ.blocks, ∑ _j : Fin σ.ports, B := by
          refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_smul]
          have := norm_nonneg (meqCov ν (fun ω => portBlockTrace (G ω) j)
            (fun ω => meqPhysProj a * G ω))
          nlinarith [h2 a j, hbn a j, norm_nonneg ((b : ℂ) * meqInc σ a j)]
      _ = (σ.blocks * σ.ports : ℕ) * B := by simp; ring
  push_cast at hP ⊢
  linarith

end Residuals

end BlockBand.Layers

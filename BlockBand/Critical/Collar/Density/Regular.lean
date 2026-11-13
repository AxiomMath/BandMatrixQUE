module

public import BlockBand.Critical.Collar.Density.RegularBound
public import BlockBand.Critical.Collar.Density.EnergyStability

/-!
# The regular clause of the collar density bound

This file reduces the regular clause of the collar density bound to the conditional Schur
identity: conditional on `(A, B)`, the top-top spectral density of the collar `ℋ_X`, averaged over
the middle block `G`, is `T_x Σ_{F_x}(0) T_x*`.

* `CollarConditionalDensityBound`, `CollarConditionalDensityIdentity`: the upper-bound and equality
  forms of the conditional Schur identity, for `0 < b < 1/2`, `W ≥ 1`, real `e`, Hermitian `X`,
  `a₁ ≤ a₂` and `u`:
  `u*E_collar[1_{[a₁,a₂]}(ℋ_X)]₁₁u ≤ ∫_{[a₁,a₂]} E_{A,B}[u* T_x Σ_{F_x}(0) T_x* u] dx`, with
  `T_x, F_x` at energy `e + x` (`ℋ_X - x` is the energy-`(e+x)` collar; the middle block is shifted
  too).
* `weight_change`: comparison of the weights `K_X` at two nearby spectral parameters.
* `collarDensityRegular_of_conditional`: the regular clause `CollarDensityRegularClause`, from
  `CollarConditionalDensityBound` together with `FreshPalmContract`, `PointDensityContract`,
  `CommonPortMeanContract`, `TraceMatrixContract` and `PSSS.SourceContract`. Its ingredients are
  the Schur algebra `𝒢₂₂ = (F - ca)⁻¹`, `L = K T H`, the bounded-shift lemma
  `(F + i)Σ(F - i) ⪯ C ⇒ K T Σ T* K* ⪯ 2C LL*`, the regular event (certificate, deformed Wegner
  cutoff, trace concentration, bond cutoff) and the bound
  `E_{A,B} q*K_X T Σ_F(0) T* K_X* q ≤ C‖q‖²` for `W ≥ W₀`, `d(X) ≤ d_R`, `e ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexOrder

variable {W : ℕ}

/-- **The conditional Schur identity, upper-bound form.** Conditional on `(A, B)`, the expected
top-top spectral measure of `ℋ_X` on `[a₁, a₂]`, averaged over the middle block `G`, is at most the
integral over `x ∈ [a₁, a₂]` of `T_x Σ_{F_x}(0) T_x*` (`condCollarDensity b (e + x) X`). Stated for
`collarLaw W b` and its first factor `layerLaw W b .common`, every `W ≥ 1`, `0 < b < 1/2`, real `e`,
Hermitian `X` (no norm bound), every `[a₁, a₂]` and vector `u`. -/
def CollarConditionalDensityBound : Prop :=
  ∀ (W : ℕ), 0 < W → ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ (e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), X.IsHermitian →
    ∀ (a₁ a₂ : ℝ), a₁ ≤ a₂ → ∀ u : Fin 2 × Fin W → ℂ,
      ENNReal.ofReal (quadForm (collarTopProjector W b e X (Set.Icc a₁ a₂)) u) ≤
        ∫⁻ x in Set.Icc a₁ a₂, ∫⁻ ω, ENNReal.ofReal (quadForm (condCollarDensity b (e + x) X ω) u)
          ∂layerLaw W b .common

/-- **The conditional Schur identity, equality form.** The same statement with `=`. It implies
`CollarConditionalDensityBound` (`CollarConditionalDensityIdentity.bound`). -/
def CollarConditionalDensityIdentity : Prop :=
  ∀ (W : ℕ), 0 < W → ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ (e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), X.IsHermitian →
    ∀ (a₁ a₂ : ℝ), a₁ ≤ a₂ → ∀ u : Fin 2 × Fin W → ℂ,
      ENNReal.ofReal (quadForm (collarTopProjector W b e X (Set.Icc a₁ a₂)) u) =
        ∫⁻ x in Set.Icc a₁ a₂, ∫⁻ ω, ENNReal.ofReal (quadForm (condCollarDensity b (e + x) X ω) u)
          ∂layerLaw W b .common

theorem CollarConditionalDensityIdentity.bound (h : CollarConditionalDensityIdentity) :
    CollarConditionalDensityBound :=
  fun W hW b hb0 hb e X hX a₁ a₂ ha u => (h W hW b hb0 hb e X hX a₁ a₂ ha u).le

/-!
## Continuity and interval averages
-/

theorem le_of_forall_setIntegral_Icc_le {φ : ℝ → ℝ} (hφ : Continuous φ) {M h₀ : ℝ}
    (hh₀ : 0 < h₀) (hI : ∀ h, 0 < h → h ≤ h₀ → ∫ x in Set.Icc (-h) h, φ x ≤ 2 * h * M) :
    φ 0 ≤ M := by
  by_contra hlt
  rw [not_le] at hlt
  set ε := (φ 0 - M) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hφ 0 ε hεpos
  set r := min h₀ (δ / 2)
  have hpos : 0 < r := lt_min hh₀ (by linarith)
  have hlow : ∀ x ∈ Set.Icc (-r) r, M + ε ≤ φ x := by
    intro x hx
    have hxd : dist x 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      have := min_le_right h₀ (δ / 2)
      constructor <;> linarith [hx.1, hx.2]
    have := hball x hxd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hint : 2 * r * (M + ε) ≤ ∫ x in Set.Icc (-r) r, φ x := by
    have hmono := setIntegral_mono_on (continuous_const.integrableOn_Icc (μ := volume))
      (hφ.integrableOn_Icc) measurableSet_Icc hlow
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith)] at hmono
    simp only [smul_eq_mul] at hmono
    linarith
  have := hI r hpos (min_le_left _ _)
  nlinarith

theorem quadForm_collarTopProjector_eq (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (a₁ a₂ : ℝ)
    (u : Fin 2 × Fin W → ℂ) :
    quadForm (collarTopProjector W b e X (Set.Icc a₁ a₂)) u =
      ∫ x in Set.Icc a₁ a₂, quadForm (collarDensity W b e X x) u := by
  have hint : ∀ i j, Integrable (fun x => collarDensity W b e X x i j)
      (volume.restrict (Set.Icc a₁ a₂)) := fun i j =>
    (continuous_collarDensity_apply hW b e hX i j).integrableOn_Icc
  rw [integral_quadForm hint u]
  congr 1
  ext i j
  simp only [matrixExpect, Matrix.of_apply]
  exact (setIntegral_collarDensity_apply hW hb e hX a₁ a₂ i j).symm

/-!
## The weight comparison at a nearby energy
-/

/-- `p = (K'*)⁻¹ K* q` with `K = K' + δ`: `K'* p = K* q` and `‖p‖² ≤ 2(1 + |δ|²/(Im z')²)‖q‖²`. -/
theorem weight_change {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {z z' : ℂ} (hz' : 0 < z'.im) (q : Fin 2 × Fin W → ℂ) :
    (z' • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ *ᵥ
        ((z' • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ⁻¹ *ᵥ
          ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ *ᵥ q)) =
      (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ *ᵥ q ∧
    ∑ a, ‖((z' • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ⁻¹ *ᵥ
          ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ *ᵥ q)) a‖ ^ 2 ≤
      2 * (1 + ‖z - z'‖ ^ 2 * (z'.im ^ 2)⁻¹) * ∑ a, ‖q a‖ ^ 2 := by
  set K' := z' • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
  have hu : IsUnit K'ᴴ.det := by
    rw [det_conjTranspose]; exact (isUnit_det_smul_one_sub hX hz').star
  constructor
  · rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  · have hK : (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ =
        K'ᴴ + (star (z - z')) • 1 := by
      simp only [K', conjTranspose_sub, conjTranspose_smul, conjTranspose_one, star_sub]
      rw [sub_smul]; abel
    have hp : K'ᴴ⁻¹ *ᵥ ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ *ᵥ q) =
        q + star (z - z') • (K'ᴴ⁻¹ *ᵥ q) := by
      rw [hK, add_mulVec, smul_mulVec, one_mulVec, mulVec_add, mulVec_mulVec,
        nonsing_inv_mul _ hu, one_mulVec, mulVec_smul]
    rw [hp]
    have h1 := norm_sq_inv_conjTranspose_mulVec_le hX hz' q
    have hpt : ∀ a, ‖(q + star (z - z') • (K'ᴴ⁻¹ *ᵥ q)) a‖ ^ 2 ≤
        2 * ‖q a‖ ^ 2 + 2 * ‖z - z'‖ ^ 2 * ‖(K'ᴴ⁻¹ *ᵥ q) a‖ ^ 2 := by
      intro a
      have := norm_sub_sq_le (q a) (-(star (z - z') * (K'ᴴ⁻¹ *ᵥ q) a))
      simp only [sub_neg_eq_add, norm_neg, norm_mul, norm_star, mul_pow] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    calc _ ≤ ∑ a, (2 * ‖q a‖ ^ 2 + 2 * ‖z - z'‖ ^ 2 * ‖(K'ᴴ⁻¹ *ᵥ q) a‖ ^ 2) :=
          Finset.sum_le_sum fun a _ => hpt a
      _ = 2 * ∑ a, ‖q a‖ ^ 2 + 2 * ‖z - z'‖ ^ 2 * ∑ a, ‖(K'ᴴ⁻¹ *ᵥ q) a‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * ∑ a, ‖q a‖ ^ 2 + 2 * ‖z - z'‖ ^ 2 * ((z'.im ^ 2)⁻¹ * ∑ a, ‖q a‖ ^ 2) := by
          gcongr
      _ = _ := by ring

/-!
## The regular clause
-/

theorem bulkInterval_add_mem {κ e x : ℝ} (he : e ∈ bulkInterval κ) (hx : |x| ≤ κ / 2) :
    e + x ∈ bulkInterval (κ / 2) := by
  have h1 := he.1; have h2 := he.2
  rw [abs_le] at hx
  constructor <;> linarith [hx.1, hx.2]

theorem bulkInterval_mono {κ κ' e : ℝ} (h : κ' ≤ κ) (he : e ∈ bulkInterval κ) :
    e ∈ bulkInterval κ' :=
  ⟨by linarith [he.1], by linarith [he.2]⟩

/-- **The regular clause of the collar density bound** (`CollarDensityRegularClause`), in the
hypothesis shape of `collarDensityStatement_of_regular` and
`Kernel.collarKernel_holds_of_densityRegular`, **from the conditional Schur identity**
`CollarConditionalDensityBound` (proved as `collarConditionalDensityBound_holds`), `FreshPalmContract`,
`PointDensityContract`, `CommonPortMeanContract`, `TraceMatrixContract` and `PSSS.SourceContract`.
-/
theorem collarDensityRegular_of_conditional (hS : CollarConditionalDensityBound)
    (hP : FreshPalmContract) (hPD : PointDensityContract) (hCM : CommonPortMeanContract)
    (hTM : TraceMatrixContract) (source : BlockBand.External.PSSS.SourceContract.{0}) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ CollarDensityRegularClause b κ dstar C W₀ := by
  intro b hb0 hb κ hκ
  set κ₁ : ℝ := min κ 1
  have hκ₁ : 0 < κ₁ := lt_min hκ one_pos
  have hκ₁1 : κ₁ ≤ 1 := min_le_right _ _
  set κ' : ℝ := κ₁ / 2 with hκ'def
  have hκ' : 0 < κ' := by positivity
  have hκ'2 : κ' < 2 := by rw [hκ'def]; linarith
  have hκ'1 : κ' ≤ κ₁ := by rw [hκ'def]; linarith
  obtain ⟨dR, CR, W₀, hdR, hCR, hR⟩ :=
    lintegral_condCollarDensity_le hP hPD hCM hTM source hb0 hb hκ' hκ'2
  have hm4 : 0 < 4 - (2 - κ') ^ 2 := BlockBand.Layers.four_sub_sq_pos hκ' (by linarith)
  have hsq : 0 < Real.sqrt (4 - (2 - κ') ^ 2) := Real.sqrt_pos.2 hm4
  set La : ℝ := 1 / 2 + 1 / Real.sqrt (4 - (2 - κ') ^ 2)
  have hLa : 0 < La := by positivity
  set Lz : ℝ := 1 + (1 - b) * La
  have hLz : 0 < Lz := by have : 0 < 1 - b := by linarith
                          positivity
  set η : ℝ := (1 - b) * Real.sqrt (4 - (2 - κ') ^ 2) / 2
  have hη : 0 < η := by have : 0 < 1 - b := by linarith
                        positivity
  set h₀ : ℝ := min (κ₁ / 2) (min (1 / Lz) (dR / (2 * (Lz / η ^ 2 + La))))
  have hh₀ : 0 < h₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set M : ℝ := CR * (2 * (1 + (η ^ 2)⁻¹))
  have hM : 0 ≤ M := by positivity
  refine ⟨dR / 2, M, W₀, by positivity, ?_⟩
  intro W hW hW₀ e he X hX hd
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have he₁ : e ∈ bulkInterval κ₁ := bulkInterval_mono (min_le_left _ _) he
  have he' : e ∈ bulkInterval κ' := bulkInterval_mono hκ'1 he₁
  have hmem : ∀ x, |x| ≤ h₀ → e + x ∈ bulkInterval κ' := fun x hx =>
    bulkInterval_add_mem he₁ (hx.trans (min_le_left _ _))
  have hηE : ∀ E ∈ bulkInterval κ', η ≤ (boundaryZ b E).im := fun E hE =>
    (BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (by linarith) hκ' hE).2
  have hz : ∀ x, |x| ≤ h₀ → ‖boundaryZ b e - boundaryZ b (e + x)‖ ≤ Lz * |x| := by
    intro x hx
    have := norm_boundaryZ_sub_le (b := b) (by linarith) hκ' he' (hmem x hx)
    rwa [show e - (e + x) = -x by ring, abs_neg] at this
  have hdx : ∀ x, |x| ≤ h₀ → matchedDistance b (e + x) X ≤ dR := by
    intro x hx
    have h1 := matchedDistance_le_energy (b := b) hW hX (hη.trans_le (hηE e he'))
      (hη.trans_le (hηE _ (hmem x hx)))
    have h2 : ‖matchedA (e + x) - matchedA e‖ ≤ La * |x| := by
      have := norm_matchedA_sub_le hκ' (hmem x hx) he'
      rw [show e + x - e = x by ring] at this
      exact this
    have h3 : ((boundaryZ b (e + x)).im * (boundaryZ b e).im)⁻¹ ≤ (η ^ 2)⁻¹ := by
      rw [sq]
      exact inv_anti₀ (by positivity) (mul_le_mul (hηE _ (hmem x hx)) (hηE e he') hη.le
        (hη.le.trans (hηE _ (hmem x hx))))
    have hx0 := abs_nonneg x
    have hxh : |x| ≤ dR / (2 * (Lz / η ^ 2 + La)) :=
      hx.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h4 : (Lz / η ^ 2 + La) * |x| ≤ dR / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Lz / η ^ 2 + La))] at hxh
      nlinarith
    have h5 : ‖boundaryZ b e - boundaryZ b (e + x)‖ *
        ((boundaryZ b (e + x)).im * (boundaryZ b e).im)⁻¹ ≤ Lz * |x| * (η ^ 2)⁻¹ :=
      mul_le_mul (hz x hx) h3 (inv_nonneg.2 (mul_pos (hη.trans_le (hηE _ (hmem x hx)))
        (hη.trans_le (hηE e he'))).le) (mul_nonneg hLz.le hx0)
    have h6 : Lz * |x| * (η ^ 2)⁻¹ + La * |x| = (Lz / η ^ 2 + La) * |x| := by
      field_simp
    linarith
  have hδ1 : ∀ x, |x| ≤ h₀ → ‖boundaryZ b e - boundaryZ b (e + x)‖ ≤ 1 := by
    intro x hx
    have hx' : |x| ≤ 1 / Lz := hx.trans ((min_le_right _ _).trans (min_le_left _ _))
    calc _ ≤ Lz * |x| := hz x hx
      _ ≤ Lz * (1 / Lz) := mul_le_mul_of_nonneg_left hx' hLz.le
      _ = 1 := by field_simp
  -- the Loewner form
  have hΨH := collarDensity_isHermitian hW b e hX 0
  refine posSemidef_of_quadForm_nonneg
    (((isHermitian_one).smul (Complex.conj_ofReal M)).sub
      (isHermitian_mul_mul_conjTranspose _ hΨH)) fun q => ?_
  rw [quadForm_sub, quadForm_real_smul, quadForm_one]
  set K := matchedLeadK b e X
  set u := Kᴴ *ᵥ q
  have hKq : quadForm (K * collarDensity W b e X 0 * Kᴴ) q =
      quadForm (collarDensity W b e X 0) u := by
    have := quadForm_conjTranspose_mul_mul Kᴴ (collarDensity W b e X 0) q
    rwa [conjTranspose_conjTranspose] at this
  rw [hKq]
  -- the conditional bound at every nearby energy
  have hcond : ∀ x, |x| ≤ h₀ → ∫⁻ ω, ENNReal.ofReal (quadForm (condCollarDensity b (e + x) X ω) u)
      ∂layerLaw W b .common ≤ ENNReal.ofReal (M * ∑ a, ‖q a‖ ^ 2) := by
    intro x hx
    obtain ⟨hp1, hp2⟩ := weight_change hX (z := boundaryZ b e) (hη.trans_le (hηE _ (hmem x hx))) q
    set K' := matchedLeadK b (e + x) X
    set p := K'ᴴ⁻¹ *ᵥ u
    have heq : ∀ ω, quadForm (condCollarDensity b (e + x) X ω) u =
        quadForm (K' * condCollarDensity b (e + x) X ω * K'ᴴ) p := by
      intro ω
      have := quadForm_conjTranspose_mul_mul K'ᴴ (condCollarDensity b (e + x) X ω) p
      rw [conjTranspose_conjTranspose] at this
      rw [this]
      congr 1
      exact hp1.symm
    simp_rw [heq]
    refine (hR W hW hW₀ (e + x) (hmem x hx) X hX (hdx x hx) p).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hδ := hδ1 x hx
    have hηx := hηE _ (hmem x hx)
    have hinv : ((boundaryZ b (e + x)).im ^ 2)⁻¹ ≤ (η ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hη.le hηx 2)
    have hq0 : 0 ≤ ∑ a, ‖q a‖ ^ 2 := by positivity
    have hp3 : ∑ a, ‖p a‖ ^ 2 ≤ 2 * (1 + (η ^ 2)⁻¹) * ∑ a, ‖q a‖ ^ 2 := by
      refine hp2.trans (mul_le_mul_of_nonneg_right ?_ hq0)
      have : ‖boundaryZ b e - boundaryZ b (e + x)‖ ^ 2 * ((boundaryZ b (e + x)).im ^ 2)⁻¹ ≤
          1 * (η ^ 2)⁻¹ :=
        mul_le_mul (pow_le_one₀ (norm_nonneg _) hδ) hinv (by positivity) zero_le_one
      linarith
    calc CR * ∑ a, ‖p a‖ ^ 2 ≤ CR * (2 * (1 + (η ^ 2)⁻¹) * ∑ a, ‖q a‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hp3 hCR
      _ = M * ∑ a, ‖q a‖ ^ 2 := by simp only [M]; ring
  -- continuity of the density and the interval averages
  have hφ : Continuous fun x => quadForm (collarDensity W b e X x) u := by
    unfold quadForm
    exact Complex.continuous_re.comp (continuous_const.dotProduct
      ((continuous_collarDensity hW b e hX).matrix_mulVec continuous_const))
  have hle := le_of_forall_setIntegral_Icc_le hφ hh₀ (M := M * ∑ a, ‖q a‖ ^ 2) (by
    intro r hr hrh
    rw [← quadForm_collarTopProjector_eq hW hb e hX (-r) r u]
    have hS' := hS W hW b hb0 hb e X hX (-r) r (by linarith) u
    have hbd : ∫⁻ x in Set.Icc (-r) r, ∫⁻ ω, ENNReal.ofReal
          (quadForm (condCollarDensity b (e + x) X ω) u) ∂layerLaw W b .common ≤
        ∫⁻ x in Set.Icc (-r) r, ENNReal.ofReal (M * ∑ a, ‖q a‖ ^ 2) :=
      setLIntegral_mono' measurableSet_Icc fun x hx => hcond x (by
        rw [abs_le]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have hq0 : 0 ≤ ∑ a, ‖q a‖ ^ 2 := by positivity
    rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (mul_nonneg hM hq0)] at hbd
    have hfin := hS'.trans hbd
    have hnn : 0 ≤ (M * ∑ a, ‖q a‖ ^ 2) * (r - -r) := mul_nonneg (mul_nonneg hM hq0) (by linarith)
    rw [ENNReal.ofReal_le_ofReal_iff hnn] at hfin
    linarith)
  linarith

end BlockBand.Critical.Collar.Density

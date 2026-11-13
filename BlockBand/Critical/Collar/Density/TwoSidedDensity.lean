module

public import BlockBand.Critical.Collar.Density.TwoSidedBound
public import BlockBand.Critical.Collar.Density.CondSchurIdentity

/-!
# The two-sided bound for the canonical collar density at zero

*Law.* `collarLaw W b`, `0 < b < 1/2`; deterministic Hermitian `X` (no norm bound);
`e ∈ bulkInterval κ`, `0 < κ ≤ 1`.

**Main result** `collarDensity_two_sided`: there are `d_P > 0`, `C_P ≥ 0`, `ε_P W → 0`, `W₀` with:
for `W ≥ W₀`, `e ∈ bulkInterval κ`, Hermitian `X` with `d(X) ≤ d_P`, every `z` with
`‖z - z_b‖ ≤ 1` and every `q`,
`|q*(z - X)Ψ_X(0)(z - X)*q - (η/π)‖q‖²| ≤ C_P(d(X) + ε_P W + ‖z - z_b‖)‖q‖²`
(`Ψ_X = collarDensity W b e X`, `η = Im z_b`).

Proof. The conditional Schur identity `collarConditionalDensityIdentity_holds` writes
`∫_{[-r,r]} u*Ψ_X(x)u dx` as `∫_{[-r,r]} E_{A,B} u*T_xΣ_{F_x}(0)T_x*u dx` (energy `e + x`; the
middle block is shifted too). At each `e + x` the weight `z - X` is changed to `K^{(e+x)}_X`
(`weight_change`, `weight_change_two_sided`) and the two-sided conditional mean
`lintegral_condCollarDensity_two_sided` is applied (`d_{e+x}(X) ≤ d(X) + L|x|`,
`matchedDistance_le_energy`). The interval averages with linear slack
(`le_of_forall_setIntegral_Icc_le'`, `ge_of_forall_setIntegral_Icc_ge'`) and the continuity of
`Ψ_X` give the value at `0`.
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

/-!
## Interval averages with a linear slack
-/

theorem le_of_forall_setIntegral_Icc_le' {φ : ℝ → ℝ} (hφ : Continuous φ) {M B h₀ : ℝ}
    (hh₀ : 0 < h₀) (hB : 0 ≤ B)
    (hI : ∀ h, 0 < h → h ≤ h₀ → ∫ x in Set.Icc (-h) h, φ x ≤ 2 * h * (M + B * h)) :
    φ 0 ≤ M := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine le_of_forall_setIntegral_Icc_le hφ (h₀ := min h₀ (ε / (B + 1)))
    (lt_min hh₀ (by positivity)) fun h hh hhle => ?_
  have h1 := hI h hh (hhle.trans (min_le_left _ _))
  have h2 : B * h ≤ ε := by
    have h3 : h ≤ ε / (B + 1) := hhle.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h3
    nlinarith
  calc _ ≤ 2 * h * (M + B * h) := h1
    _ ≤ 2 * h * (M + ε) := by gcongr

theorem ge_of_forall_setIntegral_Icc_ge' {φ : ℝ → ℝ} (hφ : Continuous φ) {M B h₀ : ℝ}
    (hh₀ : 0 < h₀) (hB : 0 ≤ B)
    (hI : ∀ h, 0 < h → h ≤ h₀ → 2 * h * (M - B * h) ≤ ∫ x in Set.Icc (-h) h, φ x) :
    M ≤ φ 0 := by
  have := le_of_forall_setIntegral_Icc_le' (φ := fun x => -φ x) hφ.neg (M := -M) hh₀ hB
    fun h hh hhle => by
      rw [integral_neg]
      have := hI h hh hhle
      linarith
  linarith

/-!
## The weight change
-/

theorem abs_sum_norm_sq_add_sub_le {ι : Type} [Fintype ι] (q v : ι → ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hv : ∑ a, ‖v a‖ ^ 2 ≤ t ^ 2 * ∑ a, ‖q a‖ ^ 2) :
    |∑ a, ‖(q + v) a‖ ^ 2 - ∑ a, ‖q a‖ ^ 2| ≤ (2 * t + t ^ 2) * ∑ a, ‖q a‖ ^ 2 := by
  set nq := ∑ a, ‖q a‖ ^ 2
  set nv := ∑ a, ‖v a‖ ^ 2
  have hpt : ∀ a, |‖(q + v) a‖ ^ 2 - ‖q a‖ ^ 2| ≤ 2 * (‖q a‖ * ‖v a‖) + ‖v a‖ ^ 2 := by
    intro a
    simp only [Pi.add_apply]
    have h1 := norm_add_le (q a) (v a)
    have h2 : ‖q a‖ ≤ ‖q a + v a‖ + ‖v a‖ := by
      have := norm_sub_le (q a + v a) (v a)
      simpa using this
    rw [abs_le]
    constructor <;> nlinarith [norm_nonneg (q a), norm_nonneg (v a), norm_nonneg (q a + v a)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖q a‖) (fun a => ‖v a‖)
  have hS : ∑ a, ‖q a‖ * ‖v a‖ ≤ t * nq := by
    have h0 : 0 ≤ ∑ a, ‖q a‖ * ‖v a‖ := by positivity
    have hnq : 0 ≤ nq := by positivity
    have : (∑ a, ‖q a‖ * ‖v a‖) ^ 2 ≤ (t * nq) ^ 2 := by
      calc _ ≤ nq * nv := hcs
        _ ≤ nq * (t ^ 2 * nq) := mul_le_mul_of_nonneg_left hv hnq
        _ = (t * nq) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 this
  calc |∑ a, ‖(q + v) a‖ ^ 2 - nq| = |∑ a, (‖(q + v) a‖ ^ 2 - ‖q a‖ ^ 2)| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ a, |‖(q + v) a‖ ^ 2 - ‖q a‖ ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, (2 * (‖q a‖ * ‖v a‖) + ‖v a‖ ^ 2) := Finset.sum_le_sum fun a _ => hpt a
    _ = 2 * ∑ a, ‖q a‖ * ‖v a‖ + nv := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (t * nq) + t ^ 2 * nq := by linarith
    _ = (2 * t + t ^ 2) * nq := by ring

/-- The weight vector `p = (K'*)⁻¹ K* q`, `K = z - X`, `K' = z' - X`: `K'* p = K* q`,
`‖p‖² ≤ 2(1 + |δ|²/(Im z')²)‖q‖²` and `|‖p‖² - ‖q‖²| ≤ (2t + t²)‖q‖²`, `t = |δ|/Im z'`,
`δ = z - z'`. -/
theorem weight_change_two_sided {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {z z' : ℂ} (hz' : 0 < z'.im) (q : Fin 2 × Fin W → ℂ) :
    |∑ a, ‖((z' • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ⁻¹ *ᵥ
          ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ *ᵥ q)) a‖ ^ 2 -
        ∑ a, ‖q a‖ ^ 2| ≤
      (2 * (‖z - z'‖ / z'.im) + (‖z - z'‖ / z'.im) ^ 2) * ∑ a, ‖q a‖ ^ 2 := by
  set K' := z' • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
  have hu : IsUnit K'ᴴ.det := by
    rw [det_conjTranspose]; exact (isUnit_det_smul_one_sub hX hz').star
  have hK : (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ =
      K'ᴴ + (star (z - z')) • 1 := by
    simp only [K', conjTranspose_sub, conjTranspose_smul, conjTranspose_one, star_sub]
    rw [sub_smul]; abel
  have hp : K'ᴴ⁻¹ *ᵥ ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ *ᵥ q) =
      q + star (z - z') • (K'ᴴ⁻¹ *ᵥ q) := by
    rw [hK, add_mulVec, smul_mulVec, one_mulVec, mulVec_add, mulVec_mulVec,
      nonsing_inv_mul _ hu, one_mulVec, mulVec_smul]
  rw [hp]
  refine abs_sum_norm_sq_add_sub_le q _ (by positivity) ?_
  have h1 := norm_sq_inv_conjTranspose_mulVec_le hX hz' q
  have h2 : ∑ a, ‖(star (z - z') • (K'ᴴ⁻¹ *ᵥ q)) a‖ ^ 2 =
      ‖z - z'‖ ^ 2 * ∑ a, ‖(K'ᴴ⁻¹ *ᵥ q) a‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_star, mul_pow]
  rw [h2]
  calc ‖z - z'‖ ^ 2 * ∑ a, ‖(K'ᴴ⁻¹ *ᵥ q) a‖ ^ 2 ≤
      ‖z - z'‖ ^ 2 * ((z'.im ^ 2)⁻¹ * ∑ a, ‖q a‖ ^ 2) := by gcongr
    _ = (‖z - z'‖ / z'.im) ^ 2 * ∑ a, ‖q a‖ ^ 2 := by rw [div_pow]; ring

theorem boundaryZ_im_le_one' {b e : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (he : |e| ≤ 2) :
    (boundaryZ b e).im ≤ 1 := by
  rw [BlockBand.Layers.boundaryZ_im he]
  have h1 := Complex.abs_im_le_norm (matchedA e)
  rw [BlockBand.Layers.norm_matchedA he] at h1
  have h2 := neg_abs_le (matchedA e).im
  nlinarith

/-- The arithmetic of the weight and energy change at a nearby energy. -/
theorem density_budget {np nq η' ηe d' d εS CS Mp Ld y Lz Cη δz : ℝ} (hnq : 0 ≤ nq)
    (hnp0 : 0 ≤ np) (hnp : np ≤ Mp * nq) (hnpq : |np - nq| ≤ Cη / 2 * (δz + Lz * y) * nq)
    (hηη : |η' - ηe| ≤ Lz * y) (hηe0 : 0 ≤ ηe) (hηe1 : ηe ≤ 1)
    (hd' : d' ≤ d + Ld * y) (hd0 : 0 ≤ d) (hLd : 0 ≤ Ld) (hεS : 0 ≤ εS) (hCS : 0 ≤ CS)
    (hy : 0 ≤ y)
    (hCη : 0 ≤ Cη) (hLz : 0 ≤ Lz) (hδz : 0 ≤ δz) :
    η' / Real.pi * np + CS * (d' + εS) * np ≤ ηe / Real.pi * nq +
        (CS * Mp * (d + εS) + Cη / Real.pi * δz +
          (CS * Mp * Ld + Lz * Mp / Real.pi + Cη * Lz / Real.pi) * y) * nq ∧
      ηe / Real.pi * nq - (CS * Mp * (d + εS) + Cη / Real.pi * δz +
          (CS * Mp * Ld + Lz * Mp / Real.pi + Cη * Lz / Real.pi) * y) * nq ≤
        η' / Real.pi * np - CS * (d' + εS) * np := by
  have hpi := Real.pi_pos
  have e1 : η' / Real.pi * np - ηe / Real.pi * nq =
      (η' - ηe) / Real.pi * np + ηe / Real.pi * (np - nq) := by ring
  have h1 : |(η' - ηe) / Real.pi * np| ≤ Lz * y / Real.pi * (Mp * nq) := by
    rw [abs_mul, abs_div, abs_of_pos hpi, abs_of_nonneg hnp0]
    exact mul_le_mul (div_le_div_of_nonneg_right hηη hpi.le) hnp hnp0 (by positivity)
  have h2 : |ηe / Real.pi * (np - nq)| ≤ 1 / Real.pi * (Cη / 2 * (δz + Lz * y) * nq) := by
    rw [abs_mul, abs_div, abs_of_pos hpi, abs_of_nonneg hηe0]
    exact mul_le_mul (div_le_div_of_nonneg_right hηe1 hpi.le) hnpq (abs_nonneg _) (by positivity)
  have h3 : |η' / Real.pi * np - ηe / Real.pi * nq| ≤
      Lz * y / Real.pi * (Mp * nq) + 1 / Real.pi * (Cη / 2 * (δz + Lz * y) * nq) := by
    rw [e1]; exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have h4 : CS * (d' + εS) * np ≤ CS * (d + Ld * y + εS) * (Mp * nq) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCS) hnp hnp0 (by positivity)
  have h5 : Lz * y / Real.pi * (Mp * nq) + 1 / Real.pi * (Cη / 2 * (δz + Lz * y) * nq) +
      CS * (d + Ld * y + εS) * (Mp * nq) ≤ (CS * Mp * (d + εS) + Cη / Real.pi * δz +
        (CS * Mp * Ld + Lz * Mp / Real.pi + Cη * Lz / Real.pi) * y) * nq := by
    have e2 : (CS * Mp * (d + εS) + Cη / Real.pi * δz +
        (CS * Mp * Ld + Lz * Mp / Real.pi + Cη * Lz / Real.pi) * y) * nq -
        (Lz * y / Real.pi * (Mp * nq) + 1 / Real.pi * (Cη / 2 * (δz + Lz * y) * nq) +
          CS * (d + Ld * y + εS) * (Mp * nq)) = Cη / (2 * Real.pi) * (δz + Lz * y) * nq := by
      field_simp; ring
    have : 0 ≤ Cη / (2 * Real.pi) * (δz + Lz * y) * nq := by positivity
    linarith
  have h3' := abs_le.1 h3
  constructor <;> linarith

/-!
## The two-sided density clause at zero
-/

set_option maxHeartbeats 1000000 in
/-- **Sharp collar density bound for the canonical density at zero, with a
nearby weight.** For `0 < κ ≤ 1` there are `d_P > 0`, `C_P ≥ 0`, `ε_P W → 0`, `W₀` such that for
`W ≥ W₀`, `e ∈ bulkInterval κ`, Hermitian `X` with `d(X) ≤ d_P`, every `z` with `‖z - z_b‖ ≤ 1` and
every `q`: `|q*(z - X)Ψ_X(0)(z - X)*q - (η/π)‖q‖²| ≤ C_P(d(X) + ε_P W + ‖z - z_b‖)‖q‖²`,
`Ψ_X = collarDensity`, `η = Im z_b`. At `z = z_b` this is `K_XΨ_XK_X* = (η/π)I + O(…)`. -/
theorem collarDensity_two_sided (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hCM : CommonPortMeanContract) (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ (dP CP : ℝ) (εP : ℕ → ℝ) (W₀ : ℕ), 0 < dP ∧ 0 ≤ CP ∧ Tendsto εP atTop (𝓝 0) ∧
      (∀ W, 0 ≤ εP W) ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ e ∈ bulkInterval κ, ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        matchedDistance b e X ≤ dP → ∀ z : ℂ, ‖z - boundaryZ b e‖ ≤ 1 →
        ∀ q : Fin 2 × Fin W → ℂ,
          |quadForm (collarDensity W b e X 0)
              ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ *ᵥ q) -
            (boundaryZ b e).im / Real.pi * ∑ a, ‖q a‖ ^ 2| ≤
          CP * (matchedDistance b e X + εP W + ‖z - boundaryZ b e‖) * ∑ a, ‖q a‖ ^ 2 := by
  set κ' : ℝ := κ / 2 with hκ'def
  have hκ' : 0 < κ' := by positivity
  have hκ'2 : κ' < 2 := by rw [hκ'def]; linarith
  obtain ⟨dS, CS, εS, WS, hdS, hCS, hεS, hεS0, hS⟩ :=
    lintegral_condCollarDensity_two_sided hP hPD hCM hTM source hb0 hb hκ' hκ'2
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
  set Ld : ℝ := Lz / η ^ 2 + La
  have hLd : 0 < Ld := by positivity
  set h₀ : ℝ := min (κ / 2) (min (1 / Lz) (dS / (2 * Ld)))
  have hh₀ : 0 < h₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set Mp : ℝ := 2 * (1 + 4 / η ^ 2)
  have hMp : 0 ≤ Mp := by positivity
  set Cη : ℝ := 4 / η + 4 / η ^ 2
  have hCη : 0 ≤ Cη := by positivity
  set CP : ℝ := CS * Mp + Cη / Real.pi
  have hpi := Real.pi_pos
  have hCP : 0 ≤ CP := by positivity
  set B₀ : ℝ := CS * Mp * Ld + Lz * Mp / Real.pi + Cη * Lz / Real.pi
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨dS / 2, CP, εS, WS, by positivity, hCP, hεS, hεS0, ?_⟩
  intro W hW hW₀ e he X hX hd z hz q
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set d := matchedDistance b e X with hddef
  have hd0 : 0 ≤ d := le_max_of_le_left (norm_nonneg _)
  set nq := ∑ a, ‖q a‖ ^ 2 with hnqdef
  have hnq : 0 ≤ nq := by positivity
  set u := (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ *ᵥ q with hu
  have he' : e ∈ bulkInterval κ' := bulkInterval_mono (by rw [hκ'def]; linarith) he
  have hmem : ∀ y, |y| ≤ h₀ → e + y ∈ bulkInterval κ' := fun y hy =>
    bulkInterval_add_mem he (hy.trans (min_le_left _ _))
  have hηE : ∀ E ∈ bulkInterval κ', η ≤ (boundaryZ b E).im := fun E hE =>
    (BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (by linarith) hκ' hE).2
  have hzy : ∀ y, |y| ≤ h₀ → ‖boundaryZ b e - boundaryZ b (e + y)‖ ≤ Lz * |y| := by
    intro y hy
    have := norm_boundaryZ_sub_le (b := b) (by linarith) hκ' he' (hmem y hy)
    rwa [show e - (e + y) = -y by ring, abs_neg] at this
  have hdy : ∀ y, |y| ≤ h₀ → matchedDistance b (e + y) X ≤ d + Ld * |y| := by
    intro y hy
    have h1 := matchedDistance_le_energy (b := b) hW hX (hη.trans_le (hηE e he'))
      (hη.trans_le (hηE _ (hmem y hy)))
    have h2 : ‖matchedA (e + y) - matchedA e‖ ≤ La * |y| := by
      have := norm_matchedA_sub_le hκ' (hmem y hy) he'
      rwa [show e + y - e = y by ring] at this
    have h3 : ((boundaryZ b (e + y)).im * (boundaryZ b e).im)⁻¹ ≤ (η ^ 2)⁻¹ := by
      rw [sq]
      exact inv_anti₀ (by positivity) (mul_le_mul (hηE _ (hmem y hy)) (hηE e he') hη.le
        (hη.le.trans (hηE _ (hmem y hy))))
    have h5 : ‖boundaryZ b e - boundaryZ b (e + y)‖ *
        ((boundaryZ b (e + y)).im * (boundaryZ b e).im)⁻¹ ≤ Lz * |y| * (η ^ 2)⁻¹ :=
      mul_le_mul (hzy y hy) h3 (inv_nonneg.2 (mul_pos (hη.trans_le (hηE _ (hmem y hy)))
        (hη.trans_le (hηE e he'))).le) (mul_nonneg hLz.le (abs_nonneg _))
    have h6 : Lz * |y| * (η ^ 2)⁻¹ + La * |y| = Ld * |y| := by
      simp only [Ld]; field_simp
    linarith only [h1, h2, h5, h6]
  have hdyS : ∀ y, |y| ≤ h₀ → matchedDistance b (e + y) X ≤ dS := by
    intro y hy
    have h1 : |y| ≤ dS / (2 * Ld) := hy.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : Ld * |y| ≤ dS / 2 := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith only [h1]
    linarith only [hdy y hy, h2, hd]
  have hLzy : ∀ y, |y| ≤ h₀ → Lz * |y| ≤ 1 := by
    intro y hy
    have h1 : |y| ≤ 1 / Lz := hy.trans ((min_le_right _ _).trans (min_le_left _ _))
    calc Lz * |y| ≤ Lz * (1 / Lz) := mul_le_mul_of_nonneg_left h1 hLz.le
      _ = 1 := by field_simp
  set A : ℝ := CS * Mp * (d + εS W) + Cη / Real.pi * ‖z - boundaryZ b e‖ with hA
  have hA0 : 0 ≤ A := by have := hεS0 W; positivity
  set c : ℝ := (boundaryZ b e).im / Real.pi * nq with hc
  have he2 : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he).le
  have hηe0 : 0 ≤ (boundaryZ b e).im := hη.le.trans (hηE e he')
  have hηe1 : (boundaryZ b e).im ≤ 1 := boundaryZ_im_le_one' hb0.le (by linarith) he2
  -- the conditional bound at every nearby energy
  have hcond : ∀ y, |y| ≤ h₀ →
      ENNReal.ofReal (c - (A + B₀ * |y|) * nq) ≤ ∫⁻ ω, ENNReal.ofReal
          (quadForm (condCollarDensity b (e + y) X ω) u) ∂layerLaw W b .common ∧
        ∫⁻ ω, ENNReal.ofReal (quadForm (condCollarDensity b (e + y) X ω) u)
          ∂layerLaw W b .common ≤ ENNReal.ofReal (c + (A + B₀ * |y|) * nq) := by
    intro y hy
    have hη' := hηE _ (hmem y hy)
    have hη'0 : 0 < (boundaryZ b (e + y)).im := hη.trans_le hη'
    obtain ⟨hp1, hp2⟩ := weight_change hX (z := z) hη'0 q
    have hp3 := weight_change_two_sided hX (z := z) hη'0 q
    set K' := matchedLeadK b (e + y) X
    set p := K'ᴴ⁻¹ *ᵥ u with hpdef
    have heq : ∀ ω, quadForm (condCollarDensity b (e + y) X ω) u =
        quadForm (K' * condCollarDensity b (e + y) X ω * K'ᴴ) p := by
      intro ω
      have := quadForm_conjTranspose_mul_mul K'ᴴ (condCollarDensity b (e + y) X ω) p
      rw [conjTranspose_conjTranspose] at this
      rw [this]
      congr 1
      exact hp1.symm
    simp_rw [heq]
    obtain ⟨hlo, hhi⟩ := hS W hW hW₀ (e + y) (hmem y hy) X hX (hdyS y hy) p
    -- the scalar inputs
    set δ := ‖z - boundaryZ b (e + y)‖ with hδ
    have hδle : δ ≤ ‖z - boundaryZ b e‖ + Lz * |y| := by
      have := norm_sub_le_norm_sub_add_norm_sub z (boundaryZ b e) (boundaryZ b (e + y))
      linarith [hzy y hy]
    have hδ2 : δ ≤ 2 := by linarith [hLzy y hy]
    have hδ0 : 0 ≤ δ := norm_nonneg _
    have hinv : ((boundaryZ b (e + y)).im ^ 2)⁻¹ ≤ (η ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hη.le hη' 2)
    have hnp : ∑ a, ‖p a‖ ^ 2 ≤ Mp * nq := by
      refine hp2.trans (mul_le_mul_of_nonneg_right ?_ hnq)
      have hδsq : δ ^ 2 ≤ 4 := by
        have := pow_le_pow_left₀ hδ0 hδ2 2
        norm_num at this
        exact this
      have h4 : δ ^ 2 * ((boundaryZ b (e + y)).im ^ 2)⁻¹ ≤ 4 * (η ^ 2)⁻¹ :=
        mul_le_mul hδsq hinv (by positivity) (by norm_num)
      have hMpe : Mp = 2 * (1 + 4 * (η ^ 2)⁻¹) := by simp only [Mp, div_eq_mul_inv]
      rw [hMpe]
      linarith only [h4]
    have ht : δ / (boundaryZ b (e + y)).im ≤ δ / η :=
      div_le_div_of_nonneg_left hδ0 hη hη'
    have hnpq : |∑ a, ‖p a‖ ^ 2 - nq| ≤ Cη / 2 * (‖z - boundaryZ b e‖ + Lz * |y|) * nq := by
      refine hp3.trans (mul_le_mul_of_nonneg_right ?_ hnq)
      have ht0 : 0 ≤ δ / (boundaryZ b (e + y)).im := by positivity
      have htη : δ / η ≤ 2 / η := div_le_div_of_nonneg_right hδ2 hη.le
      have h1 : 2 * (δ / (boundaryZ b (e + y)).im) + (δ / (boundaryZ b (e + y)).im) ^ 2 ≤
          (2 + 2 / η) * (δ / η) := by
        have := mul_le_mul ht (ht.trans htη) ht0 (by positivity)
        linarith only [this, ht, sq (δ / (boundaryZ b (e + y)).im)]
      have h2 : (2 + 2 / η) * (δ / η) = Cη / 2 * δ := by
        simp only [Cη]; field_simp; ring
      have h3 : Cη / 2 * δ ≤ Cη / 2 * (‖z - boundaryZ b e‖ + Lz * |y|) :=
        mul_le_mul_of_nonneg_left hδle (by positivity)
      linarith only [h1, h2, h3]
    have hηη : |(boundaryZ b (e + y)).im - (boundaryZ b e).im| ≤ Lz * |y| := by
      have := Complex.abs_im_le_norm (boundaryZ b e - boundaryZ b (e + y))
      rw [Complex.sub_im, abs_sub_comm] at this
      exact this.trans (hzy y hy)
    obtain ⟨hb1, hb2⟩ := density_budget hnq (by positivity) hnp hnpq hηη hηe0 hηe1
      (hdy y hy) hd0 hLd.le (hεS0 W) hCS (abs_nonneg y) hCη hLz.le (norm_nonneg _)
    constructor
    · exact (ENNReal.ofReal_le_ofReal (by simp only [hc, hA]; linarith)).trans hlo
    · exact hhi.trans (ENNReal.ofReal_le_ofReal (by simp only [hc, hA]; linarith))
  -- continuity of the density and the interval averages
  have hφ : Continuous fun x => quadForm (collarDensity W b e X x) u := by
    unfold quadForm
    exact Complex.continuous_re.comp (continuous_const.dotProduct
      ((continuous_collarDensity hW b e hX).matrix_mulVec continuous_const))
  have hφ0 : ∀ x, 0 ≤ quadForm (collarDensity W b e X x) u := fun x =>
    quadForm_nonneg_of_posSemidef (collarDensity_posSemidef hW b e hX x) u
  have hint : ∀ r, 0 < r → r ≤ h₀ →
      ENNReal.ofReal (∫ x in Set.Icc (-r) r, quadForm (collarDensity W b e X x) u) =
        ∫⁻ x in Set.Icc (-r) r, ∫⁻ ω, ENNReal.ofReal
          (quadForm (condCollarDensity b (e + x) X ω) u) ∂layerLaw W b .common := by
    intro r hr _
    rw [← quadForm_collarTopProjector_eq hW hb e hX (-r) r u]
    exact collarConditionalDensityIdentity_holds W hW b hb0 hb e X hX (-r) r (by linarith) u
  have hup := le_of_forall_setIntegral_Icc_le' hφ (M := c + A * nq) (B := B₀ * nq) hh₀
    (by positivity) (by
      intro r hr hrh
      have hbd : ∫⁻ x in Set.Icc (-r) r, ∫⁻ ω, ENNReal.ofReal
            (quadForm (condCollarDensity b (e + x) X ω) u) ∂layerLaw W b .common ≤
          ∫⁻ x in Set.Icc (-r) r, ENNReal.ofReal (c + (A + B₀ * r) * nq) :=
        setLIntegral_mono' measurableSet_Icc fun x hx => by
          have hx' : |x| ≤ r := abs_le.2 ⟨hx.1, hx.2⟩
          refine (hcond x (hx'.trans hrh)).2.trans (ENNReal.ofReal_le_ofReal ?_)
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx' hB₀) hnq
          linarith only [this]
      have hc0 : 0 ≤ c := by positivity
      rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity),
        ← hint r hr hrh] at hbd
      have hpos : 0 ≤ (c + (A + B₀ * r) * nq) * (r - -r) :=
        mul_nonneg (by positivity) (by linarith)
      rw [ENNReal.ofReal_le_ofReal_iff hpos] at hbd
      exact hbd.trans (le_of_eq (by ring)))
  have hlow := ge_of_forall_setIntegral_Icc_ge' hφ (M := c - A * nq) (B := B₀ * nq) hh₀
    (by positivity) (by
      intro r hr hrh
      have hbd : ∫⁻ x in Set.Icc (-r) r, ENNReal.ofReal (c - (A + B₀ * r) * nq) ≤
          ∫⁻ x in Set.Icc (-r) r, ∫⁻ ω, ENNReal.ofReal
            (quadForm (condCollarDensity b (e + x) X ω) u) ∂layerLaw W b .common :=
        setLIntegral_mono' measurableSet_Icc fun x hx => by
          have hx' : |x| ≤ r := abs_le.2 ⟨hx.1, hx.2⟩
          refine (ENNReal.ofReal_le_ofReal ?_).trans (hcond x (hx'.trans hrh)).1
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx' hB₀) hnq
          linarith only [this]
      have hI0 : 0 ≤ ∫ x in Set.Icc (-r) r, quadForm (collarDensity W b e X x) u :=
        setIntegral_nonneg measurableSet_Icc fun x _ => hφ0 x
      rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul' (by linarith),
        ← hint r hr hrh] at hbd
      have hid : 2 * r * (c - A * nq - B₀ * nq * r) = (c - (A + B₀ * r) * nq) * (r - -r) := by
        ring
      rcases le_or_gt ((c - (A + B₀ * r) * nq) * (r - -r)) 0 with h | h
      · linarith only [hid, h, hI0]
      · rw [ENNReal.ofReal_le_ofReal_iff hI0] at hbd
        linarith only [hid, hbd])
  rw [abs_le]
  have hfin : A * nq ≤ CP * (d + εS W + ‖z - boundaryZ b e‖) * nq := by
    refine mul_le_mul_of_nonneg_right ?_ hnq
    have := hεS0 W
    have hid : CP * (d + εS W + ‖z - boundaryZ b e‖) - A =
        CS * Mp * ‖z - boundaryZ b e‖ + Cη / Real.pi * (d + εS W) := by
      simp only [hA, CP]; ring
    have : 0 ≤ CS * Mp * ‖z - boundaryZ b e‖ + Cη / Real.pi * (d + εS W) := by positivity
    linarith only [hid, this]
  constructor
  · linarith only [hlow, hfin]
  · linarith only [hup, hfin]

end BlockBand.Critical.Collar.Density

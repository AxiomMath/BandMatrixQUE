module

public import BlockBand.Endpoints.Response.RemoteHigherChainLayerAux
public import BlockBand.Endpoints.Response.RemoteHigherPinching

/-!
# The higher one-layer clock inequality

This file proves the higher-power logistic inequality for one fresh layer.

* `rhc_layer_det`: the inequality at fixed `X`, `A`, `W` from explicit inputs.
* `ClockLayerHigherLogistic`: the uniform statement, proved in `clockLayerHigherLogistic_of`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Endpoints

/-- `M = 1 + C₀ d + C₀`, `C₀ = max C_L C_a` (`a ≤ M H` on the jet domain). -/
def rhc_M (CL Ca d : ℝ) : ℝ := 1 + max CL Ca * d + max CL Ca

/-- The Young parameter `ε = 2^{-r} c_L / ((C_L + 1) M^{r-1})`. -/
def rhc_eps (r CL cL Ca d : ℝ) : ℝ := 2 ^ (-r) * cL / ((CL + 1) * rhc_M CL Ca d ^ (r - 1))

/-- The constant `C'` of the higher one-layer inequality. -/
def rhc_layerC (p r CL cL Ca C2 Cq d : ℝ) : ℝ :=
  r * rhc_M CL Ca d ^ (r - 1) * max CL Ca +
    r * rhc_D (r - 1) * p ^ 2 * C2 ^ 2 * rhc_M CL Ca d ^ r + rhc_E r * (p * Cq) ^ (r + 2) +
    CL * rhc_M CL Ca d ^ (r - 1) * rhc_eps r CL cL Ca d ^ (-((r - 1) / 2))

theorem rhc_M_ge_one {CL Ca d : ℝ} (hCL : 0 ≤ CL) (hd : 0 ≤ d) : 1 ≤ rhc_M CL Ca d := by
  unfold rhc_M
  have : 0 ≤ max CL Ca := le_max_of_le_left hCL
  have : 0 ≤ max CL Ca * d := mul_nonneg this hd
  linarith

theorem rhc_eps_pos {r CL cL Ca d : ℝ} (hCL : 0 ≤ CL) (hcL : 0 < cL) (hd : 0 ≤ d) :
    0 < rhc_eps r CL cL Ca d := by
  unfold rhc_eps
  have hM := rhc_M_ge_one (Ca := Ca) hCL hd
  have : 0 < rhc_M CL Ca d ^ (r - 1) := Real.rpow_pos_of_pos (by linarith) _
  positivity

theorem rhc_layerC_nonneg {p r CL cL Ca C2 Cq d : ℝ} (hp : 0 ≤ p) (hr : 1 ≤ r) (hCL : 0 ≤ CL)
    (hcL : 0 < cL) (hd : 0 ≤ d) (hCq : 0 ≤ Cq) : 0 ≤ rhc_layerC p r CL cL Ca C2 Cq d := by
  unfold rhc_layerC
  have hM := rhc_M_ge_one (Ca := Ca) hCL hd
  have h1 : 0 ≤ max CL Ca := le_max_of_le_left hCL
  have h2 : 0 ≤ rhc_D (r - 1) := rhc_D_nonneg (by linarith)
  have h3 : 0 ≤ rhc_E r := rhc_E_nonneg (by linarith)
  have h4 : 0 ≤ rhc_M CL Ca d ^ (r - 1) := Real.rpow_nonneg (by linarith) _
  have h5 : 0 ≤ rhc_M CL Ca d ^ r := Real.rpow_nonneg (by linarith) _
  have h6 : 0 ≤ (p * Cq) ^ (r + 2) := Real.rpow_nonneg (by positivity) _
  have h7 : 0 ≤ rhc_eps r CL cL Ca d ^ (-((r - 1) / 2)) :=
    Real.rpow_nonneg (rhc_eps_pos hCL hcL hd).le _
  have : 0 ≤ r := by linarith
  positivity

/-- A nonnegative function with `∫⁻ f ≤ B` has `∫ f ≤ B`. -/
theorem rhc_integral_le_of_lintegral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω, 0 ≤ f ω) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal B) : ∫ ω, f ω ∂μ ≤ B := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hf]
  exact ENNReal.toReal_le_of_le_ofReal hB h

/-- Moments of a function from an `eLpNorm` bound: `‖f‖_{L^m} ≤ B` (`m ≥ 1`, `f` measurable)
gives `|f|^m` integrable with `∫ |f|^m ≤ B^m`. -/
theorem rhc_abs_rpow_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Measurable f) {m B : ℝ} (hm : 1 ≤ m) (hB : 0 ≤ B)
    (h : eLpNorm f (ENNReal.ofReal m) μ ≤ ENNReal.ofReal B) :
    Integrable (fun ω => |f ω| ^ m) μ ∧ ∫ ω, |f ω| ^ m ∂μ ≤ B ^ m := by
  have hmem : MemLp f (ENNReal.ofReal m) μ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hint : Integrable (fun ω => |f ω| ^ m) μ := by
    have := hmem.integrable_norm_rpow (by simp; linarith) ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal (by linarith)] at this
    simpa only [Real.norm_eq_abs] using this
  refine ⟨hint, ?_⟩
  have habs : eLpNorm (fun ω => |f ω|) (ENNReal.ofReal m) μ = eLpNorm f (ENNReal.ofReal m) μ := by
    have := eLpNorm_norm (p := ENNReal.ofReal m) (μ := μ) f hf.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using this
  have hb := (ce_lintegral_pow_of_eLpNorm μ (fun ω => |f ω|) (fun ω => abs_nonneg _) hm
    (habs.trans_le h)).2
  rw [max_eq_left hB] at hb
  exact rhc_integral_le_of_lintegral_le (hf.abs.pow_const _).aestronglyMeasurable
    (fun ω => Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hB _) hb

/-- Integration of the pointwise power inequality (model-free). On a probability space, for
`0 ≤ h ≤ a + ℓ` (`a > 0`, `r ≥ 1`) with `h`, `h^r`, `ℓ`, `ℓ²`, `|ℓ|^{r+2}` integrable and
`E ℓ = 0`:
`E h^r + 2^{1-r}a^{r-1}(a - E h) ≤ a^r + r D_{r-1} a^{r-2} E ℓ² + (E_r/a²) E|ℓ|^{r+2}`. -/
theorem rhc_integrated_pointwise {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {h ℓ : Ω → ℝ} {a r : ℝ} (hr : 1 ≤ r) (ha : 0 < a)
    (hh0 : ∀ ω, 0 ≤ h ω) (hhl : ∀ ω, h ω ≤ a + ℓ ω) (hhi : Integrable h μ)
    (hhri : Integrable (fun ω => h ω ^ r) μ) (hℓi : Integrable ℓ μ)
    (hℓ2 : Integrable (fun ω => ℓ ω ^ 2) μ) (hℓq : Integrable (fun ω => |ℓ ω| ^ (r + 2)) μ)
    (hℓ0 : ∫ ω, ℓ ω ∂μ = 0) :
    ∫ ω, h ω ^ r ∂μ + 2 ^ (1 - r) * a ^ (r - 1) * (a - ∫ ω, h ω ∂μ) ≤
      a ^ r + r * rhc_D (r - 1) * a ^ (r - 2) * ∫ ω, ℓ ω ^ 2 ∂μ +
        rhc_E r / a ^ 2 * ∫ ω, |ℓ ω| ^ (r + 2) ∂μ := by
  set κ := (2 : ℝ) ^ (1 - r) * a ^ (r - 1)
  set D' := r * rhc_D (r - 1) * a ^ (r - 2)
  set E' := rhc_E r / a ^ 2
  have hpt : ∀ ω, h ω ^ r + κ * (a + ℓ ω - h ω) ≤
      a ^ r + r * a ^ (r - 1) * ℓ ω + D' * ℓ ω ^ 2 + E' * |ℓ ω| ^ (r + 2) := fun ω => by
    have := rhc_pointwise hr ha (hh0 ω) (hhl ω)
    have e : rhc_E r * |ℓ ω| ^ (r + 2) / a ^ 2 = E' * |ℓ ω| ^ (r + 2) := by ring
    rw [e] at this
    exact this
  have hX : Integrable (fun ω => a + ℓ ω - h ω) μ := ((integrable_const a).add hℓi).sub hhi
  have hXκ : Integrable (fun ω => κ * (a + ℓ ω - h ω)) μ := hX.const_mul κ
  have hY1 : Integrable (fun ω => r * a ^ (r - 1) * ℓ ω) μ := hℓi.const_mul _
  have hY2 : Integrable (fun ω => D' * ℓ ω ^ 2) μ := hℓ2.const_mul _
  have hY3 : Integrable (fun ω => E' * |ℓ ω| ^ (r + 2)) μ := hℓq.const_mul _
  have hZ1 : Integrable (fun ω => a ^ r + r * a ^ (r - 1) * ℓ ω) μ := (integrable_const _).add hY1
  have hZ2 : Integrable (fun ω => a ^ r + r * a ^ (r - 1) * ℓ ω + D' * ℓ ω ^ 2) μ := hZ1.add hY2
  have hmono : ∫ ω, (h ω ^ r + κ * (a + ℓ ω - h ω)) ∂μ ≤
      ∫ ω, (a ^ r + r * a ^ (r - 1) * ℓ ω + D' * ℓ ω ^ 2 + E' * |ℓ ω| ^ (r + 2)) ∂μ :=
    integral_mono (hhri.add hXκ) (hZ2.add hY3) hpt
  have hal : Integrable (fun ω => a + ℓ ω) μ := (integrable_const a).add hℓi
  rw [integral_add hhri hXκ, integral_const_mul, integral_sub hal hhi,
    integral_add (integrable_const a) hℓi, hℓ0, integral_add hZ2 hY3, integral_add hZ1 hY2,
    integral_add (integrable_const _) hY1, integral_const_mul, integral_const_mul,
    integral_const_mul, hℓ0, integral_const, integral_const] at hmono
  simpa using hmono

variable {W : ℕ}

/-- Klein's inequality at the old clock, with the passive mean (deterministic): for `A ⪰ 0`, any
`L` and `Ū` with `c I - Ū ⪰ 0`, `Tr(L*AL)^p ≤ (1 - p + pc) Tr A^p + ℓ(LL*)`. -/
theorem rhc_fresh_klein {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : A.PosSemidef) (L Ub : Matrix (Fin W) (Fin W) ℂ) {c : ℝ}
    (hmean : (((c : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - Ub).PosSemidef) :
    fracTrace p (Lᴴ * A * L) ≤ (1 - p + p * c) * fracTrace p A + rhc_ell p hA (L * Lᴴ) Ub := by
  set V : Matrix (Fin W) (Fin W) ℂ := (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
  have hV : V ∈ unitaryGroup (Fin W) ℂ := hA.isHermitian.eigenvectorUnitary.2
  set lam := hA.isHermitian.eigenvalues
  have hlam : ∀ i, 0 ≤ lam i ^ p := fun i => Real.rpow_nonneg (hA.eigenvalues_nonneg i) _
  have hHsum : fracTrace p A = ∑ i, lam i ^ p := fracTrace_eq_sum_eigenvalues_of_posSemidef hA p
  have hU0 : (L * Lᴴ).PosSemidef := posSemidef_self_mul_conjTranspose _
  have e0 : fracTrace p (Lᴴ * A * L) = fracTrace p (cej_sqrt hA * (L * Lᴴ) * cej_sqrt hA) :=
    (cej_fracTrace_sandwich p (cej_sqrt_mul_self hA)).symm
  have hk := rhc_klein_sandwich hp0 hp1 hA hU0
  have hsum : ∑ i, lam i ^ p * ((star V * (L * Lᴴ) * V) i i).re ≤
      c * fracTrace p A + ∑ i, lam i ^ p * ((star V * (L * Lᴴ - Ub) * V) i i).re := by
    rw [hHsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hs : ((star V * (L * Lᴴ) * V) i i).re =
        ((star V * Ub * V) i i).re + ((star V * (L * Lᴴ - Ub) * V) i i).re := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, Complex.sub_re]; ring
    rw [hs, mul_add]
    have := mul_le_mul_of_nonneg_left (rhc_diag_le_of_posSemidef_sub hV hmean i) (hlam i)
    linarith
  have hℓe : rhc_ell p hA (L * Lᴴ) Ub =
      p * ∑ i, lam i ^ p * ((star V * (L * Lᴴ - Ub) * V) i i).re := rfl
  rw [e0, hℓe]
  have := mul_le_mul_of_nonneg_left hsum hp0.le
  nlinarith

/-- The real conclusion of the higher one-layer step: from the integrated power inequality
(`hmono`), the `r = 1` logistic (`hR2`) and the fluctuation moments (`hI2`, `hIq`),
`I_r + (2^{1-r}c_L/2) u H^{r+1}/γ^p ≤ (1 + C'δ + C'u) H^r + C' u g^{(r+1)(1-p)}γ^{pr}`. -/
theorem rhc_layer_det_final {r p H γ g u δ d CL cL Ca C2 Cq a Ir I1 I2 Iq : ℝ} (hr : 1 ≤ r)
    (hp0 : 0 < p) (hHp : 0 < H) (hγp : 0 < γ) (hg0 : 0 ≤ g) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hδ0 : 0 ≤ δ) (hδd : δ ≤ d) (hd : 0 ≤ d) (hCL : 0 ≤ CL) (hcL : 0 < cL) (hCq : 0 ≤ Cq)
    (ha : a = (1 + max CL Ca * δ + max CL Ca * u ^ 2) * H)
    (hmono : Ir + 2 ^ (1 - r) * a ^ (r - 1) * (a - I1) ≤
      a ^ r + r * rhc_D (r - 1) * a ^ (r - 2) * I2 + rhc_E r / a ^ 2 * Iq)
    (hR2 : I1 + cL * u * (H ^ 2 / γ ^ p) ≤ a + CL * u * (g ^ (2 * (1 - p)) * γ ^ p))
    (hI2 : I2 ≤ p ^ 2 * H ^ 2 * C2 ^ 2 * u) (hIq : Iq ≤ (p * Cq) ^ (r + 2) * H ^ (r + 2) * u) :
    Ir + 2 ^ (1 - r) * cL / 2 * u * (H ^ (r + 1) / γ ^ p) ≤
      (1 + rhc_layerC p r CL cL Ca C2 Cq d * δ + rhc_layerC p r CL cL Ca C2 Cq d * u) * H ^ r +
        rhc_layerC p r CL cL Ca C2 Cq d * u * (g ^ ((r + 1) * (1 - p)) * γ ^ (p * r)) := by
  have hr0 : 0 < r := by linarith
  have hH0 := hHp.le
  have hu2 : u ^ 2 ≤ u := by rw [sq]; exact mul_le_of_le_one_left hu0 hu1
  set C₀ := max CL Ca with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_of_le_left hCL
  set M := rhc_M CL Ca d with hMdef
  have hM1 : 1 ≤ M := rhc_M_ge_one hCL hd
  have hHa : H ≤ a := by
    rw [ha]; have : 0 ≤ C₀ * δ + C₀ * u ^ 2 := by positivity
    exact le_mul_of_one_le_left hH0 (by linarith)
  have ha0 : 0 < a := lt_of_lt_of_le hHp hHa
  have haM : a ≤ M * H := by
    rw [ha]; refine mul_le_mul_of_nonneg_right ?_ hH0
    have h1 : C₀ * δ ≤ C₀ * d := mul_le_mul_of_nonneg_left hδd hC₀0
    have h2 : C₀ * u ^ 2 ≤ C₀ := mul_le_of_le_one_right hC₀0 (hu2.trans hu1)
    simp only [hMdef, rhc_M]; linarith
  set Qr := H ^ (r + 1) / γ ^ p with hQr
  set Fr := g ^ ((r + 1) * (1 - p)) * γ ^ (p * r) with hFr
  have hQr0 : 0 ≤ Qr := by positivity
  have hFr0 : 0 ≤ Fr := by positivity
  have hF10 : 0 ≤ g ^ (2 * (1 - p)) * γ ^ p := by positivity
  set ε := rhc_eps r CL cL Ca d with hεdef
  have hεp : 0 < ε := rhc_eps_pos hCL hcL hd
  have hMr1 : 0 < M ^ (r - 1) := Real.rpow_pos_of_pos (by linarith) _
  have ht : (2 : ℝ) ^ (1 - r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have ht0 : 0 ≤ (2 : ℝ) ^ (1 - r) := Real.rpow_nonneg (by norm_num) _
  have har1 : 0 ≤ a ^ (r - 1) := Real.rpow_nonneg ha0.le _
  have hκ0 : 0 ≤ 2 ^ (1 - r) * a ^ (r - 1) := mul_nonneg ht0 har1
  have hHr1 : H ^ (r - 1) ≤ a ^ (r - 1) := Real.rpow_le_rpow hH0 hHa (by linarith)
  have hκQ : 2 ^ (1 - r) * Qr ≤ 2 ^ (1 - r) * a ^ (r - 1) * (H ^ 2 / γ ^ p) := by
    have e : H ^ (r + 1) = H ^ (r - 1) * H ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hHp]; push_cast; ring_nf
    rw [hQr, e, mul_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hHr1 (by positivity)) ht0
  have haMr1 : a ^ (r - 1) ≤ M ^ (r - 1) * H ^ (r - 1) := by
    rw [← Real.mul_rpow (by linarith) hH0]; exact Real.rpow_le_rpow ha0.le haM (by linarith)
  have hκF : 2 ^ (1 - r) * a ^ (r - 1) * (g ^ (2 * (1 - p)) * γ ^ p) ≤
      M ^ (r - 1) * (ε * Qr + ε ^ (-((r - 1) / 2)) * Fr) := by
    have hy := rhc_forcing_young (p := p) hHp hγp hg0 hr hεp
    have h1 : 2 ^ (1 - r) * a ^ (r - 1) ≤ M ^ (r - 1) * H ^ (r - 1) :=
      calc 2 ^ (1 - r) * a ^ (r - 1) ≤ 1 * a ^ (r - 1) := mul_le_mul_of_nonneg_right ht har1
        _ = a ^ (r - 1) := one_mul _
        _ ≤ M ^ (r - 1) * H ^ (r - 1) := haMr1
    calc 2 ^ (1 - r) * a ^ (r - 1) * (g ^ (2 * (1 - p)) * γ ^ p)
        ≤ M ^ (r - 1) * H ^ (r - 1) * (g ^ (2 * (1 - p)) * γ ^ p) :=
          mul_le_mul_of_nonneg_right h1 hF10
      _ = M ^ (r - 1) * (H ^ (r - 1) * (g ^ (2 * (1 - p)) * γ ^ p)) := by ring
      _ ≤ M ^ (r - 1) * (ε * Qr + ε ^ (-((r - 1) / 2)) * Fr) :=
          mul_le_mul_of_nonneg_left hy hMr1.le
  have hε : CL * M ^ (r - 1) * ε ≤ 2 ^ (1 - r) * cL / 2 := by
    rw [hεdef, rhc_eps, ← hMdef]
    have e : (2 : ℝ) ^ (1 - r) = 2 * 2 ^ (-r) := by
      rw [show (1 : ℝ) - r = 1 + -r by ring, Real.rpow_add (by norm_num), Real.rpow_one]
    rw [e]
    have h2r : 0 < (2 : ℝ) ^ (-r) := Real.rpow_pos_of_pos (by norm_num) _
    rw [show CL * M ^ (r - 1) * (2 ^ (-r) * cL / ((CL + 1) * M ^ (r - 1))) =
      2 ^ (-r) * cL * (CL / (CL + 1)) by field_simp]
    have : CL / (CL + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 ^ (-r) * cL)
    linarith
  have hMr : a ^ r ≤ M ^ r * H ^ r := by
    rw [← Real.mul_rpow (by linarith) hH0]; exact Real.rpow_le_rpow ha0.le haM hr0.le
  have hD := rhc_D_nonneg (s := r - 1) (by linarith)
  have hT2 : r * rhc_D (r - 1) * a ^ (r - 2) * I2 ≤
      r * rhc_D (r - 1) * p ^ 2 * C2 ^ 2 * M ^ r * u * H ^ r := by
    have hD0 : 0 ≤ r * rhc_D (r - 1) * a ^ (r - 2) := by
      have := Real.rpow_nonneg ha0.le (r - 2); positivity
    have ha2 : a ^ (r - 2) * H ^ 2 ≤ a ^ r := by
      have e : a ^ r = a ^ (r - 2) * a ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ha0]; push_cast; ring_nf
      rw [e]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hHa 2) (Real.rpow_nonneg ha0.le _)
    calc r * rhc_D (r - 1) * a ^ (r - 2) * I2
        ≤ r * rhc_D (r - 1) * a ^ (r - 2) * (p ^ 2 * H ^ 2 * C2 ^ 2 * u) :=
          mul_le_mul_of_nonneg_left hI2 hD0
      _ = r * rhc_D (r - 1) * p ^ 2 * C2 ^ 2 * u * (a ^ (r - 2) * H ^ 2) := by ring
      _ ≤ r * rhc_D (r - 1) * p ^ 2 * C2 ^ 2 * u * (M ^ r * H ^ r) :=
          mul_le_mul_of_nonneg_left (ha2.trans hMr) (by positivity)
      _ = _ := by ring
  have hE := rhc_E_nonneg (r := r) hr0.le
  have hTq : rhc_E r / a ^ 2 * Iq ≤ rhc_E r * (p * Cq) ^ (r + 2) * u * H ^ r := by
    have hE0 : 0 ≤ rhc_E r / a ^ 2 := by positivity
    have hH2 : H ^ (r + 2) / a ^ 2 ≤ H ^ r := by
      have e : H ^ (r + 2) = H ^ r * H ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hHp]; push_cast; ring_nf
      rw [e, div_le_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hHa 2) (Real.rpow_nonneg hH0 _)
    calc rhc_E r / a ^ 2 * Iq ≤ rhc_E r / a ^ 2 * ((p * Cq) ^ (r + 2) * H ^ (r + 2) * u) :=
          mul_le_mul_of_nonneg_left hIq hE0
      _ = rhc_E r * (p * Cq) ^ (r + 2) * u * (H ^ (r + 2) / a ^ 2) := by ring
      _ ≤ rhc_E r * (p * Cq) ^ (r + 2) * u * H ^ r :=
          mul_le_mul_of_nonneg_left hH2 (by positivity)
  have har : a ^ r ≤ (1 + r * M ^ (r - 1) * C₀ * δ + r * M ^ (r - 1) * C₀ * u) * H ^ r := by
    rw [ha, Real.mul_rpow (by positivity) hH0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hH0 _)
    have hx : C₀ * δ + C₀ * u ^ 2 ≤ C₀ * d + C₀ := by
      have h1 : C₀ * δ ≤ C₀ * d := mul_le_mul_of_nonneg_left hδd hC₀0
      have h2 : C₀ * u ^ 2 ≤ C₀ := mul_le_of_le_one_right hC₀0 (hu2.trans hu1)
      linarith
    have h := rhc_one_add_rpow_le hr (by positivity) hx
    rw [show 1 + (C₀ * d + C₀) = M by simp only [hMdef, rhc_M, hC₀]; ring,
      show 1 + (C₀ * δ + C₀ * u ^ 2) = 1 + C₀ * δ + C₀ * u ^ 2 by ring] at h
    have : r * M ^ (r - 1) * (C₀ * δ + C₀ * u ^ 2) ≤
        r * M ^ (r - 1) * C₀ * δ + r * M ^ (r - 1) * C₀ * u := by
      have : C₀ * u ^ 2 ≤ C₀ * u := mul_le_mul_of_nonneg_left hu2 hC₀0
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ r * M ^ (r - 1))
      linarith
    linarith
  have hK0nn : 0 ≤ r * M ^ (r - 1) * C₀ := by positivity
  have hK2nn : 0 ≤ r * rhc_D (r - 1) * p ^ 2 * C2 ^ 2 * M ^ r := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ M) r
    positivity
  have hKqnn : 0 ≤ rhc_E r * (p * Cq) ^ (r + 2) := by
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ p * Cq) (r + 2)
    positivity
  have key := rhc_layer_real (Ir := Ir) (I1 := I1) (Q1 := H ^ 2 / γ ^ p)
    (F1 := g ^ (2 * (1 - p)) * γ ^ p) hmono hR2 hκ0 hκQ hκF hε hT2 hTq har hu0 hCL hcL.le
    hQr0 hFr0 (Real.rpow_nonneg hH0 _) hδ0 hK0nn hK2nn hKqnn hMr1.le (Real.rpow_nonneg hεp.le _)
  have hCe : r * M ^ (r - 1) * C₀ + r * rhc_D (r - 1) * p ^ 2 * C2 ^ 2 * M ^ r +
      rhc_E r * (p * Cq) ^ (r + 2) + CL * M ^ (r - 1) * ε ^ (-((r - 1) / 2)) =
        rhc_layerC p r CL cL Ca C2 Cq d := by
    rw [rhc_layerC]
  rw [hCe] at key
  exact key

/-- **The higher one-layer clock inequality at fixed old data**. Inputs at fixed `W ≥ 1`, passive
`X` with `δ₀ ≤ d` and `A ⪰ 0`: the `r = 1` logistic inequality (`hlog`, constants `C_L`, `c_L`),
the passive mean bound (`hmean`, constant `C_a`), `E‖L‖² < ∞` and the bilinear fluctuation
bounds at `L²` and `L^{r+2}` (`PassiveSourceMixingContract.oneStepFluctuation`, constants `C₂`,
`C_q`). Conclusion with
`c' = 2^{1-r}c_L/2` and `C' = rhc_layerC`:
`E_ν H_{p,+}^r + (c'/W) H^{r+1}/γ^p ≤ (1 + C'δ₀ + C'/W) H^r + (C'/W) g^{(r+1)(1-p)}γ^{pr}`.
-/
theorem rhc_layer_det {b E p r CL cL Ca C2 Cq CU d : ℝ} {X A : Matrix (Fin W) (Fin W) ℂ}
    (hA : A.PosSemidef) (hp0 : 0 < p) (hp1 : p < 1) (hr : 1 ≤ r) (hpr : p * r ≤ 1)
    (hW1 : (1 : ℝ) ≤ W) (hCL : 0 ≤ CL) (hcL : 0 < cL) (hCa : 0 ≤ Ca) (hC2 : 0 ≤ C2)
    (hCq : 0 ≤ Cq) (hd : 0 ≤ d) (hδd : jetDistance0 b E X ≤ d)
    (hlog : ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν))
          ∂freshLaw W b +
        ENNReal.ofReal (cL / W) * ENNReal.ofReal (fracTrace p A ^ 2 / A.trace.re ^ p) ≤
      ENNReal.ofReal ((1 + CL * jetDistance0 b E X + CL / (W : ℝ) ^ 2) * fracTrace p A) +
        ENNReal.ofReal (CL / W) * ENNReal.ofReal
          (|conductanceOf (passiveTransmission b E X)| ^ (2 * (1 - p)) * A.trace.re ^ p))
    (hmean : (((1 + Ca * jetDistance0 b E X + Ca / (W : ℝ) ^ 2 : ℝ) : ℂ) •
        (1 : Matrix (Fin W) (Fin W) ℂ) - matrixExpect (freshLaw W b) (freshU b E X)).PosSemidef)
    (hL2 : ∫⁻ ν, ENNReal.ofReal (‖freshL b E X ν‖ ^ 2) ∂freshLaw W b ≤ ENNReal.ofReal CU)
    (hfl2 : ∀ u v : Fin W → ℂ, eLpNorm (fun ν => bilinear u (freshU b E X ν -
        matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal (C2 / Real.sqrt W * vecNorm u * vecNorm v))
    (hflq : ∀ u v : Fin W → ℂ, eLpNorm (fun ν => bilinear u (freshU b E X ν -
        matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal (r + 2)) (freshLaw W b) ≤
      ENNReal.ofReal (Cq / Real.sqrt W * vecNorm u * vecNorm v)) :
    ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν) ^ r)
        ∂freshLaw W b +
      ENNReal.ofReal (2 ^ (1 - r) * cL / 2 / W) *
        ENNReal.ofReal (fracTrace p A ^ (r + 1) / A.trace.re ^ p) ≤
    ENNReal.ofReal ((1 + rhc_layerC p r CL cL Ca C2 Cq d * jetDistance0 b E X +
        rhc_layerC p r CL cL Ca C2 Cq d / W) * fracTrace p A ^ r) +
      ENNReal.ofReal (rhc_layerC p r CL cL Ca C2 Cq d / W) * ENNReal.ofReal
        (|conductanceOf (passiveTransmission b E X)| ^ ((r + 1) * (1 - p)) *
          A.trace.re ^ (p * r)) := by
  have hμ := cel_isProbabilityMeasure_freshLaw W b
  have hr0 : 0 < r := by linarith
  set H := fracTrace p A with hHdef
  set γ := A.trace.re with hγdef
  set δ := jetDistance0 b E X with hδdef
  set g := |conductanceOf (passiveTransmission b E X)| with hgdef
  set C' := rhc_layerC p r CL cL Ca C2 Cq d with hC'def
  have hH0 : 0 ≤ H := fracTrace_nonneg p A
  have hγ0 : 0 ≤ γ := (Complex.le_def.mp hA.trace_nonneg).1
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hg0 : 0 ≤ g := abs_nonneg _
  have hC'0 : 0 ≤ C' := rhc_layerC_nonneg hp0.le hr hCL hcL hd hCq
  have hhle : ∀ ν, fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν) ≤
      ‖freshL b E X ν‖ ^ (2 * p) * H := fun ν =>
    fracTrace_conjTranspose_mul_mul_le_of_norm_le hA _ (norm_nonneg _) le_rfl hp0.le
  have hFr0 : 0 ≤ g ^ ((r + 1) * (1 - p)) * γ ^ (p * r) := by positivity
  have hW0 : (0 : ℝ) < W := by linarith
  -- the degenerate clock
  rcases hH0.eq_or_lt with hHz | hHp
  · have hz : ∀ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν) ^ r)
        = 0 := fun ν => by
      have h1 := hhle ν
      rw [← hHz, mul_zero] at h1
      rw [le_antisymm h1 (fracTrace_nonneg _ _), Real.zero_rpow hr0.ne', ENNReal.ofReal_zero]
    have e2 : H ^ (r + 1) / γ ^ p = 0 := by rw [← hHz, Real.zero_rpow (by linarith), zero_div]
    rw [lintegral_congr hz, lintegral_zero, e2, ENNReal.ofReal_zero, mul_zero, zero_add]
    exact zero_le
  -- `γ > 0`
  have hγp : 0 < γ := by
    rcases hγ0.eq_or_lt with h0 | h0
    · exfalso
      have := fracTrace_le_card_rpow_mul_trace_rpow hA hp0 hp1.le
      rw [← hγdef, ← h0, Real.zero_rpow hp0.ne', mul_zero] at this
      linarith
    · exact h0
  -- the width
  set u := (W : ℝ)⁻¹ with hudef
  have hu0 : 0 ≤ u := inv_nonneg.mpr hW0.le
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ hW1
  have hu2 : u ^ 2 ≤ u := by rw [sq]; exact mul_le_of_le_one_left hu0 hu1
  have eW : ∀ x : ℝ, x / W = x * u := fun x => div_eq_mul_inv _ _
  have eW2 : ∀ x : ℝ, x / (W : ℝ) ^ 2 = x * u ^ 2 := fun x => by rw [div_eq_mul_inv, inv_pow]
  -- the level `a`
  set C₀ := max CL Ca with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_of_le_left hCL
  set M := rhc_M CL Ca d with hMdef
  have hM1 : 1 ≤ M := rhc_M_ge_one hCL hd
  set a := (1 + C₀ * δ + C₀ * u ^ 2) * H with hadef
  have hHa : H ≤ a := by
    have : 0 ≤ C₀ * δ + C₀ * u ^ 2 := by positivity
    exact le_mul_of_one_le_left hH0 (by linarith)
  have ha0 : 0 < a := lt_of_lt_of_le hHp hHa
  have haM : a ≤ M * H := by
    refine mul_le_mul_of_nonneg_right ?_ hH0
    have h1 : C₀ * δ ≤ C₀ * d := mul_le_mul_of_nonneg_left hδd hC₀0
    have h2 : C₀ * u ^ 2 ≤ C₀ := mul_le_of_le_one_right hC₀0 (hu2.trans hu1)
    simp only [hMdef, rhc_M]; linarith
  -- the fresh functions
  set μ := freshLaw W b with hμdef
  set Ub := matrixExpect μ (freshU b E X) with hUbdef
  set h : LayerSample W .oneBlockOnePort → ℝ :=
    fun ν => fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν) with hhdef
  set ℓ : LayerSample W .oneBlockOnePort → ℝ := fun ν => rhc_ell p hA (freshU b E X ν) Ub
    with hℓdef
  have hh0 : ∀ ν, 0 ≤ h ν := fun ν => fracTrace_nonneg _ _
  have hLm : Measurable (freshL b E X) := cel_measurable_freshL b E X
  have hUm : Measurable (freshU b E X) := cej_measurable_freshU b E X
  have hhm : Measurable h := by
    have hm : Measurable fun ν => (freshL b E X ν)ᴴ * A * freshL b E X ν :=
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
        continuous_id).measurable.comp hLm
    exact rh_measurable_fracTrace hm (fun ν => isHermitian_conjTranspose_mul_mul _ hA.isHermitian)
      hp0
  have hL2int : Integrable (fun ν => ‖freshL b E X ν‖ ^ 2) μ := by
    refine ⟨((continuous_norm.measurable.comp hLm).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ν => by positivity)]
    exact lt_of_le_of_lt hL2 ENNReal.ofReal_lt_top
  have henv : ∀ Z : ℝ, Integrable (fun ν => (1 + ‖freshL b E X ν‖ ^ 2) * Z) μ := fun Z =>
    ((integrable_const 1).add hL2int).mul_const Z
  have hhint : Integrable h μ := by
    refine (henv H).mono' hhm.aestronglyMeasurable (Filter.Eventually.of_forall fun ν => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hh0 ν)]
    exact (hhle ν).trans (mul_le_mul_of_nonneg_right
      (rhc_rpow_le_one_add_sq (norm_nonneg _) (by positivity) (by linarith)) hH0)
  have hhrint : Integrable (fun ν => h ν ^ r) μ := by
    refine (henv (H ^ r)).mono' (hhm.pow_const r).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ν => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hh0 ν) _)]
    calc h ν ^ r ≤ (‖freshL b E X ν‖ ^ (2 * p) * H) ^ r := Real.rpow_le_rpow (hh0 ν) (hhle ν) hr0.le
      _ = ‖freshL b E X ν‖ ^ (2 * (p * r)) * H ^ r := by
          rw [Real.mul_rpow (by positivity) hH0, ← Real.rpow_mul (norm_nonneg _)]; ring_nf
      _ ≤ (1 + ‖freshL b E X ν‖ ^ 2) * H ^ r := mul_le_mul_of_nonneg_right
          (rhc_rpow_le_one_add_sq (norm_nonneg _) (by positivity) (by linarith))
          (Real.rpow_nonneg hH0 _)
  -- Klein: `h ≤ a + ℓ`
  have hkl : ∀ ν, h ν ≤ a + ℓ ν := by
    intro ν
    have hk := rhc_fresh_klein hp0 hp1 hA (freshL b E X ν) Ub hmean
    have hpCa : p * Ca ≤ C₀ := (mul_le_of_le_one_left hCa hp1.le).trans (le_max_right _ _)
    have h1 : p * Ca * δ ≤ C₀ * δ := mul_le_mul_of_nonneg_right hpCa hδ0
    have h2 : p * Ca * u ^ 2 ≤ C₀ * u ^ 2 := mul_le_mul_of_nonneg_right hpCa (sq_nonneg u)
    have h3 : (1 - p + p * (1 + Ca * δ + Ca / (W : ℝ) ^ 2)) * H ≤ a := by
      rw [eW2]; refine mul_le_mul_of_nonneg_right ?_ hH0; nlinarith
    have : h ν ≤ (1 - p + p * (1 + Ca * δ + Ca / (W : ℝ) ^ 2)) * H + ℓ ν := hk
    linarith
  -- moments of `ℓ`
  have hℓm : Measurable ℓ := (rhc_continuous_ell p hA Ub).measurable.comp hUm
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
  have hℓ2 := rhc_ell_eLpNorm hp0 hA hUm Ub (q := ENNReal.ofReal 2)
    (ENNReal.one_le_ofReal.mpr (by norm_num)) (C := C2 / Real.sqrt W) (by positivity) hfl2
  have hℓq := rhc_ell_eLpNorm hp0 hA hUm Ub (q := ENNReal.ofReal (r + 2))
    (ENNReal.one_le_ofReal.mpr (by linarith)) (C := Cq / Real.sqrt W) (by positivity) hflq
  have hmem2 : MemLp ℓ (ENNReal.ofReal 2) μ := lt_of_le_of_lt hℓ2 ENNReal.ofReal_lt_top
  have hℓint : Integrable ℓ μ := hmem2.integrable (ENNReal.one_le_ofReal.mpr (by norm_num))
  obtain ⟨hℓsq', hI2'⟩ := rhc_abs_rpow_moment hℓm (by norm_num) (by positivity) hℓ2
  obtain ⟨hℓqi, hIq'⟩ := rhc_abs_rpow_moment hℓm (by linarith) (by positivity) hℓq
  have e2 : ∀ ν, |ℓ ν| ^ (2 : ℝ) = ℓ ν ^ 2 := fun ν => by rw [Real.rpow_two, sq_abs]
  have hℓsq : Integrable (fun ν => ℓ ν ^ 2) μ := hℓsq'.congr (Filter.Eventually.of_forall e2)
  have hI2 : ∫ ν, ℓ ν ^ 2 ∂μ ≤ p ^ 2 * H ^ 2 * C2 ^ 2 * u := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall e2)]
    refine hI2'.trans (le_of_eq ?_)
    rw [Real.rpow_two, div_eq_mul_inv, mul_pow, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hW0.le]
    ring
  have hIq : ∫ ν, |ℓ ν| ^ (r + 2) ∂μ ≤ (p * Cq) ^ (r + 2) * H ^ (r + 2) * u := by
    refine hIq'.trans ?_
    rw [show p * H * (Cq / Real.sqrt W) = (p * Cq * H) / Real.sqrt W by ring,
      Real.div_rpow (by positivity) hsW.le, Real.mul_rpow (by positivity) hH0,
      div_le_iff₀ (Real.rpow_pos_of_pos hsW _)]
    have hsq : (W : ℝ) ≤ Real.sqrt W ^ (r + 2) := by
      have h1 : (1 : ℝ) ≤ Real.sqrt W := Real.one_le_sqrt.mpr hW1
      calc (W : ℝ) = Real.sqrt W ^ ((2 : ℕ) : ℝ) := by
            rw [Real.rpow_natCast, Real.sq_sqrt hW0.le]
        _ ≤ Real.sqrt W ^ (r + 2) := Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; linarith)
    calc (p * Cq) ^ (r + 2) * H ^ (r + 2) = (p * Cq) ^ (r + 2) * H ^ (r + 2) * u * W := by
          rw [hudef]; field_simp
      _ ≤ (p * Cq) ^ (r + 2) * H ^ (r + 2) * u * Real.sqrt W ^ (r + 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
  have hℓ0 : ∫ ν, ℓ ν ∂μ = 0 := rhc_integral_ell p hA (cej_integrable_freshU hL2)
  -- integrate the pointwise power inequality
  have hmono := rhc_integrated_pointwise hr ha0 hh0 hkl hhint hhrint hℓint hℓsq hℓqi hℓ0
  set Ir := ∫ ν, h ν ^ r ∂μ with hIrdef
  set I1 := ∫ ν, h ν ∂μ with hI1def
  -- the `r = 1` logistic inequality in real numbers
  have hI1e : ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν)) ∂μ =
      ENNReal.ofReal I1 :=
    (ofReal_integral_eq_lintegral_ofReal hhint (Filter.Eventually.of_forall hh0)).symm
  have hIrnn : 0 ≤ Ir := integral_nonneg fun ν => Real.rpow_nonneg (hh0 ν) _
  have hI1nn : 0 ≤ I1 := integral_nonneg hh0
  have hQ10 : 0 ≤ H ^ 2 / γ ^ p := by positivity
  have hF10 : 0 ≤ g ^ (2 * (1 - p)) * γ ^ p := by positivity
  have hR2 : I1 + cL * u * (H ^ 2 / γ ^ p) ≤ a + CL * u * (g ^ (2 * (1 - p)) * γ ^ p) := by
    have h1 := hlog
    rw [hI1e, eW, eW, eW2, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hI1nn (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    have h3 : CL * δ ≤ C₀ * δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
    have h4 : CL * u ^ 2 ≤ C₀ * u ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg u)
    have : (1 + CL * δ + CL * u ^ 2) * H ≤ a := mul_le_mul_of_nonneg_right (by linarith) hH0
    linarith
  have key := rhc_layer_det_final (Ir := Ir) (Ca := Ca) (C2 := C2) (d := d) hr hp0 hHp hγp
    hg0 hu0 hu1 hδ0 hδd hd hCL hcL hCq rfl hmono hR2 hI2 hIq
  -- back to `ℝ≥0∞`
  have hIre : ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν) ^ r) ∂μ =
      ENNReal.ofReal Ir :=
    (ofReal_integral_eq_lintegral_ofReal hhrint
      (Filter.Eventually.of_forall fun ν => Real.rpow_nonneg (hh0 ν) _)).symm
  have hQr0 : 0 ≤ H ^ (r + 1) / γ ^ p := by positivity
  rw [hIre, eW, eW, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hIrnn (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  calc Ir + 2 ^ (1 - r) * cL / 2 * u * (H ^ (r + 1) / γ ^ p)
      ≤ (1 + C' * δ + C' * u) * H ^ r + C' * u * (g ^ ((r + 1) * (1 - p)) * γ ^ (p * r)) := key
    _ = _ := by ring

/-- The higher one-layer clock inequality without the weight, deterministic in the old passive
input `X` in a fixed jet domain and in the old clock `A ⪰ 0`:
`E_ν H_p(L*AL)^r + (c/W) H_p^{r+1}/γ^p ≤ (1 + Cδ₀ + C/W) H_p^r + (C/W) |g|^{(r+1)(1-p)} γ^{pr}`,
for `0 < p < 1`, `r ≥ 1`, `pr < 1`. It is proved in `clockLayerHigherLogistic_of`. The `C/W` in
the bracket (instead of `CW⁻²`) is the cost of the fluctuation of `H_{p,+}` paid without the
concavity of `H^r`; it is absorbed by the `Cy/W` term of the discrete comparison. -/
def ClockLayerHigherLogistic : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 → ∀ s : ℂ, IsStationaryJet b E s →
      ∃ (C c d : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 < c ∧ 0 < d ∧ ∀ W : ℕ, W₀ ≤ W →
        ∀ X : Matrix (Fin W) (Fin W) ℂ, cel_InJetDomain b E s d X →
          ∀ A : Matrix (Fin W) (Fin W) ℂ, A.PosSemidef →
            ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν) ^ r)
                ∂freshLaw W b +
              ENNReal.ofReal (c / W) * ENNReal.ofReal (fracTrace p A ^ (r + 1) / A.trace.re ^ p) ≤
            ENNReal.ofReal ((1 + C * jetDistance0 b E X + C / W) * fracTrace p A ^ r) +
              ENNReal.ofReal (C / W) * ENNReal.ofReal
                (|conductanceOf (passiveTransmission b E X)| ^ ((r + 1) * (1 - p)) *
                  A.trace.re ^ (p * r))

/-- **`ClockLayerHigherLogistic` from the `r = 1` chain.** Hypotheses: `ClockLayerLogistic`
(proved from `ClockLayerJensenGap` and `OnePortPassiveMean` by `clockLayerLogistic_of_jensenGap`),
`OnePortPassiveMean`, `OnePortOperatorMoments` (at `r = 1`) and `PassiveSourceMixingContract`
(`oneStepFluctuation` at exponents `2` and `r + 2`). -/
theorem clockLayerHigherLogistic_of (hLog : ClockLayerLogistic) (ha : OnePortPassiveMean)
    (hb : OnePortOperatorMoments) (hPSM : PassiveSourceMixingContract) :
    ClockLayerHigherLogistic := by
  intro b hb0 hb' E hE hE' p r hp hp' hr hpr s hs
  obtain ⟨CL, cL, dL, WL, hCL, hcL, hdL, hLogW⟩ := hLog b hb0 hb' E hE hE' p hp hp' s hs
  obtain ⟨Ca, da, Wa, hCa, hda, haW⟩ := ha b hb0 hb' E hE hE' s hs
  obtain ⟨db, hdb, hbr⟩ := hb b hb0 hb' E hE hE' s hs
  obtain ⟨CU, Wb, hbU⟩ := hbr 1
  obtain ⟨C2, W2, hfl2⟩ := hPSM.oneStepFluctuation b hb0 hb' E hE hE' 2 (by norm_num)
  obtain ⟨Cq, Wq, hflq⟩ := hPSM.oneStepFluctuation b hb0 hb' E hE hE' (r + 2) (by linarith)
  set d := min (min dL da) db with hd
  have hd0 : 0 < d := lt_min (lt_min hdL hda) hdb
  refine ⟨rhc_layerC p r CL cL Ca (max C2 0) (max Cq 0) d, 2 ^ (1 - r) * cL / 2, d,
    max (max (max WL Wa) (max Wb W2)) (max Wq 1),
    rhc_layerC_nonneg hp.le hr hCL hcL hd0.le (le_max_right _ _),
    by have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 - r); positivity, hd0,
    fun W hW X hX A hA => ?_⟩
  have hWL : WL ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hW
  have hWa : Wa ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hW
  have hWb : Wb ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hW
  have hW2 : W2 ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hW
  have hWq : Wq ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW1 : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hXL := hX.mono ((min_le_left _ _).trans (min_le_left _ _))
  have hXa := hX.mono ((min_le_left _ _).trans (min_le_right _ _))
  have hXb := hX.mono (min_le_right _ _)
  have hlog := hLogW W hWL X hXL A hA
  obtain ⟨_, hmean⟩ := haW W hWa X hXa
  have hL2 : ∫⁻ ν, ENNReal.ofReal (‖freshL b E X ν‖ ^ 2) ∂freshLaw W b ≤ ENNReal.ofReal CU := by
    simpa using hbU W hWb X hXb
  have hf2 : ∀ u v : Fin W → ℂ, eLpNorm (fun ν => bilinear u (freshU b E X ν -
      matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal (max C2 0 / Real.sqrt W * vecNorm u * vecNorm v) := fun u v =>
    ((hfl2 W hW2 X hX.1 u v).1).trans (ENNReal.ofReal_le_ofReal (by
      have := Real.sqrt_nonneg (W : ℝ)
      have hu := Real.sqrt_nonneg (∑ i, ‖u i‖ ^ 2)
      have hv := Real.sqrt_nonneg (∑ i, ‖v i‖ ^ 2)
      unfold vecNorm
      gcongr; exact le_max_left _ _))
  have hfq : ∀ u v : Fin W → ℂ, eLpNorm (fun ν => bilinear u (freshU b E X ν -
      matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal (r + 2)) (freshLaw W b) ≤
      ENNReal.ofReal (max Cq 0 / Real.sqrt W * vecNorm u * vecNorm v) := fun u v =>
    ((hflq W hWq X hX.1 u v).1).trans (ENNReal.ofReal_le_ofReal (by
      have := Real.sqrt_nonneg (W : ℝ)
      have hu := Real.sqrt_nonneg (∑ i, ‖u i‖ ^ 2)
      have hv := Real.sqrt_nonneg (∑ i, ‖v i‖ ^ 2)
      unfold vecNorm
      gcongr; exact le_max_left _ _))
  exact rhc_layer_det hA hp hp' hr hpr.le hW1' hCL hcL hCa (le_max_right _ _) (le_max_right _ _)
    hd0.le hX.2.1 hlog hmean hL2 hf2 hfq

end BlockBand.Endpoints

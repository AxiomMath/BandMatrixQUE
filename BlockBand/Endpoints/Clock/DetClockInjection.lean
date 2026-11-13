module

public import BlockBand.Endpoints.Clock.CavityMeanProbMean
public import BlockBand.Endpoints.Clock.ClockMixingMeasure

/-!
# The deterministic-clock lemma, injection mean: `E Tr C₊/W = d + O(δ₀ + W⁻²)`

Setting: one fresh one-port layer `ω ~ freshLaw W b = layerLaw W b .oneBlockOnePort` at a
deterministic Hermitian old self-energy `X` (conditioning on the past; Fubini gives the
conditional form), `z = boundaryZ b E`, `η = Im z = etaZ b E`, `𝒢 = freshLayer b E X ω`,
`C₊ = 𝒢₁₂*𝒢₁₂ = freshC b E X ω`, `d = dStar b = (1-b)⁻¹`,
`δ₀ = jetDistance0 b E X = |W⁻¹ Tr (z - X)⁻¹ - a|`, `a = matchedA E`.

## Proof

* Ward identity (one sample, `𝒢⁻¹ - 𝒢⁻* = 2iη P_port`): `Im 𝒢₁₁ = -η 𝒢₁₂𝒢₁₂*`, hence
  `η Re Tr C₊ = -W Im(W⁻¹ Tr 𝒢₁₁)` (`etaZ_mul_trace_freshC`).
* Top mean: `|E W⁻¹ Tr 𝒢₁₁ - v| ≤ C W⁻²` for the cavity solution `(v, u)` of
  the cavity equations at `(e, z') = (E, z)` (`condMeanTop_large`). This is the proof of
  `condMean_large` (that lemma exports only the port half `|E h₊ - u|` of the stability
  bound `|v̄ - v| + |ū - u| ≤ C W⁻²`, here the top half `|v̄ - v|` is exported).
* Matched point: `(a, a)` is an approximate cavity pair with residuals `δ₀` and `0`
  (`-E - (1-b)a = z`, `(z - ba)⁻¹ = a`), so the deterministic stability theorem
  `cavity_stability` gives `|v - a| + |u - a| ≤ C δ₀` (`cavity_close_matched`).
* `-Im a/η = (1-b)⁻¹ = d` since `η = -(1-b) Im a`.

## Result

`injectionMean_of (GaussianAbsorptionContract)`: fixed `0 < b < 1/2`, `-2 < E < 2`; there are
`C, W₀`; for `W ≥ W₀` and every Hermitian `X`, `Re Tr C₊` is integrable and
`|E Re Tr C₊ / W - d| ≤ C (δ₀ + W⁻²)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix.Norms.L2Operator ComplexConjugate

namespace DetClockInj

open CavityMeanProb

/-!
## 1. The top mean `|E W⁻¹ Tr 𝒢₁₁ - v| ≤ C W⁻²`
-/

/-- **Top half of the conditional mean bound of the cavity-mean lemma**: the proof of
`condMean_large`, with the top component of the stability bound exported. -/
theorem condMeanTop_large (habs : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {η₀ M : ℝ} (hη : 0 < η₀) :
    ∃ (C : ℝ) (W₁ : ℕ), 0 < C ∧ ∀ (W : ℕ), 0 < W → W₁ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ (e : ℝ) (z' v u : ℂ), η₀ ≤ z'.im → ‖z'‖ ≤ M →
        IsCavityMatrixSolution X b (1 - 2 * b) e z' v u →
        ‖meqMeanA (layerLaw W b .oneBlockOnePort)
            (layerResolvent .oneBlockOnePort e z' (cavityLift X)) 0 - v‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨ε₁, CA, hε₁, hCA, habs'⟩ := habs b hb0 hb1 η₀ M hη
  obtain ⟨Cc, Wc, hCc, hcov⟩ := lct_cov_one_letter habs hb0 hb1 (η₀ := η₀) (M := M) hη
  have hc : 0 < 1 - 2 * b := by linarith
  obtain ⟨hK, hast, hy⟩ := step_pos (M := M) hb0 hη hCA.le
  set K := stepK b M CA with hKdef
  set astar := stepAstar b M CA with hastdef
  set y := stepY b η₀ M CA with hydef
  obtain ⟨Cs, hCs, hstab⟩ := cavity_stability hb0 hc hη (abs_nonneg M) hast
  set C0 : ℝ := 2 * Cc / y + b * Cc / η₀ with hC0
  have hC0n : 0 ≤ C0 := by positivity
  refine ⟨Cs * C0 + 1, max (max Wc ⌈2 / ε₁⌉₊) (⌈2 * b * Cc⌉₊ + 1), by positivity, ?_⟩
  intro W hW hWW X hX e z' v u hz hzM hsolM
  have hWc : Wc ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWW
  have hWε : ⌈2 / ε₁⌉₊ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWW
  have hWb : ⌈2 * b * Cc⌉₊ + 1 ≤ W := le_trans (le_max_right _ _) hWW
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have h2W : (2 : ℝ) ≤ ε₁ * W := by
    have h1 : 2 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWε)
    rw [div_le_iff₀ hε₁] at h1; linarith
  have hW2 : 2 * b * Cc ≤ (W : ℝ) ^ 2 := by
    have h1 : 2 * b * Cc ≤ (W : ℝ) := by
      have := Nat.le_ceil (2 * b * Cc)
      have h' : ((⌈2 * b * Cc⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hWb
      push_cast at h'; linarith
    have h1W : (1 : ℝ) ≤ W := by exact_mod_cast hW
    nlinarith
  have hz0 : 0 < z'.im := hη.trans_le hz
  -- the layer
  set Xl := cavityLift X with hXl_def
  have hXl : Xl.IsHermitian := cavityLift_isHermitian hX
  set μ := layerLaw W b LayerShape.oneBlockOnePort with hμ
  set G := layerResolvent LayerShape.oneBlockOnePort e z' Xl with hG
  obtain ⟨hinv, hmom⟩ := habs' W hW LayerShape.oneBlockOnePort Xl hXl e z' hz hzM
  have hG2 := meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) h2W)
  set gA := meqMeanA μ G with hgA
  set gP := meqMeanP μ G with hgP
  -- covariance bounds
  have hB : ∀ P Q : Matrix (LayerSite W LayerShape.oneBlockOnePort) (LayerSite W LayerShape.oneBlockOnePort) ℂ, ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 →
      ‖meqCov μ (fun ω => (W : ℂ)⁻¹ * (P * G ω).trace) (fun ω => Q * G ω)‖ ≤ Cc / (W : ℝ) ^ 2 :=
    fun P Q hP hQ => hcov W hW hWc LayerShape.oneBlockOnePort Xl hXl e z' hz hzM P Q hP hQ
  have hcovPhys : ∀ a : Fin LayerShape.oneBlockOnePort.blocks, ‖meqCov μ (fun ω => physBlockTrace (G ω) a)
      (fun ω => meqPhysProj a * G ω)‖ ≤ Cc / (W : ℝ) ^ 2 := fun a => by
    rw [lct_cov_phys_eq]; exact hB _ _ (meq_norm_physProj_le a) (meq_norm_physProj_le a)
  have hcovPort : ∀ (a : Fin LayerShape.oneBlockOnePort.blocks) (j : Fin LayerShape.oneBlockOnePort.ports), ‖meqCov μ
      (fun ω => portBlockTrace (G ω) j) (fun ω => meqPhysProj a * G ω)‖ ≤ Cc / (W : ℝ) ^ 2 :=
    fun a j => by
      rw [lct_cov_port_eq]; exact hB _ _ (meq_norm_portProj_le j) (meq_norm_physProj_le a)
  have hcovPP : ‖meqCov μ (fun ω => physBlockTrace (G ω) 0)
      (fun ω => meqPortProj 0 * G ω)‖ ≤ Cc / (W : ℝ) ^ 2 := by
    rw [lct_cov_phys_eq]; exact hB _ _ (meq_norm_physProj_le 0) (meq_norm_portProj_le 0)
  -- port equation
  have hport := meanEquation_port hW hb0.le hb1.le LayerShape.oneBlockOnePort hXl e hz0.le hinv hG2 0
  set rP : ℂ := (b : ℂ) * portBlockTrace (meqCov μ (fun ω => physBlockTrace (G ω) 0)
      (fun ω => meqPortProj 0 * G ω)) 0 with hrP
  have hport' : ((z' - (b : ℂ) * gA 0) * gP 0) = 1 + rP := by
    have h := hport
    simp only [meqPortCoef] at h
    simpa [meqInc, LayerShape.incident, hrP] using h
  have hrPn : ‖rP‖ ≤ b * Cc / (W : ℝ) ^ 2 := by
    rw [hrP, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((meq_norm_portBlockTrace_le _ _).trans hcovPP) hb0.le
  have hrP_half : ‖rP‖ ≤ 1 / 2 := by
    refine hrPn.trans ?_
    rw [div_le_iff₀ (by positivity)]; linarith
  -- bounds on `v̄`
  have hgAn : ‖gA 0‖ ≤ CA := lct_norm_meanA_le hCA.le (hmom 1 le_rfl (by linarith)) 0
  have hgAim : (gA 0).im ≤ 0 := lct_im_meanA_nonpos e hz0.le hXl 0
  have hden_im : η₀ ≤ (z' - (b : ℂ) * gA 0).im := by
    rw [CavityMean.im_sub_mul]; nlinarith
  have hden_inv : ‖(z' - (b : ℂ) * gA 0)⁻¹‖ ≤ 1 / η₀ := CavityMean.norm_inv_le_of_im hη hden_im
  have hden_le : ‖z' - (b : ℂ) * gA 0‖ ≤ K := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le, hKdef, stepK]
    have := le_abs_self M
    nlinarith
  -- port lower bound `|ū| ≥ a_*`
  have hgP_ge : astar ≤ ‖gP 0‖ := by
    have h1 : 1 / 2 ≤ ‖z' - (b : ℂ) * gA 0‖ * ‖gP 0‖ := by
      rw [← norm_mul, hport']
      have h' : ‖(1 : ℂ)‖ ≤ ‖1 + rP‖ + ‖rP‖ := by
        calc ‖(1 : ℂ)‖ = ‖(1 + rP) + -rP‖ := by ring_nf
          _ ≤ ‖1 + rP‖ + ‖-rP‖ := norm_add_le _ _
          _ = ‖1 + rP‖ + ‖rP‖ := by rw [norm_neg]
      rw [norm_one] at h'
      linarith
    have h2 : 1 / 2 ≤ K * ‖gP 0‖ :=
      h1.trans (mul_le_mul_of_nonneg_right hden_le (norm_nonneg _))
    rw [hastdef, stepAstar, ← hKdef, div_le_iff₀ (by positivity)]
    linarith
  -- port Ward bound
  have hEh : (∫ ω, cavityHplus e X z' ω ∂μ) = gP 0 := by
    rw [hgP, meqMeanP]
    exact integral_congr_ae (ae_cavityHplus_eq_portBlockTrace hb1 e X z')
  have hward : η₀ * ‖gP 0‖ ^ 2 ≤ -(gP 0).im := by
    have h := cavityHplus_mean_ward hW b e hX hz0
    rw [hEh] at h
    exact le_trans (mul_le_mul_of_nonneg_right hz (sq_nonneg _)) h
  -- the top matrix
  set s : ℂ := ((1 - 2 * (b : ℂ)) * gA 0 + (b : ℂ) * gP 0) with hs
  have hs_im : y ≤ -s.im := by
    have : -s.im = (1 - 2 * b) * (-(gA 0).im) + b * (-(gP 0).im) := by
      rw [hs]; simp; ring
    rw [this, hydef, stepY]
    have h1 : 0 ≤ (1 - 2 * b) * (-(gA 0).im) := mul_nonneg hc.le (by linarith)
    have h2 : b * η₀ * astar ^ 2 ≤ b * (-(gP 0).im) := by
      have : η₀ * astar ^ 2 ≤ η₀ * ‖gP 0‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hast.le hgP_ge 2) hη.le
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (this.trans hward) hb0.le
    linarith
  set H : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ := -(e : ℂ) • 1 - Xl with hH
  have hHh : H.IsHermitian := by
    refine Matrix.IsHermitian.sub ?_ hXl
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_neg, Complex.star_def,
      Complex.conj_ofReal]
  have hTeq : meqTop LayerShape.oneBlockOnePort e Xl (1 - 2 * (b : ℂ)) b gA gP = H - diagonal (fun _ => s) :=
    meqTop_oneBlock e X _ _ gA gP
  have hσ' : ∀ p : Fin 1 × Fin W, ((fun _ => s) p).im < 0 := fun _ => by
    simp only; linarith
  have hT : IsUnit (meqTop LayerShape.oneBlockOnePort e Xl (1 - 2 * (b : ℂ)) b gA gP).det := by
    rw [hTeq]; exact isUnit_iff_ne_zero.mpr (cmp_det_ne_zero H hHh _ hσ')
  have hTinv : ‖(meqTop LayerShape.oneBlockOnePort e Xl (1 - 2 * (b : ℂ)) b gA gP)⁻¹‖ ≤ y⁻¹ := by
    rw [hTeq]; exact lct_norm_shifted_inv_le H hHh _ hy fun _ => hs_im
  have htop := meanEquation_top hW hb0.le hb1.le LayerShape.oneBlockOnePort hXl e hz0.le hinv hG2 hT 0
  have hR : ‖meqResidTop μ (1 - 2 * (b : ℂ)) b G‖ ≤ 2 * (Cc / (W : ℝ) ^ 2) := by
    have h := lct_norm_residTop_le μ hb0.le hb1.le G hcovPhys hcovPort
    simp only [LayerShape.blocks, LayerShape.ports] at h
    norm_num at h
    linarith
  have hζ : ((-(e : ℂ) - s) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) - cavityLift X) =
      meqTop LayerShape.oneBlockOnePort e Xl (1 - 2 * (b : ℂ)) b gA gP := by
    rw [hTeq, hH, meqTop_oneBlock_eq_shift]
  have hζim : 0 < (-(e : ℂ) - s).im := by
    have : (-(e : ℂ) - s).im = -s.im := by simp
    rw [this]; linarith
  have hfirst : blockTrace (meqTop LayerShape.oneBlockOnePort e Xl (1 - 2 * (b : ℂ)) b gA gP)⁻¹ 0 =
      cavityStieltjes (fun _ => (W : ℝ)⁻¹) hX.eigenvalues
        (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * gA 0 - (b : ℂ) * gP 0) := by
    have hζs : (-(e : ℂ) - s) =
        (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * gA 0 - (b : ℂ) * gP 0) := by
      rw [hs]; push_cast; ring
    rw [← hζ, cavity_blockTrace_lift_inv, normalizedResolventTrace_eq hX hζim.ne', hζs]
  -- residuals
  have hε1 : ‖gA 0 - cavityStieltjes (fun _ => (W : ℝ)⁻¹) hX.eigenvalues
      (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * gA 0 - (b : ℂ) * gP 0)‖ ≤ C0 / (W : ℝ) ^ 2 := by
    have h := htop
    rw [hfirst] at h
    have hdiff : gA 0 - cavityStieltjes (fun _ => (W : ℝ)⁻¹) hX.eigenvalues
        (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * gA 0 - (b : ℂ) * gP 0) =
        blockTrace ((meqTop LayerShape.oneBlockOnePort e Xl (1 - 2 * (b : ℂ)) b gA gP)⁻¹ *
          meqResidTop μ (1 - 2 * (b : ℂ)) b G) 0 := by
      rw [sub_eq_iff_eq_add']; exact h
    rw [hdiff]
    refine (lct_norm_blockTrace_le _ _).trans ((norm_mul_le _ _).trans ?_)
    calc ‖(meqTop LayerShape.oneBlockOnePort e Xl (1 - 2 * (b : ℂ)) b gA gP)⁻¹‖ * ‖meqResidTop μ (1 - 2 * (b : ℂ)) b G‖
        ≤ y⁻¹ * (2 * (Cc / (W : ℝ) ^ 2)) :=
          mul_le_mul hTinv hR (norm_nonneg _) (by positivity)
      _ ≤ C0 / (W : ℝ) ^ 2 := by
          rw [hC0, add_div]
          have : 0 ≤ b * Cc / η₀ / (W : ℝ) ^ 2 := by positivity
          have e1 : y⁻¹ * (2 * (Cc / (W : ℝ) ^ 2)) = 2 * Cc / y / (W : ℝ) ^ 2 := by
            field_simp
          linarith
  have hε2 : ‖gP 0 - (z' - (b : ℂ) * gA 0)⁻¹‖ ≤ C0 / (W : ℝ) ^ 2 := by
    have hne : z' - (b : ℂ) * gA 0 ≠ 0 :=
      CavityMean.ne_zero_of_im_pos (hη.trans_le hden_im)
    have hdiff : gP 0 - (z' - (b : ℂ) * gA 0)⁻¹ = (z' - (b : ℂ) * gA 0)⁻¹ * rP := by
      have h1 : gP 0 = (z' - (b : ℂ) * gA 0)⁻¹ * (1 + rP) := by
        rw [← hport', ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      rw [h1]; ring
    rw [hdiff, norm_mul]
    calc ‖(z' - (b : ℂ) * gA 0)⁻¹‖ * ‖rP‖ ≤ 1 / η₀ * (b * Cc / (W : ℝ) ^ 2) :=
          mul_le_mul hden_inv hrPn (norm_nonneg _) (by positivity)
      _ ≤ C0 / (W : ℝ) ^ 2 := by
          rw [hC0, add_div]
          have : 0 ≤ 2 * Cc / y / (W : ℝ) ^ 2 := by positivity
          have e1 : 1 / η₀ * (b * Cc / (W : ℝ) ^ 2) = b * Cc / η₀ / (W : ℝ) ^ 2 := by
            field_simp
          linarith
  -- stability of the cavity solution
  have hsol := (isCavityMatrixSolution_iff hX hb0 hc).mp hsolM
  have hfin := hstab (Fin W) (fun _ => (W : ℝ)⁻¹) hX.eigenvalues e z' v u (gA 0) (gP 0)
    (C0 / (W : ℝ) ^ 2) (isCavityWeights_uniform hW) hz (hzM.trans (le_abs_self M)) hsol hgAim
    hgP_ge hward hε1 hε2
  calc ‖gA 0 - v‖ ≤ ‖gA 0 - v‖ + ‖gP 0 - u‖ := le_add_of_nonneg_right (norm_nonneg _)
    _ ≤ Cs * (C0 / (W : ℝ) ^ 2) := hfin
    _ ≤ (Cs * C0 + 1) / (W : ℝ) ^ 2 := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]; linarith

/-!
## 2. The Ward identity of one sample
-/

/-- `H⁻¹ - H⁻* = H⁻¹ (H* - H) H⁻*` for invertible `H`. -/
theorem inv_sub_conjTranspose_inv {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hH : IsUnit H.det) : H⁻¹ - (H⁻¹)ᴴ = H⁻¹ * (Hᴴ - H) * (H⁻¹)ᴴ := by
  have h2 : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hH
  have h3 : Hᴴ * (H⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, h2, Matrix.one_mul, Matrix.mul_assoc, h3, Matrix.mul_one]

/-- The port weight `diag(0, c I)` of the layer sites. -/
def portWeight (W : ℕ) (c : ℂ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  Matrix.fromBlocks 0 0 0 (c • (1 : Matrix (PortSite W .oneBlockOnePort)
    (PortSite W .oneBlockOnePort) ℂ))

/-- `𝒢⁻* - 𝒢⁻¹ = diag(0, (z̄ - z) I)` for a Hermitian top block. -/
theorem layerMatrix_conjTranspose_sub {W : ℕ} (E : ℝ) (z : ℂ)
    {X : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ}
    (hX : X.IsHermitian) (ω : LayerSample W .oneBlockOnePort) (hA : ∀ j, (ω.1 j).IsHermitian) :
    (layerMatrix .oneBlockOnePort E z X ω)ᴴ - layerMatrix .oneBlockOnePort E z X ω =
      portWeight W (conj z - z) := by
  have hT := lct_top_isHermitian (σ := .oneBlockOnePort) E hX hA
  unfold layerMatrix portWeight
  rw [Matrix.fromBlocks_conjTranspose, conjTranspose_conjTranspose, hT.eq]
  ext (i | i) (j | j)
  · simp
  · simp
  · simp
  · by_cases h : i = j
    · subst h; simp
    · simp [h]

/-- `(G diag(0, cI) G*)_{ii} = c Σ_y |G_{i,y}|²`. -/
theorem entry_portWeight {W : ℕ}
    (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) (c : ℂ)
    (i : LayerSite W .oneBlockOnePort) :
    (G * portWeight W c * Gᴴ) i i =
      c * ((∑ y : PortSite W .oneBlockOnePort, ‖G i (Sum.inr y)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [portWeight, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, conjTranspose_apply, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [RCLike.star_def]
  linear_combination c * Complex.mul_conj' (G i (Sum.inr y))

/-- **Ward identity on the top diagonal**: `Im 𝒢_{xx} = -η Σ_y |(𝒢₁₂)_{xy}|²`. -/
theorem im_freshLayer_diag {W : ℕ} (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) (ω : LayerSample W .oneBlockOnePort) (hA : ∀ j, (ω.1 j).IsHermitian)
    (hH : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω).det) (x : Fin W) :
    (freshLayer b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inl ((0 : Fin 1), x))).im =
      -etaZ b E * ∑ y : Fin W,
        ‖freshLayer b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))‖ ^ 2 := by
  set H := layerMatrix .oneBlockOnePort E (boundaryZ b E)
    (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω with hHdef
  have hXl : (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2).IsHermitian :=
    ClockMixingAlg.physEmbed_isHermitian hX
  have hW := inv_sub_conjTranspose_inv H hH
  rw [layerMatrix_conjTranspose_sub E _ hXl ω hA] at hW
  have he := congrFun (congrFun hW (Sum.inl ((0 : Fin 1), x))) (Sum.inl ((0 : Fin 1), x))
  rw [entry_portWeight] at he
  have hG : freshLayer b E X ω = H⁻¹ := rfl
  rw [hG]
  set g := H⁻¹ (Sum.inl ((0 : Fin 1), x)) (Sum.inl ((0 : Fin 1), x))
  set r : ℝ := ∑ y : PortSite W .oneBlockOnePort,
    ‖H⁻¹ (Sum.inl ((0 : Fin 1), x)) (Sum.inr y)‖ ^ 2 with hr
  have he' : g - star g = (conj (boundaryZ b E) - boundaryZ b E) * (r : ℂ) := by
    rw [← he]; simp [g, conjTranspose_apply]
  have him := congrArg Complex.im he'
  simp only [Complex.sub_im, RCLike.star_def, Complex.conj_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero] at him
  have hr' : r = ∑ y : Fin W, ‖H⁻¹ (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))‖ ^ 2 := by
    rw [hr, Fintype.sum_prod_type, Fin.sum_univ_one]
  rw [← hr']
  unfold etaZ
  linarith

/-- `Re Tr C₊ = Σ_{x,y} |(𝒢₁₂)_{xy}|²`. -/
theorem trace_freshC_eq_sum {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    (freshC b E X ω).trace.re = ∑ x : Fin W, ∑ y : Fin W,
      ‖freshLayer b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))‖ ^ 2 := by
  set G := freshLayer b E X ω
  have htr : (freshC b E X ω).trace.re =
      ∑ y : Fin W, ∑ x : Fin W, ‖G (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))‖ ^ 2 := by
    unfold freshC freshG12
    simp only [trace, diag_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm]
  rw [htr, Finset.sum_comm]

/-- **The Ward identity for the injection** (one sample, a.s.):
`η Re Tr C₊ = -W Im(W⁻¹ Tr 𝒢₁₁)`. -/
theorem etaZ_mul_trace_freshC {W : ℕ} (hW : 0 < W) (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) (ω : LayerSample W .oneBlockOnePort) (hA : ∀ j, (ω.1 j).IsHermitian)
    (hH : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω).det) :
    etaZ b E * (freshC b E X ω).trace.re =
      -(W : ℝ) * (physBlockTrace (freshLayer b E X ω) 0).im := by
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hpb : (physBlockTrace (freshLayer b E X ω) 0).im = (W : ℝ)⁻¹ *
      ∑ x : Fin W, (freshLayer b E X ω (Sum.inl ((0 : Fin 1), x))
        (Sum.inl ((0 : Fin 1), x))).im := by
    unfold physBlockTrace
    have h : ((W : ℂ))⁻¹ = (((W : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h, Complex.im_ofReal_mul, Complex.im_sum]
  rw [hpb, trace_freshC_eq_sum]
  simp only [im_freshLayer_diag b E hX ω hA hH]
  rw [← Finset.mul_sum, Finset.mul_sum]
  field_simp
  rw [Finset.mul_sum]

/-!
## 3. The cavity solution at the matched point
-/

/-- `η = Im z > 0` and `Im z = -(1-b) Im a` in the bulk. -/
theorem etaZ_pos {b E : ℝ} (hb1 : b < 1) (hE0 : -2 < E) (hE1 : E < 2) : 0 < etaZ b E := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have ha := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
  unfold etaZ
  rw [BlockBand.Layers.boundaryZ_im hE]
  have : 0 < 1 - b := by linarith
  nlinarith

/-- **The cavity solution is `O(δ₀)`-close to the matched point** (deterministic):
`(a, a)` is an approximate solution of the cavity equations at `(e, z') = (E, z_∂)` with
residuals `δ₀` and `0`, so `cavity_stability` gives `|a - v| + |a - u| ≤ C δ₀`. -/
theorem cavity_close_matched {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E)
    (hE1 : E < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ v u : ℂ, IsCavityMatrixSolution X b (1 - 2 * b) E (boundaryZ b E) v u →
        ‖matchedA E - v‖ + ‖matchedA E - u‖ ≤ C * jetDistance0 b E X := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hc : 0 < 1 - 2 * b := by linarith
  have hη := etaZ_pos (by linarith : b < 1) hE0 hE1
  obtain ⟨C, hC, hstab⟩ := cavity_stability hb0 hc hη (norm_nonneg (boundaryZ b E))
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨C, hC, fun W hW X hX v u hsol => ?_⟩
  have hsol' := (isCavityMatrixSolution_iff hX hb0 hc).mp hsol
  have ha1 : ‖matchedA E‖ = 1 := BlockBand.Layers.norm_matchedA hE
  have haim := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
  have hzim : (boundaryZ b E).im = -(1 - b) * (matchedA E).im := BlockBand.Layers.boundaryZ_im hE
  have hzeq : -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E - (b : ℂ) * matchedA E =
      boundaryZ b E := by
    rw [BlockBand.Layers.boundaryZ_eq hE]; push_cast; ring
  have ha0 : matchedA E ≠ 0 := by
    intro h; rw [h, norm_zero] at ha1; norm_num at ha1
  have hres1 : ‖matchedA E - cavityStieltjes (fun _ => (W : ℝ)⁻¹) hX.eigenvalues
      (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E - (b : ℂ) * matchedA E)‖ ≤
      jetDistance0 b E X := by
    rw [hzeq, ← normalizedResolventTrace_eq hX hη.ne', norm_sub_rev]
    exact le_rfl
  have hres2 : ‖matchedA E - (boundaryZ b E - (b : ℂ) * matchedA E)⁻¹‖ ≤ jetDistance0 b E X := by
    have : boundaryZ b E - (b : ℂ) * matchedA E = (matchedA E)⁻¹ := by unfold boundaryZ; ring
    rw [this, inv_inv, sub_self, norm_zero]
    exact norm_nonneg _
  have hport : etaZ b E * ‖matchedA E‖ ^ 2 ≤ -(matchedA E).im := by
    rw [ha1, one_pow, mul_one]
    unfold etaZ; rw [hzim]; nlinarith
  have h := hstab (Fin W) (fun _ => (W : ℝ)⁻¹) hX.eigenvalues E (boundaryZ b E) v u
    (matchedA E) (matchedA E) (jetDistance0 b E X) (isCavityWeights_uniform hW) le_rfl le_rfl
    hsol' haim.le (by rw [ha1]) hport hres1 hres2
  exact h

/-!
## 4. The injection mean
-/

/-- **Injection mean**: fixed `0 < b < 1/2`, `-2 < E < 2`; there are `C, W₀` such that for
`W ≥ W₀` and every deterministic Hermitian `X` (the past), with one fresh layer `ω ~ freshLaw W b`:
`Re Tr C₊` is integrable and `|E Re Tr C₊ / W - d| ≤ C (δ₀ + W⁻²)`, `d = (1-b)⁻¹`,
`δ₀ = jetDistance0 b E X`.
Hypothesis: `GaussianAbsorptionContract`.
-/
theorem injectionMean_of (habs : GaussianAbsorptionContract) {b E : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      Integrable (fun ω => (freshC b E X ω).trace.re) (freshLaw W b) ∧
      |(∫ ω, (freshC b E X ω).trace.re ∂freshLaw W b) / W - dStar b| ≤
        C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hc : 0 < 1 - 2 * b := by linarith
  have hη := etaZ_pos (by linarith : b < 1) hE0 hE1
  set z := boundaryZ b E with hz
  set η := etaZ b E with hηdef
  obtain ⟨C₁, W₁, hC₁, htop⟩ := condMeanTop_large habs hb0 hb1 (M := ‖z‖) hη
  obtain ⟨C₂, hC₂, hclose⟩ := cavity_close_matched hb0 hb1 hE0 hE1
  obtain ⟨ε₁, CA, hε₁, _hCA, habs'⟩ := habs b hb0 hb1 η ‖z‖ hη
  refine ⟨(C₁ + C₂) / η, max (max W₁ ⌈2 / ε₁⌉₊) 1, fun W hWW X hX => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWW
  have hWε : ⌈2 / ε₁⌉₊ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWW
  have hW : 0 < W := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hWW)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have h2W : (2 : ℝ) ≤ ε₁ * W := by
    have h1 : 2 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWε)
    rw [div_le_iff₀ hε₁] at h1; linarith
  have hXl := cavityLift_isHermitian hX
  set μ := layerLaw W b LayerShape.oneBlockOnePort with hμ
  set G := layerResolvent LayerShape.oneBlockOnePort E z (cavityLift X) with hG
  have hGf : ∀ ω, freshLayer b E X ω = G ω := fun ω => rfl
  obtain ⟨hinv, hmom⟩ := habs' W hW LayerShape.oneBlockOnePort (cavityLift X) hXl E z le_rfl le_rfl
  have hG2 := meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) h2W)
  have hGm : Measurable G := measurable_layerResolvent _ _ _ _
  have hGn : Integrable (fun ω => ‖G ω‖) μ := meq_integrable_norm_of_sq hGm.aestronglyMeasurable hG2
  -- measurability and integrability of `Re Tr C₊`
  have hCm0 : Measurable (fun ω : LayerSample W .oneBlockOnePort => freshC b E X ω) :=
    (ClockMixingProb.meas_freshC (W := W) b E).comp (f := fun ω => (X, ω))
      (measurable_const.prodMk measurable_id)
  have hCm : Measurable (fun ω => (freshC b E X ω).trace.re) :=
    Complex.measurable_re.comp (ClockMixingProb.meas_trace hCm0)
  have hCi : Integrable (fun ω => (freshC b E X ω).trace.re) μ := by
    refine Integrable.mono' (hG2.const_mul (W : ℝ)) hCm.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have h0 : 0 ≤ (freshC b E X ω).trace.re := by
      rw [trace_freshC_eq_sum]; positivity
    rw [Real.norm_of_nonneg h0]
    exact ClockMixingAlg.trace_freshC_le b E X ω
  refine ⟨hCi, ?_⟩
  -- the Ward identity, almost surely
  have hae : ∀ᵐ ω ∂μ, (freshC b E X ω).trace.re =
      -((W : ℝ) / η) * (physBlockTrace (G ω) 0).im := by
    filter_upwards [lct_ae_blocks_isHermitian W b LayerShape.oneBlockOnePort, hinv] with ω hA hH
    have h := etaZ_mul_trace_freshC hW b E hX ω hA hH
    rw [hGf] at h
    field_simp
    linarith
  have hPi : Integrable (fun ω => physBlockTrace (G ω) 0) μ :=
    Integrable.mono' hGn ((meq_continuous_physBlockTrace 0).measurable.comp hGm).aestronglyMeasurable
      (ae_of_all _ fun ω => meq_norm_physBlockTrace_le _ _)
  have hint : (∫ ω, (freshC b E X ω).trace.re ∂μ) =
      -((W : ℝ) / η) * (meqMeanA μ G 0).im := by
    rw [integral_congr_ae hae, integral_const_mul, meqMeanA]
    congr 1
    have h1 := Complex.imCLM.integral_comp_comm hPi
    simp only [Complex.imCLM_apply] at h1
    exact h1
  -- the deterministic comparison
  obtain ⟨vu, hsol, -⟩ := cavityMatrix_existsUnique hW hX hb0 hc (z' := z) hη
  have h1 : ‖meqMeanA μ G 0 - vu.1‖ ≤ C₁ / (W : ℝ) ^ 2 :=
    htop W hW hW1 X hX E z vu.1 vu.2 le_rfl le_rfl hsol
  have h2 : ‖matchedA E - vu.1‖ + ‖matchedA E - vu.2‖ ≤ C₂ * jetDistance0 b E X :=
    hclose W hW X hX vu.1 vu.2 hsol
  have hd : dStar b = -(1 / η) * (matchedA E).im := by
    have hzim : η = -(1 - b) * (matchedA E).im := BlockBand.Layers.boundaryZ_im hE
    have haim := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
    have h1b : (1 - b) ≠ 0 := by linarith
    unfold dStar
    rw [hzim]
    field_simp
    rw [div_self haim.ne]
  have hkey : (∫ ω, (freshC b E X ω).trace.re ∂μ) / W - dStar b =
      -(1 / η) * (meqMeanA μ G 0 - matchedA E).im := by
    rw [hint, hd, Complex.sub_im]
    field_simp
    ring
  change |(∫ ω, (freshC b E X ω).trace.re ∂μ) / W - dStar b| ≤ _
  rw [hkey, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / η)]
  have him : |(meqMeanA μ G 0 - matchedA E).im| ≤ ‖meqMeanA μ G 0 - vu.1‖ + ‖matchedA E - vu.1‖ := by
    refine (Complex.abs_im_le_norm _).trans ?_
    calc ‖meqMeanA μ G 0 - matchedA E‖ = ‖(meqMeanA μ G 0 - vu.1) - (matchedA E - vu.1)‖ := by
          congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hWinv : C₁ / (W : ℝ) ^ 2 = C₁ * ((W : ℝ)⁻¹) ^ 2 := by field_simp
  calc 1 / η * |(meqMeanA μ G 0 - matchedA E).im|
      ≤ 1 / η * (C₁ * ((W : ℝ)⁻¹) ^ 2 + C₂ * jetDistance0 b E X) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : ‖matchedA E - vu.1‖ ≤ C₂ * jetDistance0 b E X := by
          linarith [norm_nonneg (matchedA E - vu.2)]
        linarith
    _ ≤ (C₁ + C₂) / η * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right hη]
        have : 0 ≤ ((W : ℝ)⁻¹) ^ 2 := by positivity
        nlinarith

end DetClockInj

end BlockBand.Endpoints.Clock

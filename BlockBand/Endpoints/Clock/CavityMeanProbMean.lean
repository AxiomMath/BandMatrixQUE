module

public import BlockBand.Endpoints.Clock.CavityMeanProbSchur

/-!
# The cavity-mean lemma (ii): the conditional mean `|E(h₊(z') | X) - u| ≤ C W⁻²`

The expectation is over `layerLaw W b .oneBlockOnePort`, i.e. conditional on the deterministic
Hermitian `X`, and `c = 1 - 2b`. The constant `C` depends only on `b, η₀, M`; it is uniform in
`W ≥ 1`, Hermitian `X`, real `e`, and `z'` with `Im z' ≥ η₀`, `|z'| ≤ M`.

Proof.
* Step 1. The exact Gaussian mean equations (`meanEquation_port`, `meanEquation_top`, valid for
  every shape, here one block and one port) give, with `v̄ = E W⁻¹Tr 𝒢_phys`,
  `ū = E W⁻¹Tr 𝒢_port = E h₊`: `(z' - b v̄) ū = 1 + b·Cov-term` and
  `v̄ = W⁻¹Tr(-e - X - c v̄ - b ū)⁻¹ + W⁻¹Tr(M̄ R_phys)`. The covariance terms are `O(W⁻²)`
  (`lct_cov_one_letter`, from `GaussianAbsorptionContract`). The inverse moment `E‖𝒢‖ ≤ C_A` gives
  `|v̄| ≤ C_A`, hence `|ū| ≥ a_* = (2(|M| + b C_A + 1))⁻¹`; the Ward identity
  (`cavityHplus_port_ward` and Jensen) gives `-Im ū ≥ η₀ |ū|²`; so the top matrix has
  `-Im(c v̄ + b ū) ≥ b η₀ a_*²` and a bounded inverse.
* Step 5. The deterministic stability theorem `cavity_stability` turns the residuals `O(W⁻²)`
  into `|v̄ - v| + |ū - u| ≤ C W⁻²`.
* Small `W` (below the threshold `W₁` of the moment and covariance bounds): `|E h₊| ≤ η₀⁻¹` and
  `|u| ≤ η₀⁻¹` deterministically, so the bound holds with `C ≥ 2 W₁² / η₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Layers
open BlockBand.Internal.Contracts.TransmissionStatements (freshSchur)
open scoped Matrix.Norms.L2Operator ComplexConjugate

namespace CavityMeanProb

/-- Jensen: `|E h|² ≤ E|h|²` for a probability measure. -/
theorem norm_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {h : Ω → ℂ} (hi : Integrable h μ)
    (hi2 : Integrable (fun ω => ‖h ω‖ ^ 2) μ) :
    ‖∫ ω, h ω ∂μ‖ ^ 2 ≤ ∫ ω, ‖h ω‖ ^ 2 ∂μ := by
  set m := ∫ ω, h ω ∂μ with hm
  have key : ∀ ω, 2 * (h ω * conj m).re ≤ ‖h ω‖ ^ 2 + ‖m‖ ^ 2 := by
    intro ω
    have h0 := Complex.normSq_nonneg (h ω - m)
    rw [Complex.normSq_sub] at h0
    rw [Complex.sq_norm, Complex.sq_norm]
    linarith
  have hint : Integrable (fun ω => h ω * conj m) μ := hi.mul_const _
  have hre : ∫ ω, (h ω * conj m).re ∂μ = ‖m‖ ^ 2 := by
    have h1 := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at h1
    rw [h1, integral_mul_const, ← hm, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hmono : ∫ ω, 2 * (h ω * conj m).re ∂μ ≤ ∫ ω, (‖h ω‖ ^ 2 + ‖m‖ ^ 2) ∂μ :=
    integral_mono (hint.re.const_mul 2) (hi2.add (integrable_const _)) key
  rw [integral_const_mul, hre, integral_add hi2 (integrable_const _), integral_const,
    probReal_univ, one_smul] at hmono
  linarith

theorem integrable_cavityHplus {W : ℕ} (hW : 0 < W) (b e : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) {z' : ℂ} (hz : 0 < z'.im) :
    Integrable (fun ω => cavityHplus e X z' ω) (layerLaw W b .oneBlockOnePort) := by
  refine Integrable.of_bound (measurable_cavityHplus e X z').aestronglyMeasurable (1 / z'.im) ?_
  filter_upwards [ae_freshSchur_isHermitian W b e hX] with ω hω
  exact norm_cavityHplus_le hW e hω hz

/-- The conditional mean of `h₊` is bounded by `(Im z')⁻¹`. -/
theorem norm_integral_cavityHplus_le {W : ℕ} (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) {z' : ℂ} (hz : 0 < z'.im) :
    ‖∫ ω, cavityHplus e X z' ω ∂layerLaw W b .oneBlockOnePort‖ ≤ 1 / z'.im := by
  have h := norm_integral_le_of_norm_le_const (μ := layerLaw W b .oneBlockOnePort)
    (f := fun ω => cavityHplus e X z' ω) (C := 1 / z'.im) (by
      filter_upwards [ae_freshSchur_isHermitian W b e hX] with ω hω
      exact norm_cavityHplus_le hW e hω hz)
  rwa [probReal_univ, mul_one] at h

/-- **Ward identity for the mean**: `-Im E h₊ ≥ Im z' |E h₊|²`. -/
theorem cavityHplus_mean_ward {W : ℕ} (hW : 0 < W) (b e : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) {z' : ℂ} (hz : 0 < z'.im) :
    z'.im * ‖∫ ω, cavityHplus e X z' ω ∂layerLaw W b .oneBlockOnePort‖ ^ 2 ≤
      -(∫ ω, cavityHplus e X z' ω ∂layerLaw W b .oneBlockOnePort).im := by
  set μ := layerLaw W b .oneBlockOnePort
  have hi := integrable_cavityHplus hW b e hX hz
  have hi2 : Integrable (fun ω => ‖cavityHplus e X z' ω‖ ^ 2) μ := by
    refine Integrable.of_bound ((measurable_cavityHplus e X z').norm.pow_const 2).aestronglyMeasurable
      ((1 / z'.im) ^ 2) ?_
    filter_upwards [ae_freshSchur_isHermitian W b e hX] with ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_cavityHplus_le hW e hω hz) 2
  have hJ := norm_integral_sq_le hi hi2
  have him : (∫ ω, cavityHplus e X z' ω ∂μ).im = ∫ ω, (cavityHplus e X z' ω).im ∂μ := by
    have h1 := Complex.imCLM.integral_comp_comm hi
    simp only [Complex.imCLM_apply] at h1
    exact h1.symm
  have hmono : ∫ ω, z'.im * ‖cavityHplus e X z' ω‖ ^ 2 ∂μ ≤
      ∫ ω, -(cavityHplus e X z' ω).im ∂μ := by
    refine integral_mono_ae (hi2.const_mul _) hi.im.neg ?_
    filter_upwards [ae_freshSchur_isHermitian W b e hX] with ω hω
    exact cavityHplus_port_ward hW e hω hz
  rw [integral_const_mul, integral_neg, ← him] at hmono
  nlinarith

/-!
## Step 1 at large `W`
-/

/-- Constants of Step 1: `a_* = (2K)⁻¹`, `K = |M| + b C_A + 1`, `y = b η₀ a_*²`. -/
def stepK (b M CA : ℝ) : ℝ := |M| + b * CA + 1

/-- The port lower bound `a_*`. -/
def stepAstar (b M CA : ℝ) : ℝ := 1 / (2 * stepK b M CA)

/-- The top-matrix gap `y`. -/
def stepY (b η M CA : ℝ) : ℝ := b * η * stepAstar b M CA ^ 2

theorem step_pos {b η M CA : ℝ} (hb : 0 < b) (hη : 0 < η) (hCA : 0 ≤ CA) :
    0 < stepK b M CA ∧ 0 < stepAstar b M CA ∧ 0 < stepY b η M CA := by
  have hK : 0 < stepK b M CA := by
    unfold stepK; have := abs_nonneg M; positivity
  have ha : 0 < stepAstar b M CA := by unfold stepAstar; positivity
  exact ⟨hK, ha, by unfold stepY; positivity⟩

theorem sum_fin_one {f : Fin 1 → ℂ} : ∑ j : Fin 1, f j = f 0 := Fin.sum_univ_one f

/-- The top matrix of the one-block layer is `ζ - X` with a scalar `ζ = -e - s`. -/
theorem meqTop_oneBlock {W : ℕ} (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (c b : ℂ)
    (gA : Fin LayerShape.oneBlockOnePort.blocks → ℂ) (gP : Fin LayerShape.oneBlockOnePort.ports → ℂ) :
    meqTop .oneBlockOnePort e (cavityLift X) c b gA gP =
      (-(e : ℂ) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) - cavityLift X) -
        diagonal (fun _ => c * gA 0 + b * gP 0) := by
  unfold meqTop
  have hd : (diagonal fun x : PhysSite W .oneBlockOnePort =>
      c * gA x.1 + b * ∑ j, meqInc .oneBlockOnePort x.1 j * gP j) =
      diagonal (fun _ => c * gA 0 + b * gP 0) := by
    congr 1
    funext x
    have hx : x.1 = 0 := Subsingleton.elim _ _
    rw [hx, sum_fin_one]
    simp [meqInc, LayerShape.incident]
  rw [hd, neg_smul]

theorem meqTop_oneBlock_eq_shift {W : ℕ} (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (s : ℂ) :
    (-(e : ℂ) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) - cavityLift X) -
        diagonal (fun _ => s) =
      (-(e : ℂ) - s) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) - cavityLift X := by
  ext p q
  by_cases h : p = q
  · subst h; simp; ring
  · simp [h, Matrix.one_apply_ne h]

/-- **Step 1 + Step 5 at large `W`.** -/
theorem condMean_large (habs : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {η₀ M : ℝ} (hη : 0 < η₀) :
    ∃ (C : ℝ) (W₁ : ℕ), 0 < C ∧ ∀ (W : ℕ), 0 < W → W₁ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ (e : ℝ) (z' v u : ℂ), η₀ ≤ z'.im → ‖z'‖ ≤ M →
        IsCavityMatrixSolution X b (1 - 2 * b) e z' v u →
        ‖(∫ ω, cavityHplus e X z' ω ∂layerLaw W b .oneBlockOnePort) - u‖ ≤ C / (W : ℝ) ^ 2 := by
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
  -- `E h₊ = ū`
  have hEh : (∫ ω, cavityHplus e X z' ω ∂μ) = gP 0 := by
    rw [hgP, meqMeanP]
    exact integral_congr_ae (ae_cavityHplus_eq_portBlockTrace hb1 e X z')
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
  -- Step 5
  have hsol := (isCavityMatrixSolution_iff hX hb0 hc).mp hsolM
  have hfin := hstab (Fin W) (fun _ => (W : ℝ)⁻¹) hX.eigenvalues e z' v u (gA 0) (gP 0)
    (C0 / (W : ℝ) ^ 2) (isCavityWeights_uniform hW) hz (hzM.trans (le_abs_self M)) hsol hgAim
    hgP_ge hward hε1 hε2
  rw [hEh]
  calc ‖gP 0 - u‖ ≤ ‖gA 0 - v‖ + ‖gP 0 - u‖ := le_add_of_nonneg_left (norm_nonneg _)
    _ ≤ Cs * (C0 / (W : ℝ) ^ 2) := hfin
    _ ≤ (Cs * C0 + 1) / (W : ℝ) ^ 2 := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]; linarith

/-- `|u| ≤ (Im z')⁻¹` for the exact solution of the cavity equations. -/
theorem norm_cavity_u_le {W : ℕ} {X : Matrix (Fin W) (Fin W) ℂ} {b c e : ℝ} (hb : 0 ≤ b)
    {z' v u : ℂ} (hz : 0 < z'.im) (h : IsCavityMatrixSolution X b c e z' v u) :
    ‖u‖ ≤ 1 / z'.im := by
  obtain ⟨-, hu, hv, -⟩ := h
  rw [hu]
  refine CavityMean.norm_inv_le_of_im hz ?_
  rw [CavityMean.im_sub_mul]; nlinarith

end CavityMeanProb

open CavityMeanProb

/-- **Part (ii) of the cavity-mean lemma**, from `GaussianAbsorptionContract`.
For `0 < b < 1/2` (`c = 1 - 2b`) and `η₀ > 0`, `M`
there is `C` such that for every `W ≥ 1`, every deterministic Hermitian `X` (`W × W`; this is
the conditional statement for an independent `X`), every real `e`, every `z'` with
`Im z' ≥ η₀`, `|z'| ≤ M`, and the solution `(v, u)` of the cavity equations with
negative imaginary parts (`IsCavityMatrixSolution`, unique by `cavityMatrix_existsUnique`):
`|E(h₊(z') | X) - u| ≤ C W⁻²`, the expectation over the fresh layer
`layerLaw W b.oneBlockOnePort`.
`C` depends only on `b, η₀, M`.
-/
theorem cavityMean_condMean (habs : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {η₀ M : ℝ} (hη : 0 < η₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ (e : ℝ) (z' v u : ℂ), η₀ ≤ z'.im → ‖z'‖ ≤ M →
        IsCavityMatrixSolution X b (1 - 2 * b) e z' v u →
        ‖(∫ ω, cavityHplus e X z' ω ∂layerLaw W b .oneBlockOnePort) - u‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hlarge⟩ := condMean_large habs hb0 hb1 (M := M) hη
  refine ⟨C + 2 * (W₁ : ℝ) ^ 2 / η₀, by positivity, ?_⟩
  intro W hW X hX e z' v u hz hzM hsol
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  rcases le_or_gt W₁ W with hWW | hWW
  · refine (hlarge W hW hWW X hX e z' v u hz hzM hsol).trans ?_
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have : 0 ≤ 2 * (W₁ : ℝ) ^ 2 / η₀ := by positivity
    linarith
  · have hz0 : 0 < z'.im := hη.trans_le hz
    have h1 := norm_integral_cavityHplus_le hW b e hX hz0
    have h2 := norm_cavity_u_le hb0.le hz0 hsol
    have h3 : 1 / z'.im ≤ 1 / η₀ := one_div_le_one_div_of_le hη hz
    have hW1 : (W : ℝ) ^ 2 ≤ (W₁ : ℝ) ^ 2 := by
      have : (W : ℝ) ≤ W₁ := by exact_mod_cast hWW.le
      nlinarith
    calc ‖(∫ ω, cavityHplus e X z' ω ∂layerLaw W b .oneBlockOnePort) - u‖
        ≤ 2 / η₀ := by
          refine (norm_sub_le _ _).trans ?_
          have : 2 / η₀ = 1 / η₀ + 1 / η₀ := by ring
          linarith
      _ ≤ (C + 2 * (W₁ : ℝ) ^ 2 / η₀) / (W : ℝ) ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          have e1 : 2 / η₀ * (W : ℝ) ^ 2 ≤ 2 * (W₁ : ℝ) ^ 2 / η₀ := by
            rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hη]; nlinarith
          linarith

end BlockBand.Endpoints.Clock

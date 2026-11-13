module

public import BlockBand.Endpoints.Response.PathFractionalInverseLaw
public import BlockBand.Endpoints.Response.PathFractionalInverseSchur

/-!
# The fractional moment of the interior Schur inverse under the path law

The path fractional-inverse bound, used in the proof of the pass-derivative lemma. Schur out the
two leads; the remaining inverse is `S⁻¹`, `S = H_path - E - z⁻¹CC* = Y + iβCC*`
(`Y = H_path - E - Re(z⁻¹)CC*` Hermitian, `β = -Im z⁻¹ > 0`), with `C` the port coupling (a
function of the two port bonds).

* `pfiSchur b E W n ω = S`; `pfiHerm = Y`, `pfiGamma δ = βCC* + δ`.
* `pfiSchur_shift`: `S + 2iδ = Y + iΓ_δ + iδ` (the disk pencil at `ζ = 0`, `t = i`).
* `pfiHerm_shift`: for real `t`, `Y + tΓ_δ + iδ = D_t(bonds) + ⊕A + iδ` with the Hermitian
  deformation `D_t = (bond part) + (tβ - Re z⁻¹)CC* + (tδ - E)` independent of the blocks.
* **`lintegral_schur_shift_rpow_le`** (the subharmonic step: "apply its
  scalar Poisson inequality at `t = i` and then Tonelli; the same bound follows with `iC`"):
  for `δ > 0`, `E ‖(S + 2iδ)⁻¹‖^s ≤ (C/√c · nW)^s/(1-s)`.
* **`lintegral_schur_inv_rpow_le`** ("to justify possible real poles, first
  add a scalar positive height, use the identical Wegner bound, and pass by Fatou"):
  `E ‖S⁻¹‖^s ≤ (C/√c · nW)^s/(1-s)`.
* `ae_isUnit_schur`: `S` is almost surely invertible.

All bounds: law `growthPathLaw W b`, `0 < b < 1/2`, `-2 < E < 2`, every `n`, `W ≥ 1`,
`0 < s < 1`; `C = 2 C_count`, with `C_count` the absolute constant of
`ConditionalBlockGUECount`; Euclidean operator norm. Hypotheses:
`Inputs.ConditionalBlockGUECount` and `GUELawBridge`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory ProbabilityTheory Complex Set Filter Topology Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator Interval

/-!
### The boundary parameter
-/

theorem pfi_matchedA_normSq {e : ℝ} (he : e ^ 2 ≤ 4) : Complex.normSq (matchedA e) = 1 := by
  rw [matchedA, Complex.normSq_mk]
  have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 4 - e ^ 2 by linarith)
  nlinarith

theorem pfi_boundaryZ_im_pos {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    0 < (boundaryZ b E).im := by
  have he : E ^ 2 ≤ 4 := by nlinarith
  have h : (boundaryZ b E).im = (1 - b) * Real.sqrt (4 - E ^ 2) / 2 := by
    rw [boundaryZ, Complex.add_im, Complex.inv_im, pfi_matchedA_normSq he, Complex.mul_im]
    simp [matchedA]
    ring
  rw [h]
  have : 0 < Real.sqrt (4 - E ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have : 0 < 1 - b := by linarith
  positivity

/-- `β = -Im z⁻¹ = η/|z|²`. -/
def pfiBeta (b E : ℝ) : ℝ := -((boundaryZ b E)⁻¹).im

/-- `α = Re z⁻¹`. -/
def pfiAlpha (b E : ℝ) : ℝ := ((boundaryZ b E)⁻¹).re

theorem boundaryZ_ne_zero {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    boundaryZ b E ≠ 0 := fun h => by
  have := pfi_boundaryZ_im_pos hb hE1 hE2
  rw [h, Complex.zero_im] at this
  exact lt_irrefl _ this

theorem pfiBeta_pos {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) : 0 < pfiBeta b E := by
  rw [pfiBeta, Complex.inv_im, neg_div, neg_neg]
  exact div_pos (pfi_boundaryZ_im_pos hb hE1 hE2)
    (Complex.normSq_pos.2 (boundaryZ_ne_zero hb hE1 hE2))

/-!
### The objects
-/

section Objects

variable (b E : ℝ) (W n : ℕ)

/-- The interior block `A = H_path - E` of the full path matrix. -/
def pfiInt (ω : GrowthPath W) : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  pathMatrix (pathAt W n ω) - (E : ℂ) • 1

/-- The port coupling `C`, as a function of the bonds. -/
def pfiCoup (B : ℕ → Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ :=
  pathPortCoupling (pathAt W n (0, B))

/-- `CC*`, as a function of the bonds. -/
def pfiGram (B : ℕ → Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  pfiCoup W n B * (pfiCoup W n B)ᴴ

/-- The interior Schur complement `S = H_path - E - z⁻¹CC*`. -/
def pfiSchur (ω : GrowthPath W) : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  pfiInt E W n ω - (boundaryZ b E)⁻¹ • pfiGram W n ω.2

/-- The Hermitian part `Y = H_path - E - Re(z⁻¹) CC*`. -/
def pfiHerm (ω : GrowthPath W) : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  pfiInt E W n ω - ((pfiAlpha b E : ℝ) : ℂ) • pfiGram W n ω.2

/-- `Γ_δ = β CC* + δ`. -/
def pfiGamma (δ : ℝ) (ω : GrowthPath W) : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  ((pfiBeta b E : ℝ) : ℂ) • pfiGram W n ω.2 + (δ : ℂ) • 1

/-- The real deformation `D_t = (bond part) + (tβ - α)CC* + (tδ - E)`, a function of the bonds. -/
def pfiDef (t δ : ℝ) (B : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  pathBondPart W n B + ((t * pfiBeta b E - pfiAlpha b E : ℝ) : ℂ) • pfiGram W n B +
    ((t * δ - E : ℝ) : ℂ) • 1

end Objects

theorem fullPathMatrix_eq (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    fullPathMatrix b E W n ω = fromBlocks (pfiInt E W n ω) (pfiCoup W n ω.2)
      (pfiCoup W n ω.2)ᴴ (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) :=
  rfl

theorem pfiGram_isHermitian (W n : ℕ) (B : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    (pfiGram W n B).IsHermitian := isHermitian_mul_conjTranspose_self _

theorem pfi_isHermitian_real_smul {k : Type*} [Fintype k] {X : Matrix k k ℂ} (hX : X.IsHermitian)
    (r : ℝ) : ((r : ℂ) • X).IsHermitian := by
  rw [IsHermitian, conjTranspose_smul, hX.eq, Complex.star_def, Complex.conj_ofReal]

theorem pfi_isHermitian_real_smul_one {k : Type*} [Fintype k] [DecidableEq k] (r : ℝ) :
    ((r : ℂ) • (1 : Matrix k k ℂ)).IsHermitian :=
  pfi_isHermitian_real_smul isHermitian_one r

theorem pfiDef_isHermitian (b E : ℝ) (W n : ℕ) (t δ : ℝ) (B : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    (pfiDef b E W n t δ B).IsHermitian :=
  ((pathBondPart_isHermitian W n B).add
    (pfi_isHermitian_real_smul (pfiGram_isHermitian W n B) _)).add (pfi_isHermitian_real_smul_one _)

theorem measurable_pathBondPart (W n : ℕ) : Measurable (pathBondPart W n) := by
  have hP : Measurable (fun ω : PathSample W n => pathMatrix ω) := by
    unfold pathMatrix; fun_prop
  exact hP.comp ((measurable_pathAt W n).comp (measurable_const.prodMk measurable_id))

theorem measurable_pfiCoup (W n : ℕ) : Measurable (pfiCoup W n) := by
  have hC : Measurable (fun ω : PathSample W n => pathPortCoupling ω) := by
    unfold pathPortCoupling; fun_prop
  exact hC.comp ((measurable_pathAt W n).comp (measurable_const.prodMk measurable_id))

theorem measurable_pfiGram (W n : ℕ) : Measurable (pfiGram W n) := by
  have hc : Continuous (fun X : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ => X * Xᴴ) :=
    continuous_id.matrix_mul continuous_id.matrix_conjTranspose
  exact hc.measurable.comp (measurable_pfiCoup W n)

theorem measurable_pfiDef (b E : ℝ) (W n : ℕ) (t δ : ℝ) : Measurable (pfiDef b E W n t δ) := by
  have h1 : Measurable (fun B => ((t * pfiBeta b E - pfiAlpha b E : ℝ) : ℂ) • pfiGram W n B) :=
    (measurable_const_smul _).comp (measurable_pfiGram W n)
  have h2 : Measurable (fun B => pathBondPart W n B +
      ((t * pfiBeta b E - pfiAlpha b E : ℝ) : ℂ) • pfiGram W n B) :=
    (measurable_pathBondPart W n).add h1
  exact h2.add_const _

theorem measurable_pfiInt (E : ℝ) (W n : ℕ) : Measurable (pfiInt E W n) := by
  have hP : Measurable (fun ω : PathSample W n => pathMatrix ω) := by
    unfold pathMatrix; fun_prop
  exact (hP.comp (measurable_pathAt W n)).sub_const _

theorem measurable_gram_snd_smul (W n : ℕ) (c : ℂ) :
    Measurable (fun ω : GrowthPath W => c • pfiGram W n ω.2) :=
  (measurable_const_smul c).comp ((measurable_pfiGram W n).comp measurable_snd)

theorem measurable_pfiSchur (b E : ℝ) (W n : ℕ) : Measurable (pfiSchur b E W n) :=
  (measurable_pfiInt E W n).sub (measurable_gram_snd_smul W n _)

theorem measurable_pfiHerm (b E : ℝ) (W n : ℕ) : Measurable (pfiHerm b E W n) :=
  (measurable_pfiInt E W n).sub (measurable_gram_snd_smul W n _)

theorem measurable_pfiGamma (b E : ℝ) (W n : ℕ) (δ : ℝ) : Measurable (pfiGamma b E W n δ) :=
  (measurable_gram_snd_smul W n _).add_const _

/-!
### Algebraic identities
-/

theorem pfiInt_eq (E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    pfiInt E W n ω = blockSumOf (pathBlocks W n ω) + pathBondPart W n ω.2 - (E : ℂ) • 1 := by
  rw [pfiInt, pathMatrix_pathAt_eq]

theorem pfiInt_isHermitian (E : ℝ) (W n : ℕ) {ω : GrowthPath W}
    (hω : ∀ k, (ω.1 k).IsHermitian) : (pfiInt E W n ω).IsHermitian := by
  rw [pfiInt_eq]
  refine ((blockSumOf_isHermitian fun i => hω _).add (pathBondPart_isHermitian W n _)).sub ?_
  exact pfi_isHermitian_real_smul_one E

theorem pfiHerm_isHermitian (b E : ℝ) (W n : ℕ) {ω : GrowthPath W}
    (hω : ∀ k, (ω.1 k).IsHermitian) : (pfiHerm b E W n ω).IsHermitian :=
  (pfiInt_isHermitian E W n hω).sub (pfi_isHermitian_real_smul (pfiGram_isHermitian W n _) _)

theorem pfiGamma_isHermitian (b E : ℝ) (W n : ℕ) (δ : ℝ) (ω : GrowthPath W) :
    (pfiGamma b E W n δ ω).IsHermitian :=
  (pfi_isHermitian_real_smul (pfiGram_isHermitian W n _) _).add (pfi_isHermitian_real_smul_one δ)

theorem pfiGamma_quad_ge {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (W n : ℕ)
    (δ : ℝ) (ω : GrowthPath W) (v : Fin n × Fin W → ℂ) :
    δ * vecNormSq v ≤ (star v ⬝ᵥ (pfiGamma b E W n δ ω *ᵥ v)).re := by
  have hg : star v ⬝ᵥ (pfiGram W n ω.2 *ᵥ v) = (vecNormSq ((pfiCoup W n ω.2)ᴴ *ᵥ v) : ℂ) := by
    have := star_dotProduct_gram_mulVec (pfiCoup W n ω.2)ᴴ v
    rwa [conjTranspose_conjTranspose] at this
  rw [pfiGamma, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, dotProduct_add,
    dotProduct_smul, dotProduct_smul, hg, star_dotProduct_self, smul_eq_mul, smul_eq_mul,
    Complex.add_re, Complex.mul_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have := mul_nonneg (pfiBeta_pos hb hE1 hE2).le (vecNormSq_nonneg ((pfiCoup W n ω.2)ᴴ *ᵥ v))
  linarith

theorem inv_boundaryZ_eq (b E : ℝ) :
    (boundaryZ b E)⁻¹ = ((pfiAlpha b E : ℝ) : ℂ) - ((pfiBeta b E : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [pfiAlpha, pfiBeta]

/-- `S + 2iδ = Y + iΓ_δ + iδ`. -/
theorem pfiSchur_shift (b E : ℝ) (W n : ℕ) (δ : ℝ) (ω : GrowthPath W) :
    pfiHerm b E W n ω + I • pfiGamma b E W n δ ω + ((δ : ℂ) * I) • 1 =
      pfiSchur b E W n ω + ((2 * δ : ℝ) * I : ℂ) • 1 := by
  rw [pfiHerm, pfiGamma, pfiSchur, inv_boundaryZ_eq]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  module

/-- On the real axis: `Y + tΓ_δ + iδ = D_t(bonds) + ⊕A + iδ`. -/
theorem pfiHerm_shift (b E : ℝ) (W n : ℕ) (t δ : ℝ) (ω : GrowthPath W) :
    pfiHerm b E W n ω + (t : ℂ) • pfiGamma b E W n δ ω + ((δ : ℂ) * I) • 1 =
      pfiDef b E W n t δ ω.2 + blockSumOf (pathBlocks W n ω) + ((δ : ℂ) * I) • 1 := by
  rw [pfiHerm, pfiGamma, pfiDef, pfiInt_eq]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul]
  module

/-!
### The subharmonic step
-/

theorem ofReal_intervalIntegral_le {g : ℝ → ℝ} (hg : ∀ θ, 0 ≤ g θ) {a c : ℝ} (hac : a ≤ c) :
    ENNReal.ofReal (∫ θ in a..c, g θ) ≤ ∫⁻ θ in Ioc a c, ENNReal.ofReal (g θ) := by
  rw [intervalIntegral.integral_of_le hac]
  by_cases hi : IntegrableOn g (Ioc a c)
  · rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun θ => hg θ)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

theorem measurable_diskInv_circle {Ω : Type*} [MeasurableSpace Ω] {k : Type*} [Fintype k]
    [DecidableEq k] {Y Γ : Ω → Matrix k k ℂ} (hY : Measurable Y) (hΓ : Measurable Γ) (δ : ℝ) :
    Measurable (fun p : Ω × ℝ => diskInv (Y p.1) (Γ p.1) δ (circleMap 0 1 p.2)) := by
  have hc : Measurable (fun p : Ω × ℝ => circleMap (0 : ℂ) 1 p.2) :=
    (continuous_circleMap 0 1).measurable.comp measurable_snd
  have h1 : Measurable (fun p : Ω × ℝ => (1 - circleMap (0 : ℂ) 1 p.2)) :=
    measurable_const.sub hc
  have h2 : Measurable (fun p : Ω × ℝ => ((1 + circleMap (0 : ℂ) 1 p.2) * I)) :=
    (measurable_const.add hc).mul measurable_const
  have hYc : Measurable (fun p : Ω × ℝ => Y p.1 + ((δ : ℂ) * I) • (1 : Matrix k k ℂ)) :=
    (hY.comp measurable_fst).add_const _
  have hpen : Measurable (fun p : Ω × ℝ =>
      diskPencil (Y p.1) (Γ p.1) δ (circleMap 0 1 p.2)) :=
    (h1.smul hYc).add (h2.smul (hΓ.comp measurable_fst))
  exact h1.smul (pfi_measurable_inv.comp hpen)

/-- **The subharmonic step**: with the positive height `δ`,
`E ‖(S + 2iδ)⁻¹‖^s ≤ (C/√c · nW)^s/(1-s)`. -/
theorem lintegral_schur_shift_rpow_le (hCount : ConditionalBlockGUECount)
    (hGUE : GUELawBridge) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ (W n : ℕ), 0 < W → ∀ δ : ℝ, 0 < δ → ∀ s : ℝ, 0 < s → s < 1 →
        ∫⁻ ω, ENNReal.ofReal (‖(pfiSchur b E W n ω + ((2 * δ : ℝ) * I : ℂ) • 1)⁻¹‖ ^ s)
            ∂growthPathLaw W b ≤
          ENNReal.ofReal ((C / Real.sqrt (1 - 2 * b) * ((n * W : ℕ) : ℝ)) ^ s / (1 - s)) := by
  obtain ⟨C, hC, hmain⟩ := path_lintegral_norm_inv_rpow_le hCount hGUE
  refine ⟨C, hC, fun b hb0 hb1 E hE1 hE2 W n hW δ hδ s hs0 hs1 => ?_⟩
  have hb : b < 1 := by linarith
  have := passDeriv_isProbabilityMeasure_growthPathLaw W b
  set Bnd := (C / Real.sqrt (1 - 2 * b) * ((n * W : ℕ) : ℝ)) ^ s / (1 - s) with hBnd
  have hBnd0 : 0 ≤ Bnd := div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith)
  set F : GrowthPath W → ℝ → ℝ≥0∞ := fun ω θ => ENNReal.ofReal
    (‖diskInv (pfiHerm b E W n ω) (pfiGamma b E W n δ ω) δ (circleMap 0 1 θ)‖ ^ s) with hF
  -- Step 1: pointwise sub-mean-value inequality
  have hstep1 : ∀ᵐ ω ∂growthPathLaw W b,
      ENNReal.ofReal (‖(pfiSchur b E W n ω + ((2 * δ : ℝ) * I : ℂ) • 1)⁻¹‖ ^ s) ≤
        ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ θ in Ioc 0 (2 * π), F ω θ := by
    filter_upwards [ae_growthPath_isHermitian W b] with ω hω
    have hsub := norm_diskInv_zero_rpow_le (pfiHerm_isHermitian b E W n hω)
      (pfiGamma_isHermitian b E W n δ ω) hδ (pfiGamma_quad_ge hb hE1 hE2 W n δ ω) hδ hs0
    rw [diskInv_zero, pfiSchur_shift] at hsub
    refine (ENNReal.ofReal_le_ofReal hsub).trans ?_
    rw [circleAverage_def, smul_eq_mul, ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact ofReal_intervalIntegral_le (fun θ => Real.rpow_nonneg (norm_nonneg _) _)
      two_pi_pos.le
  -- Step 3: the Wegner bound on the circle
  have hstep3 : ∀ θ : ℝ, ∫⁻ ω, F ω θ ∂growthPathLaw W b ≤ ENNReal.ofReal Bnd := by
    intro θ
    set ζ := circleMap (0 : ℂ) 1 θ
    have hζ : ‖ζ‖ = 1 := by simp [ζ]
    by_cases h1 : ζ = 1
    · have : ∀ ω, F ω θ = 0 := fun ω => by
        simp only [hF]
        rw [show circleMap (0 : ℂ) 1 θ = 1 from h1, diskInv, sub_self, zero_smul, norm_zero,
          Real.zero_rpow hs0.ne', ENNReal.ofReal_zero]
      simp only [this, lintegral_zero]
      exact zero_le
    · set t : ℝ := (I * (1 + ζ) / (1 - ζ)).re
      have heq : ∀ ω, F ω θ = ENNReal.ofReal (‖(pfiDef b E W n t δ ω.2 +
          blockSumOf (pathBlocks W n ω) + ((δ : ℂ) * I) • 1)⁻¹‖ ^ s) := fun ω => by
        simp only [hF]
        rw [diskInv_eq_of_sphere _ _ δ hζ h1, pfiHerm_shift]
      simp only [heq]
      exact hmain W n hW b hb1 (pfiDef b E W n t δ) (measurable_pfiDef b E W n t δ)
        (pfiDef_isHermitian b E W n t δ) δ s hs0 hs1
  -- Step 2: Tonelli
  have hFm : Measurable (Function.uncurry F) := by
    have := measurable_diskInv_circle (measurable_pfiHerm b E W n)
      (measurable_pfiGamma b E W n δ) δ
    exact ((continuous_norm.measurable.comp this).pow_const s).ennreal_ofReal
  calc ∫⁻ ω, ENNReal.ofReal (‖(pfiSchur b E W n ω + ((2 * δ : ℝ) * I : ℂ) • 1)⁻¹‖ ^ s)
        ∂growthPathLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal (2 * π)⁻¹ * (∫⁻ θ in Ioc 0 (2 * π), F ω θ) ∂growthPathLaw W b :=
        lintegral_mono_ae hstep1
    _ = ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ ω, F ω θ ∂growthPathLaw W b := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_lintegral_swap hFm.aemeasurable
    _ ≤ ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ _θ : ℝ in Ioc 0 (2 * π), ENNReal.ofReal Bnd := by
        gcongr with θ
        exact hstep3 θ
    _ = ENNReal.ofReal Bnd := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hBnd0,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-!
### Almost-sure invertibility and Fatou
-/

theorem pfiHerm_eq (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    pfiHerm b E W n ω = pfiDef b E W n 0 0 ω.2 + blockSumOf (pathBlocks W n ω) := by
  have h := pfiHerm_shift b E W n 0 0 ω
  simpa using h

/-- `S` is almost surely invertible (its Hermitian part `Y = D_0(bonds) + ⊕A` is, by the
Wegner count on `[0, 0]`, and the Ward identity transfers this to `S`). -/
theorem ae_isUnit_schur (hCount : ConditionalBlockGUECount) (hGUE : GUELawBridge) {b E : ℝ}
    (hb1 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ} (hW : 0 < W) (n : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, IsUnit (pfiSchur b E W n ω).det := by
  filter_upwards [path_ae_isUnit hCount hGUE hW hb1 (pfiDef b E W n 0 0)
    (measurable_pfiDef b E W n 0 0) (pfiDef_isHermitian b E W n 0 0),
    ae_growthPath_isHermitian W b] with ω h1 hω
  rw [← pfiHerm_eq] at h1
  exact isUnit_schur_of_hermitianPart (pfiInt_isHermitian E W n hω) (pfiCoup W n ω.2)
    (pfi_boundaryZ_im_pos (by linarith) hE1 hE2) h1

theorem continuousAt_matrix_inv {k : Type*} [Fintype k] [DecidableEq k] {S : Matrix k k ℂ}
    (hS : IsUnit S.det) : ContinuousAt (fun M : Matrix k k ℂ => M⁻¹) S := by
  have : (fun M : Matrix k k ℂ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact ((continuous_id.matrix_det).continuousAt.inv₀ hS.ne_zero).smul
    (continuous_id.matrix_adjugate).continuousAt

/-- **Fatou at real poles**: `E ‖S⁻¹‖^s ≤ (C/√c · nW)^s/(1-s)`. -/
theorem lintegral_schur_inv_rpow_le (hCount : ConditionalBlockGUECount)
    (hGUE : GUELawBridge) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ (W n : ℕ), 0 < W → ∀ s : ℝ, 0 < s → s < 1 →
        ∫⁻ ω, ENNReal.ofReal (‖(pfiSchur b E W n ω)⁻¹‖ ^ s) ∂growthPathLaw W b ≤
          ENNReal.ofReal ((C / Real.sqrt (1 - 2 * b) * ((n * W : ℕ) : ℝ)) ^ s / (1 - s)) := by
  obtain ⟨C, hC, hmain⟩ := lintegral_schur_shift_rpow_le hCount hGUE
  refine ⟨C, hC, fun b hb0 hb1 E hE1 hE2 W n hW s hs0 hs1 => ?_⟩
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ : ∀ k, 0 < δ k := fun k => by positivity
  set f : ℕ → GrowthPath W → ℝ≥0∞ := fun k ω => ENNReal.ofReal
    (‖(pfiSchur b E W n ω + ((2 * δ k : ℝ) * I : ℂ) • 1)⁻¹‖ ^ s)
  have hfm : ∀ k, Measurable (f k) := fun k =>
    ((continuous_norm.measurable.comp (pfi_measurable_inv.comp
      ((measurable_pfiSchur b E W n).add_const _))).pow_const s).ennreal_ofReal
  have hlim : ∀ᵐ ω ∂growthPathLaw W b, Tendsto (fun k => f k ω) atTop
      (𝓝 (ENNReal.ofReal (‖(pfiSchur b E W n ω)⁻¹‖ ^ s))) := by
    filter_upwards [ae_isUnit_schur hCount hGUE hb1 hE1 hE2 hW n] with ω hω
    have hδ0 : Tendsto (fun k => (((2 * δ k : ℝ) * I : ℂ))) atTop (𝓝 0) := by
      have h1 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun k => ((2 * δ k : ℝ) : ℂ)) atTop (𝓝 ((2 * 0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp (h1.const_mul 2)
      simpa using h2.mul_const I
    have hM : Tendsto (fun k => pfiSchur b E W n ω + ((2 * δ k : ℝ) * I : ℂ) • 1) atTop
        (𝓝 (pfiSchur b E W n ω)) := by
      simpa using tendsto_const_nhds.add (hδ0.smul_const (1 : Matrix (Fin n × Fin W)
        (Fin n × Fin W) ℂ))
    have hinv := (continuousAt_matrix_inv hω).tendsto.comp hM
    exact ENNReal.tendsto_ofReal ((hinv.norm).rpow_const (Or.inr hs0.le))
  calc ∫⁻ ω, ENNReal.ofReal (‖(pfiSchur b E W n ω)⁻¹‖ ^ s) ∂growthPathLaw W b
      = ∫⁻ ω, liminf (fun k => f k ω) atTop ∂growthPathLaw W b := by
        refine lintegral_congr_ae ?_
        filter_upwards [hlim] with ω hω
        exact hω.liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ ω, f k ω ∂growthPathLaw W b) atTop := lintegral_liminf_le hfm
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall fun k =>
        hmain b hb0 hb1 E hE1 hE2 W n hW (δ k) (hδ k) s hs0 hs1)

end BlockBand.Endpoints

module

public import BlockBand.Transmission.PassiveCovariance.WordGrad
public import BlockBand.Transmission.PassiveCovariance.LayerBlocks
public import BlockBand.Transmission.PassiveLayer.MomentAlgebra

/-!
# The general bilinear variance and covariance bound

Hypotheses `GaussianPoincare` and `PassiveBoundsStatement` (only its `moments` clause is used).

**Statement** (`wordForm_variance`, `wordForm_covariance`). Fixed `b ∈ (0, 1/2)`,
`E ∈ (-2, 2)`, a maximal word length `L_w` and an insertion bound `K_d`; then `C, W₀`; for every
`W ≥ W₀`, every deterministic strictly passive `X` (`Y = -Im X ≻ 0`, no norm bound), every dressed
word `w` of length `m ≤ L_w` in the letters `𝒢, K̂𝒢, 𝒢ᴴ, (K̂𝒢)ᴴ` (`K̂ = diag(z - X, I)`, `kHat`)
with deterministic `2W × 2W` insertions `‖D_j‖ ≤ K_d`, and all vectors `a, c` on the `2W` layer
sites, under `layerLaw W b .oneBlockOnePort` (the fresh layer):
`Var(a*w c) ≤ (C/W)‖a‖²‖c‖²`, and for two such forms `|Cov(P, Q)| ≤ (C/W)‖a‖‖c‖‖a'‖‖c'‖`.
Norms: Euclidean operator norm for matrices, `vecNorm` for vectors. Uniform in `X` and the
vectors. Every bilinear form of a `passiveWord` (letters `𝒢_{ij}`, `K𝒢₁₁`, `L`, and
adjoints) is such a form (embed the `W`-vectors and insertions in the relevant blocks).

**Proof.** In the real Gaussian coordinates (`PassiveLayer.freshLaw_eq_map`) the form is `C¹`
(`contDiff_wordForm`); its weighted gradient is
`≤ m²(4/W)(K_d^{m+1}B^{m+1})²‖a‖²‖c‖²` with `B = ‖𝒢‖ + ‖K̂𝒢‖ ≤ 3‖𝒢‖ + ‖K𝒢₁₁‖ + ‖L‖`
(`wordForm_gradSq_le`, `wBound_kHat_le`). Poincaré and the `moments` clause of
`PassiveBoundsStatement` (`L^{2(L_w+1)}`, uniform in
passive `X`) give the variance; Cauchy–Schwarz gives the covariance.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The dressing `K̂ = diag(z - X, I)` on the layer sites (`z = z_∂(E)`). -/
def kHat (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : LayerMat W :=
  fromBlocks (liftX (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X)) 0 0 1

/-- The random letter bound `3‖𝒢‖ + ‖K𝒢₁₁‖ + ‖L‖`. -/
def btFun (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℝ :=
  3 * ‖gRes b E X ω‖ + ‖kG11 E (boundaryZ b E) X ω‖ + ‖lAt E (boundaryZ b E) X ω‖

theorem btFun_nonneg (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    0 ≤ btFun b E X ω := by unfold btFun; positivity

theorem norm_blk21_le (M : LayerMat W) : ‖blk21 M‖ ≤ ‖M‖ :=
  norm_submatrix_le M (f := fun x : Fin W => (port x : LayerSite W .oneBlockOnePort))
    (g := fun y : Fin W => (phys y : LayerSite W .oneBlockOnePort))
    (fun x y h => by simpa using h) (fun x y h => by simpa using h)

theorem norm_blk22_le (M : LayerMat W) : ‖blk22 M‖ ≤ ‖M‖ :=
  norm_submatrix_le M (f := fun x : Fin W => (port x : LayerSite W .oneBlockOnePort))
    (g := fun y : Fin W => (port y : LayerSite W .oneBlockOnePort))
    (fun x y h => by simpa using h) (fun x y h => by simpa using h)

/-- `B = ‖𝒢‖ + ‖K̂𝒢‖ ≤ 3‖𝒢‖ + ‖K𝒢₁₁‖ + ‖L‖`. -/
theorem wBound_kHat_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : wBound (kHat b E X) (gRes b E X ω) ≤ btFun b E X ω := by
  have e : kHat b E X * gRes b E X ω = fromBlocks (liftX (kG11 E (boundaryZ b E) X ω))
      (liftX (lAt E (boundaryZ b E) X ω)) (liftX (blk21 (gRes b E X ω)))
      (liftX (blk22 (gRes b E X ω))) := by
    conv_lhs => rw [layerMat_eq_fromBlocks (gRes b E X ω)]
    rw [kHat, fromBlocks_multiply]
    simp only [Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, ← liftX_mul]
    rfl
  have hK := norm_fromBlocks_le (liftX (kG11 E (boundaryZ b E) X ω))
      (liftX (lAt E (boundaryZ b E) X ω)) (liftX (blk21 (gRes b E X ω)))
      (liftX (blk22 (gRes b E X ω)))
  rw [← e] at hK
  have h1 := norm_liftX_le (kG11 E (boundaryZ b E) X ω)
  have h2 := norm_liftX_le (lAt E (boundaryZ b E) X ω)
  have h3 := (norm_liftX_le (blk21 (gRes b E X ω))).trans (norm_blk21_le _)
  have h4 := (norm_liftX_le (blk22 (gRes b E X ω))).trans (norm_blk22_le _)
  unfold wBound btFun
  linarith

theorem measurable_btFun (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Measurable (btFun b E X) := by
  have hG := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hk := measurable_kG11 (W := W) E (boundaryZ b E) X
  have hl := measurable_lAt (W := W) E (boundaryZ b E) X
  unfold btFun
  exact ((measurable_const.mul (continuous_norm.measurable.comp hG)).add
    (continuous_norm.measurable.comp hk)).add (continuous_norm.measurable.comp hl)

/-- **Moments of `1 + B`** from the `moments` clause, uniformly over passive inputs. -/
theorem btFun_moment (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (p : ℝ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
        eLpNorm (fun ω => 1 + btFun b E X ω) (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
          ENNReal.ofReal C := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C, W₀, h⟩ := hA.moments b hb0 hb _ hκ p hp
  refine ⟨1 + (3 * max C 0 + max C 0 + max C 0), W₀, by positivity, fun W hW X hX => ?_⟩
  obtain ⟨-, hg, hk, hl⟩ := h W hW E (mem_bulkInterval_min E) _
    (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have mg : MomBd μ (fun ω => ‖gRes b E X ω‖) p (max C 0) :=
    MomBd.nonneg ⟨(continuous_norm.measurable.comp hGm).aestronglyMeasurable, hg⟩
  have mk : MomBd μ (fun ω => ‖kG11 E (boundaryZ b E) X ω‖) p (max C 0) :=
    MomBd.nonneg ⟨(continuous_norm.measurable.comp
      (measurable_kG11 (W := W) E (boundaryZ b E) X)).aestronglyMeasurable, hk⟩
  have ml : MomBd μ (fun ω => ‖lAt E (boundaryZ b E) X ω‖) p (max C 0) :=
    MomBd.nonneg ⟨(continuous_norm.measurable.comp
      (measurable_lAt (W := W) E (boundaryZ b E) X)).aestronglyMeasurable, hl⟩
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have m1 : MomBd μ (fun _ => (1 : ℝ)) p 1 := by
    simpa using MomBd.const (μ := μ) (1 : ℝ) p (by linarith)
  have m3 := mg.const_mul (show (0 : ℝ) ≤ 3 by norm_num)
  have ms := ((m3.add hp mk (by positivity) hC0).add hp ml (by positivity) hC0)
  exact (m1.add hp ms zero_le_one (by positivity)).2

/-- `∫ g² ≤ K²` from `‖g‖₂ ≤ K`. -/
theorem integral_sq_le_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ) {K : ℝ} (hK : 0 ≤ K) (h : eLpNorm g 2 μ ≤ ENNReal.ofReal K) :
    ∫ ω, g ω ^ 2 ∂μ ≤ K ^ 2 := by
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hg
  simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at h2
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
    (hg.pow 2)]
  have e : ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ = ∫⁻ ω, ‖g ω‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [e, ← h2]
  refine ENNReal.toReal_le_of_le_ofReal (sq_nonneg K) ?_
  calc eLpNorm g 2 μ ^ 2 ≤ ENNReal.ofReal K ^ 2 := by gcongr
    _ = ENNReal.ofReal (K ^ 2) := (ENNReal.ofReal_pow hK 2).symm

end BlockBand.Transmission.PassiveCovariance

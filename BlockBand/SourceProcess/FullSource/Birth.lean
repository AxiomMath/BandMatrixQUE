module

public import BlockBand.SourceProcess.FullSource.Clock
public import BlockBand.Transmission.PathScalar.MeanStepLimit
public import BlockBand.Transmission.PassiveLayer.TMMain

/-!
# Moments of a tag at its birth length

* `re_trace_le_card`: `Re Tr(D*D) ≤ |rows| ‖D‖²`;
* `birth_moment_succ`: for `k ≥ 1`, `Y_{k+1;k} = D₊*D₊` a.s., so `E t_{k+1}^q ≤ C_D^{2q}` from the
  `freshD` moments of `FullSourceEstimates` (Fubini).

The case `k = 0` is proved in the sibling module: `fullPathMatrix_one_eq` and
`growthPathLaw_map_sampleOne` identify the one-block two-port path with the layer of shape
`.oneBlockTwoPorts` at `X = 0`, and `birth_moment_zero` uses `t_1 ≤ ‖G‖²`, with `‖G‖ ∈ L^{2q}` by
`GaussianAbsorptionContract`.

A tag starts with `C₊`, and `‖C₊‖_{L^p} ≤ C_p`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

theorem re_trace_le_card {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n ℂ) : (Dᴴ * D).trace.re ≤ Fintype.card m * ‖D‖ ^ 2 := by
  rw [← sum_vecNorm_rowv]
  have hrow : ∀ x, vecNorm (rowv D x) ≤ ‖D‖ := by
    intro x
    have e : rowv D x = Dᴴ *ᵥ Pi.single x 1 := by
      funext c; simp [rowv, mulVec, dotProduct, Pi.single_apply, Matrix.conjTranspose_apply]
    have h1 := vecNorm_mulVec_le' Dᴴ (Pi.single x (1 : ℂ))
    have h2 : vecNorm (Pi.single x (1 : ℂ)) = 1 := by
      rw [vecNorm, Finset.sum_eq_single x (fun l _ hl => by simp [hl]) (by simp)]; simp
    rw [e]; rw [h2, mul_one, Matrix.l2_opNorm_conjTranspose] at h1; exact h1
  calc ∑ x, vecNorm (rowv D x) ^ 2 ≤ ∑ _x : m, ‖D‖ ^ 2 :=
        Finset.sum_le_sum fun x _ => pow_le_pow_left₀
          (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _) (hrow x) 2
    _ = Fintype.card m * ‖D‖ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

variable {W : ℕ}

/-- **Birth of a tag at `k ≥ 1`.** -/
theorem birth_moment_succ {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {k q : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q) {CD : ℝ} (hCD : 0 ≤ CD)
    (hD : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      eLpNorm (fun ω => ‖freshD b E XX ω‖) (ENNReal.ofReal ((2 * q : ℕ) : ℝ)) (freshLaw W b) ≤
        ENNReal.ofReal CD) :
    ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ q) ∂growthPathLaw W b ≤
      ENNReal.ofReal (CD ^ (2 * q)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set Φ : PastSample W k × LayerSample W .oneBlockOnePort → ℝ≥0∞ := fun q' =>
    ENNReal.ofReal (‖freshD b E (pastXX E W k q'.1) q'.2‖ ^ (2 * q))
  have hmΦ : Measurable Φ := ((measurable_freshD_comp b E ((measurable_pastXX E k).comp
    measurable_fst) measurable_snd).norm.pow_const _).ennreal_ofReal
  have hZ : ∀ᵐ ω ∂growthPathLaw W b, pastCoords W k ω ∈ (Set.univ : Set (PastSample W k)) →
      ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ q) ≤ Φ (pastCoords W k ω, freshSample W k ω) := by
    filter_upwards [ae_tagResponse_succ_new_full hb0 hb hE1 hE2 hW] with ω h _
    refine ENNReal.ofReal_le_ofReal ?_
    rw [tagMass, h k hk, pastXX_eq, pow_mul]
    refine pow_le_pow_left₀ (mul_nonneg (by positivity) (trace_factor_re_nonneg _)) ?_ q
    have := re_trace_le_card (freshD b E (pastXX E W k (pastCoords W k ω)) (freshSample W k ω))
    rw [Fintype.card_fin] at this
    calc (W : ℝ)⁻¹ * _ ≤ (W : ℝ)⁻¹ * (W * _) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  have hstep : ∀ᵐ p ∂pastLaw W k b, p ∈ (Set.univ : Set (PastSample W k)) →
      ∫⁻ f, Φ (p, f) ∂freshLaw W b ≤ ENNReal.ofReal (CD ^ (2 * q)) := by
    filter_upwards [ae_pastLaw_hermitian W k b] with p hp _
    have hm : Measurable fun f => ‖freshD b E (pastXX E W k p) f‖ :=
      (measurable_freshD_comp b E measurable_const measurable_id).norm
    obtain ⟨hi, hb'⟩ := integral_abs_pow_le (ν := freshLaw W b) (n := 2 * q) (by omega) hCD
      ⟨hm.aestronglyMeasurable, hD _ (pastXX_isHermitian E hp)⟩
    simp only [Φ]
    rw [← ofReal_integral_eq_lintegral_ofReal (by simpa using hi)
      (Filter.Eventually.of_forall fun f => by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq_of_le (integral_congr_ae
      (Filter.Eventually.of_forall fun f => ?_)) hb')
    simp only [abs_of_nonneg (norm_nonneg _)]
  have h := lintegral_indicator_step (μ := growthPathLaw W b) (μP := pastLaw W k b)
    (ν := freshLaw W b) (measurable_pastCoords W k) (measurable_freshSample W k)
    (growthPathLaw_map_past_fresh W k b) MeasurableSet.univ hmΦ measurable_const hZ hstep
  simp only [Set.preimage_univ, Set.indicator_univ] at h
  refine h.trans (le_of_eq ?_)
  rw [lintegral_const, measure_univ, mul_one]

end BlockBand.SourceProcess.FullSource

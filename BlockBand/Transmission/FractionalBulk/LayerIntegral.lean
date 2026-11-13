module

public import BlockBand.Transmission.FractionalBulk.LayerGap

/-!
# One fresh layer: the integrated concavity bound at a fixed passive input

Deterministic passive `X`, `T = T(X)` with eigenvalues `t_i` and eigenvectors `u_i`, `Z = V*UV`,
`N = max(1, ‖L‖²)`:

**`layer_integral`**: `E stepFrac ≤ Σ t_i^p + c_pJ_p Σ t_i^p (E Re Z_ii - 1) - (c_p/27) Σ_{ij} E G_ij`,
`G_ij = 1{t_i ≤ t_j} t_i^p t_j^p |Z_ji - δ_ji|²/N ≥ 0`, with the integrability of every term.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.Generator
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `G_ij`. -/
def gapG (p : ℝ) {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (b E : ℝ)
    (X : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) (y : LayerSample W .oneBlockOnePort) : ℝ :=
  if ts_lam hT i ≤ ts_lam hT j then ts_lam hT i ^ p * ts_lam hT j ^ p *
    (‖bilinear (ts_vec hT j) (freshU b E X y) (ts_vec hT i) - (1 : Matrix (Fin W) (Fin W) ℂ) j i‖ ^ 2 /
      weightN b E X y) else 0

theorem gapG_nonneg (p : ℝ) {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (b E : ℝ)
    (X : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) (y) : 0 ≤ gapG p hT b E X i j y := by
  unfold gapG
  have hN : 0 < weightN b E X y := lt_of_lt_of_le one_pos (le_max_left _ _)
  split_ifs
  · have := Real.rpow_nonneg (ts_lam_nonneg hT i) p
    have := Real.rpow_nonneg (ts_lam_nonneg hT j) p
    positivity
  · exact le_rfl

theorem norm_bilinear_freshU_le {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (b E : ℝ)
    (X : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) (y) :
    ‖bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT j)‖ ≤ ‖freshL b E X y‖ ^ 2 := by
  have := norm_bilinear_le (ts_vec hT i) (freshU b E X y) (ts_vec hT j)
  rw [ts_vecNorm, ts_vecNorm, one_mul, mul_one] at this
  exact this.trans (norm_freshU_le b E X y)

theorem integrable_gapG {p : ℝ} {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (b E : ℝ)
    (X : Matrix (Fin W) (Fin W) ℂ)
    (hL4i : Integrable (fun y => ‖freshL b E X y‖ ^ 4) (freshLaw W b)) (i j : Fin W) :
    Integrable (gapG p hT b E X i j) (freshLaw W b) := by
  unfold gapG
  split_ifs
  · refine Integrable.const_mul ?_ _
    have hm : Measurable fun y => ‖bilinear (ts_vec hT j) (freshU b E X y) (ts_vec hT i) -
        (1 : Matrix (Fin W) (Fin W) ℂ) j i‖ ^ 2 / weightN b E X y :=
      ((((measurable_bilinear_freshU b E X _ _).sub measurable_const).norm).pow_const 2).div
        (measurable_weightN b E X)
    refine Integrable.mono' (((integrable_const (2 : ℝ)).add (hL4i.const_mul 2)))
      hm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    have hN1 : 1 ≤ weightN b E X y := le_max_left _ _
    have hq0 : 0 ≤ ‖bilinear (ts_vec hT j) (freshU b E X y) (ts_vec hT i) -
        (1 : Matrix (Fin W) (Fin W) ℂ) j i‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg (div_nonneg hq0 (by linarith))]
    refine (div_le_self hq0 hN1).trans ?_
    have h1 := norm_bilinear_freshU_le hT b E X j i y
    have h2 : ‖(1 : Matrix (Fin W) (Fin W) ℂ) j i‖ ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    have h3 := norm_sub_le (bilinear (ts_vec hT j) (freshU b E X y) (ts_vec hT i))
      ((1 : Matrix (Fin W) (Fin W) ℂ) j i)
    have h4 : ‖bilinear (ts_vec hT j) (freshU b E X y) (ts_vec hT i) -
        (1 : Matrix (Fin W) (Fin W) ℂ) j i‖ ≤ ‖freshL b E X y‖ ^ 2 + 1 := by linarith
    have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    nlinarith [sq_nonneg (‖freshL b E X y‖ ^ 2 - 1)]
  · exact integrable_zero _ _ _

theorem gap_rewrite {ι : Type*} [Fintype ι] (c N : ℝ) (hN : 0 < N) (P : ι → ι → Prop)
    [∀ i j, Decidable (P i j)] (f w : ι → ι → ℝ) :
    c / (27 * N) * ∑ i, ∑ j, (if P i j then f i j * w i j else 0) =
      c / 27 * ∑ i, ∑ j, (if P i j then f i j * (w i j / N) else 0) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · field_simp
  · simp

theorem layer_pointwise {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {T : Matrix (Fin W) (Fin W) ℂ}
    (hT : T.PosSemidef) (hT1 : (1 - T).PosSemidef) (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y) :
    fracTrace p (sqDiag (ts_lam hT) * eigU hT (freshU b E X y) * sqDiag (ts_lam hT)) ≤
      ∑ i, ts_lam hT i ^ p + cP p * jP p * ∑ i, ts_lam hT i ^ p *
        ((bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re - 1) -
      cP p / 27 * ∑ i, ∑ j, gapG p hT b E X i j y := by
  have h := sample_bound hp0 hp1 hT hT1 (freshL b E X y)
  have hN : 0 < max 1 (‖freshL b E X y‖ ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [gap_rewrite _ _ hN] at h
  have hU : freshL b E X y * (freshL b E X y)ᴴ = freshU b E X y := rfl
  rw [hU] at h
  simp only [eigU_apply] at h
  exact h

/-- **The integrated bound at a fixed passive input.** -/
theorem layer_integral {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ} (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hT : (passiveTransmission b E X).PosSemidef)
    (hU : ∀ x y, Integrable (fun ω => freshU b E X ω x y) (freshLaw W b))
    (hL4i : Integrable (fun y => ‖freshL b E X y‖ ^ 4) (freshLaw W b)) :
    (∀ i, Integrable (fun y => (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re)
      (freshLaw W b)) ∧
    ∫ y, stepFrac p b E X y ∂freshLaw W b ≤ ∑ i, ts_lam hT i ^ p +
      cP p * jP p * ∑ i, ts_lam hT i ^ p *
        ((∫ y, (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re ∂freshLaw W b) - 1) -
      cP p / 27 * ∑ i, ∑ j, ∫ y, gapG p hT b E X i j y ∂freshLaw W b := by
  set ν := freshLaw W b
  have hT1 := one_sub_passiveTransmission_posSemidef b E X
  have hAi : ∀ i, Integrable (fun y => (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re)
      ν := fun i => (integrable_bilinear_of hU _ _).re
  refine ⟨hAi, ?_⟩
  have hSm : Measurable (stepFrac p b E X) := by
    have h := (measurable_stepFrac (W := W) p b E).comp (measurable_prodMk_left (x := X))
    exact h
  have hSi : Integrable (stepFrac p b E X) ν :=
    Integrable.of_bound hSm.aestronglyMeasurable W (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (stepFrac_nonneg _ _ _ _ _)]; exact stepFrac_le _ _ _ _ _)
  have hpt := layer_pointwise hp0 hp1 hT hT1 b E X
  have hae := ae_stepFrac_eq (p := p) hp0 hp1 hb0 hb hW h1 h2 hY hT
  have hRi : Integrable (fun y => ∑ i, ts_lam hT i ^ p + cP p * jP p * ∑ i, ts_lam hT i ^ p *
      ((bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re - 1) -
      cP p / 27 * ∑ i, ∑ j, gapG p hT b E X i j y) ν := by
    refine ((integrable_const _).add ?_).sub ?_
    · exact (integrable_finsetSum _ fun i _ => ((hAi i).sub (integrable_const _)).const_mul _).const_mul _
    · exact (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        integrable_gapG hT b E X hL4i i j).const_mul _
  calc ∫ y, stepFrac p b E X y ∂ν ≤ ∫ y, (∑ i, ts_lam hT i ^ p + cP p * jP p * ∑ i, ts_lam hT i ^ p *
        ((bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re - 1) -
        cP p / 27 * ∑ i, ∑ j, gapG p hT b E X i j y) ∂ν := by
        refine integral_mono_ae hSi hRi ?_
        filter_upwards [hae] with y hy
        rw [hy]; exact hpt y
    _ = _ := integral_shape (∑ i, ts_lam hT i ^ p) (cP p * jP p) (cP p / 27)
        (fun i => ts_lam hT i ^ p)
        (fun i y => (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re)
        (gapG p hT b E X) hAi (fun i j => integrable_gapG hT b E X hL4i i j)

end BlockBand.Transmission.FractionalBulk

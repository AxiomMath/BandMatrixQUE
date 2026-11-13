module

public import BlockBand.Transmission.SourceMixing.MassAlg
public import BlockBand.Transmission.SourceMixing.MassMean
public import BlockBand.Transmission.SourceMixing.MassUpdate
public import BlockBand.Transmission.SourceMixing.TraceSpectral

/-!
# One fresh layer: the conditional mass moments

Law `freshLaw W b`, deterministic passive `X` (`Y ⪰ 0`), fixed `0 < b < 1/2`, `-2 < E < 2`;
`q = passiveMass b E X`, `δ₀ = jetDistance0`. Hypothesis `PassiveBoundsStatement`.

The moments of the passive mass after one fresh layer, given the old layer.

* `qc X = max q 0`: equal to `q` on passive inputs, and `0 ≤ qc ≤ W/(4η)` for every `X`.
* `ml_fresh`: `E qc(X₊) = Re Tr(Q E[LL*])` and `‖qc(X₊) - E qc(X₊)‖_n ≤ C_f q/√W` (the `bilinear`
  clause of the passive bounds, through `oneStepFluctuation_of_passiveBounds` and
  `eLpNorm_trace_mul_le`, with `Q₊ = L*QL`).
* `massLayer_step`: for every integer `n ≥ 1` there are `c > 0`, `D₁, D₂ ≥ 0` and `W₀` with
  `E qc(X₊)ⁿ ≤ qⁿ(1 - cl/W) + (clⁿ⁺¹ + D₁ + D₂(Wδ₀)ⁿ⁺¹)/W` for every `l ≥ 0`, `W ≥ W₀` and
  passive `X` (the mean from `massMean_holds`, the expansion `integral_pow_le_of_fluct`, the
  algebra `mma_layer`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The clamped mass `max q 0` (equal to `q` on passive inputs). -/
def qc (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ := max (passiveMass b E X) 0

theorem qc_eq {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    qc b E X = passiveMass b E X := max_eq_left (passiveMass_nonneg b E hY)

theorem qc_nonneg (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : 0 ≤ qc b E X := le_max_right _ _

theorem qc_le {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (X : Matrix (Fin W) (Fin W) ℂ) :
    qc b E X ≤ W / (4 * etaZ b E) := by
  have hη := etaZ_pos b E hb h1 h2
  exact max_le (passiveMass_le_width hb h1 h2 X) (by positivity)

theorem measurable_qc (b E : ℝ) : Measurable fun X : Matrix (Fin W) (Fin W) ℂ => qc b E X :=
  (measurable_passiveMass b E).max measurable_const

theorem measurable_qc_fresh (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable fun ω : LayerSample W .oneBlockOnePort => qc b E (freshSchur E X ω) := by
  have hlift : Measurable fun _ : LayerSample W .oneBlockOnePort =>
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2 :
        Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) := measurable_const
  have hS : Measurable fun ω : LayerSample W .oneBlockOnePort => freshSchur E X ω :=
    Measurable.of_eval_matrix _ fun x y =>
      (PathScalar.measurable_layerSchur .oneBlockOnePort E hlift measurable_id).eval_matrix
  exact (measurable_qc b E).comp hS

theorem ml_trace_matrixExpect {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : Matrix (Fin W) (Fin W) ℂ) {U : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hU : ∀ i j, Integrable (fun ω => U ω i j) μ) :
    ∫ ω, (Q * U ω).trace ∂μ = (Q * matrixExpect μ U).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, matrixExpect, Matrix.of_apply]
  have hi : ∀ i, ∫ ω, ∑ j, Q i j * U ω j i ∂μ = ∑ j, Q i j * ∫ ω, U ω j i ∂μ := fun i => by
    rw [integral_finsetSum _ (fun j _ => (hU j i).const_mul (Q i j))]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [integral_finsetSum _
    (fun i _ => integrable_finsetSum _ (fun j _ => (hU j i).const_mul (Q i j)))]
  exact Finset.sum_congr rfl fun i _ => hi i

/-- Entry integrability of `LL*` (the `moments` clause of the passive bounds at `p = 4`). -/
theorem ml_integrable_U (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ i j, Integrable (fun ω => freshU b E X ω i j) (freshLaw W b) := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C4, W4, h4⟩ := hA.moments b hb0 hb _ hκ 4 (by norm_num)
  refine ⟨W4, fun W hW X hX i j => ?_⟩
  have hE := PassiveLayer.mem_bulkInterval_min E
  have hz := PassiveLayer.boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  have m4 : eLpNorm (fun ω => ‖freshL b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ))) (freshLaw W b) ≤
      ENNReal.ofReal C4 := by
    have := (h4 W hW E hE _ hz X hX).2.2.2
    norm_num at this ⊢; exact this
  have hb2 := eLpNorm_two_le_of_pow_bound ((measurable_freshU b E X).eval_matrix (i := i)
    (j := j)).aestronglyMeasurable (fun _ => norm_nonneg _)
    (measurable_norm_freshL b E X).aestronglyMeasurable zero_le_one 2 (by norm_num)
    (fun ω => by rw [one_mul]; exact (norm_entry_le _ i j).trans (norm_freshU_le b E X ω)) m4
  have fin : ENNReal.ofReal 1 * ENNReal.ofReal C4 ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hmem : MemLp (fun ω => freshU b E X ω i j) 2 (freshLaw W b) := hb2.trans_lt fin.lt_top
  exact hmem.integrable one_le_two

/-- The fresh mass at a fixed energy: mean identity and fluctuation bound. -/
theorem ml_fresh (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Cf : ℝ) (W₀ : ℕ), 1 ≤ Cf ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        ∫ ω, qc b E (freshSchur E X ω) ∂freshLaw W b =
            (passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re ∧
          eLpNorm (fun ω => qc b E (freshSchur E X ω) - ∫ ω', qc b E (freshSchur E X ω')
              ∂freshLaw W b) n (freshLaw W b) ≤
            ENNReal.ofReal (Cf / Real.sqrt W * passiveMass b E X) := by
  obtain ⟨Wi, hint⟩ := ml_integrable_U hA hb0 hb h1 h2
  obtain ⟨Cb, Wb, hbil⟩ := oneStepFluctuation_of_passiveBounds hA b hb0 hb E h1 h2 n
    (by exact_mod_cast hn)
  refine ⟨max Cb 1, max (max Wi Wb) 1, le_max_right _ _, fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWi, hWb⟩, hW1⟩ := hW
  set μ := freshLaw W b
  set Q := passiveQ b E X
  have hQ : Q.PosSemidef := hX.conjTranspose_mul_mul_same _
  have hU := hint W hWi X hX
  have hTint : Integrable (fun ω => (Q * freshU b E X ω).trace) μ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hU j i).const_mul _
  have hae : ∀ᵐ ω ∂μ, qc b E (freshSchur E X ω) = (Q * freshU b E X ω).trace.re := by
    filter_upwards [ae_layer_herm (W := W) b, ae_passiveMass_freshSchur hb0 hb hW1 h1 h2 hX]
      with ω hA0 hm
    rw [qc_eq (PathScalar.passiveY_freshSchur E hX ω hA0), hm]
  have hmean : ∫ ω, qc b E (freshSchur E X ω) ∂μ =
      (Q * matrixExpect μ (freshU b E X)).trace.re := by
    rw [integral_congr_ae hae, ← ml_trace_matrixExpect μ Q hU]
    exact integral_re hTint
  refine ⟨hmean, ?_⟩
  have hB : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
      matrixExpect μ (freshU b E X)) v) n μ ≤
      ENNReal.ofReal (max Cb 1 / Real.sqrt W * vecNorm u * vecNorm v) := fun u v => by
    have := (hbil W hWb X hX u v).1
    rw [ENNReal.ofReal_natCast] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have := vecNorm_nonneg u; have := vecNorm_nonneg v
    have : Cb / Real.sqrt W ≤ max Cb 1 / Real.sqrt W :=
      div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    gcongr
  have hB0 : 0 ≤ max Cb 1 / Real.sqrt W :=
    div_nonneg (le_trans zero_le_one (le_max_right _ _)) (Real.sqrt_nonneg _)
  have hT : eLpNorm (fun ω => (Q * (freshU b E X ω - matrixExpect μ (freshU b E X))).trace) n μ ≤
      ENNReal.ofReal (max Cb 1 / Real.sqrt W * Q.trace.re) :=
    eLpNorm_trace_mul_le μ hQ (by exact_mod_cast hn) hB0 hB
  have hsm : AEStronglyMeasurable (fun ω => qc b E (freshSchur E X ω) -
      ∫ ω', qc b E (freshSchur E X ω') ∂μ) μ :=
    ((measurable_qc_fresh b E X).sub measurable_const).aestronglyMeasurable
  have hpm : passiveMass b E X = Q.trace.re := rfl
  rw [hpm]
  refine le_trans (eLpNorm_mono_ae hsm ?_) hT
  filter_upwards [hae] with ω hω
  have e : (Q * (freshU b E X ω - matrixExpect μ (freshU b E X))).trace.re =
      (Q * freshU b E X ω).trace.re - (Q * matrixExpect μ (freshU b E X)).trace.re := by
    rw [Matrix.mul_sub, trace_sub, Complex.sub_re]
  rw [hω, hmean, Real.norm_eq_abs, ← e]
  exact Complex.abs_re_le_norm _

/-- One fresh layer of the mass-moment recursion. -/
theorem massLayer_step (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (c D₁ D₂ : ℝ) (W₀ : ℕ), 0 < c ∧ 0 ≤ D₁ ∧ 0 ≤ D₂ ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ l : ℝ, 0 ≤ l →
        ∫ ω, qc b E (freshSchur E X ω) ^ n ∂freshLaw W b ≤
          qc b E X ^ n * (1 - c * l / W) +
            (c * l ^ (n + 1) + D₁ + D₂ * (W * jetDistance0 b E X) ^ (n + 1)) / W := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hα : 0 < alphaCoef b E := by
    rw [alphaCoef]
    have : 0 < (1 - b) ^ 2 := by have : 0 < 1 - b := by linarith
                                 positivity
    exact div_pos this (mul_pos hb0 hη)
  obtain ⟨Cm, Wm, hCm, hmean⟩ := massMean_holds hA hb0 hb h1 h2
  obtain ⟨Cf, Wf, hCf, hfr⟩ := ml_fresh hA hb0 hb h1 h2 n hn
  obtain ⟨c, D₁, D₂, hc, hD₁, hD₂, halg⟩ := mma_layer hn hα (by positivity : 0 ≤ (4 * etaZ b E)⁻¹)
    hCm hCf (by positivity : 0 ≤ (etaZ b E)⁻¹ + 1)
  refine ⟨c, D₁, D₂, max (max Wm Wf) 1, hc, hD₁, hD₂, fun W hW X hX l hl => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWm, hWf⟩, hW1⟩ := hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  set μ := freshLaw W b
  obtain ⟨hm, hfl⟩ := hfr W hWf X hX
  have hq0 := passiveMass_nonneg b E hX
  have hqc := qc_eq (b := b) (E := E) hX
  have hσ : 0 ≤ Cf / Real.sqrt W * passiveMass b E X := by
    have : 0 ≤ Cf := by linarith
    positivity
  have hexp := integral_pow_le_of_fluct μ n (measurable_qc_fresh b E X)
    (ae_of_all _ fun ω => qc_nonneg b E _) (ae_of_all _ fun ω => qc_le (by linarith) h1 h2 _) hσ
    hfl
  have hm0 : 0 ≤ ∫ ω, qc b E (freshSchur E X ω) ∂μ := integral_nonneg fun ω => qc_nonneg b E _
  have hqW : passiveMass b E X ≤ (4 * etaZ b E)⁻¹ * W := by
    have := passiveMass_le_width (b := b) (by linarith) h1 h2 X
    rwa [div_eq_inv_mul] at this
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδb := jetDistance0_le_bound hb0 hb h1 h2 hX
  have hmq := hmean W hWm X hX
  rw [← hm] at hmq
  rw [hqc]
  exact halg W (passiveMass b E X) _ (jetDistance0 b E X) _ hW1' hq0 hqW hδ0 hδb hm0 hmq hexp l hl

end BlockBand.Transmission.SourceMixing

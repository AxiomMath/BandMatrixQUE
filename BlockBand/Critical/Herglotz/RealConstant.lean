module

public import BlockBand.Critical.Herglotz.Assembly
public import BlockBand.Critical.Herglotz.CharIntegrated
public import BlockBand.Critical.Herglotz.BoundedMean

/-!
# The real constant vanishes

Ingredients of the real-constant step: `Im R ≥ 0`, `Im a ≥ 0` for `a = v^* near(iY) v`
(`im_quad_weighted_nonneg`); the bounded analytic mean `E e^{itq_N(iY)} → e^{-t‖v‖²}`; the
convergence in law `a_N ⇒ a_can` of the near quadratic form (the near-part law at `K = {iY}`);
`a_can = smoothQuadCauchy` a.s. and its `L²` bound (`smoothQuadCauchy_L2`); `Im R` is controlled by
the escaped mass (`im_quad_farPart_le`); and the integrated characteristic-function criterion.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric Set Complex
open scoped Matrix NNReal ENNReal ComplexOrder ComplexConjugate

namespace BlockBand.Critical.Herglotz

open scoped JV
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

variable {r : ℕ}

/-!
## Algebra of quadratic forms of weighted residue sums
-/

theorem quad_add (A B : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    quad (A + B) v = quad A v + quad B v := by
  unfold quad; rw [Matrix.add_mulVec, dotProduct_add]

theorem quad_smul (c : ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    quad (c • A) v = c * quad A v := by
  unfold quad; rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem quad_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → ℂ) : quad (∑ i ∈ s, A i) v = ∑ i ∈ s, quad (A i) v := by
  unfold quad; rw [Matrix.sum_mulVec, dotProduct_sum]

theorem quad_posSemidef {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef) (v : Fin r → ℂ) :
    (quad A v).im = 0 ∧ 0 ≤ (quad A v).re := by
  have h := Complex.nonneg_iff.1 (hA.dotProduct_mulVec_nonneg v)
  exact ⟨h.2.symm, h.1⟩

theorem continuous_quad (v : Fin r → ℂ) :
    Continuous fun M : Matrix (Fin r) (Fin r) ℂ => quad M v := by
  have : (fun M : Matrix (Fin r) (Fin r) ℂ => quad M v) =
      fun M => ∑ k, ∑ l, conj (v k) * M k l * v l := funext fun M => quad_eq M v
  rw [this]
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    (continuous_const.mul (continuous_matrix_apply k l)).mul continuous_const

theorem nearPart_atomMeasure_eq (F : AtomicHerglotz r) (L : ℝ) (z : ℂ) :
    nearPart (atomMeasure F) L z = ∑ x ∈ F.residue.support,
      (((smoothCutoff L x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) • F.residue x := by
  ext i j
  rw [nearPart_atomMeasure, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]

theorem farPart_eq (F : AtomicHerglotz r) (L : ℝ) (z : ℂ) :
    farPart F L z = F.const + ∑ x ∈ F.residue.support,
      (((1 - smoothCutoff L x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) • F.residue x := by
  ext i j
  rw [farPart_apply, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]

/-- `Im v^*(Σ_x w(x)(x - z)⁻¹ μ({x})) v = Σ_x w(x) (Im z/|x - z|²) v^*μ({x})v`. -/
theorem im_quad_weighted (F : AtomicHerglotz r) (w : ℝ → ℝ) (z : ℂ) (v : Fin r → ℂ) :
    (quad (∑ x ∈ F.residue.support, (((w x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) • F.residue x) v).im =
      ∑ x ∈ F.residue.support, w x * (z.im / Complex.normSq ((x : ℂ) - z)) *
        (quad (F.residue x) v).re := by
  rw [quad_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [quad_smul]
  obtain ⟨him, -⟩ := quad_posSemidef (F.residue_posSemidef x) v
  have hq : quad (F.residue x) v = ((quad (F.residue x) v).re : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  rw [hq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    Complex.im_ofReal_mul, ScalarAtomicHerglotz.im_inv_ofReal_sub]

theorem im_quad_weighted_nonneg (F : AtomicHerglotz r) {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    {z : ℂ} (hz : 0 ≤ z.im) (v : Fin r → ℂ) :
    0 ≤ (quad (∑ x ∈ F.residue.support,
      (((w x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) • F.residue x) v).im := by
  rw [im_quad_weighted]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (mul_nonneg (hw x)
    (div_nonneg hz (Complex.normSq_nonneg _))) (quad_posSemidef (F.residue_posSemidef x) v).2

theorem im_quad_const (F : AtomicHerglotz r) (v : Fin r → ℂ) : (quad F.const v).im = 0 := by
  have := AtomicHerglotz.star_dotProduct_mulVec_ofReal_re F.const_isHermitian v
  unfold quad
  rw [← this, Complex.ofReal_im]

theorem im_quad_nearPart_nonneg (F : AtomicHerglotz r) (L : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    (v : Fin r → ℂ) : 0 ≤ (quad (nearPart (atomMeasure F) L z) v).im := by
  rw [nearPart_atomMeasure_eq]
  exact im_quad_weighted_nonneg F (smoothCutoff_nonneg L) hz v

theorem im_quad_farPart (F : AtomicHerglotz r) (L : ℝ) (z : ℂ) (v : Fin r → ℂ) :
    (quad (farPart F L z) v).im = ∑ x ∈ F.residue.support, (1 - smoothCutoff L x) *
      (z.im / Complex.normSq ((x : ℂ) - z)) * (quad (F.residue x) v).re := by
  rw [farPart_eq, quad_add, Complex.add_im, im_quad_const, zero_add,
    im_quad_weighted F (fun x => 1 - smoothCutoff L x)]

theorem im_quad_farPart_nonneg (F : AtomicHerglotz r) (L : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    (v : Fin r → ℂ) : 0 ≤ (quad (farPart F L z) v).im := by
  rw [im_quad_farPart]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (mul_nonneg (by linarith [smoothCutoff_le_one L x])
    (div_nonneg hz (Complex.normSq_nonneg _))) (quad_posSemidef (F.residue_posSemidef x) v).2

theorem im_quad_farPart_zero (F : AtomicHerglotz r) (L : ℝ) (v : Fin r → ℂ) :
    (quad (farPart F L 0) v).im = 0 := by
  rw [im_quad_farPart]
  simp

theorem quad_eval_sub (F : AtomicHerglotz r) (L : ℝ) (z : ℂ) (v : Fin r → ℂ) :
    quad (farPart F L z) v = quad (F.eval z) v - quad (nearPart (atomMeasure F) L z) v := by
  unfold farPart; rw [quad_sub]

/-- **The imaginary part of the far part is controlled by the escaped mass**: for `Y > 0`,
`n ≥ max(1, 2Y)`, `0 ≤ Im v^* farPart(iY) v ≤ (Σ_k |v_k|)² 8Y tailMass`. -/
theorem im_quad_farPart_le (F : AtomicHerglotz r) {L Y : ℝ} (hY : 0 < Y) (hL1 : 1 ≤ L)
    (hLY : 2 * Y ≤ L) (v : Fin r → ℂ) :
    (quad (farPart F L ((Y : ℂ) * Complex.I)) v).im ≤
      (∑ k, ‖v k‖) ^ 2 * (8 * Y * tailMass F L) := by
  have h0 := im_quad_farPart_zero F L v
  have hdiff : (quad (farPart F L ((Y : ℂ) * Complex.I)) v).im =
      (quad (farPart F L ((Y : ℂ) * Complex.I) - farPart F L 0) v).im := by
    rw [quad_sub, Complex.sub_im, h0, sub_zero]
  rw [hdiff]
  refine (Complex.im_le_norm _).trans ?_
  have hYn : ‖(Y : ℂ) * Complex.I‖ ≤ Y := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  exact norm_quad_le _ _ fun k l => farPart_sub_le F hL1 hLY hYn
    (by rw [norm_zero]; exact hY.le) k l

/-!
## The canonical near quadratic form
-/

/-- A.s. the canonical near quadratic form is `smoothQuadCauchy`. -/
theorem ae_quad_nearPart_canon {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ) (L : ℝ)
    {z : ℂ} (hz : 0 < z.im) (v : Fin r → ℂ) :
    ∀ᵐ ω ∂P, quad (nearPart (canonMeasure (Ξ ω)) L z) v = smoothQuadCauchy (Ξ ω) L v z := by
  obtain ⟨hae, -⟩ := productTest_moments h (continuous_smoothCutoff L)
    (hasCompactSupport_smoothCutoff L) (smoothCutoff_nonneg L) continuous_euclidMark
    euclidMark_nonneg integrable_euclidMark_sq
  filter_upwards [hae] with ω hω
  rw [nearPart_canonMeasure, quad_eq]
  unfold smoothCauchy smoothQuadCauchy
  have hent : ∀ k l : Fin r, Integrable (fun p : ℝ × (Fin r → ℂ) =>
      ((smoothCutoff L p.1 : ℝ) : ℂ) * (((Real.pi : ℂ) * ((p.1 : ℂ) - z))⁻¹ *
        (p.2 k * conj (p.2 l)))) (Ξ ω).measure := by
    intro k l
    refine (hω.const_mul (1 / (Real.pi * z.im))).mono' ?_ (ae_of_all _ fun p => ?_)
    · have h1 : Measurable fun p : ℝ × (Fin r → ℂ) => ((smoothCutoff L p.1 : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp ((continuous_smoothCutoff L).measurable.comp measurable_fst)
      have h2 : Measurable fun p : ℝ × (Fin r → ℂ) => ((Real.pi : ℂ) * ((p.1 : ℂ) - z))⁻¹ :=
        (measurable_const.mul ((Complex.measurable_ofReal.comp measurable_fst).sub
          measurable_const)).inv
      have h3 : Measurable fun p : ℝ × (Fin r → ℂ) => p.2 k * conj (p.2 l) :=
        (((continuous_apply k).comp continuous_snd).mul (Complex.continuous_conj.comp
          ((continuous_apply l).comp continuous_snd))).measurable
      exact (h1.mul (h2.mul h3)).aestronglyMeasurable
    · have hne : (p.1 : ℂ) - z ≠ 0 := ofReal_sub_ne_zero hz.ne'
      have hn : z.im ≤ ‖(p.1 : ℂ) - z‖ := by
        refine le_trans ?_ (Complex.abs_im_le_norm _)
        simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg]
        exact le_abs_self _
      have hkl := norm_mul_norm_le_euclidMark p.2 k l
      have hχ := smoothCutoff_nonneg L p.1
      have hpi := Real.pi_pos
      rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hχ, abs_of_pos hpi, Complex.norm_conj]
      have hinv : (Real.pi * ‖(p.1 : ℂ) - z‖)⁻¹ ≤ 1 / (Real.pi * z.im) := by
        rw [one_div]; exact inv_anti₀ (by positivity) (by gcongr)
      calc smoothCutoff L p.1 * ((Real.pi * ‖(p.1 : ℂ) - z‖)⁻¹ * (‖p.2 k‖ * ‖p.2 l‖))
          ≤ smoothCutoff L p.1 * (1 / (Real.pi * z.im) * euclidMark p.2) := by
            gcongr
        _ = 1 / (Real.pi * z.im) * (smoothCutoff L p.1 * euclidMark p.2) := by ring
  have hsum : ∑ k, ∑ l, conj (v k) * (∫ p, ((smoothCutoff L p.1 : ℝ) : ℂ) *
      (((Real.pi : ℂ) * ((p.1 : ℂ) - z))⁻¹ * (p.2 k * conj (p.2 l))) ∂(Ξ ω).measure) * v l =
      ∫ p, ∑ k, ∑ l, conj (v k) * (((smoothCutoff L p.1 : ℝ) : ℂ) *
        (((Real.pi : ℂ) * ((p.1 : ℂ) - z))⁻¹ * (p.2 k * conj (p.2 l)))) * v l ∂(Ξ ω).measure := by
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      ((hent k l).const_mul _).mul_const _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => ((hent k l).const_mul _).mul_const _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, integral_const_mul]
  rw [hsum]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only
  set w : ℂ := ∑ i, star (v i) * p.2 i with hw
  have hq : ((quadMark v p.2 : ℝ) : ℂ) = w * conj w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    unfold quadMark
    push_cast
    rfl
  have hexp : ∑ k, ∑ l, conj (v k) * (((smoothCutoff L p.1 : ℝ) : ℂ) *
      (((Real.pi : ℂ) * ((p.1 : ℂ) - z))⁻¹ * (p.2 k * conj (p.2 l)))) * v l =
      ((smoothCutoff L p.1 : ℝ) : ℂ) * ((Real.pi : ℂ) * ((p.1 : ℂ) - z))⁻¹ * (w * conj w) := by
    rw [hw, map_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [RCLike.star_def, map_mul, Complex.conj_conj]
    ring
  rw [hexp, ← hq, mul_inv]
  push_cast
  ring

end BlockBand.Critical.Herglotz

module

public import BlockBand.Critical.Herglotz.Tail
public import BlockBand.Critical.Herglotz.Kernel

/-!
# Far parts, polarization and continuity

* `farPart_sub_le`: for `‖z‖, ‖z'‖ ≤ R` and `L ≥ max(1, 2R)`, every entry of
  `farPart F L z - farPart F L z'` is at most `8R tailMass F L` (far-variation kernel
  `norm_inv_sub_sub_inv_le`, and `|ρ_ij| ≤ tr ρ`).
* `norm_apply_le_polarization`: `|M_ij| ≤ ¼ Σ_{c ∈ {1,-1,i,-i}} |v_c^* M v_c|` with
  `v_c = e_i + c e_j` (sesquilinear polarization, any square matrix).
* `norm_quad_le`: `|v^* M v| ≤ (Σ_k |v_k|)² max_kl |M_kl|`.
* `continuousOn_eval` (atomic functions are continuous off the real line) and
  `continuousOn_nearPart` (every near part is continuous on compacts of the open upper
  half-plane, for every measure finite on compacts).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix NNReal ENNReal ComplexOrder ComplexConjugate

namespace BlockBand.Critical.Herglotz

variable {r : ℕ}

/-- The far part `F(z) - near_L(z)`. -/
def farPart (F : AtomicHerglotz r) (L : ℝ) (z : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  F.eval z - nearPart (atomMeasure F) L z

theorem eval_apply (F : AtomicHerglotz r) (z : ℂ) (i j : Fin r) :
    F.eval z i j = F.const i j + ∑ x ∈ F.residue.support, ((x : ℂ) - z)⁻¹ * F.residue x i j := by
  unfold AtomicHerglotz.eval Finsupp.sum
  simp [Matrix.sum_apply]

theorem farPart_apply (F : AtomicHerglotz r) (L : ℝ) (z : ℂ) (i j : Fin r) :
    farPart F L z i j = F.const i j + ∑ x ∈ F.residue.support,
      ((1 - smoothCutoff L x : ℝ) : ℂ) * (((x : ℂ) - z)⁻¹ * F.residue x i j) := by
  unfold farPart
  rw [Matrix.sub_apply, eval_apply, nearPart_atomMeasure, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast
  ring

theorem norm_apply_le_trace {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef) (i j : Fin r) :
    ‖A i j‖ ≤ (Matrix.trace A).re := by
  have h1 := PosSemidef.two_mul_norm_apply_le hA i j
  have hd : ∀ k, (A k k).re ≤ (Matrix.trace A).re := fun k => by
    rw [Matrix.trace, Complex.re_sum]
    exact Finset.single_le_sum (f := fun k => (A.diag k).re)
      (fun l _ => re_diag_nonneg hA l) (Finset.mem_univ k)
  linarith [hd i, hd j]

/-- **The far part is nearly constant on `‖z‖ ≤ R`.** For `L ≥ 1`, `L ≥ 2R`, `‖z‖, ‖z'‖ ≤ R`:
`|farPart F L z - farPart F L z'|_ij ≤ 8R tailMass F L`. -/
theorem farPart_sub_le (F : AtomicHerglotz r) {L R : ℝ} (hL1 : 1 ≤ L) (hLR : 2 * R ≤ L)
    {z z' : ℂ} (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R) (i j : Fin r) :
    ‖farPart F L z i j - farPart F L z' i j‖ ≤ 8 * R * tailMass F L := by
  rw [farPart_apply, farPart_apply, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  unfold tailMass
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  have hχ1 := smoothCutoff_le_one L y
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hz
  have htr := norm_apply_le_trace (F.residue_posSemidef y) i j
  have ht0 := trace_re_nonneg (F.residue_posSemidef y)
  have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  by_cases hy : |y| ≤ L
  · rw [smoothCutoff_eq_one hy]
    simp
  have hy' : L < |y| := not_le.1 hy
  have hk : ∀ w : ℂ, ‖w‖ ≤ R → ‖((y : ℂ) - w)⁻¹ - (y : ℂ)⁻¹‖ ≤ 4 * R / (1 + y ^ 2) := by
    intro w hw
    refine (norm_inv_sub_sub_inv_le (by linarith) (by linarith)).trans ?_
    gcongr
  have hdiff : ‖((y : ℂ) - z)⁻¹ - ((y : ℂ) - z')⁻¹‖ ≤ 8 * R / (1 + y ^ 2) := by
    have := norm_sub_le (((y : ℂ) - z)⁻¹ - (y : ℂ)⁻¹) (((y : ℂ) - z')⁻¹ - (y : ℂ)⁻¹)
    rw [sub_sub_sub_cancel_right] at this
    linarith [hk z hz, hk z' hz', show 8 * R / (1 + y ^ 2) = 4 * R / (1 + y ^ 2) +
      4 * R / (1 + y ^ 2) by ring]
  have heq : ((1 - smoothCutoff L y : ℝ) : ℂ) * (((y : ℂ) - z)⁻¹ * F.residue y i j) -
      ((1 - smoothCutoff L y : ℝ) : ℂ) * (((y : ℂ) - z')⁻¹ * F.residue y i j) =
      ((1 - smoothCutoff L y : ℝ) : ℂ) * ((((y : ℂ) - z)⁻¹ - ((y : ℂ) - z')⁻¹) *
        F.residue y i j) := by ring
  rw [heq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]
  have h1 : 0 ≤ 1 - smoothCutoff L y := by linarith
  calc (1 - smoothCutoff L y) * (‖((y : ℂ) - z)⁻¹ - ((y : ℂ) - z')⁻¹‖ * ‖F.residue y i j‖)
      ≤ (1 - smoothCutoff L y) * (8 * R / (1 + y ^ 2) * (Matrix.trace (F.residue y)).re) := by
        gcongr
    _ = 8 * R * ((1 - smoothCutoff L y) * ((Matrix.trace (F.residue y)).re / (1 + y ^ 2))) := by
        ring

/-!
## Quadratic forms and polarization
-/

/-- `v^* M v`. -/
def quad (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) : ℂ := star v ⬝ᵥ (M *ᵥ v)

theorem quad_eq (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    quad M v = ∑ k, ∑ l, conj (v k) * M k l * v l := by
  unfold quad dotProduct Matrix.mulVec dotProduct
  simp only [Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem quad_sub (M M' : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    quad (M - M') v = quad M v - quad M' v := by
  unfold quad
  rw [Matrix.sub_mulVec, dotProduct_sub]

theorem norm_quad_le (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) {B : ℝ}
    (hB : ∀ k l, ‖M k l‖ ≤ B) : ‖quad M v‖ ≤ (∑ k, ‖v k‖) ^ 2 * B := by
  rw [quad_eq, sq, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have := hB k l
  have hk := norm_nonneg (v k)
  have hl := norm_nonneg (v l)
  nlinarith [mul_nonneg hk hl]

/-- The polarization vectors `e_i + c e_j`. -/
def polVec (i j : Fin r) (c : ℂ) : Fin r → ℂ :=
  (Pi.single i (1 : ℂ) : Fin r → ℂ) + (Pi.single j c : Fin r → ℂ)

theorem sum_norm_polVec_le (i j : Fin r) {c : ℂ} (hc : ‖c‖ = 1) :
    ∑ k, ‖polVec i j c k‖ ≤ 2 := by
  classical
  unfold polVec
  calc ∑ k, ‖((Pi.single i (1 : ℂ) : Fin r → ℂ) + (Pi.single j c : Fin r → ℂ)) k‖
      ≤ ∑ k, (‖(Pi.single i (1 : ℂ) : Fin r → ℂ) k‖ + ‖(Pi.single j c : Fin r → ℂ) k‖) :=
        Finset.sum_le_sum fun k _ => norm_add_le _ _
    _ = 2 := by
        rw [Finset.sum_add_distrib]
        simp only [Pi.single_apply, apply_ite norm, norm_one, norm_zero, hc,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        norm_num

/-- **Polarization**: `4 M_ij = Q(e_i + e_j) - Q(e_i - e_j) - i Q(e_i + i e_j) + i Q(e_i - i e_j)`
for every square matrix, `Q(v) = v^* M v`. -/
theorem polarization (M : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) :
    4 * M i j = quad M (polVec i j 1) - quad M (polVec i j (-1)) -
      Complex.I * quad M (polVec i j Complex.I) + Complex.I * quad M (polVec i j (-Complex.I)) := by
  classical
  have hq : ∀ c : ℂ, quad M (polVec i j c) =
      M i i + c * M i j + conj c * M j i + conj c * c * M j j := by
    intro c
    unfold quad polVec
    have hmv : ∀ (l : Fin r) (y : ℂ) (k : Fin r), (M *ᵥ Pi.single l y) k = M k l * y := by
      intro l y k
      simp [Matrix.mulVec, dotProduct_single]
    have hstar : star ((Pi.single i (1 : ℂ) : Fin r → ℂ) + (Pi.single j c : Fin r → ℂ)) =
        (Pi.single i (1 : ℂ) : Fin r → ℂ) + (Pi.single j (conj c) : Fin r → ℂ) := by
      rw [star_add]
      congr 1
      · ext k; by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · ext k; by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
    rw [hstar]
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct, hmv]
    ring
  rw [hq, hq, hq, hq]
  simp only [map_one, map_neg, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_apply_le_polarization (M : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) :
    ‖M i j‖ ≤ (‖quad M (polVec i j 1)‖ + ‖quad M (polVec i j (-1))‖ +
      ‖quad M (polVec i j Complex.I)‖ + ‖quad M (polVec i j (-Complex.I))‖) / 4 := by
  have h := congrArg norm (polarization M i j)
  rw [norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num] at h
  have h1 := norm_add_le (quad M (polVec i j 1) - quad M (polVec i j (-1)) -
    Complex.I * quad M (polVec i j Complex.I)) (Complex.I * quad M (polVec i j (-Complex.I)))
  have h2 := norm_sub_le (quad M (polVec i j 1) - quad M (polVec i j (-1)))
    (Complex.I * quad M (polVec i j Complex.I))
  have h3 := norm_sub_le (quad M (polVec i j 1)) (quad M (polVec i j (-1)))
  rw [norm_mul, Complex.norm_I, one_mul] at h1 h2
  linarith

/-!
## Continuity
-/

theorem continuousOn_eval (F : AtomicHerglotz r) :
    ContinuousOn F.eval {z : ℂ | 0 < z.im} := by
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  have heq : (fun z => F.eval z i j) = fun z => F.const i j +
      ∑ x ∈ F.residue.support, ((x : ℂ) - z)⁻¹ * F.residue x i j :=
    funext fun z => eval_apply F z i j
  show ContinuousOn (fun z => F.eval z i j) _
  rw [heq]
  refine continuousOn_const.add (continuousOn_finsetSum _ fun x _ => ?_)
  refine ContinuousOn.mul ?_ continuousOn_const
  exact (continuousOn_const.sub continuousOn_id).inv₀ fun z hz =>
    ofReal_sub_ne_zero (ne_of_gt hz)

/-- **Every near part is continuous on compacts of the open upper half-plane.** Measure: any
`ν` on `ℝ × Matrix`. For `K` with `c ≤ Im z` and `‖z‖ ≤ R` on `K` (`c > 0`), `nearPart ν L` is
continuous on `K`: if `χ_L(y) ρ_ij` is `ν`-integrable by domination, otherwise every entry
vanishes identically on `K` (the integrand is never integrable). -/
theorem continuousOn_nearPart (ν : Measure (ℝ × Matrix (Fin r) (Fin r) ℂ)) (L : ℝ) {K : Set ℂ}
    {c R : ℝ} (hc : 0 < c) (hKc : ∀ z ∈ K, c ≤ z.im) (hKR : ∀ z ∈ K, ‖z‖ ≤ R) :
    ContinuousOn (nearPart ν L) K := by
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  show ContinuousOn (fun z => nearPart ν L z i j) K
  have hm1 : Measurable fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => ((smoothCutoff L p.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((continuous_smoothCutoff L).measurable.comp measurable_fst)
  have hm3 : Measurable fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => p.2 i j :=
    (continuous_matrix_apply i j).measurable.comp measurable_snd
  have hmz : ∀ z : ℂ, Measurable fun p : ℝ × Matrix (Fin r) (Fin r) ℂ =>
      ((smoothCutoff L p.1 : ℝ) : ℂ) * (((p.1 : ℂ) - z)⁻¹ * p.2 i j) := fun z =>
    hm1.mul (((Complex.measurable_ofReal.comp measurable_fst).sub measurable_const).inv.mul hm3)
  have hKne : ∀ z ∈ K, z.im ≠ 0 := fun z hz => (lt_of_lt_of_le hc (hKc z hz)).ne'
  by_cases hI : Integrable (fun p : ℝ × Matrix (Fin r) (Fin r) ℂ =>
      ((smoothCutoff L p.1 : ℝ) : ℂ) * p.2 i j) ν
  · have heq : (fun z => nearPart ν L z i j) = fun z => ∫ p, ((smoothCutoff L p.1 : ℝ) : ℂ) *
        (((p.1 : ℂ) - z)⁻¹ * p.2 i j) ∂ν := rfl
    rw [heq]
    have hbI : Integrable (fun p : ℝ × Matrix (Fin r) (Fin r) ℂ =>
        1 / c * ‖((smoothCutoff L p.1 : ℝ) : ℂ) * p.2 i j‖) ν := hI.norm.const_mul _
    refine continuousOn_of_dominated (bound := fun p => 1 / c *
      ‖((smoothCutoff L p.1 : ℝ) : ℂ) * p.2 i j‖) ?_ ?_ ?_ ?_
    · exact fun z _ => (hmz z).aestronglyMeasurable
    · intro z hz
      refine ae_of_all _ fun p => ?_
      rw [norm_mul, norm_mul, norm_mul]
      have hb := norm_inv_ofReal_sub_le (y := p.1) hc (hKc z hz)
      have hn : 0 ≤ ‖((smoothCutoff L p.1 : ℝ) : ℂ)‖ * ‖p.2 i j‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc ‖((smoothCutoff L p.1 : ℝ) : ℂ)‖ * (‖((p.1 : ℂ) - z)⁻¹‖ * ‖p.2 i j‖)
          = ‖((p.1 : ℂ) - z)⁻¹‖ * (‖((smoothCutoff L p.1 : ℝ) : ℂ)‖ * ‖p.2 i j‖) := by ring
        _ ≤ 1 / c * (‖((smoothCutoff L p.1 : ℝ) : ℂ)‖ * ‖p.2 i j‖) :=
          mul_le_mul_of_nonneg_right hb hn
    · exact hbI
    · refine ae_of_all _ fun p => ?_
      refine continuousOn_const.mul (ContinuousOn.mul ?_ continuousOn_const)
      exact (continuousOn_const.sub continuousOn_id).inv₀ fun z hz =>
        ofReal_sub_ne_zero (hKne z hz)
  · have hzero : ∀ z ∈ K, nearPart ν L z i j = 0 := by
      intro z hz
      unfold nearPart
      refine integral_undef fun hzI => hI ?_
      refine (hzI.norm.const_mul (L + 1 + R)).mono' (hm1.mul hm3).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      rw [norm_mul, norm_mul, norm_mul]
      by_cases hp : |p.1| < L + 1
      · have hyz : ‖(p.1 : ℂ) - z‖ ≤ L + 1 + R := by
          refine (norm_sub_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          linarith [hKR z hz]
        have hne : (p.1 : ℂ) - z ≠ 0 := ofReal_sub_ne_zero (hKne z hz)
        have h1 : 1 ≤ (L + 1 + R) * ‖((p.1 : ℂ) - z)⁻¹‖ := by
          rw [norm_inv]
          rw [le_mul_inv_iff₀ (norm_pos_iff.2 hne), one_mul]
          exact hyz
        have ha := norm_nonneg ((smoothCutoff L p.1 : ℝ) : ℂ)
        have hb := norm_nonneg (p.2 i j)
        calc ‖((smoothCutoff L p.1 : ℝ) : ℂ)‖ * ‖p.2 i j‖
            ≤ ‖((smoothCutoff L p.1 : ℝ) : ℂ)‖ * ‖p.2 i j‖ * ((L + 1 + R) *
                ‖((p.1 : ℂ) - z)⁻¹‖) := le_mul_of_one_le_right (mul_nonneg ha hb) h1
          _ = (L + 1 + R) * (‖((smoothCutoff L p.1 : ℝ) : ℂ)‖ *
                (‖((p.1 : ℂ) - z)⁻¹‖ * ‖p.2 i j‖)) := by ring
      · rw [smoothCutoff_eq_zero (not_lt.1 hp)]
        simp
    exact (continuousOn_const (c := (0 : ℂ))).congr fun z hz => hzero z hz

end BlockBand.Critical.Herglotz

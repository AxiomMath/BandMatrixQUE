module

public import BlockBand.DeterminantScore.MinorTailRow

/-!
# Row restoration with the insertion `q_B^{-r}` at fixed outer data

**`corner_gue`**: for Hermitian `K` on `Fin m`, `m = k + 1`, a unit eigenvector `w` of `K`
(`Kw = μw`), an orthonormal frame `V` of `w^⊥`, `G ~ GUE_m(t)`, `t > 0`, `0 < r < 2`, `n, α ∈ ℕ`,
with `M = K + G`, `B = V*MV`, `q_B² = (μ - t Tr B⁻¹)² + t + t² Tr B⁻²`:
`E[det(M)² 1{N_-(M) + n = α} |w*M⁻¹w|^r]
   ≤ Σ_{ℓ ∈ {α-1, α, α+1}} E[det(M)² 1{N_-(M) + n = ℓ} q_B^{-r}]`.

Proof: the rotation and row/minor splitting of `gue_tail`; at a fixed invertible minor,
`(M⁻¹)₀₀ = a⁻¹` (`rowMatrix_inv_corner`, Schur complement), `det(M)² = det(B)²a²`, so the selected
numerator is at most `det(B)²|a|^{2-r}`; Jensen (`lintegral_rpow_le`, concave power `1 - r/2`) and
`E_{x,y}a² = q_B²` (`SignedRowSpread.signedRowSpread`) give `det(B)²q_B^{2-r} = q_B^{-r}E_{x,y}det(M)²`,
and on an attained sector every row value lies in a neighbouring sector
(`PhysicalColumn.sector_neighbour`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.ScoreMoments

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.GaussianGradient BlockBand.DeterminantScore.PhysicalColumn
open BlockBand.DeterminantScore.MinorTail
open scoped NNReal ENNReal

variable {k : ℕ}

/-!
## Jensen for a concave power
-/

/-- Jensen for the concave power `x ↦ x^p`, `0 < p < 1`, under a probability measure. -/
theorem lintegral_rpow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → ℝ≥0∞} (hF : AEMeasurable F P) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∫⁻ x, F x ^ p ∂P) ≤ (∫⁻ x, F x ∂P) ^ p := by
  have hpq : (1 / p).HolderConjugate (1 / (1 - p)) :=
    Real.holderConjugate_one_div hp0 (by linarith) (by ring)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq (hF.pow_const p)
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  have e1 : ∀ x, (F x ^ p) ^ (1 / p) = F x := fun x => by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  simp only [e1, one_div_one_div] at h
  exact h

/-!
## The corner of the inverse row matrix
-/

theorem unit_inv_apply (S : Matrix Unit Unit ℂ) (hS : S () () ≠ 0) :
    S⁻¹ () () = (S () ())⁻¹ := by
  have hdet : IsUnit S.det := by rw [Matrix.det_unique]; exact isUnit_iff_ne_zero.mpr hS
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul S hdet) ()) ()
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq] at h
  exact eq_inv_of_mul_eq_one_left h

/-- `(M⁻¹)₀₀ = a⁻¹` for `M = [[μ + x, y*], [y, B]]`, `B` invertible Hermitian, `a = μ + x - y*B⁻¹y`
(both sides vanish when `a = 0`). -/
theorem rowMatrix_inv_corner (μ x : ℝ) (y : Fin k → ℂ) {B : Matrix (Fin k) (Fin k) ℂ}
    (hB : B.IsHermitian) (hdet : B.det ≠ 0) :
    (rowMatrix μ x y B)⁻¹ (Sum.inl ()) (Sum.inl ()) = (((rowSchur μ B (x, y))⁻¹ : ℝ) : ℂ) := by
  by_cases ha : rowSchur μ B (x, y) = 0
  · have hd : (rowMatrix μ x y B).det = 0 := by
      have h := det_rowMatrix μ x y hB hdet
      rw [ha] at h
      simpa using h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hd]; exact not_isUnit_zero), ha]
    simp
  let _ : Invertible B := B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hdet)
  set S : Matrix Unit Unit ℂ := Matrix.of (fun (_ : Unit) (_ : Unit) => ((μ + x : ℝ) : ℂ)) -
      Matrix.of (fun (_ : Unit) j => star (y j)) * ⅟B * Matrix.of (fun j (_ : Unit) => y j)
    with hSdef
  have hq := SignedRowSpread.quad_im_eq_zero B⁻¹ hB.inv y
  have hS00 : S () () = ((rowSchur μ B (x, y) : ℝ) : ℂ) := by
    have he : S () () = ((μ + x : ℝ) : ℂ) - star y ⬝ᵥ (B⁻¹ *ᵥ y) := by
      simp only [hSdef, Matrix.invOf_eq_nonsing_inv]
      simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    rw [he]
    apply Complex.ext
    · simp [rowSchur]
    · simp [rowSchur, hq]
  have hS0 : S () () ≠ 0 := by rw [hS00]; exact_mod_cast ha
  let _ : Invertible S := S.invertibleOfIsUnitDet (by
    rw [Matrix.det_unique]; exact isUnit_iff_ne_zero.mpr hS0)
  let _ : Invertible (rowMatrix μ x y B) := fromBlocks₂₂Invertible _ _ _ _
  rw [← Matrix.invOf_eq_nonsing_inv]
  unfold rowMatrix
  rw [invOf_fromBlocks₂₂_eq, fromBlocks_apply₁₁, Matrix.invOf_eq_nonsing_inv (A := S)]
  rw [unit_inv_apply S hS0, hS00]
  push_cast
  rfl

/-!
## The restored row at a fixed minor
-/

/-- The corner integrand `det(M)² 1{sector α} |(M⁻¹)₀₀|^r`. -/
def cornerInt (n α : ℕ) (r : ℝ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (secW n α M) * ENNReal.ofReal (‖M⁻¹ 0 0‖ ^ r)

/-- `q_B² = (μ - t Tr B⁻¹)² + t + t² Tr B⁻²`. -/
def qMinorSq (t μ : ℝ) {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℂ) : ℝ :=
  (μ - t * B⁻¹.trace.re) ^ 2 + t + t ^ 2 * invSq B

/-- The restored integrand `Σ_{ℓ=α-1}^{α+1} det(M)² 1{sector ℓ} · q_B^{-r}`, `B` the minor on
`1, …, k`. -/
def restoreInt (n α : ℕ) (t μ r : ℝ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal (secW n (α - 1) M) + ENNReal.ofReal (secW n α M) +
      ENNReal.ofReal (secW n (α + 1) M)) *
    ENNReal.ofReal (qMinorSq t μ (M.submatrix Fin.succ Fin.succ) ^ (-(r / 2)))

theorem measurable_qMinorSq (t μ : ℝ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    Measurable (qMinorSq (κ := κ) t μ) := by
  unfold qMinorSq
  have h1 : Measurable fun B : Matrix κ κ ℂ => B⁻¹.trace.re :=
    Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp measurable_inv_matrix)
  exact (((measurable_const.sub (measurable_const.mul h1)).pow_const 2).add measurable_const).add
    (measurable_const.mul measurable_invSq)

theorem measurable_cornerInt (n α : ℕ) (r : ℝ) : Measurable (cornerInt (k := k) n α r) := by
  unfold cornerInt
  have h : Measurable fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ => M⁻¹ 0 0 :=
    ExactScore.measurable_inv_apply 0 0
  exact (ENNReal.measurable_ofReal.comp (measurable_secW n α)).mul
    (ENNReal.measurable_ofReal.comp (h.norm.pow_const r))

theorem measurable_restoreInt (n α : ℕ) (t μ r : ℝ) :
    Measurable (restoreInt (k := k) n α t μ r) := by
  unfold restoreInt
  have hS : ∀ ℓ, Measurable fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ =>
      ENNReal.ofReal (secW n ℓ M) := fun ℓ => ENNReal.measurable_ofReal.comp (measurable_secW n ℓ)
  exact (((hS _).add (hS _)).add (hS _)).mul (ENNReal.measurable_ofReal.comp
    (((measurable_qMinorSq t μ).comp (continuous_id.matrix_submatrix _ _).measurable).pow_const _))

theorem sq_mul_inv_rpow_le {a r : ℝ} :
    a ^ 2 * (|a|⁻¹) ^ r ≤ |a| ^ (2 - r) := by
  by_cases ha : a = 0
  · subst ha; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      abs_zero]
    exact Real.rpow_nonneg le_rfl _
  have hpos : 0 < |a| := abs_pos.mpr ha
  rw [Real.inv_rpow hpos.le, ← sq_abs, Real.rpow_sub hpos, ← Real.rpow_natCast]
  push_cast
  rw [div_eq_mul_inv]

theorem abs_rpow_eq_sq_rpow (a r : ℝ) : |a| ^ (2 - r) = (a ^ 2) ^ (1 - r / 2) := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg a)]
  congr 1; push_cast; ring

/-- **Row restoration with the insertion `q_B^{-r}` at a fixed invertible minor.** -/
theorem corner_restore_fixed {K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hK : K.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) (μ : ℝ) (h00 : K 0 0 = μ) (h0j : ∀ j : Fin k, K 0 j.succ = 0)
    (hj0 : ∀ j : Fin k, K j.succ 0 = 0) (n α : ℕ) {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2)
    (w : RestIdx (k + 1) → ℝ)
    (hw : (K.submatrix Fin.succ Fin.succ + hermOfCoord (restVal t w)).det ≠ 0) :
    (∫⁻ u, cornerInt n α r (K + hermOfCoord (rowPoint (hermSd (k + 1) t) u w))
        ∂standardGaussianCoordinates (ι := RowIdx (k + 1))) ≤
      ∫⁻ u, restoreInt n α t μ r (K + hermOfCoord (rowPoint (hermSd (k + 1) t) u w))
        ∂standardGaussianCoordinates (ι := RowIdx (k + 1)) := by
  set σ := hermSd (k + 1) t
  set Mu := fun u : RowIdx (k + 1) → ℝ => K + hermOfCoord (rowPoint σ u w) with hMudef
  set B := K.submatrix Fin.succ Fin.succ + hermOfCoord (restVal t w) with hBdef
  set R := fun z : ℝ × (Fin k → ℂ) => rowMatrix μ z.1 z.2 B with hRdef
  have hBH : B.IsHermitian := by
    refine IsHermitian.add ?_ (isHermitian_hermOfCoord _)
    exact hK.submatrix _
  have hMuH : ∀ u, (Mu u).IsHermitian := fun u => hK.add (isHermitian_hermOfCoord _)
  have hMu : ∀ u, Mu u = (R (rowVal σ u)).submatrix (finSplit k) (finSplit k) :=
    fun u => row_block_eq K μ h00 h0j hj0 t u w
  have hminor : ∀ u, (Mu u).submatrix Fin.succ Fin.succ = B := by
    intro u
    rw [hMu u]
    ext a b
    simp [R, rowMatrix, finSplit]
  change (∫⁻ u, cornerInt n α r (Mu u) ∂standardGaussianCoordinates (ι := RowIdx (k + 1))) ≤
    ∫⁻ u, restoreInt n α t μ r (Mu u) ∂standardGaussianCoordinates (ι := RowIdx (k + 1))
  by_cases hatt : ∃ u₀, negativeCount (Mu u₀) + n = α
  swap
  · simp only [not_exists] at hatt
    refine le_trans (le_of_eq ?_) (zero_le)
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun u => ?_)
    simp [cornerInt, secW, hatt u]
  obtain ⟨u₀, hu₀⟩ := hatt
  -- the row second moment at the minor `B`
  have hS := SignedRowSpread.signedRowSpread k t μ B ht hBH hw
  dsimp only at hS
  obtain ⟨h1, -, -, -, -⟩ := hS
  set q2 := qMinorSq (t : ℝ) μ B with hq2
  have hV0 : 0 ≤ invSq B := invSq_nonneg hBH
  have htpos : (0 : ℝ) < t := ht
  have hq2pos : 0 < q2 := by unfold q2 qMinorSq; positivity
  have h1' : (∫ z, rowSchur μ B z ^ 2 ∂rowLaw k t) = q2 := by rw [h1]; rfl
  have hint1 : Integrable (fun z => rowSchur μ B z ^ 2) (rowLaw k t) := by
    by_contra hni
    rw [integral_undef hni] at h1'
    linarith
  have hlin1 : (∫⁻ z, ENNReal.ofReal (rowSchur μ B z ^ 2) ∂rowLaw k t) = ENNReal.ofReal q2 := by
    rw [← h1', ofReal_integral_eq_lintegral_ofReal hint1 (ae_of_all _ fun z => sq_nonneg _)]
  have : IsProbabilityMeasure (circularVectorLaw (Fin k)) := by
    unfold circularVectorLaw
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop : Continuous fun (r : Fin k × Fin 2 → ℝ) (a : Fin k) =>
      (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I).measurable.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (rowLaw k t) := by
    unfold rowLaw
    have : IsProbabilityMeasure ((circularVectorLaw (Fin k)).map
        fun g => (Real.sqrt (t : ℝ) : ℂ) • g) :=
      (Measure.isProbabilityMeasure_map_iff (by fun_prop : Continuous fun g : Fin k → ℂ =>
        (Real.sqrt (t : ℝ) : ℂ) • g).measurable.aemeasurable).mpr inferInstance
    infer_instance
  set p₀ : ℝ := 1 - r / 2 with hp₀
  have hp0 : 0 < p₀ := by rw [hp₀]; linarith
  have hp1 : p₀ < 1 := by rw [hp₀]; linarith
  have hRc := continuous_rowMatrix μ B
  have hac := SignedRowSpread.continuous_rowSchur μ B
  have hjen : (∫⁻ z, ENNReal.ofReal (|rowSchur μ B z| ^ (2 - r)) ∂rowLaw k t) ≤
      ENNReal.ofReal (q2 ^ p₀) := by
    have hm : AEMeasurable (fun z => ENNReal.ofReal (rowSchur μ B z ^ 2)) (rowLaw k t) :=
      (ENNReal.measurable_ofReal.comp (hac.measurable.pow_const 2)).aemeasurable
    have hj := lintegral_rpow_le hm hp0 hp1
    rw [hlin1, ENNReal.ofReal_rpow_of_nonneg hq2pos.le hp0.le] at hj
    refine le_trans (le_of_eq ?_) hj
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) hp0.le, abs_rpow_eq_sq_rpow]
  -- transport between the row coordinates and the row law
  have hdetR : ∀ z : ℝ × (Fin k → ℂ), Complex.normSq (R z).det =
      Complex.normSq B.det * rowSchur μ B z ^ 2 := fun z => det_rowMatrix μ z.1 z.2 hBH hw
  have hnB : 0 ≤ Complex.normSq B.det := Complex.normSq_nonneg _
  have hmG2 : Measurable fun z : ℝ × (Fin k → ℂ) => ENNReal.ofReal (Complex.normSq (R z).det) :=
    ENNReal.measurable_ofReal.comp
      ((Complex.continuous_normSq.comp (continuous_id.matrix_det)).comp hRc).measurable
  have hmA : Measurable fun z : ℝ × (Fin k → ℂ) =>
      ENNReal.ofReal (Complex.normSq B.det * |rowSchur μ B z| ^ (2 - r)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((hac.measurable.abs).pow_const _))
  have htr2 : (∫⁻ u, ENNReal.ofReal (Complex.normSq (Mu u).det)
      ∂standardGaussianCoordinates (ι := RowIdx (k + 1))) =
      ∫⁻ z, ENNReal.ofReal (Complex.normSq (R z).det) ∂rowLaw k t := by
    rw [← rowLaw_eq_std, lintegral_map hmG2 (measurable_rowVal σ)]
    refine lintegral_congr fun u => ?_
    rw [hMu u, det_submatrix_equiv_self]
  have htrA : (∫⁻ u, ENNReal.ofReal (Complex.normSq B.det *
        |rowSchur μ B (rowVal σ u)| ^ (2 - r))
      ∂standardGaussianCoordinates (ι := RowIdx (k + 1))) =
      ∫⁻ z, ENNReal.ofReal (Complex.normSq B.det * |rowSchur μ B z| ^ (2 - r)) ∂rowLaw k t := by
    rw [← rowLaw_eq_std, lintegral_map hmA (measurable_rowVal σ)]
  -- the pointwise bound on the selected numerator
  have hstep1 : ∀ u, cornerInt n α r (Mu u) ≤
      ENNReal.ofReal (Complex.normSq B.det * |rowSchur μ B (rowVal σ u)| ^ (2 - r)) := by
    intro u
    set z := rowVal σ u
    have hinv : (Mu u)⁻¹ 0 0 = (((rowSchur μ B z)⁻¹ : ℝ) : ℂ) := by
      rw [hMu u, inv_submatrix_equiv]
      simp only [submatrix_apply]
      have e0 : finSplit k 0 = Sum.inl () := rfl
      rw [e0]
      exact rowMatrix_inv_corner μ z.1 z.2 hBH hw
    have hdet : Complex.normSq (Mu u).det = Complex.normSq B.det * rowSchur μ B z ^ 2 := by
      rw [hMu u, det_submatrix_equiv_self]; exact hdetR z
    unfold cornerInt
    rw [hinv, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      ← ENNReal.ofReal_mul (secW_nonneg _ _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsec : secW n α (Mu u) ≤ Complex.normSq B.det * rowSchur μ B z ^ 2 := by
      rw [← hdet]; unfold secW
      split_ifs
      · rw [mul_one]
      · rw [mul_zero]; exact Complex.normSq_nonneg _
    calc secW n α (Mu u) * (|rowSchur μ B z|⁻¹) ^ r
        ≤ Complex.normSq B.det * rowSchur μ B z ^ 2 * (|rowSchur μ B z|⁻¹) ^ r :=
          mul_le_mul_of_nonneg_right hsec (Real.rpow_nonneg (inv_nonneg.mpr (abs_nonneg _)) _)
      _ = Complex.normSq B.det * (rowSchur μ B z ^ 2 * (|rowSchur μ B z|⁻¹) ^ r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left sq_mul_inv_rpow_le hnB
  have hstep3 : ∀ u, ENNReal.ofReal (Complex.normSq (Mu u).det) ≤
      ENNReal.ofReal (secW n (α - 1) (Mu u)) + ENNReal.ofReal (secW n α (Mu u)) +
        ENNReal.ofReal (secW n (α + 1) (Mu u)) := by
    intro u
    have hagree := hermOfCoord_row_agree K 0 (y := rowPoint σ u₀ w)
      (y' := rowPoint σ u w) (fun c h1 h2 => by
        have hc : ¬ IsRow c := by unfold IsRow; tauto
        simp only [rowPoint, hc, ↓reduceDIte])
    rcases sector_neighbour (hMuH u₀) (hMuH u) 0 hagree hu₀ with h | h | h
    · refine le_trans ?_ (le_add_right (le_add_right le_rfl))
      simp [secW, h]
    · refine le_trans ?_ (le_add_right (le_add_left le_rfl))
      simp [secW, h]
    · refine le_trans ?_ (le_add_left le_rfl)
      simp [secW, h]
  have hrest : ∀ u, restoreInt n α t μ r (Mu u) =
      (ENNReal.ofReal (secW n (α - 1) (Mu u)) + ENNReal.ofReal (secW n α (Mu u)) +
        ENNReal.ofReal (secW n (α + 1) (Mu u))) * ENNReal.ofReal (q2 ^ (-(r / 2))) := by
    intro u; unfold restoreInt; rw [hminor u]
  have hpow : q2 ^ p₀ = q2 ^ (-(r / 2)) * q2 := by
    rw [hp₀, show 1 - r / 2 = -(r / 2) + 1 by ring, Real.rpow_add hq2pos, Real.rpow_one]
  calc (∫⁻ u, cornerInt n α r (Mu u) ∂standardGaussianCoordinates (ι := RowIdx (k + 1)))
      ≤ ∫⁻ u, ENNReal.ofReal (Complex.normSq B.det * |rowSchur μ B (rowVal σ u)| ^ (2 - r))
          ∂standardGaussianCoordinates (ι := RowIdx (k + 1)) := lintegral_mono hstep1
    _ = ENNReal.ofReal (Complex.normSq B.det) *
          ∫⁻ z, ENNReal.ofReal (|rowSchur μ B z| ^ (2 - r)) ∂rowLaw k t := by
        rw [htrA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        rw [← ENNReal.ofReal_mul hnB]
    _ ≤ ENNReal.ofReal (Complex.normSq B.det) * ENNReal.ofReal (q2 ^ p₀) := by gcongr
    _ = ENNReal.ofReal (q2 ^ (-(r / 2))) *
          (ENNReal.ofReal (Complex.normSq B.det) * ENNReal.ofReal q2) := by
        rw [hpow, ENNReal.ofReal_mul (Real.rpow_nonneg hq2pos.le _)]
        ring
    _ = ENNReal.ofReal (q2 ^ (-(r / 2))) *
          ∫⁻ u, ENNReal.ofReal (Complex.normSq (Mu u).det)
            ∂standardGaussianCoordinates (ι := RowIdx (k + 1)) := by
        rw [htr2, ← hlin1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        refine lintegral_congr fun z => ?_
        rw [← ENNReal.ofReal_mul hnB, hdetR z]
    _ ≤ ENNReal.ofReal (q2 ^ (-(r / 2))) *
          ∫⁻ u, (ENNReal.ofReal (secW n (α - 1) (Mu u)) + ENNReal.ofReal (secW n α (Mu u)) +
            ENNReal.ofReal (secW n (α + 1) (Mu u)))
            ∂standardGaussianCoordinates (ι := RowIdx (k + 1)) := by
        gcongr with u; exact hstep3 u
    _ = ∫⁻ u, restoreInt n α t μ r (Mu u) ∂standardGaussianCoordinates (ι := RowIdx (k + 1)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun u => ?_
        rw [hrest u, mul_comm]

/-- **Row restoration with insertion `q_B^{-r}` in the coordinates of `G_{k+1}(t)`** (`K` block
diagonal in `e₀`). -/
theorem corner_coord {K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hK : K.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) (μ : ℝ) (h00 : K 0 0 = μ) (h0j : ∀ j : Fin k, K 0 j.succ = 0)
    (hj0 : ∀ j : Fin k, K j.succ 0 = 0) (n α : ℕ) {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) :
    (∫⁻ y, cornerInt n α r (K + hermOfCoord y) ∂hermGaussian (k + 1) t) ≤
      ∫⁻ y, restoreInt n α t μ r (K + hermOfCoord y) ∂hermGaussian (k + 1) t := by
  have hcont : Continuous fun y : HermCoord (k + 1) → ℝ => K + hermOfCoord y :=
    continuous_const.add continuous_hermOfCoord
  have hmL : Measurable fun y : HermCoord (k + 1) → ℝ => cornerInt n α r (K + hermOfCoord y) :=
    (measurable_cornerInt n α r).comp hcont.measurable
  have hmR : Measurable fun y : HermCoord (k + 1) → ℝ =>
      restoreInt n α t μ r (K + hermOfCoord y) :=
    (measurable_restoreInt n α t μ r).comp hcont.measurable
  rw [lintegral_hermGaussian_row t _ hmL, lintegral_hermGaussian_row t _ hmR]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_minor_det_ne_zero ht (K.submatrix Fin.succ Fin.succ)] with w hw
  exact corner_restore_fixed hK ht μ h00 h0j hj0 n α hr0 hr2 w hw

/-!
## Rotation of the eigenvector to `e₀`
-/

/-- `det(X)² 1{sector α} |w*X⁻¹w|^r`. -/
def cornerW {m : ℕ} (w : Fin m → ℂ) (n α : ℕ) (r : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (secW n α X) * ENNReal.ofReal (‖star w ⬝ᵥ (X⁻¹ *ᵥ w)‖ ^ r)

/-- `Σ_{ℓ=α-1}^{α+1} det(X)² 1{sector ℓ} · q_B^{-r}`, `B = V*XV`. -/
def restoreW {m k : ℕ} (V : Matrix (Fin m) (Fin k) ℂ) (n α : ℕ) (t μ r : ℝ)
    (X : Matrix (Fin m) (Fin m) ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal (secW n (α - 1) X) + ENNReal.ofReal (secW n α X) +
      ENNReal.ofReal (secW n (α + 1) X)) *
    ENNReal.ofReal (qMinorSq t μ (Vᴴ * X * V) ^ (-(r / 2)))

theorem measurable_cornerW {m : ℕ} (w : Fin m → ℂ) (n α : ℕ) (r : ℝ) :
    Measurable (cornerW w n α r) := by
  unfold cornerW
  have h : Measurable fun X : Matrix (Fin m) (Fin m) ℂ => star w ⬝ᵥ (X⁻¹ *ᵥ w) := by
    have hc : Continuous fun Y : Matrix (Fin m) (Fin m) ℂ => star w ⬝ᵥ (Y *ᵥ w) := by
      unfold dotProduct mulVec dotProduct; fun_prop
    exact hc.measurable.comp measurable_inv_matrix
  exact (ENNReal.measurable_ofReal.comp (measurable_secW n α)).mul
    (ENNReal.measurable_ofReal.comp (h.norm.pow_const r))

theorem measurable_restoreW {m k : ℕ} (V : Matrix (Fin m) (Fin k) ℂ) (n α : ℕ) (t μ r : ℝ) :
    Measurable (restoreW V n α t μ r) := by
  unfold restoreW
  have hS : ∀ ℓ, Measurable fun X : Matrix (Fin m) (Fin m) ℂ =>
      ENNReal.ofReal (secW n ℓ X) := fun ℓ => ENNReal.measurable_ofReal.comp (measurable_secW n ℓ)
  have hc : Continuous fun X : Matrix (Fin m) (Fin m) ℂ => Vᴴ * X * V :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact (((hS _).add (hS _)).add (hS _)).mul (ENNReal.measurable_ofReal.comp
    (((measurable_qMinorSq t μ).comp hc.measurable).pow_const _))

theorem frameCompletion_mulVec_single (w : Fin (k + 1) → ℂ) (V : Matrix (Fin (k + 1)) (Fin k) ℂ) :
    frameCompletion w V *ᵥ Pi.single 0 1 = w := by
  ext a
  simp [frameCompletion, mulVec, dotProduct, Pi.single_apply]

theorem frameCompletion_conj_mulVec {w : Fin (k + 1) → ℂ} {V : Matrix (Fin (k + 1)) (Fin k) ℂ}
    (hF : (frameCompletion w V)ᴴ * frameCompletion w V = 1) :
    (frameCompletion w V)ᴴ *ᵥ w = Pi.single 0 1 := by
  rw [show (frameCompletion w V)ᴴ *ᵥ w =
      (frameCompletion w V)ᴴ *ᵥ (frameCompletion w V *ᵥ Pi.single 0 1) by
    rw [frameCompletion_mulVec_single], mulVec_mulVec, hF, one_mulVec]

theorem cornerW_conj {w : Fin (k + 1) → ℂ} {V : Matrix (Fin (k + 1)) (Fin k) ℂ}
    (hF : (frameCompletion w V)ᴴ * frameCompletion w V = 1) (n α : ℕ) (r : ℝ)
    {Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hY : Y.IsHermitian) :
    cornerW w n α r (frameCompletion w V * Y * (frameCompletion w V)ᴴ) = cornerInt n α r Y := by
  set F := frameCompletion w V
  have hF' : (Fᴴ)ᴴ * Fᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hF
  have e1 : F * Y * Fᴴ = (Fᴴ)ᴴ * Y * Fᴴ := by rw [conjTranspose_conjTranspose]
  have hcorner : star w ⬝ᵥ ((F * Y * Fᴴ)⁻¹ *ᵥ w) = Y⁻¹ 0 0 := by
    rw [e1, inv_unitary_conj _ hF', conjTranspose_conjTranspose, ← mulVec_mulVec,
      frameCompletion_conj_mulVec hF, ← mulVec_mulVec, dotProduct_mulVec]
    have hs : star w ᵥ* F = star ((Fᴴ) *ᵥ w) := by
      rw [star_mulVec, conjTranspose_conjTranspose]
    rw [hs, frameCompletion_conj_mulVec hF]
    simp [dotProduct, mulVec, Pi.single_apply]
  unfold cornerW cornerInt
  rw [hcorner, e1, secW_unitary_conj hY hF']

theorem restoreW_conj {w : Fin (k + 1) → ℂ} {V : Matrix (Fin (k + 1)) (Fin k) ℂ}
    (hF : (frameCompletion w V)ᴴ * frameCompletion w V = 1) (n α : ℕ) (t μ r : ℝ)
    {Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hY : Y.IsHermitian) :
    restoreW V n α t μ r (frameCompletion w V * Y * (frameCompletion w V)ᴴ) =
      restoreInt n α t μ r Y := by
  set F := frameCompletion w V
  have hF' : (Fᴴ)ᴴ * Fᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hF
  have e1 : F * Y * Fᴴ = (Fᴴ)ᴴ * Y * Fᴴ := by rw [conjTranspose_conjTranspose]
  have e2 : Vᴴ * (F * Y * Fᴴ) * V = Y.submatrix Fin.succ Fin.succ := by
    rw [← frameCompletion_succ w V]
    congr 1
    simp only [F, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (frameCompletion w V)ᴴ, hF, Matrix.one_mul]
    rw [Matrix.mul_one]
  unfold restoreW restoreInt
  rw [e2, e1, secW_unitary_conj hY hF', secW_unitary_conj hY hF', secW_unitary_conj hY hF']

/-- **Fixed-`θ` corner restoration under `GUE`.** For Hermitian `K` with a unit eigenvector `w`
(eigenvalue `μ`) and an orthonormal frame `V` of `w^⊥`, `0 < r < 2`: the selected numerator of
`|w*M⁻¹w|^r` is at most the three neighbouring sector numerators of `q_B^{-r}`, `B = V*MV`. -/
theorem corner_gue {m k : ℕ} (hmk : m = k + 1) {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) {w : Fin m → ℂ} (hw : l2Norm w = 1) {μ : ℝ}
    (hKw : K *ᵥ w = (μ : ℂ) • w) {V : Matrix (Fin m) (Fin k) ℂ} (hV : Vᴴ * V = 1)
    (hVw : Vᴴ *ᵥ w = 0) (n α : ℕ) {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) :
    (∫⁻ G, cornerW w n α r (K + G) ∂gueMeasure (Fin m) t) ≤
      ∫⁻ G, restoreW V n α t μ r (K + G) ∂gueMeasure (Fin m) t := by
  subst hmk
  set F := frameCompletion w V
  have hF : Fᴴ * F = 1 := frameCompletion_unitary hw hV hVw
  have hF' : (Fᴴ)ᴴ * Fᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hF
  set K' := Fᴴ * K * F
  have hK' : K'.IsHermitian := isHermitian_conjTranspose_mul_mul F hK
  obtain ⟨h00, h0j, hj0⟩ := frameCompletion_block hK hw hKw (V := V) hVw
  have hconj : ∀ G, K + (Fᴴ)ᴴ * G * Fᴴ = F * (K' + G) * Fᴴ := by
    intro G
    rw [conjTranspose_conjTranspose]
    simp only [K', Matrix.mul_add, Matrix.add_mul]
    congr 1
    have hFF : F * Fᴴ = 1 := mul_eq_one_comm.mp hF
    rw [show F * (Fᴴ * K * F) * Fᴴ = (F * Fᴴ) * K * (F * Fᴴ) by simp only [Matrix.mul_assoc],
      hFF, Matrix.one_mul, Matrix.mul_one]
  have hmL : Measurable fun G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ => cornerW w n α r (K + G) :=
    (measurable_cornerW w n α r).comp (measurable_const_add K)
  have hmR : Measurable fun G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ =>
      restoreW V n α t μ r (K + G) :=
    (measurable_restoreW V n α t μ r).comp (measurable_const_add K)
  have hL : (∫⁻ G, cornerW w n α r (K + G) ∂gueMeasure (Fin (k + 1)) t) =
      ∫⁻ y, cornerInt n α r (K' + hermOfCoord y) ∂hermGaussian (k + 1) t := by
    rw [← map_hermOfCoord_hermGaussian, lintegral_map hmL continuous_hermOfCoord.measurable,
      ← lintegral_hermGaussian_unitary t hF' _ hmL]
    refine lintegral_congr fun y => ?_
    rw [hconj, cornerW_conj hF n α r (hK'.add (isHermitian_hermOfCoord y))]
  have hR : (∫⁻ G, restoreW V n α t μ r (K + G) ∂gueMeasure (Fin (k + 1)) t) =
      ∫⁻ y, restoreInt n α t μ r (K' + hermOfCoord y) ∂hermGaussian (k + 1) t := by
    rw [← map_hermOfCoord_hermGaussian, lintegral_map hmR continuous_hermOfCoord.measurable,
      ← lintegral_hermGaussian_unitary t hF' _ hmR]
    refine lintegral_congr fun y => ?_
    rw [hconj, restoreW_conj hF n α t μ r (hK'.add (isHermitian_hermOfCoord y))]
  rw [hL, hR]
  exact corner_coord hK' ht μ h00 h0j hj0 n α hr0 hr2

end BlockBand.DeterminantScore.ScoreMoments

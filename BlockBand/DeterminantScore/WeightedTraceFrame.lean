module

public import BlockBand.DeterminantScore.RealLoop
public import BlockBand.DeterminantScore.MinorTailInverseBad
public import BlockBand.DeterminantScore.PairRowMoment
public import BlockBand.DeterminantScore.ScoreUnsmoothing

/-!
# Frame identities at the reconstructed Gaussian

At outer data `θ = (ω, E, v)` with unit `v`, a pair frame `U` and `G'` with `M = K + G'`
invertible, let `G_d` be the reconstructed Gaussian, `A = F(E) + G_d - E = K₀ + G_d` and
`R_A = U_v M⁻¹ U_v*` (the inverse `R` embedded by zero on `v`, so the zero eigenvalue of `A` contributes zero).
* `frame_complete`: `U_vU_v* + vv* = 1` (completeness of `[U_v | v]`).
* `schurA_rec_eq`: `A = U_v M U_v*`; `isMoorePenrose_frame`: `R_A = A⁺`.
* `weightedTraceError_eq`: `Tr G'R - sE Tr R - (sd - 1) = d(1 - s) - Re Tr (K₀ + sE) R_A`,
  `d = 2W` (from `Tr G'R = (d - 1) - Tr KR`).
* `trace_decomp`: `Tr (K₀ + sE)R_A = Tr (K₀ - g₀)(R_A - Re R_η) + Tr (K₀ - g₀) Re R_η
  + (g₀ + sE) Tr R_A` (the three terms of the weighted trace proof).
* `norm_trace_mul_le`: `|Tr GR| ≤ ‖G‖ √d ‖R‖_HS`; `weightedTraceError_le_trivial`: on `|E| ≤ 2`,
  `|Tr G'R - sE Tr R - (sd - 1)| ≤ (‖G_d‖ + 2s) √d ‖R‖_HS + sd + 1` (used on exceptional
  events, `G' = U_v*G_dU_v`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeightedTrace

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.RealLoop
open BlockBand.DeterminantScore.ScoreUnsmoothing BlockBand.LocalWindow
open scoped ComplexConjugate Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

/-!
## General finite-dimensional facts
-/

section General

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- For an isometry `V` (`V*V = 1`) and invertible `M`, `V M⁻¹ V*` is the Moore–Penrose inverse
of `V M V*`. -/
theorem isMoorePenrose_frame {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1) {M : Matrix κ κ ℂ}
    (hM : M.det ≠ 0) : IsMoorePenroseInverse (V * M * Vᴴ) (V * M⁻¹ * Vᴴ) := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have h1 : V * M * Vᴴ * (V * M⁻¹ * Vᴴ) = V * Vᴴ := by
    calc V * M * Vᴴ * (V * M⁻¹ * Vᴴ) = V * M * (Vᴴ * V) * M⁻¹ * Vᴴ := by
          simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc V M, mul_nonsing_inv _ hu,
          Matrix.mul_one]
  have h2 : V * M⁻¹ * Vᴴ * (V * M * Vᴴ) = V * Vᴴ := by
    calc V * M⁻¹ * Vᴴ * (V * M * Vᴴ) = V * M⁻¹ * (Vᴴ * V) * M * Vᴴ := by
          simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc V M⁻¹, nonsing_inv_mul _ hu,
          Matrix.mul_one]
  have hP : (V * Vᴴ)ᴴ = V * Vᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]
    calc V * Vᴴ * (V * M * Vᴴ) = V * (Vᴴ * V) * M * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * M * Vᴴ := by rw [hV, Matrix.mul_one]
  · rw [h2]
    calc V * Vᴴ * (V * M⁻¹ * Vᴴ) = V * (Vᴴ * V) * M⁻¹ * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * M⁻¹ * Vᴴ := by rw [hV, Matrix.mul_one]
  · rw [h1, hP]
  · rw [h2, hP]

/-- `‖V X V*‖_HS = ‖X‖_HS` for an isometry `V`. -/
theorem hsNorm_frame {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1) (X : Matrix κ κ ℂ) :
    hsNorm (V * X * Vᴴ) = hsNorm X := by
  unfold hsNorm
  rw [sum_norm_sq_eq_re_trace, sum_norm_sq_eq_re_trace]
  have e : (V * X * Vᴴ)ᴴ * (V * X * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  rw [e, trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

/-- **`|Tr GR| ≤ ‖G‖ √d ‖R‖_HS`** (`‖G‖` the Euclidean operator norm). -/
theorem norm_trace_mul_le (G R : Matrix ι ι ℂ) :
    ‖(G * R).trace‖ ≤ ‖G‖ * Real.sqrt (Fintype.card ι) * hsNorm R := by
  set c : ι → EuclideanSpace ℂ ι := fun j => WithLp.toLp 2 (fun a => R a j)
  have hcol : ∀ j, ‖(G * R) j j‖ ≤ ‖G‖ * ‖c j‖ := fun j => by
    have h1 := G.l2_opNorm_mulVec (c j)
    have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm (G *ᵥ WithLp.ofLp (c j))) j
    have e : ((EuclideanSpace.equiv ι ℂ).symm (G *ᵥ WithLp.ofLp (c j))) j = (G * R) j j := by
      simp [c, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e] at h2
    exact h2.trans h1
  have hcs : ∑ j, ‖c j‖ ≤ Real.sqrt (Fintype.card ι) * hsNorm R := by
    have hsq : ∀ j, ‖c j‖ ^ 2 = ∑ a, ‖R a j‖ ^ 2 := fun j => by
      rw [EuclideanSpace.norm_sq_eq]
    have hcs2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun j => ‖c j‖)
    simp only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      one_mul] at hcs2
    have hR : ∑ j, ‖c j‖ ^ 2 = hsNorm R ^ 2 := by
      unfold hsNorm
      rw [Real.sq_sqrt (by positivity), Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => hsq j
    rw [hR] at hcs2
    have h0 : 0 ≤ Real.sqrt (Fintype.card ι) * hsNorm R :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have : (∑ j, ‖c j‖) ^ 2 ≤ (Real.sqrt (Fintype.card ι) * hsNorm R) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; exact hcs2
    exact abs_le_of_sq_le_sq' this h0 |>.2
  calc ‖(G * R).trace‖ ≤ ∑ j, ‖(G * R) j j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖G‖ * ‖c j‖ := Finset.sum_le_sum fun j _ => hcol j
    _ = ‖G‖ * ∑ j, ‖c j‖ := by rw [Finset.mul_sum]
    _ ≤ ‖G‖ * (Real.sqrt (Fintype.card ι) * hsNorm R) := by gcongr
    _ = _ := by ring

theorem norm_one_le : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty ι with h | h
  · rw [Subsingleton.elim (1 : Matrix ι ι ℂ) 0, norm_zero]; norm_num
  · rw [norm_one]

/-- `|Tr R| ≤ √d ‖R‖_HS`. -/
theorem norm_trace_le (R : Matrix ι ι ℂ) :
    ‖R.trace‖ ≤ Real.sqrt (Fintype.card ι) * hsNorm R := by
  have h := norm_trace_mul_le (1 : Matrix ι ι ℂ) R
  rw [Matrix.one_mul] at h
  refine h.trans ?_
  have := mul_nonneg (Real.sqrt_nonneg (Fintype.card ι : ℝ)) (Real.sqrt_nonneg
    (∑ i, ∑ j, ‖R i j‖ ^ 2))
  unfold hsNorm at this ⊢
  nlinarith [norm_one_le (ι := ι)]

/-- The three-term decomposition of the weighted trace:
`Tr (K₀ + sE)R_A = Tr (K₀ - g₀)(R_A - X) + Tr (K₀ - g₀)X + (g₀ + sE) Tr R_A`. -/
theorem trace_decomp (K₀ R X : Matrix ι ι ℂ) (g₀ c : ℂ) :
    ((K₀ + c • 1) * R).trace = ((K₀ - g₀ • 1) * (R - X)).trace + ((K₀ - g₀ • 1) * X).trace +
      (g₀ + c) * R.trace := by
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.one_mul,
    trace_add, trace_sub, trace_smul, smul_eq_mul]
  ring

end General

/-!
## The frame at the reconstructed Gaussian
-/

/-- **Completeness** of `[U_v | v]` for unit `v`: `U_vU_v* + vv* = 1`. -/
theorem frame_complete {U : FrameMap p i} (hU : IsPairFrame p i U) {v : PairSite p i → ℂ}
    (hv : l2Norm v = 1) : U v * (U v)ᴴ + vecMulVec v (star v) = 1 := by
  obtain ⟨hUU, hUv⟩ := hU.2 v hv
  have hvv := BlockBand.DeterminantScore.ScoreMoments.PairRow.star_dotProduct_self_of_l2Norm hv
  let V : Matrix (PairSite p i) (FrameIndex p ⊕ Unit) ℂ :=
    Matrix.of fun x j => Sum.elim (U v x) (fun _ => v x) j
  have hUv' : ∀ k, ∑ x, conj (U v x k) * v x = 0 := fun k => by
    have := congrFun hUv k
    simpa [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply] using this
  have hvU : ∀ k, ∑ x, conj (v x) * U v x k = 0 := fun k => by
    have h := congrArg conj (hUv' k)
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, Complex.conj_conj, mul_comm]
  have hUU' : ∀ k l, ∑ x, conj (U v x k) * U v x l = if k = l then 1 else 0 := fun k l => by
    have := congrFun (congrFun hUU k) l
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using this
  have hvv' : ∑ x, conj (v x) * v x = 1 := by
    simpa only [dotProduct, Pi.star_apply, Complex.star_def] using hvv
  have hVV : Vᴴ * V = 1 := by
    ext j j'
    rcases j with k | _ <;> rcases j' with l | _
    · simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply, hUU', Matrix.one_apply]
    · simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply, hUv']
    · simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply, hvU]
    · simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply, hvv']
  have hcard : Fintype.card (FrameIndex p ⊕ Unit) = Fintype.card (PairSite p i) := by
    rw [BlockBand.Angular.DetFactor.card_pairSite_eq]; simp
  have hVV' : V * Vᴴ = 1 := (mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).1 hVV
  rw [← hVV']
  ext x y
  simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type, vecMulVec_apply]

/-- `A = K₀ + G_d = U_v M U_v*` at the reconstructed Gaussian (unit `v`). -/
theorem schurA_rec_eq {U : FrameMap p i} (hU : IsPairFrame p i U) (ω : SplitState p i) (E : ℝ)
    {v : PairSite p i → ℂ} (hv : l2Norm v = 1) (G' : FrameMatrix p) :
    schurA p i ω (reconstructedGaussian p i U ω E v G') E =
      U v * frameM p i U ω E v G' * (U v)ᴴ := by
  have hc := frame_complete hU hv
  set F := physicalCoareaF ω.1 ω.2.1 ω.2.2 E with hF
  set X := (U v)ᴴ * F * U v + G' with hX
  have e : schurA p i ω (reconstructedGaussian p i U ω E v G') E =
      (E : ℂ) • vecMulVec v (star v) + U v * X * (U v)ᴴ - (E : ℂ) • 1 := by
    unfold schurA schurK0 reconstructedGaussian
    simp only [← hF, ← hX]
    abel
  have hM : frameM p i U ω E v G' = X - (E : ℂ) • 1 := rfl
  rw [e, hM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ← hc, smul_add]
  abel

/-- `G' = U_v* G_d U_v` at the reconstructed Gaussian. -/
theorem frame_rec_gaussian {U : FrameMap p i} (hU : IsPairFrame p i U) (ω : SplitState p i)
    (E : ℝ) {v : PairSite p i → ℂ} (hv : l2Norm v = 1) (G' : FrameMatrix p) :
    (U v)ᴴ * reconstructedGaussian p i U ω E v G' * U v = G' := by
  obtain ⟨hUU, hUv⟩ := hU.2 v hv
  set W := U v
  have h1 : Wᴴ * vecMulVec v (star v) = 0 := by
    ext a b
    have := congrFun hUv a
    simp only [mulVec, dotProduct, Pi.zero_apply] at this
    simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply, ← mul_assoc,
      ← Finset.sum_mul, this, zero_mul]
  unfold reconstructedGaussian
  simp only
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, h1,
    smul_zero, Matrix.zero_mul, zero_add]
  calc Wᴴ * (W * (Wᴴ * physicalCoareaF ω.1 ω.2.1 ω.2.2 E * W + G') * Wᴴ) * W -
        Wᴴ * physicalCoareaF ω.1 ω.2.1 ω.2.2 E * W
      = (Wᴴ * W) * (Wᴴ * physicalCoareaF ω.1 ω.2.1 ω.2.2 E * W + G') * (Wᴴ * W) -
          Wᴴ * physicalCoareaF ω.1 ω.2.1 ω.2.2 E * W := by simp only [Matrix.mul_assoc]
    _ = G' := by rw [hUU, Matrix.one_mul, Matrix.mul_one]; abel

/-- `M = U_v*K₀U_v + G'` (unit `v`). -/
theorem frameM_eq {U : FrameMap p i} (hU : IsPairFrame p i U) (ω : SplitState p i) (E : ℝ)
    {v : PairSite p i → ℂ} (hv : l2Norm v = 1) (G' : FrameMatrix p) :
    frameM p i U ω E v G' = (U v)ᴴ * schurK0 p i ω E * U v + G' := by
  have hUU := (hU.2 v hv).1
  unfold frameM schurK0
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU]
  abel

theorem card_frameIndex_real : (Fintype.card (FrameIndex p) : ℝ) = 2 * p.W - 1 := by
  have := p.W_pos
  rw [Fintype.card_fin, Nat.cast_sub (by omega)]
  push_cast; ring

theorem card_pairSite_real : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := by
  rw [card_pairSite]; push_cast; ring

/-- `R_A = U_v M⁻¹ U_v*`, the frame inverse embedded by zero on `v`. -/
def embeddedInverse (U : FrameMap p i) (θ : OuterData p i) (G' : FrameMatrix p) :
    PairMatrix p i :=
  U θ.2.2 * (outerM U θ G')⁻¹ * (U θ.2.2)ᴴ

theorem hsNorm_embeddedInverse {U : FrameMap p i} (hU : IsPairFrame p i U) {θ : OuterData p i}
    (hv : l2Norm θ.2.2 = 1) (G' : FrameMatrix p) :
    hsNorm (embeddedInverse U θ G') = invHS U θ G' := by
  unfold embeddedInverse
  rw [hsNorm_frame (hU.2 θ.2.2 hv).1]
  rfl

theorem trace_embeddedInverse (U : FrameMap p i) (θ : OuterData p i)
    (X : PairMatrix p i) (G' : FrameMatrix p) :
    (X * embeddedInverse U θ G').trace = ((U θ.2.2)ᴴ * X * U θ.2.2 * (outerM U θ G')⁻¹).trace := by
  unfold embeddedInverse
  rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- **`Tr G'R - sE Tr R - (sd - 1) = d(1 - s) - Re Tr (K₀ + sE)R_A`**, `d = 2W`, at the
reconstructed Gaussian with `M` invertible. -/
theorem weightedTraceError_eq {U : FrameMap p i} (hU : IsPairFrame p i U) (s : ℝ)
    {θ : OuterData p i} (hv : l2Norm θ.2.2 = 1) {G' : FrameMatrix p}
    (hdet : (outerM U θ G').det ≠ 0) :
    weightedTraceError s U θ G' = 2 * p.W * (1 - s) -
      ((schurK0 p i θ.1 θ.2.1 + ((s * θ.2.1 : ℝ) : ℂ) • 1) * embeddedInverse U θ G').trace.re := by
  have hUU := (hU.2 θ.2.2 hv).1
  have hu : IsUnit (outerM U θ G').det := isUnit_iff_ne_zero.mpr hdet
  set M := outerM U θ G'
  set K := (U θ.2.2)ᴴ * schurK0 p i θ.1 θ.2.1 * U θ.2.2
  have hMK : M = K + G' := frameM_eq hU θ.1 θ.2.1 hv G'
  have hG : G' * M⁻¹ = 1 - K * M⁻¹ := by
    have : G' = M - K := by rw [hMK]; abel
    rw [this, Matrix.sub_mul, mul_nonsing_inv _ hu]
  have htr : (G' * M⁻¹).trace = ((2 * p.W - 1 : ℝ) : ℂ) - (K * M⁻¹).trace := by
    rw [hG, trace_sub, trace_one, ← card_frameIndex_real]; simp
  have h1 := trace_embeddedInverse U θ (schurK0 p i θ.1 θ.2.1 + ((s * θ.2.1 : ℝ) : ℂ) • 1) G'
  have hsplit : (U θ.2.2)ᴴ * (schurK0 p i θ.1 θ.2.1 + ((s * θ.2.1 : ℝ) : ℂ) • 1) * U θ.2.2 =
      K + ((s * θ.2.1 : ℝ) : ℂ) • 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU]
  rw [h1, hsplit, Matrix.add_mul, trace_add, Matrix.smul_mul, Matrix.one_mul, trace_smul]
  unfold weightedTraceError invTrace
  rw [htr]
  simp only [smul_eq_mul, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- **Trivial bound** (exceptional events): for `|E| ≤ 2`, `0 ≤ s`,
`|Tr G'R - sE Tr R - (sd - 1)| ≤ (‖G_d‖ + 2s) √d ‖R‖_HS + sd + 1`. -/
theorem weightedTraceError_le_trivial {U : FrameMap p i} (hU : IsPairFrame p i U) {s : ℝ}
    (hs : 0 ≤ s) {θ : OuterData p i} (hv : l2Norm θ.2.2 = 1) (hE : |θ.2.1| ≤ 2)
    (G' : FrameMatrix p) :
    |weightedTraceError s U θ G'| ≤
      (‖reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'‖ + 2 * s) * Real.sqrt (2 * p.W) *
          invHS U θ G' + s * (2 * p.W) + 1 := by
  set Gd := reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'
  set RA := embeddedInverse U θ G'
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hHS := hsNorm_embeddedInverse hU hv G'
  have hG'eq := frame_rec_gaussian hU θ.1 θ.2.1 hv G'
  have h1 : (G' * (outerM U θ G')⁻¹).trace = (Gd * RA).trace := by
    rw [trace_embeddedInverse U θ, hG'eq]
  have h2 : (outerM U θ G')⁻¹.trace = RA.trace := by
    have := trace_embeddedInverse U θ 1 G'
    rw [Matrix.one_mul, Matrix.mul_one, (hU.2 θ.2.2 hv).1, Matrix.one_mul] at this
    exact this.symm
  have hc := norm_trace_mul_le Gd RA
  have ht := norm_trace_le RA
  rw [card_pairSite_real, hHS] at hc ht
  have hre1 : |(Gd * RA).trace.re| ≤ ‖(Gd * RA).trace‖ := Complex.abs_re_le_norm _
  have hre2 : |RA.trace.re| ≤ ‖RA.trace‖ := Complex.abs_re_le_norm _
  have hsq0 : 0 ≤ Real.sqrt (2 * p.W) * invHS U θ G' :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hE' : |s * θ.2.1 * RA.trace.re| ≤ 2 * s * (Real.sqrt (2 * p.W) * invHS U θ G') := by
    rw [abs_mul, abs_mul, abs_of_nonneg hs]
    have := mul_le_mul hE (hre2.trans ht) (abs_nonneg _) (by norm_num)
    nlinarith
  unfold weightedTraceError invTrace
  rw [h1, h2]
  have hlast : |s * (2 * p.W) - 1| ≤ s * (2 * p.W) + 1 := by
    rw [abs_le]; constructor <;> nlinarith
  calc |(Gd * RA).trace.re - s * θ.2.1 * RA.trace.re - (s * (2 * p.W) - 1)|
      ≤ |(Gd * RA).trace.re| + |s * θ.2.1 * RA.trace.re| + |s * (2 * p.W) - 1| := by
        have := abs_sub (Gd * RA).trace.re (s * θ.2.1 * RA.trace.re)
        have := abs_sub ((Gd * RA).trace.re - s * θ.2.1 * RA.trace.re) (s * (2 * p.W) - 1)
        linarith
    _ ≤ ‖Gd‖ * Real.sqrt (2 * p.W) * invHS U θ G' +
          2 * s * (Real.sqrt (2 * p.W) * invHS U θ G') + (s * (2 * p.W) + 1) := by
        gcongr
        exact hre1.trans hc
    _ = _ := by ring

end BlockBand.DeterminantScore.WeightedTrace

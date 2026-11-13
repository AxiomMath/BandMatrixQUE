module

public import BlockBand.Native.ErdosRiabov.VS.ResolventIto

set_option autoImplicit false

/-!
# Itô's formula for resolvent chains in VS form: drift, bracket bound, pattern form

* `chainDrift_vs` (`t ∈ [0, 1]`): for `z_j(t) = vsSpec z_j m_j (vsSat δ) t`, the flow term
  `ż_j G_j² = -m_j G_j²` combines with the diagonal Itô term:
  `drift = ∑_j [∑_{i<j} Re tr(K G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)}) +
    Re tr(K G_{[0,j]} 𝒮[G_j - m_j] G_{[j,k)})]`
  (`𝒮[m I] = m I`: rows of `shortRingProfile` sum to one, `bandSelfEnergy_smul_one`).
* `chainBracket_le`: `|Im z_j(t)| ≥ ε > 0` gives
  `chainBracket ≤ 2 N (N ‖K‖ k ε^{-(k+1)} ∏_j ‖B_j‖)²`, `N = p.n * p.W`; proof: the variance
  table (`sum_ringVariance_smul`), `‖e_aa‖ ≤ 1`, `‖e_ab + e_ba‖, ‖i e_ab - i e_ba‖ ≤ 2`,
  `|Re tr(K X)| ≤ N ‖K‖ ‖X‖`, `‖firstVar‖ ≤ k ε^{-(k+1)} ∏‖B_j‖ ‖X‖` (`norm_firstVar_le`) and
  `∑_{a,b} S_ab = N`.
* `chainBracket_le_pow`: `ε ≥ (2N)⁻¹`, `‖K‖ ≤ 1`, `‖B_j‖ ≤ 1` give
  `chainBracket ≤ 2 k² 4^{k+1} N^{2k+5}`.
* `resolventChain_ito_vs`: Itô's formula for a pattern `σ : Fin k → Bool` (`z_j ∈ {z, z̄}`,
  `m_j ∈ {m, m̄}`), `Im z > 0`, `Im m > 0`, saturation `δ = Im z / (2 Im m)`; `chainBracket_le_vs`:
  the bracket bound with `ε = Im z / 2`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory ProbabilityTheory Set Matrix Function
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.CEH.Flow
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Adapters.ErdosRiabov
open scoped NNReal ComplexConjugate Matrix.Norms.L2Operator

variable {p : BlockBand.Parameters} {k : ℕ}

/-!
### The combined drift on `[0, 1]`
-/

/-- `𝒮[c · 1] = c · 1` when the rows of `S` sum to one. -/
theorem bandSelfEnergy_smul_one {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ}
    (hS : ∀ a, ∑ b, S a b = 1) (c : ℂ) :
    bandSelfEnergy S (c • (1 : Matrix (Fin N) (Fin N) ℂ)) = c • 1 := by
  ext a d
  rw [bandSelfEnergy_apply]
  by_cases had : a = d
  · subst had
    simp only [ite_true, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hS a, Complex.ofReal_one, one_mul]
  · simp [had]

theorem bandSelfEnergy_sub {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ)
    (X Y : Matrix (Fin N) (Fin N) ℂ) :
    bandSelfEnergy S (X - Y) = bandSelfEnergy S X - bandSelfEnergy S Y := by
  simp only [bandSelfEnergy, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, diagonal_sub]

theorem sum_filter_le_eq {M : Type*} [AddCommMonoid M] (f : Fin k → M) (j : Fin k) :
    ∑ i with i ≤ j, f i = (∑ i with i < j, f i) + f j := by
  have e : (Finset.univ.filter fun i : Fin k => i ≤ j) =
      insert j (Finset.univ.filter fun i : Fin k => i < j) := by
    ext i
    simp [le_iff_lt_or_eq, or_comm]
  rw [e, Finset.sum_insert (by simp), add_comm]

/-- Flow slot plus diagonal pair term: `G_{[0,j]} 𝒮[G_j] G_{[j,k)} + (c G_j²)-slot =
G_{[0,j]} 𝒮[G_j + c] G_{[j,k)}` (rows of `S` sum to one). -/
theorem pairIns_diag_add_slot {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ} (hS : ∀ a, ∑ b, S a b = 1)
    (B R : Fin k → Matrix (Fin N) (Fin N) ℂ) (j : Fin k) (c : ℂ) :
    pairIns B R (bandSelfEnergy S) j j + slotProd B (update R j (c • (R j * R j))) =
      pairIns B R (fun X => bandSelfEnergy S (X - (-c) • (1 : Matrix (Fin N) (Fin N) ℂ))) j j := by
  have hneg : bandSelfEnergy S (R j - (-c) • (1 : Matrix (Fin N) (Fin N) ℂ)) =
      bandSelfEnergy S (R j) + c • 1 := by
    rw [bandSelfEnergy_sub, bandSelfEnergy_smul_one hS, neg_smul, sub_neg_eq_add]
  simp only [pairIns, segProd_self, one_mul, slotProd_update, hneg]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_assoc]

theorem pairIns_diag_add_slot_neg {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ}
    (hS : ∀ a, ∑ b, S a b = 1) (B R : Fin k → Matrix (Fin N) (Fin N) ℂ) (j : Fin k) (m : ℂ) :
    pairIns B R (bandSelfEnergy S) j j + slotProd B (update R j ((-m) • (R j * R j))) =
      pairIns B R (fun X => bandSelfEnergy S (X - m • (1 : Matrix (Fin N) (Fin N) ℂ))) j j := by
  simpa only [neg_neg] using pairIns_diag_add_slot hS B R j (-m)

theorem rowSum_shortRingProfile (p : BlockBand.Parameters) (a : Fin (p.n * p.W)) :
    ∑ b, shortRingProfile p.b p.n p.W a b = 1 :=
  Kernel.shortRingProfile_rowSum p.b (by have := p.n_ge_four; omega) p.W_pos a

/-- **The chain drift, VS form.** For `z_j(t) = z_j + (1 - c(t)) m_j` with the saturation
`c = vsSat δ`, `δ ≥ 0`, and `t ≤ 1` (where `ż_j = -m_j`), the chain drift is
`∑_j [∑_{i<j} Re tr(K G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)}) +
  Re tr(K G_{[0,j]} 𝒮[G_j - m_j] G_{[j,k)})]`. -/
theorem chainDrift_vs (A₀ : RingMat p) (zs ms : Fin k → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (B : Fin k → RingMat p) (K : RingMat p) {t : ℝ} (ht : t ≤ 1) (y : Fin (ringDim p) → ℝ) :
    chainDrift A₀ (fun j => vsSpec (zs j) (ms j) (vsSat δ)) B K t y =
      ∑ j, ((∑ i with i < j, reTr K (pairIns B
          (ringSlots A₀ (fun j => vsSpec (zs j) (ms j) (vsSat δ)) t y)
          (bandSelfEnergy (shortRingProfile p.b p.n p.W)) i j)) +
        reTr K (pairIns B (ringSlots A₀ (fun j => vsSpec (zs j) (ms j) (vsSat δ)) t y)
          (fun X => bandSelfEnergy (shortRingProfile p.b p.n p.W) (X - ms j • (1 : RingMat p)))
          j j)) := by
  set R := ringSlots A₀ (fun j => vsSpec (zs j) (ms j) (vsSat δ)) t y with hR
  have hder : ∀ j, deriv (vsSpec (zs j) (ms j) (vsSat δ)) t = -ms j := fun j => by
    rw [(hasDerivAt_vsSpec (zs j) (ms j) (hasDerivAt_vsSat_of_le_one hδ ht)).deriv]
    simp
  rw [chainDrift]
  simp only [hder, ← hR]
  rw [reTr_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_filter_le_eq, ← pairIns_diag_add_slot_neg (rowSum_shortRingProfile p), reTr_add]
  ring

/-!
### The bracket bound
-/

section Bounds

theorem norm_single_one_le {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι) :
    ‖single a b (1 : ℂ)‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (single a b (1 : ℂ))
  rw [conjTranspose_single, star_one, single_mul_single_same, mul_one, ← diagonal_single,
    l2_opNorm_diagonal, Pi.norm_single, norm_one] at h
  nlinarith [norm_nonneg (single a b (1 : ℂ))]

theorem abs_reTr_le {ι : Type} [Fintype ι] [DecidableEq ι] (K X : Matrix ι ι ℂ) :
    |reTr K X| ≤ Fintype.card ι * (‖K‖ * ‖X‖) := by
  unfold reTr
  calc |(trace (K * X)).re| ≤ ‖trace (K * X)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ‖(K * X) i i‖ := by
        simp only [Matrix.trace, Matrix.diag]
        exact norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖K * X‖ := Finset.sum_le_sum fun i _ =>
        ERNative.BlockBand.GaussianRing.ERSChainGlobal.norm_entry_le_l2_opNorm _ i i
    _ = Fintype.card ι * ‖K * X‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ Fintype.card ι * (‖K‖ * ‖X‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (Nat.cast_nonneg _)

variable (p) in
/-- `∑_{a,b} S_ab = N` (rows of the profile sum to one). -/
theorem sum_sum_entryVariance : ∑ x, ∑ y, p.entryVariance x y = (p.n * p.W : ℕ) := by
  have h : ∀ x, ∑ y, p.entryVariance x y = 1 := fun x => by
    rw [← rowSum_shortRingProfile p (ringSiteEquiv p x), ← (ringSiteEquiv p).sum_comp]
    exact Finset.sum_congr rfl fun y _ => (shortRingProfile_ringSiteEquiv p x y).symm
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Fintype.card_congr (ringSiteEquiv p), Fintype.card_fin]

variable (p) in
/-- **Variance-weighted coordinate sums** of a nonnegative `Q` with `Q(e_aa) ≤ D`,
`Q(e_ab + e_ba), Q(i e_ab - i e_ba) ≤ 4D`: `∑_i v_i Q(E_i) ≤ 2 N D`. -/
theorem sum_ringVariance_mul_le (Q : p.SiteMatrix → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hdiag : ∀ x, Q (single x x 1) ≤ D) (hre : ∀ x y, Q (bandRe p x y) ≤ 4 * D)
    (him : ∀ x y, Q (bandIm p x y) ≤ 4 * D) :
    ∑ i, ringVariance p i * Q (ringBasis p i) ≤ 2 * (p.n * p.W : ℕ) * D := by
  have h := sum_ringVariance_smul p (M := ℝ) Q
  simp only [smul_eq_mul] at h
  rw [h]
  have htot := sum_sum_entryVariance p
  rw [sum_sum_eq_diag_add_upper p] at htot
  have hup : ∀ x y, (if p.siteIndex x < p.siteIndex y then
      p.entryVariance x y + p.entryVariance y x else 0) =
      2 * (if p.siteIndex x < p.siteIndex y then p.entryVariance x y else 0) := fun x y => by
    split_ifs <;> simp [entryVariance_swap p x y, two_mul]
  simp only [hup, ← Finset.mul_sum] at htot
  have hA : ∑ x, p.entryVariance x x * Q (single x x 1) ≤ D * ∑ x, p.entryVariance x x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => by
      nlinarith [p.entryVariance_nonneg x x, hdiag x]
  have hB : (∑ x, ∑ y, if p.siteIndex x < p.siteIndex y then
      p.entryVariance x y / 2 * (Q (bandRe p x y) + Q (bandIm p x y)) else 0) ≤
      4 * D * ∑ x, ∑ y, if p.siteIndex x < p.siteIndex y then p.entryVariance x y else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    split_ifs
    · nlinarith [p.entryVariance_nonneg x y, hre x y, him x y]
    · simp
  have hS0 : 0 ≤ ∑ x, p.entryVariance x x :=
    Finset.sum_nonneg fun x _ => p.entryVariance_nonneg x x
  nlinarith

/-- **Bracket bound for resolvent chains.** If `|Im z_j(t)| ≥ ε > 0` for all `j`, then
`chainBracket ≤ 2 N (N ‖K‖ k ε^{-(k+1)} ∏_j ‖B_j‖)²`, `N = p.n * p.W`. -/
theorem chainBracket_le {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) (zf : Fin k → ℝ → ℂ)
    (B : Fin k → RingMat p) (K : RingMat p) {t ε : ℝ} (hε : 0 < ε)
    (hzε : ∀ j, ε ≤ |(zf j t).im|) (y : Fin (ringDim p) → ℝ) :
    chainBracket A₀ zf B K t y ≤ 2 * (p.n * p.W : ℕ) *
      ((p.n * p.W : ℕ) * ‖K‖ * (k * ε⁻¹ ^ (k + 1) * ∏ j, ‖B j‖)) ^ 2 := by
  set e := ringSiteEquiv p
  set R := ringSlots A₀ zf t y
  set D₀ := (p.n * p.W : ℕ) * ‖K‖ * (k * ε⁻¹ ^ (k + 1) * ∏ j, ‖B j‖) with hD₀
  have hR : ∀ j, ‖R j‖ ≤ ε⁻¹ := norm_resSlots_le A₀ (ringMatrixFin p)
    (hA₀.add (ringMatrixFin_isHermitian y)) hε hzε
  have hD₀0 : 0 ≤ D₀ := by
    rw [hD₀]
    have : 0 ≤ ∏ j, ‖B j‖ := Finset.prod_nonneg fun j _ => norm_nonneg _
    positivity
  set Q : p.SiteMatrix → ℝ := fun E => reTr K (firstVar B R (reindex e e E)) ^ 2 with hQ
  have hQle : ∀ E, Q E ≤ (D₀ * ‖reindex e e E‖) ^ 2 := fun E => by
    have h1 := abs_reTr_le K (firstVar B R (reindex e e E))
    have h2 := norm_firstVar_le B R hR (reindex e e E)
    rw [Fintype.card_fin] at h1
    have h3 : |reTr K (firstVar B R (reindex e e E))| ≤ D₀ * ‖reindex e e E‖ := by
      refine h1.trans ?_
      rw [hD₀]
      have hK := norm_nonneg K
      have hN : (0 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := Nat.cast_nonneg _
      calc ((p.n * p.W : ℕ) : ℝ) * (‖K‖ * ‖firstVar B R (reindex e e E)‖)
          ≤ ((p.n * p.W : ℕ) : ℝ) * (‖K‖ *
              (k * ε⁻¹ ^ (k + 1) * ‖reindex e e E‖ * ∏ l, ‖B l‖)) := by gcongr
        _ = _ := by push_cast; ring
    rw [hQ]
    simp only
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hsingle : ∀ x y : p.Site, reindex e e (single x y (1 : ℂ)) = single (e x) (e y) 1 :=
    fun x y => by simp [reindex_apply]
  have hbound : ∀ E, ‖reindex e e E‖ ≤ 2 → Q E ≤ 4 * D₀ ^ 2 := fun E hE => by
    refine (hQle E).trans ?_
    have h0 := norm_nonneg (reindex e e E)
    have h4 : ‖reindex e e E‖ ^ 2 ≤ 4 := by nlinarith
    calc (D₀ * ‖reindex e e E‖) ^ 2 = D₀ ^ 2 * ‖reindex e e E‖ ^ 2 := mul_pow _ _ _
      _ ≤ D₀ ^ 2 * 4 := mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
      _ = 4 * D₀ ^ 2 := by ring
  have hlin : ∀ E : p.SiteMatrix, reindex e e E = reindexLinearEquiv ℂ ℂ e e E := fun E => by
    rw [coe_reindexLinearEquiv]
  have hre_eq : ∀ x y : p.Site, reindex e e (bandRe p x y) =
      single (e x) (e y) 1 + single (e y) (e x) 1 := fun x y => by
    rw [hlin, bandRe, map_add, ← hlin, ← hlin, hsingle, hsingle]
  have him_eq : ∀ x y : p.Site, reindex e e (bandIm p x y) =
      Complex.I • single (e x) (e y) 1 - Complex.I • single (e y) (e x) 1 := fun x y => by
    rw [hlin, bandIm, map_sub, map_smul, map_smul, ← hlin, ← hlin, hsingle, hsingle]
  have hmain := sum_ringVariance_mul_le p Q (D := D₀ ^ 2) (sq_nonneg _)
    (fun x => by
      refine (hQle _).trans ?_
      rw [hsingle]
      have h1 := norm_single_one_le (e x) (e x)
      have h0 := norm_nonneg (single (e x) (e x) (1 : ℂ))
      have h4 : ‖single (e x) (e x) (1 : ℂ)‖ ^ 2 ≤ 1 := by nlinarith
      calc (D₀ * ‖single (e x) (e x) (1 : ℂ)‖) ^ 2
          = D₀ ^ 2 * ‖single (e x) (e x) (1 : ℂ)‖ ^ 2 := mul_pow _ _ _
        _ ≤ D₀ ^ 2 * 1 := mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
        _ = D₀ ^ 2 := mul_one _)
    (fun x y => hbound _ (by
      rw [hre_eq]
      exact (norm_add_le _ _).trans (by
        linarith [norm_single_one_le (e x) (e y), norm_single_one_le (e y) (e x)])))
    (fun x y => hbound _ (by
      rw [him_eq]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, norm_smul, Complex.norm_I, one_mul, one_mul]
      linarith [norm_single_one_le (e x) (e y), norm_single_one_le (e y) (e x)]))
  have hlhs : chainBracket A₀ zf B K t y = ∑ i, ringVariance p i * Q (ringBasis p i) := rfl
  rw [hlhs]
  exact hmain

/-- **Polynomial bracket bound (`≤ N^{C(k)}`).** If `|Im z_j(t)| ≥ (2N)⁻¹`, `‖K‖ ≤ 1` and
`‖B_j‖ ≤ 1`, then `chainBracket ≤ 2 k² 4^{k+1} N^{2k+5}`, `N = p.n * p.W`. -/
theorem chainBracket_le_pow {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) (zf : Fin k → ℝ → ℂ)
    (B : Fin k → RingMat p) (K : RingMat p) {t : ℝ}
    (hzε : ∀ j, (2 * (p.n * p.W : ℕ) : ℝ)⁻¹ ≤ |(zf j t).im|) (hK : ‖K‖ ≤ 1)
    (hB : ∀ j, ‖B j‖ ≤ 1) (y : Fin (ringDim p) → ℝ) :
    chainBracket A₀ zf B K t y ≤ 2 * k ^ 2 * 4 ^ (k + 1) * ((p.n * p.W : ℕ) : ℝ) ^ (2 * k + 5) := by
  set N : ℝ := ((p.n * p.W : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := p.n_ge_four; omega)
      p.W_pos.ne')
  have hε : 0 < (2 * N)⁻¹ := by positivity
  refine (chainBracket_le hA₀ zf B K hε hzε y).trans ?_
  have hP : ∏ j, ‖B j‖ ≤ 1 := Finset.prod_le_one₀ (fun j _ => norm_nonneg _) fun j _ => hB j
  have hP0 : 0 ≤ ∏ j, ‖B j‖ := Finset.prod_nonneg fun j _ => norm_nonneg _
  rw [inv_inv]
  have h1 : N * ‖K‖ * (k * (2 * N) ^ (k + 1) * ∏ j, ‖B j‖) ≤ N * (k * (2 * N) ^ (k + 1)) := by
    have : 0 ≤ (k : ℝ) * (2 * N) ^ (k + 1) := by positivity
    calc N * ‖K‖ * (k * (2 * N) ^ (k + 1) * ∏ j, ‖B j‖)
        = N * (k * (2 * N) ^ (k + 1)) * (‖K‖ * ∏ j, ‖B j‖) := by ring
      _ ≤ N * (k * (2 * N) ^ (k + 1)) * 1 := by
          gcongr
          calc ‖K‖ * ∏ j, ‖B j‖ ≤ 1 * 1 := by gcongr
            _ = 1 := one_mul 1
      _ = _ := mul_one _
  have h0 : 0 ≤ N * ‖K‖ * (k * (2 * N) ^ (k + 1) * ∏ j, ‖B j‖) := by positivity
  calc 2 * N * (N * ‖K‖ * (k * (2 * N) ^ (k + 1) * ∏ j, ‖B j‖)) ^ 2
      ≤ 2 * N * (N * (k * (2 * N) ^ (k + 1))) ^ 2 := by gcongr
    _ = 2 * k ^ 2 * 4 ^ (k + 1) * N ^ (2 * k + 5) := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
          show (2 : ℝ) ^ ((k + 1) * 2) = 4 ^ (k + 1) by
            rw [mul_comm, pow_mul]; norm_num]
        ring

end Bounds

/-!
### The pattern form
-/

/-- The saturated spectral parameters of a pattern `σ` (`true` = conjugate):
`z_j(t) = vsSpec (z or z̄) (m or m̄) (vsSat (Im z / (2 Im m))) t`. -/
def vsPatternSpec (z m : ℂ) (σ : Fin k → Bool) : Fin k → ℝ → ℂ :=
  fun j => vsSpec (patConj (σ j) z) (patConj (σ j) m) (vsSat (z.im / (2 * m.im)))

/-- **Itô's formula for resolvent chains along a pattern** (`z_j ∈ {z, z̄}` along the saturated VS
characteristic). -/
theorem resolventChain_ito_vs (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im)
    (σ : Fin k → Bool) (B : Fin k → RingMat p) (K : RingMat p) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
      (BlockBand.SourceProcess.Stochastic.driverAugmented (κ := Fin (ringDim p)) μ)
      (fun t x (_ : Fin 1) =>
        chainTestT A₀ (ringMatrixFin p) (vsPatternSpec z m σ) B K ((t : ℝ), vsNoise p t x))
      (fun t x (_ : Fin 1) => chainDrift A₀ (vsPatternSpec z m σ) B K t (vsNoise p t x))
      (fun t x => Matrix.of fun (_ _ : Fin 1) =>
        chainBracket A₀ (vsPatternSpec z m σ) B K t (vsNoise p t x)) :=
  resolventChain_ito μ hA₀ _ (fun _ => contDiff_vsSpec _ _ (contDiff_vsSat _ (n := 2)))
    (fun j t => vsSpec_im_ne_zero hz hm (σ j) t) B K

/-- The bracket bound along a pattern: `ε = Im z / 2` for all times. -/
theorem chainBracket_le_vs {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) {z m : ℂ} (hz : 0 < z.im)
    (hm : 0 < m.im) (σ : Fin k → Bool) (B : Fin k → RingMat p) (K : RingMat p) (t : ℝ)
    (y : Fin (ringDim p) → ℝ) :
    chainBracket A₀ (vsPatternSpec z m σ) B K t y ≤ 2 * (p.n * p.W : ℕ) *
      ((p.n * p.W : ℕ) * ‖K‖ * (k * (z.im / 2)⁻¹ ^ (k + 1) * ∏ j, ‖B j‖)) ^ 2 :=
  chainBracket_le hA₀ _ B K (half_pos hz) (fun j => half_le_abs_im_vsSpec hz hm (σ j) t) y

end BlockBand.Native.ErdosRiabov.VS

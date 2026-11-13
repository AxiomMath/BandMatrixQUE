module

public import BlockBand.Internal.Contracts.Layers
public import BlockBand.Layers.CompensatedIncrement
public import BlockBand.RankLocation.SpectralMomentTransport
public import BlockBand.RankLocation.SemicircleCDF
public import BlockBand.QUE.Fourier.CyclicTransport
public import BlockBand.Model.Construction.GaussianCompatibility
public import BlockBand.Model.Construction.OrderedEigenvalues

/-!
# Rank location and mass-law transport from the physical count bounds

Law and domain: the physical law `model.law` (`IsPhysicalGaussianRingLaw`; raw `H`, row
variance one), every admissible `p` with `p.b = b`, `n ≤ TW`; the block-mass laws
`physicalBlockMeasure` and pair-mass laws `physicalPairMeasure` (`MassLaw`). Norms: `L^q` of the
law (`eLpNorm`, `q ≥ 1` real). Ranks are zero-based (`IsBulkRank`), eigenvalues increasing
(`physicalOrderedEigenvalue`), `e_α = classicalLocation`.

* `RklPhysicalCount`: the `count_moment` and `count_mean` fields of `RankLocationContract`
  restricted to `MassLaw.physical` (the only hypothesis).
* `rkl_physicalCount_eq`: on Hermitian `H`, `N_H(E) = #{α : λ_α < E}` (`countBelow`), through
  `charpoly (H - E) = charpoly H ∘ (X + E)`.
* `rkl_lintegral_rpow_le_of_tail`: layer-cake tail integration, `P(Y > t) ≤ B (s/t)^r` for
  `t ≥ s`, `q < r` ⇒ `E Y^q ≤ s^q (1 + qB/(r-q))`.
* `rkl_moment_le`: `E|λ_α - e|^{2r} ≤ K_r N^{6r+2}` for `|e| ≤ 2` (entries of the Gaussian
  reconstruction `model.law_eq_gaussianMatrixLaw`, the entrywise eigenvalue bound, standard
  Gaussian moments; `K_r` depends on `r` only).
* `rkl_location_physical`: `‖λ_α - e_α‖_q ≤ C/(n√W)` under the physical law, `C = C(b,T,ϑ,q)`:
  near tails `t ≤ ϑ/2` from the count moment of order `r = ⌈q⌉ + 1` at `e_α ± t ∈ [-2+ϑ/2,
  2-ϑ/2]` (density `≥ √ϑ/(2π)`), far tails by interpolating the order-`(14r+4)` count tail at
  `t = ϑ/2` with the polynomial moment (`rkl_far_tail`).
* `rkl_map_spec`: the law of the whole ordered spectrum is the same under every `MassLaw`
  (cyclic mass-law transport; shift `H ↦ H(· - s)` preserving the law by
  `GaussianRingModel.map_cyclicMatrix`, block-mass covariance `physical_blockMass_cyclic_ae`,
  spectrum invariance by characteristic-polynomial uniqueness); the densities agree pointwise.
* `rankLocation_of_physicalCount`: `RankLocationContract`, with the physical constants under
  every mass law (equality of eigenvalue-only norms and means).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.RankLocation

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (negativeCount)
open BlockBand.Model.Construction
open scoped ENNReal NNReal

/-!
## 0. The physical count fields
-/

/-- The `count_moment` and `count_mean` fields of `RankLocationContract` restricted to the
physical law `MassLaw.physical` (same quantifiers, constants and bounds). -/
def RklPhysicalCount : Prop :=
  (∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
    ∃ Cq : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (E : ℝ), E ∈ bulkInterval κ →
      eLpNorm (fun H => (physicalCount p H E : ℝ) - p.N * semicircleCDF E) (ENNReal.ofReal q)
          (model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal (Cq * Real.sqrt p.W)) ∧
  (∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ C : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (E : ℝ), E ∈ bulkInterval κ →
      |(∫ H, (physicalCount p H E : ℝ) ∂(model.law : Measure p.SiteMatrix)) -
          p.N * semicircleCDF E| ≤
        C * ((p.n : ℝ) / p.W + (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)))

/-!
## 1. The physical count is the strict count of the ordered spectrum
-/

section Count

variable {p : Parameters}

/-- The ordered physical spectrum `H ↦ (λ_α(H))_α`. -/
def rklSpec (p : Parameters) (H : p.SiteMatrix) : Fin p.N → ℝ :=
  fun α => physicalOrderedEigenvalue p H α

theorem rkl_measurable_spec : Measurable (rklSpec p) :=
  measurable_pi_iff.mpr fun α => measurable_physicalOrderedEigenvalue p α

theorem rkl_spectralSum_sub_smul {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (E : ℝ) (f : ℝ → ℝ) :
    Internal.Contracts.Inputs.spectralSum (M - (E : ℂ) • 1) f =
      Internal.Contracts.Inputs.spectralSum M (fun x => f (x - E)) := by
  unfold Internal.Contracts.Inputs.spectralSum
  have hsc : (E : ℂ) • (1 : Matrix ι ι ℂ) = scalar ι (E : ℂ) := by
    rw [scalar_apply, smul_one_eq_diagonal]
  have hcp : (M - (E : ℂ) • 1).charpoly = M.charpoly.comp
      (Polynomial.C 1 * Polynomial.X + Polynomial.C (E : ℂ)) := by
    rw [hsc, charpoly_sub_scalar, Polynomial.C_1, one_mul]
  have hr := Polynomial.map_roots_comp_C_mul_X_add_C M.charpoly 1 (E : ℂ) isUnit_one
  rw [← hcp] at hr
  rw [← hr, Multiset.map_map]
  congr 2
  funext x
  simp

theorem rkl_isHermitian_sub {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (E : ℝ) : (H - (E : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  refine hH.sub ?_
  rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

theorem rkl_physicalCount_eq {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) :
    physicalCount p H E = countBelow (rklSpec p H) E := by
  have h1 : (physicalCount p H E : ℝ) =
      Internal.Contracts.Inputs.spectralSum H (fun x => Layers.cphNegInd (x - E)) := by
    unfold physicalCount
    rw [Layers.cph_negativeCount_eq_spectralSum (rkl_isHermitian_sub hH E),
      rkl_spectralSum_sub_smul]
  rw [Layers.cph_spectralSum_eq_rawSum hH] at h1
  have h2 : (countBelow (rklSpec p H) E : ℝ) =
      Layers.cphRawSum (fun x => Layers.cphNegInd (x - E)) H := by
    unfold countBelow Layers.cphRawSum Layers.cphNegInd rklSpec physicalOrderedEigenvalue
    rw [Finset.card_filter, Nat.cast_sum]
    refine (Fintype.sum_equiv (finCongr (physicalSite_card p)).symm _ _ fun α => ?_)
    simp only [physicalSpectralRank, finCongr_symm, finCongr_apply]
    by_cases h : rawIncreasingEigenvalue (Fin.cast (physicalSite_card p).symm α) H < E
    · simp [h, sub_neg.mpr h]
    · simp [h]
  exact_mod_cast h1.trans h2.symm

end Count

/-!
## 2. Tail integration
-/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem rkl_setIntegral_rpow_Ioc {q s : ℝ} (hq : 0 < q) (hs : 0 < s) :
    ∫ t in Set.Ioc 0 s, t ^ (q - 1) = s ^ q / q := by
  rw [← intervalIntegral.integral_of_le hs.le, integral_rpow (Or.inl (by linarith)),
    sub_add_cancel, Real.zero_rpow hq.ne', sub_zero]

theorem rkl_integrableOn_rpow_Ioc {q s : ℝ} (hq : 0 < q) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t ^ (q - 1)) (Set.Ioc 0 s) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith))

/-- **Tail integration.** If `P(Y > t) ≤ B (s/t)^r` for every `t ≥ s` (`Y ≥ 0`, `μ` a probability
measure, `0 < q < r`), then `E Y^q ≤ s^q (1 + q B/(r - q))`. -/
theorem rkl_lintegral_rpow_le_of_tail [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω) {q s B : ℝ} {r : ℕ} (hq : 0 < q)
    (hqr : q < r) (hs : 0 < s) (hB : 0 ≤ B)
    (htail : ∀ t, s ≤ t → μ {ω | t < Y ω} ≤ ENNReal.ofReal (B * (s / t) ^ r)) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ ≤ ENNReal.ofReal (s ^ q * (1 + q * B / (r - q))) := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ (ae_of_all _ hY0) hY hq]
  rw [← Set.Ioc_union_Ioi_eq_Ioi hs.le,
    lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi_same)]
  have hrq : 0 < (r : ℝ) - q := by linarith
  -- near part
  have h1 : ∫⁻ t in Set.Ioc 0 s, μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
      ENNReal.ofReal (s ^ q / q) := by
    calc _ ≤ ∫⁻ t in Set.Ioc 0 s, ENNReal.ofReal (t ^ (q - 1)) := by
          refine lintegral_mono fun t => ?_
          calc μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤ 1 * ENNReal.ofReal (t ^ (q - 1)) :=
                mul_le_mul_left (prob_le_one) _
            _ = _ := one_mul _
      _ = ENNReal.ofReal (s ^ q / q) := by
          rw [← rkl_setIntegral_rpow_Ioc hq hs, ofReal_integral_eq_lintegral_ofReal
            (rkl_integrableOn_rpow_Ioc hq hs)]
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact Real.rpow_nonneg ht.1.le _
  -- far part
  have hexp : q - 1 - r < -1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => B * s ^ r * t ^ (q - 1 - r)) (Set.Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt hexp hs).const_mul _
  have h2 : ∫⁻ t in Set.Ioi s, μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
      ENNReal.ofReal (B * s ^ q / (r - q)) := by
    calc _ ≤ ∫⁻ t in Set.Ioi s, ENNReal.ofReal (B * s ^ r * t ^ (q - 1 - r)) := by
          refine setLIntegral_mono (by fun_prop) fun t ht => ?_
          have ht0 : 0 < t := hs.trans ht
          calc μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
                ENNReal.ofReal (B * (s / t) ^ r) * ENNReal.ofReal (t ^ (q - 1)) :=
                mul_le_mul_left (htail t (le_of_lt ht)) _
            _ = ENNReal.ofReal (B * s ^ r * t ^ (q - 1 - r)) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                rw [div_pow, show t ^ (q - 1 - (r : ℝ)) = t ^ (q - 1) / t ^ r by
                  rw [Real.rpow_sub ht0, Real.rpow_natCast]]
                field_simp
      _ = ENNReal.ofReal (B * s ^ q / (r - q)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint]
          · congr 1
            rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp hs]
            have : q - 1 - r + 1 = q - r := by ring
            rw [this, Real.rpow_sub hs, Real.rpow_natCast,
              show q - (r : ℝ) = -((r : ℝ) - q) by ring]
            field_simp
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have ht0 : 0 < t := hs.trans ht
            positivity
  refine le_trans (mul_le_mul_right (add_le_add h1 h2) _) (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul hq.le]
  congr 1
  field_simp

end Tail

/-!
## 3. Polynomial moments of a fixed-rank eigenvalue under the physical law
-/

section Moments

/-- `E|g|^{2r}` for a standard real Gaussian `g`. -/
def rklGaussMoment (r : ℕ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (|x| ^ (2 * r)) ∂gaussianReal 0 1

theorem rkl_gaussMoment_lt_top (r : ℕ) : rklGaussMoment r < ⊤ := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp [rklGaussMoment]
  have hm := (memLp_id_gaussianReal (μ := 0) (v := 1) ((2 * r : ℕ) : ℝ≥0)).eLpNorm_lt_top
  have h2 : ((((2 * r : ℕ) : ℝ≥0)) : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]; exact_mod_cast (by omega : 2 * r ≠ 0)
  have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h2 ENNReal.coe_ne_top hm
  refine lt_of_le_of_lt (le_of_eq ?_) this
  unfold rklGaussMoment
  refine lintegral_congr fun x => ?_
  simp only [id, Real.enorm_eq_ofReal_abs, ENNReal.coe_toReal, NNReal.coe_natCast]
  rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (abs_nonneg x)]

theorem rkl_lintegral_gauss_le (r : ℕ) {v : ℝ≥0} (hv : v ≤ 1) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ (2 * r)) ∂gaussianReal 0 v ≤ rklGaussMoment r := by
  have hlaw : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr
    ext
    simp
  rw [hlaw, lintegral_map (by fun_prop) (by fun_prop)]
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  have hs0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  have hs1 : Real.sqrt v ≤ 1 := Real.sqrt_le_one.mpr (by exact_mod_cast hv)
  rw [abs_mul, abs_of_nonneg hs0, mul_pow]
  calc Real.sqrt v ^ (2 * r) * |x| ^ (2 * r) ≤ 1 * |x| ^ (2 * r) := by
        gcongr; exact pow_le_one₀ hs0 hs1
    _ = _ := one_mul _

variable {p : Parameters}

theorem rkl_entryVariance_le_one (x y : p.Site) : p.entryVariance x y ≤ 1 := by
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hc : p.c ≤ 1 := by unfold Parameters.c; linarith [p.b_pos]
  unfold Parameters.entryVariance
  split_ifs
  · exact (div_le_self p.c_pos.le hW).trans hc
  · exact (div_le_self p.b_pos.le hW).trans (by linarith [p.b_lt_half])
  · norm_num

theorem rkl_coordVariance_le_one (i : p.GaussianCoordinate) :
    p.gaussianCoordinateVariance i ≤ 1 := by
  rcases i with x | ⟨x, y, _b⟩
  · exact rkl_entryVariance_le_one x x
  · have key : ∀ (c : Prop) [Decidable c] (a : ℝ≥0), a ≤ 1 → (if c then a else 0) ≤ 1 :=
      fun c _ a ha => by split_ifs <;> simp [ha]
    refine key _ _ ?_
    have h1 : p.entryVariance x y / 2 ≤ 1 := by linarith [rkl_entryVariance_le_one x y]
    exact h1

theorem rkl_single_le (z : p.GaussianCoordinate → ℝ) (i : p.GaussianCoordinate) :
    |z i| ≤ ∑ j, |z j| :=
  Finset.single_le_sum (f := fun j => |z j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem rkl_recon_entry_le (z : p.GaussianCoordinate → ℝ) (x y : p.Site) :
    ‖p.gaussianReconstruction z x y‖ ≤ 2 * ∑ j, |z j| := by
  have hpair : ∀ a b : p.GaussianCoordinate,
      ‖(z a : ℂ) + Complex.I * (z b : ℂ)‖ ≤ 2 * ∑ j, |z j| := by
    intro a b
    calc _ ≤ ‖(z a : ℂ)‖ + ‖Complex.I * (z b : ℂ)‖ := norm_add_le _ _
      _ = |z a| + |z b| := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ _ := by linarith [rkl_single_le z a, rkl_single_le z b]
  have hpair' : ∀ a b : p.GaussianCoordinate,
      ‖(z a : ℂ) - Complex.I * (z b : ℂ)‖ ≤ 2 * ∑ j, |z j| := by
    intro a b
    calc _ ≤ ‖(z a : ℂ)‖ + ‖Complex.I * (z b : ℂ)‖ := norm_sub_le _ _
      _ = |z a| + |z b| := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ _ := by linarith [rkl_single_le z a, rkl_single_le z b]
  unfold Parameters.gaussianReconstruction
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs]
    have := rkl_single_le z (.inl x)
    have h0 : 0 ≤ ∑ j, |z j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  · exact hpair _ _
  · exact hpair' _ _

theorem rkl_abs_eigenvalue_le {H : p.SiteMatrix} (hH : H.IsHermitian) {β : ℝ}
    (hβ : ∀ x y, ‖H x y‖ ≤ β) (α : Fin p.N) :
    |physicalOrderedEigenvalue p H α| ≤ p.N * β := by
  unfold physicalOrderedEigenvalue
  rw [rawIncreasingEigenvalue_eq _ H hH]
  unfold Foundations.Spectral.increasingEigenvalue
  exact (hH.abs_eigenvalues₀_le_of_entry_le hβ (physicalSpectralRank p α).rev).trans
    (le_of_eq (by rw [physicalSite_card]))

theorem rkl_card_coord : Fintype.card p.GaussianCoordinate = p.N + p.N * p.N * 2 := by
  simp only [Parameters.GaussianCoordinate, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_bool, ZMod.card, Fintype.card_fin, Parameters.N]
  ring

theorem rkl_one_le_N : (1 : ℝ) ≤ p.N := by exact_mod_cast p.N_pos

theorem rkl_law_eq (model : p.GaussianRingModel) :
    (model.law : Measure p.SiteMatrix) = Measure.map p.gaussianReconstruction
      (Measure.pi fun i => gaussianReal 0 (p.gaussianCoordinateVariance i)) := by
  rw [model.law_eq_gaussianMatrixLaw]
  rfl

/-- Pointwise power bound along the coordinates. -/
theorem rkl_pow_le_coords (r : ℕ) (hr : 1 ≤ r) (α : Fin p.N) {e : ℝ} (he : |e| ≤ 2)
    (z : p.GaussianCoordinate → ℝ) :
    |physicalOrderedEigenvalue p (p.gaussianReconstruction z) α - e| ^ (2 * r) ≤
      ((2 * p.N) ^ (2 * r) * ((Fintype.card p.GaussianCoordinate : ℝ) + 1) ^ (2 * r - 1)) *
        (1 + ∑ j, |z j| ^ (2 * r)) := by
  set Z := ∑ j, |z j| with hZ
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hN := rkl_one_le_N (p := p)
  have hlam := rkl_abs_eigenvalue_le (p.gaussianReconstruction_isHermitian z)
    (rkl_recon_entry_le z) α
  have h1 : |physicalOrderedEigenvalue p (p.gaussianReconstruction z) α - e| ≤
      2 * p.N * (Z + 1) := by
    calc _ ≤ |physicalOrderedEigenvalue p (p.gaussianReconstruction z) α| + |e| := abs_sub _ _
      _ ≤ p.N * (2 * Z) + 2 := add_le_add hlam he
      _ ≤ 2 * p.N * (Z + 1) := by nlinarith
  have h2 : (Z + 1) ^ (2 * r) ≤ ((Fintype.card p.GaussianCoordinate : ℝ) + 1) ^ (2 * r - 1) *
      (1 + ∑ j, |z j| ^ (2 * r)) := by
    have hs := pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset (Option p.GaussianCoordinate)))
      (f := fun o => Option.elim o 1 fun j => |z j|) (fun o _ => by
        cases o <;> simp [abs_nonneg]) (2 * r - 1)
    have he2 : 2 * r - 1 + 1 = 2 * r := by omega
    rw [he2] at hs
    simp only [Finset.card_univ, Fintype.card_option, Fintype.sum_option, Option.elim_none,
      Option.elim_some, one_pow] at hs
    rw [add_comm Z 1, hZ]
    push_cast at hs
    exact hs
  calc _ ≤ (2 * p.N * (Z + 1)) ^ (2 * r) := pow_le_pow_left₀ (abs_nonneg _) h1 _
    _ = (2 * p.N) ^ (2 * r) * (Z + 1) ^ (2 * r) := mul_pow _ _ _
    _ ≤ (2 * p.N) ^ (2 * r) * (((Fintype.card p.GaussianCoordinate : ℝ) + 1) ^ (2 * r - 1) *
          (1 + ∑ j, |z j| ^ (2 * r))) := by gcongr
    _ = _ := by ring

/-- **Polynomial moments of a fixed-rank eigenvalue.** Physical law, every `p`, rank `α`
and real `|e| ≤ 2`: `E|λ_α - e|^{2r} ≤ K_r N^{6r+2}` with `K_r` depending only on `r`. -/
theorem rkl_moment_le (r : ℕ) (hr : 1 ≤ r) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) (e : ℝ), |e| ≤ 2 →
      ∫⁻ H, ENNReal.ofReal (|physicalOrderedEigenvalue p H α - e| ^ (2 * r))
          ∂(model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal (K * (p.N : ℝ) ^ (6 * r + 2)) := by
  set g := (rklGaussMoment r).toReal with hg
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  refine ⟨2 ^ (2 * r) * 4 ^ (2 * r + 1) * (1 + g), by positivity, fun p model α e he => ?_⟩
  set M : ℝ := (Fintype.card p.GaussianCoordinate : ℝ) with hM
  set A : ℝ := (2 * p.N) ^ (2 * r) * (M + 1) ^ (2 * r - 1) with hA
  have hA0 : 0 ≤ A := by positivity
  have hmeasF : Measurable fun H : p.SiteMatrix =>
      ENNReal.ofReal (|physicalOrderedEigenvalue p H α - e| ^ (2 * r)) :=
    ENNReal.measurable_ofReal.comp
      ((((measurable_physicalOrderedEigenvalue p α).sub_const e).abs).pow_const _)
  rw [rkl_law_eq model, lintegral_map hmeasF p.measurable_gaussianReconstruction]
  have hcoord : ∀ j : p.GaussianCoordinate,
      ∫⁻ z, ENNReal.ofReal (|z j| ^ (2 * r))
          ∂(Measure.pi fun i => gaussianReal 0 (p.gaussianCoordinateVariance i)) ≤
        ENNReal.ofReal g := by
    intro j
    rw [(measurePreserving_eval (fun i => gaussianReal 0 (p.gaussianCoordinateVariance i)) j
      ).lintegral_comp (f := fun x : ℝ => ENNReal.ofReal (|x| ^ (2 * r))) (by fun_prop)]
    rw [hg, ENNReal.ofReal_toReal (rkl_gaussMoment_lt_top r).ne]
    exact rkl_lintegral_gauss_le r (rkl_coordVariance_le_one j)
  calc ∫⁻ z, ENNReal.ofReal (|physicalOrderedEigenvalue p (p.gaussianReconstruction z) α - e| ^
          (2 * r)) ∂(Measure.pi fun i => gaussianReal 0 (p.gaussianCoordinateVariance i))
      ≤ ∫⁻ z, ENNReal.ofReal A * (1 + ∑ j, ENNReal.ofReal (|z j| ^ (2 * r)))
          ∂(Measure.pi fun i => gaussianReal 0 (p.gaussianCoordinateVariance i)) := by
        refine lintegral_mono fun z => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity), ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun j _ => by positivity),
          ← ENNReal.ofReal_mul hA0]
        exact ENNReal.ofReal_le_ofReal (rkl_pow_le_coords r hr α he z)
    _ = ENNReal.ofReal A * (1 + ∑ j, ∫⁻ z, ENNReal.ofReal (|z j| ^ (2 * r))
          ∂(Measure.pi fun i => gaussianReal 0 (p.gaussianCoordinateVariance i))) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one, lintegral_finsetSum _ (fun j _ => by fun_prop)]
    _ ≤ ENNReal.ofReal A * (1 + ∑ _j : p.GaussianCoordinate, ENNReal.ofReal g) := by
        gcongr with j; exact hcoord j
    _ = ENNReal.ofReal (A * (1 + M * g)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (by positivity), ← ENNReal.ofReal_mul hA0]
    _ ≤ ENNReal.ofReal (2 ^ (2 * r) * 4 ^ (2 * r + 1) * (1 + g) * (p.N : ℝ) ^ (6 * r + 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hN := rkl_one_le_N (p := p)
        have hMc : M = p.N + p.N * p.N * 2 := by rw [hM, rkl_card_coord]; push_cast; ring
        have hM1 : M + 1 ≤ 4 * (p.N : ℝ) ^ 2 := by rw [hMc]; nlinarith
        have hM0 : 0 ≤ M := by positivity
        have h4 : (1 : ℝ) ≤ 4 * (p.N : ℝ) ^ 2 := by nlinarith
        have hpow : (M + 1) ^ (2 * r - 1) ≤ (4 * (p.N : ℝ) ^ 2) ^ (2 * r) :=
          (pow_le_pow_left₀ (by positivity) hM1 _).trans (pow_le_pow_right₀ h4 (by omega))
        have hsec : 1 + M * g ≤ (1 + g) * (4 * (p.N : ℝ) ^ 2) := by nlinarith
        calc A * (1 + M * g) ≤ ((2 * p.N) ^ (2 * r) * (4 * (p.N : ℝ) ^ 2) ^ (2 * r)) *
              ((1 + g) * (4 * (p.N : ℝ) ^ 2)) := by
              rw [hA]; gcongr
          _ = _ := by ring

end Moments

/-!
## 4. Location under the physical law
-/

section Location

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Integer moments from an `eLpNorm` bound. -/
theorem rkl_lintegral_pow_le_of_eLpNorm {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {r : ℕ}
    (hr : 1 ≤ r) {D : ℝ} (h : eLpNorm f (ENNReal.ofReal r) μ ≤ ENNReal.ofReal D) :
    ∫⁻ ω, ENNReal.ofReal |f ω| ^ r ∂μ ≤ ENNReal.ofReal D ^ r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hr0)
    ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hr0.le] at h
  have h2 := ENNReal.rpow_le_rpow h hr0.le
  rw [one_div, ENNReal.rpow_inv_rpow hr0.ne', ENNReal.rpow_natCast] at h2
  refine le_trans (le_of_eq ?_) h2
  refine lintegral_congr fun ω => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_natCast]

theorem rkl_density_ge {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1 / 2) {E : ℝ}
    (hE : E ∈ bulkInterval (ϑ / 2)) :
    Real.sqrt ϑ / (2 * Real.pi) ≤ Parameters.semicircleDensity E := by
  unfold Parameters.semicircleDensity
  obtain ⟨h1, h2⟩ := hE
  refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by positivity)
  nlinarith

theorem rkl_cdf_increment {a b ρ₀ : ℝ} (hab : a ≤ b)
    (hρ : ∀ x ∈ Set.Icc a b, ρ₀ ≤ Parameters.semicircleDensity x) :
    ρ₀ * (b - a) ≤ semicircleCDF b - semicircleCDF a := by
  have hi : ∀ u v : ℝ, IntervalIntegrable Parameters.semicircleDensity volume u v :=
    fun u v => continuous_semicircleDensity.intervalIntegrable u v
  unfold semicircleCDF
  rw [intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)]
  have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const (hi a b) hρ
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

variable {p : Parameters}

theorem rkl_spec_monotone_ae (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), Monotone (rklSpec p H) := by
  filter_upwards [physicalOrderedEigenvalue_monotone_ae p model] with H hH
  exact fun α β h => hH α β h

theorem rkl_measurable_countBelow (E m : ℝ) (r : ℕ) :
    Measurable fun H : p.SiteMatrix =>
      ENNReal.ofReal |(countBelow (rklSpec p H) E : ℝ) - m| ^ r :=
  (ENNReal.measurable_ofReal.comp
    ((((MassTransport.measurable_countBelow_real E).comp rkl_measurable_spec).sub_const
      m).abs)).pow_const r

/-- **Count tails at `e ± t`** (monotonicity at the deterministic energies `e_α ± t`). -/
theorem rkl_near_tail (model : p.GaussianRingModel) (α : Fin p.N) {e ρ₀ D t : ℝ} {r : ℕ}
    (hρ : 0 < ρ₀) (ht : 0 < t) (hD : 0 ≤ D)
    (hF : semicircleCDF e = ((α.val + 1 : ℕ) : ℝ) / p.N)
    (hlow : semicircleCDF (e - t) ≤ semicircleCDF e - ρ₀ * t)
    (hup : semicircleCDF e + ρ₀ * t ≤ semicircleCDF (e + t))
    (hm1 : ∫⁻ H, ENNReal.ofReal |(physicalCount p H (e - t) : ℝ) - p.N * semicircleCDF (e - t)| ^ r
      ∂(model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal D ^ r)
    (hm2 : ∫⁻ H, ENNReal.ofReal |(physicalCount p H (e + t) : ℝ) - p.N * semicircleCDF (e + t)| ^ r
      ∂(model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal D ^ r) :
    (model.law : Measure p.SiteMatrix) {H | t < |physicalOrderedEigenvalue p H α - e|} ≤
      ENNReal.ofReal (2 * D ^ r / (p.N * ρ₀ * t) ^ r) := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hNF : (p.N : ℝ) * semicircleCDF e = α.val + 1 := by
    rw [hF]; field_simp; push_cast; ring
  have hlower : (fun E => (p.N : ℝ) * semicircleCDF E) (e - t) ≤
      (α.val + 1 : ℝ) - p.N * ρ₀ * t := by
    simp only
    nlinarith
  have hupper : (α.val + 1 : ℝ) + p.N * ρ₀ * t ≤
      (fun E => (p.N : ℝ) * semicircleCDF E) (e + t) := by
    simp only
    nlinarith
  have key := threshold_pow_mul_measure_rank_deviation_le_count_moments_of_ae_monotone
    (model.law : Measure p.SiteMatrix) (rklSpec p) (rkl_spec_monotone_ae model) α
    (fun E => (p.N : ℝ) * semicircleCDF E) e t (p.N * ρ₀ * t) r hlower hupper
    (rkl_measurable_countBelow _ _ r).aemeasurable (rkl_measurable_countBelow _ _ r).aemeasurable
  have hcong : ∀ E : ℝ, (∫⁻ H, ENNReal.ofReal |(countBelow (rklSpec p H) E : ℝ) -
      p.N * semicircleCDF E| ^ r ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ H, ENNReal.ofReal |(physicalCount p H E : ℝ) - p.N * semicircleCDF E| ^ r
        ∂(model.law : Measure p.SiteMatrix) := by
    intro E
    refine lintegral_congr_ae ?_
    filter_upwards [model.isPhysical.1] with H hH
    rw [rkl_physicalCount_eq hH E]
  rw [hcong, hcong] at key
  have hsum := key.trans (add_le_add hm1 hm2)
  have ha : 0 < (p.N : ℝ) * ρ₀ * t := by positivity
  rw [ENNReal.ofReal_div_of_pos (pow_pos ha r), ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr (pow_pos ha r)).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm,
    ENNReal.ofReal_pow ha.le]
  refine hsum.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hD, ← two_mul, ENNReal.ofReal_ofNat]

/-- **Far tail** by interpolating a small probability and a high moment. -/
theorem rkl_far_tail [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X) {δ t A Mb : ℝ} {r : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (hA0 : 0 ≤ A) (hM0 : 0 ≤ Mb)
    (hA : μ {ω | δ < |X ω|} ≤ ENNReal.ofReal A)
    (hmom : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 * r)) ∂μ ≤ ENNReal.ofReal Mb) :
    μ {ω | t < |X ω|} ≤ ENNReal.ofReal (Real.sqrt (A * Mb) / t ^ r) := by
  have ht0 : 0 < t := hδ.trans hδt
  have h1 : μ {ω | t < |X ω|} ≤ ENNReal.ofReal A :=
    (measure_mono fun ω (h : t < |X ω|) => (show δ < |X ω| from hδt.trans h)).trans hA
  have h2 : μ {ω | t < |X ω|} ≤ ENNReal.ofReal (Mb / t ^ (2 * r)) := by
    have hm := mul_meas_ge_le_lintegral₀ (μ := μ)
      (f := fun ω => ENNReal.ofReal (|X ω| ^ (2 * r)))
      ((ENNReal.measurable_ofReal.comp (hX.abs.pow_const _)).aemeasurable)
      (ENNReal.ofReal (t ^ (2 * r)))
    have hsub : {ω | t < |X ω|} ⊆
        {ω | ENNReal.ofReal (t ^ (2 * r)) ≤ ENNReal.ofReal (|X ω| ^ (2 * r))} := by
      intro ω (h : t < |X ω|)
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht0.le h.le _)
    have hm2 := (mul_le_mul_right (measure_mono hsub) _).trans (hm.trans hmom)
    rw [ENNReal.ofReal_div_of_pos (pow_pos ht0 _), ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.mpr (pow_pos ht0 _)).ne') (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact hm2
  have hfin : μ {ω | t < |X ω|} ≠ ⊤ := measure_ne_top _ _
  set P := (μ {ω | t < |X ω|}).toReal with hP
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  have hP1 : P ≤ A := ENNReal.toReal_le_of_le_ofReal hA0 h1
  have hP2 : P ≤ Mb / t ^ (2 * r) := ENNReal.toReal_le_of_le_ofReal (by positivity) h2
  have htr : 0 < t ^ r := pow_pos ht0 r
  have hPP : P * P ≤ A * (Mb / t ^ (2 * r)) := mul_le_mul hP1 hP2 hP0 hA0
  have hfinal : P ≤ Real.sqrt (A * Mb) / t ^ r := by
    rw [le_div_iff₀ htr]
    refine Real.le_sqrt_of_sq_le ?_
    have ht2 : t ^ (2 * r) = t ^ r * t ^ r := by rw [two_mul, pow_add]
    rw [ht2] at hPP
    have := mul_le_mul_of_nonneg_right hPP (le_of_lt (mul_pos htr htr))
    calc (P * t ^ r) ^ 2 = P * P * (t ^ r * t ^ r) := by ring
      _ ≤ A * (Mb / (t ^ r * t ^ r)) * (t ^ r * t ^ r) := this
      _ = A * Mb := by field_simp
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hfinal

/-- `D / (N ρ₀ t) = (M / ρ₀) (s / t)` with `D = M √W`, `s = 1/(n √W)`. -/
theorem rkl_scale_eq (p : Parameters) {M ρ₀ t : ℝ} (hρ : 0 < ρ₀) (ht : 0 < t) :
    M * Real.sqrt p.W / (p.N * ρ₀ * t) = M / ρ₀ * (1 / (p.n * Real.sqrt p.W) / t) := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hsq : 0 < Real.sqrt p.W := Real.sqrt_pos.mpr hW
  have hWs : (p.W : ℝ) = Real.sqrt p.W * Real.sqrt p.W := (Real.mul_self_sqrt hW.le).symm
  have hN : (p.N : ℝ) = p.n * p.W := by unfold Parameters.N; push_cast; ring
  rw [hN]
  field_simp
  linear_combination (-M) * hWs

/-- **Rank location under the physical law**, from the physical count moments. -/
theorem rkl_location_physical (h : RklPhysicalCount) (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (T ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
        eLpNorm (fun H => physicalOrderedEigenvalue p H α - classicalLocation p α)
            (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤
          ENNReal.ofReal (C / (p.n * Real.sqrt p.W)) := by
  set κ := ϑ / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  set r := ⌈q⌉₊ + 1 with hr
  have hr1 : 1 ≤ r := by omega
  have hqr : q < r := by
    have := Nat.le_ceil q
    rw [hr]; push_cast; linarith
  set r' := 14 * r + 4 with hr'
  have hr'1 : 1 ≤ r' := by omega
  obtain ⟨C1, hC1⟩ := h.1 b hb hb' κ T hκ0 r (by exact_mod_cast hr1)
  obtain ⟨C2, hC2⟩ := h.1 b hb hb' κ T hκ0 r' (by exact_mod_cast hr'1)
  obtain ⟨K, hK0, hK⟩ := rkl_moment_le r hr1
  set ρ₀ := Real.sqrt ϑ / (2 * Real.pi) with hρ₀
  have hρ0 : 0 < ρ₀ := by positivity
  set c1 := 2 * (max C1 0 / ρ₀) ^ r with hc1
  set c2 := 2 * (max C2 0 / ρ₀) ^ r' with hc2
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  set B := c1 + Real.sqrt (c2 * K / κ ^ r') with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨(1 + q * B / (r - q)) ^ (1 / q), fun p hpb hnT model α hα => ?_⟩
  set μ := (model.law : Measure p.SiteMatrix) with hμ
  set e := classicalLocation p α with he_def
  have he : e ∈ bulkInterval ϑ := classicalLocation_mem_bulkInterval hϑ p α hα
  have heI := classicalLocation_mem_Icc p α
  have heabs : |e| ≤ 2 := abs_le.mpr ⟨heI.1, heI.2⟩
  have hF := semicircleCDF_classicalLocation p α
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  set s := 1 / (p.n * Real.sqrt p.W) with hs_def
  have hs : 0 < s := by positivity
  -- near tails
  have near : ∀ (r0 : ℕ) (C0 : ℝ), 1 ≤ r0 →
      (∀ E ∈ bulkInterval κ, eLpNorm (fun H => (physicalCount p H E : ℝ) - p.N * semicircleCDF E)
        (ENNReal.ofReal r0) μ ≤ ENNReal.ofReal (C0 * Real.sqrt p.W)) →
      ∀ t, 0 < t → t ≤ κ → μ {H | t < |physicalOrderedEigenvalue p H α - e|} ≤
        ENNReal.ofReal (2 * (max C0 0 / ρ₀) ^ r0 * (s / t) ^ r0) := by
    intro r0 C0 hr0 hC0 t ht htκ
    have hmem1 : e - t ∈ bulkInterval κ := ⟨by linarith [he.1], by linarith [he.2]⟩
    have hmem2 : e + t ∈ bulkInterval κ := ⟨by linarith [he.1], by linarith [he.2]⟩
    have hmom : ∀ E ∈ bulkInterval κ, ∫⁻ H, ENNReal.ofReal |(physicalCount p H E : ℝ) -
        p.N * semicircleCDF E| ^ r0 ∂μ ≤ ENNReal.ofReal (max C0 0 * Real.sqrt p.W) ^ r0 := by
      intro E hE
      refine rkl_lintegral_pow_le_of_eLpNorm ?_ hr0 ((hC0 E hE).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.sqrt_nonneg _))))
      have hmc : Measurable fun H : p.SiteMatrix => (physicalCount p H E : ℝ) :=
        Layers.cph_measurable_negativeCount.comp (measurable_id.sub_const _)
      exact (hmc.sub_const _).aestronglyMeasurable
    have hdens : ∀ x ∈ Set.Icc (e - t) (e + t), ρ₀ ≤ Parameters.semicircleDensity x :=
      fun x hx => rkl_density_ge hϑ hϑ' ⟨by linarith [hx.1, hmem1.1], by linarith [hx.2, hmem2.2]⟩
    have hlow := rkl_cdf_increment (a := e - t) (b := e) (by linarith)
      fun x hx => hdens x ⟨hx.1, by linarith [hx.2]⟩
    have hup := rkl_cdf_increment (a := e) (b := e + t) (by linarith)
      fun x hx => hdens x ⟨by linarith [hx.1], hx.2⟩
    have key := rkl_near_tail model α hρ0 ht (by positivity) hF (by linarith) (by linarith)
      (hmom _ hmem1) (hmom _ hmem2)
    refine key.trans (le_of_eq ?_)
    congr 1
    rw [show (2 : ℝ) * (max C0 0 / ρ₀) ^ r0 * (s / t) ^ r0 =
        2 * (max C0 0 * Real.sqrt p.W / (p.N * ρ₀ * t)) ^ r0 by
      rw [rkl_scale_eq p hρ0 ht, mul_pow, mul_assoc], div_pow, mul_div_assoc]
  -- the tail hypothesis
  have htail : ∀ t, s ≤ t → μ {H | t < |physicalOrderedEigenvalue p H α - e|} ≤
      ENNReal.ofReal (B * (s / t) ^ r) := by
    intro t hst
    have ht0 : 0 < t := hs.trans_le hst
    by_cases htκ : t ≤ κ
    · refine (near r C1 hr1 (fun E hE => hC1 p hpb hnT model E hE) t ht0 htκ).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have : c1 ≤ B := le_add_of_nonneg_right (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · have hκt : κ < t := lt_of_not_ge htκ
      have hA := near r' C2 hr'1 (fun E hE => hC2 p hpb hnT model E hE) κ hκ0 le_rfl
      have hfar := rkl_far_tail (μ := μ)
        ((measurable_physicalOrderedEigenvalue p α).sub_const e) hκ0 hκt (by positivity)
        (by positivity) hA (hK p model α e heabs)
      refine hfar.trans (ENNReal.ofReal_le_ofReal ?_)
      -- `s^{r'} N^{6r+2} ≤ s^{2r}`
      have hN1 := rkl_one_le_N (p := p)
      have hsN : s ^ 2 * p.N ≤ 1 := by
        have hN : (p.N : ℝ) = p.n * p.W := by unfold Parameters.N; push_cast; ring
        have hs2 : s ^ 2 = 1 / (p.n ^ 2 * p.W) := by
          rw [hs_def, div_pow, one_pow, mul_pow, Real.sq_sqrt hW.le]
        have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
        rw [hs2, hN, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        nlinarith
      have hpow : s ^ r' * (p.N : ℝ) ^ (6 * r + 2) ≤ s ^ r * s ^ r := by
        have e1 : s ^ r' * (p.N : ℝ) ^ (6 * r + 2) =
            s ^ r * s ^ r * (s ^ 2 * p.N) ^ (6 * r + 2) := by
          rw [hr', mul_pow, ← pow_mul]; ring
        rw [e1]
        exact mul_le_of_le_one_right (by positivity)
          (pow_le_one₀ (by positivity) hsN)
      have hprod : c2 * (s / κ) ^ r' * (K * (p.N : ℝ) ^ (6 * r + 2)) ≤
          (c2 * K / κ ^ r') * (s ^ r * s ^ r) := by
        have : c2 * (s / κ) ^ r' * (K * (p.N : ℝ) ^ (6 * r + 2)) =
            (c2 * K / κ ^ r') * (s ^ r' * (p.N : ℝ) ^ (6 * r + 2)) := by
          rw [div_pow]; field_simp
        rw [this]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      calc Real.sqrt (c2 * (s / κ) ^ r' * (K * (p.N : ℝ) ^ (6 * r + 2))) / t ^ r
          ≤ Real.sqrt ((c2 * K / κ ^ r') * (s ^ r * s ^ r)) / t ^ r := by
            gcongr
        _ = Real.sqrt (c2 * K / κ ^ r') * (s / t) ^ r := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity), div_pow]
            ring
        _ ≤ B * (s / t) ^ r := by
            refine mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hc10) (by positivity)
  -- integrate the tail
  have hqpos : 0 < q := by linarith
  have hYm : Measurable fun H : p.SiteMatrix => |physicalOrderedEigenvalue p H α - e| :=
    ((measurable_physicalOrderedEigenvalue p α).sub_const e).abs
  have hlin := rkl_lintegral_rpow_le_of_tail (μ := μ) hYm.aemeasurable (fun H => abs_nonneg _)
    hqpos hqr hs hB0 htail
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hqpos) ENNReal.ofReal_ne_top
    ((measurable_physicalOrderedEigenvalue p α).sub_const e).aestronglyMeasurable,
    ENNReal.toReal_ofReal hqpos.le]
  have hcongr : ∫⁻ H, ‖physicalOrderedEigenvalue p H α - e‖ₑ ^ q ∂μ =
      ∫⁻ H, ENNReal.ofReal (|physicalOrderedEigenvalue p H α - e| ^ q) ∂μ := by
    refine lintegral_congr fun H => ?_
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hqpos.le]
  rw [hcongr]
  have hc : 0 ≤ 1 + q * B / (r - q) := by
    have : 0 < (r : ℝ) - q := by linarith
    positivity
  calc (∫⁻ H, ENNReal.ofReal (|physicalOrderedEigenvalue p H α - e| ^ q) ∂μ) ^ (1 / q)
      ≤ (ENNReal.ofReal (s ^ q * (1 + q * B / (r - q)))) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hlin (by positivity)
    _ = ENNReal.ofReal ((1 + q * B / (r - q)) ^ (1 / q) / (p.n * Real.sqrt p.W)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          Real.mul_rpow (by positivity) hc, ← Real.rpow_mul hs.le, mul_one_div_cancel hqpos.ne',
          Real.rpow_one, hs_def]
        ring_nf

end Location

/-!
## 5. Eigenvalue-only transport to the block-mass and pair-mass laws
-/

section Transport

variable {p : Parameters}

/-- The cyclic shift used by the transport: `H ↦ H(· - s)` blockwise. -/
def rklShift (p : Parameters) (s : ZMod p.n) (H : p.SiteMatrix) : p.SiteMatrix :=
  p.siteReindexMatrix (p.cyclicSiteEquiv (-s)) H

/-- The cyclic mass symmetry of the selected rank `α` under the physical law. -/
def rklSymm (model : p.GaussianRingModel) (α : Fin p.N) :
    MassTransport.CyclicMassSymmetry (model.law : Measure p.SiteMatrix) p.n where
  shift := rklShift p
  mass k H := ENNReal.ofReal (physicalOrderedBlockMass p H α k)
  preserving s := ⟨p.measurable_siteReindexMatrix _, model.map_cyclicMatrix (-s)⟩
  measurable_mass k := ENNReal.measurable_ofReal.comp (measurable_physicalOrderedBlockMass p α k)
  sum_mass := by
    filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => physicalOrderedBlockMass_nonneg p H α k),
      hH α, ENNReal.ofReal_one]
  covariant s k := by
    filter_upwards [QUE.Fourier.physical_blockMass_cyclic_ae p model α (-s)] with H hH
    change ENNReal.ofReal (physicalOrderedBlockMass p
      (p.siteReindexMatrix (p.cyclicSiteEquiv (-s)) H) α k) = _
    rw [hH k, ← sub_eq_add_neg]

theorem rkl_physicalBlockMeasure_eq (model : p.GaussianRingModel) (α : Fin p.N) (k : ZMod p.n) :
    physicalBlockMeasure p model α k = MassTransport.blockMassMeasure (rklSymm model α) k := by
  unfold physicalBlockMeasure MassTransport.blockMassMeasure
  congr 1
  funext H
  change ENNReal.ofReal ((p.n : ℝ) * physicalOrderedBlockMass p H α k) =
    (p.n : ℝ≥0∞) * ENNReal.ofReal (physicalOrderedBlockMass p H α k)
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem rkl_physicalPairMeasure_eq (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n) :
    QUE.Fourier.physicalPairMeasure p model α i =
      MassTransport.pairMassMeasure (rklSymm model α) i (i + 1) := by
  unfold QUE.Fourier.physicalPairMeasure MassTransport.pairMassMeasure
  congr 1
  funext H
  change ((QUE.Fourier.physicalPairWeight p α i H : ℝ≥0) : ℝ≥0∞) =
    ((p.n : ℝ≥0∞) / 2) * (ENNReal.ofReal (physicalOrderedBlockMass p H α i) +
      ENNReal.ofReal (physicalOrderedBlockMass p H α (i + 1)))
  rw [← ENNReal.ofReal_coe_nnreal]
  change ENNReal.ofReal ((p.n : ℝ) / 2 * (physicalOrderedBlockMass p H α i +
    physicalOrderedBlockMass p H α (i + 1))) = _
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add
    (physicalOrderedBlockMass_nonneg p H α i) (physicalOrderedBlockMass_nonneg p H α (i + 1)),
    ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]

theorem rkl_spec_reindex {H : p.SiteMatrix} (hH : H.IsHermitian) (e : p.Site ≃ p.Site) :
    rklSpec p (p.siteReindexMatrix e H) = rklSpec p H := by
  have hsub : p.siteReindexMatrix e H = Matrix.reindex e.symm e.symm H := rfl
  have hH' : (p.siteReindexMatrix e H).IsHermitian := by
    rw [hsub]; exact hH.submatrix _
  have hcp : (p.siteReindexMatrix e H).charpoly = H.charpoly := by
    rw [hsub, charpoly_reindex]
  have heq := (Foundations.Spectral.increasingEigenvalue_eq_iff_charpoly_eq hH' hH).2 hcp
  funext α
  unfold rklSpec physicalOrderedEigenvalue
  rw [rawIncreasingEigenvalue_eq _ _ hH', rawIncreasingEigenvalue_eq _ _ hH, heq]

theorem rkl_spec_shift_ae (model : p.GaussianRingModel) (s : ZMod p.n) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), rklSpec p (rklShift p s H) = rklSpec p H := by
  filter_upwards [model.isPhysical.1] with H hH
  exact rkl_spec_reindex hH _

/-- **Transport of the whole ordered spectrum** to every mass law. -/
theorem rkl_map_spec (model : p.GaussianRingModel) (L : MassLaw p) :
    Measure.map (rklSpec p) (L.measure model) =
      Measure.map (rklSpec p) (model.law : Measure p.SiteMatrix) := by
  cases L with
  | physical => rfl
  | block α k =>
    change Measure.map (rklSpec p) (physicalBlockMeasure p model α k) = _
    rw [rkl_physicalBlockMeasure_eq]
    exact MassTransport.map_blockMassMeasure_eq (rklSymm model α) (rklSpec p) rkl_measurable_spec
      (rkl_spec_shift_ae model) k
  | pair α i =>
    change Measure.map (rklSpec p) (QUE.Fourier.physicalPairMeasure p model α i) = _
    rw [rkl_physicalPairMeasure_eq]
    exact MassTransport.map_pairMassMeasure_eq (rklSymm model α) (rklSpec p) rkl_measurable_spec
      (rkl_spec_shift_ae model) i (i + 1)

theorem rkl_ac (model : p.GaussianRingModel) (L : MassLaw p) :
    L.measure model ≪ (model.law : Measure p.SiteMatrix) := by
  cases L with
  | physical => exact Measure.AbsolutelyContinuous.rfl
  | block α k => exact withDensity_absolutelyContinuous _ _
  | pair α i => exact withDensity_absolutelyContinuous _ _

theorem rkl_eLpNorm_transfer (model : p.GaussianRingModel) (L : MassLaw p)
    (g : (Fin p.N → ℝ) → ℝ) (hg : Measurable g) (P : ℝ≥0∞) :
    eLpNorm (fun H => g (rklSpec p H)) P (L.measure model) =
      eLpNorm (fun H => g (rklSpec p H)) P (model.law : Measure p.SiteMatrix) := by
  have h1 := eLpNorm_map_measure (μ := L.measure model) (p := P) hg.aestronglyMeasurable
    rkl_measurable_spec.aemeasurable
  have h2 := eLpNorm_map_measure (μ := (model.law : Measure p.SiteMatrix)) (p := P)
    hg.aestronglyMeasurable rkl_measurable_spec.aemeasurable
  rw [rkl_map_spec] at h1
  exact h1.symm.trans h2

theorem rkl_integral_transfer (model : p.GaussianRingModel) (L : MassLaw p)
    (g : (Fin p.N → ℝ) → ℝ) (hg : Measurable g) :
    ∫ H, g (rklSpec p H) ∂(L.measure model) =
      ∫ H, g (rklSpec p H) ∂(model.law : Measure p.SiteMatrix) := by
  rw [← integral_map rkl_measurable_spec.aemeasurable hg.aestronglyMeasurable, rkl_map_spec,
    integral_map rkl_measurable_spec.aemeasurable hg.aestronglyMeasurable]

theorem rkl_count_ae (model : p.GaussianRingModel) (L : MassLaw p) (E : ℝ) :
    ∀ᵐ H ∂(L.measure model), (physicalCount p H E : ℝ) = countBelow (rklSpec p H) E := by
  filter_upwards [rkl_ac model L model.isPhysical.1] with H hH
  rw [rkl_physicalCount_eq hH E]

end Transport

/-!
## 6. Assembly
-/

/-- **The rank-location theorem** from its physical count fields: the location field under the
physical law, and all three fields under every block-mass and pair-mass law by transport, with the
physical constants. -/
theorem rankLocation_of_physicalCount (h : RklPhysicalCount) : RankLocationContract where
  count_moment := by
    intro b hb hb' κ T hκ q hq
    obtain ⟨Cq, hCq⟩ := h.1 b hb hb' κ T hκ q hq
    refine ⟨Cq, fun p hpb hnT model L E hE => ?_⟩
    have hmc : Measurable fun v : Fin p.N → ℝ => (countBelow v E : ℝ) - p.N * semicircleCDF E :=
      (MassTransport.measurable_countBelow_real E).sub_const _
    have hL : eLpNorm (fun H => (physicalCount p H E : ℝ) - p.N * semicircleCDF E)
        (ENNReal.ofReal q) (L.measure model) =
        eLpNorm (fun H => (countBelow (rklSpec p H) E : ℝ) - p.N * semicircleCDF E)
          (ENNReal.ofReal q) (L.measure model) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [rkl_count_ae model L E] with H hH
      rw [hH]
    have hP : eLpNorm (fun H => (physicalCount p H E : ℝ) - p.N * semicircleCDF E)
        (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) =
        eLpNorm (fun H => (countBelow (rklSpec p H) E : ℝ) - p.N * semicircleCDF E)
          (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [rkl_count_ae model .physical E] with H hH
      rw [hH]
    rw [hL, rkl_eLpNorm_transfer model L _ hmc, ← hP]
    exact hCq p hpb hnT model E hE
  count_mean := by
    intro b hb hb' κ T hκ
    obtain ⟨C, hC⟩ := h.2 b hb hb' κ T hκ
    refine ⟨C, fun p hpb hnT model L E hE => ?_⟩
    have hmc : Measurable fun v : Fin p.N → ℝ => (countBelow v E : ℝ) :=
      MassTransport.measurable_countBelow_real E
    have hL : ∫ H, (physicalCount p H E : ℝ) ∂(L.measure model) =
        ∫ H, (physicalCount p H E : ℝ) ∂(model.law : Measure p.SiteMatrix) := by
      rw [integral_congr_ae (rkl_count_ae model L E), rkl_integral_transfer model L _ hmc]
      exact (integral_congr_ae (rkl_count_ae model .physical E)).symm
    rw [hL]
    exact hC p hpb hnT model E hE
  location := by
    intro b hb hb' T ϑ hϑ hϑ' q hq
    obtain ⟨C, hC⟩ := rkl_location_physical h b hb hb' T ϑ hϑ hϑ' q hq
    refine ⟨C, fun p hpb hnT model L α hα => ?_⟩
    have hg : Measurable fun v : Fin p.N → ℝ => v α - classicalLocation p α :=
      (measurable_pi_apply α).sub_const _
    have := rkl_eLpNorm_transfer model L _ hg (ENNReal.ofReal q)
    change eLpNorm (fun H => rklSpec p H α - classicalLocation p α) (ENNReal.ofReal q)
      (L.measure model) ≤ _
    rw [this]
    exact hC p hpb hnT model α hα

end BlockBand.RankLocation

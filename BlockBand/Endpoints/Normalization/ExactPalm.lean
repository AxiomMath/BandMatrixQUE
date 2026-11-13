module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Coarea.ClockRank
public import BlockBand.Coarea.ContractClauses
public import BlockBand.Coarea.ProjectiveHaar
public import BlockBand.Coarea.GUELaw
public import BlockBand.Coarea.FixedOmegaGaussian

/-!
# The exact-Palm proposition, clauses `mass` and `index`, from the coarea theorem

The `mass` and `index` fields of `Clocks.ExactPalmContract` follow from `CoareaContract`, with no
other input; this is the local form of the coarea calculation. The clauses used are
`CoareaContract.formula` (index), `CoareaContract.formula_fixed` (mass, rank by rank) and
`CoareaContract.reconstructed_rank` (both), at `s = pairS p = min(b, c)` (`0 < s ≤ min(c, b)`). The
assembly into an `ExactPalmContract` is `exactPalmContract_holds`.

Proof (exact identities in `[0,∞]`; measures: the physical law on the left, `Pω`, Lebesgue
`de`, `projectiveHaar` and `GUE_{2W-1}(t)` on the right). The left side is transported to
`Pω ⊗ GUE_{2W}(t)` by `IsPairSplitting`. In the coarea integrand, for `Pω`-a.e. `ω` (Hermitian
`H_R`, `V`), Lebesgue-a.e. `E` (`det(H_R - E) ≠ 0`), `ν`-a.e. `v` (unit) and `GUE`-a.e. `G'`
(Hermitian): if `det M = 0` both sides vanish; otherwise `reconstructed_rank` gives
`λ_α = E` and `ψψ* = LL*/‖L‖²`, so `p_α = reconBlockMass` and `q_{αS} = ‖L‖⁻² = 1/(v*Dv)`
(`v*Dv = ‖L_E v‖²`, `reconstruction_of_coarea`). The indicator `1{N_-(M) + N_-(H_R-E) = α}`
is split into sectors `ℓ < 2W` (`sector_lintegral`, pointwise, since `N_-(M) ≤ 2W - 1`).
For `mass` the speed cancels against `q_{αS}`, and `Σ_α 1{ℓ + N_-(H_R-E) = α} = 1` for
`ℓ < 2W` because `N_-(H_R-E) ≤ |R| = N - 2W` (`sum_rank_indicator`); the sum over `α` is moved
through the `G`- and `e`-integrals using measurability of the angular fiber in `e`
(`measurable_pairSectorFiber`) at fixed `ω`.

Supporting facts: the a.e. lemmas, the sector identity and the measurability lemmas are
unconditional; the reconstruction and integrand identities on the support take `hC`
(`reconstructed_rank`).

The `massReal`, `indexReal` and `upper` fields of `ExactPalmContract` are proved separately.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexConjugate

section Scalars

variable (p : Parameters)

theorem pairS_pos : 0 < pairS p := lt_min p.b_pos p.c_pos

theorem pairS_le : pairS p ≤ min p.c p.b := (min_comm p.b p.c).le

end Scalars

section Lemmas

variable (p : Parameters) (i : ZMod p.n)

/-- For every splitting law, `Pω`-a.e. exterior has `H_R` and `V` Hermitian. -/
theorem ae_split_isHermitian (model : p.GaussianRingModel) (s : ℝ)
    (Pω : Measure (SplitState p i)) (hP : IsPairSplitting p i model s Pω) :
    ∀ᵐ ω ∂Pω, ω.1.IsHermitian ∧ ω.2.2.IsHermitian := by
  have h0 := model.isPhysical.1
  rw [← hP, ae_map_iff (ContractClauses.measurable_assemble p i).aemeasurable
    measurableSet_isHermitian] at h0
  filter_upwards [Measure.ae_ae_of_ae_prod h0] with ω hω
  obtain ⟨G, hG, hGh⟩ := (hω.and (GUELaw.ae_isHermitian_gueMeasure (ι := PairSite p i)
    (pairTime p s))).exists
  refine ⟨?_, ?_⟩
  · ext x y
    have h := hG.apply x.1 y.1
    simp only [assemble, x.2, y.2, dite_false] at h
    simpa [Matrix.conjTranspose_apply] using h
  · ext x y
    have h := hG.apply x.1 y.1
    have h' := hGh.apply x y
    simp only [assemble, x.2, y.2, dite_true, Subtype.coe_eta, star_add] at h
    rw [Matrix.conjTranspose_apply]
    rw [h'] at h
    exact add_right_cancel h

/-- `det(H_R - E) ≠ 0` for Lebesgue-a.e. real `E`. -/
theorem ae_det_shift_ne_zero (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) :
    ∀ᵐ E : ℝ, (H_R - (E : ℂ) • 1).det ≠ 0 := by
  have hfin : {E : ℝ | (H_R - (E : ℂ) • 1).det = 0}.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot (H_R.charpoly_monic.ne_zero)).preimage
      (Complex.ofReal_injective.injOn) |>.subset ?_
    intro E hE
    simp only [Set.mem_ofPred_eq] at hE ⊢
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot, Matrix.eval_charpoly]
    have : Matrix.scalar (ExteriorSite p i) (E : ℂ) - H_R = -(H_R - (E : ℂ) • 1) := by
      rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [this, Matrix.det_neg, hE, mul_zero]
  exact measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)

/-- `F(E)` is Hermitian for a Hermitian exterior. -/
theorem physicalCoareaF_isHermitian (ω : SplitState p i) (h1 : ω.1.IsHermitian)
    (h3 : ω.2.2.IsHermitian) (E : ℝ) :
    (physicalCoareaF ω.1 ω.2.1 ω.2.2 E).IsHermitian := by
  unfold physicalCoareaF physicalCoareaResolvent
  exact h3.sub (Matrix.isHermitian_conjTranspose_mul_mul _ (ClockRank.shift_isHermitian h1 E).inv)

/-- The reconstructed Gaussian is Hermitian. -/
theorem reconstructedGaussian_isHermitian
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian) (E : ℝ)
    (v : PairSite p i → ℂ) (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ)
    (hG' : G'.IsHermitian) :
    (reconstructedGaussian p i U ω E v G').IsHermitian := by
  have hF := physicalCoareaF_isHermitian p i ω h1 h3 E
  have hvv : (vecMulVec v (star v)).IsHermitian := by
    ext a b
    simp [vecMulVec, Matrix.conjTranspose_apply, mul_comm]
  have hE : ((E : ℂ) • vecMulVec v (star v)).IsHermitian := by
    rw [IsHermitian, Matrix.conjTranspose_smul, hvv.eq, Complex.star_def, Complex.conj_ofReal]
  unfold reconstructedGaussian
  exact (hE.add (Matrix.isHermitian_mul_mul_conjTranspose _
    ((Matrix.isHermitian_conjTranspose_mul_mul _ hF).add hG'))).sub hF

theorem re_star_dotProduct_self {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    (star w ⬝ᵥ w).re = ∑ k, ‖w k‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- `v*𝒟(E)v = ‖L_E v‖²` (`𝒟 = 1 + TᴴT`, `L_E v = (v, -Tv)`). -/
theorem clockSpeed_eq_l2Norm_sq (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) :
    clockSpeed p i ω E v = l2Norm (schurLift p i ω.1 ω.2.1 E v) ^ 2 := by
  set L := schurLift p i ω.1 ω.2.1 E v
  set T := physicalCoareaT ω.1 ω.2.1 E
  have hL2 : l2Norm L ^ 2 = ∑ x, ‖L x‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _)
  have hpair := ClockRank.schurLift_pair p i ω.1 ω.2.1 E v
  have hext := ClockRank.schurLift_ext p i ω.1 ω.2.1 E v
  have hS : ∑ s : PairSite p i, ‖L s.1‖ ^ 2 = ∑ s, ‖v s‖ ^ 2 :=
    Finset.sum_congr rfl fun s _ => by rw [← congrFun hpair s]
  have hR : ∑ r : ExteriorSite p i, ‖L r.1‖ ^ 2 = ∑ r, ‖(T *ᵥ v) r‖ ^ 2 :=
    Finset.sum_congr rfl fun r _ => by rw [show L r.1 = -(T *ᵥ v) r from congrFun hext r, norm_neg]
  rw [hL2, ClockRank.sum_site_real p i, hS, hR, clockSpeed, physicalCoareaD, schurClock,
    Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    re_star_dotProduct_self, re_star_dotProduct_self]

theorem sum_normSq_eq_one {ι : Type*} [Fintype ι] (v : ι → ℂ) (hv : l2Norm v = 1) :
    ∑ k, ‖v k‖ ^ 2 = 1 := by
  have h0 : 0 ≤ ∑ k, ‖v k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have := Real.sq_sqrt h0
  rw [← l2Norm, hv] at this
  linarith

/-- `v*𝒟v = ‖L_E v‖² ≥ ‖v‖² = 1` for unit `v`. -/
theorem one_le_clockSpeed (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ)
    (hv : l2Norm v = 1) : 1 ≤ clockSpeed p i ω E v := by
  rw [clockSpeed, physicalCoareaD, schurClock,
    Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    re_star_dotProduct_self, re_star_dotProduct_self, sum_normSq_eq_one v hv]
  have : 0 ≤ ∑ k, ‖(physicalCoareaT ω.1 ω.2.1 E *ᵥ v) k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  linarith

theorem clockSpeed_nonneg (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) :
    0 ≤ clockSpeed p i ω E v := by
  rw [clockSpeed_eq_l2Norm_sq]; exact sq_nonneg _

/-- **Reconstruction on the support** (consumes `CoareaContract.reconstructed_rank`): for a
Hermitian exterior, Hermitian `G'`, unit `v`, `det(H_R - E) ≠ 0`, `det M ≠ 0` and the rank
condition, the reconstructed matrix `H = assemble ω G_rec` has `λ_α(H) = E`, block masses
`p_α(H) = p(v,E)` (`reconBlockMass`) and pair mass `q_{αS}(H) = 1/(v*Dv)`. -/
theorem reconstruction_of_coarea (hC : CoareaContract) (α : Fin p.N)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian) (E : ℝ)
    (v : PairSite p i → ℂ) (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ)
    (hG' : G'.IsHermitian) (hv : l2Norm v = 1) (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0)
    (hM : (frameM p i U ω E v G').det ≠ 0)
    (hcnt : negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val) :
    physicalOrderedEigenvalue p (assemble p i ω (reconstructedGaussian p i U ω E v G')) α = E ∧
      blockMassVector p (assemble p i ω (reconstructedGaussian p i U ω E v G')) α =
        reconBlockMass p i ω E v ∧
      clockSpeed p i ω E v *
        pairMass p i α (assemble p i ω (reconstructedGaussian p i U ω E v G')) = 1 := by
  have hH := ContractClauses.assemble_isHermitian p i ω _ h1 h3
    (reconstructedGaussian_isHermitian p i U ω h1 h3 E v G' hG')
  obtain ⟨hlam, hproj⟩ := hC.reconstructed_rank p α i U hU ω E v G' hH hv hD hM hcnt
  set L := schurLift p i ω.1 ω.2.1 E v
  set H := assemble p i ω (reconstructedGaussian p i U ω E v G')
  have hpair := ClockRank.schurLift_pair p i ω.1 ω.2.1 E v
  have hpt : ∀ x, ‖physicalOrderedEigenvector p H α x‖ ^ 2 = (l2Norm L ^ 2)⁻¹ * ‖L x‖ ^ 2 := by
    intro x
    have h := congrArg Complex.re (hproj x x)
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, Complex.ofReal_re] at h
    rw [h]
    norm_cast
  have hspeed : clockSpeed p i ω E v = l2Norm L ^ 2 := clockSpeed_eq_l2Norm_sq p i ω E v
  have hpos : l2Norm L ^ 2 ≠ 0 := by
    rw [← hspeed]; exact (lt_of_lt_of_le one_pos (one_le_clockSpeed p i ω E v hv)).ne'
  refine ⟨hlam, ?_, ?_⟩
  · funext k
    simp only [blockMassVector, physicalOrderedBlockMass, reconBlockMass, hpt, hspeed]
    rw [← Finset.mul_sum, inv_mul_eq_div]
  · have hm : pairMass p i α H = (l2Norm L ^ 2)⁻¹ := by
      rw [ClockRank.pairMass_eq]
      simp_rw [hpt]
      rw [← Finset.mul_sum]
      have : ∑ s : PairSite p i, ‖L s.1‖ ^ 2 = 1 := by
        rw [← sum_normSq_eq_one v hv]
        exact Finset.sum_congr rfl fun s _ => by rw [← congrFun hpair s]
      rw [this, mul_one]
    rw [hm, hspeed, mul_inv_cancel₀ hpos]

theorem nonempty_pairSite : Nonempty (PairSite p i) :=
  ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩

theorem negativeCount_le_card {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    negativeCount M ≤ Fintype.card ι := by
  classical
  unfold negativeCount
  split_ifs
  · exact (Finset.card_filter_le _ _).trans (Finset.card_univ).le
  · exact Nat.zero_le _

theorem negativeCount_frame_lt (M : Matrix (FrameIndex p) (FrameIndex p) ℂ) :
    negativeCount M < 2 * p.W := by
  have h := negativeCount_le_card M
  rw [Fintype.card_fin] at h
  have := p.W_pos
  omega

end Lemmas

/-!
## The sector decomposition of the inertia indicator
-/

/-- `1{N_-(M) + n_R = α} = Σ_{ℓ < K} 1{ℓ + n_R = α} 1{N_-(M) = ℓ}` under the integral, when
`N_-(M) < K` everywhere (no measurability is needed: at most one sector is attainable). -/
theorem sector_lintegral {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (K : ℕ) (m : A → B → ℕ) (hm : ∀ a b, m a b < K)
    (nR α : ℕ) (X Y : A → B → ℝ≥0∞) :
    (∫⁻ a, ∫⁻ b, X a b * (if m a b + nR = α then 1 else 0) * Y a b ∂ν ∂μ) =
      ∑ ℓ ∈ Finset.range K, (if ℓ + nR = α then 1 else 0) *
        ∫⁻ a, ∫⁻ b, X a b * (if m a b = ℓ then 1 else 0) * Y a b ∂ν ∂μ := by
  by_cases h : nR ≤ α ∧ α - nR < K
  · rw [Finset.sum_eq_single (α - nR)]
    · rw [ite_eq_left (by omega), one_mul]
      refine lintegral_congr fun a => lintegral_congr fun b => ?_
      by_cases hab : m a b = α - nR
      · rw [ite_eq_left (by omega), ite_eq_left hab]
      · rw [ite_eq_right (by omega), ite_eq_right hab]
    · intro ℓ _ hℓ
      rw [ite_eq_right (by omega), zero_mul]
    · intro hn
      exact absurd (Finset.mem_range.2 h.2) hn
  · have h0 : ∀ a b, ¬ (m a b + nR = α) := fun a b hab =>
      h ⟨by omega, by have := hm a b; omega⟩
    rw [Finset.sum_eq_zero]
    · simp [h0]
    · intro ℓ hℓ
      rw [Finset.mem_range] at hℓ
      rw [ite_eq_right (by omega), zero_mul]

/-!
## The integrands on the support
-/

section Integrands

variable (p : Parameters) (i : ZMod p.n)

/-- Index integrand: the coarea density with speed `v*Dv` and observable `f(λ_α, p_α)` of the
reconstructed matrix equals the angular density times `(v*Dv) f(E, p(v,E))`. -/
theorem index_integrand (hC : CoareaContract) (α : Fin p.N)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian) (E : ℝ)
    (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0) (v : PairSite p i → ℂ) (hv : l2Norm v = 1)
    (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ) (hG' : G'.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞) :
    ENNReal.ofReal (a * clockSpeed p i ω E v * Complex.normSq (frameM p i U ω E v G').det) *
        (if negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
          then 1 else 0) *
        f (physicalOrderedEigenvalue p (assemble p i ω (reconstructedGaussian p i U ω E v G')) α)
          (blockMassVector p (assemble p i ω (reconstructedGaussian p i U ω E v G')) α) =
      ENNReal.ofReal (a * Complex.normSq (frameM p i U ω E v G').det) *
        (if negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
          then 1 else 0) *
        (ENNReal.ofReal (clockSpeed p i ω E v) * f E (reconBlockMass p i ω E v)) := by
  by_cases hM : (frameM p i U ω E v G').det = 0
  · simp [hM]
  by_cases hc : negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
  · obtain ⟨hlam, hbm, -⟩ :=
      reconstruction_of_coarea p i hC α U hU ω h1 h3 E v G' hG' hv hD hM hc
    rw [hlam, hbm, ite_eq_left hc, mul_one, mul_one,
      show a * clockSpeed p i ω E v * Complex.normSq (frameM p i U ω E v G').det =
        (a * Complex.normSq (frameM p i U ω E v G').det) * clockSpeed p i ω E v by ring,
      ENNReal.ofReal_mul (mul_nonneg ha (Complex.normSq_nonneg _)), mul_assoc]
  · rw [ite_eq_right hc]; simp

/-- Mass integrand: with the pair weight `q_{αS}` in the observable, the speed `v*Dv` cancels. -/
theorem mass_integrand (hC : CoareaContract) (α : Fin p.N)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian) (E : ℝ)
    (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0) (v : PairSite p i → ℂ) (hv : l2Norm v = 1)
    (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ) (hG' : G'.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞) :
    ENNReal.ofReal (a * clockSpeed p i ω E v * Complex.normSq (frameM p i U ω E v G').det) *
        (if negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
          then 1 else 0) *
        (ENNReal.ofReal
            (pairMass p i α (assemble p i ω (reconstructedGaussian p i U ω E v G'))) *
          f (physicalOrderedEigenvalue p
              (assemble p i ω (reconstructedGaussian p i U ω E v G')) α)
            (blockMassVector p (assemble p i ω (reconstructedGaussian p i U ω E v G')) α)) =
      ENNReal.ofReal (a * Complex.normSq (frameM p i U ω E v G').det) *
        (if negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
          then 1 else 0) *
        f E (reconBlockMass p i ω E v) := by
  by_cases hM : (frameM p i U ω E v G').det = 0
  · simp [hM]
  by_cases hc : negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
  · obtain ⟨hlam, hbm, hsm⟩ :=
      reconstruction_of_coarea p i hC α U hU ω h1 h3 E v G' hG' hv hD hM hc
    rw [hlam, hbm, ite_eq_left hc, mul_one, mul_one, ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ha (clockSpeed_nonneg p i ω E v))
        (Complex.normSq_nonneg _))]
    congr 2
    linear_combination (a * Complex.normSq (frameM p i U ω E v G').det) * hsm
  · rw [ite_eq_right hc]; simp

end Integrands

/-!
## The fixed-`ω` fiber in sector form
-/

section Fiber

variable (p : Parameters) (i : ZMod p.n)

/-- Fixed-`ω` coarea fiber (speed `v*Dv`, observable `Φ` of the reconstructed pair Gaussian) in
the sector form `∫ de Σ_ℓ 1{ℓ + N_-(H_R - e) = α} 𝒜_{ℓ,e}[g_e]`, whenever, for a Hermitian
exterior, the integrands agree for every pole-free `E`, unit `v` and Hermitian `G'`. -/
theorem coareaFiber_eq_sector (α : Fin p.N)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (Φ : PairMatrix p i → ℝ≥0∞) (g : ℝ → (PairSite p i → ℂ) → ℝ≥0∞)
    (hpt : ∀ E : ℝ, (ω.1 - (E : ℂ) • 1).det ≠ 0 → ∀ v : PairSite p i → ℂ, l2Norm v = 1 →
      ∀ G' : Matrix (FrameIndex p) (FrameIndex p) ℂ, G'.IsHermitian →
      ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
          regressionFactor (pairTime p (pairS p)) E v (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) *
          clockSpeed p i ω E v * Complex.normSq (frameM p i U ω E v G').det) *
        (if negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
          then 1 else 0) * Φ (reconstructedGaussian p i U ω E v G') =
      ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
          regressionFactor (pairTime p (pairS p)) E v (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) *
          Complex.normSq (frameM p i U ω E v G').det) *
        (if negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
          then 1 else 0) * g E v) :
    coareaFiber p α i (pairS p) U (clockSpeed p i) ω Φ =
      ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          pairSectorFiber p i U ω e ℓ (g e) := by
  have := nonempty_pairSite p i
  unfold coareaFiber
  refine lintegral_congr_ae ?_
  filter_upwards [ae_det_shift_ne_zero p i ω.1] with E hE
  refine Eq.trans ?_ (Eq.trans (sector_lintegral (projectiveHaar (PairSite p i))
    (gueMeasure (FrameIndex p) (pairTime p (pairS p))) (2 * p.W)
    (fun v G' => negativeCount (frameM p i U ω E v G')) (fun v G' => negativeCount_frame_lt p _)
    (negativeCount (ω.1 - (E : ℂ) • 1)) α.val
    (fun v G' => ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
        regressionFactor (pairTime p (pairS p)) E v (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) *
        Complex.normSq (frameM p i U ω E v G').det))
    (fun v _ => g E v)) ?_)
  swap
  · rfl
  refine lintegral_congr_ae ?_
  filter_upwards [ProjectiveHaar.ae_l2Norm_projectiveHaar (PairSite p i)] with v hv
  refine lintegral_congr_ae ?_
  filter_upwards [GUELaw.ae_isHermitian_gueMeasure (ι := FrameIndex p)
    (pairTime p (pairS p))] with G' hG'
  exact hpt E hE v hv G' hG'

theorem coareaConstant_mul_regression_nonneg (t : ℝ≥0) (E : ℝ) (v : PairSite p i → ℂ)
    (F : PairMatrix p i) :
    0 ≤ coareaConstant (2 * p.W) t * regressionFactor t E v F :=
  mul_nonneg (by unfold coareaConstant; positivity) (Real.exp_pos _).le

end Fiber

/-!
## `index`
-/

/-- **The exact Palm formula, clause `index`**, from `CoareaContract` (`formula` at
`s = pairS p = min(b, c)`, and `reconstructed_rank`). Measures: the exact physical law on the
left; `Pω`, Lebesgue `de`, `projectiveHaar` and `GUE_{2W-1}(t)` on the right. Exact identity in `[0,∞]`, every admissible `p`, model, pair, frame, rank and
measurable `f ≥ 0`.
-/
theorem exactPalm_index_of_coarea (hC : CoareaContract) :
    ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
    (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
    ∀ U, IsPairFrame p i U → ∀ (α : Fin p.N) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞),
      Measurable (Function.uncurry f) →
      (∫⁻ H, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ ω, ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          pairSectorFiber p i U ω e ℓ
            (fun v => ENNReal.ofReal (clockSpeed p i ω e v) * f e (reconBlockMass p i ω e v))
        ∂volume ∂Pω := by
  intro p model i Pω hP U hU α f hf
  have hA := ContractClauses.measurable_assemble p i
  have hobs : Measurable fun H : p.SiteMatrix =>
      f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) :=
    hf.comp ((measurable_physicalOrderedEigenvalue p α).prodMk
      (Measurable.of_eval fun k => measurable_physicalOrderedBlockMass p α k))
  have hΦ : Measurable (Function.uncurry fun (ω : SplitState p i) (G : PairMatrix p i) =>
      f (physicalOrderedEigenvalue p (assemble p i ω G) α)
        (blockMassVector p (assemble p i ω G) α)) := hobs.comp hA
  rw [← hP, lintegral_map hobs hA,
    hC.formula p model α i (pairS p) (pairS_pos p) (pairS_le p) Pω hP U hU _ hΦ, coareaRHS]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_split_isHermitian p i model (pairS p) Pω hP] with ω hω
  refine coareaFiber_eq_sector p i α U ω _ _ fun E hE v hv G' hG' => ?_
  exact index_integrand p i hC α U hU ω hω.1 hω.2 E hE v hv G' hG' _
    (coareaConstant_mul_regression_nonneg p i _ E v _) f

/-!
## Measurability of the angular fiber in the energy
-/

section Measurability

variable (p : Parameters) (i : ZMod p.n)

theorem measurable_mulVec' {X : Type*} [MeasurableSpace X] {m n : Type*} [Fintype n]
    {A : X → Matrix m n ℂ} {w : X → n → ℂ} (hA : Measurable A) (hw : Measurable w) :
    Measurable fun x => A x *ᵥ w x := by
  refine Measurable.of_eval fun r => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ =>
    (hA.eval_matrix (i := r) (j := j)).mul ((measurable_pi_apply j).comp hw)

theorem measurable_star_dotProduct' {X : Type*} [MeasurableSpace X] {n : Type*} [Fintype n]
    {w z : X → n → ℂ} (hw : Measurable w) (hz : Measurable z) :
    Measurable fun x => star (w x) ⬝ᵥ z x := by
  simp only [dotProduct, Pi.star_apply]
  exact Finset.measurable_sum _ fun j _ =>
    (Complex.continuous_conj.measurable.comp ((measurable_pi_apply j).comp hw)).mul
      ((measurable_pi_apply j).comp hz)

theorem measurable_shift (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) :
    Measurable fun E : ℝ => H_R - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) := by
  apply Measurable.of_eval_matrix
  intro a b
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  fun_prop

theorem measurable_resolvent (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) :
    Measurable fun E : ℝ => physicalCoareaResolvent H_R E :=
  CoareaNative.BlockBand.Measurable.matrixNonsingInv (measurable_shift p i H_R)

theorem measurable_coareaT (ω : SplitState p i) :
    Measurable fun E : ℝ => physicalCoareaT ω.1 ω.2.1 E :=
  CoareaNative.BlockBand.measurable_matrix_mul_rect (measurable_resolvent p i ω.1)
    measurable_const

theorem measurable_coareaF (ω : SplitState p i) :
    Measurable fun E : ℝ => physicalCoareaF ω.1 ω.2.1 ω.2.2 E := by
  unfold physicalCoareaF
  exact FixedOmega.measurable_matrix_sub measurable_const
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.measurable_matrix_mul_rect measurable_const
        (measurable_resolvent p i ω.1)) measurable_const)

theorem measurable_coareaD (ω : SplitState p i) :
    Measurable fun E : ℝ => physicalCoareaD ω.1 ω.2.1 E := by
  unfold physicalCoareaD schurClock
  have hT := measurable_coareaT p i ω
  exact FixedOmega.measurable_matrix_add measurable_const
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.Measurable.matrix_conjTranspose hT) hT)

theorem continuous_regressionFactor {ι : Type*} [Fintype ι] (t : ℝ) :
    Continuous (fun x : ℝ × (ι → ℂ) × Matrix ι ι ℂ => regressionFactor t x.1 x.2.1 x.2.2) := by
  unfold regressionFactor l2Norm
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

theorem measurable_regressionFactor_joint {ι : Type*} [Fintype ι] (t : ℝ) :
    Measurable (fun x : ℝ × (ι → ℂ) × Matrix ι ι ℂ => regressionFactor t x.1 x.2.1 x.2.2) :=
  (continuous_regressionFactor t).measurable

/-- `(E, v) ↦ v*D(E)v` is measurable. -/
theorem measurable_clockSpeed_joint (ω : SplitState p i) :
    Measurable fun x : ℝ × (PairSite p i → ℂ) => clockSpeed p i ω x.1 x.2 := by
  unfold clockSpeed
  exact Complex.measurable_re.comp (measurable_star_dotProduct' measurable_snd
    (measurable_mulVec' ((measurable_coareaD p i ω).comp measurable_fst) measurable_snd))

/-- `(E, v) ↦ L_E v` is measurable. -/
theorem measurable_schurLift_joint (ω : SplitState p i) :
    Measurable fun x : ℝ × (PairSite p i → ℂ) => schurLift p i ω.1 ω.2.1 x.1 x.2 := by
  have hTv : Measurable fun x : ℝ × (PairSite p i → ℂ) => physicalCoareaT ω.1 ω.2.1 x.1 *ᵥ x.2 :=
    measurable_mulVec' ((measurable_coareaT p i ω).comp measurable_fst) measurable_snd
  refine Measurable.of_eval fun y => ?_
  unfold schurLift
  by_cases hy : y.1 = i ∨ y.1 = i + 1
  · simp only [hy, dite_true]
    exact (measurable_pi_apply _).comp measurable_snd
  · simp only [hy, dite_false]
    exact ((measurable_pi_apply _).comp hTv).neg

/-- `(E, v) ↦ p(v, E)` (`reconBlockMass`) is measurable. -/
theorem measurable_reconBlockMass_joint (ω : SplitState p i) :
    Measurable fun x : ℝ × (PairSite p i → ℂ) => reconBlockMass p i ω x.1 x.2 := by
  refine Measurable.of_eval fun k => ?_
  unfold reconBlockMass
  refine Measurable.div (Finset.measurable_sum _ fun a _ => ?_) (measurable_clockSpeed_joint p i ω)
  exact (((measurable_pi_apply _).comp (measurable_schurLift_joint p i ω)).norm).pow_const 2

/-- `((E, v), G') ↦ M = U_v* F(E) U_v + G' - E` is measurable. -/
theorem measurable_frameM_joint (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (hU : Measurable U) (ω : SplitState p i) :
    Measurable fun q : (ℝ × (PairSite p i → ℂ)) × Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      frameM p i U ω q.1.1 q.1.2 q.2 := by
  have hU1 : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ => U q.1.2 :=
    hU.comp (measurable_snd.comp measurable_fst)
  have hF : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ => physicalCoareaF ω.1 ω.2.1 ω.2.2 q.1.1 :=
    (measurable_coareaF p i ω).comp (measurable_fst.comp measurable_fst)
  have hE : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      ((q.1.1 : ℝ) : ℂ) • (1 : Matrix (FrameIndex p) (FrameIndex p) ℂ) := by
    apply Measurable.of_eval_matrix
    intro a b
    simp only [Matrix.smul_apply]
    exact (Complex.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).smul
      measurable_const
  unfold frameM
  exact FixedOmega.measurable_matrix_sub (FixedOmega.measurable_matrix_add
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.measurable_matrix_mul_rect
        (CoareaNative.BlockBand.Measurable.matrix_conjTranspose hU1) hF) hU1) measurable_snd) hE

/-- `(E, v) ↦ 𝓡(E, v, F(E))` is measurable. -/
theorem measurable_regression_joint (ω : SplitState p i) (t : ℝ) :
    Measurable fun x : ℝ × (PairSite p i → ℂ) =>
      regressionFactor t x.1 x.2 (physicalCoareaF ω.1 ω.2.1 ω.2.2 x.1) := by
  have hg : Measurable fun x : ℝ × (PairSite p i → ℂ) =>
      (x.1, x.2, physicalCoareaF ω.1 ω.2.1 ω.2.2 x.1) :=
    measurable_fst.prodMk (measurable_snd.prodMk ((measurable_coareaF p i ω).comp measurable_fst))
  have h1 := measurable_regressionFactor_joint (ι := PairSite p i) t
  have h2 := h1.comp hg
  exact h2

/-- The integrand of `𝒜_{ℓ,e}` is jointly measurable in `((e, v), G')`. -/
theorem measurable_sectorIntegrand
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (hU : Measurable U) (ω : SplitState p i) (ℓ : ℕ)
    (g : ℝ → (PairSite p i → ℂ) → ℝ≥0∞) (hg : Measurable (Function.uncurry g)) :
    Measurable fun q : (ℝ × (PairSite p i → ℂ)) × Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
          regressionFactor (pairTime p (pairS p)) q.1.1 q.1.2
            (physicalCoareaF ω.1 ω.2.1 ω.2.2 q.1.1) *
          Complex.normSq (frameM p i U ω q.1.1 q.1.2 q.2).det) *
        (if negativeCount (frameM p i U ω q.1.1 q.1.2 q.2) = ℓ then 1 else 0) *
        g q.1.1 q.1.2 := by
  have hM := measurable_frameM_joint p i U hU ω
  have hR : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      regressionFactor (pairTime p (pairS p)) q.1.1 q.1.2
        (physicalCoareaF ω.1 ω.2.1 ω.2.2 q.1.1) :=
    (measurable_regression_joint p i ω (pairTime p (pairS p))).comp measurable_fst
  have hdet : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      Complex.normSq (frameM p i U ω q.1.1 q.1.2 q.2).det :=
    Complex.continuous_normSq.measurable.comp ((continuous_id.matrix_det).measurable.comp hM)
  have hind : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      (if negativeCount (frameM p i U ω q.1.1 q.1.2 q.2) = ℓ then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun ((FixedOmega.measurable_negativeCount _).comp hM)
      measurable_const) measurable_const measurable_const
  have hgq : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ => g q.1.1 q.1.2 := hg.comp measurable_fst
  exact ((ENNReal.measurable_ofReal.comp ((measurable_const.mul hR).mul hdet)).mul hind).mul hgq

/-- The angular sector fiber `e ↦ 𝒜_{ℓ,e}[g(e, ·)]` is measurable in the energy, for every
exterior `ω`, measurable frame and jointly measurable `g`. -/
theorem measurable_pairSectorFiber (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (hU : Measurable U) (ω : SplitState p i) (ℓ : ℕ)
    (g : ℝ → (PairSite p i → ℂ) → ℝ≥0∞) (hg : Measurable (Function.uncurry g)) :
    Measurable fun e : ℝ => pairSectorFiber p i U ω e ℓ (g e) := by
  have h2 := (measurable_sectorIntegrand p i U hU ω ℓ g hg).lintegral_prod_right'
    (ν := gueMeasure (FrameIndex p) (pairTime p (pairS p)))
  have h3 := h2.lintegral_prod_right' (ν := projectiveHaar (PairSite p i))
  unfold pairSectorFiber
  exact h3

end Measurability

/-!
## `mass`
-/

theorem card_exteriorSite_add (p : Parameters) (i : ZMod p.n) :
    Fintype.card (ExteriorSite p i) + 2 * p.W = p.N := by
  classical
  have h1 := Fintype.card_subtype_compl (fun x : p.Site => x.1 = i ∨ x.1 = i + 1)
  have h2 := ContractClauses.card_pairSite p i
  have h3 : Fintype.card p.Site = p.N := by
    simp [Parameters.N, Fintype.card_prod, ZMod.card]
  have h4 := Fintype.card_subtype_le (fun x : p.Site => x.1 = i ∨ x.1 = i + 1)
  have h5 : Fintype.card (ExteriorSite p i) =
      Fintype.card {x : p.Site // ¬ (x.1 = i ∨ x.1 = i + 1)} := rfl
  have h6 : Fintype.card (PairSite p i) =
      Fintype.card {x : p.Site // x.1 = i ∨ x.1 = i + 1} := rfl
  omega

/-- `Σ_α 1{ℓ + N_-(H_R - e) = α} = 1` for every attainable sector `ℓ < 2W`. -/
theorem sum_rank_indicator (p : Parameters) (i : ZMod p.n)
    (M : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) (ℓ : ℕ) (hℓ : ℓ < 2 * p.W) :
    (∑ α : Fin p.N, (if ℓ + negativeCount M = α.val then (1 : ℝ≥0∞) else 0)) = 1 := by
  have hc := negativeCount_le_card M
  have hN := card_exteriorSite_add p i
  have hlt : ℓ + negativeCount M < p.N := by omega
  rw [Finset.sum_eq_single_of_mem (⟨ℓ + negativeCount M, hlt⟩ : Fin p.N) (Finset.mem_univ _)]
  · simp
  · intro β _ hβ
    rw [ite_eq_right]
    intro h
    exact hβ (Fin.ext h.symm)

/-- **The exact Palm formula, clause `mass`**, from `CoareaContract` (`formula_fixed` at
`s = pairS p = min(b, c)`, rank by rank, and `reconstructed_rank`). On the support the pair
mass is `q_{αS} = 1/(v*Dv)` and cancels the crossing speed; the rank indicators then sum to
one over `α` for every attainable sector.
Measures: the exact physical law on the left;
`Pω`, Lebesgue `de`,
`projectiveHaar` and `GUE_{2W-1}(t)` on the right.
Exact identity in `[0,∞]`.
-/
theorem exactPalm_mass_of_coarea (hC : CoareaContract) :
    ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
    (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
    ∀ U, IsPairFrame p i U → ∀ f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞, Measurable (Function.uncurry f) →
      (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (pairMass p i α H) *
          f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ ω, ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)) ∂volume ∂Pω := by
  intro p model i Pω hP U hU f hf
  have hA := ContractClauses.measurable_assemble p i
  have hobsα : ∀ α : Fin p.N, Measurable fun H : p.SiteMatrix =>
      ENNReal.ofReal (pairMass p i α H) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) := fun α =>
    (ENNReal.measurable_ofReal.comp ((measurable_physicalOrderedBlockMass p α i).add
      (measurable_physicalOrderedBlockMass p α (i + 1)))).mul
      (hf.comp ((measurable_physicalOrderedEigenvalue p α).prodMk
        (Measurable.of_eval fun k => measurable_physicalOrderedBlockMass p α k)))
  have hobs : Measurable fun H : p.SiteMatrix => ∑ α : Fin p.N,
      ENNReal.ofReal (pairMass p i α H) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) :=
    Finset.measurable_sum _ fun α _ => hobsα α
  have hg : Measurable fun z : SplitState p i × PairMatrix p i =>
      ∑ α : Fin p.N, ENNReal.ofReal (pairMass p i α (assemble p i z.1 z.2)) *
        f (physicalOrderedEigenvalue p (assemble p i z.1 z.2) α)
          (blockMassVector p (assemble p i z.1 z.2) α) := hobs.comp hA
  rw [← hP, lintegral_map hobs hA, lintegral_prod _ hg.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_split_isHermitian p i model (pairS p) Pω hP,
    ae_all_iff.2 fun α : Fin p.N =>
      hC.formula_fixed p model α i (pairS p) (pairS_pos p) (pairS_le p) Pω hP U hU]
    with ω hω hfix
  have hAω : Measurable fun G : PairMatrix p i => assemble p i ω G :=
    hA.comp measurable_prodMk_left
  rw [lintegral_finsetSum Finset.univ (f := fun (α : Fin p.N) (G : PairMatrix p i) =>
      ENNReal.ofReal (pairMass p i α (assemble p i ω G)) *
        f (physicalOrderedEigenvalue p (assemble p i ω G) α)
          (blockMassVector p (assemble p i ω G) α)) fun α _ => (hobsα α).comp hAω]
  have hfib : ∀ α : Fin p.N,
      (∫⁻ G, ENNReal.ofReal (pairMass p i α (assemble p i ω G)) *
        f (physicalOrderedEigenvalue p (assemble p i ω G) α)
          (blockMassVector p (assemble p i ω G) α)
        ∂(gueMeasure (PairSite p i) (pairTime p (pairS p)))) =
      ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)) := by
    intro α
    refine (hfix α _ ((hobsα α).comp hAω)).trans ?_
    refine coareaFiber_eq_sector p i α U ω _ (fun e v => f e (reconBlockMass p i ω e v))
      fun E hE v hv G' hG' => ?_
    exact mass_integrand p i hC α U hU ω hω.1 hω.2 E hE v hv G' hG' _
      (coareaConstant_mul_regression_nonneg p i _ E v _) f
  rw [Finset.sum_congr rfl fun α _ => hfib α]
  have hgm : Measurable (Function.uncurry fun (e : ℝ) (v : PairSite p i → ℂ) =>
      f e (reconBlockMass p i ω e v)) :=
    hf.comp (measurable_fst.prodMk (measurable_reconBlockMass_joint p i ω))
  have hfibm : ∀ ℓ, Measurable fun e : ℝ =>
      pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)) := fun ℓ =>
    measurable_pairSectorFiber p i U hU.1 ω ℓ (fun e v => f e (reconBlockMass p i ω e v)) hgm
  have hNR : Measurable fun e : ℝ => negativeCount (ω.1 - (e : ℂ) • 1) :=
    (FixedOmega.measurable_negativeCount _).comp (measurable_shift p i ω.1)
  rw [← lintegral_finsetSum Finset.univ (f := fun (α : Fin p.N) (e : ℝ) =>
      ∑ ℓ ∈ Finset.range (2 * p.W),
        (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)))
    fun α _ => Finset.measurable_sum _ fun ℓ _ =>
      (Measurable.ite (measurableSet_eq_fun (hNR.const_add ℓ) measurable_const)
        measurable_const measurable_const).mul (hfibm ℓ)]
  refine lintegral_congr fun e => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [← Finset.sum_mul, sum_rank_indicator p i _ ℓ (Finset.mem_range.1 hℓ), one_mul]

end BlockBand.Endpoints.Normalization

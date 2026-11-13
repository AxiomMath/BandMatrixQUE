module

public import BlockBand.Endpoints.Sine.FlowAdmissionPalmGaussian
public import BlockBand.Endpoints.Sine.MicroscopicTagAssemblyNormalizer

/-!
# The fixed-exterior mass Palm identity from the fixed-exterior coarea identity

`fap_mass_fiber`: for a Hermitian exterior `ω` at which the fixed-`ω` coarea identity of
`CoareaContract.formula_fixed` holds for every rank, the integral over the fresh pair block of
`Σ_α q_{αS} f(λ_α, p_α)` equals the integral over energies of the angular sector fibers. The
proof uses unit vectors under the Haar measure, the algebra of the reconstructed support, the
sector decomposition of the inertia indicator and measurability of the angular fiber in the
energy.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexConjugate

/-!
## Unit vectors under `ν_𝒩`
-/

section Haar

variable (ι : Type*) [Fintype ι]

theorem fap_continuous_l2Norm : Continuous (l2Norm (ι := ι)) := by
  unfold l2Norm
  fun_prop

theorem fap_l2Norm_smul (c : ℂ) (g : ι → ℂ) : l2Norm (c • g) = ‖c‖ * l2Norm g := by
  unfold l2Norm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem fap_l2Norm_eq_zero {g : ι → ℂ} (h : l2Norm g = 0) : g = 0 := by
  unfold l2Norm at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun k _ => sq_nonneg _),
    Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)] at h
  funext k
  simpa using h k (Finset.mem_univ k)

theorem fap_ae_circular_ne_zero [Nonempty ι] : ∀ᵐ g ∂circularVectorLaw ι, g ≠ 0 := by
  obtain ⟨a⟩ := ‹Nonempty ι›
  have hT : Measurable fun r : ι × Fin 2 → ℝ => fun b : ι =>
      (r (b, 0) : ℂ) + (r (b, 1) : ℂ) * Complex.I :=
    Measurable.of_eval fun b => (Complex.measurable_ofReal.comp (measurable_pi_apply _)).add
      ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).mul measurable_const)
  unfold circularVectorLaw
  refine (ae_map_iff hT.aemeasurable (measurableSet_singleton (0 : ι → ℂ)).compl).mpr ?_
  have h0 : (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0))
      (Function.eval (a, 0) ⁻¹' {0}) = 0 := by
    refine Measure.pi_eval_preimage_null _ ?_
    have := nullSingletonClass_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (by norm_num)
    exact measure_singleton 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with r hr
  intro hz
  apply hr
  have := congrArg Complex.re (congrFun hz a)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero, Pi.zero_apply,
    Complex.zero_re] at this
  simpa using this

theorem fap_ae_l2Norm_projectiveHaar [Nonempty ι] : ∀ᵐ v ∂projectiveHaar ι, l2Norm v = 1 := by
  have hN : Measurable fun g : ι → ℂ => ((l2Norm g : ℂ))⁻¹ • g :=
    (Complex.measurable_ofReal.comp (fap_continuous_l2Norm ι).measurable).inv.smul measurable_id
  unfold projectiveHaar
  refine (ae_map_iff hN.aemeasurable (measurableSet_eq_fun (fap_continuous_l2Norm ι).measurable
    measurable_const)).mpr ?_
  filter_upwards [fap_ae_circular_ne_zero ι] with g hg
  have hpos : l2Norm g ≠ 0 := fun h => hg (fap_l2Norm_eq_zero ι h)
  have hnn : 0 ≤ l2Norm g := Real.sqrt_nonneg _
  rw [fap_l2Norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn,
    inv_mul_cancel₀ hpos]

theorem fap_isProbabilityMeasure_circularVectorLaw :
    IsProbabilityMeasure (circularVectorLaw ι) := by
  unfold circularVectorLaw
  infer_instance

theorem fap_isProbabilityMeasure_projectiveHaar : IsProbabilityMeasure (projectiveHaar ι) := by
  have := fap_isProbabilityMeasure_circularVectorLaw ι
  unfold projectiveHaar
  infer_instance

end Haar

/-!
## Algebra on the reconstructed support
-/

section Lemmas

variable (p : Parameters) (i : ZMod p.n)

/-- `det(H_R - E) ≠ 0` for Lebesgue-a.e. real `E`. -/
theorem fap_ae_det_shift_ne_zero (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) :
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

theorem fap_shift_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (E : ℝ) : (A - (E : ℂ) • 1).IsHermitian :=
  hA.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))

/-- `F(E)` is Hermitian for a Hermitian exterior. -/
theorem fap_physicalCoareaF_isHermitian (ω : SplitState p i) (h1 : ω.1.IsHermitian)
    (h3 : ω.2.2.IsHermitian) (E : ℝ) :
    (physicalCoareaF ω.1 ω.2.1 ω.2.2 E).IsHermitian := by
  unfold physicalCoareaF physicalCoareaResolvent
  exact h3.sub (Matrix.isHermitian_conjTranspose_mul_mul _ (fap_shift_isHermitian h1 E).inv)

/-- The reconstructed Gaussian is Hermitian. -/
theorem fap_reconstructedGaussian_isHermitian
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian) (E : ℝ)
    (v : PairSite p i → ℂ) (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ)
    (hG' : G'.IsHermitian) :
    (reconstructedGaussian p i U ω E v G').IsHermitian := by
  have hF := fap_physicalCoareaF_isHermitian p i ω h1 h3 E
  have hvv : (vecMulVec v (star v)).IsHermitian := by
    ext a b
    simp [vecMulVec, Matrix.conjTranspose_apply, mul_comm]
  have hE : ((E : ℂ) • vecMulVec v (star v)).IsHermitian := by
    rw [IsHermitian, Matrix.conjTranspose_smul, hvv.eq, Complex.star_def, Complex.conj_ofReal]
  unfold reconstructedGaussian
  exact (hE.add (Matrix.isHermitian_mul_mul_conjTranspose _
    ((Matrix.isHermitian_conjTranspose_mul_mul _ hF).add hG'))).sub hF

theorem fap_re_star_dotProduct_self {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    (star w ⬝ᵥ w).re = ∑ k, ‖w k‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem fap_sum_site_real (f : p.Site → ℝ) :
    ∑ x, f x = ∑ s : PairSite p i, f s.1 + ∑ r : ExteriorSite p i, f r.1 := by
  rw [← Equiv.sum_comp (Equiv.sumCompl (fun x : p.Site => x.1 = i ∨ x.1 = i + 1)),
    Fintype.sum_sum_type]
  rfl

theorem fap_schurLift_pair (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (v : PairSite p i → ℂ) :
    (fun s : PairSite p i => schurLift p i H_R C E v s.1) = v := by
  funext s; simp [schurLift, s.2]

theorem fap_schurLift_ext (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (v : PairSite p i → ℂ) :
    (fun r : ExteriorSite p i => schurLift p i H_R C E v r.1) =
      -(physicalCoareaT H_R C E *ᵥ v) := by
  funext r; simp [schurLift, r.2]

/-- `v*𝒟(E)v = ‖L_E v‖²` (`𝒟 = 1 + TᴴT`, `L_E v = (v, -Tv)`). -/
theorem fap_clockSpeed_eq_l2Norm_sq (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) :
    clockSpeed p i ω E v = l2Norm (schurLift p i ω.1 ω.2.1 E v) ^ 2 := by
  set L := schurLift p i ω.1 ω.2.1 E v
  set T := physicalCoareaT ω.1 ω.2.1 E
  have hL2 : l2Norm L ^ 2 = ∑ x, ‖L x‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _)
  have hpair := fap_schurLift_pair p i ω.1 ω.2.1 E v
  have hext := fap_schurLift_ext p i ω.1 ω.2.1 E v
  have hS : ∑ s : PairSite p i, ‖L s.1‖ ^ 2 = ∑ s, ‖v s‖ ^ 2 :=
    Finset.sum_congr rfl fun s _ => by rw [← congrFun hpair s]
  have hR : ∑ r : ExteriorSite p i, ‖L r.1‖ ^ 2 = ∑ r, ‖(T *ᵥ v) r‖ ^ 2 :=
    Finset.sum_congr rfl fun r _ => by
      rw [show L r.1 = -(T *ᵥ v) r from congrFun hext r, norm_neg]
  rw [hL2, fap_sum_site_real p i, hS, hR, clockSpeed, physicalCoareaD, schurClock,
    Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    fap_re_star_dotProduct_self, fap_re_star_dotProduct_self]

theorem fap_sum_normSq_eq_one {ι : Type*} [Fintype ι] (v : ι → ℂ) (hv : l2Norm v = 1) :
    ∑ k, ‖v k‖ ^ 2 = 1 := by
  have h0 : 0 ≤ ∑ k, ‖v k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have := Real.sq_sqrt h0
  rw [← l2Norm, hv] at this
  linarith

/-- `v*𝒟v ≥ ‖v‖² = 1` for unit `v`. -/
theorem fap_one_le_clockSpeed (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ)
    (hv : l2Norm v = 1) : 1 ≤ clockSpeed p i ω E v := by
  rw [clockSpeed, physicalCoareaD, schurClock,
    Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    fap_re_star_dotProduct_self, fap_re_star_dotProduct_self, fap_sum_normSq_eq_one v hv]
  have : 0 ≤ ∑ k, ‖(physicalCoareaT ω.1 ω.2.1 E *ᵥ v) k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  linarith

theorem fap_clockSpeed_nonneg (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) :
    0 ≤ clockSpeed p i ω E v := by
  rw [fap_clockSpeed_eq_l2Norm_sq]; exact sq_nonneg _

theorem fap_assemble_isHermitian (ω : SplitState p i) (G : PairMatrix p i)
    (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian) (hG : G.IsHermitian) :
    (assemble p i ω G).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  unfold assemble
  by_cases hx : x.1 = i ∨ x.1 = i + 1 <;> by_cases hy : y.1 = i ∨ y.1 = i + 1
  · simp only [hx, hy, dite_true, star_add]
    rw [h3.apply, hG.apply]
  · simp [hx, hy]
  · simp [hx, hy]
  · simp only [hx, hy, dite_false]
    exact h1.apply _ _

theorem fap_pair_ne_succ : i ≠ i + 1 := by
  intro h
  have h1 : ((1 : ℕ) : ZMod p.n) = 0 := by
    have : (1 : ZMod p.n) = 0 := by
      have := congrArg (fun x => x - i) h
      simpa using this.symm
    exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd one_pos h1
  have := p.n_ge_four
  omega

theorem fap_pairMass_eq (α : Fin p.N) (H : p.SiteMatrix) :
    pairMass p i α H = ∑ s : PairSite p i, ‖physicalOrderedEigenvector p H α s.1‖ ^ 2 := by
  have hs : ∀ x : p.Site, x ∈ ({i, i + 1} : Finset (ZMod p.n)) ×ˢ
      (Finset.univ : Finset (Fin p.W)) ↔ (x.1 = i ∨ x.1 = i + 1) := by
    intro x; simp
  rw [← Finset.sum_subtype _ hs (fun x => ‖physicalOrderedEigenvector p H α x‖ ^ 2),
    Finset.sum_product, Finset.sum_pair (fap_pair_ne_succ p i)]
  rfl

/-- **Reconstruction on the support** (`CoareaContract.reconstructed_rank`):
`λ_α(H) = E`, `p_α(H) = p(v,E)` and `q_{αS}(H) v*Dv = 1` for `H = assemble ω G_rec`.
-/
theorem fap_reconstruction (hC : CoareaContract) (α : Fin p.N)
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
  have hH := fap_assemble_isHermitian p i ω _ h1 h3
    (fap_reconstructedGaussian_isHermitian p i U ω h1 h3 E v G' hG')
  obtain ⟨hlam, hproj⟩ := hC.reconstructed_rank p α i U hU ω E v G' hH hv hD hM hcnt
  set L := schurLift p i ω.1 ω.2.1 E v
  set H := assemble p i ω (reconstructedGaussian p i U ω E v G')
  have hpair := fap_schurLift_pair p i ω.1 ω.2.1 E v
  have hpt : ∀ x, ‖physicalOrderedEigenvector p H α x‖ ^ 2 =
      (l2Norm L ^ 2)⁻¹ * ‖L x‖ ^ 2 := by
    intro x
    have h := congrArg Complex.re (hproj x x)
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, Complex.ofReal_re] at h
    rw [h]
    norm_cast
  have hspeed : clockSpeed p i ω E v = l2Norm L ^ 2 := fap_clockSpeed_eq_l2Norm_sq p i ω E v
  have hpos : l2Norm L ^ 2 ≠ 0 := by
    rw [← hspeed]; exact (lt_of_lt_of_le one_pos (fap_one_le_clockSpeed p i ω E v hv)).ne'
  refine ⟨hlam, ?_, ?_⟩
  · funext k
    simp only [blockMassVector, physicalOrderedBlockMass, reconBlockMass, hpt, hspeed]
    rw [← Finset.mul_sum, inv_mul_eq_div]
  · have hm : pairMass p i α H = (l2Norm L ^ 2)⁻¹ := by
      rw [fap_pairMass_eq]
      simp_rw [hpt]
      rw [← Finset.mul_sum]
      have : ∑ s : PairSite p i, ‖L s.1‖ ^ 2 = 1 := by
        rw [← fap_sum_normSq_eq_one v hv]
        exact Finset.sum_congr rfl fun s _ => by rw [← congrFun hpair s]
      rw [this, mul_one]
    rw [hm, hspeed, mul_inv_cancel₀ hpos]

theorem fap_nonempty_pairSite : Nonempty (PairSite p i) :=
  ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩

theorem fap_negativeCount_frame_lt (M : Matrix (FrameIndex p) (FrameIndex p) ℂ) :
    negativeCount M < 2 * p.W := by
  have h := mts_negativeCount_le M
  rw [Fintype.card_fin] at h
  have := p.W_pos
  omega

end Lemmas

/-!
## The sector decomposition of the inertia indicator
-/

/-- `1{N_-(M) + n_R = α} = Σ_{ℓ < K} 1{ℓ + n_R = α} 1{N_-(M) = ℓ}` under the integral, when
`N_-(M) < K` everywhere (no measurability is needed: at most one sector is attainable). -/
theorem fap_sector_lintegral {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
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
## The integrand and the fiber on the support
-/

section Fiber

variable (p : Parameters) (i : ZMod p.n)

/-- Mass integrand: with the pair weight `q_{αS}` in the observable, the speed `v*Dv` cancels. -/
theorem fap_mass_integrand (hC : CoareaContract) (α : Fin p.N)
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
  by_cases hc :
      negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
  · obtain ⟨hlam, hbm, hsm⟩ :=
      fap_reconstruction p i hC α U hU ω h1 h3 E v G' hG' hv hD hM hc
    rw [hlam, hbm, ite_eq_left hc, mul_one, mul_one, ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ha (fap_clockSpeed_nonneg p i ω E v))
        (Complex.normSq_nonneg _))]
    congr 2
    linear_combination (a * Complex.normSq (frameM p i U ω E v G').det) * hsm
  · rw [ite_eq_right hc]; simp

/-- Fixed-`ω` coarea fiber in sector form, whenever the integrands agree on the support. -/
theorem fap_coareaFiber_eq_sector (α : Fin p.N)
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
  have := fap_nonempty_pairSite p i
  unfold coareaFiber
  refine lintegral_congr_ae ?_
  filter_upwards [fap_ae_det_shift_ne_zero p i ω.1] with E hE
  refine Eq.trans ?_ (Eq.trans (fap_sector_lintegral (projectiveHaar (PairSite p i))
    (gueMeasure (FrameIndex p) (pairTime p (pairS p))) (2 * p.W)
    (fun v G' => negativeCount (frameM p i U ω E v G'))
    (fun v G' => fap_negativeCount_frame_lt p _)
    (negativeCount (ω.1 - (E : ℂ) • 1)) α.val
    (fun v G' => ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
        regressionFactor (pairTime p (pairS p)) E v (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) *
        Complex.normSq (frameM p i U ω E v G').det))
    (fun v _ => g E v)) ?_)
  swap
  · rfl
  refine lintegral_congr_ae ?_
  filter_upwards [fap_ae_l2Norm_projectiveHaar (PairSite p i)] with v hv
  refine lintegral_congr_ae ?_
  filter_upwards [PhaseFractional.ae_gue_isHermitian (FrameIndex p)
    (pairTime p (pairS p))] with G' hG'
  exact hpt E hE v hv G' hG'

theorem fap_coareaConstant_mul_regression_nonneg (t : ℝ≥0) (E : ℝ) (v : PairSite p i → ℂ)
    (F : PairMatrix p i) :
    0 ≤ coareaConstant (2 * p.W) t * regressionFactor t E v F :=
  mul_nonneg (by unfold coareaConstant; positivity) (Real.exp_pos _).le

end Fiber

/-!
## Measurability of the angular fiber in the energy
-/

section Measurability

variable (p : Parameters) (i : ZMod p.n)

theorem fap_measurable_negativeCount {ι : Type} [Fintype ι] [DecidableEq ι] :
    Measurable (negativeCount : Matrix ι ι ℂ → ℕ) :=
  measurable_to_countable' fun ℓ => mts_measurableSet_negativeCount ℓ

theorem fap_measurable_matrix_add {X : Type*} [MeasurableSpace X] {m n : Type*}
    {A B : X → Matrix m n ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => A x + B x :=
  Measurable.of_eval fun a => Measurable.of_eval fun b =>
    (measurable_entry_matrixC hA a b).add (measurable_entry_matrixC hB a b)

theorem fap_measurable_matrix_sub {X : Type*} [MeasurableSpace X] {m n : Type*}
    {A B : X → Matrix m n ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => A x - B x :=
  Measurable.of_eval fun a => Measurable.of_eval fun b =>
    (measurable_entry_matrixC hA a b).sub (measurable_entry_matrixC hB a b)

theorem fap_measurable_conjTranspose {X : Type*} [MeasurableSpace X] {m n : Type*}
    {A : X → Matrix m n ℂ} (hA : Measurable A) : Measurable fun x => (A x)ᴴ :=
  Measurable.of_eval fun a => Measurable.of_eval fun b => by
    simp only [Matrix.conjTranspose_apply]
    exact Complex.continuous_conj.measurable.comp (measurable_entry_matrixC hA b a)

theorem fap_measurable_mulVec {X : Type*} [MeasurableSpace X] {m n : Type*} [Fintype n]
    {A : X → Matrix m n ℂ} {w : X → n → ℂ} (hA : Measurable A) (hw : Measurable w) :
    Measurable fun x => A x *ᵥ w x := by
  refine Measurable.of_eval fun r => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_entry_matrixC hA r j).mul ((measurable_pi_apply j).comp hw)

theorem fap_measurable_star_dotProduct {X : Type*} [MeasurableSpace X] {n : Type*} [Fintype n]
    {w z : X → n → ℂ} (hw : Measurable w) (hz : Measurable z) :
    Measurable fun x => star (w x) ⬝ᵥ z x := by
  simp only [dotProduct, Pi.star_apply]
  exact Finset.measurable_sum _ fun j _ =>
    (Complex.continuous_conj.measurable.comp ((measurable_pi_apply j).comp hw)).mul
      ((measurable_pi_apply j).comp hz)

theorem fap_measurable_shiftE (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) :
    Measurable fun E : ℝ =>
      H_R - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) := by
  refine Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  fun_prop

theorem fap_measurable_resolvent (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) :
    Measurable fun E : ℝ => physicalCoareaResolvent H_R E :=
  measurable_inv_matrixC.comp (fap_measurable_shiftE p i H_R)

theorem fap_measurable_coareaT (ω : SplitState p i) :
    Measurable fun E : ℝ => physicalCoareaT ω.1 ω.2.1 E :=
  measurable_mul_matrixC (fap_measurable_resolvent p i ω.1) measurable_const

theorem fap_measurable_coareaF (ω : SplitState p i) :
    Measurable fun E : ℝ => physicalCoareaF ω.1 ω.2.1 ω.2.2 E := by
  unfold physicalCoareaF
  exact fap_measurable_matrix_sub measurable_const (measurable_mul_matrixC
    (measurable_mul_matrixC measurable_const (fap_measurable_resolvent p i ω.1)) measurable_const)

theorem fap_measurable_coareaD (ω : SplitState p i) :
    Measurable fun E : ℝ => physicalCoareaD ω.1 ω.2.1 E := by
  unfold physicalCoareaD schurClock
  have hT := fap_measurable_coareaT p i ω
  exact fap_measurable_matrix_add measurable_const
    (measurable_mul_matrixC (fap_measurable_conjTranspose hT) hT)

theorem fap_continuous_regressionFactor {ι : Type*} [Fintype ι] (t : ℝ) :
    Continuous (fun x : ℝ × (ι → ℂ) × Matrix ι ι ℂ => regressionFactor t x.1 x.2.1 x.2.2) := by
  unfold regressionFactor l2Norm
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

theorem fap_measurable_clockSpeed_joint (ω : SplitState p i) :
    Measurable fun x : ℝ × (PairSite p i → ℂ) => clockSpeed p i ω x.1 x.2 := by
  unfold clockSpeed
  exact Complex.measurable_re.comp (fap_measurable_star_dotProduct measurable_snd
    (fap_measurable_mulVec ((fap_measurable_coareaD p i ω).comp measurable_fst) measurable_snd))

theorem fap_measurable_schurLift_joint (ω : SplitState p i) :
    Measurable fun x : ℝ × (PairSite p i → ℂ) => schurLift p i ω.1 ω.2.1 x.1 x.2 := by
  have hTv : Measurable fun x : ℝ × (PairSite p i → ℂ) =>
      physicalCoareaT ω.1 ω.2.1 x.1 *ᵥ x.2 :=
    fap_measurable_mulVec ((fap_measurable_coareaT p i ω).comp measurable_fst) measurable_snd
  refine Measurable.of_eval fun y => ?_
  unfold schurLift
  by_cases hy : y.1 = i ∨ y.1 = i + 1
  · simp only [hy, dite_true]
    exact (measurable_pi_apply _).comp measurable_snd
  · simp only [hy, dite_false]
    exact ((measurable_pi_apply _).comp hTv).neg

theorem fap_measurable_reconBlockMass_joint (ω : SplitState p i) :
    Measurable fun x : ℝ × (PairSite p i → ℂ) => reconBlockMass p i ω x.1 x.2 := by
  refine Measurable.of_eval fun k => ?_
  unfold reconBlockMass
  refine Measurable.div (Finset.measurable_sum _ fun a _ => ?_)
    (fap_measurable_clockSpeed_joint p i ω)
  exact (((measurable_pi_apply _).comp (fap_measurable_schurLift_joint p i ω)).norm).pow_const 2

theorem fap_measurable_frameM_joint
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (hU : Measurable U) (ω : SplitState p i) :
    Measurable fun q : (ℝ × (PairSite p i → ℂ)) × Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      frameM p i U ω q.1.1 q.1.2 q.2 := by
  have hU1 : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ => U q.1.2 :=
    hU.comp (measurable_snd.comp measurable_fst)
  have hF : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ => physicalCoareaF ω.1 ω.2.1 ω.2.2 q.1.1 :=
    (fap_measurable_coareaF p i ω).comp (measurable_fst.comp measurable_fst)
  have hE : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      ((q.1.1 : ℝ) : ℂ) • (1 : Matrix (FrameIndex p) (FrameIndex p) ℂ) := by
    refine Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
    simp only [Matrix.smul_apply]
    exact (Complex.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).smul
      measurable_const
  unfold frameM
  exact fap_measurable_matrix_sub (fap_measurable_matrix_add (measurable_mul_matrixC
    (measurable_mul_matrixC (fap_measurable_conjTranspose hU1) hF) hU1) measurable_snd) hE

theorem fap_measurable_regression_joint (ω : SplitState p i) (t : ℝ) :
    Measurable fun x : ℝ × (PairSite p i → ℂ) =>
      regressionFactor t x.1 x.2 (physicalCoareaF ω.1 ω.2.1 ω.2.2 x.1) := by
  have hg : Measurable fun x : ℝ × (PairSite p i → ℂ) =>
      (x.1, x.2, physicalCoareaF ω.1 ω.2.1 ω.2.2 x.1) :=
    measurable_fst.prodMk (measurable_snd.prodMk
      ((fap_measurable_coareaF p i ω).comp measurable_fst))
  have h1 := (fap_continuous_regressionFactor (ι := PairSite p i) t).measurable
  have h2 := h1.comp hg
  exact h2

theorem fap_measurable_sectorIntegrand
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
  have hM := fap_measurable_frameM_joint p i U hU ω
  have hR : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      regressionFactor (pairTime p (pairS p)) q.1.1 q.1.2
        (physicalCoareaF ω.1 ω.2.1 ω.2.2 q.1.1) :=
    (fap_measurable_regression_joint p i ω (pairTime p (pairS p))).comp measurable_fst
  have hdet : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      Complex.normSq (frameM p i U ω q.1.1 q.1.2 q.2).det :=
    Complex.continuous_normSq.measurable.comp ((continuous_id.matrix_det).measurable.comp hM)
  have hind : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      (if negativeCount (frameM p i U ω q.1.1 q.1.2 q.2) = ℓ then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun (fap_measurable_negativeCount.comp hM)
      measurable_const) measurable_const measurable_const
  have hgq : Measurable fun q : (ℝ × (PairSite p i → ℂ)) ×
      Matrix (FrameIndex p) (FrameIndex p) ℂ => g q.1.1 q.1.2 := hg.comp measurable_fst
  exact ((ENNReal.measurable_ofReal.comp ((measurable_const.mul hR).mul hdet)).mul hind).mul hgq

/-- `e ↦ 𝒜_{ℓ,e}[g(e, ·)]` is measurable, for every exterior and jointly measurable `g`. -/
theorem fap_measurable_pairSectorFiber
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (hU : Measurable U) (ω : SplitState p i) (ℓ : ℕ)
    (g : ℝ → (PairSite p i → ℂ) → ℝ≥0∞) (hg : Measurable (Function.uncurry g)) :
    Measurable fun e : ℝ => pairSectorFiber p i U ω e ℓ (g e) := by
  have := isProbabilityMeasure_gueMeasure (FrameIndex p) (pairTime p (pairS p))
  have := fap_isProbabilityMeasure_projectiveHaar (PairSite p i)
  have h2 := (fap_measurable_sectorIntegrand p i U hU ω ℓ g hg).lintegral_prod_right'
    (ν := gueMeasure (FrameIndex p) (pairTime p (pairS p)))
  have h3 := h2.lintegral_prod_right' (ν := projectiveHaar (PairSite p i))
  unfold pairSectorFiber
  exact h3

end Measurability

/-!
## The fixed-exterior mass identity
-/

theorem fap_card_exteriorSite_add (p : Parameters) (i : ZMod p.n) :
    Fintype.card (ExteriorSite p i) + 2 * p.W = p.N := by
  classical
  have h1 := Fintype.card_subtype_compl (fun x : p.Site => x.1 = i ∨ x.1 = i + 1)
  have h2 := card_pairSite p i
  have h3 : Fintype.card p.Site = p.N := by
    simp [Parameters.N, Fintype.card_prod, ZMod.card]
  have h4 := Fintype.card_subtype_le (fun x : p.Site => x.1 = i ∨ x.1 = i + 1)
  have h5 : Fintype.card (ExteriorSite p i) =
      Fintype.card {x : p.Site // ¬ (x.1 = i ∨ x.1 = i + 1)} := rfl
  have h6 : Fintype.card (PairSite p i) =
      Fintype.card {x : p.Site // x.1 = i ∨ x.1 = i + 1} := rfl
  omega

/-- `Σ_α 1{ℓ + N_-(H_R - e) = α} = 1` for every attainable sector `ℓ < 2W`. -/
theorem fap_sum_rank_indicator (p : Parameters) (i : ZMod p.n)
    (M : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) (ℓ : ℕ) (hℓ : ℓ < 2 * p.W) :
    (∑ α : Fin p.N, (if ℓ + negativeCount M = α.val then (1 : ℝ≥0∞) else 0)) = 1 := by
  have hc := mts_negativeCount_le M
  have hN := fap_card_exteriorSite_add p i
  have hlt : ℓ + negativeCount M < p.N := by omega
  rw [Finset.sum_eq_single_of_mem (⟨ℓ + negativeCount M, hlt⟩ : Fin p.N) (Finset.mem_univ _)]
  · simp
  · intro β _ hβ
    rw [ite_eq_right]
    intro h
    exact hβ (Fin.ext h.symm)

/-- The fixed-`ω` coarea identity of `CoareaContract.formula_fixed`, at one exterior `ω`, for one
rank `α` (`s = pairS p`). -/
def FapFixedAt (p : Parameters) (i : ZMod p.n)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (α : Fin p.N)
    (ω : SplitState p i) : Prop :=
  ∀ g : PairMatrix p i → ℝ≥0∞, Measurable g →
    (∫⁻ G, g G ∂(gueMeasure (PairSite p i) (pairTime p (pairS p)))) =
      coareaFiber p α i (pairS p) U (clockSpeed p i) ω g

/-- The fixed-exterior mass Palm identity (the mass Palm identity before the `ω`-integration): for
a Hermitian exterior at which the fixed-`ω` coarea identity holds for every rank,
`∫ Σ_α q_{αS} f(λ_α, p_α)(assemble ω G) dGUE(G) = ∫ Σ_{ℓ<2W} 𝒜_{ℓ,e}[f(e, p(v,e))] de`. -/
theorem fap_mass_fiber (hC : CoareaContract) (p : Parameters) (i : ZMod p.n)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian)
    (hfix : ∀ α, FapFixedAt p i U α ω)
    (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    (∫⁻ G, ∑ α : Fin p.N, ENNReal.ofReal (pairMass p i α (assemble p i ω G)) *
        f (physicalOrderedEigenvalue p (assemble p i ω G) α)
          (blockMassVector p (assemble p i ω G) α)
      ∂(gueMeasure (PairSite p i) (pairTime p (pairS p)))) =
      ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
        pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)) := by
  have hA := measurable_assemble p i
  have hobsα : ∀ α : Fin p.N, Measurable fun H : p.SiteMatrix =>
      ENNReal.ofReal (pairMass p i α H) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) := fun α =>
    (ENNReal.measurable_ofReal.comp ((measurable_physicalOrderedBlockMass p α i).add
      (measurable_physicalOrderedBlockMass p α (i + 1)))).mul
      (hf.comp ((measurable_physicalOrderedEigenvalue p α).prodMk
        (Measurable.of_eval fun k => measurable_physicalOrderedBlockMass p α k)))
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
    refine fap_coareaFiber_eq_sector p i α U ω _ (fun e v => f e (reconBlockMass p i ω e v))
      fun E hE v hv G' hG' => ?_
    exact fap_mass_integrand p i hC α U hU ω h1 h3 E hE v hv G' hG' _
      (fap_coareaConstant_mul_regression_nonneg p i _ E v _) f
  rw [Finset.sum_congr rfl fun α _ => hfib α]
  have hgm : Measurable (Function.uncurry fun (e : ℝ) (v : PairSite p i → ℂ) =>
      f e (reconBlockMass p i ω e v)) :=
    hf.comp (measurable_fst.prodMk (fap_measurable_reconBlockMass_joint p i ω))
  have hfibm : ∀ ℓ, Measurable fun e : ℝ =>
      pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)) := fun ℓ =>
    fap_measurable_pairSectorFiber p i U hU.1 ω ℓ (fun e v => f e (reconBlockMass p i ω e v)) hgm
  have hNR : Measurable fun e : ℝ => negativeCount (ω.1 - (e : ℂ) • 1) :=
    fap_measurable_negativeCount.comp (fap_measurable_shiftE p i ω.1)
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
  rw [← Finset.sum_mul, fap_sum_rank_indicator p i _ ℓ (Finset.mem_range.1 hℓ), one_mul]

end BlockBand.Endpoints

module

public import BlockBand.Angular.PairCoareaBridge
public import BlockBand.Angular.Stein

/-!
# The pair-coarea fiber in angular form

* `regressionFactor_eq_exp`, `regressionFactor_eq_exp_expo` — the regression factor
  `𝓡(E,v,F)` of the coarea regression formula is `exp(-‖K₀v‖²/t + (v*K₀v)²/(2t))`, `K₀ = F - E`, at
  unit `v`; this is `exp (AngularData.expo v)` when the data's `K` is `K₀`, `s > 0` and the
  index set is the pair (`card = 2W`, `pairTime p s = s/2W = AngularData.t`);
* `frameM_eq_compress` — `frameM = U_v*K₀U_v + G'` (the matrix in `𝔷`);
* `coareaFiber_eq_angular` — at fixed `ω` (Hermitian blocks), the pair-law fiber of an
  observable `Ψ(λ_α, ψ_αψ_α*)` equals `∫ dE ∫ ν_N(dv) c_{d,t}(n/2)𝓡 · Ψ(E, L_E v(L_E v)*/‖L_E v‖²)
  · 𝔷_E(v)` with `𝔷 = detFactor` (`reconstructed_rank`; the exceptional sets are a
  Lebesgue-null set of `E` (`Spec H_R`), the `ν_N`-null set of non-unit `v`, the GUE-null set
  of non-Hermitian `G'`, and the zero locus of `det`, where the integrand vanishes);
* contrast and test functions on the line `L_E v`: `projContrast_lineProjector_schurLift`
  (`physicalPairContrast = quadQuot J v`, `J = pairContrast`),
  `projPairMass_lineProjector_schurLift`
  (`p_i + p_{i+1} = ‖v‖²/‖L_E v‖²`), `phase_eq_of_eigenProjector_eq` (a phase-invariant test
  of `ψ_α` is the test of `L_E v/‖L_E v‖`), and scale invariance in `v`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.FiberAngular

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Stein BlockBand.Angular.DegreeZero
open BlockBand.Angular.PairCoareaBridge BlockBand.Coarea BlockBand.Angular.Stein.AngularData
open scoped ENNReal NNReal ComplexConjugate

/-!
## The regression factor in angular form
-/

section Regression

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem normSqSum_sub_smul (w v : ι → ℂ) (c : ℂ) :
    normSqSum (w - c • v) =
      normSqSum w - 2 * (conj c * (star v ⬝ᵥ w)).re + ‖c‖ ^ 2 * normSqSum v := by
  unfold normSqSum
  simp only [dotProduct, Finset.mul_sum, Complex.re_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, Complex.sq_norm,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.star_def]
  ring

theorem l2Norm_sq_eq (x : ι → ℂ) : l2Norm x ^ 2 = normSqSum x :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)

theorem normSqSum_of_l2Norm {v : ι → ℂ} (hv : l2Norm v = 1) : normSqSum v = 1 := by
  rw [← l2Norm_sq_eq, hv, one_pow]

theorem quadNum_eq_dot' (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadNum M x = (star x ⬝ᵥ (M *ᵥ x)).re := rfl

/-- **The coarea regression factor in angular form.** For a unit `v` with `v*Fv` real (e.g. `F`
Hermitian) and every `t, E`, with `K₀ = F - E`:
`𝓡(E,v,F) = exp(-‖K₀v‖²/t + (Re v*K₀v)²/(2t))`. -/
theorem regressionFactor_eq_exp (t E : ℝ) (v : ι → ℂ) (F : Matrix ι ι ℂ) (hv : l2Norm v = 1)
    (ha : (star v ⬝ᵥ (F *ᵥ v)).im = 0) :
    regressionFactor t E v F =
      Real.exp (-normSqSum ((F - (E : ℂ) • 1) *ᵥ v) / t +
        quadNum (F - (E : ℂ) • 1) v ^ 2 / (2 * t)) := by
  have hv1 := normSqSum_of_l2Norm hv
  set a := star v ⬝ᵥ (F *ᵥ v) with ha_def
  have hK : (F - (E : ℂ) • 1) *ᵥ v = F *ᵥ v - (E : ℂ) • v := by
    rw [sub_mulVec, smul_mulVec, one_mulVec]
  have hq : quadNum (F - (E : ℂ) • 1) v = a.re - E := by
    rw [quadNum_sub, quadNum_eq_dot' F, ← ha_def, quadNum_real_smul, quadNum_one, hv1, mul_one]
  have h1 : normSqSum (F *ᵥ v - a • v) = normSqSum (F *ᵥ v) - a.re ^ 2 := by
    rw [normSqSum_sub_smul, ← ha_def, hv1]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply, ha]
    ring
  have h2 : normSqSum (F *ᵥ v - (E : ℂ) • v) = normSqSum (F *ᵥ v) - 2 * E * a.re + E ^ 2 := by
    rw [normSqSum_sub_smul, ← ha_def, hv1]
    simp only [Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Complex.re_ofReal_mul]
    ring
  unfold regressionFactor
  simp only
  rw [← ha_def, l2Norm_sq_eq, h1, hK, h2, hq]
  congr 1
  ring

theorem im_dot_eq_zero_of_isHermitian {F : Matrix ι ι ℂ} (hF : F.IsHermitian) (v : ι → ℂ) :
    (star v ⬝ᵥ (F *ᵥ v)).im = 0 :=
  hF.im_star_dotProduct_mulVec_self v

theorem quadNum_mul_self_of_isHermitian {K : Matrix ι ι ℂ} (hK : K.IsHermitian) (v : ι → ℂ) :
    quadNum (K * K) v = normSqSum (K *ᵥ v) := by
  have h : K * K = Kᴴ * K := by rw [hK.eq]
  rw [h, ← reInner_mulVec, normSqSum_eq_reInner]

/-- The regression factor is `exp (AngularData.expo v)` at unit `v` when the data's `K` is
`K₀ = F - E` and `t = s/N_aux`, `N_aux = card ι` (`AngularData.t`). -/
theorem regressionFactor_eq_exp_expo (D : AngularData ι) (E : ℝ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hDK : D.K = F - (E : ℂ) • 1) {v : ι → ℂ} (hv : l2Norm v = 1) :
    regressionFactor (Real.toNNReal (D.s / Fintype.card ι)) E v F = Real.exp (D.expo v) := by
  have hv1 := normSqSum_of_l2Norm hv
  have ht : ((Real.toNNReal (D.s / Fintype.card ι) : ℝ≥0) : ℝ) = D.t := by
    rw [Real.coe_toNNReal _ (div_nonneg D.hs.le (Nat.cast_nonneg _))]; rfl
  rw [ht, regressionFactor_eq_exp _ _ _ _ hv (im_dot_eq_zero_of_isHermitian hF v)]
  unfold AngularData.expo AngularData.b₂ AngularData.a
  rw [quadQuot_of_unit hv1, quadQuot_of_unit hv1, hDK,
    quadNum_mul_self_of_isHermitian (hDK ▸ D.hK)]

end Regression

/-!
## The exposed pair: cardinality, time, Hermitian blocks
-/

section Pair

variable (p : Parameters) (i : ZMod p.n)

theorem self_ne_add_one : i ≠ i + 1 := by
  intro h
  have h1 : ((1 : ℕ) : ZMod p.n) = 0 := by
    rw [Nat.cast_one]
    have := congrArg (fun x => x - i) h
    simpa using this.symm
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_one] at h1
  have := p.n_ge_four
  omega

/-- `N_aux = |S| = 2W`. -/
theorem card_pairSite : Fintype.card (PairSite p i) = 2 * p.W := by
  classical
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun x : p.Site => x.1 = i ∨ x.1 = i + 1) =
      ({i, i + 1} : Finset (ZMod p.n)) ×ˢ (Finset.univ : Finset (Fin p.W)) := by
    ext x; simp
  rw [this, Finset.card_product, Finset.card_pair (self_ne_add_one p i), Finset.card_univ,
    Fintype.card_fin]

instance : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩

/-- `pairTime p s = s/2W` is the angular time `s/N_aux` on the pair. -/
theorem pairTime_eq_card (s : ℝ) :
    pairTime p s = Real.toNNReal (s / Fintype.card (PairSite p i)) := by
  rw [card_pairSite, pairTime]; push_cast; rfl

/-- Regression factor: for angular data on the pair with `K = F(E) - E`, `s` the
splitting parameter, and unit `v`, `𝓡(E,v,F(E)) = exp (expo v)`. -/
theorem regressionFactor_pairTime_eq_exp_expo (D : AngularData (PairSite p i)) (E : ℝ)
    (F : PairMatrix p i) (hF : F.IsHermitian) (hDK : D.K = F - (E : ℂ) • 1)
    {v : PairSite p i → ℂ} (hv : l2Norm v = 1) :
    regressionFactor (pairTime p D.s) E v F = Real.exp (D.expo v) := by
  rw [pairTime_eq_card]
  exact regressionFactor_eq_exp_expo D E F hF hDK hv

theorem physicalCoareaF_isHermitian {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    {H_R : Matrix α α ℂ} (hR : H_R.IsHermitian) (C : Matrix α β ℂ) {V : Matrix β β ℂ}
    (hV : V.IsHermitian) (E : ℝ) : (physicalCoareaF H_R C V E).IsHermitian := by
  unfold physicalCoareaF physicalCoareaResolvent
  have hres : ((H_R - (E : ℂ) • 1)⁻¹)ᴴ = (H_R - (E : ℂ) • 1)⁻¹ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_smul, conjTranspose_one,
      hR.eq]
    simp
  refine hV.sub ?_
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hres, Matrix.mul_assoc]

theorem vecMulVec_smul_isHermitian {ι : Type*} (E : ℝ) (v : ι → ℂ) :
    ((E : ℂ) • vecMulVec v (star v)).IsHermitian := by
  unfold IsHermitian
  ext a b
  simp only [conjTranspose_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul,
    star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- `assemble ω G` is Hermitian when `H_R` and `V + G` are. -/
theorem assemble_isHermitian {ω : SplitState p i} {G : PairMatrix p i}
    (hR : ω.1.IsHermitian) (hVG : (ω.2.2 + G).IsHermitian) :
    (assemble p i ω G).IsHermitian := by
  funext x y
  simp only [Matrix.conjTranspose_apply, assemble]
  split_ifs with hy hx hx
  · have := congrFun (congrFun hVG ⟨x, hx⟩) ⟨y, hy⟩
    simpa only [Matrix.conjTranspose_apply, Matrix.add_apply, star_add] using this
  · exact star_star _
  · rfl
  · exact congrFun (congrFun hR ⟨x, hx⟩) ⟨y, hy⟩

/-- On Hermitian blocks and Hermitian `G'`, the reconstructed matrix is Hermitian. -/
theorem assemble_reconstructedGaussian_isHermitian
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    {ω : SplitState p i} (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ)
    (v : PairSite p i → ℂ) {G' : Matrix (FrameIndex p) (FrameIndex p) ℂ}
    (hG' : G'.IsHermitian) :
    (assemble p i ω (reconstructedGaussian p i U ω E v G')).IsHermitian := by
  refine assemble_isHermitian p i hR ?_
  have hF := physicalCoareaF_isHermitian hR ω.2.1 hV E
  have hX : ((U v)ᴴ * physicalCoareaF ω.1 ω.2.1 ω.2.2 E * U v + G').IsHermitian :=
    (isHermitian_conjTranspose_mul_mul (U v) hF).add hG'
  simp only [reconstructedGaussian]
  exact hV.add (((vecMulVec_smul_isHermitian E v).add
    (isHermitian_mul_mul_conjTranspose (U v) hX)).sub hF)

/-- The matrix of `𝔷`: `frameM = U_v*K₀U_v + G'`, `K₀ = F(E) - E`, for a frame of a unit `v`. -/
theorem frameM_eq_compress {U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ}
    (hU : IsPairFrame p i U) (ω : SplitState p i) (E : ℝ) {v : PairSite p i → ℂ}
    (hv : l2Norm v = 1) (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ) :
    frameM p i U ω E v G' =
      (U v)ᴴ * (physicalCoareaF ω.1 ω.2.1 ω.2.2 E - (E : ℂ) • 1) * U v + G' := by
  unfold frameM
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    (hU.2 v hv).1]
  abel

/-- `|det M|² = (det M)²` (real determinant) for the Hermitian frame matrix. -/
theorem normSq_det_frameM {U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ}
    {ω : SplitState p i} (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ)
    (v : PairSite p i → ℂ) {G' : Matrix (FrameIndex p) (FrameIndex p) ℂ}
    (hG' : G'.IsHermitian) :
    Complex.normSq (frameM p i U ω E v G').det = ((frameM p i U ω E v G').det.re) ^ 2 := by
  have hF := physicalCoareaF_isHermitian hR ω.2.1 hV E
  have hM : (frameM p i U ω E v G').IsHermitian := by
    unfold frameM
    refine ((isHermitian_conjTranspose_mul_mul (U v) hF).add hG').sub ?_
    unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_one]; simp
  have him : (frameM p i U ω E v G').det.im = 0 := by
    have h := congrArg Matrix.det hM.eq
    rw [det_conjTranspose] at h
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  rw [Complex.normSq_apply, him]; ring

/-- Lebesgue-almost every energy avoids `Spec H_R`. -/
theorem ae_det_sub_smul_ne_zero {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ) :
    ∀ᵐ E : ℝ, (A - (E : ℂ) • 1).det ≠ 0 := by
  have hfin : Set.Finite (Complex.ofReal ⁻¹' {z | A.charpoly.IsRoot z}) :=
    (Polynomial.finite_setOfPred_isRoot (charpoly_monic A).ne_zero).preimage
      Complex.ofReal_injective.injOn
  rw [ae_iff]
  refine measure_mono_null (fun E hE => ?_) (hfin.measure_zero volume)
  simp only [Set.mem_ofPred_eq, not_not] at hE
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot.def, eval_charpoly]
  have : Matrix.scalar κ (E : ℂ) - A = -(A - (E : ℂ) • 1) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [this, det_neg, hE, mul_zero]

end Pair

/-!
## Eigenline projectors
-/

section Projector

variable {ι : Type} [Fintype ι]

/-- The rank-one matrix `ψψ*` of a vector (entries `ψ_x conj ψ_y`). -/
def eigenProjector (ψ : ι → ℂ) : ι → ι → ℂ := fun x y => ψ x * conj (ψ y)

/-- The orthogonal projector `LL*/‖L‖²` onto the line of `L` (zero for `L = 0`). -/
def lineProjector (L : ι → ℂ) : ι → ι → ℂ :=
  fun x y => ((l2Norm L ^ 2)⁻¹ : ℂ) * (L x * conj (L y))

/-- The unit vector `L/‖L‖`. -/
def normalize (L : ι → ℂ) : ι → ℂ := ((l2Norm L)⁻¹ : ℂ) • L

theorem l2Norm_smul (c : ℂ) (L : ι → ℂ) : l2Norm (c • L) = ‖c‖ * l2Norm L := by
  unfold l2Norm
  have : (∑ k, ‖(c • L) k‖ ^ 2) = ‖c‖ ^ 2 * ∑ k, ‖L k‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- `LL*/‖L‖²` is invariant under `L ↦ cL`, `c ≠ 0`. -/
theorem lineProjector_smul {c : ℂ} (hc : c ≠ 0) (L : ι → ℂ) :
    lineProjector (c • L) = lineProjector L := by
  funext x y
  unfold lineProjector
  rw [l2Norm_smul]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  have hc2 : ((‖c‖ : ℂ) ^ 2)⁻¹ * (‖c‖ : ℂ) ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.2 hc))
  have hcc : c * conj c = (‖c‖ : ℂ) ^ 2 := Complex.mul_conj' c
  push_cast
  linear_combination (((l2Norm L : ℂ) ^ 2)⁻¹ * ((‖c‖ : ℂ) ^ 2)⁻¹ * (L x * conj (L y))) * hcc +
    (((l2Norm L : ℂ) ^ 2)⁻¹ * (L x * conj (L y))) * hc2

theorem normalize_smul_pos {r : ℝ} (hr : 0 < r) (L : ι → ℂ) :
    normalize ((r : ℂ) • L) = normalize L := by
  unfold normalize
  rw [l2Norm_smul, smul_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  by_cases hL : l2Norm L = 0
  · simp [hL]
  · have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hl' : (l2Norm L : ℂ) ≠ 0 := by exact_mod_cast hL
    congr 1
    push_cast
    field_simp

/-- If `ψψ* = LL*/‖L‖²` with `L ≠ 0`, then `ψ = c L/‖L‖` for a phase `|c| = 1`. -/
theorem exists_phase_of_eigenProjector_eq {ψ L : ι → ℂ} (hL : L ≠ 0)
    (h : eigenProjector ψ = lineProjector L) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ψ = c • normalize L := by
  classical
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hL
  simp only [Pi.zero_apply] at hx
  have hr : 0 < l2Norm L := by
    unfold l2Norm
    exact Real.sqrt_pos.2 (lt_of_lt_of_le (by positivity : 0 < ‖L x‖ ^ 2)
      (Finset.single_le_sum (f := fun k => ‖L k‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ x)))
  set r := l2Norm L with hr_def
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hxx := congrFun (congrFun h x) x
  unfold eigenProjector lineProjector at hxx
  rw [← hr_def, Complex.mul_conj', Complex.mul_conj'] at hxx
  have hψx : ψ x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hxx
    have : (‖L x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hx
    simp [hrC, this] at hxx
  have hcψ : conj (ψ x) ≠ 0 := by simpa using hψx
  have hnorm : ‖ψ x‖ = ‖L x‖ / r := by
    have h2 : (‖ψ x‖ : ℂ) ^ 2 = ((‖L x‖ / r : ℝ) : ℂ) ^ 2 := by
      rw [hxx]; push_cast; field_simp
    have h3 : ‖ψ x‖ ^ 2 = (‖L x‖ / r) ^ 2 := by exact_mod_cast h2
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
  refine ⟨(r : ℂ)⁻¹ * conj (L x) / conj (ψ x), ?_, ?_⟩
  · rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_conj, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, hnorm]
    have : ‖L x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    field_simp
  · funext y
    have hyx := congrFun (congrFun h y) x
    unfold eigenProjector lineProjector at hyx
    rw [← hr_def] at hyx
    simp only [normalize, Pi.smul_apply, smul_eq_mul, ← hr_def]
    field_simp
    have hrr : (r : ℂ) ^ 2 * ((r : ℂ)⁻¹) ^ 2 = 1 := by field_simp
    linear_combination (r : ℂ) ^ 2 * hyx + L y * conj (L x) * hrr

/-- A phase-invariant test of `ψ` with `ψψ* = LL*/‖L‖²`, `L ≠ 0`, is the test of `L/‖L‖`. -/
theorem phase_eq_of_eigenProjector_eq {β : Type*} (φ : (ι → ℂ) → β)
    (hφ : ∀ (ψ : ι → ℂ) (c : ℂ), ‖c‖ = 1 → φ (c • ψ) = φ ψ) {ψ L : ι → ℂ} (hL : L ≠ 0)
    (h : eigenProjector ψ = lineProjector L) : φ ψ = φ (normalize L) := by
  obtain ⟨c, hc, rfl⟩ := exists_phase_of_eigenProjector_eq hL h
  exact hφ _ c hc

end Projector

/-!
## Block masses and the contrast as functions of the eigenline
-/

section Contrast

variable (p : Parameters) (i : ZMod p.n)

/-- Block mass `Σ_a P_{(k,a),(k,a)}` of a matrix `P` on sites (`p_k` for `P = ψψ*`). -/
def projBlockMass (P : p.Site → p.Site → ℂ) (k : ZMod p.n) : ℝ :=
  ∑ a : Fin p.W, (P (k, a) (k, a)).re

/-- Pair mass `p_i + p_{i+1}` of `P`. -/
def projPairMass (P : p.Site → p.Site → ℂ) : ℝ :=
  projBlockMass p P i + projBlockMass p P (i + 1)

/-- Contrast `(p_i - p_{i+1})/(p_i + p_{i+1})` of `P`. -/
def projContrast (P : p.Site → p.Site → ℂ) : ℝ :=
  (projBlockMass p P i - projBlockMass p P (i + 1)) / projPairMass p i P

theorem physicalOrderedBlockMass_eq_projBlockMass (H : p.SiteMatrix) (α : Fin p.N)
    (k : ZMod p.n) : physicalOrderedBlockMass p H α k =
      projBlockMass p (eigenProjector (physicalOrderedEigenvector p H α)) k := by
  unfold physicalOrderedBlockMass projBlockMass eigenProjector
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem pairMass_eq_projPairMass (α : Fin p.N) (H : p.SiteMatrix) :
    pairMass p i α H = projPairMass p i (eigenProjector (physicalOrderedEigenvector p H α)) := by
  unfold pairMass projPairMass
  rw [physicalOrderedBlockMass_eq_projBlockMass, physicalOrderedBlockMass_eq_projBlockMass]

theorem physicalPairContrast_eq_projContrast (α : Fin p.N) (H : p.SiteMatrix) :
    physicalPairContrast p α i H =
      projContrast p i (eigenProjector (physicalOrderedEigenvector p H α)) := by
  unfold physicalPairContrast projContrast projPairMass
  rw [physicalOrderedBlockMass_eq_projBlockMass, physicalOrderedBlockMass_eq_projBlockMass]

theorem projBlockMass_lineProjector (L : p.Site → ℂ) (k : ZMod p.n) :
    projBlockMass p (lineProjector L) k = (∑ a : Fin p.W, ‖L (k, a)‖ ^ 2) / l2Norm L ^ 2 := by
  unfold projBlockMass lineProjector
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, Complex.ofReal_re, div_eq_inv_mul]

/-- Sum over the pair `S = {i, i+1}` as two block sums. -/
theorem sum_pairSite (g : p.Site → ℝ) :
    ∑ x : PairSite p i, g x.1 = ∑ a : Fin p.W, g (i, a) + ∑ a : Fin p.W, g (i + 1, a) := by
  classical
  rw [← Finset.sum_subtype (({i, i + 1} : Finset (ZMod p.n)) ×ˢ Finset.univ)
    (fun x => by simp) g, Finset.sum_product, Finset.sum_pair (self_ne_add_one p i)]

theorem schurLift_pair (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (v : PairSite p i → ℂ)
    (x : PairSite p i) : schurLift p i H_R C E v x.1 = v x := by
  unfold schurLift
  split_ifs with h
  · rfl
  · exact absurd x.2 h

theorem schurLift_smul (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (c : ℂ) (v : PairSite p i → ℂ) :
    schurLift p i H_R C E (c • v) = c • schurLift p i H_R C E v := by
  funext x
  unfold schurLift
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rfl
  · rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_neg]

theorem schurLift_ne_zero (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) {v : PairSite p i → ℂ}
    (hv : v ≠ 0) : schurLift p i H_R C E v ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hv
  intro h
  apply hx
  rw [← schurLift_pair p i H_R C E v x, h]; rfl

/-- `p_i + p_{i+1} = ‖v‖²/‖L_E v‖²` on the line of `L_E v`. -/
theorem projPairMass_lineProjector_schurLift
    (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (v : PairSite p i → ℂ) :
    projPairMass p i (lineProjector (schurLift p i H_R C E v)) =
      normSqSum v / l2Norm (schurLift p i H_R C E v) ^ 2 := by
  set L := schurLift p i H_R C E v
  have hv : normSqSum v = ∑ x : PairSite p i, ‖L x.1‖ ^ 2 := by
    unfold normSqSum
    exact Finset.sum_congr rfl fun x _ => by
      rw [show L x.1 = v x from schurLift_pair p i H_R C E v x]
  unfold projPairMass
  rw [projBlockMass_lineProjector, projBlockMass_lineProjector, hv,
    sum_pairSite p i (fun y => ‖L y‖ ^ 2), add_div]

/-- **The contrast on the line of `L_E v`**:
`(p_i - p_{i+1})/(p_i + p_{i+1}) = Re(v*Jv)/‖v‖²`,
`J = P_i - P_{i+1}` on the pair, for `v ≠ 0`.
-/
theorem projContrast_lineProjector_schurLift
    (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) {v : PairSite p i → ℂ}
    (hv : v ≠ 0) :
    projContrast p i (lineProjector (schurLift p i H_R C E v)) =
      quadQuot (pairContrast p i) v := by
  set L := schurLift p i H_R C E v
  have hL : l2Norm L ^ 2 ≠ 0 := by
    have := schurLift_ne_zero p i H_R C E hv
    rw [l2Norm_sq_eq]; exact (normSqSum_pos this).ne'
  set Mi := ∑ a : Fin p.W, ‖L (i, a)‖ ^ 2
  set Mj := ∑ a : Fin p.W, ‖L (i + 1, a)‖ ^ 2
  have hnorm : normSqSum v = Mi + Mj := by
    have : normSqSum v = ∑ x : PairSite p i, ‖L x.1‖ ^ 2 := by
      unfold normSqSum
      exact Finset.sum_congr rfl fun x _ => by
        rw [show L x.1 = v x from schurLift_pair p i H_R C E v x]
    rw [this, sum_pairSite p i (fun y => ‖L y‖ ^ 2)]
  have hJ : (∑ a, conj (v a) * (pairContrast p i *ᵥ v) a).re = Mi - Mj := by
    have : (∑ a, conj (v a) * (pairContrast p i *ᵥ v) a).re =
        ∑ x : PairSite p i, (if x.1.1 = i then (1 : ℝ) else -1) * ‖L x.1‖ ^ 2 := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      unfold pairContrast
      rw [mulVec_diagonal, show L x.1 = v x from schurLift_pair p i H_R C E v x]
      split_ifs
      · rw [one_mul, mul_comm, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re,
          one_mul]
      · rw [neg_one_mul, mul_neg, mul_comm, Complex.mul_conj', ← Complex.ofReal_pow,
          Complex.neg_re, Complex.ofReal_re, neg_one_mul]
    rw [this, sum_pairSite p i (fun y => (if y.1 = i then (1 : ℝ) else -1) * ‖L y‖ ^ 2)]
    have hne : ¬ (i + 1 = i) := fun h => self_ne_add_one p i h.symm
    simp only [ite_true, one_mul, hne, ite_false, neg_one_mul, Finset.sum_neg_distrib]
    ring
  unfold projContrast projPairMass
  rw [projBlockMass_lineProjector, projBlockMass_lineProjector, quadQuot, hJ, hnorm,
    ← sub_div, ← add_div, div_div_div_cancel_right₀ hL]

/-- The angular test `v ↦ φ(L_E v/‖L_E v‖)` is scale invariant in `v`. -/
theorem isScaleInvariant_normalize_schurLift
    (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (φ : (p.Site → ℂ) → ℝ) :
    IsScaleInvariant (fun v => φ (normalize (schurLift p i H_R C E v))) := by
  intro v r hr
  simp only
  rw [show r • v = (r : ℂ) • v from (Complex.coe_smul r v).symm, schurLift_smul,
    normalize_smul_pos hr]

/-- Observables of the eigenline `L_E v(L_E v)*/‖L_E v‖²` are scale invariant in `v`. -/
theorem isScaleInvariant_lineProjector_schurLift
    (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (f : (p.Site → p.Site → ℂ) → ℝ) :
    IsScaleInvariant (fun v => f (lineProjector (schurLift p i H_R C E v))) := by
  intro v r hr
  simp only
  rw [show r • v = (r : ℂ) • v from (Complex.coe_smul r v).symm, schurLift_smul,
    lineProjector_smul (by exact_mod_cast hr.ne')]

end Contrast

/-!
## The fixed-`ω` pair-law fiber in angular form
-/

section Fiber

variable (p : Parameters) (i : ZMod p.n)

/-- The determinant factor `𝔷_E(v) = E_{G_{d-1}}[|det(U_v*K₀U_v + G)|² 1{N_- = α - N_R(E) - 1}]`
(`K₀ = F(E) - E`; the matrix is `frameM`, `frameM_eq_compress`; `|det|² = det²`,
`normSq_det_frameM`; zero-based rank `α`, as in `coareaFiber`). -/
def detFactor (α : Fin p.N) (s : ℝ)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) : ℝ≥0∞ :=
  ∫⁻ G', ENNReal.ofReal (Complex.normSq (frameM p i U ω E v G').det) *
      (if negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
        then 1 else 0)
    ∂(gueMeasure (FrameIndex p) (pairTime p s))

/-- The angular weight `c_{d,t} 𝓡(E,v,F(E)) (n/2)` of the size-biased pair law. -/
def angularWeight (s : ℝ) (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) : ℝ :=
  coareaConstant (2 * p.W) (pairTime p s) *
    regressionFactor (pairTime p s) E v (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) * ((p.n : ℝ) / 2)

theorem angularWeight_nonneg (s : ℝ) (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) :
    0 ≤ angularWeight p i s ω E v := by
  unfold angularWeight
  have h1 : 0 ≤ coareaConstant (2 * p.W) (pairTime p s) := by
    unfold coareaConstant
    have : (0 : ℝ) ≤ (pairTime p s : ℝ) := NNReal.coe_nonneg _
    positivity
  have h2 : 0 ≤ regressionFactor (pairTime p s) E v (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) :=
    (Real.exp_pos _).le
  have h3 : (0 : ℝ) ≤ (p.n : ℝ) / 2 := by positivity
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-- At unit `v`, the angular weight is `c_{d,t}(n/2) exp (expo v)` for the angular data with
`K = F(E) - E` and `s` the splitting parameter (the angular measure, `N_aux = 2W`). -/
theorem angularWeight_eq_exp_expo (ω : SplitState p i) (hR : ω.1.IsHermitian)
    (hV : ω.2.2.IsHermitian) (E : ℝ) (D : AngularData (PairSite p i))
    (hDK : D.K = physicalCoareaF ω.1 ω.2.1 ω.2.2 E - (E : ℂ) • 1) {v : PairSite p i → ℂ}
    (hv : l2Norm v = 1) :
    angularWeight p i D.s ω E v =
      coareaConstant (2 * p.W) (pairTime p D.s) * ((p.n : ℝ) / 2) * Real.exp (D.expo v) := by
  unfold angularWeight
  rw [regressionFactor_pairTime_eq_exp_expo p i D E _ (physicalCoareaF_isHermitian hR ω.2.1 hV E)
    hDK hv]
  ring

/-- **The fixed-`ω` pair-law fiber in angular form.**
For a frame `U`, Hermitian exterior and pair blocks of `ω`, and every finite observable `Ψ`
of `(λ_α, ψ_αψ_α*)`, the fiber of the pair law (`coareaFiber` with crossing factor `n/2`) is
`∫ dE ∫ ν_N(dv) c_{d,t}(n/2)𝓡 · Ψ(E, L_Ev(L_Ev)*/‖L_Ev‖²) · 𝔷_E(v)`.
The observable leaves the `G'`-integral because, on the support of the inertia indicator and of
`det`, `reconstructed_rank` gives `λ_α = E` and the eigenline of `L_E v`, independent of `G'`.
The exceptional sets: `E ∈ Spec H_R` (Lebesgue-null, `ae_det_sub_smul_ne_zero`), non-unit `v`
(`ν_N`-null), non-Hermitian `G'` (GUE-null), and `det = 0` (integrand zero). -/
theorem coareaFiber_eq_angular (hC : CoareaContract) (α : Fin p.N) (s : ℝ)
    {U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ} (hU : IsPairFrame p i U)
    (ω : SplitState p i) (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian)
    (Ψ : ℝ → (p.Site → p.Site → ℂ) → ℝ≥0∞) (hΨ : ∀ E P, Ψ E P ≠ ∞) :
    coareaFiber p α i s U (fun _ _ _ => (p.n : ℝ) / 2) ω
        (fun G => Ψ (physicalOrderedEigenvalue p (assemble p i ω G) α)
          (eigenProjector (physicalOrderedEigenvector p (assemble p i ω G) α))) =
      ∫⁻ E, ∫⁻ v, ENNReal.ofReal (angularWeight p i s ω E v) *
          Ψ E (lineProjector (schurLift p i ω.1 ω.2.1 E v)) * detFactor p i α s U ω E v
        ∂projectiveHaar (PairSite p i) ∂volume := by
  unfold coareaFiber
  refine lintegral_congr_ae ?_
  filter_upwards [ae_det_sub_smul_ne_zero ω.1] with E hE
  refine lintegral_congr_ae ?_
  filter_upwards [ae_projectiveHaar_unit] with v hv
  have hl2 : l2Norm v = 1 := by rw [l2Norm, ← normSqSum, hv, Real.sqrt_one]
  unfold detFactor
  rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hΨ _ _))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_gueMeasure_isHermitian (FrameIndex p) (pairTime p s)] with G' hG'
  have hw : coareaConstant (2 * p.W) (pairTime p s) *
      regressionFactor (pairTime p s) E v (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) *
      ((p.n : ℝ) / 2) * Complex.normSq (frameM p i U ω E v G').det =
      angularWeight p i s ω E v * Complex.normSq (frameM p i U ω E v G').det := rfl
  rw [hw, ENNReal.ofReal_mul (angularWeight_nonneg p i s ω E v)]
  by_cases hdet : (frameM p i U ω E v G').det = 0
  · simp [hdet]
  by_cases hind :
      negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
  · have hr := hC.reconstructed_rank p α i U hU ω E v G'
      (assemble_reconstructedGaussian_isHermitian p i U hR hV E v hG') hl2 hE hdet hind
    simp only at hr
    obtain ⟨h1, h2⟩ := hr
    have hP : eigenProjector (physicalOrderedEigenvector p
        (assemble p i ω (reconstructedGaussian p i U ω E v G')) α) =
        lineProjector (schurLift p i ω.1 ω.2.1 E v) :=
      funext fun x => funext fun y => h2 x y
    simp only [hind, ite_true, h1, hP]
    ring
  · simp only [hind, ite_false, mul_zero, zero_mul]

/-- The same identity for the full right side `coareaRHS` (the complete coarea formula with `n/2`),
for observables `Ψ(ω, λ_α, ψ_αψ_α*)`, when `Pω`-a.e. `ω` has Hermitian blocks
(`ae_hermitian_of_isPairSplitting`). -/
theorem coareaRHS_eq_angular (hC : CoareaContract) (α : Fin p.N) (s : ℝ)
    (Pω : Measure (SplitState p i))
    (hherm : ∀ᵐ ω ∂Pω, ω.1.IsHermitian ∧ ω.2.2.IsHermitian)
    {U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ} (hU : IsPairFrame p i U)
    (Ψ : SplitState p i → ℝ → (p.Site → p.Site → ℂ) → ℝ≥0∞) (hΨ : ∀ ω E P, Ψ ω E P ≠ ∞) :
    coareaRHS p α i s Pω U (fun _ _ _ => (p.n : ℝ) / 2)
        (fun ω G => Ψ ω (physicalOrderedEigenvalue p (assemble p i ω G) α)
          (eigenProjector (physicalOrderedEigenvector p (assemble p i ω G) α))) =
      ∫⁻ ω, ∫⁻ E, ∫⁻ v, ENNReal.ofReal (angularWeight p i s ω E v) *
          Ψ ω E (lineProjector (schurLift p i ω.1 ω.2.1 E v)) * detFactor p i α s U ω E v
        ∂projectiveHaar (PairSite p i) ∂volume ∂Pω := by
  unfold coareaRHS
  refine lintegral_congr_ae ?_
  filter_upwards [hherm] with ω hω
  exact coareaFiber_eq_angular p i hC α s hU ω hω.1 hω.2 (Ψ ω) (hΨ ω)

/-- Every exact pair splitting has Hermitian exterior and pair blocks almost surely. -/
theorem ae_hermitian_of_isPairSplitting {model : p.GaussianRingModel} {s : ℝ}
    {Pω : Measure (SplitState p i)} (h : IsPairSplitting p i model s Pω) :
    ∀ᵐ ω ∂Pω, ω.1.IsHermitian ∧ ω.2.2.IsHermitian := by
  have hH : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.IsHermitian := model.isPhysical.1
  rw [← h, ae_map_iff (measurable_assemble p i).aemeasurable
    (measurableSet_isHermitian p.Site)] at hH
  have hG := ae_gueMeasure_isHermitian (PairSite p i) (pairTime p s)
  have hprob : IsProbabilityMeasure (gueMeasure (PairSite p i) (pairTime p s)) := by
    unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
    infer_instance
  have h2 := Measure.ae_ae_of_ae_prod hH
  filter_upwards [h2] with ω hω
  obtain ⟨G, hGa, hGh⟩ := (hω.and hG).exists
  refine ⟨?_, ?_⟩
  · funext x y
    have := congrFun (congrFun hGa x.1) y.1
    simpa [Matrix.conjTranspose_apply, assemble, x.2, y.2] using this
  · have hVG : (ω.2.2 + G).IsHermitian := by
      funext x y
      have := congrFun (congrFun hGa x.1) y.1
      simpa [Matrix.conjTranspose_apply, assemble, x.2, y.2] using this
    have := hVG.sub hGh
    simpa using this

end Fiber

/-!
## Composition with the center splitting (`PairCoareaBridge`)
-/

section Center

variable (p : Parameters) (i : ZMod p.n)

theorem measurable_eigenProjector_physical (α : Fin p.N) :
    Measurable (fun H : p.SiteMatrix => eigenProjector (physicalOrderedEigenvector p H α)) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  exact (measurable_physicalOrderedEigenvector p α x).mul
    (Complex.continuous_conj.measurable.comp (measurable_physicalOrderedEigenvector p α y))

/-- **Step 1 on the center extension.** For a center splitting (`IsCenterSplitting`), every
pair-law expectation of a finite measurable observable `Ψ(ω, λ_α, ψ_αψ_α*)` of the split
residual `ω = (H_R, C, V)` of `H - G_e` and the eigenline of the reassembled matrix is the
`Pω`-average of the angular form
`∫ dE ∫ ν_N(dv) c_{d,t}(n/2)𝓡 Ψ(ω, E, L_Ev(L_Ev)*/‖L_Ev‖²) 𝔷_E(v)`, `s = min(c,b)`. -/
theorem lintegral_extendedPairMeasure_eq_angular (hC : CoareaContract)
    {model : p.GaussianRingModel} (α : Fin p.N) (X : PairExtension p model)
    (G : X.Ω → PairMatrix p i) (hG : IsCenterSplitting X G)
    {U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ} (hU : IsPairFrame p i U)
    (Ψ : SplitState p i → ℝ → (p.Site → p.Site → ℂ) → ℝ≥0∞)
    (hΨm : Measurable (fun x : SplitState p i × ℝ × (p.Site → p.Site → ℂ) => Ψ x.1 x.2.1 x.2.2))
    (hΨ : ∀ ω E P, Ψ ω E P ≠ ∞) :
    (∫⁻ ω, (fun (ω' : SplitState p i) (G' : PairMatrix p i) =>
          Ψ ω' (physicalOrderedEigenvalue p (assemble p i ω' G') α)
            (eigenProjector (physicalOrderedEigenvector p (assemble p i ω' G') α)))
          (splitOf p i (X.Hm ω - embedPair p i (G ω))) (G ω)
        ∂extendedPairMeasure p α i X.P X.Hm) =
      ∫⁻ ω, ∫⁻ E, ∫⁻ v, ENNReal.ofReal (angularWeight p i (splitS p) ω E v) *
          Ψ ω E (lineProjector (schurLift p i ω.1 ω.2.1 E v)) *
            detFactor p i α (splitS p) U ω E v
        ∂projectiveHaar (PairSite p i) ∂volume
        ∂(X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω)))) := by
  have hm : Measurable (Function.uncurry (fun (ω' : SplitState p i) (G' : PairMatrix p i) =>
      Ψ ω' (physicalOrderedEigenvalue p (assemble p i ω' G') α)
        (eigenProjector (physicalOrderedEigenvector p (assemble p i ω' G') α)))) := by
    have hA := measurable_assemble p i
    exact hΨm.comp (measurable_fst.prodMk
      (((measurable_physicalOrderedEigenvalue p α).comp hA).prodMk
        ((measurable_eigenProjector_physical p α).comp hA)))
  rw [lintegral_extendedPairMeasure_eq_coareaRHS p i hC α X G hG U hU _ hm]
  exact coareaRHS_eq_angular p i hC α (splitS p) _
    (ae_hermitian_of_isPairSplitting p i (isPairSplitting_of_centerSplitting p i X G hG)) hU Ψ hΨ

end Center

end BlockBand.Angular.FiberAngular

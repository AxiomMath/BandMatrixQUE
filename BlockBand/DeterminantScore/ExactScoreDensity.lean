module

public import BlockBand.DeterminantScore.ExactScoreFrame

/-!
# The horizontal derivative of the angular density `𝔷`

The generic part of the `exact` clause of the determinant score theorem.

Setting: `card ι = m + 1`, `K₀` Hermitian, `G ~ G_m(t)` (`hermGaussian m t`, every `t ≥ 0`),
every sector `ℓ`; `𝔷 = angularDensity m t ℓ K₀` (`BlockBand.Angular.DetFactor`).
* `sectorInvMoment m t K ℓ = E[1{N_-(K+G)=ℓ} det(K+G)² (K+G)⁻¹]` (the unnormalized `Z_ℓ R̄`);
  entrywise integrable (`integrable_sectorDetSqInv`, pole removal `sectorDetSqInv_eq`) and
  Hermitian (`sectorInvMoment_isHermitian`);
  `integral_sector_trace`: `E[1 det² Tr(R X)] = Tr(S X)` for every matrix `X`.
* `angularDensity_fderiv_horizontal`: for every orthonormal frame `U` of `v^⊥`, unit `v`, any
  real Fréchet derivative `D` of `𝔷` at `v` and every `h ⊥ v` (`h*v = 0`),
  `D[h] = -4 Re((U*h)* S (U*K₀v))`, `S = sectorInvMoment m t (U*K₀U) ℓ`.
  Proof: along the great circle `γ(ε) = cos ε v + sin ε h` (unit `h`) the rotated frame
  `U(ε)` gives `𝔷(γ(ε)) = Re Z_ℓ(U(ε)*K₀U(ε))` (frame independence, `angularDensity_eq`);
  `mass_hasFDerivAt` (the mass derivative of the sector integration by parts) and
  `paramDeriv_rotCompress` give `d/dε|₀ = Re 2E[1 det² Tr(R ∂K)]`, `∂K = -(ac* + ca*)`, and the
  trace algebra `realJacobi_horizontal_rankTwo` gives the factor `-4`. General `h` by real
  homogeneity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.ExactScore

open MeasureTheory Matrix Filter
open BlockBand.Angular.DetFactor BlockBand.DeterminantScore.Sector
open scoped NNReal Topology ComplexOrder

variable {m : ℕ}

/-- `S = E[1{N_-(K+G)=ℓ} det(K+G)² (K+G)⁻¹]`, `G ~ G_m(t)`. -/
def sectorInvMoment (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun j k => ∫ x, sectorDetSqInv K ℓ j k x ∂hermGaussian m t

theorem integrable_sectorDetSqInv (t : ℝ≥0) {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (ℓ : ℕ) (j k : Fin m) : Integrable (sectorDetSqInv K ℓ j k) (hermGaussian m t) := by
  rw [sectorDetSqInv_eq, sectorDetAdj_eq_cut, hermGaussian_eq]
  exact integrable_cut hK ℓ _ _

/-- `E[1{N_-=ℓ} det² Tr(R X)] = Tr(S X)`. -/
theorem integral_sector_trace (t : ℝ≥0) {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (ℓ : ℕ) (X : Matrix (Fin m) (Fin m) ℂ) :
    (∫ x, (if InSector K ℓ x then
        (K + hermOfCoord x).det ^ 2 * ((K + hermOfCoord x)⁻¹ * X).trace else 0)
      ∂hermGaussian m t) = (sectorInvMoment m t K ℓ * X).trace := by
  have hpt : ∀ x, (if InSector K ℓ x then
      (K + hermOfCoord x).det ^ 2 * ((K + hermOfCoord x)⁻¹ * X).trace else 0) =
      ∑ j, ∑ k, sectorDetSqInv K ℓ j k x * X k j := by
    intro x
    unfold sectorDetSqInv
    split_ifs
    · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · simp
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    (integrable_sectorDetSqInv t hK ℓ j k).mul_const _]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sectorInvMoment, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => (integrable_sectorDetSqInv t hK ℓ j k).mul_const _]
  exact Finset.sum_congr rfl fun k _ => integral_mul_const _ _

/-- `S` is Hermitian (`det(K+G)` is real and `R` is Hermitian). -/
theorem sectorInvMoment_isHermitian (t : ℝ≥0) {K : Matrix (Fin m) (Fin m) ℂ}
    (hK : K.IsHermitian) (ℓ : ℕ) : (sectorInvMoment m t K ℓ).IsHermitian := by
  ext j k
  simp only [conjTranspose_apply, sectorInvMoment, Matrix.of_apply, Complex.star_def]
  rw [← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hM := hK.add (isHermitian_hermOfCoord x)
  have him := det_im_eq_zero hM
  simp only [sectorDetSqInv]
  split_ifs
  · rw [map_mul, map_pow, Complex.conj_eq_iff_im.2 him, ← Complex.star_def, hM.inv.apply j k]
  · simp

section Horizontal

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem angularDensity_fderiv_horizontal_unit (hcard : Fintype.card ι = m + 1) (t : ℝ≥0)
    {K₀ : Matrix ι ι ℂ} (hK₀ : K₀.IsHermitian) (ℓ : ℕ) {U : Matrix ι (Fin m) ℂ} {v : ι → ℂ}
    (hU : IsFrame U v) (hv : star v ⬝ᵥ v = 1) {D : (ι → ℂ) →L[ℝ] ℝ}
    (hD : HasFDerivAt (angularDensity m t ℓ K₀) D v) {h : ι → ℂ} (hh : star h ⬝ᵥ h = 1)
    (hhv : star h ⬝ᵥ v = 0) :
    D h = -4 * (star (Uᴴ *ᵥ h) ⬝ᵥ
      (sectorInvMoment m t (Uᴴ * K₀ * U) ℓ *ᵥ (Uᴴ *ᵥ (K₀ *ᵥ v)))).re := by
  have hKH : ∀ ε, (rotCompress U v h K₀ ε).IsHermitian := fun ε =>
    isHermitian_conjTranspose_mul_mul _ hK₀
  have hK' : ∀ a b, DifferentiableAt ℝ (fun ε => rotCompress U v h K₀ ε a b) 0 := fun a b =>
    (hasDerivAt_compress_apply K₀ (rotFrame U v h) _ 0
      (hasDerivAt_rotFrame_apply U v h) a b).differentiableAt
  obtain ⟨L, hL, hLf⟩ := mass_hasFDerivAt t ℓ (rotCompress U v h K₀) 0 hKH hK'
  have h2 : HasDerivAt (fun ε => (sectorMass m t (rotCompress U v h K₀ ε) ℓ).re) (L 1).re 0 :=
    ((Complex.reCLM.hasFDerivAt).comp (0 : ℝ) hL).hasDerivAt
  have hγ : HasDerivAt (rotVec v h) h 0 := by
    refine hasDerivAt_pi.2 fun x => ?_
    have hc := (Real.hasDerivAt_cos 0).ofReal_comp
    have hs := (Real.hasDerivAt_sin 0).ofReal_comp
    convert (hc.mul_const (v x)).add (hs.mul_const (h x)) using 1
    · funext ε
      simp [rotVec]
    · simp
  have hD' : HasFDerivAt (angularDensity m t ℓ K₀) D (rotVec v h 0) := by
    rwa [rotVec_zero]
  have h1 := hD'.comp_hasDerivAt 0 hγ
  have heq : angularDensity m t ℓ K₀ ∘ rotVec v h =
      fun ε => (sectorMass m t (rotCompress U v h K₀ ε) ℓ).re :=
    funext fun ε => angularDensity_eq hcard t hK₀ ℓ (rotVec_ne_zero hv hh hhv ε)
      (isFrame_rotFrame hv hh hhv hU ε)
  rw [heq] at h1
  rw [h1.unique h2, hLf 1, paramDeriv_rotCompress U v h hK₀, rotCompress_zero,
    integral_sector_trace t (isHermitian_conjTranspose_mul_mul U hK₀) ℓ,
    ← realJacobi_horizontal_rankTwo _ (sectorInvMoment_isHermitian t
      (isHermitian_conjTranspose_mul_mul U hK₀) ℓ)]
  simp [Complex.mul_re]

/-- **The horizontal derivative of `𝔷`**: `D𝔷(v)[h] = -4 Re((U*h)* S (U*K₀v))` for every
`h ⊥ v`, every frame `U` of `v^⊥` and unit `v`. -/
theorem angularDensity_fderiv_horizontal (hcard : Fintype.card ι = m + 1) (t : ℝ≥0)
    {K₀ : Matrix ι ι ℂ} (hK₀ : K₀.IsHermitian) (ℓ : ℕ) {U : Matrix ι (Fin m) ℂ} {v : ι → ℂ}
    (hU : IsFrame U v) (hv : star v ⬝ᵥ v = 1) {D : (ι → ℂ) →L[ℝ] ℝ}
    (hD : HasFDerivAt (angularDensity m t ℓ K₀) D v) {h : ι → ℂ} (hhv : star h ⬝ᵥ v = 0) :
    D h = -4 * (star (Uᴴ *ᵥ h) ⬝ᵥ
      (sectorInvMoment m t (Uᴴ * K₀ * U) ℓ *ᵥ (Uᴴ *ᵥ (K₀ *ᵥ v)))).re := by
  by_cases h0 : h = 0
  · subst h0
    simp
  set ρ : ℝ := BlockBand.Internal.Contracts.CoareaPalm.l2Norm h
  have hρ2 : star h ⬝ᵥ h = ((ρ ^ 2 : ℝ) : ℂ) := by
    rw [star_dotProduct_self_eq, l2Norm_sq]
  have hρ : 0 < ρ := by
    refine lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm fun hz => h0 ?_)
    refine dotProduct_star_self_eq_zero.1 ?_
    rw [hρ2, hz]
    simp
  set hu : ι → ℂ := ((ρ⁻¹ : ℝ) : ℂ) • h
  have hhu : star hu ⬝ᵥ hu = 1 := by
    simp only [hu, star_smul, star_ofReal, smul_dotProduct, dotProduct_smul, hρ2, smul_eq_mul]
    push_cast
    field_simp
  have hhuv : star hu ⬝ᵥ v = 0 := by
    simp only [hu, star_smul, star_ofReal, smul_dotProduct, hhv, smul_zero]
  have hh : h = ρ • hu := by
    simp only [hu, ← Complex.coe_smul, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ (by exact_mod_cast hρ.ne'), one_smul]
  have hD1 := angularDensity_fderiv_horizontal_unit hcard t hK₀ ℓ hU hv hD hhu hhuv
  clear_value ρ hu
  subst hh
  rw [D.map_smul, hD1, Matrix.mulVec_smul, star_smul, star_trivial ρ, smul_dotProduct,
    Complex.smul_re, smul_eq_mul, smul_eq_mul]
  ring

end Horizontal

end BlockBand.DeterminantScore.ExactScore

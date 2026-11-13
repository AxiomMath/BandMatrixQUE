module

public import BlockBand.Critical.RelativeVectors.Angular.GapStop

/-!
# Continuity of phase-invariant functions of the eigenvector array

The selected eigenvectors `freshEigenvector K ℓ` are measurable but not continuous in `K` (their
phases jump). A label-phase-invariant function of the array `frameArray V K = (√N V^* u_ℓ(K))_ℓ` is
nevertheless continuous at every Hermitian `K₀` with simple spectrum, along Hermitian matrices
(`tendsto_phaseInvariant_frameArray`): near `K₀` the normalized vectors
`P_ℓ(K) u_ℓ(K₀)/‖P_ℓ(K) u_ℓ(K₀)‖₂` are continuous and differ from `u_ℓ(K)` by unit phases, where
`P_ℓ` is the Lagrange spectral projection (continuous at simple spectrum,
`continuousAt_dysonProjection`). Also `norm_frameArray_le`: `‖frameArray V K‖ ≤ √N Σ |V_xa|` (sup
norm), for every `K`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.Foundations.Spectral BlockBand.Model.Construction BlockBand.Palm.MomentFlow
open scoped ComplexConjugate

variable {N r : ℕ}

/-!
## The spectral projection is continuous at simple spectrum
-/

theorem continuousAt_dysonProjection {H₀ : Matrix (Fin N) (Fin N) ℂ}
    (hs : HasSimpleSpectrum N H₀) (i : Fin N) :
    ContinuousAt (fun H => dysonProjection N H i) H₀ := by
  unfold dysonProjection
  refine tendsto_list_prod (f := fun j H => (((dysonEigenvalue N H i - dysonEigenvalue N H j)⁻¹ :
      ℂ) • (H - (dysonEigenvalue N H j : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)))) _ fun j hj => ?_
  have hji : j ≠ i := by simpa using (List.mem_filter.mp hj).2
  have hcj : Continuous fun H : Matrix (Fin N) (Fin N) ℂ => (dysonEigenvalue N H j : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_dysonEigenvalue j)
  have hci : Continuous fun H : Matrix (Fin N) (Fin N) ℂ => (dysonEigenvalue N H i : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_dysonEigenvalue i)
  have hne : (dysonEigenvalue N H₀ i : ℂ) - dysonEigenvalue N H₀ j ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast fun e => hji (hs.injective e).symm
  exact (((hci.sub hcj).continuousAt.inv₀ hne).smul
    (continuous_id.sub (hcj.smul continuous_const)).continuousAt)

/-- Simple spectrum is an open condition. -/
theorem eventually_hasSimpleSpectrum {H₀ : Matrix (Fin N) (Fin N) ℂ}
    (hs : HasSimpleSpectrum N H₀) : ∀ᶠ H in 𝓝 H₀, HasSimpleSpectrum N H := by
  have h : ∀ᶠ H in 𝓝 H₀, ∀ i j : Fin N, i < j →
      dysonEigenvalue N H j < dysonEigenvalue N H i := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : i < j
    · exact ((continuous_dysonEigenvalue j).continuousAt.eventually_lt
        (continuous_dysonEigenvalue i).continuousAt (hs hij)).mono fun H hH _ => hH
    · exact Filter.Eventually.of_forall fun H h => absurd h hij
  exact h.mono fun H hH i j hij => hH i j hij

/-!
## The selected eigenvectors
-/

theorem star_dotProduct_freshEigenvector_self {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hs : HasSimpleSpectrum N K) (ℓ : Fin N) :
    star (freshEigenvector K ℓ) ⬝ᵥ freshEigenvector K ℓ = 1 := by
  have h := orderedColumnSelection_orthonormal (Fin.cast (Fintype.card_fin N).symm ℓ)
    (Fin.cast (Fintype.card_fin N).symm ℓ) ⟨K, hK⟩ (injective_orderedEigenvalue hK hs)
  simp only [ite_true] at h
  rw [← h]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, freshEigenvector,
    rawOrderedColumnSelection_eq _ K hK]

theorem l2Norm_freshEigenvector {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hs : HasSimpleSpectrum N K) (ℓ : Fin N) : l2Norm (freshEigenvector K ℓ) = 1 := by
  have h := sum_norm_sq_orderedColumnSelection (Fin.cast (Fintype.card_fin N).symm ℓ) ⟨K, hK⟩
    (injective_orderedEigenvalue hK hs)
  unfold l2Norm
  have e : (∑ k, ‖freshEigenvector K ℓ k‖ ^ 2) = 1 := by
    rw [← h]
    simp only [freshEigenvector, rawOrderedColumnSelection_eq _ K hK]
  rw [e, Real.sqrt_one]

theorem l2Norm_smul (c : ℂ) (v : Fin N → ℂ) : l2Norm (c • v) = ‖c‖ * l2Norm v := by
  unfold l2Norm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem continuous_l2Norm : Continuous (l2Norm : (Fin N → ℂ) → ℝ) := by
  unfold l2Norm
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun k _ =>
    ((continuous_apply k).norm).pow 2)

/-- The spectral projection at label `ℓ.rev` is the outer product of `freshEigenvector K ℓ`. -/
theorem dysonProjection_rev_eq_vecMulVec {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hs : HasSimpleSpectrum N K) (ℓ : Fin N) :
    dysonProjection N K ℓ.rev = vecMulVec (freshEigenvector K ℓ) (star (freshEigenvector K ℓ)) := by
  have h := isEigenSelection_revSelection N K hK hs ℓ.rev
  simpa [revSelection, Fin.rev_rev] using h

/-!
## Continuity of phase-invariant functions
-/

/-- The continuous local frame `n_ℓ(H) = P_ℓ(H) u₀/‖P_ℓ(H) u₀‖₂`, `u₀ = u_ℓ(K₀)`. -/
def localFrame (K₀ : Matrix (Fin N) (Fin N) ℂ) (H : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    Fin N → ℂ :=
  ((l2Norm (dysonProjection N H ℓ.rev *ᵥ freshEigenvector K₀ ℓ))⁻¹ : ℂ) •
    (dysonProjection N H ℓ.rev *ᵥ freshEigenvector K₀ ℓ)

theorem vecMulVec_mulVec' (u v w : Fin N → ℂ) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  funext x
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem projection_mulVec_self {K₀ : Matrix (Fin N) (Fin N) ℂ} (hK₀ : K₀.IsHermitian)
    (hs : HasSimpleSpectrum N K₀) (ℓ : Fin N) :
    dysonProjection N K₀ ℓ.rev *ᵥ freshEigenvector K₀ ℓ = freshEigenvector K₀ ℓ := by
  rw [dysonProjection_rev_eq_vecMulVec hK₀ hs, vecMulVec_mulVec',
    star_dotProduct_freshEigenvector_self hK₀ hs, one_smul]

theorem continuous_mulVec_const (v : Fin N → ℂ) :
    Continuous fun M : Matrix (Fin N) (Fin N) ℂ => M *ᵥ v :=
  Continuous.matrix_mulVec continuous_id continuous_const

theorem continuousAt_projection_mulVec {K₀ : Matrix (Fin N) (Fin N) ℂ}
    (hs : HasSimpleSpectrum N K₀) (ℓ : Fin N) (v : Fin N → ℂ) :
    ContinuousAt (fun H => dysonProjection N H ℓ.rev *ᵥ v) K₀ :=
  (continuous_mulVec_const v).continuousAt.comp (continuousAt_dysonProjection hs ℓ.rev)

theorem continuousAt_localFrame {K₀ : Matrix (Fin N) (Fin N) ℂ} (hK₀ : K₀.IsHermitian)
    (hs : HasSimpleSpectrum N K₀) (ℓ : Fin N) :
    ContinuousAt (fun H => localFrame K₀ H ℓ) K₀ := by
  have hw := continuousAt_projection_mulVec hs ℓ (freshEigenvector K₀ ℓ)
  have hn : l2Norm (dysonProjection N K₀ ℓ.rev *ᵥ freshEigenvector K₀ ℓ) ≠ 0 := by
    rw [projection_mulVec_self hK₀ hs, l2Norm_freshEigenvector hK₀ hs]; exact one_ne_zero
  unfold localFrame
  have hn' : ((l2Norm (dysonProjection N K₀ ℓ.rev *ᵥ freshEigenvector K₀ ℓ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hn
  exact ((Complex.continuous_ofReal.continuousAt.comp
    (continuous_l2Norm.continuousAt.comp hw)).inv₀ hn').smul hw

theorem localFrame_self {K₀ : Matrix (Fin N) (Fin N) ℂ} (hK₀ : K₀.IsHermitian)
    (hs : HasSimpleSpectrum N K₀) (ℓ : Fin N) :
    localFrame K₀ K₀ ℓ = freshEigenvector K₀ ℓ := by
  unfold localFrame
  rw [projection_mulVec_self hK₀ hs, l2Norm_freshEigenvector hK₀ hs]
  simp

theorem localFrame_eq_phase {K₀ H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hsH : HasSimpleSpectrum N H) (ℓ : Fin N)
    (hne : l2Norm (dysonProjection N H ℓ.rev *ᵥ freshEigenvector K₀ ℓ) ≠ 0) :
    ∃ α : ℝ, localFrame K₀ H ℓ = Complex.exp ((α : ℂ) * Complex.I) • freshEigenvector H ℓ := by
  set u := freshEigenvector H ℓ
  set c := star u ⬝ᵥ freshEigenvector K₀ ℓ
  have hw : dysonProjection N H ℓ.rev *ᵥ freshEigenvector K₀ ℓ = c • u := by
    rw [dysonProjection_rev_eq_vecMulVec hH hsH, vecMulVec_mulVec']
  rw [hw, l2Norm_smul, l2Norm_freshEigenvector hH hsH, mul_one] at hne
  refine ⟨Complex.arg c, ?_⟩
  unfold localFrame
  rw [hw, l2Norm_smul, l2Norm_freshEigenvector hH hsH, mul_one, smul_smul]
  congr 1
  have h1 := Complex.norm_mul_exp_arg_mul_I c
  have hc : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hne
  calc ((‖c‖ : ℝ) : ℂ)⁻¹ * c = ((‖c‖ : ℝ) : ℂ)⁻¹ * (((‖c‖ : ℝ) : ℂ) *
        Complex.exp ((Complex.arg c : ℂ) * Complex.I)) := by rw [h1]
    _ = Complex.exp ((Complex.arg c : ℂ) * Complex.I) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- **Continuity of phase-invariant functions of the array** at a Hermitian matrix with simple
spectrum, along Hermitian matrices. -/
theorem tendsto_phaseInvariant_frameArray {α : Type*} {l : Filter α}
    {K : α → Matrix (Fin N) (Fin N) ℂ} {K₀ : Matrix (Fin N) (Fin N) ℂ} (hK : Tendsto K l (𝓝 K₀))
    (hherm : ∀ a, (K a).IsHermitian) (hK₀ : K₀.IsHermitian) (hs : HasSimpleSpectrum N K₀)
    (V : Matrix (Fin N) (Fin r) ℂ) {φ : (Fin N → Fin r → ℂ) → ℝ} (hφ : IsLabelPhaseInvariant φ)
    (hφc : ContinuousAt φ (frameArray V K₀)) :
    Tendsto (fun a => φ (frameArray V (K a))) l (𝓝 (φ (frameArray V K₀))) := by
  set A : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin r → ℂ :=
    fun H ℓ => ((Real.sqrt N : ℝ) : ℂ) • (Vᴴ *ᵥ localFrame K₀ H ℓ)
  have hA0 : A K₀ = frameArray V K₀ := by
    funext ℓ; simp only [A, localFrame_self hK₀ hs, frameArray]
  have hAc : ContinuousAt A K₀ := by
    refine continuousAt_pi.2 fun ℓ => ?_
    have hV : Continuous fun v : Fin N → ℂ => Vᴴ *ᵥ v :=
      Continuous.matrix_mulVec continuous_const continuous_id
    exact (continuousAt_const (y := ((Real.sqrt N : ℝ) : ℂ))).smul
      (hV.continuousAt.comp (continuousAt_localFrame hK₀ hs ℓ))
  have hΨc : ContinuousAt (fun H => φ (A H)) K₀ := by
    have : ContinuousAt φ (A K₀) := by rw [hA0]; exact hφc
    exact this.comp hAc
  have hev : ∀ᶠ a in l, φ (A (K a)) = φ (frameArray V (K a)) := by
    have h1 := hK.eventually (eventually_hasSimpleSpectrum hs)
    have h2 : ∀ ℓ : Fin N, ∀ᶠ a in l,
        l2Norm (dysonProjection N (K a) ℓ.rev *ᵥ freshEigenvector K₀ ℓ) ≠ 0 := by
      intro ℓ
      have hc : ContinuousAt (fun H =>
          l2Norm (dysonProjection N H ℓ.rev *ᵥ freshEigenvector K₀ ℓ)) K₀ :=
        continuous_l2Norm.continuousAt.comp (continuousAt_projection_mulVec hs ℓ _)
      have h0 : l2Norm (dysonProjection N K₀ ℓ.rev *ᵥ freshEigenvector K₀ ℓ) ≠ 0 := by
        rw [projection_mulVec_self hK₀ hs, l2Norm_freshEigenvector hK₀ hs]; exact one_ne_zero
      exact hK.eventually (hc.eventually_ne h0)
    filter_upwards [h1, Filter.eventually_all.2 h2] with a ha hb
    choose θ hθ using fun ℓ => localFrame_eq_phase (K₀ := K₀) (hherm a) ha ℓ (hb ℓ)
    have e : A (K a) = fun ℓ => Complex.exp ((θ ℓ : ℂ) * Complex.I) • frameArray V (K a) ℓ := by
      funext ℓ
      simp only [A, hθ ℓ, frameArray, Matrix.mulVec_smul, smul_smul]
      rw [mul_comm]
    rw [e]
    exact hφ θ _
  rw [← hA0]
  exact (hΨc.tendsto.comp hK).congr' hev

theorem norm_freshEigenvector_apply_le' (K : Matrix (Fin N) (Fin N) ℂ) (ℓ i : Fin N) :
    ‖freshEigenvector K ℓ i‖ ≤ 1 := by
  have h := BlockBand.Palm.FreshPalmAssembly.sum_norm_sq_freshEigenvector_le K ℓ
  have hi : ‖freshEigenvector K ℓ i‖ ^ 2 ≤ ∑ x, ‖freshEigenvector K ℓ x‖ ^ 2 :=
    Finset.single_le_sum (f := fun x => ‖freshEigenvector K ℓ x‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ‖freshEigenvector K ℓ i‖ ^ 2 ≤ 1 ^ 2 := by rw [one_pow]; exact hi.trans h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h2

/-- Sup-norm bound of the array, for every raw matrix. -/
def frameBound (V : Matrix (Fin N) (Fin r) ℂ) : ℝ :=
  Real.sqrt N * ∑ x, ∑ a, ‖V x a‖

theorem norm_frameArray_le (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ) :
    ‖frameArray V K‖ ≤ frameBound V := by
  have h0 : 0 ≤ frameBound V := by unfold frameBound; positivity
  refine pi_norm_le_iff_of_nonneg h0 |>.2 fun ℓ => pi_norm_le_iff_of_nonneg h0 |>.2 fun a => ?_
  simp only [frameArray, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold frameBound
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have h1 : ‖(Vᴴ *ᵥ freshEigenvector K ℓ) a‖ ≤ ∑ x, ‖V x a‖ := by
    simp only [Matrix.mulVec, dotProduct, conjTranspose_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (norm_freshEigenvector_apply_le' K ℓ x)
  refine h1.trans ?_
  rw [Finset.sum_comm]
  exact Finset.single_le_sum (f := fun a => ∑ x, ‖V x a‖) (fun _ _ => by positivity)
    (Finset.mem_univ a)

end BlockBand.Critical.RelativeVectors.Angular

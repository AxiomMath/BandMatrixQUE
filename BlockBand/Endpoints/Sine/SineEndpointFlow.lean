module

public import BlockBand.Endpoints.Sine.FlowAdmissionDefs
public import BlockBand.Model.Construction.GaussianDiscriminant
public import BlockBand.Model.Construction.OrderedEigenvalues
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import BlockBand.Endpoints.Sine.FlowAdmissionShifted

/-!
# Eigenvalue branches of the scalar pair flow (deterministic)

This file proves that the unfolded eigenvalue branches of the scalar pair flow are continuous and
absolutely continuous, with velocity given by the pair mass.

**Results.** For Hermitian `H` the branch `t ↦ u_α(t)` is continuous (Weyl,
`se_continuous_branch`); if moreover `H` has simple spectrum and `ρ(E) > 0`, then
`u_α(t) - u_α(s) = ∫_s^t v_α` with `v_α` interval integrable (`se_branch_ftc`).

**Proof.** Simplicity of `H` propagates to `H(t)` off a countable set of `t`: the discriminant
of `charpoly(H + X P_S)` is a polynomial in `X`, nonzero at `0` (`sef_countable_nonsep`). At a
time with simple spectrum the sorted eigenvalue is differentiable with derivative
`‖P_Sψ_α‖²/(𝒩ρ)` (Hellmann–Feynman, `sef_hasDerivAt_eig`: elementary eigenbasis expansion with
Weyl's inequality and the spectral gap, giving a quadratic remainder, `sef_eig_quad`). The
fundamental theorem of calculus off a countable set (`integral_eq_of_hasDerivAt_off_countable_of_le`)
then integrates, the velocity being bounded by `n/2` off that set. No probability is used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks
open scoped InnerProductSpace

/-- A positive lower bound for the gaps of an injective finite family to a fixed value. -/
theorem sef_exists_gap {n : ℕ} (lam : Fin n → ℝ) (hinj : Function.Injective lam) (k : Fin n) :
    ∃ g : ℝ, 0 < g ∧ ∀ β, β ≠ k → g ≤ |lam β - lam k| := by
  classical
  refine ⟨∏ β ∈ Finset.univ.erase k, min |lam β - lam k| 1, ?_, ?_⟩
  · refine Finset.prod_pos fun β hβ => lt_min ?_ one_pos
    have hne : β ≠ k := Finset.ne_of_mem_erase hβ
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hne (hinj h))
  · intro β hβ
    have hmem : β ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hβ, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase _ _ hmem]
    have h1 : ∏ γ ∈ (Finset.univ.erase k).erase β, min |lam γ - lam k| 1 ≤ 1 :=
      Finset.prod_le_one₀ (fun γ _ => le_min (abs_nonneg _) zero_le_one) (fun γ _ => min_le_right _ _)
    have h0 : 0 ≤ min |lam β - lam k| 1 := le_min (abs_nonneg _) zero_le_one
    calc min |lam β - lam k| 1 * ∏ γ ∈ (Finset.univ.erase k).erase β, min |lam γ - lam k| 1
        ≤ min |lam β - lam k| 1 * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ ≤ |lam β - lam k| := by rw [mul_one]; exact min_le_left _ _

section Pert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {n : ℕ}

/-- The quadratic Hellmann–Feynman estimate at one perturbation size. -/
theorem sef_eig_quad (hn : Module.finrank ℂ E = n) (T0 Tp : E →ₗ[ℂ] E) (h0 : T0.IsSymmetric)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖Tp x‖ ≤ B * ‖x‖) (k : Fin n) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ β, β ≠ k → g ≤ |h0.eigenvalues hn β - h0.eigenvalues hn k|)
    (δ : ℝ) (hT : (T0 + (δ : ℂ) • Tp).IsSymmetric)
    (hδ : |δ| * (4 * B * (n + 1)) ≤ g) :
    |hT.eigenvalues hn k - h0.eigenvalues hn k -
        δ * RCLike.re ⟪h0.eigenvectorBasis hn k, Tp (h0.eigenvectorBasis hn k)⟫_ℂ| ≤
      4 * n * B ^ 2 / g * δ ^ 2 := by
  classical
  set lam := h0.eigenvalues hn with hlam
  set e := h0.eigenvectorBasis hn with he
  set μ := hT.eigenvalues hn k with hμ
  set X := hT.eigenvectorBasis hn k with hX
  set a : Fin n → ℂ := fun β => ⟪e β, X⟫_ℂ with ha
  have hXn : ‖X‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.1 k
  have hen : ∀ β, ‖e β‖ = 1 := fun β => (h0.eigenvectorBasis hn).orthonormal.1 β
  -- the eigenvalue equation in the unperturbed eigenbasis
  have hI1 : ∀ β, ((μ : ℂ) - lam β) * a β = (δ : ℂ) * ⟪e β, Tp X⟫_ℂ := by
    intro β
    have h1 : ⟪e β, (T0 + (δ : ℂ) • Tp) X⟫_ℂ = (μ : ℂ) * a β := by
      rw [hX, LinearMap.IsSymmetric.apply_eigenvectorBasis, inner_smul_right]; rfl
    have h2 : ⟪e β, T0 X⟫_ℂ = (lam β : ℂ) * a β := by
      rw [← h0 (e β) X, he, LinearMap.IsSymmetric.apply_eigenvectorBasis, inner_smul_left]
      simp [ha, he, hlam]
    rw [LinearMap.add_apply, LinearMap.smul_apply, inner_add_right, inner_smul_right, h2] at h1
    rw [sub_mul, ← h1]; ring
  -- Weyl's inequality
  have hW : |μ - lam k| ≤ |δ| * B := by
    refine LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le hT h0 hn (fun x => ?_) k
    rw [add_sub_cancel_left, LinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg δ)
  -- the matrix entries of `Tp` between unit vectors are bounded by `B`
  have hI3 : ∀ β (Y : E), ‖Y‖ = 1 → ‖⟪e β, Tp Y⟫_ℂ‖ ≤ B := by
    intro β Y hY
    calc ‖⟪e β, Tp Y⟫_ℂ‖ ≤ ‖e β‖ * ‖Tp Y‖ := norm_inner_le_norm _ _
      _ ≤ 1 * (B * 1) := by rw [hen β, ← hY]; gcongr; exact hB Y
      _ = B := by ring
  have hgpos : 0 ≤ |δ| := abs_nonneg δ
  -- smallness consequences
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hsmall1 : |δ| * B ≤ g / 4 := by
    have : |δ| * B * 4 ≤ |δ| * (4 * B * (n + 1)) := by
      have : |δ| * B * 4 * 1 ≤ |δ| * B * 4 * (n + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) (by positivity)
      linarith
    linarith
  -- the coefficients off `k` are `O(δ)`
  have hI4 : ∀ β, β ≠ k → ‖a β‖ ≤ 2 * |δ| * B / g := by
    intro β hβ
    have hgap' : g / 2 ≤ |μ - lam β| := by
      have := hgap β hβ
      have h3 : |lam β - lam k| ≤ |μ - lam β| + |μ - lam k| := by
        calc |lam β - lam k| = |(μ - lam k) - (μ - lam β)| := by ring_nf
          _ ≤ |μ - lam k| + |μ - lam β| := abs_sub _ _
          _ = _ := add_comm _ _
      linarith
    have hpos : 0 < |μ - lam β| := by linarith
    have heq := congrArg norm (hI1 β)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at heq
    rw [le_div_iff₀ hg]
    have hb := hI3 β X hXn
    have : |μ - lam β| * ‖a β‖ ≤ |δ| * B := by
      rw [heq]; exact mul_le_mul_of_nonneg_left hb hgpos
    nlinarith [norm_nonneg (a β)]
  -- Parseval
  have hP : ∑ β, ‖a β‖ ^ 2 = 1 := by
    rw [ha, (h0.eigenvectorBasis hn).sum_sq_norm_inner_right X, hXn, one_pow]
  have hq : 2 * |δ| * B / g ≤ 1 / (2 * (n + 1)) := by
    rw [div_le_div_iff₀ hg (by positivity)]
    nlinarith
  have hak : 1 / 2 ≤ ‖a k‖ := by
    have hsplit := Finset.add_sum_erase Finset.univ (fun β => ‖a β‖ ^ 2) (Finset.mem_univ k)
    rw [hP] at hsplit
    have hrest : ∑ β ∈ Finset.univ.erase k, ‖a β‖ ^ 2 ≤ n * (1 / (2 * (n + 1))) ^ 2 := by
      calc ∑ β ∈ Finset.univ.erase k, ‖a β‖ ^ 2
          ≤ ∑ β ∈ Finset.univ.erase k, (1 / (2 * (n + 1) : ℝ)) ^ 2 := by
            refine Finset.sum_le_sum fun β hβ => ?_
            have := (hI4 β (Finset.ne_of_mem_erase hβ)).trans hq
            gcongr
        _ = ((Finset.univ.erase k).card : ℝ) * (1 / (2 * (n + 1))) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ n * (1 / (2 * (n + 1))) ^ 2 := by
            gcongr
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
            exact_mod_cast Nat.sub_le n 1
    have hbd : (n : ℝ) * (1 / (2 * (n + 1))) ^ 2 ≤ 1 / 4 := by
      rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : 1 / 4 ≤ ‖a k‖ ^ 2 := by linarith
    nlinarith [norm_nonneg (a k)]
  -- expansion
  have hexp : ⟪e k, Tp X⟫_ℂ = ∑ β, a β * ⟪e k, Tp (e β)⟫_ℂ := by
    conv_lhs => rw [← (h0.eigenvectorBasis hn).sum_repr' X]
    rw [map_sum, inner_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [map_smul, inner_smul_right]
  set mc := ⟪e k, Tp (e k)⟫_ℂ with hmc
  have hkey : (((μ : ℂ) - lam k) - (δ : ℂ) * mc) * a k =
      (δ : ℂ) * ∑ β ∈ Finset.univ.erase k, a β * ⟪e k, Tp (e β)⟫_ℂ := by
    rw [sub_mul, hI1 k, hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    ring
  have hrhs : ‖(δ : ℂ) * ∑ β ∈ Finset.univ.erase k, a β * ⟪e k, Tp (e β)⟫_ℂ‖ ≤
      |δ| * (n * (2 * |δ| * B / g * B)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ hgpos
    calc ‖∑ β ∈ Finset.univ.erase k, a β * ⟪e k, Tp (e β)⟫_ℂ‖
        ≤ ∑ β ∈ Finset.univ.erase k, ‖a β * ⟪e k, Tp (e β)⟫_ℂ‖ := norm_sum_le _ _
      _ ≤ ∑ β ∈ Finset.univ.erase k, (2 * |δ| * B / g * B) := by
          refine Finset.sum_le_sum fun β hβ => ?_
          rw [norm_mul]
          exact mul_le_mul (hI4 β (Finset.ne_of_mem_erase hβ)) (hI3 k (e β) (hen β))
            (norm_nonneg _) (by positivity)
      _ = ((Finset.univ.erase k).card : ℝ) * (2 * |δ| * B / g * B) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * (2 * |δ| * B / g * B) := by
          gcongr
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
          exact_mod_cast Nat.sub_le n 1
  have hnorm : ‖((μ : ℂ) - lam k) - (δ : ℂ) * mc‖ ≤ 4 * n * B ^ 2 / g * δ ^ 2 := by
    have h1 := congrArg norm hkey
    rw [norm_mul] at h1
    have h2 : ‖((μ : ℂ) - lam k) - (δ : ℂ) * mc‖ * (1 / 2) ≤
        |δ| * (n * (2 * |δ| * B / g * B)) := by
      calc _ ≤ ‖((μ : ℂ) - lam k) - (δ : ℂ) * mc‖ * ‖a k‖ :=
            mul_le_mul_of_nonneg_left hak (norm_nonneg _)
        _ = _ := h1
        _ ≤ _ := hrhs
    have h3 : |δ| * (n * (2 * |δ| * B / g * B)) = 4 * n * B ^ 2 / g * δ ^ 2 / 2 := by
      rw [← sq_abs δ]; field_simp; ring
    linarith
  calc |μ - lam k - δ * RCLike.re mc|
      = |RCLike.re (((μ : ℂ) - lam k) - (δ : ℂ) * mc)| := by
        congr 1
        simp [Complex.sub_re, Complex.mul_re]
    _ ≤ ‖((μ : ℂ) - lam k) - (δ : ℂ) * mc‖ := RCLike.abs_re_le_norm _
    _ ≤ _ := hnorm

/-- **Hellmann–Feynman** for a simple sorted eigenvalue of a symmetric linear family
`T0 + δ Tp`: the derivative at `δ = 0` is `⟪e_k, Tp e_k⟫`. -/
theorem sef_hasDerivAt_eig (hn : Module.finrank ℂ E = n) (T0 Tp : E →ₗ[ℂ] E) (h0 : T0.IsSymmetric)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖Tp x‖ ≤ B * ‖x‖)
    (hinj : Function.Injective (h0.eigenvalues hn)) (k : Fin n)
    (hs : ∀ δ : ℝ, (T0 + (δ : ℂ) • Tp).IsSymmetric) :
    HasDerivAt (fun δ : ℝ => (hs δ).eigenvalues hn k)
      (RCLike.re ⟪h0.eigenvectorBasis hn k, Tp (h0.eigenvectorBasis hn k)⟫_ℂ) 0 := by
  obtain ⟨g, hg, hgap⟩ := sef_exists_gap _ hinj k
  have h00 : (hs 0).eigenvalues hn k = h0.eigenvalues hn k := by
    rw [LinearMap.IsSymmetric.eigenvalues_congr (by simp) (hs 0) h0 hn]
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero, h00, smul_eq_mul]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_id (n := 2) one_lt_two)
  refine Asymptotics.IsBigO.of_bound (4 * n * B ^ 2 / g) ?_
  have hc : Tendsto (fun δ : ℝ => |δ| * (4 * B * (n + 1))) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun δ : ℝ => |δ| * (4 * B * (n + 1))) := by fun_prop
    have := hcont.tendsto (0 : ℝ)
    simpa using this
  filter_upwards [hc.eventually (gt_mem_nhds hg)] with δ hδ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg δ)]
  exact sef_eig_quad hn T0 Tp h0 hB0 hB k hg hgap δ (hs δ) hδ.le

end Pert

section Flow

variable (p : Parameters) (i : ZMod p.n)

/-- The unfolded eigenvalue branch `u_α(t) = Nρ(λ_α(H(t)) - E)` of the pair flow
`H(t) = H + t/(𝒩ρ) P_S` (ranks with multiplicity, raw `H`). -/
def se_branch (H : p.SiteMatrix) (E : ℝ) (α : Fin p.N) (t : ℝ) : ℝ :=
  microCoord p E (physicalOrderedEigenvalue p (pairFlow p i H E t) α)

/-- The velocity `v_α(t) = (n/2)‖P_Sψ_α(t)‖²` of the branch `se_branch`, with the selected
eigenvector of `H(t)`.
-/
def se_speed (H : p.SiteMatrix) (E : ℝ) (α : Fin p.N) (t : ℝ) : ℝ :=
  (p.n : ℝ) / 2 * pairMass p i α (pairFlow p i H E t)

theorem se_pairFlow_zero (H : p.SiteMatrix) (E : ℝ) : pairFlow p i H E 0 = H := by
  simp [pairFlow]

section Helpers

open Matrix

theorem sef_poe_eq (A : p.SiteMatrix) (hA : A.IsHermitian) (α : Fin p.N) :
    physicalOrderedEigenvalue p A α =
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace
        (physicalSpectralRank p α).rev := by
  unfold physicalOrderedEigenvalue
  rw [rawIncreasingEigenvalue_eq _ A hA]
  rfl

theorem sef_poe_eq_zero_index (A : p.SiteMatrix) (hA : A.IsHermitian) (α : Fin p.N) :
    physicalOrderedEigenvalue p A α = hA.eigenvalues₀ (physicalSpectralRank p α).rev := by
  unfold physicalOrderedEigenvalue
  rw [rawIncreasingEigenvalue_eq _ A hA]
  rfl

theorem sef_eigvec_eq (A : p.SiteMatrix) (hA : A.IsHermitian) (r : Fin (Fintype.card p.Site)) :
    ⇑((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace
        r.rev) = BlockBand.Foundations.Spectral.increasingEigenvector hA r := by
  simp [BlockBand.Foundations.Spectral.increasingEigenvector,
    BlockBand.Foundations.Spectral.increasingEigenbasis_apply, Matrix.IsHermitian.eigenvectorBasis,
    BlockBand.Foundations.Spectral.increasingIndex]

theorem sef_norm_pairProjector_le (x y : p.Site) : ‖pairProjector p i x y‖ ≤ 1 := by
  unfold pairProjector
  by_cases h : x = y
  · subst h; rw [diagonal_apply_eq]; split_ifs <;> simp
  · rw [diagonal_apply_ne _ h]; simp

theorem sef_isHermitian_shift (A : p.SiteMatrix) (hA : A.IsHermitian) (s : ℝ) :
    (A + (s : ℂ) • pairProjector p i).IsHermitian :=
  hA.add (fa_isHermitian_shift p i s)

/-- Weyl: the shifted branches are `card`-Lipschitz in the shift. -/
theorem sef_abs_sub_le (A : p.SiteMatrix) (hA : A.IsHermitian) (α : Fin p.N) (s s' : ℝ) :
    |physicalOrderedEigenvalue p (A + (s : ℂ) • pairProjector p i) α -
        physicalOrderedEigenvalue p (A + (s' : ℂ) • pairProjector p i) α| ≤
      (Fintype.card p.Site : ℝ) * |s - s'| := by
  rw [sef_poe_eq_zero_index p _ (sef_isHermitian_shift p i A hA s),
    sef_poe_eq_zero_index p _ (sef_isHermitian_shift p i A hA s')]
  refine Matrix.IsHermitian.abs_eigenvalues₀_sub_le_of_entry_le _ _ (fun x y => ?_) _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_add_left_eq_sub]
  rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc |s - s'| * ‖pairProjector p i x y‖ ≤ |s - s'| * 1 :=
        mul_le_mul_of_nonneg_left (sef_norm_pairProjector_le p i x y) (abs_nonneg _)
    _ = |s - s'| := mul_one _

theorem sef_continuous_shift (A : p.SiteMatrix) (hA : A.IsHermitian) (α : Fin p.N) :
    Continuous fun s : ℝ => physicalOrderedEigenvalue p (A + (s : ℂ) • pairProjector p i) α := by
  refine (LipschitzWith.of_dist_le' (K := (Fintype.card p.Site : ℝ)) fun s s' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  exact sef_abs_sub_le p i A hA α s s'

/-- Simple spectrum of `H` forces simple spectrum of `H + sP_S` off a countable set of `s`. -/
theorem sef_countable_nonsep (A : p.SiteMatrix) (hsep : A.charpoly.Separable) :
    {s : ℝ | ¬ (A + (s : ℂ) • pairProjector p i).charpoly.Separable}.Countable := by
  classical
  let Q : Matrix p.Site p.Site (Polynomial ℂ) :=
    (Polynomial.C : ℂ →+* Polynomial ℂ).mapMatrix A +
      (Polynomial.X : Polynomial ℂ) • (Polynomial.C : ℂ →+* Polynomial ℂ).mapMatrix
        (pairProjector p i)
  let D : Polynomial ℂ := Q.charpoly.discr
  have hev : ∀ z : ℂ, (A + z • pairProjector p i).charpoly.discr = D.eval z := by
    intro z
    have hmap : Q.map (Polynomial.evalRingHom z) = A + z • pairProjector p i := by
      ext x y
      simp only [Q, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, RingHom.mapMatrix_apply,
        Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, smul_eq_mul,
        Polynomial.eval_mul, Polynomial.eval_X]
    rw [← hmap, Matrix.charpoly_map,
      BlockBand.Parameters.Polynomial.discr_map_of_monic _ _ (Matrix.charpoly_monic Q)]
    rfl
  have hD : D ≠ 0 := by
    intro h
    have h0 := hev 0
    rw [zero_smul, add_zero, h, Polynomial.eval_zero] at h0
    exact BlockBand.Parameters.Polynomial.discr_ne_zero_of_monic_separable
      (Matrix.charpoly_monic A) hsep h0
  refine ((D.roots.toFinset.finite_toSet.countable).preimage
    Complex.ofReal_injective).mono ?_
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs
  have hz : (A + (s : ℂ) • pairProjector p i).charpoly.discr = 0 :=
    (BlockBand.Parameters.Polynomial.discr_eq_zero_iff_not_separable
      (Matrix.charpoly_monic _)).mpr hs
  rw [hev] at hz
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  exact (Polynomial.mem_roots hD).mpr hz

theorem sef_ne_succ : i ≠ i + 1 := by
  intro h
  have h1 : ((1 : ℕ) : ZMod p.n) = 0 := by
    have := congrArg (fun x => x - i) h
    simp only [sub_self, add_sub_cancel_left] at this
    exact_mod_cast this.symm
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd one_pos h1
  have := p.n_ge_four
  omega

/-- The pair mass is the `P_S`-quadratic form of the selected vector. -/
theorem sef_pairMass_eq (A : p.SiteMatrix) (α : Fin p.N) :
    pairMass p i α A = ∑ x : p.Site, (if x.1 = i ∨ x.1 = i + 1 then (1 : ℝ) else 0) *
      ‖physicalOrderedEigenvector p A α x‖ ^ 2 := by
  classical
  unfold pairMass physicalOrderedBlockMass
  rw [Fintype.sum_prod_type]
  have hk : ∀ k : ZMod p.n, (∑ a : Fin p.W, (if k = i ∨ k = i + 1 then (1 : ℝ) else 0) *
      ‖physicalOrderedEigenvector p A α (k, a)‖ ^ 2) =
      if k = i ∨ k = i + 1 then ∑ a : Fin p.W, ‖physicalOrderedEigenvector p A α (k, a)‖ ^ 2
        else 0 := by
    intro k; split_ifs <;> simp
  simp_rw [hk]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hf : (Finset.univ.filter fun k : ZMod p.n => k = i ∨ k = i + 1) = {i, i + 1} := by
    ext k; simp
  rw [hf, Finset.sum_pair (sef_ne_succ p i)]

/-- **Hellmann–Feynman for the pair shift**: at a Hermitian matrix with simple spectrum, the
sorted eigenvalue of `A + δ P_S` has derivative `‖P_Sψ_α‖²` at `δ = 0`. -/
theorem sef_hasDerivAt_shift (A : p.SiteMatrix) (hA : A.IsHermitian) (hsep : A.charpoly.Separable)
    (α : Fin p.N) :
    HasDerivAt (fun δ : ℝ => physicalOrderedEigenvalue p (A + (δ : ℂ) • pairProjector p i) α)
      (pairMass p i α A) 0 := by
  classical
  set T0 := Matrix.toEuclideanLin A with hT0
  set Tp := Matrix.toEuclideanLin (pairProjector p i) with hTp
  have h0 : T0.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hn : Module.finrank ℂ (EuclideanSpace ℂ p.Site) = Fintype.card p.Site :=
    finrank_euclideanSpace
  have hTδ : ∀ δ : ℝ, T0 + (δ : ℂ) • Tp = Matrix.toEuclideanLin (A + (δ : ℂ) • pairProjector p i) := by
    intro δ; rw [map_add, map_smul]
  have hs : ∀ δ : ℝ, (T0 + (δ : ℂ) • Tp).IsSymmetric := fun δ => by
    rw [hTδ δ]; exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (sef_isHermitian_shift p i A hA δ)
  have hB : ∀ x, ‖Tp x‖ ≤ (Fintype.card p.Site : ℝ) * ‖x‖ := by
    intro x
    have := Matrix.norm_toEuclideanLin_le_of_entry_le_square (ε := 1)
      (sef_norm_pairProjector_le p i) x
    simpa [hTp] using this
  have hinj : Function.Injective (h0.eigenvalues hn) := by
    have h := orderedEigenvalue_injective_of_separable (⟨A, hA⟩ : HermitianMatrix p.Site) hsep
    intro j j' hjj
    have : orderedEigenvalue (⟨A, hA⟩ : HermitianMatrix p.Site) j.rev =
        orderedEigenvalue (⟨A, hA⟩ : HermitianMatrix p.Site) j'.rev := by
      simp only [orderedEigenvalue, BlockBand.Foundations.Spectral.increasingEigenvalue,
        Matrix.IsHermitian.eigenvalues₀, Fin.rev_rev]
      exact hjj
    exact Fin.rev_injective (h this)
  set r := physicalSpectralRank p α with hr
  have key := sef_hasDerivAt_eig hn T0 Tp h0 (Nat.cast_nonneg _) hB hinj r.rev hs
  have hfun : (fun δ : ℝ => physicalOrderedEigenvalue p (A + (δ : ℂ) • pairProjector p i) α) =
      fun δ : ℝ => (hs δ).eigenvalues hn r.rev := by
    funext δ
    rw [sef_poe_eq p _ (sef_isHermitian_shift p i A hA δ)]
    exact congrFun (LinearMap.IsSymmetric.eigenvalues_congr (hTδ δ).symm _ _ hn) r.rev
  rw [hfun]
  convert key using 1
  -- identify the derivative
  have hb : ⇑(h0.eigenvectorBasis hn r.rev) =
      BlockBand.Foundations.Spectral.increasingEigenvector hA r := sef_eigvec_eq p A hA r
  rw [EuclideanSpace.inner_eq_star_dotProduct, hTp, Matrix.ofLp_toLpLin]
  rw [sef_pairMass_eq, hb, Matrix.toLin'_apply, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hsq : ‖physicalOrderedEigenvector p A α x‖ ^ 2 =
      ‖BlockBand.Foundations.Spectral.increasingEigenvector hA r x‖ ^ 2 := by
    unfold physicalOrderedEigenvector
    rw [rawOrderedColumnSelection_eq _ A hA,
      norm_sq_orderedColumnSelection r (⟨A, hA⟩ : HermitianMatrix p.Site)
        (orderedEigenvalue_injective_of_separable (⟨A, hA⟩ : HermitianMatrix p.Site) hsep)]
  rw [hsq, pairProjector, Matrix.mulVec_diagonal]
  set z := BlockBand.Foundations.Spectral.increasingEigenvector hA r x
  have hz : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Pi.star_apply, RCLike.re_to_complex]
  split_ifs
  · rw [one_mul, one_mul, hz, Complex.ofReal_re]
  · simp

theorem sef_pairFlow_eq (H : p.SiteMatrix) (E t t0 : ℝ) :
    pairFlow p i H E t =
      pairFlow p i H E t0 + (((t - t0) / crossingScale p E : ℝ) : ℂ) • pairProjector p i := by
  unfold pairFlow
  rw [add_assoc, ← add_smul]
  congr 2
  push_cast
  ring

/-- Hellmann–Feynman along the flow, at a time with simple spectrum. -/
theorem sef_hasDerivAt_flow (H : p.SiteMatrix) (hH : H.IsHermitian) (E t0 : ℝ)
    (hsep : (pairFlow p i H E t0).charpoly.Separable) (α : Fin p.N) :
    HasDerivAt (fun t => physicalOrderedEigenvalue p (pairFlow p i H E t) α)
      (pairMass p i α (pairFlow p i H E t0) * (1 / crossingScale p E)) t0 := by
  have hA0 : (pairFlow p i H E t0).IsHermitian := sef_isHermitian_shift p i H hH _
  have key := sef_hasDerivAt_shift p i _ hA0 hsep α
  have hlin : HasDerivAt (fun t : ℝ => (t - t0) / crossingScale p E) (1 / crossingScale p E) t0 :=
    ((hasDerivAt_id t0).sub_const t0).div_const _
  have h00 : (t0 - t0) / crossingScale p E = 0 := by simp
  rw [← h00] at key
  have hc := key.comp t0 hlin
  convert hc using 1
  funext t
  simp only [Function.comp]
  rw [sef_pairFlow_eq p i H E t t0]

end Helpers

theorem sef_measurable_pairFlow (H : p.SiteMatrix) (E : ℝ) :
    Measurable fun t : ℝ => pairFlow p i H E t := by
  unfold pairFlow
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem sef_pairMass_le_one (A : p.SiteMatrix) (hA : A.IsHermitian) (hsep : A.charpoly.Separable)
    (α : Fin p.N) : pairMass p i α A ≤ 1 := by
  rw [sef_pairMass_eq]
  refine le_trans (Finset.sum_le_sum fun x _ => ?_)
    (physicalOrderedEigenvector_totalMass p A hA hsep α).le
  exact mul_le_of_le_one_left (sq_nonneg _) (by split_ifs <;> norm_num)

theorem se_speed_nonneg (H : p.SiteMatrix) (E : ℝ) (α : Fin p.N) (t : ℝ) :
    0 ≤ se_speed p i H E α t :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) zero_le_two) (fa_pairMass_nonneg p i α _)

theorem se_measurable_speed (H : p.SiteMatrix) (E : ℝ) (α : Fin p.N) :
    Measurable (se_speed p i H E α) :=
  measurable_const.mul ((fa_measurable_pairMass p i α).comp (sef_measurable_pairFlow p i H E))

/-- Branches are continuous in the flow parameter (Weyl). -/
theorem se_continuous_branch (H : p.SiteMatrix) (hH : H.IsHermitian) (E : ℝ) (α : Fin p.N) :
    Continuous (se_branch p i H E α) := by
  have hg := (sef_continuous_shift p i H hH α).comp (continuous_id.div_const (crossingScale p E))
  unfold se_branch microCoord
  exact continuous_const.mul (hg.sub continuous_const)

/-- **Fundamental theorem of calculus along the flow** (the pair-flow velocity formula, integrated):
for Hermitian `H` with simple spectrum and `ρ(E) > 0`, every branch satisfies
`u_α(t) - u_α(s) = ∫_s^t v_α`, with `v_α` interval integrable. -/
theorem se_branch_ftc (H : p.SiteMatrix) (hH : H.IsHermitian) (hsep : H.charpoly.Separable)
    (E : ℝ) (hρ : 0 < Parameters.semicircleDensity E) (α : Fin p.N) (s t : ℝ) (hst : s ≤ t) :
    IntervalIntegrable (se_speed p i H E α) volume s t ∧
      se_branch p i H E α t - se_branch p i H E α s = ∫ r in s..t, se_speed p i H E α r := by
  have hW : (0 : ℝ) < p.W := Nat.cast_pos.mpr p.W_pos
  have hcs : 0 < crossingScale p E := by unfold crossingScale; positivity
  set S' : Set ℝ := {t | ¬ (pairFlow p i H E t).charpoly.Separable} with hS'def
  have hS' : S'.Countable :=
    (sef_countable_nonsep p i H hsep).preimage
      (fun a b (h : a / crossingScale p E = b / crossingScale p E) => (div_left_inj' hcs.ne').mp h)
  have hbd : ∀ r, r ∉ S' → ‖se_speed p i H E α r‖ ≤ (p.n : ℝ) / 2 := by
    intro r hr
    have hr' : (pairFlow p i H E r).charpoly.Separable := by
      simpa [hS'def] using hr
    rw [Real.norm_of_nonneg (se_speed_nonneg p i H E α r)]
    unfold se_speed
    have := sef_pairMass_le_one p i (pairFlow p i H E r) (sef_isHermitian_shift p i H hH _) hr' α
    have h0 : (0 : ℝ) ≤ (p.n : ℝ) / 2 := by positivity
    nlinarith
  have hae : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ S' :=
    (measure_eq_zero_iff_ae_notMem).mp (hS'.measure_zero volume)
  have hint : IntervalIntegrable (se_speed p i H E α) volume s t := by
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := (p.n : ℝ) / 2) (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne)
      (se_measurable_speed p i H E α).aestronglyMeasurable ?_
    exact ae_restrict_of_ae (hae.mono fun r hr => hbd r hr)
  refine ⟨hint, ?_⟩
  refine (integral_eq_of_hasDerivAt_off_countable_of_le _ _ hst hS'
    (se_continuous_branch p i H hH E α).continuousOn (fun r hr => ?_) hint).symm
  have hr' : (pairFlow p i H E r).charpoly.Separable := by
    have := hr.2
    simpa [hS'def] using this
  have hd := ((sef_hasDerivAt_flow p i H hH E r hr' α).sub_const E).const_mul
    ((p.N : ℝ) * Parameters.semicircleDensity E)
  convert hd using 1
  · funext y; rfl
  unfold se_speed crossingScale
  simp only [Parameters.N]
  push_cast
  field_simp

end Flow

end BlockBand.Endpoints

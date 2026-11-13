module

public import BlockBand.SourceProcess.ClosingLeak.RankOne
public import BlockBand.SourceProcess.ClosingAux.Integrand

/-!
# The pointwise closing error of the sampled integrand

For one sample `x` (path, tag locations, Gaussians) and one phase `θ`, write
`\widehat Q_{M,i} = Σ_l κ_i u_{il}u_{il}*` with `u_{il} = 𝒰*ι_{k_{il}}g_{il}` and
`κ_i = m_i/(MW)` (`sampledSource`), and `D = C(e^{iθ}) - 1` for the physical closing map.
Since every factor lies in `[0,1]`, telescoping and the rank-one bound `abs_invDet_sum_sub_le` give

`|Π_j F(X_j) - Π_j F(C*X_jC)| ≤ Σ_j Σ_{il} √a_{j,i} (Re Tr(DD* κ_iu_{il}u_{il}*))^{1/2}`

(`abs_integrand_sub_le`), `X_j = Σ_i a_{ji}\widehat Q_{M,i}`. The right side is the quantity whose
phase average is given by the Gaussian closing error (`E_z DD* = 2A_-`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingLeak

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.Sampling BlockBand.SourceProcess.ClosingAux
open scoped ComplexOrder

/-- Telescoping: `|Π_i f_i - Π_i g_i| ≤ Σ_i |f_i - g_i|` for values in `[0,1]`. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.sum_insert hk]
    have hP : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg fun i _ => (hg i).1
    have hP1 : ∏ i ∈ s, g i ≤ 1 := Finset.prod_le_one₀ (fun i _ => (hg i).1) fun i _ => (hg i).2
    have e : f k * ∏ i ∈ s, f i - g k * ∏ i ∈ s, g i =
        f k * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f k - g k) * ∏ i ∈ s, g i := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hf k).1, abs_of_nonneg hP]
    have h1 : f k * |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| :=
      (mul_le_of_le_one_left (abs_nonneg _) (hf k).2).trans ih
    have h2 : |f k - g k| * ∏ i ∈ s, g i ≤ |f k - g k| :=
      mul_le_of_le_one_right (abs_nonneg _) hP1
    linarith

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `C* (Σ c_k u_ku_k*) C = Σ c_k (C*u_k)(C*u_k)*`. -/
theorem conj_rkSum (C : Matrix n n ℂ) {κ : Type*} (s : Finset κ) (c : κ → ℝ) (u : κ → n → ℂ) :
    Cᴴ * rkSum s c u * C = rkSum s c (fun k => Cᴴ *ᵥ u k) := by
  simp only [rkSum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_vecMulVec, vecMulVec_mul, star_mulVec, conjTranspose_conjTranspose]

omit [DecidableEq n] in
/-- `√c ‖D*u‖₂ = (Re Tr(DD* · c uu*))^{1/2}`. -/
theorem sqrt_mul_l2 (D : Matrix n n ℂ) {c : ℝ} (hc : 0 ≤ c) (u : n → ℂ) :
    Real.sqrt c * l2 (Dᴴ *ᵥ u) =
      Real.sqrt ((D * Dᴴ * ((c : ℂ) • vecMulVec u (star u))).trace.re) := by
  have h := re_dot_conj_mul Dᴴ u
  rw [conjTranspose_conjTranspose] at h
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul, trace_mul_vecMulVec, h,
    Real.sqrt_mul hc, Real.sqrt_sq (l2_nonneg _)]

theorem l2_sub_conj (C : Matrix n n ℂ) (u : n → ℂ) :
    l2 (u - Cᴴ *ᵥ u) = l2 ((C - 1)ᴴ *ᵥ u) := by
  have e : u - Cᴴ *ᵥ u = -((C - 1)ᴴ *ᵥ u) := by
    rw [conjTranspose_sub, conjTranspose_one, sub_mulVec, one_mulVec, neg_sub]
  rw [e, l2, l2]
  simp

/-!
## The physical sampled integrand
-/

variable {W : ℕ}

/-- The sampled vectors `u_{il} = 𝒰*ι_{k_{il}} g_{il}`. -/
def sampVec (b E : ℝ) (n : ℕ) {p M : ℕ} (x : SampledPath W p M) (il : Fin p × Fin M) :
    Fin 2 × Fin W → ℂ :=
  (boundaryToInterior b E W n x.1)ᴴ *ᵥ tagVector W n (x.2.1 il) (x.2.2 il)

/-- The weights `a_{ji} κ_i`, `κ_i = m_i/(MW)`. -/
def sampCoef (W n : ℕ) {p J : ℕ} (q : Fin p → ℝ → ℝ) (a : Fin J → Fin p → ℝ) (M : ℕ)
    (j : Fin J) (il : Fin p × Fin M) : ℝ :=
  a j il.1 * (gridMass W n (q il.1) / (M * W))

theorem sampCoef_nonneg (W n : ℕ) {p J : ℕ} {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x)
    {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (M : ℕ) (j : Fin J) (il : Fin p × Fin M) :
    0 ≤ sampCoef W n q a M j il :=
  mul_nonneg (ha j il.1) (div_nonneg (gridMass_nonneg W n (hq il.1)) (by positivity))

theorem sourceComb_eq (b E : ℝ) (n : ℕ) {p J M : ℕ} (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) (j : Fin J) (x : SampledPath W p M) :
    ∑ i, (a j i : ℂ) • sampledSource b E W n (q i) M (fun l => x.2.1 (i, l))
        (fun l => x.2.2 (i, l)) x.1 = rkSum Finset.univ (sampCoef W n q a M j) (sampVec b E n x) := by
  simp only [rkSum, sampledSource, sampCoef, sampVec, Finset.smul_sum, smul_smul,
    Fintype.sum_prod_type]
  push_cast
  rfl

/-- The integrand of `sampledPhysTransform`. -/
def physIntegrand (b E T : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ) (a : Fin J → Fin p → ℝ)
    (M W : ℕ) (x : SampledPath W p M) : ℝ :=
  ∏ j, (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      ∑ i, (a j i : ℂ) • sampledSource b E W ⌊(W : ℝ) * T⌋₊ (q i) M (fun l => x.2.1 (i, l))
        (fun l => x.2.2 (i, l)) x.1).det⁻¹).re

theorem sampledPhysTransform_eq (b E T : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) (M W : ℕ) :
    sampledPhysTransform b E T q a M W =
      ∫ x, physIntegrand b E T q a M W x ∂sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M := rfl

/-- The closing defect `D = C(e^{iθ}) - 1` of the sample `y = (x, θ)`. -/
abbrev closeDefect (b E s T h : ℝ) {p M : ℕ} (y : SampledPath W p M × ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  physClosingMap b E s T h W y.1.1 (phase y.2) - 1

/-- The leaked mass of one sampled injection, `Re Tr(DD* κ_i u_{il}u_{il}*)`. -/
def leakTerm (b E s T h : ℝ) {p : ℕ} (q : Fin p → ℝ → ℝ) (M W : ℕ) (il : Fin p × Fin M)
    (y : SampledPath W p M × ℝ) : ℝ :=
  (closeDefect b E s T h y * (closeDefect b E s T h y)ᴴ *
    rankOne (boundaryToInterior b E W ⌊(W : ℝ) * T⌋₊ y.1.1)
      (gridMass W ⌊(W : ℝ) * T⌋₊ (q il.1) / (M * W)) (y.1.2.1 il, y.1.2.2 il)).trace.re

/-- **The pointwise closing error**:
`|phys(x) - closed(x, θ)| ≤ Σ_j Σ_{il} √a_{ji} (leakTerm_{il})^{1/2}`. -/
theorem abs_integrand_sub_le (b E s T h : ℝ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (M W : ℕ)
    (y : SampledPath W p M × ℝ) :
    |physIntegrand b E T q a M W y.1 - closedIntegrand b E s T h q a M W y| ≤
      ∑ j, ∑ il : Fin p × Fin M,
        Real.sqrt (a j il.1) * Real.sqrt (leakTerm b E s T h q M W il y) := by
  set n := ⌊(W : ℝ) * T⌋₊
  set C := physClosingMap b E s T h W y.1.1 (phase y.2)
  have hc := sampCoef_nonneg W n hq ha M
  have hpsd : ∀ j, (rkSum Finset.univ (sampCoef W n q a M j) (sampVec b E n y.1)).PosSemidef :=
    fun j => rkSum_psd _ (hc j) _
  rw [closedIntegrand_eq]
  simp only [physIntegrand, sourceComb_eq, conj_rkSum]
  change |∏ j, invDet (rkSum Finset.univ (sampCoef W n q a M j) (sampVec b E n y.1)) -
      ∏ j, invDet (rkSum Finset.univ (sampCoef W n q a M j) fun k => Cᴴ *ᵥ sampVec b E n y.1 k)| ≤ _
  refine (abs_prod_sub_prod_le _ (fun j => ⟨(invDet_mem (hpsd j)).1.le, (invDet_mem (hpsd j)).2⟩)
    fun j => ⟨(invDet_mem (rkSum_psd _ (hc j) _)).1.le, (invDet_mem (rkSum_psd _ (hc j) _)).2⟩).trans
    (Finset.sum_le_sum fun j _ => ?_)
  have h := abs_invDet_sum_sub_le Finset.univ (hc j) (sampVec b E n y.1)
    (fun k => Cᴴ *ᵥ sampVec b E n y.1 k) 0 PosSemidef.zero
  simp only [zero_add] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun il _ => ?_))
  have hκ : 0 ≤ gridMass W n (q il.1) / (M * W) :=
    div_nonneg (gridMass_nonneg W n (hq il.1)) (by positivity)
  rw [l2_sub_conj, sampCoef, Real.sqrt_mul (ha j il.1), mul_assoc, sqrt_mul_l2 _ hκ]
  rfl

end BlockBand.SourceProcess.ClosingLeak

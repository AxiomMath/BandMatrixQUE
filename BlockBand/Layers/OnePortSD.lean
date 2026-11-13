module

public import BlockBand.Layers.OnePortSDDouble
public import BlockBand.Layers.OnePortMeanInputs
public import BlockBand.Layers.OnePortMeanAlgebra

/-!
# The passive one-port Schwinger–Dyson system (`OppPassiveMeanEquations`)

The last input of `OnePortPassiveMeanContract`: the mean equations, the bottom-source trace
equations and the first form of the passive mean identity, with the passive-bounds lemma.

Main result: `oppPassiveMeanEquations_holds (hcount) (hgrad) : OppPassiveMeanEquations`.

## Proof

1. **Coordinates.** The fresh layer law is the image of a real Gaussian vector
   (`tfl_layerLaw_eq_map`); `N(x) = 𝒢(x)⁻¹ = C₀ + Λ(x)` is affine with Hermitian `Λ(x)`.
2. **Doubling** (`OnePortSDDouble`): `𝒩 = [[N, -ηP], [0, -N*]]` has `Im 𝒩 ⪰ 0` for passive `X`,
   `𝒩⁻¹ = [[𝒢, -ηF], [0, -𝒢*]]`, `F = 𝒢P_port𝒢*`. The generic first-order identity
   (`core_limit_identity`) for `𝒩` gives, in its `(1,1)` and `(1,2)` blocks, the first-order
   identity `C₀E𝒢 - E[S(𝒢)𝒢] = 1` and the second-order identity
   `C₀EF - E[S(𝒢)F + S(F)𝒢*] = P E𝒢*` (`osd_SD`, blocks `osd_blocks`), `S(G) = diag(σ_A(G), σ_B(G))`,
   `σ_A = c g₁ + b g₂`, `σ_B = b g₁` (`osd_meqS_eq`).
3. **Covariances** (`osd_cov_layer`): every error term is a block of a one-letter covariance of
   `𝒩⁻¹`: `Cov(σ_A(𝒢), 𝒢₁₁)`, `Cov(σ_B(𝒢), 𝒢₂₂)`, `Cov(σ_A(𝒢), F₁₁)`, `Cov(σ_A(F), (𝒢*)₁₁)`,
   `Cov(σ_B(𝒢), F₂₂)`, `Cov(σ_B(F), (𝒢*)₂₂)`, and the weighted `Cov(σ_A(𝒢), F₁₁K*)`,
   `Cov(σ_A(F), (𝒢*)₁₁K*)` — the words `𝒢, 𝒢*, F = 𝒢P𝒢*, 𝒢*K* = (K𝒢)*` only (never `𝒢₁₁K*`).
   Each is `≤ C/W²` uniformly in passive `X` (`osd_cov_pkg`).
4. **Algebra** (deterministic): the five conclusions (numbered 1–5) of
   `OppPassiveMeanEquations`, with `‖Ḡ₁₁‖, |ḡ₂|, t₁, t₂ ≤ C₀` from the majorant `H` and `T̄`
   invertible with `‖M̄‖ ≤ 2C₀` once conclusion 1 holds with `ρ ≤ 1/2`; `KM̄ = 1 + (z + E + σ̄_A)M̄` is bounded.
5. **Transfer** to the layer law and to `Fin W` (reindexing by `x ↦ (0, x)`).

`GaussianLpGradient` is not needed (the covariances are bounded by the Ornstein–Uhlenbeck
identity, not by fluctuations); it is kept in the signature.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.LayersOnePort
open BlockBand.Internal.Contracts.Inputs (gaussianProduct ConditionalBlockGUECount GaussianLpGradient)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Entrywise expectations
-/

section Expect

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem osd_mE_fromBlocks {n m : Type*} (a : Ω → Matrix n n ℂ) (b : Ω → Matrix n m ℂ)
    (c : Ω → Matrix m n ℂ) (d : Ω → Matrix m m ℂ) :
    matrixExpect μ (fun x => fromBlocks (a x) (b x) (c x) (d x)) =
      fromBlocks (matrixExpect μ a) (matrixExpect μ b) (matrixExpect μ c) (matrixExpect μ d) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem osd_mE_smul {n m : Type*} (r : ℂ) (U : Ω → Matrix n m ℂ) :
    matrixExpect μ (fun x => r • U x) = r • matrixExpect μ U := by
  ext i j
  simp only [matrixExpect, of_apply, Matrix.smul_apply, smul_eq_mul, integral_const_mul]

theorem osd_mE_neg {n m : Type*} (U : Ω → Matrix n m ℂ) :
    matrixExpect μ (fun x => -U x) = -matrixExpect μ U := by
  ext i j
  simp only [matrixExpect, of_apply, Matrix.neg_apply, integral_neg]

theorem osd_mE_zero {n m : Type*} : matrixExpect μ (fun _ => (0 : Matrix n m ℂ)) = 0 := by
  ext i j
  simp [matrixExpect]

theorem osd_mE_add {n m : Type*} {U V : Ω → Matrix n m ℂ}
    (hU : ∀ i j, Integrable (fun x => U x i j) μ) (hV : ∀ i j, Integrable (fun x => V x i j) μ) :
    matrixExpect μ (fun x => U x + V x) = matrixExpect μ U + matrixExpect μ V := by
  ext i j
  simp only [matrixExpect, of_apply, Matrix.add_apply]
  exact integral_add (hU i j) (hV i j)

theorem osd_mE_conjTranspose {n : Type*} (U : Ω → Matrix n n ℂ) :
    matrixExpect μ (fun x => (U x)ᴴ) = (matrixExpect μ U)ᴴ := by
  ext i j
  simp only [matrixExpect, of_apply, conjTranspose_apply]
  exact integral_conj

theorem osd_mE_mul_left {n m : Type*} [Fintype n] (D : Matrix m n ℂ) {U : Ω → Matrix n n ℂ}
    (hU : ∀ i j, Integrable (fun x => U x i j) μ) :
    matrixExpect μ (fun x => D * U x) = D * matrixExpect μ U := by
  ext i j
  simp only [matrixExpect, of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ fun k _ => (hU k j).const_mul _]
  exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _

theorem osd_mE_mul_right {n m : Type*} [Fintype n] (D : Matrix n m ℂ) {U : Ω → Matrix n n ℂ}
    (hU : ∀ i j, Integrable (fun x => U x i j) μ) :
    matrixExpect μ (fun x => U x * D) = matrixExpect μ U * D := by
  ext i j
  simp only [matrixExpect, of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ fun k _ => (hU i k).mul_const _]
  exact Finset.sum_congr rfl fun k _ => integral_mul_const _ _

theorem osd_integral_trace {n : Type*} [Fintype n] (w : ℂ) (D : Matrix n n ℂ)
    {U : Ω → Matrix n n ℂ} (hU : ∀ i j, Integrable (fun x => U x i j) μ) :
    ∫ x, w * (D * U x).trace ∂μ = w * (D * matrixExpect μ U).trace := by
  rw [integral_const_mul]
  congr 1
  have e : ∀ x, (D * U x).trace = ∑ i, ∑ k, D i k * U x k i := fun x => by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have e' : (D * matrixExpect μ U).trace = ∑ i, ∑ k, D i k * ∫ x, U x k i ∂μ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, matrixExpect, of_apply]
  rw [e']
  calc ∫ x, (D * U x).trace ∂μ = ∫ x, ∑ i, ∑ k, D i k * U x k i ∂μ :=
        integral_congr_ae (ae_of_all _ e)
    _ = ∑ i, ∫ x, ∑ k, D i k * U x k i ∂μ :=
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => (hU k i).const_mul _
    _ = ∑ i, ∑ k, ∫ x, D i k * U x k i ∂μ :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun k _ => (hU k i).const_mul _
    _ = ∑ i, ∑ k, D i k * ∫ x, U x k i ∂μ :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => integral_const_mul _ _

/-- `E[fU] = E[f] E[U] + Cov(f, U)` (definition of `meqCov`). -/
theorem osd_mE_smul_eq {n : Type*} (f : Ω → ℂ) (U : Ω → Matrix n n ℂ) :
    matrixExpect μ (fun x => f x • U x) = (∫ x, f x ∂μ) • matrixExpect μ U + meqCov μ f U := by
  rw [meqCov]; abel

theorem osd_cov_submatrix {n k : Type*} (f : Ω → ℂ) (U : Ω → Matrix n n ℂ) (r c : k → n) :
    meqCov μ f (fun x => (U x).submatrix r c) = (meqCov μ f U).submatrix r c := by
  ext i j
  simp [meqCov, matrixExpect]

theorem osd_cov_mul_right {n : Type*} [Fintype n] (f : Ω → ℂ) {U : Ω → Matrix n n ℂ}
    (D : Matrix n n ℂ) (hU : ∀ i j, Integrable (fun x => U x i j) μ)
    (hfU : ∀ i j, Integrable (fun x => f x * U x i j) μ) :
    meqCov μ f (fun x => U x * D) = meqCov μ f U * D := by
  have h1 : matrixExpect μ (fun x => f x • (U x * D)) = matrixExpect μ (fun x => f x • U x) * D := by
    rw [← osd_mE_mul_right D (U := fun x => f x • U x) (fun i j => by simpa using hfU i j)]
    congr 1
    funext x
    rw [Matrix.smul_mul]
  rw [meqCov, meqCov, h1, osd_mE_mul_right D hU, Matrix.sub_mul, Matrix.smul_mul]

end Expect

/-!
## 2. The self-energy of the one-port layer
-/

section Shift

variable {W : ℕ}

/-- `σ_A(G) = c g₁(G) + b g₂(G)`, `c = 1 - 2b` (the physical-block self-energy coefficient). -/
def osdSA (b : ℝ) (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) : ℂ :=
  (1 - 2 * (b : ℂ)) * physBlockTrace G 0 + (b : ℂ) * portBlockTrace G 0

/-- `σ_B(G) = b g₁(G)` (the port self-energy coefficient). -/
def osdSB (b : ℝ) (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) : ℂ :=
  (b : ℂ) * physBlockTrace G 0

/-- `D₁ = diag(c, b)`, so that `σ_A(G) = W⁻¹ Tr(D₁G)`. -/
def osdD1 (W : ℕ) (b : ℝ) : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks ((1 - 2 * (b : ℂ)) • 1) 0 0 ((b : ℂ) • 1)

/-- `D₂ = diag(b, 0)`, so that `σ_B(G) = W⁻¹ Tr(D₂G)`. -/
def osdD2 (W : ℕ) (b : ℝ) : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks ((b : ℂ) • 1) 0 0 0

theorem osd_phys_eq (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    physBlockTrace G 0 = (W : ℂ)⁻¹ * G.toBlocks₁₁.trace := by
  unfold physBlockTrace
  congr 1
  simp only [Matrix.trace, Matrix.diag, toBlocks₁₁, of_apply, Fintype.sum_prod_type,
    Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem osd_port_eq (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    portBlockTrace G 0 = (W : ℂ)⁻¹ * G.toBlocks₂₂.trace := by
  unfold portBlockTrace
  congr 1
  simp only [Matrix.trace, Matrix.diag, toBlocks₂₂, of_apply, Fintype.sum_prod_type,
    Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem osd_SA_eq (b : ℝ)
    (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    osdSA b G = (W : ℂ)⁻¹ * (osdD1 W b * G).trace := by
  conv_rhs => rw [← fromBlocks_toBlocks G]
  rw [osdSA, osd_phys_eq, osd_port_eq, osdD1, fromBlocks_multiply, wl_trace_fromBlocks]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add, trace_smul,
    smul_eq_mul]
  ring

theorem osd_SB_eq (b : ℝ)
    (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    osdSB b G = (W : ℂ)⁻¹ * (osdD2 W b * G).trace := by
  conv_rhs => rw [← fromBlocks_toBlocks G]
  rw [osdSB, osd_phys_eq, osdD2, fromBlocks_multiply, wl_trace_fromBlocks]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.zero_mul, add_zero, trace_smul,
    smul_eq_mul, trace_zero]
  ring

theorem osd_norm_D1_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) : ‖osdD1 W b‖ ≤ 1 := by
  refine (osd_norm_fromBlocks_le _ _ _ _).trans ?_
  simp only [norm_zero]
  rw [norm_smul, norm_smul]
  have h1 := lct_norm_one_le (n := PhysSite W .oneBlockOnePort)
  have h2 := lct_norm_one_le (n := PortSite W .oneBlockOnePort)
  have e1 : ‖(1 - 2 * (b : ℂ))‖ = 1 - 2 * b := by
    rw [show (1 - 2 * (b : ℂ)) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have e2 : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0]
  rw [e1, e2]
  nlinarith [norm_nonneg (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ),
    norm_nonneg (1 : Matrix (PortSite W .oneBlockOnePort) (PortSite W .oneBlockOnePort) ℂ)]

theorem osd_norm_D2_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) : ‖osdD2 W b‖ ≤ 1 := by
  refine (osd_norm_fromBlocks_le _ _ _ _).trans ?_
  simp only [norm_zero]
  rw [norm_smul]
  have h1 := lct_norm_one_le (n := PhysSite W .oneBlockOnePort)
  have e2 : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0]
  rw [e2]
  nlinarith [norm_nonneg (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ)]

/-- **The layer contraction of the one-port layer**: `S(G) = diag(σ_A(G), σ_B(G))`. -/
theorem osd_meqS_eq (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    meqS W b .oneBlockOnePort G = fromBlocks (osdSA b G • 1) 0 0 (osdSB b G • 1) := by
  rw [meqS_eq hW, meq_coefA hW hb1, meq_coefB hW hb0]
  ext p q
  rcases p with ⟨i, α⟩ | ⟨i, α⟩ <;> rcases q with ⟨j, β⟩ | ⟨j, β⟩ <;>
    obtain rfl : i = 0 := Subsingleton.elim _ _ <;> obtain rfl : j = 0 := Subsingleton.elim _ _ <;>
    simp [meqShift, diagonal, osdSA, osdSB, meqInc, LayerShape.incident, Matrix.one_apply]

/-- `diag(α, β) M = [[αM₁₁, αM₁₂], [βM₂₁, βM₂₂]]`. -/
theorem osd_shift_mul (α β : ℂ)
    (M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    (fromBlocks (α • 1) 0 0 (β • 1) : Matrix (LayerSite W .oneBlockOnePort)
        (LayerSite W .oneBlockOnePort) ℂ) * M =
      fromBlocks (α • M.toBlocks₁₁) (α • M.toBlocks₁₂) (β • M.toBlocks₂₁) (β • M.toBlocks₂₂) := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [fromBlocks_multiply]
  simp

theorem osd_meqS_smul (b : ℝ) (r : ℂ)
    (M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    meqS W b .oneBlockOnePort (r • M) = r • meqS W b .oneBlockOnePort M := by
  unfold meqS
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]

theorem osd_meqS_neg (b : ℝ)
    (M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    meqS W b .oneBlockOnePort (-M) = -meqS W b .oneBlockOnePort M := by
  rw [← neg_one_smul ℂ M, osd_meqS_smul, neg_one_smul]

theorem osd_meqS_zero (b : ℝ) :
    meqS W b .oneBlockOnePort (0 : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ) = 0 := by
  unfold meqS
  simp

end Shift

/-!
## 3. The standing hypotheses and the doubled words
-/

section Words

variable {W : ℕ}

/-- The standing hypotheses at fixed `W, b, E, X` (all produced by `osd_setup` and `wl_bulk`). -/
structure OsdHyp (W : ℕ) (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Prop where
  hW : 0 < W
  hb0 : 0 < b
  hb1 : b < 1 / 2
  hX : IsPassiveInput X
  hE : |E| ≤ 2
  hz : ‖boundaryZ b E‖ ≤ 3
  heta : 0 < (boundaryZ b E).im
  hinv : ∀ᵐ x ∂gaussianProduct (tflVar W b .oneBlockOnePort), IsUnit (osdN b E X x).det
  hH4 : Integrable (fun x => osdH b E X x ^ 4) (gaussianProduct (tflVar W b .oneBlockOnePort))

/-- A trace–matrix covariance with integrable data and norm at most `ρ`. -/
def OsdCovOK {Ω k : Type*} [MeasurableSpace Ω] [Fintype k] [DecidableEq k] (μ : Measure Ω)
    (f : Ω → ℂ) (U : Ω → Matrix k k ℂ) (ρ : ℝ) : Prop :=
  Integrable f μ ∧ (∀ i j, Integrable (fun x => U x i j) μ) ∧
    (∀ i j, Integrable (fun x => f x * U x i j) μ) ∧ ‖meqCov μ f U‖ ≤ ρ

/-- `𝒫_A(D) = diag(D, 0)`: `Tr(𝒫_A(D) 𝒩⁻¹) = Tr(D𝒢)`. -/
def osdPA (D : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks D 0 0 0

/-- `𝒫_B(D) = [[0, 0], [-η⁻¹D, 0]]`: `Tr(𝒫_B(D) 𝒩⁻¹) = Tr(DF)`. -/
def osdPB (η : ℝ) (D : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks 0 0 (-(η : ℂ)⁻¹ • D) 0

/-- `𝒬₀ = diag(-η⁻¹, -1)`: `𝒬₀ 𝒩⁻¹ diag(0, Z) = [[0, FZ], [0, 𝒢*Z]]`. -/
def osdQ0 (W : ℕ) (η : ℝ) :
    Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks (-(η : ℂ)⁻¹ • 1) 0 0 (-1)

theorem osd_trA (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (D : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ)
    (x : TflCoord W .oneBlockOnePort → ℝ) :
    (osdPA D * osdB b E X x).trace = (D * osdG b E X x).trace := by
  rw [osdPA, osdB, fromBlocks_multiply, wl_trace_fromBlocks]
  simp

theorem osd_trB {b E : ℝ} (hη : (boundaryZ b E).im ≠ 0) (X : Matrix (Fin W) (Fin W) ℂ)
    (D : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ)
    (x : TflCoord W .oneBlockOnePort → ℝ) :
    (osdPB (boundaryZ b E).im D * osdB b E X x).trace = (D * osdF b E X x).trace := by
  have hc : ((boundaryZ b E).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη
  rw [osdPB, osdB, fromBlocks_multiply, wl_trace_fromBlocks]
  simp [hc]

theorem osd_UI (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    1 * osdB b E X x * fromBlocks 1 0 0 0 = fromBlocks (osdG b E X x) 0 0 0 := by
  rw [Matrix.one_mul, osdB, fromBlocks_multiply]
  simp

theorem osd_UII {b E : ℝ} (hη : (boundaryZ b E).im ≠ 0) (X : Matrix (Fin W) (Fin W) ℂ)
    (Z : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ)
    (x : TflCoord W .oneBlockOnePort → ℝ) :
    osdQ0 W (boundaryZ b E).im * osdB b E X x * fromBlocks 0 0 0 Z =
      fromBlocks 0 (osdF b E X x * Z) 0 ((osdG b E X x)ᴴ * Z) := by
  have hc : ((boundaryZ b E).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη
  rw [osdQ0, osdB, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.smul_mul,
    Matrix.one_mul, neg_neg, neg_zero, neg_smul, smul_smul, neg_mul, mul_neg, inv_mul_cancel₀ hc,
    one_smul]

theorem osd_norm_PA_le (D : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ‖osdPA D‖ ≤ ‖D‖ := by
  refine (osd_norm_fromBlocks_le _ _ _ _).trans ?_
  simp

theorem osd_norm_PB_le {η : ℝ} (hη : 0 < η)
    (D : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ‖osdPB η D‖ ≤ η⁻¹ * ‖D‖ := by
  refine (osd_norm_fromBlocks_le _ _ _ _).trans ?_
  simp only [norm_zero, zero_add, add_zero, norm_smul, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hη.le, le_refl]

theorem osd_norm_Q0_le {η : ℝ} (hη : 0 < η) : ‖osdQ0 W η‖ ≤ η⁻¹ + 1 := by
  refine (osd_norm_fromBlocks_le _ _ _ _).trans ?_
  simp only [norm_zero, add_zero, norm_smul, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hη.le]
  have h1 := lct_norm_one_le (n := LayerSite W .oneBlockOnePort)
  have : η⁻¹ * ‖(1 : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ)‖ ≤
      η⁻¹ := by
    have := inv_pos.mpr hη
    nlinarith [norm_nonneg (1 : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ)]
  linarith

theorem osd_norm_fb1_le :
    ‖(fromBlocks 1 0 0 0 : Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ)‖ ≤ 1 := by
  refine (osd_norm_fromBlocks_le _ _ _ _).trans ?_
  simp only [norm_zero, add_zero]
  exact lct_norm_one_le

theorem osd_norm_fb2_le :
    ‖(fromBlocks 0 0 0 1 : Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ)‖ ≤ 1 := by
  refine (osd_norm_fromBlocks_le _ _ _ _).trans ?_
  simp only [norm_zero, zero_add]
  exact lct_norm_one_le

/-- **Layer-level covariance from the package**: a block (submatrix) of a one-letter covariance
of `𝒩⁻¹`. -/
theorem osd_cov_layer {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (h : OsdHyp W b E X)
    (P Q Wt : Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ)
    (hWt : ‖Wt‖ ≤ 1 ∨ Wt = osdWK b E X) {K : ℝ} (hP : ‖P‖ ≤ K) (hQ : ‖Q‖ ≤ K)
    {k : Type} [Fintype k] [DecidableEq k]
    (r c : k → LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
    (hr : Function.Injective r) (hc : Function.Injective c)
    (f : (TflCoord W .oneBlockOnePort → ℝ) → ℂ)
    (U : (TflCoord W .oneBlockOnePort → ℝ) → Matrix k k ℂ)
    (hf : ∀ x, (W : ℂ)⁻¹ * (P * osdB b E X x).trace = f x)
    (hU : ∀ x, (Q * osdB b E X x * Wt).submatrix r c = U x) :
    OsdCovOK (gaussianProduct (tflVar W b .oneBlockOnePort)) f U
      (40 / (W : ℝ) ^ 2 * K ^ 2 *
        ∫ x, osdH b E X x ^ 4 ∂gaussianProduct (tflVar W b .oneBlockOnePort)) := by
  obtain ⟨h1, h2, h3, h4⟩ := osd_cov_pkg h.hW h.hb0 h.hb1 h.hX h.hE h.hz h.heta.le h.hinv h.hH4
    P Q Wt hWt
  have eU : (fun x => (Q * osdB b E X x * Wt).submatrix r c) = U := funext hU
  simp only [hf] at h1 h3 h4
  refine ⟨h1, fun i j => ?_, fun i j => ?_, ?_⟩
  · rw [← eU]; exact h2 (r i) (c j)
  · rw [← eU]; exact h3 (r i) (c j)
  · rw [← eU, osd_cov_submatrix]
    refine (wl_norm_submatrix_le _ hr hc).trans (h4.trans ?_)
    have hI : 0 ≤ ∫ x, osdH b E X x ^ 4 ∂gaussianProduct (tflVar W b .oneBlockOnePort) :=
      integral_nonneg fun x => by unfold osdH; positivity
    have hK : 0 ≤ K := (norm_nonneg _).trans hP
    have hPQ : ‖P‖ * ‖Q‖ ≤ K ^ 2 := by
      rw [sq]; exact mul_le_mul hP hQ (norm_nonneg _) hK
    have hW0 : (0 : ℝ) ≤ 40 / (W : ℝ) ^ 2 := by positivity
    calc 40 / (W : ℝ) ^ 2 * ‖P‖ * ‖Q‖ * ∫ x, osdH b E X x ^ 4 ∂gaussianProduct (tflVar W b _)
        = 40 / (W : ℝ) ^ 2 * (‖P‖ * ‖Q‖) * ∫ x, osdH b E X x ^ 4 ∂gaussianProduct
            (tflVar W b _) := by ring
      _ ≤ 40 / (W : ℝ) ^ 2 * K ^ 2 * ∫ x, osdH b E X x ^ 4 ∂gaussianProduct (tflVar W b _) := by
          gcongr

end Words

/-!
## 4. The eight error covariances of the passive one-port layer
-/

section Covs

variable {W : ℕ} {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}

/-- The covariance scale `ρ = (40/W²) (1 + η⁻¹)² E H⁴`. -/
def osdRho (W : ℕ) (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  40 / (W : ℝ) ^ 2 * (1 + ((boundaryZ b E).im)⁻¹) ^ 2 *
    ∫ x, osdH b E X x ^ 4 ∂gaussianProduct (tflVar W b .oneBlockOnePort)

/-- The physical weight `K̃ = z - X̃` on the physical sites. -/
abbrev osdKt (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ :=
  boundaryZ b E • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) -
    onePortLift X

theorem OsdHyp.K_ge (h : OsdHyp W b E X) : 1 ≤ 1 + ((boundaryZ b E).im)⁻¹ := by
  have := inv_pos.mpr h.heta; linarith

theorem OsdHyp.normPA (h : OsdHyp W b E X)
    {D : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ} (hD : ‖D‖ ≤ 1) :
    ‖osdPA D‖ ≤ 1 + ((boundaryZ b E).im)⁻¹ :=
  (osd_norm_PA_le D).trans (hD.trans h.K_ge)

theorem OsdHyp.normPB (h : OsdHyp W b E X)
    {D : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ} (hD : ‖D‖ ≤ 1) :
    ‖osdPB (boundaryZ b E).im D‖ ≤ 1 + ((boundaryZ b E).im)⁻¹ := by
  refine (osd_norm_PB_le h.heta D).trans ?_
  have := inv_pos.mpr h.heta
  nlinarith [norm_nonneg D]

theorem OsdHyp.normQ1 (h : OsdHyp W b E X) :
    ‖(1 : Matrix (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort ⊕ LayerSite W .oneBlockOnePort) ℂ)‖ ≤
      1 + ((boundaryZ b E).im)⁻¹ :=
  lct_norm_one_le.trans h.K_ge

theorem OsdHyp.normQ0 (h : OsdHyp W b E X) :
    ‖osdQ0 W (boundaryZ b E).im‖ ≤ 1 + ((boundaryZ b E).im)⁻¹ := by
  have := osd_norm_Q0_le (W := W) h.heta; linarith

theorem OsdHyp.D1 (h : OsdHyp W b E X) : ‖osdD1 W b‖ ≤ 1 := osd_norm_D1_le h.hb0.le h.hb1.le
theorem OsdHyp.D2 (h : OsdHyp W b E X) : ‖osdD2 W b‖ ≤ 1 := osd_norm_D2_le h.hb0.le h.hb1.le

theorem osd_fA1 (x : TflCoord W .oneBlockOnePort → ℝ) :
    (W : ℂ)⁻¹ * (osdPA (osdD1 W b) * osdB b E X x).trace = osdSA b (osdG b E X x) := by
  rw [osd_trA, osd_SA_eq]

theorem osd_fA2 (x : TflCoord W .oneBlockOnePort → ℝ) :
    (W : ℂ)⁻¹ * (osdPA (osdD2 W b) * osdB b E X x).trace = osdSB b (osdG b E X x) := by
  rw [osd_trA, osd_SB_eq]

theorem OsdHyp.fB1 (h : OsdHyp W b E X) (x : TflCoord W .oneBlockOnePort → ℝ) :
    (W : ℂ)⁻¹ * (osdPB (boundaryZ b E).im (osdD1 W b) * osdB b E X x).trace =
      osdSA b (osdF b E X x) := by
  rw [osd_trB h.heta.ne', osd_SA_eq]

theorem OsdHyp.fB2 (h : OsdHyp W b E X) (x : TflCoord W .oneBlockOnePort → ℝ) :
    (W : ℂ)⁻¹ * (osdPB (boundaryZ b E).im (osdD2 W b) * osdB b E X x).trace =
      osdSB b (osdF b E X x) := by
  rw [osd_trB h.heta.ne', osd_SB_eq]

variable (h : OsdHyp W b E X)
include h

theorem osd_cov1 : OsdCovOK (gaussianProduct (tflVar W b .oneBlockOnePort))
    (fun x => osdSA b (osdG b E X x)) (fun x => (osdG b E X x).toBlocks₁₁) (osdRho W b E X) :=
  osd_cov_layer h _ 1 (fromBlocks 1 0 0 0) (Or.inl osd_norm_fb1_le) (h.normPA h.D1) h.normQ1
    (fun p => Sum.inl (Sum.inl p)) (fun p => Sum.inl (Sum.inl p))
    (Sum.inl_injective.comp Sum.inl_injective) (Sum.inl_injective.comp Sum.inl_injective) _ _
    osd_fA1 fun x => by rw [osd_UI]; rfl

theorem osd_cov2 : OsdCovOK (gaussianProduct (tflVar W b .oneBlockOnePort))
    (fun x => osdSB b (osdG b E X x)) (fun x => (osdG b E X x).toBlocks₂₂) (osdRho W b E X) :=
  osd_cov_layer h _ 1 (fromBlocks 1 0 0 0) (Or.inl osd_norm_fb1_le) (h.normPA h.D2) h.normQ1
    (fun p => Sum.inl (Sum.inr p)) (fun p => Sum.inl (Sum.inr p))
    (Sum.inl_injective.comp Sum.inr_injective) (Sum.inl_injective.comp Sum.inr_injective) _ _
    osd_fA2 fun x => by rw [osd_UI]; rfl

theorem osd_cov3 : OsdCovOK (gaussianProduct (tflVar W b .oneBlockOnePort))
    (fun x => osdSA b (osdG b E X x)) (fun x => (osdF b E X x).toBlocks₁₁) (osdRho W b E X) :=
  osd_cov_layer h _ _ (fromBlocks 0 0 0 1) (Or.inl osd_norm_fb2_le) (h.normPA h.D1) h.normQ0
    (fun p => Sum.inl (Sum.inl p)) (fun p => Sum.inr (Sum.inl p))
    (Sum.inl_injective.comp Sum.inl_injective) (Sum.inr_injective.comp Sum.inl_injective) _ _
    osd_fA1 fun x => by rw [osd_UII h.heta.ne']; simp only [Matrix.mul_one]; rfl

theorem osd_cov4 : OsdCovOK (gaussianProduct (tflVar W b .oneBlockOnePort))
    (fun x => osdSA b (osdF b E X x)) (fun x => ((osdG b E X x)ᴴ).toBlocks₁₁) (osdRho W b E X) :=
  osd_cov_layer h _ _ (fromBlocks 0 0 0 1) (Or.inl osd_norm_fb2_le) (h.normPB h.D1) h.normQ0
    (fun p => Sum.inr (Sum.inl p)) (fun p => Sum.inr (Sum.inl p))
    (Sum.inr_injective.comp Sum.inl_injective) (Sum.inr_injective.comp Sum.inl_injective) _ _
    h.fB1 fun x => by rw [osd_UII h.heta.ne']; simp only [Matrix.mul_one]; rfl

theorem osd_cov5 : OsdCovOK (gaussianProduct (tflVar W b .oneBlockOnePort))
    (fun x => osdSB b (osdG b E X x)) (fun x => (osdF b E X x).toBlocks₂₂) (osdRho W b E X) :=
  osd_cov_layer h _ _ (fromBlocks 0 0 0 1) (Or.inl osd_norm_fb2_le) (h.normPA h.D2) h.normQ0
    (fun p => Sum.inl (Sum.inr p)) (fun p => Sum.inr (Sum.inr p))
    (Sum.inl_injective.comp Sum.inr_injective) (Sum.inr_injective.comp Sum.inr_injective) _ _
    osd_fA2 fun x => by rw [osd_UII h.heta.ne']; simp only [Matrix.mul_one]; rfl

theorem osd_cov6 : OsdCovOK (gaussianProduct (tflVar W b .oneBlockOnePort))
    (fun x => osdSB b (osdF b E X x)) (fun x => ((osdG b E X x)ᴴ).toBlocks₂₂) (osdRho W b E X) :=
  osd_cov_layer h _ _ (fromBlocks 0 0 0 1) (Or.inl osd_norm_fb2_le) (h.normPB h.D2) h.normQ0
    (fun p => Sum.inr (Sum.inr p)) (fun p => Sum.inr (Sum.inr p))
    (Sum.inr_injective.comp Sum.inr_injective) (Sum.inr_injective.comp Sum.inr_injective) _ _
    h.fB2 fun x => by rw [osd_UII h.heta.ne']; simp only [Matrix.mul_one]; rfl

theorem osd_cov7 : OsdCovOK (gaussianProduct (tflVar W b .oneBlockOnePort))
    (fun x => osdSA b (osdG b E X x))
    (fun x => (osdF b E X x).toBlocks₁₁ * (osdKt b E X)ᴴ) (osdRho W b E X) :=
  osd_cov_layer h _ _ (osdWK b E X) (Or.inr rfl) (h.normPA h.D1) h.normQ0
    (fun p => Sum.inl (Sum.inl p)) (fun p => Sum.inr (Sum.inl p))
    (Sum.inl_injective.comp Sum.inl_injective) (Sum.inr_injective.comp Sum.inl_injective) _ _
    osd_fA1 fun x => by
      rw [osdWK, osd_UII h.heta.ne', wlKh_conjTranspose, ← wl_mul_Kh_toBlocks11]; rfl

theorem osd_cov8 : OsdCovOK (gaussianProduct (tflVar W b .oneBlockOnePort))
    (fun x => osdSA b (osdF b E X x))
    (fun x => ((osdG b E X x)ᴴ).toBlocks₁₁ * (osdKt b E X)ᴴ) (osdRho W b E X) :=
  osd_cov_layer h _ _ (osdWK b E X) (Or.inr rfl) (h.normPB h.D1) h.normQ0
    (fun p => Sum.inr (Sum.inl p)) (fun p => Sum.inr (Sum.inl p))
    (Sum.inr_injective.comp Sum.inl_injective) (Sum.inr_injective.comp Sum.inl_injective) _ _
    h.fB1 fun x => by
      rw [osdWK, osd_UII h.heta.ne', wlKh_conjTranspose, ← wl_mul_Kh_toBlocks11]; rfl

theorem osd_int_G : ∀ i j, Integrable (fun x => osdG b E X x i j)
    (gaussianProduct (tflVar W b .oneBlockOnePort)) :=
  (osd_cov_layer h _ 1 (fromBlocks 1 0 0 0) (Or.inl osd_norm_fb1_le) (h.normPA h.D1) h.normQ1
    Sum.inl Sum.inl Sum.inl_injective Sum.inl_injective _ (fun x => osdG b E X x)
    osd_fA1 fun x => by rw [osd_UI]; rfl).2.1

theorem osd_int_F : ∀ i j, Integrable (fun x => osdF b E X x i j)
    (gaussianProduct (tflVar W b .oneBlockOnePort)) :=
  (osd_cov_layer h _ _ (fromBlocks 0 0 0 1) (Or.inl osd_norm_fb2_le) (h.normPA h.D1) h.normQ0
    Sum.inl Sum.inr Sum.inl_injective Sum.inr_injective _ (fun x => osdF b E X x)
    osd_fA1 fun x => by rw [osd_UII h.heta.ne']; simp only [Matrix.mul_one]; rfl).2.1

theorem osd_int_Gh : ∀ i j, Integrable (fun x => (osdG b E X x)ᴴ i j)
    (gaussianProduct (tflVar W b .oneBlockOnePort)) :=
  (osd_cov_layer h _ _ (fromBlocks 0 0 0 1) (Or.inl osd_norm_fb2_le) (h.normPA h.D1) h.normQ0
    Sum.inr Sum.inr Sum.inr_injective Sum.inr_injective _ (fun x => (osdG b E X x)ᴴ)
    osd_fA1 fun x => by rw [osd_UII h.heta.ne']; simp only [Matrix.mul_one]; rfl).2.1

end Covs

/-!
## 5. The first- and second-order Schwinger–Dyson identities and their blocks
-/

section System

variable {W : ℕ} {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}

theorem osd_fromBlocks_sub {n m : Type*} (A A' : Matrix n n ℂ) (B B' : Matrix n m ℂ)
    (C C' : Matrix m n ℂ) (D D' : Matrix m m ℂ) :
    fromBlocks A B C D - fromBlocks A' B' C' D' = fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem osd_diag_mul_11 {n m : Type*} [Fintype n] [Fintype m] (A : Matrix n n ℂ) (D : Matrix m m ℂ)
    (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : (fromBlocks A 0 0 D * M).toBlocks₁₁ = A * M.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [fromBlocks_multiply]
  simp

theorem osd_diag_mul_22 {n m : Type*} [Fintype n] [Fintype m] (A : Matrix n n ℂ) (D : Matrix m m ℂ)
    (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : (fromBlocks A 0 0 D * M).toBlocks₂₂ = D * M.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [fromBlocks_multiply]
  simp

theorem osd_toBlocks11_conjTranspose {n m : Type*} (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (Gᴴ).toBlocks₁₁ = (G.toBlocks₁₁)ᴴ := by
  ext x y; simp [toBlocks₁₁, conjTranspose_apply]

theorem osd_toBlocks22_conjTranspose {n m : Type*} (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (Gᴴ).toBlocks₂₂ = (G.toBlocks₂₂)ᴴ := by
  ext x y; simp [toBlocks₂₂, conjTranspose_apply]

/-- **The first- and second-order Schwinger–Dyson identities** of the passive one-port layer
(`(1,1)` and `(1,2)` blocks of `osd_identity`): `C₀Ḡ - E[S(𝒢)𝒢] = 1` and
`C₀F̄ - E[S(𝒢)F + S(F)𝒢*] = P E𝒢*`. -/
theorem osd_SD (h : OsdHyp W b E X) :
    tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X) *
        matrixExpect (gaussianProduct (tflVar W b .oneBlockOnePort)) (osdG b E X) -
      matrixExpect (gaussianProduct (tflVar W b .oneBlockOnePort))
        (fun x => meqS W b .oneBlockOnePort (osdG b E X x) * osdG b E X x) = 1 ∧
    tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X) *
        matrixExpect (gaussianProduct (tflVar W b .oneBlockOnePort)) (osdF b E X) -
      matrixExpect (gaussianProduct (tflVar W b .oneBlockOnePort))
        (fun x => meqS W b .oneBlockOnePort (osdG b E X x) * osdF b E X x +
          meqS W b .oneBlockOnePort (osdF b E X x) * (osdG b E X x)ᴴ) =
      onePortPortProj * matrixExpect (gaussianProduct (tflVar W b .oneBlockOnePort))
        (fun x => (osdG b E X x)ᴴ) := by
  set μ := gaussianProduct (tflVar W b .oneBlockOnePort) with hμ
  set η : ℝ := (boundaryZ b E).im with hηdef
  have hηc : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.heta.ne'
  have hid := osd_identity h.hX h.hE h.hz h.heta.le h.hinv h.hH4
  have e1 : matrixExpect μ (osdB b E X) =
      fromBlocks (matrixExpect μ (osdG b E X)) (-((η : ℂ) • matrixExpect μ (osdF b E X))) 0
        (-matrixExpect μ (fun x => (osdG b E X x)ᴴ)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [matrixExpect, osdB, integral_neg, integral_const_mul, hηdef]
  have e2 : ∀ x, coreS (tflVar W b .oneBlockOnePort) (osdL W b) (osdB b E X x) * osdB b E X x =
      fromBlocks (meqS W b .oneBlockOnePort (osdG b E X x) * osdG b E X x)
        (-((η : ℂ) • (meqS W b .oneBlockOnePort (osdG b E X x) * osdF b E X x +
          meqS W b .oneBlockOnePort (osdF b E X x) * (osdG b E X x)ᴴ))) 0
        (meqS W b .oneBlockOnePort ((osdG b E X x)ᴴ) * (osdG b E X x)ᴴ) := by
    intro x
    rw [osdB, osd_coreS_fromBlocks, fromBlocks_multiply, osd_meqS_neg, osd_meqS_smul,
      osd_meqS_zero, osd_meqS_neg]
    simp only [neg_neg, neg_zero, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, neg_add, hηdef,
      smul_zero]
  have e3 : matrixExpect μ (fun x => coreS (tflVar W b .oneBlockOnePort) (osdL W b) (osdB b E X x) *
      osdB b E X x) =
      fromBlocks (matrixExpect μ (fun x => meqS W b .oneBlockOnePort (osdG b E X x) * osdG b E X x))
        (-((η : ℂ) • matrixExpect μ (fun x => meqS W b .oneBlockOnePort (osdG b E X x) *
          osdF b E X x + meqS W b .oneBlockOnePort (osdF b E X x) * (osdG b E X x)ᴴ))) 0
        (matrixExpect μ (fun x => meqS W b .oneBlockOnePort ((osdG b E X x)ᴴ) *
          (osdG b E X x)ᴴ)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [matrixExpect, of_apply, e2, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
        integral_neg, integral_const_mul, Matrix.zero_apply, integral_zero]
  rw [e1, e3, osdC0, osdDbl, fromBlocks_multiply, osd_fromBlocks_sub, ← fromBlocks_one] at hid
  obtain ⟨h11, h12, -, -⟩ := Matrix.fromBlocks_inj.mp hid
  refine ⟨?_, ?_⟩
  · rw [← h11]; simp
  · have h12' : (η : ℂ) • (-(tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X) *
        matrixExpect μ (osdF b E X)) + onePortPortProj * matrixExpect μ (fun x => (osdG b E X x)ᴴ) +
        matrixExpect μ (fun x => meqS W b .oneBlockOnePort (osdG b E X x) * osdF b E X x +
          meqS W b .oneBlockOnePort (osdF b E X x) * (osdG b E X x)ᴴ)) = 0 := by
      rw [← h12]
      simp only [Matrix.mul_neg, Matrix.mul_smul, Matrix.neg_mul, Matrix.smul_mul,
        neg_neg, sub_neg_eq_add, smul_add, smul_neg, hηdef]
    have h0 := (smul_eq_zero.mp h12').resolve_left hηc
    rw [← sub_eq_zero]
    rw [← neg_eq_zero, ← h0]
    abel

end System

section Blocks

variable {W : ℕ} {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}

theorem osd_int_SA {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Ω → Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ}
    (hU : ∀ i j, Integrable (fun x => U x i j) μ) :
    ∫ x, osdSA b (U x) ∂μ = osdSA b (matrixExpect μ U) := by
  simp only [osd_SA_eq]
  exact osd_integral_trace _ _ hU

theorem osd_int_SB {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Ω → Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ}
    (hU : ∀ i j, Integrable (fun x => U x i j) μ) :
    ∫ x, osdSB b (U x) ∂μ = osdSB b (matrixExpect μ U) := by
  simp only [osd_SB_eq]
  exact osd_integral_trace _ _ hU

theorem osd_shift_11 (hW : 0 < W) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (G M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    (meqS W b .oneBlockOnePort G * M).toBlocks₁₁ = osdSA b G • M.toBlocks₁₁ := by
  rw [osd_meqS_eq hW hb0 hb1, osd_shift_mul, toBlocks_fromBlocks₁₁]

theorem osd_shift_22 (hW : 0 < W) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (G M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    (meqS W b .oneBlockOnePort G * M).toBlocks₂₂ = osdSB b G • M.toBlocks₂₂ := by
  rw [osd_meqS_eq hW hb0 hb1, osd_shift_mul, toBlocks_fromBlocks₂₂]

/-- **The block system** (the four scalar/matrix equations behind the five conclusions of
`OppPassiveMeanEquations`), with the eight error covariances of `osd_cov1`–`osd_cov6` as explicit remainders. -/
theorem osd_blocks (h : OsdHyp W b E X) :
    let μ := gaussianProduct (tflVar W b .oneBlockOnePort)
    let Gb := matrixExpect μ (osdG b E X)
    let Fb := matrixExpect μ (osdF b E X)
    (-((E : ℂ) • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ)) -
          onePortLift X) * Gb.toBlocks₁₁ -
        (osdSA b Gb • Gb.toBlocks₁₁ + meqCov μ (fun x => osdSA b (osdG b E X x))
          (fun x => (osdG b E X x).toBlocks₁₁)) = 1 ∧
      boundaryZ b E • Gb.toBlocks₂₂ -
        (osdSB b Gb • Gb.toBlocks₂₂ + meqCov μ (fun x => osdSB b (osdG b E X x))
          (fun x => (osdG b E X x).toBlocks₂₂)) = 1 ∧
      (-((E : ℂ) • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ)) -
          onePortLift X) * Fb.toBlocks₁₁ -
        ((osdSA b Gb • Fb.toBlocks₁₁ + meqCov μ (fun x => osdSA b (osdG b E X x))
          (fun x => (osdF b E X x).toBlocks₁₁)) +
         (osdSA b Fb • (Gb.toBlocks₁₁)ᴴ + meqCov μ (fun x => osdSA b (osdF b E X x))
          (fun x => ((osdG b E X x)ᴴ).toBlocks₁₁))) = 0 ∧
      boundaryZ b E • Fb.toBlocks₂₂ -
        ((osdSB b Gb • Fb.toBlocks₂₂ + meqCov μ (fun x => osdSB b (osdG b E X x))
          (fun x => (osdF b E X x).toBlocks₂₂)) +
         (osdSB b Fb • (Gb.toBlocks₂₂)ᴴ + meqCov μ (fun x => osdSB b (osdF b E X x))
          (fun x => ((osdG b E X x)ᴴ).toBlocks₂₂))) = (Gb.toBlocks₂₂)ᴴ := by
  intro μ Gb Fb
  obtain ⟨hI, hII⟩ := osd_SD h
  have hW := h.hW
  have hb0 := h.hb0.le
  have hb1 := h.hb1.le
  have iG := osd_int_G h
  have iF := osd_int_F h
  have mG : ∫ x, osdSA b (osdG b E X x) ∂μ = osdSA b Gb := osd_int_SA iG
  have mG' : ∫ x, osdSB b (osdG b E X x) ∂μ = osdSB b Gb := osd_int_SB iG
  have mF : ∫ x, osdSA b (osdF b E X x) ∂μ = osdSA b Fb := osd_int_SA iF
  have mF' : ∫ x, osdSB b (osdF b E X x) ∂μ = osdSB b Fb := osd_int_SB iF
  have hGh11 : matrixExpect μ (fun x => ((osdG b E X x)ᴴ).toBlocks₁₁) = (Gb.toBlocks₁₁)ᴴ := by
    change (matrixExpect μ (fun x => (osdG b E X x)ᴴ)).toBlocks₁₁ = _
    rw [osd_mE_conjTranspose, osd_toBlocks11_conjTranspose]
  have hGh22 : matrixExpect μ (fun x => ((osdG b E X x)ᴴ).toBlocks₂₂) = (Gb.toBlocks₂₂)ᴴ := by
    change (matrixExpect μ (fun x => (osdG b E X x)ᴴ)).toBlocks₂₂ = _
    rw [osd_mE_conjTranspose, osd_toBlocks22_conjTranspose]
  have hP11 : ∀ M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ,
      (onePortPortProj * M).toBlocks₁₁ = 0 := fun M => by
    rw [onePortPortProj, osd_diag_mul_11, Matrix.zero_mul]
  have hP22 : ∀ M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ,
      (onePortPortProj * M).toBlocks₂₂ = M.toBlocks₂₂ := fun M => by
    rw [onePortPortProj, osd_diag_mul_22, Matrix.one_mul]
  have hC11 : ∀ M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ,
      (tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X) * M).toBlocks₁₁ =
        (-((E : ℂ) • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ)) -
          onePortLift X) * M.toBlocks₁₁ := fun M => by
    rw [tflConst, osd_diag_mul_11]
  have hC22 : ∀ M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ,
      (tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X) * M).toBlocks₂₂ =
        boundaryZ b E • M.toBlocks₂₂ := fun M => by
    rw [tflConst, osd_diag_mul_22, Matrix.smul_mul, Matrix.one_mul]
  have hfU : ∀ {k : Type} [Fintype k] [DecidableEq k] {f : (TflCoord W .oneBlockOnePort → ℝ) → ℂ}
      {U : (TflCoord W .oneBlockOnePort → ℝ) → Matrix k k ℂ} {ρ : ℝ}, OsdCovOK μ f U ρ →
      ∀ i j, Integrable (fun x => (f x • U x) i j) μ := by
    intro k _ _ f U ρ hc i j
    simpa using hc.2.2.1 i j
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := congrArg Matrix.toBlocks₁₁ hI
    rw [← fromBlocks_one, toBlocks_fromBlocks₁₁] at e
    refine Eq.trans ?_ e
    change _ = (tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X) * Gb).toBlocks₁₁ -
      matrixExpect μ (fun x => (meqS W b .oneBlockOnePort (osdG b E X x) * osdG b E X x).toBlocks₁₁)
    rw [hC11]
    simp only [osd_shift_11 hW hb0 hb1]
    rw [osd_mE_smul_eq, mG]
    rfl
  · have e := congrArg Matrix.toBlocks₂₂ hI
    rw [← fromBlocks_one, toBlocks_fromBlocks₂₂] at e
    refine Eq.trans ?_ e
    change _ = (tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X) * Gb).toBlocks₂₂ -
      matrixExpect μ (fun x => (meqS W b .oneBlockOnePort (osdG b E X x) * osdG b E X x).toBlocks₂₂)
    rw [hC22]
    simp only [osd_shift_22 hW hb0 hb1]
    rw [osd_mE_smul_eq, mG']
    rfl
  · have e := congrArg Matrix.toBlocks₁₁ hII
    rw [hP11] at e
    refine Eq.trans ?_ e
    change _ = (tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X) * Fb).toBlocks₁₁ -
      matrixExpect μ (fun x => (meqS W b .oneBlockOnePort (osdG b E X x) * osdF b E X x).toBlocks₁₁ +
        (meqS W b .oneBlockOnePort (osdF b E X x) * (osdG b E X x)ᴴ).toBlocks₁₁)
    rw [hC11]
    simp only [osd_shift_11 hW hb0 hb1]
    rw [osd_mE_add (hfU (osd_cov3 h)) (hfU (osd_cov4 h)), osd_mE_smul_eq, osd_mE_smul_eq, mG, mF,
      hGh11]
    rfl
  · have e := congrArg Matrix.toBlocks₂₂ hII
    rw [hP22] at e
    refine Eq.trans ?_ (e.trans hGh22)
    change _ = (tflConst .oneBlockOnePort E (boundaryZ b E) (onePortLift X) * Fb).toBlocks₂₂ -
      matrixExpect μ (fun x => (meqS W b .oneBlockOnePort (osdG b E X x) * osdF b E X x).toBlocks₂₂ +
        (meqS W b .oneBlockOnePort (osdF b E X x) * (osdG b E X x)ᴴ).toBlocks₂₂)
    rw [hC22]
    simp only [osd_shift_22 hW hb0 hb1]
    rw [osd_mE_add (hfU (osd_cov5 h)) (hfU (osd_cov6 h)), osd_mE_smul_eq, osd_mE_smul_eq, mG', mF',
      hGh22]
    rfl

end Blocks

/-!
## 6. The deterministic algebra
-/

section Algebra

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem osd_ntr_le {W : ℕ} (hW : 0 < W) {k : Type} [Fintype k] [DecidableEq k]
    (hk : Fintype.card k = W) (N : Matrix k k ℂ) : ‖(W : ℂ)⁻¹ * N.trace‖ ≤ ‖N‖ := by
  have h := tfl_trace_le N
  rw [hk] at h
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖N.trace‖ ≤ (W : ℝ)⁻¹ * (W * ‖N‖) := by gcongr
    _ = ‖N‖ := by field_simp

theorem osd_ntr_one {W : ℕ} (hW : 0 < W) {k : Type} [Fintype k] [DecidableEq k]
    (hk : Fintype.card k = W) : (W : ℂ)⁻¹ * (1 : Matrix k k ℂ).trace = 1 := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  rw [trace_one, hk, inv_mul_cancel₀ hW']

/-- **The five conclusions of `OppPassiveMeanEquations`, deterministically.** From the block system (`e1`–`e4`, the weighted
remainders `e7`, `e8`), `K = A₀ + w`, `|w| ≤ 5`, the bounds `‖G₁₁‖, ‖G₂₂‖, ‖F₁₁‖, ‖F₂₂‖ ≤ C₀`
(`C₀ ≥ 1`) and `‖C_k‖ ≤ ρ ≤ 1/2`: with `T = A₀ - σ`, `σ = cg₁ + bg₂`, `s = ct₁ + bt₂`,
`q = z - bg₁`, conclusions 1–5 hold with errors `ρ`, `ρ`, `200C₀⁵ρ`, `200C₀⁵ρ`, `200C₀⁵ρ`
(`T` is invertible with `‖T⁻¹‖ ≤ 2C₀`, `‖q⁻¹‖ ≤ 2C₀`, `‖KT⁻¹‖ ≤ 13C₀²`). -/
theorem osd_algebra {W : ℕ} (hW : 0 < W) (hn : Fintype.card n = W) (hm : Fintype.card m = W)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) {z w : ℂ} (hw : ‖w‖ ≤ 5)
    {A0 K G11 F11 C1 C3 C4 C7 C8 : Matrix n n ℂ} {G22 F22 C2 C5 C6 : Matrix m m ℂ}
    {C₀ ρ : ℝ} (hC₀ : 1 ≤ C₀) (hρ : ρ ≤ 1 / 2)
    (hG11 : ‖G11‖ ≤ C₀) (hG22 : ‖G22‖ ≤ C₀) (hF11 : ‖F11‖ ≤ C₀) (hF22 : ‖F22‖ ≤ C₀)
    (hC1 : ‖C1‖ ≤ ρ) (hC2 : ‖C2‖ ≤ ρ) (hC3 : ‖C3‖ ≤ ρ) (hC4 : ‖C4‖ ≤ ρ) (hC5 : ‖C5‖ ≤ ρ)
    (hC6 : ‖C6‖ ≤ ρ) (hC7 : ‖C7‖ ≤ ρ) (hC8 : ‖C8‖ ≤ ρ)
    (hK : K = A0 + w • 1)
    (e1 : A0 * G11 - (((1 - 2 * (b : ℂ)) * ((W : ℂ)⁻¹ * G11.trace) +
        (b : ℂ) * ((W : ℂ)⁻¹ * G22.trace)) • G11 + C1) = 1)
    (e2 : z • G22 - (((b : ℂ) * ((W : ℂ)⁻¹ * G11.trace)) • G22 + C2) = 1)
    (e3 : A0 * F11 - ((((1 - 2 * (b : ℂ)) * ((W : ℂ)⁻¹ * G11.trace) +
        (b : ℂ) * ((W : ℂ)⁻¹ * G22.trace)) • F11 + C3) +
      (((1 - 2 * (b : ℂ)) * ((W : ℂ)⁻¹ * F11.trace) + (b : ℂ) * ((W : ℂ)⁻¹ * F22.trace)) • G11ᴴ +
        C4)) = 0)
    (e4 : z • F22 - ((((b : ℂ) * ((W : ℂ)⁻¹ * G11.trace)) • F22 + C5) +
      (((b : ℂ) * ((W : ℂ)⁻¹ * F11.trace)) • G22ᴴ + C6)) = G22ᴴ)
    (e7 : C3 * Kᴴ = C7) (e8 : C4 * Kᴴ = C8) :
    let g1 : ℂ := (W : ℂ)⁻¹ * G11.trace
    let g2 : ℂ := (W : ℂ)⁻¹ * G22.trace
    let t1 : ℂ := (W : ℂ)⁻¹ * F11.trace
    let t2 : ℂ := (W : ℂ)⁻¹ * F22.trace
    let σ : ℂ := (1 - 2 * (b : ℂ)) * g1 + (b : ℂ) * g2
    let s : ℂ := (1 - 2 * (b : ℂ)) * t1 + (b : ℂ) * t2
    let T : Matrix n n ℂ := A0 - σ • 1
    ‖T * G11 - 1‖ ≤ ρ ∧ ‖g2 * (z - (b : ℂ) * g1) - 1‖ ≤ ρ ∧
      ‖t1 - s * ((W : ℂ)⁻¹ * (T⁻¹ * T⁻¹ᴴ).trace)‖ ≤ 200 * C₀ ^ 5 * ρ ∧
      ‖t2 - (1 + (b : ℂ) * t1) * ((‖(z - (b : ℂ) * g1)⁻¹‖ ^ 2 : ℝ) : ℂ)‖ ≤ 200 * C₀ ^ 5 * ρ ∧
      ‖K * F11 * Kᴴ - s • ((K * T⁻¹) * (K * T⁻¹)ᴴ)‖ ≤ 200 * C₀ ^ 5 * ρ := by
  intro g1 g2 t1 t2 σ s T
  have hC0 : 0 ≤ C₀ := by linarith
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hC1
  have hbc : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0]
  have hcc : ‖(1 - 2 * (b : ℂ))‖ = 1 - 2 * b := by
    rw [show (1 - 2 * (b : ℂ)) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hg1 : ‖g1‖ ≤ C₀ := (osd_ntr_le hW hn G11).trans hG11
  have hg2 : ‖g2‖ ≤ C₀ := (osd_ntr_le hW hm G22).trans hG22
  have ht1 : ‖t1‖ ≤ C₀ := (osd_ntr_le hW hn F11).trans hF11
  have ht2 : ‖t2‖ ≤ C₀ := (osd_ntr_le hW hm F22).trans hF22
  have hmix : ∀ u v : ℂ, ‖u‖ ≤ C₀ → ‖v‖ ≤ C₀ → ‖(1 - 2 * (b : ℂ)) * u + (b : ℂ) * v‖ ≤ C₀ := by
    intro u v hu hv
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hcc, hbc]
    nlinarith [norm_nonneg u, norm_nonneg v]
  have hσ : ‖σ‖ ≤ C₀ := hmix g1 g2 hg1 hg2
  have hs : ‖s‖ ≤ C₀ := hmix t1 t2 ht1 ht2
  -- conclusion 1
  have hTG : T * G11 = A0 * G11 - σ • G11 := by
    simp only [T, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  have h1 : T * G11 - 1 = C1 := by
    have e1' := e1
    rw [sub_eq_iff_eq_add] at e1'
    rw [hTG, e1']
    abel
  have i1 : ‖T * G11 - 1‖ ≤ ρ := by rw [h1]; exact hC1
  obtain ⟨hTu, hMn⟩ := opp_inv_of_mul_near_one i1 hρ
  set M := T⁻¹ with hMdef
  have hM : ‖M‖ ≤ 2 * C₀ := hMn.trans (by linarith)
  have hMT : M * T = 1 := nonsing_inv_mul T hTu
  have hTM : T * M = 1 := mul_nonsing_inv T hTu
  have hG11e : G11 = M + M * C1 := by
    have : G11 = M * (T * G11) := by rw [← Matrix.mul_assoc, hMT, Matrix.one_mul]
    rw [this, ← h1]
    simp [Matrix.mul_sub, ← Matrix.mul_assoc]
  have hp5 : C₀ ≤ C₀ ^ 5 := le_self_pow₀ hC₀ (by norm_num)
  have hp3 : C₀ ^ 3 ≤ C₀ ^ 5 := pow_le_pow_right₀ hC₀ (by norm_num)
  have hp2 : C₀ ^ 2 ≤ C₀ ^ 5 := pow_le_pow_right₀ hC₀ (by norm_num)
  have hg1d : g1 = (W : ℂ)⁻¹ * G11.trace := rfl
  have hg2d : g2 = (W : ℂ)⁻¹ * G22.trace := rfl
  have ht1d : t1 = (W : ℂ)⁻¹ * F11.trace := rfl
  have ht2d : t2 = (W : ℂ)⁻¹ * F22.trace := rfl
  -- conclusion 2
  have e2' := sub_eq_iff_eq_add.mp e2
  have h2 : (z - (b : ℂ) * g1) • G22 - 1 = C2 := by
    rw [sub_smul, e2']; abel
  have i2 : ‖g2 * (z - (b : ℂ) * g1) - 1‖ ≤ ρ := by
    have htr : (W : ℂ)⁻¹ * ((z - (b : ℂ) * g1) • G22 - 1).trace = g2 * (z - (b : ℂ) * g1) - 1 := by
      rw [trace_sub, trace_smul, smul_eq_mul, mul_sub, osd_ntr_one hW hm, hg2d]; ring
    rw [← htr, h2]
    exact (osd_ntr_le hW hm C2).trans hC2
  -- conclusion 3
  have e3' := sub_eq_zero.mp e3
  have hTF : T * F11 = s • G11ᴴ + C3 + C4 := by
    have : T * F11 = A0 * F11 - σ • F11 := by
      simp only [T, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [this, e3']; abel
  have hF11e : F11 = M * (s • G11ᴴ + C3 + C4) := by
    rw [← hTF, ← Matrix.mul_assoc, hMT, Matrix.one_mul]
  have hid3 : F11 - s • (M * Mᴴ) = s • (M * C1ᴴ * Mᴴ) + M * (C3 + C4) := by
    rw [hF11e, hG11e, conjTranspose_add, conjTranspose_mul]
    simp only [Matrix.mul_add, Matrix.mul_smul, smul_add, Matrix.mul_assoc]
    abel
  have i3 : ‖t1 - s * ((W : ℂ)⁻¹ * (M * Mᴴ).trace)‖ ≤ 200 * C₀ ^ 5 * ρ := by
    have htr : t1 - s * ((W : ℂ)⁻¹ * (M * Mᴴ).trace) =
        (W : ℂ)⁻¹ * (F11 - s • (M * Mᴴ)).trace := by
      rw [trace_sub, trace_smul, smul_eq_mul, ht1d]; ring
    rw [htr, hid3]
    refine (osd_ntr_le hW hn _).trans ?_
    have hb1' : ‖s • (M * C1ᴴ * Mᴴ)‖ ≤ C₀ * ((2 * C₀) * ρ * (2 * C₀)) := by
      rw [norm_smul]
      refine mul_le_mul hs ?_ (norm_nonneg _) hC0
      calc ‖M * C1ᴴ * Mᴴ‖ ≤ ‖M‖ * ‖C1ᴴ‖ * ‖Mᴴ‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ (2 * C₀) * ρ * (2 * C₀) := by
            rw [l2_opNorm_conjTranspose, l2_opNorm_conjTranspose]
            exact mul_le_mul (mul_le_mul hM hC1 (norm_nonneg _) (by linarith)) hM (norm_nonneg _)
              (by positivity)
    have hb2' : ‖M * (C3 + C4)‖ ≤ (2 * C₀) * (ρ + ρ) :=
      (norm_mul_le _ _).trans (mul_le_mul hM ((norm_add_le _ _).trans (add_le_add hC3 hC4))
        (norm_nonneg _) (by linarith))
    calc ‖s • (M * C1ᴴ * Mᴴ) + M * (C3 + C4)‖ ≤ C₀ * ((2 * C₀) * ρ * (2 * C₀)) +
          (2 * C₀) * (ρ + ρ) := (norm_add_le _ _).trans (add_le_add hb1' hb2')
      _ = 4 * C₀ ^ 3 * ρ + 4 * C₀ * ρ := by ring
      _ ≤ 200 * C₀ ^ 5 * ρ := by
          linarith only [mul_le_mul_of_nonneg_right hp3 hρ0, mul_le_mul_of_nonneg_right hp5 hρ0,
            mul_nonneg (pow_nonneg hC0 5) hρ0]
  -- conclusion 4
  have e4' := sub_eq_iff_eq_add.mp e4
  set q : ℂ := z - (b : ℂ) * g1 with hq
  have h4 : q • F22 = (1 + (b : ℂ) * t1) • G22ᴴ + C5 + C6 := by
    rw [hq, sub_smul, e4', add_smul, one_smul]; abel
  have hconj : (W : ℂ)⁻¹ * (G22ᴴ).trace = conj g2 := by
    rw [trace_conjTranspose, hg2d, map_mul, map_inv₀, Complex.conj_natCast]; rfl
  set τ : ℂ := (W : ℂ)⁻¹ * (C5 + C6).trace with hτ
  have htr4 : q * t2 = (1 + (b : ℂ) * t1) * conj g2 + τ := by
    have := congrArg (fun N : Matrix m m ℂ => (W : ℂ)⁻¹ * N.trace) h4
    simp only [trace_add, trace_smul, smul_eq_mul, mul_add] at this
    rw [ht2d, ← hconj, hτ, trace_add, mul_add]
    linear_combination this
  obtain ⟨hq0, hqi, hgq⟩ := opp_step_port i2 hρ hg2
  have ht2e : t2 = q⁻¹ * ((1 + (b : ℂ) * t1) * conj g2 + τ) := by
    rw [← htr4]; field_simp
  have hnq : (((‖q⁻¹‖ ^ 2 : ℝ)) : ℂ) = q⁻¹ * conj q⁻¹ := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have i4 : ‖t2 - (1 + (b : ℂ) * t1) * ((‖q⁻¹‖ ^ 2 : ℝ) : ℂ)‖ ≤ 200 * C₀ ^ 5 * ρ := by
    have e : t2 - (1 + (b : ℂ) * t1) * ((‖q⁻¹‖ ^ 2 : ℝ) : ℂ) =
        q⁻¹ * (1 + (b : ℂ) * t1) * conj (g2 - q⁻¹) + q⁻¹ * τ := by
      rw [ht2e, hnq, map_sub]; ring
    rw [e]
    have hbt : ‖1 + (b : ℂ) * t1‖ ≤ 2 * C₀ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_mul, hbc]
      nlinarith [norm_nonneg t1]
    have hτn : ‖τ‖ ≤ ρ + ρ :=
      (osd_ntr_le hW hm _).trans ((norm_add_le _ _).trans (add_le_add hC5 hC6))
    have hcn : ‖conj (g2 - q⁻¹)‖ = ‖g2 - q⁻¹‖ := Complex.norm_conj _
    calc ‖q⁻¹ * (1 + (b : ℂ) * t1) * conj (g2 - q⁻¹) + q⁻¹ * τ‖
        ≤ ‖q⁻¹‖ * ‖1 + (b : ℂ) * t1‖ * ‖conj (g2 - q⁻¹)‖ + ‖q⁻¹‖ * ‖τ‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul_le _ _))
          rw [norm_mul, norm_mul]
      _ ≤ (2 * C₀) * (2 * C₀) * (2 * C₀ * ρ) + (2 * C₀) * (ρ + ρ) := by
          rw [hcn]
          exact add_le_add (mul_le_mul (mul_le_mul hqi hbt (norm_nonneg _) (by linarith)) hgq
            (norm_nonneg _) (by positivity)) (mul_le_mul hqi hτn (norm_nonneg _) (by linarith))
      _ = 8 * C₀ ^ 3 * ρ + 4 * C₀ * ρ := by ring
      _ ≤ 200 * C₀ ^ 5 * ρ := by
          linarith only [mul_le_mul_of_nonneg_right hp3 hρ0, mul_le_mul_of_nonneg_right hp5 hρ0,
            mul_nonneg (pow_nonneg hC0 5) hρ0]
  -- conclusion 5
  have hKT : K = T + (w + σ) • 1 := by
    rw [hK]; simp only [T, add_smul]; abel
  set N := K * M with hNdef
  have hN : N = 1 + (w + σ) • M := by
    rw [hNdef, hKT, Matrix.add_mul, hTM, Matrix.smul_mul, Matrix.one_mul]
  have hNn : ‖N‖ ≤ 13 * C₀ ^ 2 := by
    rw [hN]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have h1n := lct_norm_one_le (n := n)
    have hwσ : ‖w + σ‖ ≤ 5 + C₀ := (norm_add_le _ _).trans (add_le_add hw hσ)
    have := mul_le_mul hwσ hM (norm_nonneg _) (by linarith)
    nlinarith
  have hTFK : T * (F11 * Kᴴ) = s • (G11ᴴ * Kᴴ) + C7 + C8 := by
    rw [← Matrix.mul_assoc, hTF, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, e7, e8]
  have hKF : K * F11 * Kᴴ = N * (T * (F11 * Kᴴ)) := by
    rw [hNdef, Matrix.mul_assoc K M, ← Matrix.mul_assoc M T, hMT, Matrix.one_mul,
      Matrix.mul_assoc]
  have hKG : K * G11 = N + N * C1 := by
    rw [hG11e, Matrix.mul_add, ← Matrix.mul_assoc, hNdef]
  have hGK : G11ᴴ * Kᴴ = Nᴴ + C1ᴴ * Nᴴ := by
    rw [← conjTranspose_mul, hKG, conjTranspose_add, conjTranspose_mul N C1]
  have hid5 : K * F11 * Kᴴ - s • (N * Nᴴ) = s • (N * C1ᴴ * Nᴴ) + N * (C7 + C8) := by
    rw [hKF, hTFK, hGK]
    simp only [Matrix.mul_add, Matrix.mul_smul, smul_add, Matrix.mul_assoc]
    abel
  have i5 : ‖K * F11 * Kᴴ - s • (N * Nᴴ)‖ ≤ 200 * C₀ ^ 5 * ρ := by
    rw [hid5]
    have hNh : ‖Nᴴ‖ = ‖N‖ := l2_opNorm_conjTranspose _
    have hb1' : ‖s • (N * C1ᴴ * Nᴴ)‖ ≤ C₀ * ((13 * C₀ ^ 2) * ρ * (13 * C₀ ^ 2)) := by
      rw [norm_smul]
      refine mul_le_mul hs ?_ (norm_nonneg _) hC0
      calc ‖N * C1ᴴ * Nᴴ‖ ≤ ‖N‖ * ‖C1ᴴ‖ * ‖Nᴴ‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ (13 * C₀ ^ 2) * ρ * (13 * C₀ ^ 2) := by
            rw [l2_opNorm_conjTranspose, hNh]
            exact mul_le_mul (mul_le_mul hNn hC1 (norm_nonneg _) (by positivity)) hNn
              (norm_nonneg _) (by positivity)
    have hb2' : ‖N * (C7 + C8)‖ ≤ (13 * C₀ ^ 2) * (ρ + ρ) :=
      (norm_mul_le _ _).trans (mul_le_mul hNn ((norm_add_le _ _).trans (add_le_add hC7 hC8))
        (norm_nonneg _) (by positivity))
    calc ‖s • (N * C1ᴴ * Nᴴ) + N * (C7 + C8)‖ ≤ C₀ * ((13 * C₀ ^ 2) * ρ * (13 * C₀ ^ 2)) +
          (13 * C₀ ^ 2) * (ρ + ρ) := (norm_add_le _ _).trans (add_le_add hb1' hb2')
      _ = 169 * C₀ ^ 5 * ρ + 26 * C₀ ^ 2 * ρ := by ring
      _ ≤ 200 * C₀ ^ 5 * ρ := by
          linarith only [mul_le_mul_of_nonneg_right hp2 hρ0, mul_nonneg (pow_nonneg hC0 5) hρ0]
  exact ⟨i1, i2, i3, i4, i5⟩

end Algebra

/-!
## 7. Mean bounds and the transfer to the layer law
-/

section Bounds

variable {W : ℕ} {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}

theorem osd_measurable_G (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Measurable (osdG b E X) :=
  measurable_matrix_inv.comp ((measurable_layerMatrix _ _ _ _).comp (tfl_measurable_embed W b _))

theorem osd_H_ge (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (hη : 0 ≤ (boundaryZ b E).im)
    (x : TflCoord W .oneBlockOnePort → ℝ) : ‖osdG b E X x‖ ≤ osdH b E X x := by
  have h1 := osd_wlF_ge_norm b E X x
  have h2 := osd_one_le_wlF b E X x
  unfold osdH
  set F := wlF E (boundaryZ b E) (onePortLift X) (tflEmbed W b .oneBlockOnePort x)
  have : F ≤ (4 + 4 * (boundaryZ b E).im) * F ^ 2 := by
    have hF : F ≤ F ^ 2 := by rw [sq]; exact le_mul_of_one_le_right (by linarith) h2
    have : F ^ 2 ≤ (4 + 4 * (boundaryZ b E).im) * F ^ 2 :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    linarith
  linarith

/-- `‖Ḡ‖, ‖F̄‖ ≤ 1 + E H⁴`. -/
theorem osd_mean_bounds (h : OsdHyp W b E X) :
    ‖matrixExpect (gaussianProduct (tflVar W b .oneBlockOnePort)) (osdG b E X)‖ ≤
        1 + ∫ x, osdH b E X x ^ 4 ∂gaussianProduct (tflVar W b .oneBlockOnePort) ∧
      ‖matrixExpect (gaussianProduct (tflVar W b .oneBlockOnePort)) (osdF b E X)‖ ≤
        1 + ∫ x, osdH b E X x ^ 4 ∂gaussianProduct (tflVar W b .oneBlockOnePort) := by
  set μ := gaussianProduct (tflVar W b .oneBlockOnePort) with hμ
  have hHge := osd_H_ge (W := W) b E X h.heta.le
  have hH0 : ∀ x, 0 ≤ osdH b E X x := fun x => (norm_nonneg _).trans (hHge x)
  have hGm := osd_measurable_G (W := W) b E X
  have hFm : Measurable (osdF b E X) := by
    have hc : Continuous (fun M : Matrix (LayerSite W .oneBlockOnePort)
        (LayerSite W .oneBlockOnePort) ℂ => M * onePortPortProj * Mᴴ) :=
      (continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_conjTranspose
    exact hc.measurable.comp hGm
  have h1H : Integrable (fun x => 1 + osdH b E X x ^ 4) μ := (integrable_const _).add h.hH4
  have hGb : ∀ x, ‖osdG b E X x‖ ≤ 1 + osdH b E X x ^ 4 := fun x =>
    (hHge x).trans (osd_le_one_add_pow4 _).1
  have hFb : ∀ x, ‖osdF b E X x‖ ≤ 1 + osdH b E X x ^ 4 := fun x => by
    have hP : ‖(onePortPortProj : Matrix (LayerSite W .oneBlockOnePort)
        (LayerSite W .oneBlockOnePort) ℂ)‖ ≤ 1 :=
      wl_norm_Q_le (n := PhysSite W .oneBlockOnePort) (m := PortSite W .oneBlockOnePort)
    have hG := hHge x
    have e : ‖osdF b E X x‖ ≤ ‖osdG b E X x‖ * 1 * ‖osdG b E X x‖ := by
      unfold osdF
      calc _ ≤ ‖osdG b E X x‖ * ‖(onePortPortProj : Matrix (LayerSite W .oneBlockOnePort)
            (LayerSite W .oneBlockOnePort) ℂ)‖ * ‖(osdG b E X x)ᴴ‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ ‖osdG b E X x‖ * 1 * ‖osdG b E X x‖ := by
            rw [l2_opNorm_conjTranspose]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
              (norm_nonneg _)
    refine e.trans ?_
    have : ‖osdG b E X x‖ * 1 * ‖osdG b E X x‖ ≤ osdH b E X x ^ 2 := by
      rw [mul_one, sq]; exact mul_le_mul hG hG (norm_nonneg _) (hH0 x)
    exact this.trans (osd_le_one_add_pow4 _).2
  have hGi : Integrable (osdG b E X) μ :=
    Integrable.mono' h1H hGm.aestronglyMeasurable (ae_of_all _ hGb)
  have hFi : Integrable (osdF b E X) μ :=
    Integrable.mono' h1H hFm.aestronglyMeasurable (ae_of_all _ hFb)
  have hI : ∫ x, (1 + osdH b E X x ^ 4) ∂μ = 1 + ∫ x, osdH b E X x ^ 4 ∂μ := by
    rw [integral_add (integrable_const _) h.hH4, integral_const, probReal_univ, one_smul]
  constructor
  · rw [meq_matrixExpect_eq hGi, ← hI]
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono hGi.norm h1H hGb)
  · rw [meq_matrixExpect_eq hFi, ← hI]
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono hFi.norm h1H hFb)

end Bounds

section Transfer

variable {W : ℕ}

/-- The reindexing `Fin W ≃ Fin 1 × Fin W`, `x ↦ (0, x)`. -/
abbrev osdE (W : ℕ) : Fin W ≃ Fin 1 × Fin W := Equiv.ofBijective (opmIncl W) opmIncl_bijective

theorem osd_sm_sub {k l : Type*} (A B : Matrix k k ℂ) (r : l → k) :
    (A - B).submatrix r r = A.submatrix r r - B.submatrix r r := rfl

theorem osd_sm_smul {k l : Type*} (c : ℂ) (A : Matrix k k ℂ) (r : l → k) :
    (c • A).submatrix r r = c • A.submatrix r r := rfl

theorem osd_trace_sm (A : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) :
    (A.submatrix (osdE W) (osdE W)).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, submatrix_apply]
  exact Equiv.sum_comp (osdE W) (fun p => A p p)

theorem osd_lift_sm (X : Matrix (Fin W) (Fin W) ℂ) :
    (onePortLift X).submatrix (osdE W) (osdE W) = X := by
  ext i j; rfl

theorem osd_trace_mul_self_real {k : Type*} [Fintype k] (M : Matrix k k ℂ) :
    (((M * Mᴴ).trace.re : ℝ) : ℂ) = (M * Mᴴ).trace := by
  have h : (M * Mᴴ).trace = star (M * Mᴴ).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

theorem osd_F11 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    (osdF b E X x).toBlocks₁₁ = (osdG b E X x).toBlocks₁₂ * ((osdG b E X x).toBlocks₁₂)ᴴ := by
  unfold osdF onePortPortProj
  conv_lhs => rw [← fromBlocks_toBlocks (osdG b E X x)]
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, toBlocks_fromBlocks₁₁]
  simp

theorem osd_F22 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x : TflCoord W .oneBlockOnePort → ℝ) :
    (osdF b E X x).toBlocks₂₂ = (osdG b E X x).toBlocks₂₂ * ((osdG b E X x).toBlocks₂₂)ᴴ := by
  unfold osdF onePortPortProj
  conv_lhs => rw [← fromBlocks_toBlocks (osdG b E X x)]
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, toBlocks_fromBlocks₂₂]
  simp

theorem osd_mE_layer (b : ℝ) {k l : Type*} {U : LayerSample W .oneBlockOnePort → Matrix k l ℂ}
    (hU : ∀ i j, Measurable (fun ω => U ω i j)) :
    matrixExpect (layerLaw W b .oneBlockOnePort) U =
      matrixExpect (gaussianProduct (tflVar W b .oneBlockOnePort))
        (fun x => U (tflEmbed W b .oneBlockOnePort x)) := by
  ext i j
  simp only [matrixExpect, of_apply]
  rw [tfl_layerLaw_eq_map, integral_map (tfl_measurable_embed W b _).aemeasurable
    (hU i j).aestronglyMeasurable]

theorem osd_int_layer (b : ℝ) {g : LayerSample W .oneBlockOnePort → ℝ} (hg : Measurable g) :
    ∫ ω, g ω ∂layerLaw W b .oneBlockOnePort =
      ∫ x, g (tflEmbed W b .oneBlockOnePort x) ∂gaussianProduct (tflVar W b .oneBlockOnePort) := by
  rw [tfl_layerLaw_eq_map, integral_map (tfl_measurable_embed W b _).aemeasurable
    hg.aestronglyMeasurable]

theorem osd_meas_entry (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) {k l : Type*}
    {φ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ → Matrix k l ℂ}
    (hφ : Continuous φ) (i : k) (j : l) :
    Measurable (fun ω => φ (onePortResolvent b E X ω) i j) :=
  ((continuous_apply j).comp ((continuous_apply i).comp hφ)).measurable.comp
    (measurable_layerResolvent _ _ _ _)

theorem osd_int_mul_left {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {k l : Type*} [Fintype k]
    (D : Matrix l k ℂ) {U : Ω → Matrix k k ℂ} (hU : ∀ i j, Integrable (fun x => U x i j) μ) :
    ∀ i j, Integrable (fun x => (D * U x) i j) μ := fun i j => by
  simp only [Matrix.mul_apply]
  exact integrable_finsetSum _ fun k _ => (hU k j).const_mul _

end Transfer

/-!
## 8. The passive one-port Schwinger–Dyson system
-/

set_option linter.unusedVariables false in
/-- **The passive one-port Schwinger–Dyson system** (`OppPassiveMeanEquations`): the mean
equations `M = (z - X - Ω)⁻¹`, `m = W⁻¹ Tr M`, `v = (z - bm)⁻¹`, the bottom-source trace
equations `t₁ = A_M(ct₁ + bt₂) + O(W⁻²)`, `t₂ = h(1 + bt₁) + O(W⁻²)` and the first form of the
passive mean identity, `E(LL*|X) = (ct₁ + bt₂)(KM)(KM)* + O_op(W⁻²)`, written at the layer
means.

* **Law / measure.** The fresh one-block one-port layer `layerLaw W b .oneBlockOnePort`
  (`A ~ GUE_W(c/W)`, `c = 1 - 2b`, `B ~ Gin(b/W)` independent) at `z = z_∂(E) = boundaryZ b E`,
  conditional on the deterministic input `X` (expectations over the fresh layer only).
* **Domain.** `b ∈ (0,1/2)`, `κ > 0`, `E ∈ bulkInterval κ`, `W ≥ W₀`, every **passive** `X`
  (`IsPassiveInput X`: `-Im X ⪰ 0`; no bound on `‖X‖` or on `‖Im X‖`; no scalar- or jet-domain
  restriction).
* **Objects / norms.** As in `OppPassiveMeanEquations`: `Ḡ = E𝒢₁₁`, `ḡ₁ = W⁻¹ Tr Ḡ`,
  `ḡ₂ = W⁻¹ Tr E𝒢₂₂`, `t₁ = E W⁻¹ Tr 𝒢₁₂𝒢₁₂*`, `t₂ = E W⁻¹ Tr 𝒢₂₂𝒢₂₂*`,
  `T̄ = (-E - cḡ₁ - bḡ₂) - X`, `M̄ = T̄⁻¹`, `v̄ = (z - bḡ₁)⁻¹`, `A = W⁻¹ Re Tr M̄M̄*`,
  `s = ct₁ + bt₂`, `K = z - X`, `L = K𝒢₁₂`; `ℓ²` operator norm on `W × W` matrices, modulus on
  scalars; matrix expectations entrywise (`matrixExpect`).
* **Conclusion.** `‖T̄Ḡ - 1‖`, `|ḡ₂(z - bḡ₁) - 1|`, `|t₁ - sA|`, `|t₂ - (1 + bt₁)|v̄|²|`,
  `‖E LL* - s(KM̄)(KM̄)*‖` are all `≤ C/W²`.
* **Quantifier order / uniformity.** `b, κ` first; then `C = 200 C₀⁵ C_c` (`C₀ = 1 + C_H`,
  `C_c = 40(1 + η₀⁻¹)² C_H`) and `W₀ = max(W₁, ⌈2C_c⌉ + 1)`, where `η₀(b,κ)` is the bulk lower bound
  of `Im z_∂` and `C_H, W₁` come from `osd_setup` (passive inverse moments of order 16 and the
  Gaussian moments of `Λ`); then uniformly in `W ≥ W₀`, passive `X` and `E ∈ bulkInterval κ`.
  No order of limits (fixed `W`; the regularization `κ' → 0` is internal to `osd_cov_limit`
  and `core_limit_identity`).
* **Proof.** Doubling `𝒩 = [[N, -ηP], [0, -N*]]` (`Im 𝒩 ⪰ 0` for passive `X`): the generic
  first-order identity gives both Schwinger–Dyson identities (`osd_SD`), whose blocks are
  `osd_blocks`; the eight error covariances are one-letter covariances of `𝒩⁻¹`
  (`osd_cov1`–`osd_cov8`, `≤ C_c/W²`), in the words `𝒢, 𝒢*, F = 𝒢P𝒢*, 𝒢*K* = (K𝒢)*` only;
  `osd_algebra` concludes, and the result is transported to the layer law and to `Fin W`
  (`osd_mE_layer`, `osdE`).
* **Inputs.** `hcount : ConditionalBlockGUECount` (through `opm_passive_inverse_moments` and
  `gaussianAbsorption_holds`). `hgrad : GaussianLpGradient` is not used: every error is a
  trace–matrix covariance, bounded by the Ornstein–Uhlenbeck identity (`ou_covariance_matrix`),
  not by a fluctuation estimate. -/
theorem oppPassiveMeanEquations_holds (hcount : ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : OppPassiveMeanEquations := by
  intro b hb0 hb1 κ hκ
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨CH, W₁, hCH, hset⟩ := osd_setup hcount b hb0 hb1 κ hκ
  set C₀ : ℝ := 1 + CH with hC₀def
  set Cc : ℝ := 40 * (1 + η₀⁻¹) ^ 2 * CH with hCcdef
  have hC₀1 : 1 ≤ C₀ := by linarith
  have hCc0 : 0 ≤ Cc := by positivity
  refine ⟨200 * C₀ ^ 5 * Cc, max W₁ (⌈2 * Cc⌉₊ + 1), ?_⟩
  intro W hW hWW X hX E hE
  obtain ⟨hzη, hzM, hE2⟩ := hbulk E hE
  obtain ⟨hinv, hH4, hHI⟩ := hset W hW (le_of_max_le_left hWW) X hX E hE
  have hη : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη₀ hzη
  have h : OsdHyp W b E X := ⟨hW, hb0, hb1, hX, hE2, hzM, hη, hinv, hH4⟩
  set μ := gaussianProduct (tflVar W b .oneBlockOnePort) with hμ
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  -- the covariance scale
  set ρ : ℝ := Cc / (W : ℝ) ^ 2 with hρdef
  have hI0 : 0 ≤ ∫ x, osdH b E X x ^ 4 ∂μ := integral_nonneg fun x => by unfold osdH; positivity
  have hρρ : osdRho W b E X ≤ ρ := by
    have hk : (1 + ((boundaryZ b E).im)⁻¹) ^ 2 ≤ (1 + η₀⁻¹) ^ 2 := by
      have : ((boundaryZ b E).im)⁻¹ ≤ η₀⁻¹ := inv_anti₀ hη₀ hzη
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    have e : ρ = 40 / (W : ℝ) ^ 2 * (1 + η₀⁻¹) ^ 2 * CH := by rw [hρdef, hCcdef]; ring
    rw [e, osdRho]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hk (by positivity)) hHI hI0 (by positivity)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρhalf : ρ ≤ 1 / 2 := by
    have h1 : (2 * Cc : ℝ) ≤ ⌈2 * Cc⌉₊ := Nat.le_ceil _
    have h2 : ((⌈2 * Cc⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hWW
    push_cast at h2
    have hW1 : (1 : ℝ) ≤ W := by linarith
    have hWW2 : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
    rw [hρdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hρC' : 200 * C₀ ^ 5 * ρ = 200 * C₀ ^ 5 * Cc / (W : ℝ) ^ 2 := by rw [hρdef]; ring
  have hρC : ρ ≤ 200 * C₀ ^ 5 * Cc / (W : ℝ) ^ 2 := by
    have : 1 ≤ 200 * C₀ ^ 5 := by nlinarith [one_le_pow₀ (n := 5) hC₀1]
    rw [← hρC']
    exact le_mul_of_one_le_left hρ0 this
  -- the eight covariances
  obtain ⟨-, -, -, c1⟩ := osd_cov1 h
  obtain ⟨-, -, -, c2⟩ := osd_cov2 h
  obtain ⟨-, u3, fu3, c3⟩ := osd_cov3 h
  obtain ⟨-, u4, fu4, c4⟩ := osd_cov4 h
  obtain ⟨-, -, -, c5⟩ := osd_cov5 h
  obtain ⟨-, -, -, c6⟩ := osd_cov6 h
  obtain ⟨-, -, -, c7⟩ := osd_cov7 h
  obtain ⟨-, -, -, c8⟩ := osd_cov8 h
  have e7 := osd_cov_mul_right (μ := μ) (fun x => osdSA b (osdG b E X x)) (osdKt b E X)ᴴ u3 fu3
  have e8 := osd_cov_mul_right (μ := μ) (fun x => osdSA b (osdF b E X x)) (osdKt b E X)ᴴ u4 fu4
  -- the block system
  obtain ⟨e1, e2, e3, e4⟩ := osd_blocks h
  set Gb := matrixExpect μ (osdG b E X) with hGbdef
  set Fb := matrixExpect μ (osdF b E X) with hFbdef
  obtain ⟨hGn, hFn⟩ := osd_mean_bounds h
  have hGn' : ‖Gb‖ ≤ C₀ := hGn.trans (by linarith)
  have hFn' : ‖Fb‖ ≤ C₀ := hFn.trans (by linarith)
  have hSA : ∀ M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ,
      osdSA b M = (1 - 2 * (b : ℂ)) * ((W : ℂ)⁻¹ * M.toBlocks₁₁.trace) +
        (b : ℂ) * ((W : ℂ)⁻¹ * M.toBlocks₂₂.trace) := fun M => by
    rw [osdSA, osd_phys_eq, osd_port_eq]
  have hSB : ∀ M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ,
      osdSB b M = (b : ℂ) * ((W : ℂ)⁻¹ * M.toBlocks₁₁.trace) := fun M => by
    rw [osdSB, osd_phys_eq]
  rw [hSA] at e1
  rw [hSB] at e2
  rw [hSA, hSA] at e3
  rw [hSB, hSB] at e4
  have hn : Fintype.card (PhysSite W .oneBlockOnePort) = W := by simp
  have hm : Fintype.card (PortSite W .oneBlockOnePort) = W := by simp
  have hK : osdKt b E X = (-((E : ℂ) • (1 : Matrix (PhysSite W .oneBlockOnePort)
      (PhysSite W .oneBlockOnePort) ℂ)) - onePortLift X) + (boundaryZ b E + (E : ℂ)) • 1 := by
    rw [osdKt, add_smul]; abel
  have hw : ‖boundaryZ b E + (E : ℂ)‖ ≤ 5 :=
    (norm_add_le _ _).trans (by rw [Complex.norm_real, Real.norm_eq_abs]; linarith)
  obtain ⟨i1, i2, i3, i4, i5⟩ := osd_algebra hW hn hm hb0.le hb1.le hw hC₀1 hρhalf
    ((wl_norm_toBlocks11_le Gb).trans hGn') ((osd_norm_toBlocks22_le Gb).trans hGn')
    ((wl_norm_toBlocks11_le Fb).trans hFn') ((osd_norm_toBlocks22_le Fb).trans hFn')
    (c1.trans hρρ) (c2.trans hρρ) (c3.trans hρρ) (c4.trans hρρ) (c5.trans hρρ) (c6.trans hρρ)
    (c7.trans hρρ) (c8.trans hρρ) hK e1 e2 e3 e4 e7.symm e8.symm
  -- transfer to the layer law and to `Fin W`
  set e := osdE W with hedef
  have he : Function.Injective e := e.injective
  have iF := osd_int_F h
  have hMT : oppMeanTop b E X = Gb.toBlocks₁₁.submatrix e e := by
    unfold oppMeanTop
    rw [osd_mE_layer b (U := oppG11 b E X) (fun i j => osd_meas_entry b E X
      (continuous_id.matrix_submatrix (fun x => Sum.inl ((0 : Fin 1), x))
        (fun y => Sum.inl ((0 : Fin 1), y))) i j)]
    ext i j; rfl
  have hM22 : matrixExpect (layerLaw W b .oneBlockOnePort) (oppG22 b E X) =
      Gb.toBlocks₂₂.submatrix e e := by
    rw [osd_mE_layer b (U := oppG22 b E X) (fun i j => osd_meas_entry b E X
      (continuous_id.matrix_submatrix (fun x => Sum.inr ((0 : Fin 1), x))
        (fun y => Sum.inr ((0 : Fin 1), y))) i j)]
    ext i j; rfl
  have hg1 : oppG1 b E X = (W : ℂ)⁻¹ * Gb.toBlocks₁₁.trace := by
    unfold oppG1; rw [hMT, osd_trace_sm]
  have hg2 : oppG2 b E X = (W : ℂ)⁻¹ * Gb.toBlocks₂₂.trace := by
    unfold oppG2; rw [hM22, osd_trace_sm]
  have hG12 : ∀ x, onePortG12 b E X (tflEmbed W b .oneBlockOnePort x) =
      (osdG b E X x).toBlocks₁₂.submatrix e e := fun x => by ext i j; rfl
  have hG22 : ∀ x, oppG22 b E X (tflEmbed W b .oneBlockOnePort x) =
      (osdG b E X x).toBlocks₂₂.submatrix e e := fun x => by ext i j; rfl
  have hT1pt : ∀ x, (onePortG12 b E X (tflEmbed W b .oneBlockOnePort x) *
      (onePortG12 b E X (tflEmbed W b .oneBlockOnePort x))ᴴ).trace =
        (osdF b E X x).toBlocks₁₁.trace := fun x => by
    rw [hG12, conjTranspose_submatrix, submatrix_mul_equiv, osd_trace_sm, osd_F11]
  have hT2pt : ∀ x, (oppG22 b E X (tflEmbed W b .oneBlockOnePort x) *
      (oppG22 b E X (tflEmbed W b .oneBlockOnePort x))ᴴ).trace =
        (osdF b E X x).toBlocks₂₂.trace := fun x => by
    rw [hG22, conjTranspose_submatrix, submatrix_mul_equiv, osd_trace_sm, osd_F22]
  have hF11r : ∀ x, ((((osdF b E X x).toBlocks₁₁.trace).re : ℝ) : ℂ) =
      (osdF b E X x).toBlocks₁₁.trace := fun x => by
    rw [osd_F11]; exact osd_trace_mul_self_real _
  have hF22r : ∀ x, ((((osdF b E X x).toBlocks₂₂.trace).re : ℝ) : ℂ) =
      (osdF b E X x).toBlocks₂₂.trace := fun x => by
    rw [osd_F22]; exact osd_trace_mul_self_real _
  have ht1 : ((oppT1 b E X : ℝ) : ℂ) = (W : ℂ)⁻¹ * Fb.toBlocks₁₁.trace := by
    unfold oppT1
    have hmeas : Measurable (fun ω => (W : ℝ)⁻¹ *
        (onePortG12 b E X ω * (onePortG12 b E X ω)ᴴ).trace.re) := by
      have hc : Continuous (fun M : Matrix (LayerSite W .oneBlockOnePort)
          (LayerSite W .oneBlockOnePort) ℂ => (W : ℝ)⁻¹ *
            ((M.submatrix (fun x => Sum.inl ((0 : Fin 1), x)) (fun y => Sum.inr ((0 : Fin 1), y))) *
              (M.submatrix (fun x => Sum.inl ((0 : Fin 1), x))
                (fun y => Sum.inr ((0 : Fin 1), y)))ᴴ).trace.re) :=
        continuous_const.mul (Complex.continuous_re.comp
          (((continuous_id.matrix_submatrix _ _).matrix_mul
            (continuous_id.matrix_submatrix _ _).matrix_conjTranspose).matrix_trace))
      exact hc.measurable.comp (measurable_layerResolvent _ _ _ _)
    rw [osd_int_layer b hmeas, ← integral_complex_ofReal]
    have e1 : ∀ x, (((W : ℝ)⁻¹ * (onePortG12 b E X (tflEmbed W b .oneBlockOnePort x) *
        (onePortG12 b E X (tflEmbed W b .oneBlockOnePort x))ᴴ).trace.re : ℝ) : ℂ) =
        (W : ℂ)⁻¹ * (1 * (osdF b E X x).toBlocks₁₁).trace := fun x => by
      rw [hT1pt, Matrix.one_mul]; push_cast; rw [hF11r]
    rw [integral_congr_ae (ae_of_all _ e1), osd_integral_trace (U := fun x =>
      (osdF b E X x).toBlocks₁₁) _ _ (fun i j => iF (Sum.inl i) (Sum.inl j)), Matrix.one_mul]
    rfl
  have ht2 : ((oppT2 b E X : ℝ) : ℂ) = (W : ℂ)⁻¹ * Fb.toBlocks₂₂.trace := by
    unfold oppT2
    have hmeas : Measurable (fun ω => (W : ℝ)⁻¹ *
        (oppG22 b E X ω * (oppG22 b E X ω)ᴴ).trace.re) := by
      have hc : Continuous (fun M : Matrix (LayerSite W .oneBlockOnePort)
          (LayerSite W .oneBlockOnePort) ℂ => (W : ℝ)⁻¹ *
            ((M.submatrix (fun x => Sum.inr ((0 : Fin 1), x)) (fun y => Sum.inr ((0 : Fin 1), y))) *
              (M.submatrix (fun x => Sum.inr ((0 : Fin 1), x))
                (fun y => Sum.inr ((0 : Fin 1), y)))ᴴ).trace.re) :=
        continuous_const.mul (Complex.continuous_re.comp
          (((continuous_id.matrix_submatrix _ _).matrix_mul
            (continuous_id.matrix_submatrix _ _).matrix_conjTranspose).matrix_trace))
      exact hc.measurable.comp (measurable_layerResolvent _ _ _ _)
    rw [osd_int_layer b hmeas, ← integral_complex_ofReal]
    have e1 : ∀ x, (((W : ℝ)⁻¹ * (oppG22 b E X (tflEmbed W b .oneBlockOnePort x) *
        (oppG22 b E X (tflEmbed W b .oneBlockOnePort x))ᴴ).trace.re : ℝ) : ℂ) =
        (W : ℂ)⁻¹ * (1 * (osdF b E X x).toBlocks₂₂).trace := fun x => by
      rw [hT2pt, Matrix.one_mul]; push_cast; rw [hF22r]
    rw [integral_congr_ae (ae_of_all _ e1), osd_integral_trace (U := fun x =>
      (osdF b E X x).toBlocks₂₂) _ _ (fun i j => iF (Sum.inr i) (Sum.inr j)), Matrix.one_mul]
    rfl
  set Tm : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ :=
    (-((E : ℂ) • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ)) -
      onePortLift X) - ((1 - 2 * (b : ℂ)) * ((W : ℂ)⁻¹ * Gb.toBlocks₁₁.trace) +
        (b : ℂ) * ((W : ℂ)⁻¹ * Gb.toBlocks₂₂.trace)) • 1 with hTmdef
  have hTop : oppTopMatrix b E X (oppG1 b E X) (oppG2 b E X) = Tm.submatrix e e := by
    rw [hg1, hg2]
    unfold oppTopMatrix
    ext i j
    simp only [hTmdef, hedef, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      submatrix_apply, Equiv.ofBijective_apply, smul_eq_mul, onePortLift, of_apply]
    by_cases hij : i = j
    · subst hij; simp; ring
    · have : ((0 : Fin 1), i) ≠ ((0 : Fin 1), j) := fun h => hij (congrArg Prod.snd h)
      simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne this]
  have hKs : boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X = (osdKt b E X).submatrix e e := by
    ext i j
    simp only [osdKt, hedef, Matrix.sub_apply, Matrix.smul_apply, submatrix_apply,
      Equiv.ofBijective_apply, smul_eq_mul, onePortLift, of_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have : ((0 : Fin 1), i) ≠ ((0 : Fin 1), j) := fun h => hij (congrArg Prod.snd h)
      simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne this]
  have hLL : matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => onePortL b E X ω * (onePortL b E X ω)ᴴ) =
        (osdKt b E X * Fb.toBlocks₁₁ * (osdKt b E X)ᴴ).submatrix e e := by
    have hc : Continuous (fun M : Matrix (LayerSite W .oneBlockOnePort)
        (LayerSite W .oneBlockOnePort) ℂ =>
          ((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
            M.submatrix (fun x => Sum.inl ((0 : Fin 1), x)) (fun y => Sum.inr ((0 : Fin 1), y))) *
          ((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
            M.submatrix (fun x => Sum.inl ((0 : Fin 1), x)) (fun y => Sum.inr ((0 : Fin 1), y)))ᴴ) :=
      (continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)).matrix_mul
        (continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)).matrix_conjTranspose
    rw [osd_mE_layer b (U := fun ω => onePortL b E X ω * (onePortL b E X ω)ᴴ)
      (fun i j => osd_meas_entry b E X hc i j)]
    have hpt : ∀ x, onePortL b E X (tflEmbed W b .oneBlockOnePort x) *
        (onePortL b E X (tflEmbed W b .oneBlockOnePort x))ᴴ =
          (osdKt b E X * (osdF b E X x).toBlocks₁₁ * (osdKt b E X)ᴴ).submatrix e e := by
      intro x
      have hL : onePortL b E X (tflEmbed W b .oneBlockOnePort x) =
          (osdKt b E X * (osdG b E X x).toBlocks₁₂).submatrix e e := by
        rw [onePortL, hKs, hG12, submatrix_mul_equiv]
      rw [hL, conjTranspose_submatrix, submatrix_mul_equiv, osd_F11, conjTranspose_mul,
        Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    simp only [hpt]
    have iF11 : ∀ i j, Integrable (fun x => (osdF b E X x).toBlocks₁₁ i j) μ :=
      fun i j => iF (Sum.inl i) (Sum.inl j)
    have e1 : matrixExpect μ (fun x => (osdKt b E X * (osdF b E X x).toBlocks₁₁ *
        (osdKt b E X)ᴴ).submatrix e e) = (matrixExpect μ (fun x => osdKt b E X *
          (osdF b E X x).toBlocks₁₁ * (osdKt b E X)ᴴ)).submatrix e e := by ext i j; rfl
    rw [e1, osd_mE_mul_right _ (osd_int_mul_left _ iF11), osd_mE_mul_left _ iF11]
    rfl
  have hs : ((oppS b (oppT1 b E X) (oppT2 b E X) : ℝ) : ℂ) =
      (1 - 2 * (b : ℂ)) * ((W : ℂ)⁻¹ * Fb.toBlocks₁₁.trace) +
        (b : ℂ) * ((W : ℂ)⁻¹ * Fb.toBlocks₂₂.trace) := by
    unfold oppS; push_cast; rw [ht1, ht2]
  have hNTr : oppNTr (oppTopMatrix b E X (oppG1 b E X) (oppG2 b E X))⁻¹ =
      (W : ℝ)⁻¹ * (Tm⁻¹ * Tm⁻¹ᴴ).trace.re := by
    rw [hTop, inv_submatrix_equiv]
    unfold oppNTr
    rw [conjTranspose_submatrix, submatrix_mul_equiv, osd_trace_sm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hTop, hMT, submatrix_mul_equiv, ← submatrix_one_equiv e, ← osd_sm_sub]
    exact (wl_norm_submatrix_le _ he he).trans (i1.trans hρC)
  · rw [hg1, hg2]; exact i2.trans hρC
  · rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, Complex.ofReal_mul, hs,
      hNTr, Complex.ofReal_mul, osd_trace_mul_self_real, ht1]
    push_cast
    exact i3.trans hρC'.le
  · rw [← Real.norm_eq_abs, ← Complex.norm_real]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one]
    rw [ht1, ht2, oppPortV, hg1]
    exact i4.trans hρC'.le
  · rw [hLL, hKs, hTop, inv_submatrix_equiv, submatrix_mul_equiv, conjTranspose_submatrix,
      submatrix_mul_equiv, hs, ← osd_sm_smul, ← osd_sm_sub]
    exact (wl_norm_submatrix_le _ he he).trans (i5.trans hρC'.le)

end BlockBand.Layers

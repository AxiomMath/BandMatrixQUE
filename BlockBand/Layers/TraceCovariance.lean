module

public import BlockBand.Layers.TraceFluctuation
public import BlockBand.Layers.OUCovariance
public import BlockBand.Layers.WordCalculus

/-!
# The fresh trace–matrix covariance bound

The `covariance` field of `TraceMatrixContract` (the trace–matrix lemma): "In real Gaussian
coordinates ... `Cov(f,U) = ∫_0^∞ e^{-t} E[∇f(x)·Σ∇U(x_t)] dt` ... a term in `df` is
`W⁻¹ Tr K d𝓗`, a term in `dU` is `L d𝓗 N`. Their entry covariance contracts them to
`W⁻² L 𝒱(K) N` ... `‖𝒱(K)‖ ≤ C‖K‖` ... Hölder and the Gaussian absorption lemma bound the
remaining factors at `x` and `x_t`". The only hypothesis of `traceCovariance_holds` is
`GaussianAbsorptionContract` (a.s. invertibility and `‖‖𝒢‖‖_{L^p} ≤ C_A` for `1 ≤ p ≤ ε₁W`),
proved as `gaussianAbsorption_holds hcount`.

Law and normalization: `layerLaw W b σ` (`A_a ~ GUE_W(c/W)`, `c = 1-2b`, bonds `Gin(b/W)`),
realized as the image of `gaussianProduct (tflVar W b σ)` under `tflEmbed`
(`tfl_layerLaw_eq_map`). Norms: `ℓ²` operator norm on matrices; matrix expectations entrywise
(`matrixExpect`), identified with the Bochner integral in the coordinates
(`tcv_matrixExpect_eq`).

Proof.
1. **Contraction lemma** (§1, deterministic). Every coordinate direction `Λᵢ = ∂ᵢ𝒢⁻¹` is an
   explicit Hermitian two-entry matrix (`tcv_coordA0`, …, `tcv_coordB1`); summing each real/
   imaginary pair (`tcv_pair`) writes `𝒱(K) = Σᵢ vᵢ Tr(KΛᵢ) Λᵢ` as the block compressions
   `t_A P_a K P_a` (blocks `a`) and `t_B (P_a K Q_j + Q_j K P_a)` (incident bonds `a ~ j`)
   (`tcv_contract_eq`), each compression of norm `≤ ‖K‖` (`tcv_proj_le`), so
   `‖𝒱(K)‖ ≤ (2t_A + 8t_B)‖K‖ ≤ (10/W)‖K‖` (`tcv_contract_le`).
2. **Regularization** (§2). `G_κ = (𝒢⁻¹ + iκ)⁻¹` (`tcvG`, from `TraceFluctuation`): smooth,
   `‖G_κ‖ ≤ κ⁻¹`, `‖G_κ‖ ≤ 2‖𝒢‖` where `𝒢⁻¹` is invertible, `dG_κ(v) = -G_κ (Λv) G_κ`
   (`tcv_G_hasFDerivAt`) with `Λv` Hermitian (`tcv_lin_herm`). By the word product rule
   (`tcv_word_hasFDerivAt`) the derivatives of `f_κ = W⁻¹ Tr w_f(G_κ)` and
   `U_κ = w_U(G_κ)` are `W⁻¹ Tr(Σⱼ aⱼ Λ cⱼ)` and `Σₖ a'ₖ Λ c'ₖ` with
   `‖aⱼ‖‖cⱼ‖ ≤ K^{ℓ+1}‖G_κ‖^{ℓ+1}`.
3. **Fixed `κ`** (§4). `ou_covariance_matrix` (bounded `C¹` class) and the kernel algebra
   (`tcv_kernel_eq`) give the integrand `W⁻¹ Σⱼ Σₖ a'ₖ(x_t) 𝒱(cⱼaⱼ(x)) c'ₖ(x_t)`, bounded by
   `(10 ℓ_f ℓ_U K^n / W²)(‖G_κ(x)‖^n + ‖G_κ(x_t)‖^n)`, `n = ℓ_f + ℓ_U + 2` (`tcv_kernel_le`,
   AM–GM `tcv_pow_mul_le`); `x_t ∼ μ` under `μ ⊗ μ` (`tcv_integral_interp`, rotation
   invariance), so `‖Cov(f_κ, U_κ)‖ ≤ (10 ℓ_f ℓ_U K^n / W²) · 2E‖G_κ‖^n` (`tcv_cov_reg`).
4. **`κ → 0`** (§5). `G_κ → 𝒢` a.s.; dominated convergence with majorants `C‖𝒢‖^m`,
   `m ≤ ℓ_f + ℓ_U`, and `E‖G_κ‖^n ≤ 2^n E‖𝒢‖^n ≤ (2C_A)^n` (`tcv_moment`, `n ≤ 2L+2 ≤ ε₁W`):
   `tcv_core`. The integrability clauses follow from the same majorants.

Constants: `W₀ = ⌈(2L+2)/ε₁⌉₊`, `C = tcvConst L K C_A = Σ_{ℓ_f,ℓ_U ≤ L} 20 ℓ_f ℓ_U |K|^n (2C_A)^n`
(`ε₁, C_A` from `GaussianAbsorptionContract b η₀ M`, depending only on `b, η₀, M`), uniform
in `W ≥ W₀`, the shape, Hermitian `X`, real `E`, `Im z ≥ η₀`, `|z| ≤ M` and the words.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open BlockBand.Internal.Contracts.CoareaPalm (gueSample)
open BlockBand.SourceProcess (circularBrownianCoordinates)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. The covariance contraction `𝒱(K)`
-/

section Contraction

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem tcv_pair (K : Matrix n n ℂ) (u v : n) (q : ℝ) :
    (K * ((q : ℂ) • (single u v 1 + single v u 1))).trace •
        ((q : ℂ) • (single u v 1 + single v u 1)) +
      (K * ((q : ℂ) • (Complex.I • single u v 1 - Complex.I • single v u 1))).trace •
        ((q : ℂ) • (Complex.I • single u v 1 - Complex.I • single v u 1)) =
      ((2 * q ^ 2 : ℝ) : ℂ) • (K u v • single u v (1 : ℂ) + K v u • single v u 1) := by
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, trace_add, trace_sub, trace_smul,
    trace_mul_single]
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, single_apply, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  push_cast
  split_ifs <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem tcv_projector_le {ι : Type*} [Fintype ι] {f : ι → n} (hf : Function.Injective f) :
    ‖∑ i, single (f i) (f i) (1 : ℂ)‖ ≤ 1 := by
  set P := ∑ i, single (f i) (f i) (1 : ℂ) with hPdef
  have hidem : P * P = P := by
    rw [hPdef, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [single_mul_single_same, one_mul]
    · intro j _ hji
      exact single_mul_single_of_ne (h := fun h => hji (hf h).symm) ..
    · intro h; exact absurd (Finset.mem_univ i) h
  have hherm : Pᴴ = P := by
    rw [hPdef, conjTranspose_sum]
    simp [conjTranspose_single]
  have h1 : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hherm, hidem]
  have h0 := norm_nonneg P
  nlinarith

theorem tcv_proj_le {ι κ : Type*} [Fintype ι] [Fintype κ] (K : Matrix n n ℂ) {f : ι → n}
    {g : κ → n} (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖∑ i, ∑ j, K (f i) (g j) • single (f i) (g j) (1 : ℂ)‖ ≤ ‖K‖ := by
  have heq : ∑ i, ∑ j, K (f i) (g j) • single (f i) (g j) (1 : ℂ) =
      (∑ i, single (f i) (f i) (1 : ℂ)) * K * ∑ j, single (g j) (g j) (1 : ℂ) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [single_mul_mul_single, smul_single, smul_eq_mul, one_mul, mul_one]
  rw [heq]
  set P := ∑ i, single (f i) (f i) (1 : ℂ)
  set Q := ∑ j, single (g j) (g j) (1 : ℂ)
  have h1 : ‖P‖ ≤ 1 := tcv_projector_le hf
  have h2 : ‖Q‖ ≤ 1 := tcv_projector_le hg
  have h3 : ‖P * K * Q‖ ≤ ‖P‖ * ‖K‖ * ‖Q‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have hK := norm_nonneg K
  have hP0 := norm_nonneg P
  have hQ0 := norm_nonneg Q
  calc ‖P * K * Q‖ ≤ ‖P‖ * ‖K‖ * ‖Q‖ := h3
    _ ≤ 1 * ‖K‖ * 1 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right h1 hK) h2 hQ0 (by positivity)
    _ = ‖K‖ := by ring

section Coord
variable (W : ℕ) (b : ℝ) (σ : LayerShape)

theorem tcv_coordA0 (a : Fin σ.blocks) (α β : Fin W) :
    tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), 0))) 1) =
      ((Real.sqrt ((tflTA W b : ℝ) / 2) / Real.sqrt 2 : ℝ) : ℂ) •
        (single (Sum.inl (a, α)) (Sum.inl (a, β)) 1 +
          single (Sum.inl (a, β)) (Sum.inl (a, α)) 1) := by
  ext i j
  rcases i with ⟨a', α'⟩ | ⟨a', α'⟩ <;> rcases j with ⟨c, β'⟩ | ⟨c, β'⟩ <;>
    simp [tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords,
      gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble, Pi.single_apply,
      Matrix.single_apply, ite_and]
  split_ifs <;> (try subst_vars) <;> simp_all <;> ring

theorem tcv_coordA1 (a : Fin σ.blocks) (α β : Fin W) :
    tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), 1))) 1) =
      ((Real.sqrt ((tflTA W b : ℝ) / 2) / Real.sqrt 2 : ℝ) : ℂ) •
        (Complex.I • single (Sum.inl (a, α)) (Sum.inl (a, β)) 1 -
          Complex.I • single (Sum.inl (a, β)) (Sum.inl (a, α)) 1) := by
  ext i j
  rcases i with ⟨a', α'⟩ | ⟨a', α'⟩ <;> rcases j with ⟨c, β'⟩ | ⟨c, β'⟩ <;>
    simp [tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords,
      gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble, Pi.single_apply,
      Matrix.single_apply, ite_and]
  split_ifs <;> (try subst_vars) <;> simp_all <;> (ring_nf; try simp)

theorem tcv_coordB0 (a : Fin σ.blocks) (j : Fin σ.ports) (α β : Fin W) :
    tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, 0)) 1) =
      ((if σ.incident a j then 1 else 0 : ℝ) : ℂ) •
        (single (Sum.inl (a, α)) (Sum.inr (j, β)) 1 +
          single (Sum.inr (j, β)) (Sum.inl (a, α)) 1) := by
  ext i j
  rcases i with ⟨a', α'⟩ | ⟨a', α'⟩ <;> rcases j with ⟨c, β'⟩ | ⟨c, β'⟩ <;>
    simp [tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords,
      gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble, Pi.single_apply,
      Matrix.single_apply, ite_and]
  all_goals (split_ifs <;> (try subst_vars) <;> simp_all)

theorem tcv_coordB1 (a : Fin σ.blocks) (j : Fin σ.ports) (α β : Fin W) :
    tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, 1)) 1) =
      ((if σ.incident a j then 1 else 0 : ℝ) : ℂ) •
        (Complex.I • single (Sum.inl (a, α)) (Sum.inr (j, β)) 1 -
          Complex.I • single (Sum.inr (j, β)) (Sum.inl (a, α)) 1) := by
  ext i j
  rcases i with ⟨a', α'⟩ | ⟨a', α'⟩ <;> rcases j with ⟨c, β'⟩ | ⟨c, β'⟩ <;>
    simp [tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords,
      gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble, Pi.single_apply,
      Matrix.single_apply, ite_and]
  all_goals (split_ifs <;> (try subst_vars) <;> simp_all)

theorem tcv_pairA (K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (a : Fin σ.blocks) (α β : Fin W) :
    (((tflVar W b σ (Sum.inl (a, ((α, β), 0))) : ℝ) : ℂ) *
        (K * tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), 0))) 1)).trace) •
        tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), 0))) 1) +
      (((tflVar W b σ (Sum.inl (a, ((α, β), 1))) : ℝ) : ℂ) *
        (K * tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), 1))) 1)).trace) •
        tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), 1))) 1) =
      (((tflTA W b : ℝ) / 2 : ℝ) : ℂ) •
        (K (Sum.inl (a, α)) (Sum.inl (a, β)) • single (Sum.inl (a, α)) (Sum.inl (a, β)) (1 : ℂ) +
          K (Sum.inl (a, β)) (Sum.inl (a, α)) • single (Sum.inl (a, β)) (Sum.inl (a, α)) 1) := by
  rw [tcv_coordA0, tcv_coordA1]
  simp only [tflVar, Sum.elim_inl, NNReal.coe_one, Complex.ofReal_one, one_mul]
  rw [tcv_pair]
  congr 2
  have ht := (tflTA W b).2
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
  ring

theorem tcv_pairB (K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (a : Fin σ.blocks)
    (j : Fin σ.ports) (α β : Fin W) :
    (((tflVar W b σ (Sum.inr (a, j, α, β, 0)) : ℝ) : ℂ) *
        (K * tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, 0)) 1)).trace) •
        tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, 0)) 1) +
      (((tflVar W b σ (Sum.inr (a, j, α, β, 1)) : ℝ) : ℂ) *
        (K * tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, 1)) 1)).trace) •
        tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, 1)) 1) =
      (((tflTB W b : ℝ) * (if σ.incident a j then 1 else 0) : ℝ) : ℂ) •
        (K (Sum.inl (a, α)) (Sum.inr (j, β)) • single (Sum.inl (a, α)) (Sum.inr (j, β)) (1 : ℂ) +
          K (Sum.inr (j, β)) (Sum.inl (a, α)) • single (Sum.inr (j, β)) (Sum.inl (a, α)) 1) := by
  rw [tcv_coordB0, tcv_coordB1]
  simp only [tflVar, Sum.elim_inr, mul_smul]
  rw [← smul_add, tcv_pair, smul_smul]
  congr 1
  split_ifs <;> simp

/-- The covariance contraction `𝒱(K) = Σᵢ vᵢ Tr(K Λᵢ) Λᵢ`, `Λᵢ = ∂ᵢ 𝒢⁻¹`. -/
def tcvContract (K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  ∑ i, (((tflVar W b σ i : ℝ) : ℂ) * (K * tflLin W b σ (Pi.single i 1)).trace) •
    tflLin W b σ (Pi.single i 1)

theorem tcv_contract_eq (K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    tcvContract W b σ K =
      (∑ a : Fin σ.blocks, ∑ α : Fin W, ∑ β : Fin W, (((tflTA W b : ℝ) / 2 : ℝ) : ℂ) •
        (K (Sum.inl (a, α)) (Sum.inl (a, β)) • single (Sum.inl (a, α)) (Sum.inl (a, β)) (1 : ℂ) +
          K (Sum.inl (a, β)) (Sum.inl (a, α)) • single (Sum.inl (a, β)) (Sum.inl (a, α)) 1)) +
      ∑ a : Fin σ.blocks, ∑ j : Fin σ.ports, ∑ α : Fin W, ∑ β : Fin W,
        (((tflTB W b : ℝ) * (if σ.incident a j then 1 else 0) : ℝ) : ℂ) •
        (K (Sum.inl (a, α)) (Sum.inr (j, β)) • single (Sum.inl (a, α)) (Sum.inr (j, β)) (1 : ℂ) +
          K (Sum.inr (j, β)) (Sum.inl (a, α)) • single (Sum.inr (j, β)) (Sum.inl (a, α)) 1) := by
  rw [tcvContract, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, tcv_pairA, tcv_pairB]

omit [Fintype n] in
theorem tcv_inl_injective (a : Fin σ.blocks) :
    Function.Injective (fun α : Fin W => (Sum.inl (a, α) : LayerSite W σ)) :=
  fun _ _ h => by simpa using h

theorem tcv_inr_injective (j : Fin σ.ports) :
    Function.Injective (fun β : Fin W => (Sum.inr (j, β) : LayerSite W σ)) :=
  fun _ _ h => by simpa using h

/-- Norm of one symmetrized block of the contraction. -/
theorem tcv_sym_le (K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {f g : Fin W → LayerSite W σ}
    (hf : Function.Injective f) (hg : Function.Injective g) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ α : Fin W, ∑ β : Fin W, (c : ℂ) •
        (K (f α) (g β) • single (f α) (g β) (1 : ℂ) + K (g β) (f α) • single (g β) (f α) 1)‖ ≤
      2 * c * ‖K‖ := by
  have heq : ∑ α : Fin W, ∑ β : Fin W, (c : ℂ) •
      (K (f α) (g β) • single (f α) (g β) (1 : ℂ) + K (g β) (f α) • single (g β) (f α) 1) =
      (c : ℂ) • ((∑ α : Fin W, ∑ β : Fin W, K (f α) (g β) • single (f α) (g β) (1 : ℂ)) +
        ∑ β : Fin W, ∑ α : Fin W, K (g β) (f α) • single (g β) (f α) (1 : ℂ)) := by
    rw [Finset.sum_comm (f := fun β α => K (g β) (f α) • single (g β) (f α) (1 : ℂ))]
    simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib]
  rw [heq, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
  have h1 := tcv_proj_le K hf hg
  have h2 := tcv_proj_le K hg hf
  have h3 := norm_add_le (∑ α : Fin W, ∑ β : Fin W, K (f α) (g β) • single (f α) (g β) (1 : ℂ))
    (∑ β : Fin W, ∑ α : Fin W, K (g β) (f α) • single (g β) (f α) (1 : ℂ))
  nlinarith

/-- **The contraction lemma** (in the paper: `‖𝒱(K)‖ ≤ C‖K‖` with the covariance
`O(W⁻¹)`): `‖Σᵢ vᵢ Tr(K Λᵢ) Λᵢ‖ ≤ (10/W) ‖K‖`. -/
theorem tcv_contract_le (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ‖tcvContract W b σ K‖ ≤ 10 / W * ‖K‖ := by
  obtain ⟨hA, hB⟩ := tfl_TA_TB_le hW hb0 hb1
  have htA := (tflTA W b).2
  have htB := (tflTB W b).2
  have hK := norm_nonneg K
  have hbl : (σ.blocks : ℝ) ≤ 2 := by
    have : σ.blocks ≤ 2 := by cases σ <;> decide
    exact_mod_cast this
  have hpo : (σ.ports : ℝ) ≤ 2 := by
    have : σ.ports ≤ 2 := by cases σ <;> decide
    exact_mod_cast this
  rw [tcv_contract_eq]
  refine (norm_add_le _ _).trans ?_
  have hPA : ‖(∑ a : Fin σ.blocks, ∑ α : Fin W, ∑ β : Fin W, (((tflTA W b : ℝ) / 2 : ℝ) : ℂ) •
        (K (Sum.inl (a, α)) (Sum.inl (a, β)) • single (Sum.inl (a, α)) (Sum.inl (a, β)) (1 : ℂ) +
          K (Sum.inl (a, β)) (Sum.inl (a, α)) • single (Sum.inl (a, β)) (Sum.inl (a, α)) 1) :
          Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤
      σ.blocks * ((tflTA W b : ℝ) * ‖K‖) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _a : Fin σ.blocks, (tflTA W b : ℝ) * ‖K‖ := by
          refine Finset.sum_le_sum fun a _ => ?_
          have := tcv_sym_le W σ K (tcv_inl_injective W σ a) (tcv_inl_injective W σ a)
            ((tflTA W b : ℝ) / 2) (by positivity)
          linarith
      _ = _ := by simp
  have hPB : ‖(∑ a : Fin σ.blocks, ∑ j : Fin σ.ports, ∑ α : Fin W, ∑ β : Fin W,
        (((tflTB W b : ℝ) * (if σ.incident a j then 1 else 0) : ℝ) : ℂ) •
        (K (Sum.inl (a, α)) (Sum.inr (j, β)) • single (Sum.inl (a, α)) (Sum.inr (j, β)) (1 : ℂ) +
          K (Sum.inr (j, β)) (Sum.inl (a, α)) • single (Sum.inr (j, β)) (Sum.inl (a, α)) 1) :
          Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤
      σ.blocks * (σ.ports * (2 * (tflTB W b : ℝ) * ‖K‖)) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _a : Fin σ.blocks, σ.ports * (2 * (tflTB W b : ℝ) * ‖K‖) := by
          refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans ?_
          calc _ ≤ ∑ _j : Fin σ.ports, 2 * (tflTB W b : ℝ) * ‖K‖ := by
                refine Finset.sum_le_sum fun j _ => ?_
                have hc0 : (0 : ℝ) ≤ (tflTB W b : ℝ) * (if σ.incident a j then 1 else 0) := by
                  split_ifs <;> simp
                have hc1 : (tflTB W b : ℝ) * (if σ.incident a j then 1 else 0) ≤ tflTB W b := by
                  split_ifs <;> simp
                have := tcv_sym_le W σ K (tcv_inl_injective W σ a) (tcv_inr_injective W σ j)
                  _ hc0
                nlinarith
            _ = _ := by simp
      _ = _ := by simp
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have e10 : 10 / (W : ℝ) * ‖K‖ = 2 * (1 / W * ‖K‖) + 8 * (1 / W * ‖K‖) := by ring
  rw [e10]
  have hAK : (tflTA W b : ℝ) * ‖K‖ ≤ 1 / W * ‖K‖ := mul_le_mul_of_nonneg_right hA hK
  have hBK : (tflTB W b : ℝ) * ‖K‖ ≤ 1 / W * ‖K‖ := mul_le_mul_of_nonneg_right hB hK
  have hAK0 : 0 ≤ (tflTA W b : ℝ) * ‖K‖ := by positivity
  have hBK0 : 0 ≤ (tflTB W b : ℝ) * ‖K‖ := by positivity
  have hbl0 : (0 : ℝ) ≤ σ.blocks := by positivity
  have hpo0 : (0 : ℝ) ≤ σ.ports := by positivity
  have h1 : (σ.blocks : ℝ) * ((tflTA W b : ℝ) * ‖K‖) ≤ 2 * (1 / W * ‖K‖) :=
    mul_le_mul hbl hAK hAK0 (by norm_num)
  have h2 : (σ.blocks : ℝ) * (σ.ports * (2 * (tflTB W b : ℝ) * ‖K‖)) ≤ 8 * (1 / W * ‖K‖) := by
    have h3 : (σ.ports : ℝ) * (2 * (tflTB W b : ℝ) * ‖K‖) ≤ 2 * (2 * (1 / W * ‖K‖)) :=
      mul_le_mul hpo (by linarith) (by positivity) (by norm_num)
    calc (σ.blocks : ℝ) * (σ.ports * (2 * (tflTB W b : ℝ) * ‖K‖))
        ≤ 2 * (2 * (2 * (1 / W * ‖K‖))) := mul_le_mul hbl h3 (by positivity) (by norm_num)
      _ = 8 * (1 / W * ‖K‖) := by ring
  linarith

end Coord

end Contraction

/-!
## 2. The regularized resolvent and its words in the real coordinates
-/

section Regularized

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)

/-- The regularized resolvent `G_κ(x) = (𝒢⁻¹ + iκ)⁻¹` in the real coordinates. -/
def tcvG (κ : ℝ) (x : TflCoord W σ → ℝ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  Ring.inverse (tflPsi W b σ E z X κ x)

/-- The coordinate derivative `Λ v = ∂_v 𝒢⁻¹` as a continuous linear map. -/
def tcvLam : (TflCoord W σ → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  LinearMap.toContinuousLinearMap (tflLinMap W b σ)

theorem tcvLam_apply (v : TflCoord W σ → ℝ) : tcvLam W b σ v = tflLin W b σ v := rfl

/-- Every coordinate direction of the layer matrix is Hermitian. -/
theorem tcv_lin_herm (v : TflCoord W σ → ℝ) : (tflLin W b σ v)ᴴ = tflLin W b σ v := by
  have h : (tflLin W b σ v).IsHermitian :=
    IsHermitian.fromBlocks (tflEmbed_blockDiag_isHermitian W b σ v) rfl (by simp [IsHermitian])
  exact h

variable {X} in
theorem tcv_G_contDiff (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ 1 (tcvG W b σ E z X κ) := by
  have hL : ContDiff ℝ 1 (tflPsi W b σ E z X κ) :=
    contDiff_const.add (ContinuousLinearMap.contDiff _)
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have h := contDiffAt_ringInverse ℝ (n := 1) (tflPsi_isUnit W b σ E z hX hz hκ x).unit
  rw [IsUnit.unit_spec] at h
  exact h.comp x hL.contDiffAt

variable {X} in
/-- `d G_κ (v) = -G_κ (Λ v) G_κ`. -/
theorem tcv_G_hasFDerivAt (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) :
    ∃ T : (TflCoord W σ → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      HasFDerivAt (tcvG W b σ E z X κ) T x ∧
        ∀ v, T v = -(tcvG W b σ E z X κ x * tcvLam W b σ v * tcvG W b σ E z X κ x) := by
  set u := (tflPsi_isUnit W b σ E z hX hz hκ x).unit with hu
  have hL : HasFDerivAt (tflPsi W b σ E z X κ) (tcvLam W b σ) x :=
    (ContinuousLinearMap.hasFDerivAt _).const_add _
  have h : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) ↑u⁻¹ ↑u⁻¹))
      (tflPsi W b σ E z X κ x) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rwa [IsUnit.unit_spec] at this
  have hinv : (↑u⁻¹ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) = tcvG W b σ E z X κ x := by
    rw [tcvG, ← Ring.inverse_unit, IsUnit.unit_spec]
  refine ⟨_, h.comp x hL, fun v => ?_⟩
  simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, hinv]

variable {X} in
theorem tcv_G_le (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) : ‖tcvG W b σ E z X κ x‖ ≤ κ⁻¹ :=
  tflPsi_inv_le W b σ E z hX hz hκ x

/-- The normalized trace `N ↦ W⁻¹ Tr N` (real-linear). -/
def tcvTrLin : Matrix (LayerSite W σ) (LayerSite W σ) ℂ →ₗ[ℝ] ℂ where
  toFun N := (W : ℂ)⁻¹ * N.trace
  map_add' N N' := by simp [Matrix.trace_add, mul_add]
  map_smul' r N := by simp [Matrix.trace_smul]; ring

/-- The normalized trace as a continuous linear map. -/
def tcvTr : Matrix (LayerSite W σ) (LayerSite W σ) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (tcvTrLin W σ)

theorem tcvTr_apply (N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    tcvTr W σ N = (W : ℂ)⁻¹ * N.trace := rfl

variable {W} in
/-- `|W⁻¹ Tr N| ≤ 4 ‖N‖`. -/
theorem tcv_tr_le (hW : 0 < W) (N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ‖tcvTr W σ N‖ ≤ 4 * ‖N‖ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [tcvTr_apply, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 := tfl_trace_le N
  have h2 := tfl_card_layerSite_le W σ
  calc (W : ℝ)⁻¹ * ‖N.trace‖ ≤ (W : ℝ)⁻¹ * (4 * W * ‖N‖) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ = 4 * ‖N‖ := by field_simp

/-- The entry functional `N ↦ N x y` as a continuous linear map. -/
def tcvEntry (x y : LayerSite W σ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun N => N x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem tcvEntry_apply (x y : LayerSite W σ) (N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    tcvEntry W σ x y N = N x y := rfl

end Regularized

/-!
## 3. Generic estimates: kernel algebra, AM–GM, moments, the law of `x_t`
-/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Reordering a triple sum. -/
theorem tcv_sum_rot {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (u : Finset γ) (F : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, F a b c = ∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, F a b c := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]

omit [DecidableEq n] in
/-- **Kernel algebra.** With `∂ᵢ f = w Tr(Σⱼ aⱼ Λᵢ cⱼ)` and `∂ᵢ U = Σₖ a'ₖ Λᵢ c'ₖ`,
`Σᵢ sᵢ ∂ᵢ f ∂ᵢ U = w Σⱼ Σₖ a'ₖ (Σᵢ sᵢ Tr((cⱼ aⱼ) Λᵢ) Λᵢ) c'ₖ`. -/
theorem tcv_kernel_eq {ι : Type*} [Fintype ι] (s : ι → ℂ) (Λ : ι → Matrix n n ℂ) (w : ℂ)
    {ℓf ℓU : ℕ} (a c : Fin ℓf → Matrix n n ℂ) (a' c' : Fin ℓU → Matrix n n ℂ) :
    ∑ i, (s i * (w * (∑ j, a j * Λ i * c j).trace)) • (∑ k, a' k * Λ i * c' k) =
      w • ∑ j, ∑ k, a' k * (∑ i, (s i * (c j * a j * Λ i).trace) • Λ i) * c' k := by
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum,
    smul_smul, trace_sum, Finset.sum_smul]
  rw [tcv_sum_rot]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => ?_
  rw [trace_mul_cycle (a j)]
  congr 1
  ring

/-- `u^a w^b ≤ u^{a+b} + w^{a+b}` for `u, w ≥ 0`. -/
theorem tcv_pow_mul_le {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) (a c : ℕ) :
    u ^ a * w ^ c ≤ u ^ (a + c) + w ^ (a + c) := by
  rcases le_total u w with h | h
  · have h1 : u ^ a ≤ w ^ a := pow_le_pow_left₀ hu h a
    have h2 : u ^ a * w ^ c ≤ w ^ a * w ^ c := mul_le_mul_of_nonneg_right h1 (by positivity)
    rw [← pow_add] at h2
    have : 0 ≤ u ^ (a + c) := by positivity
    linarith
  · have h1 : w ^ c ≤ u ^ c := pow_le_pow_left₀ hw h c
    have h2 : u ^ a * w ^ c ≤ u ^ a * u ^ c := mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [← pow_add] at h2
    have : 0 ≤ w ^ (a + c) := by positivity
    linarith

/-- Integer moments from an `L^m` bound: `E‖F‖^m ≤ C^m`. -/
theorem tcv_moment {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F] {μ : Measure Ω}
    {G : Ω → F} {m : ℕ} (hm : 1 ≤ m) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm (fun ω => ‖G ω‖) (ENNReal.ofReal m) μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ‖G ω‖ ^ m) μ ∧ ∫ ω, ‖G ω‖ ^ m ∂μ ≤ C ^ m := by
  have hm0 : m ≠ 0 := by omega
  rw [ENNReal.ofReal_natCast] at h
  have hmem : MemLp (fun ω => ‖G ω‖) (m : ℝ≥0∞) μ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hint : Integrable (fun ω => ‖G ω‖ ^ m) μ := by
    simpa only [norm_norm] using hmem.integrable_norm_pow hm0
  refine ⟨hint, ?_⟩
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hm0) (ENNReal.natCast_ne_top m)] at h
  simp only [norm_norm, ENNReal.toReal_natCast, Real.rpow_natCast] at h
  have hI0 : 0 ≤ ∫ ω, ‖G ω‖ ^ m ∂μ := integral_nonneg fun ω => by positivity
  have h1 := (ENNReal.ofReal_le_ofReal_iff hC).mp h
  have h2 : ((∫ ω, ‖G ω‖ ^ m ∂μ) ^ (m : ℝ)⁻¹) ^ m ≤ C ^ m :=
    pow_le_pow_left₀ (by positivity) h1 m
  rwa [Real.rpow_inv_natCast_pow hI0 hm0] at h2

/-- **The law of `x_t`.** Under `μ ⊗ μ`, `e^{-t} x + √(1-e^{-2t}) x'` has law `μ` (`t ≥ 0`). -/
theorem tcv_integral_interp {ι : Type} [Fintype ι] (v : ι → ℝ≥0) {h : (ι → ℝ) → ℝ}
    (hh : Continuous h) {t : ℝ} (ht : 0 ≤ t) :
    ∫ p, h (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
        ∂(gaussianProduct v).prod (gaussianProduct v) = ∫ x, h x ∂gaussianProduct v := by
  have hc01 : Real.exp (-t) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hθc : Real.cos (Real.arccos (Real.exp (-t))) = Real.exp (-t) :=
    Real.cos_arccos (by linarith [(Real.exp_pos (-t)).le]) hc01
  have hθs : Real.sin (Real.arccos (Real.exp (-t))) = Real.sqrt (1 - Real.exp (-2 * t)) := by
    rw [Real.sin_arccos, ou_exp_sq]
  have hG : AEStronglyMeasurable (fun p : (ι → ℝ) × (ι → ℝ) => h p.1)
      ((gaussianProduct v).prod (gaussianProduct v)) :=
    (hh.comp continuous_fst).aestronglyMeasurable
  have h1 := ou_integral_rotation v (Real.arccos (Real.exp (-t))) hG
  simp only [ContinuousLinearMap.rotation_apply, hθc, hθs] at h1
  rw [h1, integral_fun_fst, probReal_univ, one_smul]

end Generic

/-!
## 4. The covariance bound for a fixed regularization `κ > 0`
-/

section FixedKappa

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)

variable {W b} in
/-- **Pointwise kernel bound**: with `‖aⱼ‖‖cⱼ‖ ≤ B_f`, `‖a'ₖ‖‖c'ₖ‖ ≤ B_U`,
`‖W⁻¹ Σⱼ Σₖ a'ₖ 𝒱(cⱼ aⱼ) c'ₖ‖ ≤ 10 ℓ_f ℓ_U B_f B_U / W²`. -/
theorem tcv_kernel_le (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) {ℓf ℓU : ℕ}
    (a c : Fin ℓf → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (a' c' : Fin ℓU → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {Bf BU : ℝ} (hBf0 : 0 ≤ Bf)
    (hBf : ∀ j, ‖a j‖ * ‖c j‖ ≤ Bf) (hBU : ∀ k, ‖a' k‖ * ‖c' k‖ ≤ BU) :
    ‖((W : ℂ)⁻¹) • ∑ j, ∑ k, a' k * tcvContract W b σ (c j * a j) * c' k‖ ≤
      10 * ℓf * ℓU * Bf * BU / (W : ℝ) ^ 2 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hterm : ∀ j k, ‖a' k * tcvContract W b σ (c j * a j) * c' k‖ ≤ 10 / W * Bf * BU := by
    intro j k
    have h1 : ‖a' k * tcvContract W b σ (c j * a j) * c' k‖ ≤
        ‖a' k‖ * ‖tcvContract W b σ (c j * a j)‖ * ‖c' k‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    have h2 := tcv_contract_le W b σ hW hb0 hb1 (c j * a j)
    have h3 : ‖c j * a j‖ ≤ ‖c j‖ * ‖a j‖ := norm_mul_le _ _
    have ha := norm_nonneg (a j)
    have hc := norm_nonneg (c j)
    have ha' := norm_nonneg (a' k)
    have hc' := norm_nonneg (c' k)
    have hC0 := norm_nonneg (tcvContract W b σ (c j * a j))
    have h10 : (0 : ℝ) ≤ 10 / W := by positivity
    have h4 : ‖tcvContract W b σ (c j * a j)‖ ≤ 10 / W * (‖a j‖ * ‖c j‖) := by
      refine h2.trans ?_
      rw [mul_comm (‖a j‖)]
      exact mul_le_mul_of_nonneg_left h3 h10
    calc ‖a' k * tcvContract W b σ (c j * a j) * c' k‖
        ≤ ‖a' k‖ * ‖tcvContract W b σ (c j * a j)‖ * ‖c' k‖ := h1
      _ ≤ ‖a' k‖ * (10 / W * (‖a j‖ * ‖c j‖)) * ‖c' k‖ := by gcongr
      _ = 10 / W * (‖a j‖ * ‖c j‖) * (‖a' k‖ * ‖c' k‖) := by ring
      _ ≤ 10 / W * Bf * BU := by
          have := mul_le_mul (hBf j) (hBU k) (by positivity) hBf0
          calc 10 / W * (‖a j‖ * ‖c j‖) * (‖a' k‖ * ‖c' k‖)
              = 10 / W * ((‖a j‖ * ‖c j‖) * (‖a' k‖ * ‖c' k‖)) := by ring
            _ ≤ 10 / W * (Bf * BU) := mul_le_mul_of_nonneg_left this h10
            _ = 10 / W * Bf * BU := by ring
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ j, ∑ k, a' k * tcvContract W b σ (c j * a j) * c' k‖ ≤
      ℓf * (ℓU * (10 / W * Bf * BU)) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _j : Fin ℓf, ℓU * (10 / W * Bf * BU) := by
          refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans ?_
          calc _ ≤ ∑ _k : Fin ℓU, 10 / W * Bf * BU := Finset.sum_le_sum fun k _ => hterm j k
            _ = _ := by simp
      _ = _ := by simp
  calc (W : ℝ)⁻¹ * ‖∑ j, ∑ k, a' k * tcvContract W b σ (c j * a j) * c' k‖
      ≤ (W : ℝ)⁻¹ * (ℓf * (ℓU * (10 / W * Bf * BU))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 10 * ℓf * ℓU * Bf * BU / (W : ℝ) ^ 2 := by field_simp

variable {W b X} in
/-- **The covariance bound at fixed `κ > 0`** (in the real coordinates, `μ = gaussianProduct`):
for the regularized words `f_κ = W⁻¹ Tr w_f(G_κ)`, `U_κ = w_U(G_κ)`,
`‖E(f_κ U_κ) - E f_κ E U_κ‖ ≤ (10 ℓ_f ℓ_U K^n / W²) · 2 E‖G_κ‖^n`, `n = ℓ_f + ℓ_U + 2`
(OU identity, the contraction lemma, AM–GM, and `x_t ∼ μ`). -/
theorem tcv_cov_reg (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) {K : ℝ} (hK : 0 ≤ K) {ℓf ℓU : ℕ}
    (εf : Fin ℓf → Bool) (Df : Fin (ℓf + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (εU : Fin ℓU → Bool) (DU : Fin (ℓU + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (hDf : ∀ j, ‖Df j‖ ≤ K) (hDU : ∀ j, ‖DU j‖ ≤ K) :
    ‖(∫ x, tcvTr W σ (wordEval εf Df (tcvG W b σ E z X κ x)) •
          wordEval εU DU (tcvG W b σ E z X κ x) ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, tcvTr W σ (wordEval εf Df (tcvG W b σ E z X κ x)) ∂gaussianProduct (tflVar W b σ)) •
          (∫ x, wordEval εU DU (tcvG W b σ E z X κ x) ∂gaussianProduct (tflVar W b σ))‖ ≤
      10 * ℓf * ℓU * K ^ (ℓf + ℓU + 2) / (W : ℝ) ^ 2 *
        (2 * ∫ x, ‖tcvG W b σ E z X κ x‖ ^ (ℓf + ℓU + 2) ∂gaussianProduct (tflVar W b σ)) := by
  set v := tflVar W b σ with hv
  set μ := gaussianProduct v with hμ
  set G := tcvG W b σ E z X κ with hGdef
  set Λ := tcvLam W b σ with hΛdef
  set n := ℓf + ℓU + 2 with hn
  set f : (TflCoord W σ → ℝ) → ℂ := fun x => tcvTr W σ (wordEval εf Df (G x)) with hfdef
  set U : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => wordEval εU DU (G x) with hUdef
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hGc : ContDiff ℝ 1 G := tcv_G_contDiff W b σ E z hX hz hκ
  have hGcont : Continuous G := hGc.continuous
  have hGle : ∀ x, ‖G x‖ ≤ κ⁻¹ := tcv_G_le W b σ E z hX hz hκ
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hderG := tcv_G_hasFDerivAt W b σ E z hX hz hκ
  have hΛh : ∀ v', (Λ v')ᴴ = Λ v' := tcv_lin_herm W b σ
  have hfd : ContDiff ℝ 1 f := (tcvTr W σ).contDiff.comp (tcv_contDiff_word hGc εf Df)
  have hUd : ContDiff ℝ 1 U := tcv_contDiff_word hGc εU DU
  -- bounds on the functions and their derivatives
  have hpowle : ∀ (m : ℕ) x, ‖G x‖ ^ m ≤ κ⁻¹ ^ m := fun m x =>
    pow_le_pow_left₀ (norm_nonneg _) (hGle x) m
  have hfC : ∀ x, ‖f x‖ ≤ 4 * (K ^ (ℓf + 1) * κ⁻¹ ^ ℓf) := fun x => by
    refine (tcv_tr_le σ hW _).trans ?_
    gcongr
    exact (tcv_norm_wordEval_le hK εf Df (G x) hDf).trans (by gcongr; exact hGle x)
  have hUC : ∀ x, ‖U x‖ ≤ K ^ (ℓU + 1) * κ⁻¹ ^ ℓU := fun x =>
    (tcv_norm_wordEval_le hK εU DU (G x) hDU).trans (by gcongr; exact hGle x)
  have hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤
      ‖tcvTr W σ‖ * (ℓf * (K ^ (ℓf + 1) * κ⁻¹ ^ (ℓf + 1)) * ‖Λ‖) := fun x => by
    obtain ⟨T, hT, a, c, hTv, hac⟩ := tcv_word_hasFDerivAt hΛh hderG hK x εf Df hDf
    have hfx : HasFDerivAt f ((tcvTr W σ).comp T) x := (tcvTr W σ).hasFDerivAt.comp x hT
    rw [hfx.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    gcongr
    exact tcv_clm_norm_le hTv (by positivity) fun m =>
      (hac m).trans (by gcongr; exact hGle x)
  have hU'C : ∀ x, ‖fderiv ℝ U x‖ ≤ ℓU * (K ^ (ℓU + 1) * κ⁻¹ ^ (ℓU + 1)) * ‖Λ‖ := fun x => by
    obtain ⟨T, hT, a, c, hTv, hac⟩ := tcv_word_hasFDerivAt hΛh hderG hK x εU DU hDU
    rw [hT.fderiv]
    exact tcv_clm_norm_le hTv (by positivity) fun m =>
      (hac m).trans (by gcongr; exact hGle x)
  -- the pointwise kernel bound
  set c₀ : ℝ := 10 * ℓf * ℓU * K ^ n / (W : ℝ) ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hker : ∀ x y : TflCoord W σ → ℝ,
      ‖∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f x (Pi.single i 1)) • fderiv ℝ U y (Pi.single i 1)‖ ≤
        c₀ * (‖G x‖ ^ n + ‖G y‖ ^ n) := by
    intro x y
    obtain ⟨Tf, hTf, a, c, hTfv, hacf⟩ := tcv_word_hasFDerivAt hΛh hderG hK x εf Df hDf
    obtain ⟨TU, hTU, a', c', hTUv, hacU⟩ := tcv_word_hasFDerivAt hΛh hderG hK y εU DU hDU
    have hfx : HasFDerivAt f ((tcvTr W σ).comp Tf) x := (tcvTr W σ).hasFDerivAt.comp x hTf
    have e1 : ∀ i, fderiv ℝ f x (Pi.single i 1) =
        (W : ℂ)⁻¹ * (∑ j, a j * Λ (Pi.single i 1) * c j).trace := fun i => by
      rw [hfx.fderiv, ContinuousLinearMap.comp_apply, hTfv, tcvTr_apply]
    have e2 : ∀ i, fderiv ℝ U y (Pi.single i 1) = ∑ k, a' k * Λ (Pi.single i 1) * c' k :=
      fun i => by rw [hTU.fderiv, hTUv]
    simp_rw [e1, e2]
    rw [tcv_kernel_eq]
    have hk := tcv_kernel_le σ hW hb0 hb1 a c a' c' (Bf := K ^ (ℓf + 1) * ‖G x‖ ^ (ℓf + 1))
      (BU := K ^ (ℓU + 1) * ‖G y‖ ^ (ℓU + 1)) (by positivity) hacf hacU
    refine hk.trans ?_
    have hamgm := tcv_pow_mul_le (norm_nonneg (G x)) (norm_nonneg (G y)) (ℓf + 1) (ℓU + 1)
    have e3 : ℓf + 1 + (ℓU + 1) = n := by omega
    rw [e3] at hamgm
    calc 10 * ℓf * ℓU * (K ^ (ℓf + 1) * ‖G x‖ ^ (ℓf + 1)) *
          (K ^ (ℓU + 1) * ‖G y‖ ^ (ℓU + 1)) / (W : ℝ) ^ 2
        = c₀ * (‖G x‖ ^ (ℓf + 1) * ‖G y‖ ^ (ℓU + 1)) := by
          rw [hc₀, hn, show ℓf + ℓU + 2 = (ℓf + 1) + (ℓU + 1) by omega, pow_add]
          ring
      _ ≤ c₀ * (‖G x‖ ^ n + ‖G y‖ ^ n) := mul_le_mul_of_nonneg_left hamgm hc₀0
  -- integrate in `p` and in `t`
  set I : ℝ := ∫ x, ‖G x‖ ^ n ∂μ with hI
  have hpc : Continuous (fun x => ‖G x‖ ^ n) := (continuous_norm.comp hGcont).pow n
  have hkt : ∀ t : ℝ, 0 < t →
      ‖∫ p, ∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ U (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂μ.prod μ‖ ≤ c₀ * (2 * I) := by
    intro t ht
    set y : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) → (TflCoord W σ → ℝ) :=
      fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2 with hy
    have hyc : Continuous y := by fun_prop
    have hA : Integrable (fun p : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) => ‖G p.1‖ ^ n)
        (μ.prod μ) :=
      ou_integrable_bdd v (hpc.comp continuous_fst) (C := κ⁻¹ ^ n) fun p => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpowle n p.1
    have hB : Integrable (fun p : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) => ‖G (y p)‖ ^ n)
        (μ.prod μ) :=
      ou_integrable_bdd v (hpc.comp hyc) (C := κ⁻¹ ^ n) fun p => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpowle n (y p)
    have hbd := norm_integral_le_of_norm_le ((hA.add hB).const_mul c₀)
      (Eventually.of_forall fun p => hker p.1 (y p))
    refine hbd.trans (le_of_eq ?_)
    rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add hA hB, integral_fun_fst (fun x => ‖G x‖ ^ n),
      probReal_univ, one_smul, tcv_integral_interp v hpc ht.le]
    ring
  rw [ou_covariance_matrix v hfd hfC hf'C hUd hUC hU'C]
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t) * (c₀ * (2 * I))) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).mul_const _
  refine (norm_integral_le_of_norm_le hexp ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hkt t ht) (Real.exp_pos _).le
  · rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]

end FixedKappa

/-!
## 5. The limit `κ → 0` in the real coordinates
-/

section Limit

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)

variable {W b X} in
/-- `G_κ → 𝒢` as `κ → 0` wherever the layer matrix is invertible. -/
theorem tcv_G_tendsto {x : TflCoord W σ → ℝ}
    (hx : IsUnit (layerMatrix σ E z X (tflEmbed W b σ x)).det) {κm : ℕ → ℝ}
    (hκlim : Tendsto κm atTop (𝓝 0)) :
    Tendsto (fun m => tcvG W b σ E z X (κm m) x) atTop
      (𝓝 (layerResolvent σ E z X (tflEmbed W b σ x))) := by
  set N := layerMatrix σ E z X (tflEmbed W b σ x) with hN
  have hU : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr hx
  have hcN : Continuous (fun κ : ℝ => N + ((κ : ℂ) * Complex.I) •
      (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) := by fun_prop
  have h1 : Tendsto (fun m => tflPsi W b σ E z X (κm m) x) atTop (𝓝 N) := by
    have := (hcN.tendsto 0).comp hκlim
    simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
    refine this.congr fun m => ?_
    simp only [Function.comp_apply]
    rw [tflPsi_eq, tflReg]
  have hc := NormedRing.inverse_continuousAt hU.unit
  rw [IsUnit.unit_spec] at hc
  have h2 := hc.tendsto.comp h1
  rw [layerResolvent, ← hN, Matrix.nonsing_inv_eq_ringInverse]
  exact h2

variable {W b X} in
/-- **The covariance bound in the real coordinates** (`κ → 0` by dominated convergence), with
the a.e. invertibility and the integer moments `E‖𝒢‖^m ≤ C_A^m`, `1 ≤ m ≤ ℓ_f + ℓ_U + 2`, as
hypotheses. -/
theorem tcv_core (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) {K : ℝ} (hK : 0 ≤ K) {ℓf ℓU : ℕ}
    (εf : Fin ℓf → Bool) (Df : Fin (ℓf + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (εU : Fin ℓU → Bool) (DU : Fin (ℓU + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (hDf : ∀ j, ‖Df j‖ ≤ K) (hDU : ∀ j, ‖DU j‖ ≤ K)
    (hinv : ∀ᵐ x ∂gaussianProduct (tflVar W b σ),
      IsUnit (layerMatrix σ E z X (tflEmbed W b σ x)).det)
    {CA : ℝ}
    (hmom : ∀ m : ℕ, 1 ≤ m → m ≤ ℓf + ℓU + 2 →
      Integrable (fun x => ‖layerResolvent σ E z X (tflEmbed W b σ x)‖ ^ m)
        (gaussianProduct (tflVar W b σ)) ∧
      ∫ x, ‖layerResolvent σ E z X (tflEmbed W b σ x)‖ ^ m ∂gaussianProduct (tflVar W b σ) ≤
        CA ^ m) :
    Integrable (fun x => tcvTr W σ (wordEval εf Df (layerResolvent σ E z X (tflEmbed W b σ x))))
        (gaussianProduct (tflVar W b σ)) ∧
      Integrable (fun x => wordEval εU DU (layerResolvent σ E z X (tflEmbed W b σ x)))
        (gaussianProduct (tflVar W b σ)) ∧
      Integrable (fun x => tcvTr W σ (wordEval εf Df (layerResolvent σ E z X (tflEmbed W b σ x))) •
          wordEval εU DU (layerResolvent σ E z X (tflEmbed W b σ x)))
        (gaussianProduct (tflVar W b σ)) ∧
      ‖(∫ x, tcvTr W σ (wordEval εf Df (layerResolvent σ E z X (tflEmbed W b σ x))) •
            wordEval εU DU (layerResolvent σ E z X (tflEmbed W b σ x))
              ∂gaussianProduct (tflVar W b σ)) -
          (∫ x, tcvTr W σ (wordEval εf Df (layerResolvent σ E z X (tflEmbed W b σ x)))
              ∂gaussianProduct (tflVar W b σ)) •
            (∫ x, wordEval εU DU (layerResolvent σ E z X (tflEmbed W b σ x))
              ∂gaussianProduct (tflVar W b σ))‖ ≤
        10 * ℓf * ℓU * K ^ (ℓf + ℓU + 2) / (W : ℝ) ^ 2 *
          (2 * (2 * CA) ^ (ℓf + ℓU + 2)) := by
  set v := tflVar W b σ with hv
  set μ := gaussianProduct v with hμ
  set n := ℓf + ℓU + 2 with hn
  set Gr : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (tflEmbed W b σ x) with hGrdef
  have hGr : Measurable Gr :=
    (measurable_layerResolvent σ E z X).comp (tfl_measurable_embed W b σ)
  have hpow : ∀ m : ℕ, m ≤ n → Integrable (fun x => ‖Gr x‖ ^ m) μ := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp only [pow_zero]; exact integrable_const _
    · exact (hmom m h0 hm).1
  set F : (TflCoord W σ → ℝ) → ℂ := fun x => tcvTr W σ (wordEval εf Df (Gr x)) with hFdef
  set U : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => wordEval εU DU (Gr x) with hUdef
  have hFc : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      tcvTr W σ (wordEval εf Df N)) :=
    (tcvTr W σ).continuous.comp (tcv_continuous_wordEval εf Df)
  have hUc : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      wordEval εU DU N) := tcv_continuous_wordEval εU DU
  have hFm : AEStronglyMeasurable F μ := (hFc.measurable.comp hGr).aestronglyMeasurable
  have hUm : AEStronglyMeasurable U μ := (hUc.measurable.comp hGr).aestronglyMeasurable
  -- the dominating functions
  set cF : ℝ := 4 * K ^ (ℓf + 1) * 2 ^ ℓf with hcF
  set cU : ℝ := K ^ (ℓU + 1) * 2 ^ ℓU with hcU
  have hFle : ∀ {N M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}, ‖N‖ ≤ 2 * ‖M‖ →
      ‖tcvTr W σ (wordEval εf Df N)‖ ≤ cF * ‖M‖ ^ ℓf := by
    intro N M h
    refine (tcv_tr_le σ hW _).trans ?_
    have h1 := tcv_norm_wordEval_le hK εf Df N hDf
    have h2 : ‖N‖ ^ ℓf ≤ (2 * ‖M‖) ^ ℓf := pow_le_pow_left₀ (norm_nonneg _) h ℓf
    calc 4 * ‖wordEval εf Df N‖ ≤ 4 * (K ^ (ℓf + 1) * (2 * ‖M‖) ^ ℓf) := by
          gcongr; exact h1.trans (by gcongr)
      _ = cF * ‖M‖ ^ ℓf := by rw [hcF, mul_pow]; ring
  have hUle : ∀ {N M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}, ‖N‖ ≤ 2 * ‖M‖ →
      ‖wordEval εU DU N‖ ≤ cU * ‖M‖ ^ ℓU := by
    intro N M h
    have h1 := tcv_norm_wordEval_le hK εU DU N hDU
    have h2 : ‖N‖ ^ ℓU ≤ (2 * ‖M‖) ^ ℓU := pow_le_pow_left₀ (norm_nonneg _) h ℓU
    calc ‖wordEval εU DU N‖ ≤ K ^ (ℓU + 1) * (2 * ‖M‖) ^ ℓU := h1.trans (by gcongr)
      _ = cU * ‖M‖ ^ ℓU := by rw [hcU, mul_pow]; ring
  have hself : ∀ M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖M‖ ≤ 2 * ‖M‖ := fun M => by
    linarith [norm_nonneg M]
  have hFint : Integrable F μ :=
    Integrable.mono' ((hpow ℓf (by omega)).const_mul cF) hFm
      (Eventually.of_forall fun x => hFle (hself (Gr x)))
  have hUint : Integrable U μ :=
    Integrable.mono' ((hpow ℓU (by omega)).const_mul cU) hUm
      (Eventually.of_forall fun x => hUle (hself (Gr x)))
  have hFUle : ∀ {N M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}, ‖N‖ ≤ 2 * ‖M‖ →
      ‖tcvTr W σ (wordEval εf Df N) • wordEval εU DU N‖ ≤ (cF * cU) * ‖M‖ ^ (ℓf + ℓU) := by
    intro N M h
    rw [norm_smul, pow_add]
    calc ‖tcvTr W σ (wordEval εf Df N)‖ * ‖wordEval εU DU N‖
        ≤ (cF * ‖M‖ ^ ℓf) * (cU * ‖M‖ ^ ℓU) :=
          mul_le_mul (hFle h) (hUle h) (norm_nonneg _) (by positivity)
      _ = cF * cU * (‖M‖ ^ ℓf * ‖M‖ ^ ℓU) := by ring
  have hFUint : Integrable (fun x => F x • U x) μ :=
    Integrable.mono' ((hpow (ℓf + ℓU) (by omega)).const_mul (cF * cU)) (hFm.smul hUm)
      (Eventually.of_forall fun x => hFUle (hself (Gr x)))
  refine ⟨hFint, hUint, hFUint, ?_⟩
  -- the regularized family `κ_m = 1/(m+1)`
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Gm : ℕ → (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun m => tcvG W b σ E z X (κm m) with hGm
  have hGmc : ∀ m, Continuous (Gm m) := fun m =>
    (tcv_G_contDiff W b σ E z hX hz (hκpos m)).continuous
  have hGm2 : ∀ m, ∀ᵐ x ∂μ, ‖Gm m x‖ ≤ 2 * ‖Gr x‖ := fun m => by
    filter_upwards [hinv] with x hx
    exact tflPsi_inv_le_two W b σ E z hX hz (hκpos m) x hx
  have hGmlim : ∀ᵐ x ∂μ, Tendsto (fun m => Gm m x) atTop (𝓝 (Gr x)) := by
    filter_upwards [hinv] with x hx
    exact tcv_G_tendsto σ E z hx hκlim
  -- dominated convergence for the three means
  have hlimFU : Tendsto (fun m => ∫ x, tcvTr W σ (wordEval εf Df (Gm m x)) •
      wordEval εU DU (Gm m x) ∂μ) atTop (𝓝 (∫ x, F x • U x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (cF * cU) * ‖Gr x‖ ^ (ℓf + ℓU))
      (fun m => ((hFc.comp (hGmc m)).smul (hUc.comp (hGmc m))).aestronglyMeasurable)
      ((hpow (ℓf + ℓU) (by omega)).const_mul _) (fun m => ?_) ?_
    · filter_upwards [hGm2 m] with x hx
      exact hFUle hx
    · filter_upwards [hGmlim] with x hx
      exact ((hFc.tendsto _).comp hx).smul ((hUc.tendsto _).comp hx)
  have hlimF : Tendsto (fun m => ∫ x, tcvTr W σ (wordEval εf Df (Gm m x)) ∂μ) atTop
      (𝓝 (∫ x, F x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => cF * ‖Gr x‖ ^ ℓf)
      (fun m => (hFc.comp (hGmc m)).aestronglyMeasurable)
      ((hpow ℓf (by omega)).const_mul _) (fun m => ?_) ?_
    · filter_upwards [hGm2 m] with x hx
      exact hFle hx
    · filter_upwards [hGmlim] with x hx
      exact (hFc.tendsto _).comp hx
  have hlimU : Tendsto (fun m => ∫ x, wordEval εU DU (Gm m x) ∂μ) atTop
      (𝓝 (∫ x, U x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => cU * ‖Gr x‖ ^ ℓU)
      (fun m => (hUc.comp (hGmc m)).aestronglyMeasurable)
      ((hpow ℓU (by omega)).const_mul _) (fun m => ?_) ?_
    · filter_upwards [hGm2 m] with x hx
      exact hUle hx
    · filter_upwards [hGmlim] with x hx
      exact (hUc.tendsto _).comp hx
  have hlim := (hlimFU.sub (hlimF.smul hlimU)).norm
  refine le_of_tendsto' hlim fun m => ?_
  -- the bound for each `κ_m`
  refine (tcv_cov_reg σ E z hW hb0 hb1 hX hz (hκpos m) hK εf Df εU DU hDf hDU).trans ?_
  have hc0 : 0 ≤ 10 * ℓf * ℓU * K ^ n / (W : ℝ) ^ 2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hc0
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hGmn : Integrable (fun x => ‖Gm m x‖ ^ n) μ := by
    refine Integrable.of_bound (((hGmc m).norm.pow n).aestronglyMeasurable) ((κm m)⁻¹ ^ n)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (tcv_G_le W b σ E z hX hz (hκpos m) x) n
  calc ∫ x, ‖Gm m x‖ ^ n ∂μ ≤ ∫ x, 2 ^ n * ‖Gr x‖ ^ n ∂μ := by
        refine integral_mono_ae hGmn ((hpow n le_rfl).const_mul _) ?_
        filter_upwards [hGm2 m] with x hx
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hx n
    _ = 2 ^ n * ∫ x, ‖Gr x‖ ^ n ∂μ := integral_const_mul _ _
    _ ≤ 2 ^ n * CA ^ n := by
        gcongr
        exact (hmom n (by omega) le_rfl).2
    _ = (2 * CA) ^ n := by rw [mul_pow]

end Limit

/-!
## 6. Transfer to `layerLaw` and the contract
-/

section Contract

variable {W : ℕ} {b : ℝ} {σ : LayerShape}

/-- Entrywise expectation under `layerLaw` is the Bochner integral in the coordinates. -/
theorem tcv_matrixExpect_eq {Y : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hY : Measurable Y)
    (hint : Integrable (fun x => Y (tflEmbed W b σ x)) (gaussianProduct (tflVar W b σ))) :
    matrixExpect (layerLaw W b σ) Y =
      ∫ x, Y (tflEmbed W b σ x) ∂gaussianProduct (tflVar W b σ) := by
  have hΦ := tfl_measurable_embed W b σ
  ext x y
  have hm : Measurable (fun ω => Y ω x y) :=
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hY)
  simp only [matrixExpect, of_apply]
  rw [tfl_layerLaw_eq_map, integral_map hΦ.aemeasurable hm.aestronglyMeasurable]
  exact ContinuousLinearMap.integral_comp_comm (tcvEntry W σ x y) hint

/-- The constant of the contract: a finite sum over the word lengths `ℓ_f, ℓ_U ≤ L`. -/
def tcvConst (L : ℕ) (K CA : ℝ) : ℝ :=
  ∑ ℓf ∈ Finset.range (L + 1), ∑ ℓU ∈ Finset.range (L + 1),
    10 * ℓf * ℓU * |K| ^ (ℓf + ℓU + 2) * (2 * (2 * CA) ^ (ℓf + ℓU + 2))

theorem tcv_le_const {L : ℕ} {K CA : ℝ} (hCA : 0 ≤ CA) {ℓf ℓU : ℕ} (hf : ℓf ≤ L)
    (hU : ℓU ≤ L) :
    10 * ℓf * ℓU * |K| ^ (ℓf + ℓU + 2) * (2 * (2 * CA) ^ (ℓf + ℓU + 2)) ≤ tcvConst L K CA := by
  unfold tcvConst
  have hnn : ∀ a c : ℕ,
      0 ≤ 10 * (a : ℝ) * c * |K| ^ (a + c + 2) * (2 * (2 * CA) ^ (a + c + 2)) :=
    fun a c => by positivity
  refine le_trans ?_ (Finset.single_le_sum (f := fun a : ℕ => ∑ c ∈ Finset.range (L + 1),
    10 * (a : ℝ) * c * |K| ^ (a + c + 2) * (2 * (2 * CA) ^ (a + c + 2)))
    (fun a _ => Finset.sum_nonneg fun c _ => hnn a c)
    (Finset.mem_range.mpr (show ℓf < L + 1 by omega)))
  exact Finset.single_le_sum (f := fun c : ℕ => 10 * (ℓf : ℝ) * c * |K| ^ (ℓf + c + 2) *
    (2 * (2 * CA) ^ (ℓf + c + 2))) (fun c _ => hnn ℓf c)
    (Finset.mem_range.mpr (show ℓU < L + 1 by omega))

end Contract

/-- **The trace–matrix covariance bound**: the `covariance` field of `TraceMatrixContract`, from
`GaussianAbsorptionContract` alone. With `ε₁, C_A` from `GaussianAbsorptionContract b η₀ M`:
`W₀ = ⌈(2L+2)/ε₁⌉₊` and `C = Σ_{ℓ_f, ℓ_U ≤ L} 20 ℓ_f ℓ_U |K|^{n} (2C_A)^{n}`, `n = ℓ_f+ℓ_U+2`;
uniformly in `W ≥ W₀`, the shape, Hermitian `X`, real `E`, `Im z ≥ η₀`, `|z| ≤ M` and the words
(at most `L` resolvent letters, deterministic letters of norm `≤ K`). -/
theorem traceCovariance_holds (habs : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ η₀ M : ℝ, 0 < η₀ → ∀ (L : ℕ) (K : ℝ),
    ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
      ∀ (ℓf ℓU : ℕ), ℓf ≤ L → ℓU ≤ L →
      ∀ (εf : Fin ℓf → Bool) (Df : Fin (ℓf + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
        (εU : Fin ℓU → Bool) (DU : Fin (ℓU + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ),
        (∀ j, ‖Df j‖ ≤ K) → (∀ j, ‖DU j‖ ≤ K) →
        let μ := layerLaw W b σ
        let f : LayerSample W σ → ℂ := fun ω =>
          (W : ℂ)⁻¹ * (wordEval εf Df (layerResolvent σ E z X ω)).trace
        let U : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ := fun ω =>
          wordEval εU DU (layerResolvent σ E z X ω)
        Integrable f μ ∧ (∀ x y, Integrable (fun ω => U ω x y) μ) ∧
          (∀ x y, Integrable (fun ω => f ω * U ω x y) μ) ∧
          ‖matrixExpect μ (fun ω => f ω • U ω) - (∫ ω, f ω ∂μ) • matrixExpect μ U‖ ≤
            C / (W : ℝ) ^ 2 := by
  intro b hb0 hb1 η₀ M hη L K
  obtain ⟨ε₁, CA, hε₁, hCA, habs'⟩ := habs b hb0 hb1 η₀ M hη
  refine ⟨tcvConst L K CA, ⌈(2 * L + 2 : ℝ) / ε₁⌉₊, ?_⟩
  intro W hW hW₀ σ X hX E z hz hzM ℓf ℓU hℓf hℓU εf Df εU DU hDf hDU μ f U
  obtain ⟨hinv, hmom⟩ := habs' W hW σ X hX E z hz hzM
  have hK : 0 ≤ K := (norm_nonneg _).trans (hDf 0)
  have hz0 : 0 ≤ z.im := le_trans hη.le hz
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set μc := gaussianProduct (tflVar W b σ) with hμc
  set Φ := tflEmbed W b σ with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b σ
  have hlaw : layerLaw W b σ = μc.map Φ := tfl_layerLaw_eq_map W b σ
  -- moments and invertibility in the coordinates
  have hεW : (2 * L + 2 : ℝ) ≤ ε₁ * W := by
    have h1 : (2 * L + 2 : ℝ) / ε₁ ≤ W :=
      (Nat.le_ceil _).trans (by exact_mod_cast hW₀)
    rw [div_le_iff₀ hε₁] at h1
    linarith
  have hinvc : ∀ᵐ x ∂μc, IsUnit (layerMatrix σ E z X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  have hGr : Measurable (fun x => layerResolvent σ E z X (Φ x)) :=
    (measurable_layerResolvent σ E z X).comp hΦ
  have hmomc : ∀ m : ℕ, 1 ≤ m → m ≤ ℓf + ℓU + 2 →
      Integrable (fun x => ‖layerResolvent σ E z X (Φ x)‖ ^ m) μc ∧
      ∫ x, ‖layerResolvent σ E z X (Φ x)‖ ^ m ∂μc ≤ CA ^ m := by
    intro m hm1 hmn
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmε : (m : ℝ) ≤ ε₁ * W := by
      have : (m : ℝ) ≤ 2 * L + 2 := by
        have : m ≤ 2 * L + 2 := by omega
        exact_mod_cast this
      linarith
    have h := hmom m hm1' hmε
    rw [hlaw, eLpNorm_map_measure (measurable_norm_layerResolvent σ E z X).aestronglyMeasurable
      hΦ.aemeasurable] at h
    exact tcv_moment hm1 hCA.le h
  obtain ⟨hFi, hUi, hFUi, hbd⟩ :=
    tcv_core σ E z hW hb0 hb1 hX hz0 hK εf Df εU DU hDf hDU hinvc hmomc
  -- measurability on the layer
  have hFc : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      tcvTr W σ (wordEval εf Df N)) :=
    (tcvTr W σ).continuous.comp (tcv_continuous_wordEval εf Df)
  have hUc : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      wordEval εU DU N) := tcv_continuous_wordEval εU DU
  have hfm : Measurable f := hFc.measurable.comp (measurable_layerResolvent σ E z X)
  have hUm : Measurable U := hUc.measurable.comp (measurable_layerResolvent σ E z X)
  have hent : ∀ x y, Measurable (fun ω => U ω x y) := fun x y =>
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hUm)
  refine ⟨?_, fun x y => ?_, fun x y => ?_, ?_⟩
  · change Integrable f (layerLaw W b σ)
    rw [hlaw, integrable_map_measure hfm.aestronglyMeasurable hΦ.aemeasurable]
    exact hFi
  · change Integrable (fun ω => U ω x y) (layerLaw W b σ)
    rw [hlaw, integrable_map_measure (hent x y).aestronglyMeasurable hΦ.aemeasurable]
    exact (tcvEntry W σ x y).integrable_comp hUi
  · change Integrable (fun ω => f ω * U ω x y) (layerLaw W b σ)
    have hfU : Measurable (fun ω => f ω * U ω x y) := hfm.mul (hent x y)
    rw [hlaw, integrable_map_measure hfU.aestronglyMeasurable hΦ.aemeasurable]
    exact (tcvEntry W σ x y).integrable_comp hFUi
  · change ‖matrixExpect (layerLaw W b σ) (fun ω => f ω • U ω) -
      (∫ ω, f ω ∂layerLaw W b σ) • matrixExpect (layerLaw W b σ) U‖ ≤ _
    have hfUm : Measurable (fun ω => f ω • U ω) := hfm.smul hUm
    rw [tcv_matrixExpect_eq hfUm hFUi, tcv_matrixExpect_eq hUm hUi, hlaw,
      integral_map hΦ.aemeasurable hfm.aestronglyMeasurable]
    refine hbd.trans ?_
    have hc := tcv_le_const (K := K) hCA.le hℓf hℓU
    rw [abs_of_nonneg hK] at hc
    calc 10 * ℓf * ℓU * K ^ (ℓf + ℓU + 2) / (W : ℝ) ^ 2 * (2 * (2 * CA) ^ (ℓf + ℓU + 2))
        = 10 * ℓf * ℓU * K ^ (ℓf + ℓU + 2) * (2 * (2 * CA) ^ (ℓf + ℓU + 2)) / (W : ℝ) ^ 2 := by
          ring
      _ ≤ tcvConst L K CA / (W : ℝ) ^ 2 := by gcongr

/-- `traceCovariance_holds` has exactly the type of `TraceMatrixContract.covariance`. -/
example (habs : GaussianAbsorptionContract) (hT : TraceMatrixContract) :
    hT.covariance = traceCovariance_holds habs := rfl

end BlockBand.Layers

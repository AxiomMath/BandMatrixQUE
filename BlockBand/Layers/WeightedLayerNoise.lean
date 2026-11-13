module

public import BlockBand.Layers.TraceCovariance
public import BlockBand.Layers.LayerContraction
public import BlockBand.Layers.BondMoments

/-!
# The weighted layer: moments, the unrestricted bound and the clock noise

The moments, unrestricted and clock-noise fields of `WeightedLayerContract` (the weighted-layer
lemma; `wl_moments`, `wl_unrestricted`, `wl_clockNoise`), from `ConditionalBlockGUECount` (through `gaussianAbsorption_holds`) and
`GaussianLpGradient`.

Setting (exactly that of `WeightedLayerContract`). One separate-port layer (`layerLaw W b .separate`:
`A_a ~ GUE_W(c/W)`, `c = 1 - 2b`, bonds `Gin(b/W)`, all independent), a deterministic Hermitian
two-port `X` (the independent old input, conditioning by Fubini), `E ∈ bulkInterval κ`,
`z = z_∂(E)`, `𝒢 = layerResolvent`, `K = z - X`, `L = K 𝒢₁₂`, `Y ⪰ 0` deterministic,
`u = W⁻¹ Tr Y`. Norms: `ℓ²` operator norms (`Matrix.Norms.L2Operator`), Hilbert–Schmidt sums
`wlHS M = Σ |M_xy|²`; `L^p` norms are `eLpNorm` under `layerLaw`.

Proof.
1. **Weighted inverse identities** (§2, deterministic). With `𝒦 = diag(K, 0)` on the layer
   sites, `J = diag(1, 0)` and any `N` with `N G = 1`,
   `𝒦 G = J + (𝒦 - J N) G`, and for `N = 𝒢⁻¹ + iκ` the matrix `𝒦 - J N =
   ((z+E-iκ) J - J Λ)` (`Λ = [[A, B], [B*, 0]]` the random part) has norm
   `≤ |z| + |E| + κ + ‖Λ‖`: this is the paper identity `K𝒢₁₁ = I + [(z+E) - A + …]𝒢₁₁`
   (written with the second block row instead of the Schur complement). The blocks of `𝒦 𝒢`
   are `K𝒢₁₁` and `L = K𝒢₁₂`; likewise `𝒢 𝒦* = J + 𝒢 (𝒦* - N J)` has block `𝒢₁₁ K*`.
2. **Random part** (§3). `‖Λ‖` has all fixed moments uniformly in `W`: for unit `n, n'`,
   `Re⟨n, Λ(x) n'⟩` is a centered Gaussian of variance `≤ Σᵢ vᵢ |Tr(n'n* Λᵢ)|² ≤ 4/W`
   (`tfl_weighted_trace_le`), nets of the unit spheres give
   `P(‖Λ‖ ≥ a) ≤ exp(W(48 - a²/32))`, and the dyadic layer cake gives
   `E(1 + ‖Λ‖)^q ≤ C^q` for `1 ≤ q ≤ W`.
3. **Moments** (§4): `‖𝒦𝒢‖ ≤ 1 + (|z| + |E| + ‖Λ‖)‖𝒢‖` a.s., Minkowski and Hölder with
   the Gaussian absorption lemma (`gaussianAbsorption_holds`).
4. **Unrestricted bound** (§5): `0 ≤ W⁻¹ Tr L*YL ≤ ‖L‖² u` (`Y = B*B`, Hilbert–Schmidt).
5. **Clock noise** (§6–9): regularize `𝒢 ↦ G_κ = (𝒢⁻¹ + iκ)⁻¹`; `t_κ = W⁻¹ Tr(Ŷ 𝓛 𝓛*)`,
   `𝓛 = 𝒦 G_κ Q` (`Q` the port projector, `Ŷ = diag(Y, 0)`), is smooth with
   `|∂ᵢ t_κ| ≤ 2W⁻¹ |Tr(G_κ Q 𝓛* Ŷ 𝒦 G_κ Λᵢ)|`, so its weighted gradient is at most
   `4 W⁻¹ √(W⁻¹ Tr Y²) ‖G_κ‖ ‖𝒦 G_κ‖²` (in the paper: "gradient norm at most `CW⁻¹‖Y‖_HS` times
   such factors", covariance `W⁻¹`); `Inputs.GaussianLpGradient` and the moments give the bound for
   each `κ ∈ (0, 1]`, and `κ → 0` (dominated convergence, Fatou) gives the clock-noise bound;
   `Tr Y² ≤ (Tr Y)²` gives its second inequality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient
  ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Generic matrix facts: Hilbert–Schmidt sums and positive weights
-/

section Generic

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq m]
  [DecidableEq n]

/-- The Hilbert–Schmidt sum `Σ |M_xy|²`. -/
def wlHS (M : Matrix m n ℂ) : ℝ := ∑ x, ∑ y, ‖M x y‖ ^ 2

theorem wlHS_nonneg (M : Matrix m n ℂ) : 0 ≤ wlHS M := by unfold wlHS; positivity

theorem wlHS_conjTranspose (M : Matrix m n ℂ) : wlHS Mᴴ = wlHS M := by
  unfold wlHS
  rw [Finset.sum_comm]
  simp [conjTranspose_apply]

/-- Column form: `Σ_x |(A v)_x|² ≤ ‖A‖² Σ |v|²`. -/
theorem wl_col_le (A : Matrix m n ℂ) (v : n → ℂ) :
    ∑ x, ‖(A *ᵥ v) x‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ y, ‖v y‖ ^ 2 := by
  have h := norm_toLp_mulVec_le A v
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

/-- `‖A B‖²_HS ≤ ‖A‖² ‖B‖²_HS`. -/
theorem wlHS_mul_left_le (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    wlHS (A * B) ≤ ‖A‖ ^ 2 * wlHS B := by
  unfold wlHS
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => ‖B x y‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := wl_col_le A (fun k => B k y)
  convert h using 2
  rfl

/-- `‖B C‖²_HS ≤ ‖B‖²_HS ‖C‖²`. -/
theorem wlHS_mul_right_le (B : Matrix l m ℂ) (C : Matrix m n ℂ) :
    wlHS (B * C) ≤ wlHS B * ‖C‖ ^ 2 := by
  rw [← wlHS_conjTranspose, conjTranspose_mul, ← wlHS_conjTranspose B]
  have := wlHS_mul_left_le Cᴴ Bᴴ
  rw [l2_opNorm_conjTranspose] at this
  linarith

/-- `Tr(M* M) = ‖M‖²_HS`. -/
theorem wl_trace_conjTranspose_mul_self (M : Matrix m n ℂ) :
    (Mᴴ * M).trace = (wlHS M : ℂ) := by
  unfold wlHS
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- Cauchy–Schwarz for the trace pairing: `|Tr(A B)| ≤ ‖A‖_HS ‖B‖_HS`. -/
theorem wl_norm_trace_mul_le (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    ‖(A * B).trace‖ ≤ Real.sqrt (wlHS A) * Real.sqrt (wlHS B) := by
  have e : (A * B).trace = ∑ p : m × n, A p.1 p.2 * B p.2 p.1 := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    simp [Matrix.mul_apply]
  have hA : wlHS A = ∑ p : m × n, ‖A p.1 p.2‖ ^ 2 := by
    rw [wlHS, Fintype.sum_prod_type]
  have hB : wlHS B = ∑ p : m × n, ‖B p.2 p.1‖ ^ 2 := by
    rw [wlHS, Fintype.sum_prod_type, Finset.sum_comm]
  rw [e, hA, hB]
  refine (norm_sum_le _ _).trans ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p : m × n => ‖A p.1 p.2‖)
    (fun p => ‖B p.2 p.1‖)
  have h0 : 0 ≤ ∑ p : m × n, ‖A p.1 p.2‖ * ‖B p.2 p.1‖ := by positivity
  rw [← Real.sqrt_mul (by positivity)]
  refine le_trans (le_of_eq ?_) (Real.sqrt_le_sqrt hcs)
  · rw [Real.sqrt_sq h0]
    exact Finset.sum_congr rfl fun p _ => norm_mul _ _

/-- `‖A‖² ≤ ‖A‖²_HS`. -/
theorem wl_opNorm_sq_le_hs (A : Matrix m n ℂ) : ‖A‖ ^ 2 ≤ wlHS A := by
  have hb : ‖A‖ ≤ Real.sqrt (wlHS A) := by
    rw [l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    change ‖toEuclideanLin A v‖ ≤ _
    have hsq : ‖toEuclideanLin A v‖ ^ 2 ≤ wlHS A * ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [toLpLin_apply, PiLp.toLp_apply]
      unfold wlHS
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [Matrix.mulVec, dotProduct]
      refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => ‖A x y‖)
        (fun y => ‖(WithLp.ofLp v) y‖)
      simpa only [norm_mul] using hcs
    have h2 : Real.sqrt (‖toEuclideanLin A v‖ ^ 2) ≤ Real.sqrt (wlHS A * ‖v‖ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (wlHS_nonneg A),
      Real.sqrt_sq (norm_nonneg _)] at h2
  calc ‖A‖ ^ 2 ≤ Real.sqrt (wlHS A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = wlHS A := Real.sq_sqrt (wlHS_nonneg A)

open scoped MatrixOrder ComplexOrder in
/-- A positive semidefinite matrix is a Gram matrix `B* B`. -/
theorem wl_psd_eq {Y : Matrix n n ℂ} (hY : Y.PosSemidef) : ∃ B : Matrix n n ℂ, Y = Bᴴ * B := by
  obtain ⟨X, hX, -, hXX⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hY.isHermitian
      (QuasispectrumRestricts.nnreal_of_nonneg hY.nonneg)
  refine ⟨X, ?_⟩
  have : Xᴴ = X := hX.star_eq
  rw [this]; exact hXX.symm

open scoped ComplexOrder in
/-- **Weighted trace bound**: for `Y ⪰ 0`, `0 ≤ Re Tr(L* Y L) ≤ ‖L‖² Re Tr Y`. -/
theorem wl_trace_weight_le {Y : Matrix n n ℂ} (hY : Y.PosSemidef) (L : Matrix n m ℂ) :
    0 ≤ (Lᴴ * Y * L).trace.re ∧ (Lᴴ * Y * L).trace.re ≤ ‖L‖ ^ 2 * Y.trace.re := by
  obtain ⟨B, rfl⟩ := wl_psd_eq hY
  have e1 : Lᴴ * (Bᴴ * B) * L = (B * L)ᴴ * (B * L) := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e1, wl_trace_conjTranspose_mul_self, wl_trace_conjTranspose_mul_self, Complex.ofReal_re,
    Complex.ofReal_re]
  refine ⟨wlHS_nonneg _, ?_⟩
  have := wlHS_mul_right_le B L
  linarith

open scoped ComplexOrder in
/-- **Trace pairing with a positive weight**: `|Tr(Y N)| ≤ ‖N‖ Re Tr Y` for `Y ⪰ 0`. -/
theorem wl_norm_trace_weight_le {Y : Matrix n n ℂ} (hY : Y.PosSemidef) (N : Matrix n n ℂ) :
    ‖(Y * N).trace‖ ≤ ‖N‖ * Y.trace.re := by
  obtain ⟨B, rfl⟩ := wl_psd_eq hY
  have e1 : (Bᴴ * B * N).trace = ((B * N) * Bᴴ).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [e1, wl_trace_conjTranspose_mul_self, Complex.ofReal_re]
  refine (wl_norm_trace_mul_le _ _).trans ?_
  rw [wlHS_conjTranspose]
  have h1 := wlHS_mul_right_le B N
  have hN := norm_nonneg N
  have hB := wlHS_nonneg B
  have h2 : Real.sqrt (wlHS (B * N)) ≤ Real.sqrt (wlHS B) * ‖N‖ := by
    rw [← Real.sqrt_sq hN, ← Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt h1
  calc Real.sqrt (wlHS (B * N)) * Real.sqrt (wlHS B)
      ≤ Real.sqrt (wlHS B) * ‖N‖ * Real.sqrt (wlHS B) :=
        mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
    _ = ‖N‖ * wlHS B := by
        rw [mul_comm (Real.sqrt _) ‖N‖, mul_assoc, Real.mul_self_sqrt hB]

open scoped ComplexOrder in
/-- `0 ≤ Re Tr Y² ≤ (Re Tr Y)²` for `Y ⪰ 0`. -/
theorem wl_trace_sq_le {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    0 ≤ (Y * Y).trace.re ∧ (Y * Y).trace.re ≤ Y.trace.re ^ 2 := by
  obtain ⟨B, rfl⟩ := wl_psd_eq hY
  have e1 : (Bᴴ * B * (Bᴴ * B)).trace = ((B * Bᴴ)ᴴ * (B * Bᴴ)).trace := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show Bᴴ * B * (Bᴴ * B) = Bᴴ * (B * Bᴴ * B) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e1, wl_trace_conjTranspose_mul_self, wl_trace_conjTranspose_mul_self, Complex.ofReal_re,
    Complex.ofReal_re]
  refine ⟨wlHS_nonneg _, ?_⟩
  have h1 := wlHS_mul_left_le B Bᴴ
  have h2 := wl_opNorm_sq_le_hs B
  rw [wlHS_conjTranspose] at h1
  have hB := wlHS_nonneg B
  nlinarith

end Generic

/-!
## 2. The weighted inverse identities
-/

section Blocks

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A Hermitian idempotent has operator norm `≤ 1`. -/
theorem wl_norm_proj_le {P : Matrix n n ℂ} (hH : Pᴴ = P) (hP : P * P = P) : ‖P‖ ≤ 1 := by
  have h1 : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hH, hP]
  have h0 := norm_nonneg P
  nlinarith

/-- The coordinate inclusion matrix of an injective map. -/
def wlIncl {ι κ : Type*} (f : ι → κ) [DecidableEq κ] : Matrix ι κ ℂ :=
  Matrix.of fun x y => if y = f x then 1 else 0

theorem wl_norm_incl_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {f : ι → κ} (hf : Function.Injective f) : ‖wlIncl f‖ ≤ 1 := by
  have hJJ : wlIncl f * (wlIncl f)ᴴ = 1 := by
    ext x y
    simp only [Matrix.mul_apply, conjTranspose_apply, wlIncl, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (f x)]
    · by_cases h : x = y
      · subst h; simp
      · have : f x ≠ f y := fun h' => h (hf h')
        simp [h, this]
    · intro c _ hc; simp [hc]
    · simp
  have h1 : ‖(wlIncl f)ᴴ‖ * ‖(wlIncl f)ᴴ‖ = ‖((wlIncl f)ᴴ)ᴴ * (wlIncl f)ᴴ‖ :=
    (l2_opNorm_conjTranspose_mul_self _).symm
  rw [conjTranspose_conjTranspose, hJJ, l2_opNorm_conjTranspose] at h1
  have h2 := lct_norm_one_le (n := ι)
  have h0 := norm_nonneg (wlIncl f)
  nlinarith

/-- `‖M_{f,g}‖ ≤ ‖M‖` for injective `f, g` (compression). -/
theorem wl_norm_submatrix_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix n m ℂ) {f : ι → n} {g : κ → m} (hf : Function.Injective f)
    (hg : Function.Injective g) : ‖M.submatrix f g‖ ≤ ‖M‖ := by
  have heq : M.submatrix f g = wlIncl f * M * (wlIncl g)ᴴ := by
    ext x y
    simp only [Matrix.mul_apply, conjTranspose_apply, wlIncl, Matrix.of_apply, submatrix_apply]
    simp [Finset.sum_ite_eq', ite_mul]
  rw [heq]
  calc ‖wlIncl f * M * (wlIncl g)ᴴ‖ ≤ ‖wlIncl f‖ * ‖M‖ * ‖(wlIncl g)ᴴ‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖M‖ * 1 := by
        rw [l2_opNorm_conjTranspose]
        exact mul_le_mul (mul_le_mul_of_nonneg_right (wl_norm_incl_le hf) (norm_nonneg _))
          (wl_norm_incl_le hg) (norm_nonneg _) (by positivity)
    _ = ‖M‖ := by ring

theorem wl_norm_toBlocks12_le (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : ‖M.toBlocks₁₂‖ ≤ ‖M‖ :=
  wl_norm_submatrix_le M Sum.inl_injective Sum.inr_injective

theorem wl_norm_toBlocks11_le (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : ‖M.toBlocks₁₁‖ ≤ ‖M‖ :=
  wl_norm_submatrix_le M Sum.inl_injective Sum.inl_injective

/-- `J = diag(1, 0)`. -/
def wlJ (n m : Type*) [DecidableEq n] : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks 1 0 0 0

/-- The port projector `Q = diag(0, 1)`. -/
def wlQ (n m : Type*) [DecidableEq m] : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks 0 0 0 1

/-- `𝒦 = diag(K, 0)`. -/
def wlKh (K : Matrix n n ℂ) : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks K 0 0 0

theorem wlJ_conjTranspose : (wlJ n m)ᴴ = wlJ n m := by
  rw [wlJ, fromBlocks_conjTranspose]; simp

theorem wlQ_conjTranspose : (wlQ n m)ᴴ = wlQ n m := by
  rw [wlQ, fromBlocks_conjTranspose]; simp

theorem wlJ_mul_self : wlJ n m * wlJ n m = wlJ n m := by
  rw [wlJ, fromBlocks_multiply]; simp

theorem wlQ_mul_self : wlQ n m * wlQ n m = wlQ n m := by
  rw [wlQ, fromBlocks_multiply]; simp

theorem wl_norm_J_le : ‖wlJ n m‖ ≤ 1 := wl_norm_proj_le wlJ_conjTranspose wlJ_mul_self

theorem wl_norm_Q_le : ‖wlQ n m‖ ≤ 1 := wl_norm_proj_le wlQ_conjTranspose wlQ_mul_self

theorem wlKh_conjTranspose (K : Matrix n n ℂ) : (wlKh (m := m) K)ᴴ = wlKh Kᴴ := by
  rw [wlKh, wlKh, fromBlocks_conjTranspose]; simp

/-- **Left weighted identity**: `N G = 1 ⇒ 𝒦 G = J + (𝒦 - J N) G`. -/
theorem wl_Kh_mul_eq {N G : Matrix (n ⊕ m) (n ⊕ m) ℂ} (h : N * G = 1) (Kh : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    Kh * G = wlJ n m + (Kh - wlJ n m * N) * G := by
  rw [Matrix.sub_mul, Matrix.mul_assoc, h, Matrix.mul_one]; abel

/-- **Right weighted identity**: `G N = 1 ⇒ G 𝒦* = J + G (𝒦* - N J)`. -/
theorem wl_mul_Kh_eq {N G : Matrix (n ⊕ m) (n ⊕ m) ℂ} (h : G * N = 1) (Kh : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    G * Kh = wlJ n m + G * (Kh - N * wlJ n m) := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.one_mul]; abel

theorem wl_norm_weighted_le {G D : Matrix (n ⊕ m) (n ⊕ m) ℂ} :
    ‖wlJ n m + D * G‖ ≤ 1 + ‖D‖ * ‖G‖ :=
  (norm_add_le _ _).trans (add_le_add wl_norm_J_le (norm_mul_le _ _))

theorem wl_norm_weighted_le' {G D : Matrix (n ⊕ m) (n ⊕ m) ℂ} :
    ‖wlJ n m + G * D‖ ≤ 1 + ‖D‖ * ‖G‖ := by
  refine (norm_add_le _ _).trans (add_le_add wl_norm_J_le ?_)
  rw [mul_comm]; exact norm_mul_le _ _

theorem wl_Kh_mul_toBlocks11 (K : Matrix n n ℂ) (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (wlKh K * G).toBlocks₁₁ = K * G.toBlocks₁₁ := by
  ext x y
  simp [wlKh, toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]

theorem wl_Kh_mul_toBlocks12 (K : Matrix n n ℂ) (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (wlKh K * G).toBlocks₁₂ = K * G.toBlocks₁₂ := by
  ext x y
  simp [wlKh, toBlocks₁₂, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]

theorem wl_mul_Kh_toBlocks11 (K : Matrix n n ℂ) (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (G * wlKh K).toBlocks₁₁ = G.toBlocks₁₁ * K := by
  ext x y
  simp [wlKh, toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]

end Blocks

section LayerBlocks

variable {W : ℕ} {σ : LayerShape}

/-- The random part `Λ = [[diag A, B], [B*, 0]]` of the layer matrix (`= tflLin` in
coordinates). -/
def wlLam (ω : LayerSample W σ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  fromBlocks (Internal.Contracts.Layers.blockDiag ω.1) (bondMatrix σ ω.2)
    (bondMatrix σ ω.2)ᴴ 0

theorem wlLam_embed (b : ℝ) (x : TflCoord W σ → ℝ) :
    wlLam (tflEmbed W b σ x) = tflLin W b σ x := rfl

theorem wl_measurable_wlLam : Measurable (fun ω : LayerSample W σ => wlLam ω) := by
  have hA : Measurable (fun ω : LayerSample W σ => Internal.Contracts.Layers.blockDiag ω.1) := by
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    unfold Internal.Contracts.Layers.blockDiag
    split_ifs
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        ((measurable_pi_apply _).comp measurable_fst))
    · exact measurable_const
  have hB := bond_measurable_bondMatrix (W := W) σ
  have hBh : Measurable (fun ω : LayerSample W σ => (bondMatrix σ ω.2)ᴴ) :=
    (continuous_id.matrix_conjTranspose).measurable.comp hB
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  rcases x with x | x <;> rcases y with y | y
  · simp only [wlLam, fromBlocks_apply₁₁]
    exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hA)
  · simp only [wlLam, fromBlocks_apply₁₂]
    exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hB)
  · simp only [wlLam, fromBlocks_apply₂₁]
    exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hBh)
  · simp only [wlLam, fromBlocks_apply₂₂]
    exact measurable_const

theorem wl_layerMatrix_eq (E : ℝ) (z : ℂ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (ω : LayerSample W σ) : layerMatrix σ E z X ω = tflConst σ E z X + wlLam ω := by
  rw [layerMatrix, tflConst, wlLam, fromBlocks_add]
  congr 1 <;> abel

/-- `𝒦 - J (𝒢⁻¹ + iκ) = (z + E - iκ) J - J Λ`. -/
theorem wl_Kh_sub_left (E : ℝ) (z : ℂ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (ω : LayerSample W σ) (κ : ℝ) :
    wlKh (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X) -
        wlJ (PhysSite W σ) (PortSite W σ) * tflReg κ (layerMatrix σ E z X ω) =
      (z + E - (κ : ℂ) * Complex.I) • wlJ (PhysSite W σ) (PortSite W σ) -
        wlJ (PhysSite W σ) (PortSite W σ) * wlLam ω := by
  rw [tflReg, layerMatrix, wlLam, wlJ, wlKh, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add,
    fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul]
  ext p q
  rcases p with p | p <;> rcases q with q | q
  · simp only [fromBlocks_apply₁₁, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, smul_eq_mul]
    split_ifs <;> simp <;> ring
  all_goals simp

/-- `𝒦* - (𝒢⁻¹ + iκ) J = (z̄ + E - iκ) J - Λ J` for Hermitian `X`. -/
theorem wl_Kh_sub_right (E : ℝ) (z : ℂ) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) (ω : LayerSample W σ) (κ : ℝ) :
    wlKh (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)ᴴ -
        tflReg κ (layerMatrix σ E z X ω) * wlJ (PhysSite W σ) (PortSite W σ) =
      (conj z + E - (κ : ℂ) * Complex.I) • wlJ (PhysSite W σ) (PortSite W σ) -
        wlLam ω * wlJ (PhysSite W σ) (PortSite W σ) := by
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq]
  rw [tflReg, layerMatrix, wlLam, wlJ, wlKh, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add,
    fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul]
  ext p q
  rcases p with p | p <;> rcases q with q | q
  · simp only [fromBlocks_apply₁₁, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.mul_one, Matrix.mul_zero, add_zero, smul_eq_mul]
    split_ifs <;> simp <;> ring
  all_goals simp

theorem wl_norm_shift_le (E : ℝ) (w : ℂ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖(w + E - (κ : ℂ) * Complex.I)‖ ≤ ‖w‖ + |E| + κ := by
  refine (norm_sub_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (by simp)) ?_
  simp [abs_of_nonneg hκ]

/-- `‖𝒦 - J (𝒢⁻¹ + iκ)‖ ≤ |z| + |E| + κ + ‖Λ‖`. -/
theorem wl_norm_Kh_sub_left_le (E : ℝ) (z : ℂ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (ω : LayerSample W σ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖wlKh (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X) -
        wlJ (PhysSite W σ) (PortSite W σ) * tflReg κ (layerMatrix σ E z X ω)‖ ≤
      ‖z‖ + |E| + κ + ‖wlLam ω‖ := by
  rw [wl_Kh_sub_left]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    calc _ ≤ (‖z‖ + |E| + κ) * 1 :=
          mul_le_mul (wl_norm_shift_le E z hκ) wl_norm_J_le (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · calc _ ≤ ‖wlJ (PhysSite W σ) (PortSite W σ)‖ * ‖wlLam ω‖ := norm_mul_le _ _
      _ ≤ 1 * ‖wlLam ω‖ := mul_le_mul_of_nonneg_right wl_norm_J_le (norm_nonneg _)
      _ = _ := one_mul _

/-- `‖𝒦* - (𝒢⁻¹ + iκ) J‖ ≤ |z| + |E| + κ + ‖Λ‖` for Hermitian `X`. -/
theorem wl_norm_Kh_sub_right_le (E : ℝ) (z : ℂ) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) (ω : LayerSample W σ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖wlKh (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)ᴴ -
        tflReg κ (layerMatrix σ E z X ω) * wlJ (PhysSite W σ) (PortSite W σ)‖ ≤
      ‖z‖ + |E| + κ + ‖wlLam ω‖ := by
  rw [wl_Kh_sub_right E z hX]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    have h := wl_norm_shift_le E (conj z) hκ
    rw [Complex.norm_conj] at h
    calc _ ≤ (‖z‖ + |E| + κ) * 1 :=
          mul_le_mul h wl_norm_J_le (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · calc _ ≤ ‖wlLam ω‖ * ‖wlJ (PhysSite W σ) (PortSite W σ)‖ := norm_mul_le _ _
      _ ≤ ‖wlLam ω‖ * 1 := mul_le_mul_of_nonneg_left wl_norm_J_le (norm_nonneg _)
      _ = _ := mul_one _

theorem wl_tflReg_zero (N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) : tflReg 0 N = N := by
  simp [tflReg]

end LayerBlocks

/-!
## 3. The random part `Λ` has bounded moments
-/

section RandomPart

/-- `gaussianProduct v` is the image of standard white noise under `y ↦ (√vᵢ yᵢ)ᵢ`. -/
theorem wl_gaussianProduct_eq_map {ι : Type} [Fintype ι] (v : ι → ℝ≥0) :
    gaussianProduct v = (whiteNoise ι 1).map (fun y i => Real.sqrt (v i) * y i) := by
  unfold gaussianProduct whiteNoise
  rw [Measure.pi_map_pi (fun i => (measurable_const_mul _).aemeasurable)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp

/-- **Gaussian tail of a linear functional**: under `gaussianProduct v`, if
`2 Σ vᵢ cᵢ² ≤ t`, then `P(s ≤ Σ cᵢ xᵢ) ≤ exp(-s²/t)` for `s > 0`. -/
theorem wl_linear_tail {ι : Type} [Fintype ι] (v : ι → ℝ≥0) (c : ι → ℝ) {t : ℝ≥0}
    (ht : 2 * ∑ i, (v i : ℝ) * c i ^ 2 ≤ t) {s : ℝ} (hs : 0 < s) :
    gaussianProduct v {x | s ≤ ∑ i, c i * x i} ≤ ENNReal.ofReal (Real.exp (-s ^ 2 / t)) := by
  set M : Unit → ι → ℝ := fun _ i => c i * Real.sqrt (v i) with hMdef
  set m : ℝ≥0 := Real.toNNReal (∑ i, (v i : ℝ) * c i ^ 2) with hm
  have hmv : (m : ℝ) = ∑ i, (v i : ℝ) * c i ^ 2 := Real.coe_toNNReal _ (by positivity)
  have hM : ∀ t' : Unit → ℝ, ∑ i, (∑ k, t' k * M k i) ^ 2 = m * ∑ k, t' k ^ 2 := by
    intro t'
    simp only [Finset.univ_unique, Finset.sum_singleton, hMdef]
    rw [hmv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (NNReal.coe_nonneg (v i))]
    ring
  have hφ : Measurable (fun y : ι → ℝ => fun i => Real.sqrt (v i) * y i) := by fun_prop
  have hset : MeasurableSet {x : ι → ℝ | s ≤ ∑ i, c i * x i} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [wl_gaussianProduct_eq_map, Measure.map_apply hφ hset]
  have hL : Measurable (fun y : ι → ℝ => fun k : Unit => ∑ i, M k i * y i) := by fun_prop
  have hpre : (fun y : ι → ℝ => fun i => Real.sqrt (v i) * y i) ⁻¹'
      {x : ι → ℝ | s ≤ ∑ i, c i * x i} =
      (fun y : ι → ℝ => fun k : Unit => ∑ i, M k i * y i) ⁻¹' {w | s ≤ w ()} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hMdef]
    constructor <;> intro h <;> convert h using 2 <;> ring
  rw [hpre, ← Measure.map_apply hL (measurableSet_le measurable_const (measurable_pi_apply ())),
    whiteNoise_map_linear 1 m M hM]
  have hbox : {w : Unit → ℝ | s ≤ w ()} = Set.univ.pi (fun _ => Set.Ici s) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ici]
    exact ⟨fun h _ => h, fun h => h ()⟩
  rw [hbox, whiteNoise, Measure.pi_pi, Finset.univ_unique, Finset.prod_singleton]
  refine gaussianReal_Ici_le_of_le ?_ hs
  rw [mul_one]
  have : ((2 * m : ℝ≥0) : ℝ) ≤ t := by
    push_cast; rw [hmv]; exact ht
  exact_mod_cast this

/-- `⟨n, M n'⟩` in coordinates (the form of `measure_opNorm_ge_of_net`). -/
def wlPair {ι : Type*} [Fintype ι] (n n' : EuclideanSpace ℂ ι) (M : Matrix ι ι ℂ) : ℂ :=
  ∑ x, ∑ y, star ((WithLp.ofLp n) x) * (M x y * (WithLp.ofLp n') y)

theorem wlPair_eq_trace {ι : Type*} [Fintype ι] (n n' : EuclideanSpace ℂ ι) (M : Matrix ι ι ℂ) :
    wlPair n n' M =
      ((Matrix.of fun y x => (WithLp.ofLp n') y * star ((WithLp.ofLp n) x)) * M).trace := by
  rw [wlPair, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem wlPair_sum_smul {ι κ : Type*} [Fintype ι] [Fintype κ] (n n' : EuclideanSpace ℂ ι)
    (r : κ → ℝ) (M : κ → Matrix ι ι ℂ) :
    (wlPair n n' (∑ i, r i • M i)).re = ∑ i, (wlPair n n' (M i)).re * r i := by
  rw [wlPair_eq_trace, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, wlPair_eq_trace, smul_eq_mul, mul_comm]

variable {W : ℕ} {b : ℝ} {σ : LayerShape}

theorem wl_tflLin_eq_sum (x : TflCoord W σ → ℝ) :
    tflLin W b σ x = ∑ i, x i • tflLin W b σ (Pi.single i 1) := by
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : TflCoord W σ → ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  change tflLinMap W b σ _ = _
  rw [map_sum]
  simp only [map_smul]
  rfl

/-- **Fixed-pair tail of `Λ`**: for unit `n, n'`, `P(s ≤ Re⟨n, Λ n'⟩) ≤ exp(-s² W/8)`. -/
theorem wl_lam_pair_tail (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (n n' : EuclideanSpace ℂ (LayerSite W σ)) (hn : ‖n‖ = 1) (hn' : ‖n'‖ = 1) {s : ℝ}
    (hs : 0 < s) :
    gaussianProduct (tflVar W b σ) {x | s ≤ (wlPair n n' (tflLin W b σ x)).re} ≤
      ENNReal.ofReal (Real.exp (-s ^ 2 / (8 / W : ℝ))) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set c : TflCoord W σ → ℝ := fun i => (wlPair n n' (tflLin W b σ (Pi.single i 1))).re with hc
  have hset : {x : TflCoord W σ → ℝ | s ≤ (wlPair n n' (tflLin W b σ x)).re} =
      {x | s ≤ ∑ i, c i * x i} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [wl_tflLin_eq_sum (b := b) x, wlPair_sum_smul]
  rw [hset]
  set Km : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    Matrix.of fun y x => (WithLp.ofLp n') y * star ((WithLp.ofLp n) x) with hKm
  have hHS : ∑ x, ∑ y, ‖Km x y‖ ^ 2 = 1 := by
    have h1 := sum_sq_eq_one_of_norm hn
    have h2 := sum_sq_eq_one_of_norm hn'
    simp only [hKm, Matrix.of_apply, norm_mul, norm_star, mul_pow]
    rw [← Finset.sum_mul_sum, h1, h2, one_mul]
  have hvar : ∑ i, (tflVar W b σ i : ℝ) * c i ^ 2 ≤ 4 / W := by
    have h := tfl_weighted_trace_le W b σ Km
    rw [hHS, mul_one] at h
    obtain ⟨hA, hB⟩ := tfl_TA_TB_le hW hb0 hb1
    have hle : ∀ i, (tflVar W b σ i : ℝ) * c i ^ 2 ≤
        (tflVar W b σ i : ℝ) * ‖(Km * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 := by
      intro i
      refine mul_le_mul_of_nonneg_left ?_ (tflVar W b σ i).2
      simp only [hc]
      rw [wlPair_eq_trace]
      have := Complex.abs_re_le_norm (Km * tflLin W b σ (Pi.single i 1)).trace
      calc _ = |((Km * tflLin W b σ (Pi.single i 1)).trace).re| ^ 2 := (sq_abs _).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2
    calc _ ≤ ∑ i, (tflVar W b σ i : ℝ) * ‖(Km * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hle i
      _ ≤ 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) := h
      _ ≤ 4 / W := by
          have : (4 : ℝ) / W = 2 * (1 / W) + 2 * (1 / W) := by ring
          rw [this]; linarith
  have ht : 2 * ∑ i, (tflVar W b σ i : ℝ) * c i ^ 2 ≤ ((Real.toNNReal (8 / W) : ℝ≥0) : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    have : (8 : ℝ) / W = 2 * (4 / W) := by ring
    linarith
  refine (wl_linear_tail (tflVar W b σ) c ht hs).trans (le_of_eq ?_)
  rw [Real.coe_toNNReal _ (by positivity)]

/-- **Tail of `‖Λ‖`**: `P(‖Λ‖ ≥ a) ≤ exp(W(48 - a²/32))`, `a > 0`. -/
theorem wl_lam_tail (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) {a : ℝ} (ha : 0 < a) :
    gaussianProduct (tflVar W b σ) {x | a ≤ ‖tflLin W b σ x‖} ≤
      ENNReal.ofReal (Real.exp (W * (48 - a ^ 2 / 32))) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨N, hN1, hNc, hN⟩ := bond_exists_net (LayerSite W σ)
  have h := measure_opNorm_ge_of_net (gaussianProduct (tflVar W b σ)) (tflLin W b σ) N N hN hN ha
    (p := Real.exp (-(a / 2) ^ 2 / (8 / W : ℝ))) fun n hn n' hn' =>
      wl_lam_pair_tail hW hb0 hb1 n n' (hN1 n hn) (hN1 n' hn') (by positivity)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcard := tfl_card_layerSite_le W σ
  have hN0 : (0 : ℝ) ≤ N.card := Nat.cast_nonneg _
  have hNN : (N.card : ℝ) * N.card ≤ Real.exp (48 * W) := by
    have h12 : (12 : ℝ) ^ (2 * Fintype.card (LayerSite W σ)) ≤ Real.exp (24 * W) := by
      calc (12 : ℝ) ^ (2 * Fintype.card (LayerSite W σ))
          ≤ Real.exp 3 ^ (2 * Fintype.card (LayerSite W σ)) :=
            pow_le_pow_left₀ (by norm_num) bond_twelve_le_exp_three _
        _ = Real.exp ((2 * Fintype.card (LayerSite W σ) : ℕ) * 3) :=
            (Real.exp_nat_mul 3 _).symm
        _ ≤ Real.exp (24 * W) := by
            refine Real.exp_le_exp.mpr ?_
            push_cast
            nlinarith
    have := mul_le_mul (hNc.trans h12) (hNc.trans h12) hN0 (by positivity)
    rwa [← Real.exp_add, show 24 * (W : ℝ) + 24 * W = 48 * W by ring] at this
  calc (N.card : ℝ) * N.card * Real.exp (-(a / 2) ^ 2 / (8 / W : ℝ))
      ≤ Real.exp (48 * W) * Real.exp (-(a / 2) ^ 2 / (8 / W : ℝ)) :=
        mul_le_mul_of_nonneg_right hNN (by positivity)
    _ = Real.exp (W * (48 - a ^ 2 / 32)) := by
        rw [← Real.exp_add]; congr 1; field_simp; ring

/-- **Moments from a dyadic tail** (the layer cake of `bond_lintegral_rpow_le`, generic law):
if `P(K ≥ 2ⁿ a₀) ≤ exp(W(24 - (2ⁿ a₀)²/(4b)))` with `a₀ = 10 √b`, then
`E(1 + K)^q ≤ C₂(b)^q` for real `1 ≤ q ≤ W`. -/
theorem wl_lintegral_rpow_le_of_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : Ω → ℝ} (hKm : Measurable K) (hK0 : ∀ ω, 0 ≤ K ω) {W : ℕ}
    {b q : ℝ} (hb : 0 < b) (hq1 : 1 ≤ q) (hqW : q ≤ W)
    (htail : ∀ n : ℕ, μ {ω | (2 : ℝ) ^ n * (10 * Real.sqrt b) ≤ K ω} ≤
      ENNReal.ofReal (Real.exp (W * (24 - ((2 : ℝ) ^ n * (10 * Real.sqrt b)) ^ 2 / (4 * b))))) :
    ∫⁻ ω, ENNReal.ofReal ((1 + K ω) ^ q) ∂μ ≤ ENNReal.ofReal (bondMomentConst b ^ q) := by
  set a₀ := 10 * Real.sqrt b with ha₀
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have ha0 : 0 < a₀ := by positivity
  have hq0 : 0 ≤ q := by linarith
  set S : ℕ → Set Ω := fun n => {ω | (2 : ℝ) ^ n * a₀ ≤ K ω} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n => measurableSet_le measurable_const hKm
  set d : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q) with hd
  set D : ℝ := (2 * (1 + a₀)) ^ q with hD
  have hpt : ∀ ω, ENNReal.ofReal ((1 + K ω) ^ q) ≤
      ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, (S n).indicator (fun _ => d n) ω := by
    intro ω
    refine (bond_rpow_le_tsum (hK0 ω) ha0 hq0).trans (le_of_eq ?_)
    congr 1
  have hterm : ∀ n, d n * μ (S n) ≤ ENNReal.ofReal D * 2⁻¹ ^ n := by
    intro n
    calc d n * μ (S n)
        ≤ ENNReal.ofReal (((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q) *
            ENNReal.ofReal (Real.exp (W * (24 - ((2 : ℝ) ^ n * a₀) ^ 2 / (4 * b)))) := by
          gcongr; exact htail n
      _ = ENNReal.ofReal (((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q *
            Real.exp (W * (24 - ((2 : ℝ) ^ n * a₀) ^ 2 / (4 * b)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (D * (1 / 2) ^ n) :=
          ENNReal.ofReal_le_ofReal (bond_dyadic_term_le hb hq1 hqW n)
      _ = ENNReal.ofReal D * 2⁻¹ ^ n := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), one_div,
            ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  calc ∫⁻ ω, ENNReal.ofReal ((1 + K ω) ^ q) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, (S n).indicator (fun _ => d n) ω) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((1 + a₀) ^ q) * μ Set.univ +
          ∑' n, ∫⁻ ω, (S n).indicator (fun _ => d n) ω ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_tsum fun n => (measurable_const.indicator (hSm n)).aemeasurable]
    _ = ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, d n * μ (S n) := by
        rw [measure_univ, mul_one]
        congr 1
        exact tsum_congr fun n => lintegral_indicator_const (hSm n) _
    _ ≤ ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, ENNReal.ofReal D * 2⁻¹ ^ n := by
        exact add_le_add le_rfl (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal ((1 + a₀) ^ q + 2 * D) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat, mul_comm (2 : ℝ≥0∞)]
    _ ≤ ENNReal.ofReal (bondMomentConst b ^ q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (1 + a₀) ^ q ≤ D := Real.rpow_le_rpow (by positivity) (by linarith) hq0
        have h3 : (3 : ℝ) ≤ 3 ^ q := by
          calc (3 : ℝ) = 3 ^ (1 : ℝ) := (Real.rpow_one 3).symm
            _ ≤ 3 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
        have hC : bondMomentConst b ^ q = 3 ^ q * D := by
          rw [hD, ← Real.mul_rpow (by norm_num) (by positivity)]
          unfold bondMomentConst
          congr 1
          ring
        have hD0 : 0 ≤ D := by positivity
        rw [hC]
        nlinarith

/-- `L^q` form of `wl_lintegral_rpow_le_of_tail`. -/
theorem wl_eLpNorm_le_of_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : Ω → ℝ} (hKm : Measurable K) (hK0 : ∀ ω, 0 ≤ K ω) {W : ℕ}
    {b q : ℝ} (hb : 0 < b) (hq1 : 1 ≤ q) (hqW : q ≤ W)
    (htail : ∀ n : ℕ, μ {ω | (2 : ℝ) ^ n * (10 * Real.sqrt b) ≤ K ω} ≤
      ENNReal.ofReal (Real.exp (W * (24 - ((2 : ℝ) ^ n * (10 * Real.sqrt b)) ^ 2 / (4 * b))))) :
    eLpNorm (fun ω => 1 + K ω) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (bondMomentConst b) := by
  have hq0 : 0 < q := by linarith
  have hp0 : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq0
  have hm : Measurable (fun ω => 1 + K ω) := measurable_const.add hKm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq0.le]
  have hint : ∫⁻ ω, ‖1 + K ω‖ₑ ^ q ∂μ = ∫⁻ ω, ENNReal.ofReal ((1 + K ω) ^ q) ∂μ := by
    refine lintegral_congr fun ω => ?_
    have := hK0 ω
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
  rw [hint]
  have hC := bondMomentConst_pos b
  calc (∫⁻ ω, ENNReal.ofReal ((1 + K ω) ^ q) ∂μ) ^ (1 / q)
      ≤ ENNReal.ofReal (bondMomentConst b ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (wl_lintegral_rpow_le_of_tail hKm hK0 hb hq1 hqW htail)
          (by positivity)
    _ = ENNReal.ofReal (bondMomentConst b) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← Real.rpow_mul hC.le, mul_one_div_cancel hq0.ne', Real.rpow_one]

/-- The moment constant of `Λ`: `C₂(392/25)`. -/
def wlLamConst : ℝ := bondMomentConst (392 / 25)

theorem wlLamConst_pos : 0 < wlLamConst := bondMomentConst_pos _

theorem wl_measurable_norm_tflLin :
    Measurable (fun x : TflCoord W σ → ℝ => ‖tflLin W b σ x‖) :=
  continuous_norm.measurable.comp (LinearMap.continuous_of_finiteDimensional (tflLinMap W b σ)).measurable

/-- **Moments of `Λ` in the coordinates**: `‖1 + ‖Λ‖‖_{L^q} ≤ wlLamConst` for `1 ≤ q ≤ W`,
uniformly in `W`, the shape and `0 < b < 1/2`. -/
theorem wl_lam_eLpNorm_le (hb0 : 0 < b) (hb1 : b < 1 / 2) {q : ℝ} (hq1 : 1 ≤ q)
    (hqW : q ≤ W) :
    eLpNorm (fun x => 1 + ‖tflLin W b σ x‖) (ENNReal.ofReal q) (gaussianProduct (tflVar W b σ)) ≤
      ENNReal.ofReal wlLamConst := by
  have hW : 0 < W := by
    have : (1 : ℝ) ≤ W := hq1.trans hqW
    exact_mod_cast this
  refine wl_eLpNorm_le_of_tail wl_measurable_norm_tflLin (fun _ => norm_nonneg _)
    (by norm_num) hq1 hqW fun k => ?_
  have hsb : 0 < Real.sqrt (392 / 25 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine (wl_lam_tail hW hb0 hb1 (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
  refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg W))
  have hsq : Real.sqrt (392 / 25 : ℝ) ^ 2 = 392 / 25 := Real.sq_sqrt (by norm_num)
  have ht : (1 : ℝ) ≤ ((2 : ℝ) ^ k) ^ 2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have e1 : ((2 : ℝ) ^ k * (10 * Real.sqrt (392 / 25))) ^ 2 / 32 = 49 * ((2 : ℝ) ^ k) ^ 2 := by
    rw [mul_pow, mul_pow, hsq]; ring
  have e2 : ((2 : ℝ) ^ k * (10 * Real.sqrt (392 / 25))) ^ 2 / (4 * (392 / 25)) =
      25 * ((2 : ℝ) ^ k) ^ 2 := by
    rw [mul_pow, mul_pow, hsq]; ring
  rw [e1, e2]
  linarith

/-- **Moments of `Λ` under `layerLaw`**. -/
theorem wl_lam_eLpNorm_le_layer (hb0 : 0 < b) (hb1 : b < 1 / 2) {q : ℝ} (hq1 : 1 ≤ q)
    (hqW : q ≤ W) :
    eLpNorm (fun ω => 1 + ‖wlLam ω‖) (ENNReal.ofReal q) (layerLaw W b σ) ≤
      ENNReal.ofReal wlLamConst := by
  have hm : Measurable (fun ω : LayerSample W σ => 1 + ‖wlLam ω‖) :=
    measurable_const.add (continuous_norm.measurable.comp wl_measurable_wlLam)
  rw [tfl_layerLaw_eq_map, eLpNorm_map_measure hm.aestronglyMeasurable
    (tfl_measurable_embed W b σ).aemeasurable]
  exact wl_lam_eLpNorm_le hb0 hb1 hq1 hqW

end RandomPart

/-!
## 4. The weighted moments (`moments`)
-/

section Moments

/-- Hölder: `‖f g‖_p ≤ ‖f‖_{2p} ‖g‖_{2p}`. -/
theorem wl_eLpNorm_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun ω => f ω * g ω) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal (2 * p)) μ * eLpNorm g (ENNReal.ofReal (2 * p)) μ := by
  have hT : ENNReal.HolderTriple (ENNReal.ofReal (2 * p)) (ENNReal.ofReal (2 * p))
      (ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hp,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring⟩
  have h := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal (2 * p)) (q := ENNReal.ofReal (2 * p))
    (r := ENNReal.ofReal p) hf hg
  have e : (fun ω => f ω * g ω) = f • g := by funext ω; simp [smul_eq_mul]
  rw [e]
  exact h

/-- `‖1 + 6 (1 + Λ) G‖_q ≤ 1 + 6 C_Λ C_A` from `‖1 + Λ‖_{2q} ≤ C_Λ`, `‖G‖_{2q} ≤ C_A`. -/
theorem wl_eLpNorm_F_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Lam Gn : Ω → ℝ} (hL : AEStronglyMeasurable Lam μ) (hG : AEStronglyMeasurable Gn μ)
    {q CL CA : ℝ} (hq : 1 ≤ q) (hCL0 : 0 ≤ CL) (hCA0 : 0 ≤ CA)
    (hCL : eLpNorm (fun ω => 1 + Lam ω) (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal CL)
    (hCA : eLpNorm Gn (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal CA) :
    eLpNorm (fun ω => 1 + 6 * ((1 + Lam ω) * Gn ω)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (1 + 6 * (CL * CA)) := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by rw [ENNReal.one_le_ofReal]; exact hq
  have hL1 : AEStronglyMeasurable (fun ω => 1 + Lam ω) μ := aestronglyMeasurable_const.add hL
  have hprod : AEStronglyMeasurable (fun ω => (1 + Lam ω) * Gn ω) μ := hL1.mul hG
  have e1 : (fun ω => 1 + 6 * ((1 + Lam ω) * Gn ω)) =
      (fun _ => (1 : ℝ)) + (6 : ℝ) • (fun ω => (1 + Lam ω) * Gn ω) := by
    funext ω; simp [smul_eq_mul]
  rw [e1]
  refine (eLpNorm_add_le hq1).trans ?_
  rw [eLpNorm_const_smul, eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ),
    measure_univ, ENNReal.one_rpow, mul_one]
  have h2 := wl_eLpNorm_mul_le hL1 hG (by linarith : (0 : ℝ) < q)
  calc ‖(1 : ℝ)‖ₑ + ‖(6 : ℝ)‖ₑ * eLpNorm (fun ω => (1 + Lam ω) * Gn ω) (ENNReal.ofReal q) μ
      ≤ ENNReal.ofReal 1 + ENNReal.ofReal 6 * (ENNReal.ofReal CL * ENNReal.ofReal CA) := by
        rw [Real.enorm_eq_ofReal (by norm_num), Real.enorm_eq_ofReal (by norm_num)]
        gcongr
        exact h2.trans (mul_le_mul' hCL hCA)
    _ = ENNReal.ofReal (1 + 6 * (CL * CA)) := by
        rw [← ENNReal.ofReal_mul hCL0, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by norm_num) (by positivity)]

variable {W : ℕ} {σ : LayerShape}

/-- The weight majorant `F = 1 + 6 (1 + ‖Λ‖) ‖𝒢‖`. -/
def wlF (E : ℝ) (z : ℂ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) : ℝ :=
  1 + 6 * ((1 + ‖wlLam ω‖) * ‖layerResolvent σ E z X ω‖)

theorem wl_measurable_wlF (E : ℝ) (z : ℂ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) :
    Measurable (wlF E z X) :=
  measurable_const.add (measurable_const.mul ((measurable_const.add
    (continuous_norm.measurable.comp wl_measurable_wlLam)).mul
      (measurable_norm_layerResolvent σ E z X)))

theorem wl_shift_le {r g : ℝ} (hr : r ≤ 5) (hl : 0 ≤ g) (lam : ℝ) (hlam : 0 ≤ lam) :
    1 + (r + lam) * g ≤ 1 + 6 * ((1 + lam) * g) := by
  nlinarith

/-- **Pointwise weighted bounds**: wherever `𝒢⁻¹` is invertible, for
Hermitian `X`, `|E| ≤ 2`, `|z| ≤ 3`: `‖𝒦 𝒢‖, ‖𝒢 𝒦*‖ ≤ F`. -/
theorem wl_weighted_le {E : ℝ} {z : ℂ} {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) (hE : |E| ≤ 2) (hz : ‖z‖ ≤ 3) (ω : LayerSample W σ)
    (hN : IsUnit (layerMatrix σ E z X ω).det) :
    ‖wlKh (m := PortSite W σ) (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X) *
        layerResolvent σ E z X ω‖ ≤ wlF E z X ω ∧
      ‖layerResolvent σ E z X ω *
        wlKh (m := PortSite W σ) (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)ᴴ‖ ≤
        wlF E z X ω := by
  set N := layerMatrix σ E z X ω with hNdef
  have h1 : N * layerResolvent σ E z X ω = 1 := mul_nonsing_inv _ hN
  have h2 : layerResolvent σ E z X ω * N = 1 := nonsing_inv_mul _ hN
  have hG0 := norm_nonneg (layerResolvent σ E z X ω)
  have hl0 := norm_nonneg (wlLam ω)
  have hr : ‖z‖ + |E| + 0 ≤ 5 := by linarith
  constructor
  · rw [wl_Kh_mul_eq h1]
    refine wl_norm_weighted_le.trans ?_
    have hb := wl_norm_Kh_sub_left_le E z X ω (le_refl (0 : ℝ))
    rw [wl_tflReg_zero] at hb
    refine (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb hG0)).trans ?_
    exact wl_shift_le hr hG0 _ hl0
  · rw [wl_mul_Kh_eq h2]
    refine wl_norm_weighted_le'.trans ?_
    have hb := wl_norm_Kh_sub_right_le E z hX ω (le_refl (0 : ℝ))
    rw [wl_tflReg_zero] at hb
    refine (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb hG0)).trans ?_
    exact wl_shift_le hr hG0 _ hl0

/-- **Moments of the weight majorant** (the Gaussian absorption lemma and §3): `b` and `η₀ > 0`
first, then for each `q ≥ 1` there are `C, W₀` such that for `W ≥ W₀`, every shape, Hermitian
`X`, real `E` and `Im z ≥ η₀`, `|z| ≤ 3`: `𝒢⁻¹` is a.s. invertible and `‖F‖_{L^q} ≤ C`. -/
theorem wl_moment_setup (hcount : ConditionalBlockGUECount) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {η₀ : ℝ} (hη₀ : 0 < η₀) {q : ℝ} (hq : 1 ≤ q) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ (σ : LayerShape)
      (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian → ∀ (E : ℝ) (z : ℂ),
      η₀ ≤ z.im → ‖z‖ ≤ 3 →
        (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
        eLpNorm (wlF E z X) (ENNReal.ofReal q) (layerLaw W b σ) ≤ ENNReal.ofReal C := by
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  refine ⟨1 + 6 * (wlLamConst * CA), max ⌈2 * q / ε₁⌉₊ ⌈2 * q⌉₊, by
    have := wlLamConst_pos; positivity, ?_⟩
  intro W hW hWW σ X hX E z hz hzM
  obtain ⟨hinv, hmom⟩ := habs W hW σ X hX E z hz hzM
  have hW1 : 2 * q ≤ ε₁ * W := by
    have h1 : 2 * q / ε₁ ≤ (W : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans hWW)
    rw [div_le_iff₀ hε₁] at h1; linarith
  have hW2 : 2 * q ≤ W :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hWW)
  have := bond_isProbabilityMeasure_layerLaw W b σ
  refine ⟨hinv, ?_⟩
  exact wl_eLpNorm_F_le (continuous_norm.measurable.comp wl_measurable_wlLam).aestronglyMeasurable
    (measurable_norm_layerResolvent σ E z X).aestronglyMeasurable hq wlLamConst_pos.le hCA.le
    (wl_lam_eLpNorm_le_layer hb0 hb1 (by linarith) hW2) (hmom _ (by linarith) hW1)

/-- Uniform bulk data: `Im z_∂ ≥ η₀ > 0`, `|z_∂| ≤ 3`, `|E| ≤ 2` on `bulkInterval κ`. -/
theorem wl_bulk {b κ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ E ∈ bulkInterval κ,
      η₀ ≤ (boundaryZ b E).im ∧ ‖boundaryZ b E‖ ≤ 3 ∧ |E| ≤ 2 := by
  obtain ⟨α₀, hα₀, -, hbulk⟩ := cmp_bulk_setup hκ
  refine ⟨(1 - b) * α₀, by nlinarith, fun E hE => ?_⟩
  obtain ⟨hE2, -, ha⟩ := hbulk E hE
  refine ⟨?_, norm_boundaryZ_le hb0.le (by linarith) hE2.le, hE2.le⟩
  rw [boundaryZ_im hE2.le]
  nlinarith

end Moments

/-!
## 5. The contract fields `moments` and `unrestricted`
-/

section Fields

theorem wl_continuous_toBlocks11 {n m : Type*} :
    Continuous (fun M : Matrix (n ⊕ m) (n ⊕ m) ℂ => M.toBlocks₁₁) :=
  continuous_id.matrix_submatrix Sum.inl Sum.inl

theorem wl_continuous_toBlocks12 {n m : Type*} :
    Continuous (fun M : Matrix (n ⊕ m) (n ⊕ m) ℂ => M.toBlocks₁₂) :=
  continuous_id.matrix_submatrix Sum.inl Sum.inr

theorem wlF_nonneg {W : ℕ} {σ : LayerShape} (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) : 0 ≤ wlF E z X ω := by
  unfold wlF; positivity

/-- **`moments`** (the weighted-layer lemma): the weighted
factors `K𝒢₁₁`, `𝒢₁₁K*` and `L = K𝒢₁₂` have `L^p` norms at most `C_p` for `W ≥ W₀(p)`,
uniformly in Hermitian `X` and `E ∈ I`. -/
theorem wl_moments (hcount : ConditionalBlockGUECount) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let G := fun ω => layerResolvent .separate E (boundaryZ b E) X ω
      eLpNorm (fun ω => ‖K * (G ω).toBlocks₁₁‖) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cp ∧
      eLpNorm (fun ω => ‖(G ω).toBlocks₁₁ * Kᴴ‖) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cp ∧
      eLpNorm (fun ω => ‖K * (G ω).toBlocks₁₂‖) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cp := by
  intro b hb0 hb1 κ hκ p hp
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨C, W₀, -, h⟩ := wl_moment_setup hcount hb0 hb1 hη₀ hp
  refine ⟨C, W₀, ?_⟩
  intro W hW hWW X hX E hE μ K G
  obtain ⟨hz, hzM, hE2⟩ := hbulk E hE
  obtain ⟨hinv, hF⟩ := h W hW hWW .separate X hX E _ hz hzM
  have hpt := hinv.mono fun ω hω => wl_weighted_le (σ := .separate) hX hE2 hzM ω hω
  have hGm : Measurable G := measurable_layerResolvent .separate E (boundaryZ b E) X
  have hFn : ∀ ω, ‖wlF (σ := .separate) E (boundaryZ b E) X ω‖ =
      wlF (σ := .separate) E (boundaryZ b E) X ω := fun ω =>
    Real.norm_of_nonneg (wlF_nonneg _ _ _ ω)
  refine ⟨?_, ?_, ?_⟩
  · have hc : Continuous (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
        ‖K * M.toBlocks₁₁‖) :=
      continuous_norm.comp (continuous_const.matrix_mul wl_continuous_toBlocks11)
    have hm : Measurable (fun ω => ‖K * (G ω).toBlocks₁₁‖) := hc.measurable.comp hGm
    refine (eLpNorm_mono_ae hm.aestronglyMeasurable (hpt.mono fun ω hω => ?_)).trans hF
    rw [norm_norm, hFn, ← wl_Kh_mul_toBlocks11]
    exact (wl_norm_toBlocks11_le _).trans hω.1
  · have hc : Continuous (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
        ‖M.toBlocks₁₁ * Kᴴ‖) :=
      continuous_norm.comp (wl_continuous_toBlocks11.matrix_mul continuous_const)
    have hm : Measurable (fun ω => ‖(G ω).toBlocks₁₁ * Kᴴ‖) := hc.measurable.comp hGm
    refine (eLpNorm_mono_ae hm.aestronglyMeasurable (hpt.mono fun ω hω => ?_)).trans hF
    rw [norm_norm, hFn, ← wl_mul_Kh_toBlocks11]
    exact (wl_norm_toBlocks11_le _).trans hω.2
  · have hc : Continuous (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
        ‖K * M.toBlocks₁₂‖) :=
      continuous_norm.comp (continuous_const.matrix_mul wl_continuous_toBlocks12)
    have hm : Measurable (fun ω => ‖K * (G ω).toBlocks₁₂‖) := hc.measurable.comp hGm
    refine (eLpNorm_mono_ae hm.aestronglyMeasurable (hpt.mono fun ω hω => ?_)).trans hF
    rw [norm_norm, hFn, ← wl_Kh_mul_toBlocks12]
    exact (wl_norm_toBlocks12_le _).trans hω.1

open scoped ComplexOrder in
theorem wl_trace_re_nonneg {n : Type*} [Fintype n] {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    0 ≤ Y.trace.re :=
  (Complex.le_def.mp hY.trace_nonneg).1

/-- **`unrestricted`** (the weighted-layer lemma):
`‖W⁻¹ Tr L*YL‖_p ≤ C_p u` for every Hermitian `X`, `E ∈ I`, `Y ⪰ 0`, `W ≥ W₀(p)`. -/
theorem wl_unrestricted (hcount : ConditionalBlockGUECount) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
    ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Lm := fun ω => K * (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂
      eLpNorm (fun ω => (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cp * ((W : ℝ)⁻¹ * Y.trace.re)) := by
  intro b hb0 hb1 κ hκ p hp
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨C, W₀, hC, h⟩ := wl_moment_setup hcount hb0 hb1 hη₀ (q := 2 * p) (by linarith)
  refine ⟨C ^ 2, W₀, ?_⟩
  intro W hW hWW X hX E hE Y hY μ K Lm
  obtain ⟨hz, hzM, hE2⟩ := hbulk E hE
  obtain ⟨hinv, hF⟩ := h W hW hWW .separate X hX E _ hz hzM
  set u : ℝ := (W : ℝ)⁻¹ * Y.trace.re with hu
  have hu0 : 0 ≤ u := mul_nonneg (by positivity) (wl_trace_re_nonneg hY)
  set F := wlF (σ := .separate) E (boundaryZ b E) X with hFdef
  have hFm : Measurable F := wl_measurable_wlF _ _ _
  have hGm := measurable_layerResolvent .separate E (boundaryZ b E) X
  have hLc : Continuous (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
      K * M.toBlocks₁₂) := continuous_const.matrix_mul wl_continuous_toBlocks12
  have hLm : Measurable Lm := hLc.measurable.comp hGm
  have htm : Measurable (fun ω => (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re) := by
    have hc : Continuous (fun M : Matrix (Fin 2 × Fin W) (PortSite W .separate) ℂ =>
        (W : ℝ)⁻¹ * (Mᴴ * Y * M).trace.re) := by fun_prop
    exact hc.measurable.comp hLm
  have hpt : ∀ᵐ ω ∂μ, ‖(W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re‖ ≤ ‖u * (F ω * F ω)‖ := by
    filter_upwards [hinv] with ω hω
    have hL : ‖Lm ω‖ ≤ F ω := by
      change ‖K * (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂‖ ≤ _
      rw [← wl_Kh_mul_toBlocks12]
      exact (wl_norm_toBlocks12_le _).trans (wl_weighted_le (σ := .separate) hX hE2 hzM ω hω).1
    obtain ⟨h0, h1⟩ := wl_trace_weight_le hY (Lm ω)
    have hF0 := wlF_nonneg (σ := .separate) E (boundaryZ b E) X ω
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hL2 : ‖Lm ω‖ ^ 2 ≤ F ω * F ω := by
      rw [sq]; exact mul_le_mul hL hL (norm_nonneg _) hF0
    calc (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re ≤ (W : ℝ)⁻¹ * (‖Lm ω‖ ^ 2 * Y.trace.re) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (W : ℝ)⁻¹ * ((F ω * F ω) * Y.trace.re) := by
          gcongr
          exact wl_trace_re_nonneg hY
      _ = u * (F ω * F ω) := by rw [hu]; ring
  refine (eLpNorm_mono_ae htm.aestronglyMeasurable hpt).trans ?_
  have e1 : (fun ω => u * (F ω * F ω)) = u • (fun ω => F ω * F ω) := rfl
  rw [e1, eLpNorm_const_smul, Real.enorm_eq_ofReal hu0]
  have h2 := wl_eLpNorm_mul_le (μ := μ) hFm.aestronglyMeasurable hFm.aestronglyMeasurable
    (by linarith : (0 : ℝ) < p)
  calc ENNReal.ofReal u * eLpNorm (fun ω => F ω * F ω) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal u * (ENNReal.ofReal C * ENNReal.ofReal C) := by
        gcongr
        exact h2.trans (mul_le_mul' hF hF)
    _ = ENNReal.ofReal (C ^ 2 * u) := by
        rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul hu0]
        congr 1; ring

end Fields

/-!
## 6. The clock functional and its gradient
-/

section ClockFunctional

variable {W : ℕ} {σ : LayerShape}

/-- The clock functional `M ↦ W⁻¹ Tr(Ŷ (𝒦 M Q)(𝒦 M Q)*)` on layer matrices. -/
def wlTr (Kh Yh M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) : ℂ :=
  (W : ℂ)⁻¹ * (Yh * ((Kh * M * wlQ (PhysSite W σ) (PortSite W σ)) *
    (Kh * M * wlQ (PhysSite W σ) (PortSite W σ))ᴴ)).trace

theorem wl_continuous_wlTr (Kh Yh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Continuous (wlTr Kh Yh) := by
  have hA : Continuous (fun M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      Kh * M * wlQ (PhysSite W σ) (PortSite W σ)) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact continuous_const.mul
    ((continuous_const.matrix_mul (hA.matrix_mul hA.matrix_conjTranspose)).matrix_trace)

theorem wl_Kh_mul_Q (K : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    wlKh K * M * wlQ (PhysSite W σ) (PortSite W σ) = fromBlocks 0 (K * M.toBlocks₁₂) 0 0 := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [wlKh, wlQ, fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₂,
      Matrix.one_apply]

theorem wl_trace_fromBlocks {n m : Type*} [Fintype n] [Fintype m] (A : Matrix n n ℂ)
    (B : Matrix n m ℂ) (C : Matrix m n ℂ) (D : Matrix m m ℂ) :
    (fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- `W⁻¹ Tr(Ŷ 𝓛 𝓛*) = W⁻¹ Tr(L* Y L)` with `𝓛 = 𝒦 M Q`, `L = K M₁₂`. -/
theorem wlTr_eq (K Y : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    wlTr (wlKh K) (wlKh Y) M =
      (W : ℂ)⁻¹ * ((K * M.toBlocks₁₂)ᴴ * Y * (K * M.toBlocks₁₂)).trace := by
  rw [wlTr, wl_Kh_mul_Q, fromBlocks_conjTranspose, fromBlocks_multiply, wlKh,
    fromBlocks_multiply, wl_trace_fromBlocks]
  simp only [conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    trace_zero]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (Y * (K * M.toBlocks₁₂)), Matrix.mul_assoc]

/-- `wlHS diag(Y, 0) = wlHS Y`. -/
theorem wlHS_wlKh (Y : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) :
    wlHS (wlKh (m := PortSite W σ) Y) = wlHS Y := by
  unfold wlHS
  simp [wlKh, Fintype.sum_sum_type, fromBlocks]

/-- **Derivative of the clock functional along a path** `y ↦ G(y)` with `dG(x) = T`. -/
theorem wl_hasFDerivAt_wlTr {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {G : V → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    {T : V →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ} {x : V} (hG : HasFDerivAt G T x)
    (Kh Yh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ∃ S : V →L[ℝ] ℂ, HasFDerivAt (fun y => wlTr Kh Yh (G y)) S x ∧ ∀ v, S v =
      (W : ℂ)⁻¹ * (Yh * ((Kh * T v * wlQ (PhysSite W σ) (PortSite W σ)) *
        (Kh * G x * wlQ (PhysSite W σ) (PortSite W σ))ᴴ +
        (Kh * G x * wlQ (PhysSite W σ) (PortSite W σ)) *
          (Kh * T v * wlQ (PhysSite W σ) (PortSite W σ))ᴴ)).trace := by
  set Q := wlQ (PhysSite W σ) (PortSite W σ)
  set L := ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) Kh Q
  have hA : HasFDerivAt (fun y => Kh * G y * Q) (L.comp T) x := L.hasFDerivAt.comp x hG
  have hAh := tcvConjCLM.hasFDerivAt.comp x hA
  have hP := hA.mul' hAh
  have hS := (tflTraceCLM W σ Yh).hasFDerivAt.comp x hP
  refine ⟨_, hS, fun v => ?_⟩
  simp only [ContinuousLinearMap.comp_apply, _root_.add_apply,
    _root_.smul_apply, tflTraceCLM_apply, tcvConjCLM_apply, smul_eq_mul]
  rw [add_comm (Kh * G x * Q * _)]
  rfl

/-- `|Tr(Ŷ A B*)| = |Tr(Ŷ B A*)|` for Hermitian `Ŷ`. -/
theorem wl_norm_trace_swap {n : Type*} [Fintype n] {Yh : Matrix n n ℂ} (hY : Yhᴴ = Yh)
    (A B : Matrix n n ℂ) : ‖(Yh * (A * Bᴴ)).trace‖ = ‖(Yh * (B * Aᴴ)).trace‖ := by
  have h : (Yh * (A * Bᴴ)).trace = star (Yh * (B * Aᴴ)).trace := by
    rw [← trace_conjTranspose]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hY]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.mul_assoc]
  rw [h, norm_star]

end ClockFunctional

/-!
## 7. The regularized clock in the real coordinates
-/

section NoiseCoord

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)

/-- The regularized clock `t_κ(x) = W⁻¹ Tr(Ŷ (𝒦 G_κ Q)(𝒦 G_κ Q)*)` in coordinates. -/
def wlTk (Kh Yh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (κ : ℝ) (x : TflCoord W σ → ℝ) : ℂ :=
  wlTr Kh Yh (tcvG W b σ E z X κ x)

variable {X} in
theorem wlTk_contDiff (hX : X.IsHermitian) (hz : 0 ≤ z.im)
    (Kh Yh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ 1 (wlTk W b σ E z X Kh Yh κ) := by
  set Q := wlQ (PhysSite W σ) (PortSite W σ)
  set L := ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) Kh Q
  have hG := tcv_G_contDiff W b σ E z hX hz hκ
  have hA : ContDiff ℝ 1 (fun x => L (tcvG W b σ E z X κ x)) := L.contDiff.comp hG
  have hAh := (tcvConjCLM (n := LayerSite W σ)).contDiff.comp hA
  have hP := hA.mul hAh
  exact (tflTraceCLM W σ Yh).contDiff.comp hP

variable {W b X} in
/-- **Gradient bound for the regularized clock**: for Hermitian `Y`, at every
point, `(Σᵢ vᵢ |∂ᵢ t_κ|²)^{1/2} ≤ (4/W) √(W⁻¹ ‖Y‖²_HS) ‖G_κ‖ ‖𝒦 G_κ‖²`. -/
theorem wl_grad_le (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) (K Y : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (hY : Y.IsHermitian)
    {κ : ℝ} (hκ : 0 < κ) (x : TflCoord W σ → ℝ) :
    weightedGradientNorm (tflVar W b σ) (wlTk W b σ E z X (wlKh K) (wlKh Y) κ) x ≤
      4 / W * Real.sqrt ((W : ℝ)⁻¹ * wlHS Y) * ‖tcvG W b σ E z X κ x‖ *
        ‖wlKh (m := PortSite W σ) K * tcvG W b σ E z X κ x‖ ^ 2 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set Q := wlQ (PhysSite W σ) (PortSite W σ) with hQ
  set G := tcvG W b σ E z X κ x with hGdef
  set Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := wlKh K with hKh
  set Yh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := wlKh Y with hYhd
  have hYh : Yhᴴ = Yh := by rw [hYhd, wlKh_conjTranspose, hY.eq]
  set A := Kh * G * Q with hA
  set Mx := G * Q * Aᴴ * (Yh * (Kh * G)) with hMx
  obtain ⟨T, hT, hTv⟩ := tcv_G_hasFDerivAt W b σ E z hX hz hκ x
  obtain ⟨S, hS, hSv⟩ := wl_hasFDerivAt_wlTr hT Kh Yh
  have hfd : fderiv ℝ (wlTk W b σ E z X Kh Yh κ) x = S := hS.fderiv
  have hdi : ∀ i : TflCoord W σ, ‖fderiv ℝ (wlTk W b σ E z X Kh Yh κ) x (Pi.single i 1)‖ ≤
      2 * (W : ℝ)⁻¹ * ‖(Mx * tflLin W b σ (Pi.single i 1)).trace‖ := by
    intro i
    set Λ := tflLin W b σ (Pi.single i 1) with hΛ
    set dA := Kh * T (Pi.single i 1) * Q with hdA
    rw [hfd, hSv]
    change ‖(W : ℂ)⁻¹ * (Yh * (dA * Aᴴ + A * dAᴴ)).trace‖ ≤ _
    rw [Matrix.mul_add, trace_add, norm_mul, norm_inv, Complex.norm_natCast]
    have hsw := wl_norm_trace_swap hYh A dA
    have htr : (Yh * (dA * Aᴴ)).trace = -(Mx * Λ).trace := by
      rw [hdA, hTv, hMx]
      simp only [Matrix.mul_neg, Matrix.neg_mul, trace_neg, tcvLam_apply]
      refine congrArg Neg.neg ?_
      rw [show Yh * (Kh * (G * Λ * G) * Q * Aᴴ) = (Yh * (Kh * (G * Λ))) * (G * Q * Aᴴ) by
        simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    calc (W : ℝ)⁻¹ * ‖(Yh * (dA * Aᴴ)).trace + (Yh * (A * dAᴴ)).trace‖
        ≤ (W : ℝ)⁻¹ * (‖(Yh * (dA * Aᴴ)).trace‖ + ‖(Yh * (A * dAᴴ)).trace‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.mpr hW'.le)
      _ = 2 * (W : ℝ)⁻¹ * ‖(Mx * Λ).trace‖ := by
          rw [hsw, htr, norm_neg]; ring
  -- the Hilbert–Schmidt bound on `Mx`
  have hAn : ‖A‖ ≤ ‖Kh * G‖ := by
    calc ‖A‖ ≤ ‖Kh * G‖ * ‖Q‖ := norm_mul_le _ _
      _ ≤ ‖Kh * G‖ * 1 := mul_le_mul_of_nonneg_left wl_norm_Q_le (norm_nonneg _)
      _ = _ := mul_one _
  have hP : ‖G * Q * Aᴴ‖ ≤ ‖G‖ * ‖Kh * G‖ := by
    calc ‖G * Q * Aᴴ‖ ≤ ‖G * Q‖ * ‖Aᴴ‖ := norm_mul_le _ _
      _ ≤ (‖G‖ * 1) * ‖A‖ := by
          rw [l2_opNorm_conjTranspose]
          gcongr
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left wl_norm_Q_le (norm_nonneg _))
      _ ≤ ‖G‖ * ‖Kh * G‖ := by rw [mul_one]; gcongr
  have hHS : wlHS Mx ≤ (‖G‖ * ‖Kh * G‖ ^ 2) ^ 2 * wlHS Y := by
    have h1 := wlHS_mul_left_le (G * Q * Aᴴ) (Yh * (Kh * G))
    have h2 := wlHS_mul_right_le Yh (Kh * G)
    have hYs : wlHS Yh = wlHS Y := by rw [hYhd, wlHS_wlKh]
    rw [hYs] at h2
    have hY0 := wlHS_nonneg Y
    have hP2 : ‖G * Q * Aᴴ‖ ^ 2 ≤ (‖G‖ * ‖Kh * G‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hP 2
    calc wlHS Mx ≤ ‖G * Q * Aᴴ‖ ^ 2 * wlHS (Yh * (Kh * G)) := h1
      _ ≤ (‖G‖ * ‖Kh * G‖) ^ 2 * (wlHS Y * ‖Kh * G‖ ^ 2) :=
          mul_le_mul hP2 h2 (wlHS_nonneg _) (sq_nonneg _)
      _ = (‖G‖ * ‖Kh * G‖ ^ 2) ^ 2 * wlHS Y := by ring
  obtain ⟨hTA, hTB⟩ := tfl_TA_TB_le hW hb0 hb1
  have hsum : ∑ i, (tflVar W b σ i : ℝ) *
      ‖fderiv ℝ (wlTk W b σ E z X Kh Yh κ) x (Pi.single i 1)‖ ^ 2 ≤
      (4 / W * Real.sqrt ((W : ℝ)⁻¹ * wlHS Y) * ‖G‖ * ‖Kh * G‖ ^ 2) ^ 2 := by
    have hw := tfl_weighted_trace_le W b σ Mx
    have hc : 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) ≤ 4 / W := by
      have : (4 : ℝ) / W = 2 * (1 / W) + 2 * (1 / W) := by ring
      rw [this]; linarith
    have hsq : Real.sqrt ((W : ℝ)⁻¹ * wlHS Y) ^ 2 = (W : ℝ)⁻¹ * wlHS Y :=
      Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr hW'.le) (wlHS_nonneg Y))
    calc ∑ i, (tflVar W b σ i : ℝ) *
          ‖fderiv ℝ (wlTk W b σ E z X Kh Yh κ) x (Pi.single i 1)‖ ^ 2
        ≤ ∑ i, (tflVar W b σ i : ℝ) *
            ((2 * (W : ℝ)⁻¹) ^ 2 * ‖(Mx * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (tflVar W b σ i).2
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hdi i) 2
      _ = (2 * (W : ℝ)⁻¹) ^ 2 *
            ∑ i, (tflVar W b σ i : ℝ) * ‖(Mx * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (2 * (W : ℝ)⁻¹) ^ 2 * ((4 / W) * wlHS Mx) := by
          gcongr
          exact hw.trans (mul_le_mul_of_nonneg_right hc (wlHS_nonneg _))
      _ ≤ (2 * (W : ℝ)⁻¹) ^ 2 * ((4 / W) * ((‖G‖ * ‖Kh * G‖ ^ 2) ^ 2 * wlHS Y)) := by
          gcongr
      _ = (4 / W * Real.sqrt ((W : ℝ)⁻¹ * wlHS Y) * ‖G‖ * ‖Kh * G‖ ^ 2) ^ 2 := by
          rw [show (4 / W * Real.sqrt ((W : ℝ)⁻¹ * wlHS Y) * ‖G‖ * ‖Kh * G‖ ^ 2) ^ 2 =
            (4 / W) ^ 2 * Real.sqrt ((W : ℝ)⁻¹ * wlHS Y) ^ 2 * ‖G‖ ^ 2 * (‖Kh * G‖ ^ 2) ^ 2 by
              ring, hsq]
          field_simp
          ring
  unfold weightedGradientNorm
  calc Real.sqrt (∑ i, (tflVar W b σ i : ℝ) *
        ‖fderiv ℝ (wlTk W b σ E z X Kh Yh κ) x (Pi.single i 1)‖ ^ 2)
      ≤ Real.sqrt ((4 / W * Real.sqrt ((W : ℝ)⁻¹ * wlHS Y) * ‖G‖ * ‖Kh * G‖ ^ 2) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = 4 / W * Real.sqrt ((W : ℝ)⁻¹ * wlHS Y) * ‖G‖ * ‖Kh * G‖ ^ 2 :=
        Real.sqrt_sq (mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hW'.le)
          (Real.sqrt_nonneg _)) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 2))

end NoiseCoord

/-!
## 8. The clock noise: fixed `κ` and the limit `κ → 0`
-/

section NoiseCore

variable {W : ℕ} {b : ℝ} {σ : LayerShape}

/-- `|wlTr 𝒦 Ŷ M| ≤ 4 ‖Ŷ‖ (‖𝒦‖ ‖M‖)²`. -/
theorem wl_norm_wlTr_le (hW : 0 < W) (Kh Yh M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ‖wlTr Kh Yh M‖ ≤ 4 * ‖Yh‖ * (‖Kh‖ * ‖M‖) ^ 2 := by
  set A := Kh * M * wlQ (PhysSite W σ) (PortSite W σ)
  have hA : ‖A‖ ≤ ‖Kh‖ * ‖M‖ := by
    calc ‖A‖ ≤ ‖Kh * M‖ * ‖wlQ (PhysSite W σ) (PortSite W σ)‖ := norm_mul_le _ _
      _ ≤ (‖Kh‖ * ‖M‖) * 1 := mul_le_mul (norm_mul_le _ _) wl_norm_Q_le (norm_nonneg _)
          (by positivity)
      _ = _ := mul_one _
  have h1 := tcv_tr_le σ hW (Yh * (A * Aᴴ))
  rw [tcvTr_apply] at h1
  refine h1.trans ?_
  have h2 : ‖Yh * (A * Aᴴ)‖ ≤ ‖Yh‖ * (‖Kh‖ * ‖M‖) ^ 2 := by
    calc ‖Yh * (A * Aᴴ)‖ ≤ ‖Yh‖ * (‖A‖ * ‖Aᴴ‖) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _ = ‖Yh‖ * ‖A‖ ^ 2 := by rw [l2_opNorm_conjTranspose]; ring
      _ ≤ ‖Yh‖ * (‖Kh‖ * ‖M‖) ^ 2 := by gcongr
  linarith

/-- `‖𝒦 G_κ‖ ≤ 2 F` and `‖G_κ‖ ≤ 2F` for `0 < κ ≤ 1`, `|E| ≤ 2`, `|z| ≤ 3`, wherever `𝒢⁻¹` is
invertible (`F = wlF` at the embedded sample). -/
theorem wl_reg_weighted_le {E : ℝ} {z : ℂ} {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) (hz : 0 ≤ z.im) (hE : |E| ≤ 2) (hzM : ‖z‖ ≤ 3) {κ : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (x : TflCoord W σ → ℝ)
    (hx : IsUnit (layerMatrix σ E z X (tflEmbed W b σ x)).det) :
    ‖tcvG W b σ E z X κ x‖ ≤ 2 * wlF E z X (tflEmbed W b σ x) ∧
      ‖wlKh (m := PortSite W σ) (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X) *
        tcvG W b σ E z X κ x‖ ≤ 2 * wlF E z X (tflEmbed W b σ x) := by
  have hG2 := tflPsi_inv_le_two W b σ E z hX hz hκ x hx
  change ‖tcvG W b σ E z X κ x‖ ≤ _ at hG2
  set g := ‖layerResolvent σ E z X (tflEmbed W b σ x)‖ with hg
  set lam := ‖wlLam (tflEmbed W b σ x)‖ with hlam
  have hg0 : 0 ≤ g := norm_nonneg _
  have hl0 : 0 ≤ lam := norm_nonneg _
  have hFe : wlF E z X (tflEmbed W b σ x) = 1 + 6 * ((1 + lam) * g) := rfl
  refine ⟨hG2.trans ?_, ?_⟩
  · rw [hFe]; nlinarith
  · have hU : IsUnit (tflReg κ (layerMatrix σ E z X (tflEmbed W b σ x))) := by
      rw [← tflPsi_eq]; exact tflPsi_isUnit W b σ E z hX hz hκ x
    have hNG : tflReg κ (layerMatrix σ E z X (tflEmbed W b σ x)) * tcvG W b σ E z X κ x = 1 := by
      rw [tcvG, tflPsi_eq]; exact Ring.mul_inverse_cancel _ hU
    rw [wl_Kh_mul_eq hNG]
    refine wl_norm_weighted_le.trans ?_
    have hb := wl_norm_Kh_sub_left_le E z X (tflEmbed W b σ x) hκ.le
    have hGn0 := norm_nonneg (tcvG W b σ E z X κ x)
    calc 1 + ‖wlKh (z • 1 - X) - wlJ (PhysSite W σ) (PortSite W σ) *
          tflReg κ (layerMatrix σ E z X (tflEmbed W b σ x))‖ * ‖tcvG W b σ E z X κ x‖
        ≤ 1 + (‖z‖ + |E| + κ + lam) * (2 * g) :=
          add_le_add le_rfl (mul_le_mul hb hG2 hGn0 (by positivity))
      _ ≤ 2 * wlF E z X (tflEmbed W b σ x) := by
          rw [hFe]
          have : ‖z‖ + |E| + κ ≤ 6 := by linarith
          nlinarith

/-- **Core clock-noise bound in the coordinates**, from the gradient
inequality with constant `C_g`, a.e. invertibility, `‖F³‖_p ≤ C₃` and `‖𝒢‖ ∈ L²`:
`‖t - Et‖_p ≤ C_g √p (32/W) √(W⁻¹‖Y‖²_HS) C₃` for `t = W⁻¹ Tr(Ŷ 𝓛𝓛*)`. -/
theorem wl_noise_core {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) {E : ℝ} {z : ℂ} (hz : 0 ≤ z.im) (hE : |E| ≤ 2) (hzM : ‖z‖ ≤ 3)
    (Y : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (hY : Y.IsHermitian) {p : ℝ} (hp : 1 ≤ p)
    {C3 : ℝ}
    (hinv : ∀ᵐ x ∂gaussianProduct (tflVar W b σ),
      IsUnit (layerMatrix σ E z X (tflEmbed W b σ x)).det)
    (hF3 : eLpNorm (fun x => wlF E z X (tflEmbed W b σ x) ^ 3) (ENNReal.ofReal p)
      (gaussianProduct (tflVar W b σ)) ≤ ENNReal.ofReal C3)
    (hG2 : Integrable (fun x => ‖layerResolvent σ E z X (tflEmbed W b σ x)‖ ^ 2)
      (gaussianProduct (tflVar W b σ))) :
    eLpNorm (fun x => wlTr (wlKh (z • 1 - X)) (wlKh Y) (layerResolvent σ E z X (tflEmbed W b σ x)) -
        ∫ y, wlTr (wlKh (z • 1 - X)) (wlKh Y) (layerResolvent σ E z X (tflEmbed W b σ y))
          ∂gaussianProduct (tflVar W b σ)) (ENNReal.ofReal p) (gaussianProduct (tflVar W b σ)) ≤
      ENNReal.ofReal (Cg * Real.sqrt p * (32 / W * Real.sqrt ((W : ℝ)⁻¹ * wlHS Y)) * C3) := by
  set μ := gaussianProduct (tflVar W b σ) with hμ
  set Φ := tflEmbed W b σ with hΦdef
  set Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := wlKh (z • 1 - X) with hKh
  set Yh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := wlKh Y with hYh
  set Gr : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (Φ x) with hGrdef
  have hGr : Measurable Gr := (measurable_layerResolvent σ E z X).comp (tfl_measurable_embed W b σ)
  set F : (TflCoord W σ → ℝ) → ℂ := fun x => wlTr Kh Yh (Gr x) with hFdef
  have hF : Measurable F := (wl_continuous_wlTr Kh Yh).measurable.comp hGr
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set s : ℝ := Real.sqrt ((W : ℝ)⁻¹ * wlHS Y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set c : ℝ := 32 / W * s with hc
  have hc0 : 0 ≤ c := by positivity
  set B : ℝ≥0∞ := ENNReal.ofReal (Cg * Real.sqrt p * c * C3) with hB
  have hFm : Measurable (fun x => wlF E z X (Φ x)) :=
    (wl_measurable_wlF E z X).comp (tfl_measurable_embed W b σ)
  -- the bound for each `0 < κ ≤ 1`
  have hstep : ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
      eLpNorm (fun x => wlTk W b σ E z X Kh Yh κ x - ∫ y, wlTk W b σ E z X Kh Yh κ y ∂μ)
        (ENNReal.ofReal p) μ ≤ B := by
    intro κ hκ hκ1
    have hC := wlTk_contDiff W b σ E z hX hz Kh Yh hκ
    have hcont : Continuous (wlTk W b σ E z X Kh Yh κ) := hC.continuous
    have hmem : MemLp (wlTk W b σ E z X Kh Yh κ) (ENNReal.ofReal p) μ := by
      refine MemLp.of_bound hcont.aestronglyMeasurable (4 * ‖Yh‖ * (‖Kh‖ * κ⁻¹) ^ 2)
        (ae_of_all _ fun x => ?_)
      refine (wl_norm_wlTr_le hW Kh Yh _).trans ?_
      gcongr
      exact tcv_G_le W b σ E z hX hz hκ x
    have h1 := hgr p hp (TflCoord W σ) (tflVar W b σ) (wlTk W b σ E z X Kh Yh κ) hC hmem
    refine h1.trans ?_
    have hwc : Continuous (weightedGradientNorm (tflVar W b σ) (wlTk W b σ E z X Kh Yh κ)) := by
      have hd := hC.continuous_fderiv one_ne_zero
      unfold weightedGradientNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    have hwle : ∀ᵐ x ∂μ, ‖weightedGradientNorm (tflVar W b σ) (wlTk W b σ E z X Kh Yh κ) x‖ ≤
        ‖c * wlF E z X (Φ x) ^ 3‖ := by
      filter_upwards [hinv] with x hx
      have hg := wl_grad_le σ E z hW hb0 hb1 hX hz (z • 1 - X) Y hY hκ x
      obtain ⟨hG1, hKG⟩ := wl_reg_weighted_le hX hz hE hzM hκ hκ1 x hx
      have hg0 : 0 ≤ weightedGradientNorm (tflVar W b σ) (wlTk W b σ E z X Kh Yh κ) x :=
        Real.sqrt_nonneg _
      have hF0 := wlF_nonneg E z X (Φ x)
      rw [Real.norm_of_nonneg hg0, Real.norm_of_nonneg (by positivity)]
      refine hg.trans ?_
      have hK2 : ‖wlKh (m := PortSite W σ) (z • 1 - X) * tcvG W b σ E z X κ x‖ ^ 2 ≤
          (2 * wlF E z X (Φ x)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hKG 2
      have h4 : 0 ≤ 4 / (W : ℝ) * s := by positivity
      calc 4 / (W : ℝ) * s * ‖tcvG W b σ E z X κ x‖ *
            ‖wlKh (m := PortSite W σ) (z • 1 - X) * tcvG W b σ E z X κ x‖ ^ 2
          ≤ 4 / (W : ℝ) * s * (2 * wlF E z X (Φ x)) * (2 * wlF E z X (Φ x)) ^ 2 := by
            gcongr
        _ = c * wlF E z X (Φ x) ^ 3 := by rw [hc]; ring
    have h4 := eLpNorm_mono_ae (p := ENNReal.ofReal p) hwc.aestronglyMeasurable hwle
    have h5 : eLpNorm (fun x => c * wlF E z X (Φ x) ^ 3) (ENNReal.ofReal p) μ =
        ENNReal.ofReal c * eLpNorm (fun x => wlF E z X (Φ x) ^ 3) (ENNReal.ofReal p) μ := by
      rw [show (fun x => c * wlF E z X (Φ x) ^ 3) = c • (fun x => wlF E z X (Φ x) ^ 3) from rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal hc0]
    calc ENNReal.ofReal (Cg * Real.sqrt p) *
          eLpNorm (weightedGradientNorm (tflVar W b σ) (wlTk W b σ E z X Kh Yh κ))
            (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal (Cg * Real.sqrt p) * (ENNReal.ofReal c * ENNReal.ofReal C3) := by
          gcongr
          exact h4.trans (h5.le.trans (by gcongr))
      _ = B := by
          rw [hB, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
  -- the limit `κ = 1/(m+1) → 0`
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκ1 : ∀ m, κm m ≤ 1 := fun m => by
    rw [hκm, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Fm : ℕ → (TflCoord W σ → ℝ) → ℂ := fun m => wlTk W b σ E z X Kh Yh (κm m) with hFm
  have hFmc : ∀ m, Continuous (Fm m) := fun m =>
    (wlTk_contDiff W b σ E z hX hz Kh Yh (hκpos m)).continuous
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun m => Fm m x) atTop (𝓝 (F x)) := by
    filter_upwards [hinv] with x hx
    exact ((wl_continuous_wlTr Kh Yh).tendsto _).comp (tcv_G_tendsto σ E z hx hκlim)
  set cD : ℝ := 4 * ‖Yh‖ * (‖Kh‖ * 2) ^ 2 with hcD
  have hbound : ∀ m, ∀ᵐ x ∂μ, ‖Fm m x‖ ≤ cD * ‖Gr x‖ ^ 2 := by
    intro m
    filter_upwards [hinv] with x hx
    refine (wl_norm_wlTr_le hW Kh Yh _).trans ?_
    have h2 := tflPsi_inv_le_two W b σ E z hX hz (hκpos m) x hx
    change ‖tcvG W b σ E z X (κm m) x‖ ≤ 2 * ‖Gr x‖ at h2
    calc 4 * ‖Yh‖ * (‖Kh‖ * ‖tcvG W b σ E z X (κm m) x‖) ^ 2
        ≤ 4 * ‖Yh‖ * (‖Kh‖ * (2 * ‖Gr x‖)) ^ 2 := by gcongr
      _ = cD * ‖Gr x‖ ^ 2 := by rw [hcD]; ring
  have hint : Tendsto (fun m => ∫ x, Fm m x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => cD * ‖Gr x‖ ^ 2)
      (fun m => (hFmc m).aestronglyMeasurable) (hG2.const_mul _) hbound hconv
  have hconv2 : ∀ᵐ x ∂μ, Tendsto (fun m => Fm m x - ∫ y, Fm m y ∂μ) atTop
      (𝓝 (F x - ∫ y, F y ∂μ)) := hconv.mono fun x hx => hx.sub hint
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun m => ((hFmc m).sub continuous_const).aestronglyMeasurable)
    (fun x => F x - ∫ y, F y ∂μ) (hF.sub_const _).aestronglyMeasurable hconv2
  refine hfatou.trans (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_))
  exact hstep (κm m) (hκpos m) (hκ1 m)

end NoiseCore

/-!
## 9. The contract field `clockNoise`
-/

section ClockNoise

theorem wl_re_inv_mul (W : ℕ) (c : ℂ) : ((W : ℂ)⁻¹ * c).re = (W : ℝ)⁻¹ * c.re := by
  rw [show ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]

theorem wl_hs_eq_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) : wlHS Y = (Y * Y).trace.re := by
  have h := wl_trace_conjTranspose_mul_self Y
  rw [hY.eq] at h
  rw [h, Complex.ofReal_re]

/-- `‖F³‖_p ≤ C³` from `‖F‖_{4p} ≤ C` (Hölder, probability law). -/
theorem wl_eLpNorm_cube_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hF : AEStronglyMeasurable F μ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (h : eLpNorm F (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => F ω ^ 3) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C ^ 3) := by
  have h2 : eLpNorm F (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal C :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans h
  have e : (fun ω => F ω ^ 3) = fun ω => F ω * (F ω * F ω) := by funext ω; ring
  rw [e]
  refine (wl_eLpNorm_mul_le hF (hF.mul hF) hp).trans ?_
  have h3 := wl_eLpNorm_mul_le hF hF (by linarith : (0 : ℝ) < 2 * p)
  rw [show 2 * (2 * p) = 4 * p by ring] at h3
  calc eLpNorm F (ENNReal.ofReal (2 * p)) μ *
        eLpNorm (fun ω => F ω * F ω) (ENNReal.ofReal (2 * p)) μ
      ≤ ENNReal.ofReal C * (ENNReal.ofReal C * ENNReal.ofReal C) :=
        mul_le_mul' h2 (h3.trans (mul_le_mul' h h))
    _ = ENNReal.ofReal (C ^ 3) := by
        rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul hC]; congr 1; ring

/-- **`clockNoise`** (the clock-noise bound of the weighted-layer lemma): for each `p ≥ 1`,
`W ≥ W₀(p)`, every Hermitian `X`, `E ∈ I` and `Y ⪰ 0`,
`‖W⁻¹Tr L*YL - E‖_p ≤ (C_p/W) √(W⁻¹ Tr Y²) ≤ C_p u/√W`. -/
theorem wl_clockNoise (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
    ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Lm := fun ω => K * (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂
      let t := fun ω => (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re
      let u := (W : ℝ)⁻¹ * Y.trace.re
      eLpNorm (fun ω => t ω - ∫ ω', t ω' ∂μ) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (Cp / W * Real.sqrt ((W : ℝ)⁻¹ * (Y * Y).trace.re)) ∧
        Cp / W * Real.sqrt ((W : ℝ)⁻¹ * (Y * Y).trace.re) ≤ Cp * u / Real.sqrt W := by
  intro b hb0 hb1 κ hκ p hp
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨C, W₀, hC, hmom⟩ := wl_moment_setup hcount hb0 hb1 hη₀ (q := 4 * p) (by linarith)
  have hCp0 : 0 ≤ Cg * Real.sqrt p * 32 * C ^ 3 := by positivity
  refine ⟨Cg * Real.sqrt p * 32 * C ^ 3, W₀, ?_⟩
  intro W hW hWW X hX E hE Y hY μ K Lm t u
  obtain ⟨hz, hzM, hE2⟩ := hbulk E hE
  have hz0 : 0 ≤ (boundaryZ b E).im := hη₀.le.trans hz
  obtain ⟨hinv, hF⟩ := hmom W hW hWW .separate X hX E _ hz hzM
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  set μc := gaussianProduct (tflVar W b .separate) with hμc
  set Φ := tflEmbed W b .separate with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b .separate
  have hlaw : layerLaw W b .separate = μc.map Φ := tfl_layerLaw_eq_map W b .separate
  set F := wlF (σ := .separate) E (boundaryZ b E) X with hFdef
  have hFm : Measurable F := wl_measurable_wlF _ _ _
  have hGm := measurable_layerResolvent .separate E (boundaryZ b E) X
  -- moments in the coordinates
  have hinvc : ∀ᵐ x ∂μc, IsUnit (layerMatrix .separate E (boundaryZ b E) X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  have hF3 : eLpNorm (fun ω => F ω ^ 3) (ENNReal.ofReal p) (layerLaw W b .separate) ≤
      ENNReal.ofReal (C ^ 3) :=
    wl_eLpNorm_cube_le hFm.aestronglyMeasurable (by linarith) hC hF
  have hF3c : eLpNorm (fun x => F (Φ x) ^ 3) (ENNReal.ofReal p) μc ≤ ENNReal.ofReal (C ^ 3) := by
    have hm : Measurable (fun ω => F ω ^ 3) := hFm.pow_const 3
    rw [hlaw, eLpNorm_map_measure hm.aestronglyMeasurable hΦ.aemeasurable] at hF3
    exact hF3
  have hFmem : MemLp F 2 (layerLaw W b .separate) := by
    have h1 : MemLp F (ENNReal.ofReal (4 * p)) (layerLaw W b .separate) :=
      memLp_iff.mpr (lt_of_le_of_lt hF ENNReal.ofReal_lt_top)
    refine h1.mono_exponent ?_
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hG2 : Integrable (fun ω => ‖layerResolvent .separate E (boundaryZ b E) X ω‖ ^ 2)
      (layerLaw W b .separate) := by
    refine Integrable.mono' hFmem.integrable_sq ((hGm.norm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    have hg0 := norm_nonneg (layerResolvent .separate E (boundaryZ b E) X ω)
    have hl0 := norm_nonneg (wlLam ω)
    rw [Real.norm_of_nonneg (by positivity)]
    have : ‖layerResolvent .separate E (boundaryZ b E) X ω‖ ≤ F ω := by
      rw [hFdef, wlF]; nlinarith
    exact pow_le_pow_left₀ hg0 this 2
  have hG2c : Integrable (fun x => ‖layerResolvent .separate E (boundaryZ b E) X (Φ x)‖ ^ 2) μc := by
    rw [hlaw, integrable_map_measure ((hGm.norm.pow_const 2).aestronglyMeasurable)
      hΦ.aemeasurable] at hG2
    exact hG2
  have hcore := wl_noise_core hCg.le hgr hW hb0 hb1 hX hz0 hE2 hzM Y hY.isHermitian hp hinvc hF3c
    hG2c
  -- the real clock is the real part of the complex clock functional
  set f : LayerSample W .separate → ℂ := fun ω =>
    wlTr (wlKh (boundaryZ b E • 1 - X)) (wlKh Y) (layerResolvent .separate E (boundaryZ b E) X ω)
    with hfdef
  have hfm : Measurable f :=
    (wl_continuous_wlTr _ _).measurable.comp hGm
  have htf : ∀ ω, t ω = (f ω).re := by
    intro ω
    simp only [hfdef, t, Lm, K]
    rw [wlTr_eq, wl_re_inv_mul]
  have hfi : Integrable f μ := by
    refine Integrable.mono' (hG2.const_mul (4 * ‖wlKh (m := PortSite W .separate) Y‖ *
      ‖wlKh (m := PortSite W .separate) (boundaryZ b E • 1 - X)‖ ^ 2))
      hfm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    refine (wl_norm_wlTr_le hW _ _ _).trans (le_of_eq ?_)
    ring
  have hti : ∫ ω, t ω ∂μ = (∫ ω, f ω ∂μ).re := by
    rw [integral_congr_ae (ae_of_all _ htf)]
    exact integral_re hfi
  have hle : eLpNorm (fun ω => t ω - ∫ ω', t ω' ∂μ) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂μ) (ENNReal.ofReal p) μ := by
    have hLc : Continuous (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
        K * M.toBlocks₁₂) := continuous_const.matrix_mul wl_continuous_toBlocks12
    have hLm : Measurable Lm := hLc.measurable.comp hGm
    have hc : Continuous (fun M : Matrix (Fin 2 × Fin W) (PortSite W .separate) ℂ =>
        (W : ℝ)⁻¹ * (Mᴴ * Y * M).trace.re) := by fun_prop
    have htm : Measurable (fun ω => t ω - ∫ ω', t ω' ∂μ) :=
      (hc.measurable.comp hLm).sub_const _
    refine eLpNorm_mono_ae htm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [htf, hti, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have htransfer : eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂μ) (ENNReal.ofReal p) μ =
      eLpNorm (fun x => f (Φ x) - ∫ y, f (Φ y) ∂μc) (ENNReal.ofReal p) μc := by
    change eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂layerLaw W b .separate) (ENNReal.ofReal p)
      (layerLaw W b .separate) = _
    rw [hlaw, integral_map hΦ.aemeasurable hfm.aestronglyMeasurable,
      eLpNorm_map_measure (hfm.sub_const _).aestronglyMeasurable hΦ.aemeasurable]
    rfl
  have hY2 := wl_trace_sq_le hY
  have hTY := wl_trace_re_nonneg hY
  refine ⟨hle.trans (htransfer.le.trans (hcore.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))),
    ?_⟩
  · rw [wl_hs_eq_trace hY.isHermitian]
    ring
  · -- `Tr Y² ≤ (Tr Y)²`
    have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW'
    have hsq : Real.sqrt ((W : ℝ)⁻¹ * (Y * Y).trace.re) ≤ Y.trace.re / Real.sqrt W := by
      calc Real.sqrt ((W : ℝ)⁻¹ * (Y * Y).trace.re)
          ≤ Real.sqrt ((W : ℝ)⁻¹ * Y.trace.re ^ 2) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hY2.2 (by positivity))
        _ = Y.trace.re / Real.sqrt W := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hTY, Real.sqrt_inv]
            ring
    calc Cg * Real.sqrt p * 32 * C ^ 3 / W * Real.sqrt ((W : ℝ)⁻¹ * (Y * Y).trace.re)
        ≤ Cg * Real.sqrt p * 32 * C ^ 3 / W * (Y.trace.re / Real.sqrt W) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Cg * Real.sqrt p * 32 * C ^ 3 * u / Real.sqrt W := by
          simp only [u]; ring

end ClockNoise

end BlockBand.Layers

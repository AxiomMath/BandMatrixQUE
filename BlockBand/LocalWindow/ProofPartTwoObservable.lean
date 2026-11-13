module

public import BlockBand.LocalWindow.ProofPartTwoStability

/-!
# The class (b) observables on the grid

Lipschitz bounds for the functional calculus and for the window centre in the observable, used to
move the class (b) observables of part (ii) to grid energies.

## Main results

* `sqNorm_unitary_mulVec`, `frob_unitary_mul`, `frob_mul_unitary`: unitary invariance.
* `sqNorm_mulVec_le_frob`, **`opNorm_le_sqrt_frob`**: `‖A‖ ≤ √frob A`.
* `frob_conj_diagonal_sub`: `frob(U D₁ U* - V D₂ V*) = Σ_{ab} |d₁(a) - d₂(b)|² |(U*V)_{ab}|²`.
* **`frob_cfc_sub_le`**: for Hermitian `X, Y` and `L`-Lipschitz `f`,
  `frob(f(X) - f(Y)) ≤ L² frob(X - Y)` (no commutation, no gap).
* **`opNorm_cfc_sub_le`**, **`opNorm_spectralFn_sub_le`**: `‖f(X) - f(Y)‖ ≤ √d L ‖X - Y‖`.
* `isHermitian_spectralFn`, **`opNorm_spectralFn_le`**: `f(X)` is a Hermitian contraction when
  `|f| ≤ 1`.
* **`lipschitz_of_isSpectralTest`**: `IsSpectralTest k K₀ f` with `k ≥ 1` gives
  `|f a - f b| ≤ K₀ |a - b|`.
* **`isWindowObservable_hermitian_contraction`**: every observable of `IsWindowObservable` is a
  Hermitian contraction at every `(ω, E)`.
* **`opNorm_spectralTest_sub_le`**: for `IsSpectralTest k K₀ f`, `k ≥ 1` and Hermitian pair
  matrices, `‖f(K) - f(K')‖ ≤ √(2W) K₀ ‖K - K'‖`.
* `norm_quadForm_le`, **`abs_quadForm_sub_le`**: `|u*Bu - u*B'u| ≤ ‖B - B'‖` for a unit `u`.
* **`pairCentre_sub_le_obs`**, **`windowCenter_sub_le_obs`**: at a Dyson root at the real `x`,
  `|j_B(x) - j_{B'}(x)| ≤ ‖B - B'‖` (the centre is linear in `B`, `d⁻¹ Tr Γ ≤ 1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator ContDiff

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `‖U v‖² = ‖v‖²` for `U* U = 1`. -/
theorem sqNorm_unitary_mulVec {U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) (v : ι → ℂ) :
    sqNorm (U *ᵥ v) = sqNorm v := by
  have h1 := star_dotProduct_self (U *ᵥ v)
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hU, one_mulVec,
    star_dotProduct_self] at h1
  exact_mod_cast h1.symm

/-- `frob (U M) = frob M` for `U* U = 1`. -/
theorem frob_unitary_mul {U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) (M : Matrix ι ι ℂ) :
    frob (U * M) = frob M := by
  have h := trace_mul_conjTranspose (U * M)
  rw [conjTranspose_mul, show U * M * (Mᴴ * Uᴴ) = U * (M * Mᴴ * Uᴴ) by
      simp only [Matrix.mul_assoc], trace_mul_comm U] at h
  simp only [Matrix.mul_assoc, hU, Matrix.mul_one] at h
  rw [trace_mul_conjTranspose] at h
  exact_mod_cast h.symm

/-- `frob (M V) = frob M` for `V V* = 1`. -/
theorem frob_mul_unitary {V : Matrix ι ι ℂ} (hV : V * Vᴴ = 1) (M : Matrix ι ι ℂ) :
    frob (M * V) = frob M := by
  rw [← frob_conjTranspose, conjTranspose_mul,
    frob_unitary_mul (by rw [conjTranspose_conjTranspose]; exact hV), frob_conjTranspose]

/-- `‖A v‖² ≤ frob A ‖v‖²` (Cauchy–Schwarz in each row). -/
theorem sqNorm_mulVec_le_frob (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    sqNorm (A *ᵥ v) ≤ frob A * sqNorm v := by
  unfold sqNorm frob
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have h1 : ‖(A *ᵥ v) a‖ ≤ ∑ b, ‖A a b‖ * ‖v b‖ := by
    simp only [mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => ‖A a b‖) (fun b => ‖v b‖)
  calc ‖(A *ᵥ v) a‖ ^ 2 ≤ (∑ b, ‖A a b‖ * ‖v b‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- **`‖A‖ ≤ √frob A`** (`L²` operator norm against the Frobenius norm). -/
theorem opNorm_le_sqrt_frob (A : Matrix ι ι ℂ) : ‖A‖ ≤ Real.sqrt (frob A) := by
  refine opNorm_le_of_sqNorm (Real.sqrt_nonneg _) fun v => ?_
  rw [Real.sq_sqrt (frob_nonneg A)]
  exact sqNorm_mulVec_le_frob A v

/-- `frob(U D₁ U* - V D₂ V*) = Σ_{a,b} |d₁ a - d₂ b|² |(U* V)_{ab}|²` for unitary `U, V`. -/
theorem frob_conj_diagonal_sub {U V : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1) (d₁ d₂ : ι → ℂ) :
    frob (U * diagonal d₁ * Uᴴ - V * diagonal d₂ * Vᴴ) =
      ∑ a, ∑ b, ‖d₁ a - d₂ b‖ ^ 2 * ‖(Uᴴ * V) a b‖ ^ 2 := by
  set A := U * diagonal d₁ * Uᴴ - V * diagonal d₂ * Vᴴ
  have h1 : frob A = frob (Uᴴ * A * V) := by
    rw [frob_mul_unitary hV', frob_unitary_mul (by rw [conjTranspose_conjTranspose]; exact hU')]
  have h2 : Uᴴ * A * V = diagonal d₁ * (Uᴴ * V) - (Uᴴ * V) * diagonal d₂ := by
    simp only [A, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    · calc Uᴴ * (U * diagonal d₁ * Uᴴ) * V = (Uᴴ * U) * diagonal d₁ * (Uᴴ * V) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.one_mul]
    · calc Uᴴ * (V * diagonal d₂ * Vᴴ) * V = (Uᴴ * V) * diagonal d₂ * (Vᴴ * V) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV, Matrix.mul_one]
  rw [h1, h2]
  unfold frob
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.sub_apply, diagonal_mul, mul_diagonal, ← mul_pow, ← norm_mul]
  congr 2
  ring

/-- The `cfc` of a Hermitian matrix as a unitary conjugate of a diagonal matrix. -/
theorem cfc_eq_conj {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    hX.cfc f = (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun a => ((f (hX.eigenvalues a) : ℝ) : ℂ)) *
        (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  unfold IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  rfl

theorem unitary_conj_mul_self {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hX.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _

theorem unitary_mul_conj_self {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix ι ι ℂ) * (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ = 1 := by
  rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _

/-- **Frobenius–Lipschitz bound of the functional calculus**: for Hermitian `X, Y` and
`|f a - f b| ≤ L |a - b|`, `frob(f(X) - f(Y)) ≤ L² frob(X - Y)`. -/
theorem frob_cfc_sub_le {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    {f : ℝ → ℝ} {L : ℝ} (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) :
    frob (hX.cfc f - hY.cfc f) ≤ L ^ 2 * frob (X - Y) := by
  have hXe : X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun a => ((hX.eigenvalues a : ℝ) : ℂ)) *
        (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hYe : Y = (hY.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun a => ((hY.eigenvalues a : ℝ) : ℂ)) *
        (hY.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => rw [hY.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have e1 := frob_conj_diagonal_sub (unitary_conj_mul_self hX) (unitary_mul_conj_self hX)
      (unitary_conj_mul_self hY) (unitary_mul_conj_self hY)
      (fun a => ((f (hX.eigenvalues a) : ℝ) : ℂ)) (fun a => ((f (hY.eigenvalues a) : ℝ) : ℂ))
  have e2 := frob_conj_diagonal_sub (unitary_conj_mul_self hX) (unitary_mul_conj_self hX)
      (unitary_conj_mul_self hY) (unitary_mul_conj_self hY)
      (fun a => ((hX.eigenvalues a : ℝ) : ℂ)) (fun a => ((hY.eigenvalues a : ℝ) : ℂ))
  rw [← cfc_eq_conj, ← cfc_eq_conj] at e1
  rw [show X - Y = _ from congrArg₂ (· - ·) hXe hYe, e2, e1, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, ← mul_pow]
  have h := hf (hX.eigenvalues a) (hY.eigenvalues b)
  exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using h) 2

/-- **Operator-Lipschitz bound of the functional calculus** (through Frobenius): for Hermitian
`X, Y`, `0 ≤ L` and `|f a - f b| ≤ L |a - b|`, `‖f(X) - f(Y)‖ ≤ √d L ‖X - Y‖`, `d = |ι|`. -/
theorem opNorm_cfc_sub_le {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) :
    ‖hX.cfc f - hY.cfc f‖ ≤ Real.sqrt (Fintype.card ι) * L * ‖X - Y‖ := by
  refine (opNorm_le_sqrt_frob _).trans ?_
  calc Real.sqrt (frob (hX.cfc f - hY.cfc f)) ≤ Real.sqrt (L ^ 2 * frob (X - Y)) :=
        Real.sqrt_le_sqrt (frob_cfc_sub_le hX hY hf)
    _ = L * Real.sqrt (frob (X - Y)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL]
    _ ≤ L * (Real.sqrt (Fintype.card ι) * ‖X - Y‖) :=
        mul_le_mul_of_nonneg_left (sqrt_frob_le _) hL
    _ = _ := by ring

/-- `spectralFn f X = f(X)` for Hermitian `X`. -/
theorem spectralFn_of_isHermitian {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    BlockBand.LocalWindow.spectralFn f X = hX.cfc f := by
  unfold BlockBand.LocalWindow.spectralFn
  rw [dite_eq_left_of_eq_true (eq_true hX)]

/-- `‖f(X) - f(Y)‖ ≤ √d L ‖X - Y‖` for `spectralFn` (Hermitian `X, Y`). -/
theorem opNorm_spectralFn_sub_le {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) :
    ‖BlockBand.LocalWindow.spectralFn f X - BlockBand.LocalWindow.spectralFn f Y‖ ≤
      Real.sqrt (Fintype.card ι) * L * ‖X - Y‖ := by
  rw [spectralFn_of_isHermitian hX, spectralFn_of_isHermitian hY]
  exact opNorm_cfc_sub_le hX hY hL hf

/-- `f(X)` is Hermitian (`spectralFn` is `0` off the Hermitian set). -/
theorem isHermitian_spectralFn (f : ℝ → ℝ) (X : Matrix ι ι ℂ) :
    (BlockBand.LocalWindow.spectralFn f X).IsHermitian := by
  unfold BlockBand.LocalWindow.spectralFn
  split_ifs with hX
  · rw [cfc_eq_conj]
    refine isHermitian_mul_mul_conjTranspose _ ?_
    refine isHermitian_diagonal_of_self_adjoint _ ?_
    ext a
    simp
  · exact isHermitian_zero

/-- `‖diagonal d‖ ≤ c` for `|d a| ≤ c`. -/
theorem opNorm_diagonal_le {d : ι → ℂ} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ a, ‖d a‖ ≤ c) :
    ‖diagonal d‖ ≤ c := by
  refine opNorm_le_of_sqNorm hc fun v => ?_
  unfold sqNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [mulVec_diagonal, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd a) 2) (by positivity)

/-- `‖U‖ ≤ 1` for `U* U = 1`. -/
theorem opNorm_le_one_of_unitary {U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) : ‖U‖ ≤ 1 :=
  opNorm_le_of_sqNorm zero_le_one fun v => by rw [sqNorm_unitary_mulVec hU, one_pow, one_mul]

/-- **`f(X)` is a contraction** when `|f| ≤ 1` (`spectralFn`, any matrix `X`). -/
theorem opNorm_spectralFn_le {f : ℝ → ℝ} (hf : ∀ x, |f x| ≤ 1) (X : Matrix ι ι ℂ) :
    ‖BlockBand.LocalWindow.spectralFn f X‖ ≤ 1 := by
  unfold BlockBand.LocalWindow.spectralFn
  split_ifs with hX
  · rw [cfc_eq_conj]
    have hU := opNorm_le_one_of_unitary (unitary_conj_mul_self hX)
    have hU' := opNorm_le_one_of_unitary (U := (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ)
      (by rw [conjTranspose_conjTranspose]; exact unitary_mul_conj_self hX)
    have hD : ‖diagonal (fun a => ((f (hX.eigenvalues a) : ℝ) : ℂ))‖ ≤ 1 :=
      opNorm_diagonal_le zero_le_one fun a => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hf _
    calc _ ≤ ‖(hX.eigenvectorUnitary : Matrix ι ι ℂ) *
            diagonal (fun a => ((f (hX.eigenvalues a) : ℝ) : ℂ))‖ *
          ‖(hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ‖ := norm_mul_le _ _
      _ ≤ (‖(hX.eigenvectorUnitary : Matrix ι ι ℂ)‖ *
            ‖diagonal (fun a => ((f (hX.eigenvalues a) : ℝ) : ℂ))‖) *
          ‖(hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (1 * 1) * 1 := by gcongr
      _ = 1 := by norm_num
  · rw [norm_zero]; exact zero_le_one

/-- `|x* D x| ≤ ‖D‖ ‖x‖²`. -/
theorem norm_quadForm_le (D : Matrix ι ι ℂ) (x : ι → ℂ) :
    ‖star x ⬝ᵥ (D *ᵥ x)‖ ≤ ‖D‖ * sqNorm x := by
  have hnorm : ∀ v : ι → ℂ, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ = Real.sqrt (sqNorm v) := by
    intro v; rw [EuclideanSpace.norm_eq]; rfl
  have hinner : star x ⬝ᵥ (D *ᵥ x) =
      inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
        ((EuclideanSpace.equiv ι ℂ).symm (D *ᵥ (WithLp.toLp 2 x : EuclideanSpace ℂ ι))) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  rw [hinner]
  refine (norm_inner_le_norm _ _).trans ?_
  have h2 := Matrix.l2_opNorm_mulVec D (WithLp.toLp 2 x)
  have h3 : ‖(EuclideanSpace.equiv ι ℂ).symm (D *ᵥ (WithLp.toLp 2 x : EuclideanSpace ℂ ι))‖ ≤
      ‖D‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ := h2
  calc ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
        ‖(EuclideanSpace.equiv ι ℂ).symm (D *ᵥ (WithLp.toLp 2 x : EuclideanSpace ℂ ι))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
          (‖D‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = ‖D‖ * Real.sqrt (sqNorm x) ^ 2 := by rw [hnorm]; ring
    _ = ‖D‖ * sqNorm x := by rw [Real.sq_sqrt (sqNorm_nonneg _)]

/-- **Overlaps are `1`-Lipschitz in the observable**: `|Re(u*Bu) - Re(u*B'u)| ≤ ‖B - B'‖` for a
unit vector `u`. -/
theorem abs_quadForm_sub_le (B B' : Matrix ι ι ℂ) {u : ι → ℂ} (hu : l2Norm u = 1) :
    |(star u ⬝ᵥ (B *ᵥ u)).re - (star u ⬝ᵥ (B' *ᵥ u)).re| ≤ ‖B - B'‖ := by
  rw [← Complex.sub_re, ← dotProduct_sub, ← sub_mulVec]
  refine (Complex.abs_re_le_norm _).trans ?_
  have := norm_quadForm_le (B - B') u
  rwa [sqNorm_eq_one_of_l2Norm hu, mul_one] at this

end Generic

/-- **A spectral test is `K₀`-Lipschitz** (`IsSpectralTest k K₀ f` with `k ≥ 1`; mean value
theorem with `|f'| = |iteratedDeriv 1 f| ≤ K₀`). -/
theorem lipschitz_of_isSpectralTest {k : ℕ} {K₀ : ℝ} {f : ℝ → ℝ}
    (hf : BlockBand.LocalWindow.IsSpectralTest k K₀ f) (hk : 1 ≤ k) (a b : ℝ) :
    |f a - f b| ≤ K₀ * |a - b| := by
  obtain ⟨hsmooth, -, hder, -⟩ := hf
  have hdiff : Differentiable ℝ f := hsmooth.differentiable (by simp)
  have hbound : ∀ x ∈ (univ : Set ℝ), ‖deriv f x‖ ≤ K₀ := fun x _ => by
    have := hder 1 hk x
    rwa [iteratedDeriv_one, ← Real.norm_eq_abs] at this
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun x _ => hdiff x) hbound
    (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using h

/-- `0 ≤ K₀` for a spectral test (`|f'| ≤ K₀`, `k ≥ 1`). -/
theorem nonneg_of_isSpectralTest {k : ℕ} {K₀ : ℝ} {f : ℝ → ℝ}
    (hf : BlockBand.LocalWindow.IsSpectralTest k K₀ f) (hk : 1 ≤ k) : 0 ≤ K₀ :=
  (abs_nonneg _).trans (hf.2.2.1 1 hk 0)

variable {p : Parameters} {i : ZMod p.n}

/-- **Every window observable is a Hermitian contraction** (`IsWindowObservable`, both classes),
at every exterior state and energy. -/
theorem isWindowObservable_hermitian_contraction {k : ℕ} {K₀ : ℝ}
    {B : SplitState p i → ℝ → PairMatrix p i}
    (hB : BlockBand.LocalWindow.IsWindowObservable p i k K₀ B) (om : SplitState p i) (E : ℝ) :
    (B om E).IsHermitian ∧ ‖B om E‖ ≤ 1 := by
  rcases hB with ⟨B₀, -, hB₀, hBE⟩ | ⟨f, hf, hBE⟩
  · rw [hBE]; exact hB₀ om
  · rw [hBE]
    exact ⟨isHermitian_spectralFn f _, opNorm_spectralFn_le hf.2.1 _⟩

/-- **Class (b) observables on the grid** (polynomial Lipschitz dependence):
for `IsSpectralTest k K₀ f` with `k ≥ 1` and Hermitian pair matrices `K, K'`,
`‖f(K) - f(K')‖ ≤ √(2W) K₀ ‖K - K'‖`. -/
theorem opNorm_spectralTest_sub_le {k : ℕ} {K₀ : ℝ} {f : ℝ → ℝ}
    (hf : BlockBand.LocalWindow.IsSpectralTest k K₀ f) (hk : 1 ≤ k) {K K' : PairMatrix p i}
    (hK : K.IsHermitian) (hK' : K'.IsHermitian) :
    ‖BlockBand.LocalWindow.spectralFn f K - BlockBand.LocalWindow.spectralFn f K'‖ ≤
      Real.sqrt (2 * (p.W : ℝ)) * K₀ * ‖K - K'‖ := by
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * (p.W : ℝ) := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
  have h := opNorm_spectralFn_sub_le hK hK' (nonneg_of_isSpectralTest hf hk)
    (lipschitz_of_isSpectralTest hf hk)
  rwa [hcard] at h

/-- **The centre is `1`-Lipschitz in the observable**: at a Dyson root `m` of the
Hermitian `K` at the real `x`, `|pairCentre B K s x - pairCentre B' K s x| ≤ ‖B - B'‖`
(`Γ = s M M*` and `s frob M ≤ d`). -/
theorem pairCentre_sub_le_obs {K B B' : PairMatrix p i} (hK : K.IsHermitian) {s x : ℝ}
    (hs : 0 < s) {m : ℂ} (hm : IsDysonRoot K s (x : ℂ) m) :
    ‖pairCentre B K s x - pairCentre B' K s x‖ ≤ ‖B - B'‖ := by
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  have hp : BlockBand.LocalWindow.pairDyson p i K s x = m :=
    pairDyson_eq_of_isDysonRoot p i hK hs (by simp) hm
  set R := (K - ((x : ℂ) + (s : ℂ) * m) • (1 : PairMatrix p i))⁻¹ with hR
  have hg : BlockBand.LocalWindow.windowGamma p i K s x = (s : ℂ) • (R * Rᴴ) := by
    rw [windowGamma_eq, hp]
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * (p.W : ℝ) := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
  have hW2 : (0 : ℝ) < 2 * (p.W : ℝ) := by have := p.W_pos; positivity
  have hdiff : pairCentre B K s x - pairCentre B' K s x =
      (((2 * (p.W : ℝ))⁻¹ : ℝ) : ℂ) * (s : ℂ) * (Rᴴ * (B - B') * R).trace := by
    unfold pairCentre
    rw [hg, ← mul_sub, ← trace_sub, ← Matrix.sub_mul, mul_smul_comm, trace_smul, smul_eq_mul,
      trace_mul_cycle, trace_mul_comm (B - B'), ← mul_assoc]
  have ht : ‖(Rᴴ * (B - B') * R).trace‖ ≤ ‖B - B'‖ * frob R := by
    have h := norm_trace_mul_mul_le_opNorm Rᴴ (B - B') R
    rwa [frob_conjTranspose, Real.mul_self_sqrt (frob_nonneg R)] at h
  have hf := s_frob_le hK hs (by simp) hm
  rw [hcard] at hf
  rw [hdiff, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hW2), abs_of_pos hs]
  calc (2 * (p.W : ℝ))⁻¹ * s * ‖(Rᴴ * (B - B') * R).trace‖
      ≤ (2 * (p.W : ℝ))⁻¹ * s * (‖B - B'‖ * frob R) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ = ‖B - B'‖ * ((2 * (p.W : ℝ))⁻¹ * (s * frob R)) := by ring
    _ ≤ ‖B - B'‖ * ((2 * (p.W : ℝ))⁻¹ * (2 * (p.W : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf (by positivity)) (norm_nonneg _)
    _ = ‖B - B'‖ := by rw [inv_mul_cancel₀ hW2.ne', mul_one]

/-- `pairCentre_sub_le_obs` for the real window centre `windowCenter`. -/
theorem windowCenter_sub_le_obs {K B B' : PairMatrix p i} (hK : K.IsHermitian) {s x : ℝ}
    (hs : 0 < s) {m : ℂ} (hm : IsDysonRoot K s (x : ℂ) m) :
    |BlockBand.LocalWindow.windowCenter p i B K s x -
        BlockBand.LocalWindow.windowCenter p i B' K s x| ≤ ‖B - B'‖ := by
  rw [← re_pairCentre, ← re_pairCentre, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (pairCentre_sub_le_obs hK hs hm)

end BlockBand.LocalWindow.ProofPartTwo

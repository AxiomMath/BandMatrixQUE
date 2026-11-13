module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.Backward
public import BlockBand.Critical.RelativeVectors.GenDiff

/-!
# Bounds on the generators

For `g` Euclidean bounded-`C²` with constant `C` (`IsArrayC2Bounded C g`), the sup-norm operator
norms of `Dg`, `D²g` are at most `M = supC2Const N r C = C (√(N r) + √(N r)²)`. Write `‖z‖` for
the sup norm of the array.

* `abs_referenceArrayGenerator_le` (time bound before the gap stop): if every gap of
  `λ = flowEigenvalue F a ω σ` exceeds `1/n` (`n > 0`), then
  `|𝓛_ref(σ) g (z)| ≤ refGenConst N r C n b₀ ℓ · (1 + ‖z‖²)`, with
  `refGenConst = N² n² M + N max(N n², b₀N/ℓ) (1 + r) M`.
* `abs_generator_diff_le` (generator difference on long gaps): if `ℓ ≥ 1`, `δ > 0` and every
  long gap (`labelDist i j ≥ ℓ`) is `≥ δ`, then
  `|(𝒜_σ - 𝓛_ref(σ)) g (z)| ≤ genDiffConst N r C δ b₀ ℓ · (1 + ‖z‖²)`, with
  `genDiffConst = N² δ⁻² ((1 + r) M / 2 + M) + N |b₀N/ℓ| (1 + r) M`. The short rotations cancel
  exactly (`generator_diff_eq`); no simple-spectrum or short-gap hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Critical.RelativeVectors

variable {N r : ℕ}

/-!
## Constants
-/

/-- Sup-norm bound `M = C (√(N r) + √(N r)²)` for `‖Dg‖` and `‖D²g‖`. -/
def supC2Const (N r : ℕ) (C : ℝ) : ℝ := C * (Real.sqrt (N * r) + Real.sqrt (N * r) ^ 2)

/-- Constant of the reference-generator bound under gaps `> 1/n`. -/
def refGenConst (N r : ℕ) (C : ℝ) (n : ℕ) (b₀ : ℝ) (ℓ : ℕ) : ℝ :=
  N * N * (n : ℝ) ^ 2 * supC2Const N r C +
    N * max (N * (n : ℝ) ^ 2) (b₀ * N / ℓ) * (1 + r) * supC2Const N r C

/-- Constant of the generator-difference bound under long gaps `≥ δ`. -/
def genDiffConst (N r : ℕ) (C δ b₀ : ℝ) (ℓ : ℕ) : ℝ :=
  N * N * (1 / δ ^ 2) * ((1 + r) * supC2Const N r C / 2 + supC2Const N r C) +
    N * |b₀ * N / ℓ| * (1 + r) * supC2Const N r C

/-- `M ≥ 0` for `C ≥ 0`. -/
theorem supC2Const_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ supC2Const N r C := by
  unfold supC2Const; positivity

/-- `‖Dg(z)‖ ≤ M`. -/
theorem norm_fderiv_le_supC2Const {C : ℝ} {g : (Fin N → Fin r → ℂ) → ℝ}
    (hg : IsArrayC2Bounded C g) (z : Fin N → Fin r → ℂ) : ‖fderiv ℝ g z‖ ≤ supC2Const N r C := by
  have h1 := arrayC2_norm_fderiv_le hg z
  have h2 : 0 ≤ C * Real.sqrt (N * r) ^ 2 := mul_nonneg (arrayC2_nonneg hg) (sq_nonneg _)
  unfold supC2Const
  rw [mul_add]
  linarith

/-- `‖D²g(z)‖ ≤ M`. -/
theorem norm_fderiv_fderiv_le_supC2Const {C : ℝ} {g : (Fin N → Fin r → ℂ) → ℝ}
    (hg : IsArrayC2Bounded C g) (z : Fin N → Fin r → ℂ) :
    ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ supC2Const N r C := by
  have h1 := arrayC2_norm_fderiv_fderiv_le hg z
  have h2 : 0 ≤ C * Real.sqrt (N * r) :=
    mul_nonneg (arrayC2_nonneg hg) (Real.sqrt_nonneg _)
  unfold supC2Const
  rw [mul_add]
  linarith

/-!
## Elementary bounds
-/

/-- `|D¹ x| ≤ ‖D¹‖ ‖x‖`. -/
theorem abs_clm_le (D1 : (Fin N → Fin r → ℂ) →L[ℝ] ℝ) (x : Fin N → Fin r → ℂ) :
    |D1 x| ≤ ‖D1‖ * ‖x‖ := by
  rw [← Real.norm_eq_abs]; exact D1.le_opNorm x

/-- `|D² x y| ≤ ‖D²‖ ‖x‖ ‖y‖`. -/
theorem abs_bil_le (D2 : ArrBil N r) (x y : Fin N → Fin r → ℂ) :
    |D2 x y| ≤ ‖D2‖ * ‖x‖ * ‖y‖ := by
  rw [← Real.norm_eq_abs]; exact D2.le_opNorm₂ x y

/-- A sum over a subset of `Fin n` of terms bounded by `B ≥ 0` is bounded by `n B`. -/
theorem abs_sum_le_card_mul {n : ℕ} (s : Finset (Fin n)) {f : Fin n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j ∈ s, |f j| ≤ B) : |∑ j ∈ s, f j| ≤ n * B := by
  calc |∑ j ∈ s, f j| ≤ ∑ j ∈ s, |f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ s, B := Finset.sum_le_sum h
    _ = s.card * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * B := by
        gcongr
        have := Finset.card_le_univ s
        rw [Fintype.card_fin] at this
        exact_mod_cast this

/-- `‖e_i v‖ = ‖v‖` (sup norm). -/
theorem norm_single_eq (i : Fin N) (v : Fin r → ℂ) : ‖single i v‖ = ‖v‖ :=
  Pi.norm_single (G := fun _ : Fin N => Fin r → ℂ) v

/-- `‖i v‖ = ‖v‖`. -/
theorem norm_I_smul (v : Fin r → ℂ) : ‖Complex.I • v‖ = ‖v‖ := by
  rw [norm_smul, Complex.norm_I, one_mul]

/-- `‖e_q‖ = 1` in `ℂ^r`. -/
theorem norm_single_one (q : Fin r) : ‖(Pi.single q (1 : ℂ) : Fin r → ℂ)‖ = 1 := by
  rw [Pi.norm_single, norm_one]

/-- `‖X_ij z‖ ≤ ‖z‖`. -/
theorem norm_rotX_le (i j : Fin N) (z : Fin N → Fin r → ℂ) : ‖rotX i j z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun k => ?_
  simp only [rotX]
  split_ifs
  · exact norm_le_pi_norm z j
  · rw [norm_neg]; exact norm_le_pi_norm z i
  · simp

/-- `‖Y_ij z‖ ≤ ‖z‖`. -/
theorem norm_rotY_le (i j : Fin N) (z : Fin N → Fin r → ℂ) : ‖rotY i j z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun k => ?_
  simp only [rotY]
  split_ifs
  · rw [norm_I_smul]; exact norm_le_pi_norm z j
  · rw [norm_I_smul]; exact norm_le_pi_norm z i
  · simp

/-- `x ≤ 1 + x²`. -/
theorem le_one_add_sq (x : ℝ) : x ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (x - 1)]

/-- `|W²h(z)| ≤ 2M(1 + ‖z‖²)` for a vector field with `‖W y‖ ≤ ‖y‖` and `‖Dh‖, ‖D²h‖ ≤ M`. -/
theorem abs_fieldSq_le {W : (Fin N → Fin r → ℂ) → (Fin N → Fin r → ℂ)}
    (hW : ∀ y, ‖W y‖ ≤ ‖y‖) {h : (Fin N → Fin r → ℂ) → ℝ} {z : Fin N → Fin r → ℂ} {M : ℝ}
    (hM0 : 0 ≤ M) (h1 : ‖fderiv ℝ h z‖ ≤ M) (h2 : ‖fderiv ℝ (fderiv ℝ h) z‖ ≤ M) :
    |fieldSq W h z| ≤ 2 * M * (1 + ‖z‖ ^ 2) := by
  have hx0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hWz : ‖W z‖ ≤ ‖z‖ := hW z
  have hWWz : ‖W (W z)‖ ≤ ‖z‖ := (hW _).trans hWz
  have e1 : |fderiv ℝ (fderiv ℝ h) z (W z) (W z)| ≤ M * ‖z‖ * ‖z‖ :=
    (abs_bil_le _ _ _).trans (by gcongr)
  have e2 : |fderiv ℝ h z (W (W z))| ≤ M * ‖z‖ :=
    (abs_clm_le _ _).trans (by gcongr)
  have hxle := le_one_add_sq ‖z‖
  have h3 : M * ‖z‖ ≤ M * (1 + ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left hxle hM0
  have h4 : M * ‖z‖ ^ 2 ≤ M * (1 + ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hM0
  unfold fieldSq
  calc _ ≤ |fderiv ℝ (fderiv ℝ h) z (W z) (W z)| + |fderiv ℝ h z (W (W z))| := abs_add_le _ _
    _ ≤ M * ‖z‖ * ‖z‖ + M * ‖z‖ := add_le_add e1 e2
    _ ≤ 2 * M * (1 + ‖z‖ ^ 2) := by nlinarith

/-- `|hq D² i v| ≤ 2 ‖D²‖ ‖v‖²`. -/
theorem abs_hq_le (D2 : ArrBil N r) (i : Fin N) (v : Fin r → ℂ) :
    |hq D2 i v| ≤ 2 * ‖D2‖ * ‖v‖ ^ 2 := by
  unfold hq
  calc _ ≤ |D2 (single i v) (single i v)| +
        |D2 (single i (Complex.I • v)) (single i (Complex.I • v))| := abs_add_le _ _
    _ ≤ ‖D2‖ * ‖single i v‖ * ‖single i v‖ +
        ‖D2‖ * ‖single i (Complex.I • v)‖ * ‖single i (Complex.I • v)‖ :=
        add_le_add (abs_bil_le _ _ _) (abs_bil_le _ _ _)
    _ = 2 * ‖D2‖ * ‖v‖ ^ 2 := by
        rw [norm_single_eq, norm_single_eq, norm_I_smul]; ring

/-- `|hqTrace D² i| ≤ r · 2‖D²‖`. -/
theorem abs_hqTrace_le (D2 : ArrBil N r) (i : Fin N) : |hqTrace D2 i| ≤ r * (2 * ‖D2‖) := by
  unfold hqTrace
  refine abs_sum_le_card_mul _ (by positivity) fun q _ => ?_
  calc |hq D2 i (Pi.single q 1)| ≤ 2 * ‖D2‖ * ‖(Pi.single q (1 : ℂ) : Fin r → ℂ)‖ ^ 2 :=
        abs_hq_le D2 i _
    _ = 2 * ‖D2‖ := by rw [norm_single_one]; ring

/-- `|crossTerm D² z i j| ≤ 4 ‖D²‖ ‖z‖²`. -/
theorem abs_crossTerm_le (D2 : ArrBil N r) (z : Fin N → Fin r → ℂ) (i j : Fin N) :
    |crossTerm D2 z i j| ≤ 4 * ‖D2‖ * ‖z‖ ^ 2 := by
  have hi : ‖z i‖ ≤ ‖z‖ := norm_le_pi_norm z i
  have hj : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
  have hB := norm_nonneg D2
  have b : ∀ x y : Fin r → ℂ, ∀ k l : Fin N, ‖x‖ ≤ ‖z‖ → ‖y‖ ≤ ‖z‖ →
      |D2 (single k x) (single l y)| ≤ ‖D2‖ * ‖z‖ * ‖z‖ := by
    intro x y k l hx hy
    refine (abs_bil_le _ _ _).trans ?_
    rw [norm_single_eq, norm_single_eq]
    gcongr
  have hIi : ‖Complex.I • z i‖ ≤ ‖z‖ := by rw [norm_I_smul]; exact hi
  have hIj : ‖Complex.I • z j‖ ≤ ‖z‖ := by rw [norm_I_smul]; exact hj
  unfold crossTerm
  have t1 := b _ _ i j hIj hIi
  have t2 := b _ _ j i hIi hIj
  have t3 := b _ _ i j hj hi
  have t4 := b _ _ j i hi hj
  calc _ ≤ |D2 (single i (Complex.I • z j)) (single j (Complex.I • z i))| +
        |D2 (single j (Complex.I • z i)) (single i (Complex.I • z j))| +
        |D2 (single i (z j)) (single j (z i))| + |D2 (single j (z i)) (single i (z j))| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ 4 * ‖D2‖ * ‖z‖ ^ 2 := by nlinarith

/-- Couplings of pairs with gap `≥ δ > 0` are in `[0, δ⁻²]`. -/
theorem dysonCoupling_bounds {lam : Fin N → ℝ} {i j : Fin N} {δ : ℝ} (hδ : 0 < δ)
    (h : δ ≤ |lam i - lam j|) :
    0 ≤ dysonCoupling N lam i j ∧ dysonCoupling N lam i j ≤ 1 / δ ^ 2 := by
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Fin.pos i)
  have hd : δ ^ 2 ≤ (lam i - lam j) ^ 2 := by
    rw [← sq_abs (lam i - lam j)]; exact pow_le_pow_left₀ hδ.le h 2
  have hδ2 : 0 < δ ^ 2 := by positivity
  unfold dysonCoupling
  refine ⟨by positivity, one_div_le_one_div_of_le hδ2 ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hN (sq_nonneg (lam i - lam j))]

/-- Couplings `flowRate` are nonnegative. -/
theorem flowRate_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ)
    (i j : Fin N) : 0 ≤ flowRate F a ω σ i j := by
  unfold flowRate; positivity

/-- Long couplings `β_i` are nonnegative. -/
theorem longCoupling_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (i : Fin N) : 0 ≤ longCoupling F a ω ℓ σ i := by
  unfold longCoupling
  exact Finset.sum_nonneg fun m _ => flowRate_nonneg F a ω σ i m

/-- `0 ≤ β̂_i - β_i ≤ |b₀N/ℓ|`. -/
theorem abs_refDamping_sub_le (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) (i : Fin N) :
    |refDamping F a b₀ ω ℓ σ i - longCoupling F a ω ℓ σ i| ≤ |b₀ * N / ℓ| := by
  have hβ := longCoupling_nonneg F a ω ℓ σ i
  unfold refDamping
  rw [abs_of_nonneg (sub_nonneg.2 (le_max_left _ _))]
  rcases max_cases (longCoupling F a ω ℓ σ i) (b₀ * N / ℓ) with ⟨e, -⟩ | ⟨e, -⟩
  · rw [e, sub_self]; exact abs_nonneg _
  · rw [e]; linarith [le_abs_self (b₀ * N / ℓ)]

/-!
## The reference generator before the gap stop
-/

/-- **Time bound for the reference generator.** If every gap of `λ(σ)` exceeds `1/n` (`n > 0`),
then for every Euclidean bounded-`C²` `g` with constant `C`,
`|𝓛_ref(σ) g (z)| ≤ refGenConst N r C n b₀ ℓ (1 + ‖z‖²)`. -/
theorem abs_referenceArrayGenerator_le {C : ℝ} {g : (Fin N → Fin r → ℂ) → ℝ}
    (hg : IsArrayC2Bounded C g) (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) {n : ℕ} (hn : 0 < n)
    (hgap : ∀ i j : Fin N, i ≠ j →
      1 / (n : ℝ) < |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)
    (z : Fin N → Fin r → ℂ) :
    |referenceArrayGenerator F a b₀ ω ℓ σ g z| ≤ refGenConst N r C n b₀ ℓ * (1 + ‖z‖ ^ 2) := by
  set M := supC2Const N r C with hMdef
  have hM0 : 0 ≤ M := supC2Const_nonneg (arrayC2_nonneg hg)
  have hD1 : ‖fderiv ℝ g z‖ ≤ M := norm_fderiv_le_supC2Const hg z
  have hD2 : ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ M := norm_fderiv_fderiv_le_supC2Const hg z
  have hZ0 : 0 ≤ 1 + ‖z‖ ^ 2 := by positivity
  have hZ1 : 1 ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
  have hxZ := le_one_add_sq ‖z‖
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv : 1 / (1 / (n : ℝ)) ^ 2 = (n : ℝ) ^ 2 := by rw [one_div_pow, one_div_one_div]
  -- couplings
  have hc : ∀ i j : Fin N, i ≠ j → 0 ≤ dysonCoupling N (flowEigenvalue F a ω σ) i j ∧
      dysonCoupling N (flowEigenvalue F a ω σ) i j ≤ (n : ℝ) ^ 2 := by
    intro i j hij
    have := dysonCoupling_bounds (by positivity) (hgap i j hij).le
    rw [hinv] at this
    exact this
  have hrate : ∀ i m : Fin N, flowRate F a ω σ i m ≤ (n : ℝ) ^ 2 := by
    intro i m
    by_cases him : i = m
    · subst him; simp [flowRate]
    · rw [← dysonCoupling_flow]; exact (hc i m him).2
  set β₀ : ℝ := max (N * (n : ℝ) ^ 2) (b₀ * N / ℓ) with hβ₀
  have hβ₀0 : 0 ≤ β₀ := le_max_of_le_left (by positivity)
  have hβ : ∀ i, 0 ≤ refDamping F a b₀ ω ℓ σ i ∧ refDamping F a b₀ ω ℓ σ i ≤ β₀ := by
    intro i
    have h0 := longCoupling_nonneg F a ω ℓ σ i
    have h1 : longCoupling F a ω ℓ σ i ≤ N * (n : ℝ) ^ 2 := by
      refine (le_abs_self _).trans ?_
      unfold longCoupling
      exact abs_sum_le_card_mul _ (by positivity) fun m _ => by
        rw [abs_of_nonneg (flowRate_nonneg F a ω σ i m)]; exact hrate i m
    unfold refDamping
    exact ⟨le_max_of_le_left h0, max_le_max h1 le_rfl⟩
  rw [referenceArrayGenerator_eq]
  -- short rotations
  have hS : |rotPart N r (flowEigenvalue F a ω σ) (fun i j => labelDist i j < ℓ) g z| ≤
      N * N * (n : ℝ) ^ 2 * M * (1 + ‖z‖ ^ 2) := by
    unfold rotPart
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have hB0 : 0 ≤ (n : ℝ) ^ 2 * (4 * M * (1 + ‖z‖ ^ 2)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hM0) hZ0)
    refine (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans (le_of_eq
      (show (1 / 4 : ℝ) * (N * (N * ((n : ℝ) ^ 2 * (4 * M * (1 + ‖z‖ ^ 2))))) = _ by ring))
    refine abs_sum_le_card_mul _ (mul_nonneg (Nat.cast_nonneg N) hB0) fun i _ => ?_
    refine abs_sum_le_card_mul _ hB0 fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_filter.1 hj).2.1.ne
    obtain ⟨h0, h1⟩ := hc i j hij
    rw [abs_mul, abs_of_nonneg h0]
    have hX := abs_fieldSq_le (norm_rotX_le i j) hM0 hD1 hD2
    have hY := abs_fieldSq_le (norm_rotY_le i j) hM0 hD1 hD2
    refine mul_le_mul_of_nonneg' h1 ((abs_add_le _ _).trans ?_) (abs_nonneg _) (sq_nonneg _)
    linarith
  -- OU part
  have hOU : |∑ i, refDamping F a b₀ ω ℓ σ i *
      (-(1 / 2 : ℝ) * fderiv ℝ g z (single i (z i)) +
        (1 / 4 : ℝ) * hqTrace (fderiv ℝ (fderiv ℝ g) z) i)| ≤
      N * β₀ * (1 + r) * M * (1 + ‖z‖ ^ 2) := by
    have hI0 : 0 ≤ (1 + r) * M * (1 + ‖z‖ ^ 2) :=
      mul_nonneg (mul_nonneg (by positivity) hM0) hZ0
    refine (abs_sum_le_card_mul _ (mul_nonneg hβ₀0 hI0) fun i _ => ?_).trans
      (le_of_eq (by ring))
    rw [abs_mul, abs_of_nonneg (hβ i).1]
    refine mul_le_mul_of_nonneg' (hβ i).2 ?_ (abs_nonneg _) hβ₀0
    have e1 : |fderiv ℝ g z (single i (z i))| ≤ M * ‖z‖ := by
      refine (abs_clm_le _ _).trans ?_
      rw [norm_single_eq]
      exact mul_le_mul_of_nonneg' hD1 (norm_le_pi_norm z i) (norm_nonneg _) hM0
    have e2 : |hqTrace (fderiv ℝ (fderiv ℝ g) z) i| ≤ r * (2 * M) :=
      (abs_hqTrace_le _ i).trans (by gcongr)
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    calc _ ≤ |-(1 / 2 : ℝ) * fderiv ℝ g z (single i (z i))| +
          |(1 / 4 : ℝ) * hqTrace (fderiv ℝ (fderiv ℝ g) z) i| := abs_add_le _ _
      _ = 1 / 2 * |fderiv ℝ g z (single i (z i))| +
          1 / 4 * |hqTrace (fderiv ℝ (fderiv ℝ g) z) i| := by
          rw [abs_mul, abs_mul]; norm_num
      _ ≤ 1 / 2 * (M * ‖z‖) + 1 / 4 * (r * (2 * M)) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 (by norm_num))
            (mul_le_mul_of_nonneg_left e2 (by norm_num))
      _ ≤ (1 + r) * M * (1 + ‖z‖ ^ 2) := by
          nlinarith [mul_le_mul_of_nonneg_left hxZ hM0,
            mul_le_mul_of_nonneg_left hZ1 (mul_nonneg hr hM0), mul_nonneg hM0 hZ0,
            mul_nonneg (mul_nonneg hr hM0) hZ0]
  calc _ ≤ |rotPart N r (flowEigenvalue F a ω σ) (fun i j => labelDist i j < ℓ) g z| +
        |∑ i, refDamping F a b₀ ω ℓ σ i *
          (-(1 / 2 : ℝ) * fderiv ℝ g z (single i (z i)) +
            (1 / 4 : ℝ) * hqTrace (fderiv ℝ (fderiv ℝ g) z) i)| := abs_add_le _ _
    _ ≤ N * N * (n : ℝ) ^ 2 * M * (1 + ‖z‖ ^ 2) + N * β₀ * (1 + r) * M * (1 + ‖z‖ ^ 2) :=
        add_le_add hS hOU
    _ = refGenConst N r C n b₀ ℓ * (1 + ‖z‖ ^ 2) := by
        simp only [refGenConst, hMdef, hβ₀]; ring

/-!
## The generator difference on long gaps
-/

/-- **Generator difference on long gaps.** If `ℓ ≥ 1`, `δ > 0` and every long gap
(`labelDist i j ≥ ℓ`) of `λ(σ)` is at least `δ`, then for every Euclidean bounded-`C²` `g` with
constant `C`, `|(𝒜_σ - 𝓛_ref(σ)) g (z)| ≤ genDiffConst N r C δ b₀ ℓ (1 + ‖z‖²)`. The short
rotations cancel exactly (`generator_diff_eq`); no hypothesis on short gaps is needed. -/
theorem abs_generator_diff_le {C : ℝ} {g : (Fin N → Fin r → ℂ) → ℝ}
    (hg : IsArrayC2Bounded C g) (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (σ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hlong : ∀ i j : Fin N, ℓ ≤ labelDist i j →
      δ ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)
    (z : Fin N → Fin r → ℂ) :
    |complexAngularGenerator N r (flowEigenvalue F a ω σ) g z -
        referenceArrayGenerator F a b₀ ω ℓ σ g z| ≤
      genDiffConst N r C δ b₀ ℓ * (1 + ‖z‖ ^ 2) := by
  set M := supC2Const N r C with hMdef
  have hM0 : 0 ≤ M := supC2Const_nonneg (arrayC2_nonneg hg)
  have hD1 : ‖fderiv ℝ g z‖ ≤ M := norm_fderiv_le_supC2Const hg z
  have hD2 : ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ M := norm_fderiv_fderiv_le_supC2Const hg z
  have hZ0 : 0 ≤ 1 + ‖z‖ ^ 2 := by positivity
  have hZ1 : 1 ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
  have hxZ := le_one_add_sq ‖z‖
  have hx2Z : ‖z‖ ^ 2 ≤ 1 + ‖z‖ ^ 2 := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hδ2 : 0 ≤ 1 / δ ^ 2 := by positivity
  have hc : ∀ i j : Fin N, ℓ ≤ labelDist i j →
      0 ≤ dysonCoupling N (flowEigenvalue F a ω σ) i j ∧
        dysonCoupling N (flowEigenvalue F a ω σ) i j ≤ 1 / δ ^ 2 :=
    fun i j hij => dysonCoupling_bounds hδ (hlong i j hij)
  set D1 := fderiv ℝ g z
  set D2 := fderiv ℝ (fderiv ℝ g) z
  have hTr : ∀ i, |hqTrace D2 i| ≤ r * (2 * M) := fun i =>
    (abs_hqTrace_le D2 i).trans (by gcongr)
  rw [generator_diff_eq F a b₀ ω hℓ σ g z]
  -- diagonal error
  have hdiag : |diagError N r (flowEigenvalue F a ω σ) ℓ D2 z| ≤
      N * N * (1 / δ ^ 2) * ((1 + r) * M / 2) * (1 + ‖z‖ ^ 2) := by
    unfold diagError
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have hB0 : 0 ≤ 1 / δ ^ 2 * (2 * (1 + r) * M * (1 + ‖z‖ ^ 2)) :=
      mul_nonneg hδ2 (mul_nonneg (mul_nonneg (by positivity) hM0) hZ0)
    refine (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans (le_of_eq
      (show (1 / 4 : ℝ) * (N * (N * (1 / δ ^ 2 * (2 * (1 + r) * M * (1 + ‖z‖ ^ 2))))) = _ by
        ring))
    refine abs_sum_le_card_mul _ (mul_nonneg (Nat.cast_nonneg N) hB0) fun i _ => ?_
    refine abs_sum_le_card_mul _ hB0 fun j hj => ?_
    obtain ⟨h0, h1⟩ := hc i j (Finset.mem_filter.1 hj).2
    rw [abs_mul, abs_of_nonneg h0]
    refine mul_le_mul_of_nonneg' h1 ?_ (abs_nonneg _) hδ2
    have e1 : |hq D2 i (z j)| ≤ 2 * M * ‖z‖ ^ 2 := by
      refine (abs_hq_le D2 i (z j)).trans ?_
      have := norm_le_pi_norm z j
      gcongr
    calc _ ≤ |hq D2 i (z j)| + |hqTrace D2 i| := abs_sub _ _
      _ ≤ 2 * M * ‖z‖ ^ 2 + r * (2 * M) := add_le_add e1 (hTr i)
      _ ≤ 2 * (1 + r) * M * (1 + ‖z‖ ^ 2) := by
          nlinarith [mul_le_mul_of_nonneg_left hx2Z hM0,
            mul_le_mul_of_nonneg_left hZ1 (mul_nonneg hr hM0), mul_nonneg hM0 hZ0,
            mul_nonneg (mul_nonneg hr hM0) hZ0, mul_nonneg hr (mul_nonneg hM0 hZ0)]
  -- cross error
  have hcross : |crossError N r (flowEigenvalue F a ω σ) ℓ D2 z| ≤
      N * N * (1 / δ ^ 2) * M * (1 + ‖z‖ ^ 2) := by
    unfold crossError
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have hB0 : 0 ≤ 1 / δ ^ 2 * (4 * M * (1 + ‖z‖ ^ 2)) :=
      mul_nonneg hδ2 (mul_nonneg (mul_nonneg (by norm_num) hM0) hZ0)
    refine (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans (le_of_eq
      (show (1 / 4 : ℝ) * (N * (N * (1 / δ ^ 2 * (4 * M * (1 + ‖z‖ ^ 2))))) = _ by ring))
    refine abs_sum_le_card_mul _ (mul_nonneg (Nat.cast_nonneg N) hB0) fun i _ => ?_
    refine abs_sum_le_card_mul _ hB0 fun j hj => ?_
    obtain ⟨h0, h1⟩ := hc i j (Finset.mem_filter.1 hj).2.2
    rw [abs_mul, abs_of_nonneg h0]
    refine mul_le_mul_of_nonneg' h1 ((abs_crossTerm_le D2 z i j).trans ?_) (abs_nonneg _) hδ2
    have : ‖D2‖ * ‖z‖ ^ 2 ≤ M * (1 + ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg' hD2 hx2Z (sq_nonneg _) hM0
    linarith
  -- floor error
  have hfloor : |floorError (refDamping F a b₀ ω ℓ σ) (longCoupling F a ω ℓ σ) D1 D2 z| ≤
      N * |b₀ * N / ℓ| * (1 + r) * M * (1 + ‖z‖ ^ 2) := by
    unfold floorError
    have hI0 : 0 ≤ (1 + r) * M * (1 + ‖z‖ ^ 2) :=
      mul_nonneg (mul_nonneg (by positivity) hM0) hZ0
    refine (abs_sum_le_card_mul _ (mul_nonneg (abs_nonneg (b₀ * N / ℓ)) hI0)
      fun i _ => ?_).trans (le_of_eq (by ring))
    rw [abs_mul]
    refine mul_le_mul_of_nonneg' (abs_refDamping_sub_le F a b₀ ω ℓ σ i) ?_ (abs_nonneg _)
      (abs_nonneg _)
    have e1 : |D1 (single i (z i))| ≤ M * ‖z‖ := by
      refine (abs_clm_le _ _).trans ?_
      rw [norm_single_eq]
      exact mul_le_mul_of_nonneg' hD1 (norm_le_pi_norm z i) (norm_nonneg _) hM0
    calc _ ≤ |(1 / 2 : ℝ) * D1 (single i (z i))| + |(1 / 4 : ℝ) * hqTrace D2 i| :=
          abs_sub _ _
      _ = 1 / 2 * |D1 (single i (z i))| + 1 / 4 * |hqTrace D2 i| := by
          rw [abs_mul, abs_mul]; norm_num
      _ ≤ 1 / 2 * (M * ‖z‖) + 1 / 4 * (r * (2 * M)) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 (by norm_num))
            (mul_le_mul_of_nonneg_left (hTr i) (by norm_num))
      _ ≤ (1 + r) * M * (1 + ‖z‖ ^ 2) := by
          nlinarith [mul_le_mul_of_nonneg_left hxZ hM0,
            mul_le_mul_of_nonneg_left hZ1 (mul_nonneg hr hM0), mul_nonneg hM0 hZ0,
            mul_nonneg (mul_nonneg hr hM0) hZ0]
  calc _ ≤ |diagError N r (flowEigenvalue F a ω σ) ℓ D2 z| +
        |crossError N r (flowEigenvalue F a ω σ) ℓ D2 z| +
        |floorError (refDamping F a b₀ ω ℓ σ) (longCoupling F a ω ℓ σ) D1 D2 z| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ N * N * (1 / δ ^ 2) * ((1 + r) * M / 2) * (1 + ‖z‖ ^ 2) +
        N * N * (1 / δ ^ 2) * M * (1 + ‖z‖ ^ 2) +
        N * |b₀ * N / ℓ| * (1 + r) * M * (1 + ‖z‖ ^ 2) :=
        add_le_add (add_le_add hdiag hcross) hfloor
    _ = genDiffConst N r C δ b₀ ℓ * (1 + ‖z‖ ^ 2) := by
        simp only [genDiffConst, hMdef]; ring

end BlockBand.Critical.RelativeVectors.RelativeDuhamel

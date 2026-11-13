module

public import BlockBand.Layers.FullEnergyPath

/-!
# `FetStepMean`: the conditional mean of the energy derivative at one separate-port step

The step sentence of the energy paragraph in the proof of the tagged-trace lemma:
`fetStepMean_holds (hcount) (hgrad) : FetStepMean`, the named input of `FullEnergyPath`, with no
further hypothesis.

Law: the fresh layer `layerLaw W b .separate`, conditional on the deterministic old input `X`
(Hermitian) and source `S ⪰ 0`; `z = z_∂(E)`, `E ∈ bulkInterval κ`. Norms: `ℓ²` operator norm on
matrices, modulus on scalars.

## Proof

1. **Scalar system** (`fetS_scalar`, deterministic): `x = f + Q(1 + z' + c x + b y) + e`,
   `y = κ(b x - z') + r`, `κ ≈ a²`, with `a²(ba' - z') = a'`, `1 + z' + (c + b)a' = 0` and the
   strict-contraction margin `|c + b²a²| Σ_j |Q_ij| ≤ t < 1 - b`: `|y - a'| ≤ q max|f - a'| + O(errors)`,
   `q = (b + g/4)/(b + 3g/4) < 1`, `g = 1 - b - t`.
2. **Clock pairing and comparison** (`fetS_pair_le`, `fetS_norm_RK_le`, `fetS_compare`):
   `S = K*YK`, `|W⁻¹ Tr(A S B)_{aa}| ≤ ‖KB‖‖AK*‖ u`, `‖R K*‖ ≤ 1` (normality of `R = K⁻¹`);
   traces of `T⁻¹ S T⁻¹ M` and `R S R` differ by `O((‖T - K‖ + ‖M - 1‖) u)`.
3. **Deterministic step** (`fetS_det_phys`, `fetS_det_port`, `fetS_det`): block rows of the exact
   mean identity `(𝒟 - 𝒮(ḡ))Ḡ = I + Res` and of its energy derivative
   `(𝒟' - 𝒮(ḡ'))Ḡ + (𝒟 - 𝒮(ḡ))Ḡ' = Res'`, `𝒟' = diag(-(I + S), z')`.
4. **Analytic input** (`fetS_energy_family`, `fetS_hasDerivAt_integral`, `fetS_resid_eq`,
   `fetS_resid_deriv`, `fetS_analytic`): along `X + (E' - E)S`, `∂_E Ḡ = E[-𝒢P𝒢]` (dominated
   convergence, fourth moments of the Gaussian absorption lemma), the residual is a combination of
   `Cov(W⁻¹ Tr(D𝒢), 𝒢)` whose energy derivatives are bounded by the energy clause of
   the differentiated-covariance lemma (`C(1+u)/W`), and `‖Res‖ ≤ C/W²`
   (the trace–matrix lemma, one-letter words).
5. **Assembly** (`fetS_small`, `fetS_final_arith`, `fetStepMean_holds`): means within
   `C δ + C/W²` of `a` (`layerComparison_holds`), row sums from `strictContraction_holds`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. The scalar linear system
-/

/-- `‖v j‖ ≤ max ‖v 0‖ ‖v 1‖`. -/
theorem fetS_le_max (v : Fin 2 → ℂ) (j : Fin 2) : ‖v j‖ ≤ max ‖v 0‖ ‖v 1‖ := by
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- **The differentiated two-port system** (deterministic).
Unknowns `x` (physical derivatives) and `y` (port derivatives) with
`x_i = f_i + Σ_j Q_ij (1 + z' + c x_j + b y_j) + e_i`, `y_j = κ_j (b x_j - z') + r_j`, where
`κ_j ≈ a²`, `a²(b a' - z') = a'` and `1 + z' + (c + b) a' = 0`. If
`|c + b²a²| Σ_j |Q_ij| ≤ t` with a gap `t + b + g ≤ 1`, then
`|y_j - a'| ≤ q max_i |f_i - a'| + O(η + ρ + ε + θ)` with `q = (b + g/4)/(b + 3g/4) < 1`. -/
theorem fetS_scalar (a a₁ z₁ : ℂ) (b c : ℝ) {t Qm A₁ η ρ ε θ g : ℝ}
    (hb : 0 ≤ b) (ha : ‖a‖ = 1) (hrel : a ^ 2 * ((b : ℂ) * a₁ - z₁) = a₁)
    (hcan : 1 + z₁ + ((c : ℂ) + b) * a₁ = 0)
    (Q : Fin 2 → Fin 2 → ℂ) (hmarg : ∀ i, ‖(c : ℂ) + (b : ℂ) ^ 2 * a ^ 2‖ * ∑ j, ‖Q i j‖ ≤ t)
    (hQm : ∀ i, ∑ j, ‖Q i j‖ ≤ Qm) (hQm0 : 0 ≤ Qm)
    (hA₁ : ‖a₁‖ ≤ A₁) (hA₁' : ‖(b : ℂ) * a₁ - z₁‖ ≤ A₁)
    (x y f e κ r : Fin 2 → ℂ)
    (hx : ∀ i, x i = f i + ∑ j, Q i j * (1 + z₁ + (c : ℂ) * x j + (b : ℂ) * y j) + e i)
    (hy : ∀ j, y j = κ j * ((b : ℂ) * x j - z₁) + r j)
    (hκ : ∀ j, ‖κ j - a ^ 2‖ ≤ η) (hr : ∀ j, ‖r j‖ ≤ ρ)
    (he : ∀ i, ‖e i‖ ≤ ε + θ * (‖x 0‖ + ‖x 1‖ + ‖y 0‖ + ‖y 1‖))
    (hη0 : 0 ≤ η) (hρ0 : 0 ≤ ρ) (hε0 : 0 ≤ ε) (hθ0 : 0 ≤ θ)
    (hg : 0 < g) (hgt : t + b + g ≤ 1)
    (hsmall : Qm * b ^ 2 * η + θ * (2 + 4 * b) ≤ g / 4) (hη1 : η ≤ 1) (hbη : b * η ≤ g / 4) :
    ∀ j, ‖y j - a₁‖ ≤ (b + g / 4) / (b + 3 * g / 4) * max ‖f 0 - a₁‖ ‖f 1 - a₁‖ +
      ((Qm * b + 3) * (A₁ * η + ρ) + ε + 4 * A₁ * θ) := by
  have hA0 : 0 ≤ A₁ := (norm_nonneg _).trans hA₁
  have ha2 : ‖a ^ 2‖ = 1 := by rw [norm_pow, ha, one_pow]
  set v : Fin 2 → ℂ := fun i => x i - a₁ with hv
  set w : Fin 2 → ℂ := fun j => y j - a₁ with hw
  set h : Fin 2 → ℂ := fun j => (κ j - a ^ 2) * ((b : ℂ) * a₁ - z₁) + r j with hh
  set H := A₁ * η + ρ with hH
  have hH0 : 0 ≤ H := by positivity
  have hhb : ∀ j, ‖h j‖ ≤ H := fun j => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul (hκ j) hA₁' (norm_nonneg _) hη0
    nlinarith [hr j]
  have hwj : ∀ j, w j = (b : ℂ) * κ j * v j + h j := fun j => by
    simp only [hw, hv, hh]
    rw [hy j]
    linear_combination hrel
  have hκn : ∀ j, ‖κ j‖ ≤ 1 + η := fun j => by
    have := norm_le_norm_add_norm_sub' (κ j) (a ^ 2)
    rw [ha2] at this
    linarith [hκ j]
  set V := max ‖v 0‖ ‖v 1‖ with hV
  have hvV : ∀ j, ‖v j‖ ≤ V := fetS_le_max v
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hvV 0)
  have hwb : ∀ j, ‖w j‖ ≤ b * (1 + η) * V + H := fun j => by
    rw [hwj j]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb]
    have h1 := mul_le_mul (mul_le_mul_of_nonneg_left (hκn j) hb) (hvV j) (norm_nonneg _)
      (by positivity)
    linarith [hhb j]
  -- the physical rows
  set Dm := max ‖f 0 - a₁‖ ‖f 1 - a₁‖ with hDm
  have hcoef : ∀ j, 1 + z₁ + (c : ℂ) * x j + (b : ℂ) * y j =
      ((c : ℂ) + (b : ℂ) ^ 2 * a ^ 2) * v j +
        ((b : ℂ) ^ 2 * (κ j - a ^ 2) * v j + (b : ℂ) * h j) := fun j => by
    have e1 : x j = a₁ + v j := by simp [hv]
    have e2 : y j = a₁ + w j := by simp [hw]
    rw [e1, e2, hwj j]
    linear_combination hcan
  have hcb : ∀ j, ‖(b : ℂ) ^ 2 * (κ j - a ^ 2) * v j + (b : ℂ) * h j‖ ≤ b ^ 2 * η * V + b * H :=
    fun j => by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb]
      have h1 := mul_le_mul (mul_le_mul_of_nonneg_left (hκ j) (by positivity : (0 : ℝ) ≤ b ^ 2))
        (hvV j) (norm_nonneg _) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left (hhb j) hb
      linarith
  have hxn : ‖x 0‖ + ‖x 1‖ + ‖y 0‖ + ‖y 1‖ ≤ 4 * A₁ + 2 * H + (2 + 4 * b) * V := by
    have ex : ∀ j, ‖x j‖ ≤ A₁ + V := fun j => by
      have : x j = a₁ + v j := by simp [hv]
      rw [this]; exact (norm_add_le _ _).trans (add_le_add hA₁ (hvV j))
    have ey : ∀ j, ‖y j‖ ≤ A₁ + (b * (1 + η) * V + H) := fun j => by
      have : y j = a₁ + w j := by simp [hw]
      rw [this]; exact (norm_add_le _ _).trans (add_le_add hA₁ (hwb j))
    have hbη2 : b * (1 + η) * V ≤ 2 * b * V := by
      have : b * (1 + η) ≤ 2 * b := by nlinarith
      exact mul_le_mul_of_nonneg_right this hV0
    linarith [ex 0, ex 1, ey 0, ey 1]
  have hvi : ∀ i, ‖v i‖ ≤ Dm + t * V + Qm * (b ^ 2 * η * V + b * H) +
      (ε + θ * (4 * A₁ + 2 * H + (2 + 4 * b) * V)) := fun i => by
    have e1 : v i = (f i - a₁) + ∑ j, Q i j * (((c : ℂ) + (b : ℂ) ^ 2 * a ^ 2) * v j) +
        ∑ j, Q i j * ((b : ℂ) ^ 2 * (κ j - a ^ 2) * v j + (b : ℂ) * h j) + e i := by
      have : v i = x i - a₁ := rfl
      have hs : ∑ j, Q i j * (1 + z₁ + (c : ℂ) * x j + (b : ℂ) * y j) =
          ∑ j, Q i j * (((c : ℂ) + (b : ℂ) ^ 2 * a ^ 2) * v j) +
            ∑ j, Q i j * ((b : ℂ) ^ 2 * (κ j - a ^ 2) * v j + (b : ℂ) * h j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hcoef j]; ring
      rw [this, hx i, hs]
      ring
    rw [e1]
    have s1 : ‖∑ j, Q i j * (((c : ℂ) + (b : ℂ) ^ 2 * a ^ 2) * v j)‖ ≤ t * V := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ j, ‖Q i j * (((c : ℂ) + (b : ℂ) ^ 2 * a ^ 2) * v j)‖ ≤
          ‖(c : ℂ) + (b : ℂ) ^ 2 * a ^ 2‖ * ‖Q i j‖ * V := fun j => by
        rw [norm_mul, norm_mul]
        have := mul_le_mul_of_nonneg_left (hvV j)
          (mul_nonneg (norm_nonneg (Q i j)) (norm_nonneg ((c : ℂ) + (b : ℂ) ^ 2 * a ^ 2)))
        linarith [mul_comm ‖Q i j‖ ‖(c : ℂ) + (b : ℂ) ^ 2 * a ^ 2‖]
      refine (Finset.sum_le_sum fun j _ => this j).trans ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_right (hmarg i) hV0
    have s2 : ‖∑ j, Q i j * ((b : ℂ) ^ 2 * (κ j - a ^ 2) * v j + (b : ℂ) * h j)‖ ≤
        Qm * (b ^ 2 * η * V + b * H) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ j, ‖Q i j * ((b : ℂ) ^ 2 * (κ j - a ^ 2) * v j + (b : ℂ) * h j)‖ ≤
          ‖Q i j‖ * (b ^ 2 * η * V + b * H) := fun j => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hcb j) (norm_nonneg _)
      refine (Finset.sum_le_sum fun j _ => this j).trans ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hQm i) (by positivity)
    have s3 : ‖e i‖ ≤ ε + θ * (4 * A₁ + 2 * H + (2 + 4 * b) * V) :=
      (he i).trans (by have := mul_le_mul_of_nonneg_left hxn hθ0; linarith)
    have s0 : ‖f i - a₁‖ ≤ Dm := fetS_le_max (fun i => f i - a₁) i
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add s0 s1)) s2)) s3).trans (le_of_eq ?_)
    ring
  have hVb : V ≤ Dm + t * V + Qm * (b ^ 2 * η * V + b * H) +
      (ε + θ * (4 * A₁ + 2 * H + (2 + 4 * b) * V)) := max_le (hvi 0) (hvi 1)
  set N0 := Qm * b * H + ε + θ * (4 * A₁ + 2 * H) with hN0
  have hDen : (b + 3 * g / 4) * V ≤ Dm + N0 := by
    have e : Qm * (b ^ 2 * η * V + b * H) = (Qm * b ^ 2 * η) * V + Qm * b * H := by ring
    have e2 : θ * (4 * A₁ + 2 * H + (2 + 4 * b) * V) =
        θ * (4 * A₁ + 2 * H) + θ * (2 + 4 * b) * V := by ring
    rw [e, e2] at hVb
    have hm : (Qm * b ^ 2 * η + θ * (2 + 4 * b)) * V ≤ g / 4 * V :=
      mul_le_mul_of_nonneg_right hsmall hV0
    nlinarith
  have hDp : 0 < b + 3 * g / 4 := by linarith
  have hVle : V ≤ (Dm + N0) / (b + 3 * g / 4) := by
    rw [le_div_iff₀ hDp]; linarith
  have hDm0 : 0 ≤ Dm := (norm_nonneg _).trans (le_max_left _ _)
  have hθ1 : θ ≤ 1 / 8 := by
    have h1 : θ * (2 + 4 * b) ≤ g / 4 := by nlinarith [mul_nonneg (mul_nonneg hQm0 (sq_nonneg b)) hη0]
    have hg1 : g ≤ 1 := by
      have : 0 ≤ t := (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)).trans
        (hmarg 0)
      linarith
    nlinarith
  intro j
  have hwj' := hwb j
  have hq : b * (1 + η) * V ≤ (b + g / 4) / (b + 3 * g / 4) * (Dm + N0) := by
    have h1 : b * (1 + η) ≤ b + g / 4 := by linarith
    calc b * (1 + η) * V ≤ (b + g / 4) * V := mul_le_mul_of_nonneg_right h1 hV0
      _ ≤ (b + g / 4) * ((Dm + N0) / (b + 3 * g / 4)) :=
          mul_le_mul_of_nonneg_left hVle (by positivity)
      _ = _ := by ring
  have hq1 : (b + g / 4) / (b + 3 * g / 4) ≤ 1 := by
    rw [div_le_one hDp]; linarith
  have hN00 : 0 ≤ N0 := by positivity
  have hqN : (b + g / 4) / (b + 3 * g / 4) * N0 ≤ N0 := by
    have := mul_le_mul_of_nonneg_right hq1 hN00; linarith
  have hfin : N0 + H ≤ (Qm * b + 3) * H + ε + 4 * A₁ * θ := by
    have h1 : θ * (2 * H) ≤ H := by
      have : θ * 2 ≤ 1 := by linarith
      calc θ * (2 * H) = (θ * 2) * H := by ring
        _ ≤ 1 * H := mul_le_mul_of_nonneg_right this hH0
        _ = H := one_mul H
    have e : N0 = Qm * b * H + ε + 4 * A₁ * θ + θ * (2 * H) := by rw [hN0]; ring
    rw [e]; linarith
  change ‖w j‖ ≤ _
  calc ‖w j‖ ≤ b * (1 + η) * V + H := hwj'
    _ ≤ (b + g / 4) / (b + 3 * g / 4) * (Dm + N0) + H := by linarith
    _ = (b + g / 4) / (b + 3 * g / 4) * Dm + ((b + g / 4) / (b + 3 * g / 4) * N0 + H) := by ring
    _ ≤ (b + g / 4) / (b + 3 * g / 4) * Dm + ((Qm * b + 3) * (A₁ * η + ρ) + ε + 4 * A₁ * θ) := by
        have : (b + g / 4) / (b + 3 * g / 4) * N0 + H ≤ (Qm * b + 3) * H + ε + 4 * A₁ * θ := by
          linarith
        linarith

/-!
## 2. Block traces, the trace pairing with the clock, and resolvent comparisons
-/

section Blocks

variable {W : ℕ}

/-- The block projection `P_b` on `Fin 2 × Fin W`. -/
def fetSPb (b : Fin 2) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  diagonal fun x => if x.1 = b then 1 else 0

theorem fetS_blockTrace_eq (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (a : Fin 2) :
    blockTrace N a = (W : ℂ)⁻¹ * (fetSPb a * N).trace := by
  unfold blockTrace fetSPb
  congr 1
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag, diagonal_mul]
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [hc]
  · simp

theorem fetS_norm_Pb_le (b : Fin 2) : ‖(fetSPb b : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ 1 := by
  rw [fetSPb, l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun x => ?_
  split_ifs <;> simp

theorem fetS_blockTrace_add (N M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (a : Fin 2) :
    blockTrace (N + M) a = blockTrace N a + blockTrace M a := by
  unfold blockTrace; rw [← mul_add, ← Finset.sum_add_distrib]; rfl

theorem fetS_blockTrace_sub (N M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (a : Fin 2) :
    blockTrace (N - M) a = blockTrace N a - blockTrace M a := by
  unfold blockTrace; rw [← mul_sub, ← Finset.sum_sub_distrib]; rfl

theorem fetS_blockTrace_smul (c : ℂ) (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (a : Fin 2) :
    blockTrace (c • N) a = c * blockTrace N a := by
  unfold blockTrace; rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]; ring

/-- `W⁻¹ Tr (R P_b R)_{aa} = Q_ab`. -/
theorem fetS_blockTrace_Pb (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (a b : Fin 2) :
    blockTrace (R * fetSPb b * R) a = blockPairTrace R a b := by
  unfold blockTrace blockPairTrace fetSPb
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun y _ => ?_
    simp [Matrix.mul_diagonal]
  · intro c _ hc
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [Matrix.mul_diagonal, hc]
  · simp

/-- `diag(λ_{x.1}) = Σ_b λ_b P_b`. -/
theorem fetS_diag_eq (lam : Fin 2 → ℂ) :
    (diagonal fun x : Fin 2 × Fin W => lam x.1) = ∑ b, lam b • fetSPb b := by
  ext x y
  rw [Matrix.sum_apply, Fin.sum_univ_two]
  simp only [fetSPb, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    rcases Fin.exists_fin_two.mp ⟨x.1, rfl⟩ with h | h <;> simp [h]
  · simp [hxy]

theorem fetS_one_eq : (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) = ∑ b, fetSPb b := by
  have := fetS_diag_eq (W := W) (fun _ => 1)
  simp only [one_smul, diagonal_one] at this
  exact this

/-- `W⁻¹ Tr (R L R)_{aa} = Σ_b λ_b Q_ab` for `L = diag(λ_{x.1})`. -/
theorem fetS_blockTrace_diag (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (lam : Fin 2 → ℂ)
    (a : Fin 2) :
    blockTrace (R * (diagonal fun x : Fin 2 × Fin W => lam x.1) * R) a =
      ∑ b, lam b * blockPairTrace R a b := by
  rw [fetS_diag_eq, Fin.sum_univ_two, Fin.sum_univ_two, Matrix.mul_add, Matrix.add_mul,
    fetS_blockTrace_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    fetS_blockTrace_smul, fetS_blockTrace_smul, fetS_blockTrace_Pb, fetS_blockTrace_Pb]

/-- `W⁻¹ Tr (R R)_{aa} = Σ_b Q_ab`. -/
theorem fetS_blockTrace_sq (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (a : Fin 2) :
    blockTrace (R * R) a = ∑ b, blockPairTrace R a b := by
  have := fetS_blockTrace_diag R (fun _ => 1) a
  simp only [diagonal_one, Matrix.mul_one, one_mul] at this
  exact this

/-- **Trace pairing with the clock**: for `S = K* Y K`, `Y ⪰ 0`,
`|W⁻¹ Tr (A S B)_{aa}| ≤ ‖K B‖ ‖A K*‖ W⁻¹ Re Tr Y`. -/
theorem fetS_pair_le {Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : Y.PosSemidef)
    (K A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (a : Fin 2) :
    ‖blockTrace (A * (Kᴴ * Y * K) * B) a‖ ≤ ‖K * B‖ * ‖A * Kᴴ‖ * ((W : ℝ)⁻¹ * Y.trace.re) := by
  rw [fetS_blockTrace_eq]
  have e : (fetSPb a * (A * (Kᴴ * Y * K) * B)).trace =
      (Y * (K * B * fetSPb a * (A * Kᴴ))).trace := by
    rw [show fetSPb a * (A * (Kᴴ * Y * K) * B) = (fetSPb a * A * Kᴴ) * (Y * (K * B)) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 := wl_norm_trace_weight_le hY (K * B * fetSPb a * (A * Kᴴ))
  have h2 : ‖K * B * fetSPb a * (A * Kᴴ)‖ ≤ ‖K * B‖ * ‖A * Kᴴ‖ := by
    calc ‖K * B * fetSPb a * (A * Kᴴ)‖ ≤ ‖K * B * fetSPb a‖ * ‖A * Kᴴ‖ := norm_mul_le _ _
      _ ≤ (‖K * B‖ * 1) * ‖A * Kᴴ‖ := by
          gcongr
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (fetS_norm_Pb_le a)
            (norm_nonneg _))
      _ = _ := by ring
  have h0 : 0 ≤ Y.trace.re := (norm_nonneg _).trans (dcv_norm_le_trace hY)
  calc (W : ℝ)⁻¹ * ‖(Y * (K * B * fetSPb a * (A * Kᴴ))).trace‖
      ≤ (W : ℝ)⁻¹ * (‖K * B * fetSPb a * (A * Kᴴ)‖ * Y.trace.re) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (W : ℝ)⁻¹ * ((‖K * B‖ * ‖A * Kᴴ‖) * Y.trace.re) := by gcongr
    _ = _ := by ring

/-- `‖(z - X)⁻¹ (z - X)*‖ ≤ 1` for Hermitian `X`, `Im z > 0` (normality). -/
theorem fetS_norm_RK_le {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    ‖(z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ *
      (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ‖ ≤ 1 := by
  set K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X with hK
  have hdet : IsUnit K.det := isUnit_iff_ne_zero.mpr (resolvent_det_ne_zero X hX z hz)
  have hKR : K * K⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hn := resolvent_normal X hX z hz
  have e : (K⁻¹ * Kᴴ)ᴴ * (K⁻¹ * Kᴴ) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc K * K⁻¹ᴴ * (K⁻¹ * Kᴴ) = K * (K⁻¹ᴴ * K⁻¹) * Kᴴ := by simp only [Matrix.mul_assoc]
      _ = K * (K⁻¹ * K⁻¹ᴴ) * Kᴴ := by rw [hn]
      _ = (K * K⁻¹) * (K * K⁻¹)ᴴ := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hKR, conjTranspose_one, Matrix.mul_one]
  have h1 := l2_opNorm_conjTranspose_mul_self (K⁻¹ * Kᴴ)
  rw [e] at h1
  have h2 := lct_norm_one_le (n := Fin 2 × Fin W)
  have h0 := norm_nonneg (K⁻¹ * Kᴴ)
  nlinarith

end Blocks

/-!
## 3. Comparison of the mean top inverse with the old resolvent
-/

section Compare

variable {W : ℕ}

/-- **Comparison estimates** (deterministic). `K` invertible with `R = K⁻¹`, `‖R‖ ≤ B_R`,
`‖R K*‖ ≤ 1`; `T = K + D` invertible with `U = T⁻¹`, `‖U‖ ≤ B_U`, `‖D‖ ≤ δ₁`; `M = 1 + ρ₁`,
`‖ρ₁‖ ≤ r₀`; `S = K* Y K`, `Y ⪰ 0`, `u = W⁻¹ Re Tr Y`. Then the physical trace of `U S U M`
differs from that of `R S R` by `O((δ₁ + r₀) u)`, and that of `U L U M` from that of `R L R` by
`O((δ₁ + r₀) ‖L‖)`. -/
theorem fetS_compare {K R T U D M ρ₁ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {BR BU δ₁ r₀ : ℝ} (hKR : K * R = 1) (hRK : ‖R * Kᴴ‖ ≤ 1) (hRn : ‖R‖ ≤ BR)
    (hT : T = K + D) (hUT : U * T = 1) (hTU : T * U = 1) (hUn : ‖U‖ ≤ BU) (hDn : ‖D‖ ≤ δ₁)
    (hM : M = 1 + ρ₁) (hρ : ‖ρ₁‖ ≤ r₀) (hY : Y.PosSemidef) (hBU : 0 ≤ BU) (hδ₁ : 0 ≤ δ₁)
    (hr₀ : 0 ≤ r₀) {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hS : S = Kᴴ * Y * K)
    (a : Fin 2) :
    ‖blockTrace (U * S * U * M) a - blockTrace (R * S * R) a‖ ≤
        (BU * δ₁ * ((1 + δ₁ * BU) * (1 + r₀)) + (r₀ + δ₁ * BU * (1 + r₀))) *
          ((W : ℝ)⁻¹ * Y.trace.re) ∧
      ∀ L : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        ‖blockTrace (U * L * U * M) a - blockTrace (R * L * R) a‖ ≤
          ‖L‖ * (BU * δ₁ * BR * (BU * (1 + r₀)) + BR * (BU * r₀ + BU * δ₁ * BR)) := by
  have hBR : 0 ≤ BR := (norm_nonneg _).trans hRn
  have hone := lct_norm_one_le (n := Fin 2 × Fin W)
  have hUR : U - R = -(U * D * R) := by
    have h1 : U * T * R = U * K * R + U * D * R := by
      rw [hT]; simp only [Matrix.mul_add, Matrix.add_mul]
    rw [hUT, Matrix.one_mul, Matrix.mul_assoc U K R, hKR, Matrix.mul_one] at h1
    have h' : U + U * D * R = R := h1.symm
    calc U - R = U - (U + U * D * R) := by rw [h']
      _ = -(U * D * R) := by abel
  have hKU : K * U = 1 - D * U := by
    have : T * U = K * U + D * U := by rw [hT, Matrix.add_mul]
    rw [hTU] at this; rw [this]; abel
  have hMn : ‖M‖ ≤ 1 + r₀ := by rw [hM]; exact (norm_add_le _ _).trans (by linarith)
  have hDU : ‖D * U‖ ≤ δ₁ * BU := (norm_mul_le _ _).trans (mul_le_mul hDn hUn (norm_nonneg _) hδ₁)
  have hKUn : ‖K * U‖ ≤ 1 + δ₁ * BU := by rw [hKU]; exact (norm_sub_le _ _).trans (by linarith)
  have hURn : ‖U - R‖ ≤ BU * δ₁ * BR := by
    rw [hUR, norm_neg]
    refine (norm_mul_le _ _).trans ?_
    refine mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul hUn hDn (norm_nonneg _) hBU)) hRn
      (norm_nonneg _) (by positivity)
  have hUMR : ‖U * M - R‖ ≤ BU * r₀ + BU * δ₁ * BR := by
    have e : U * M - R = U * ρ₁ + (U - R) := by rw [hM, Matrix.mul_add, Matrix.mul_one]; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans
      (mul_le_mul hUn hρ (norm_nonneg _) hBU)) hURn)
  have hUMn : ‖U * M‖ ≤ BU * (1 + r₀) := (norm_mul_le _ _).trans (mul_le_mul hUn hMn
    (norm_nonneg _) hBU)
  constructor
  · have e : U * S * U * M - R * S * R = (U - R) * S * (U * M) + R * S * (U * M - R) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]; abel
    rw [← fetS_blockTrace_sub, e, fetS_blockTrace_add]
    refine (norm_add_le _ _).trans ?_
    have t1 := fetS_pair_le hY K (U - R) (U * M) a
    have t2 := fetS_pair_le hY K R (U * M - R) a
    rw [← hS] at t1 t2
    have hu : 0 ≤ (W : ℝ)⁻¹ * Y.trace.re :=
      mul_nonneg (by positivity) ((norm_nonneg _).trans (dcv_norm_le_trace hY))
    have k1 : ‖K * (U * M)‖ ≤ (1 + δ₁ * BU) * (1 + r₀) := by
      rw [← Matrix.mul_assoc]
      exact (norm_mul_le _ _).trans (mul_le_mul hKUn hMn (norm_nonneg _) (by positivity))
    have k2 : ‖(U - R) * Kᴴ‖ ≤ BU * δ₁ := by
      have e3 : (U - R) * Kᴴ = -(U * (D * (R * Kᴴ))) := by
        rw [hUR]; simp only [Matrix.neg_mul, Matrix.mul_assoc]
      rw [e3, norm_neg]
      refine (norm_mul_le _ _).trans ?_
      have := (norm_mul_le D (R * Kᴴ)).trans (mul_le_mul hDn hRK (norm_nonneg _) hδ₁)
      calc ‖U‖ * ‖D * (R * Kᴴ)‖ ≤ BU * (δ₁ * 1) := mul_le_mul hUn this (norm_nonneg _) hBU
        _ = BU * δ₁ := by ring
    have k3 : ‖K * (U * M - R)‖ ≤ r₀ + δ₁ * BU * (1 + r₀) := by
      have e2 : K * (U * M - R) = ρ₁ - D * U * M := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc, hKU, hKR, hM]
        simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]; abel
      rw [e2]
      refine (norm_sub_le _ _).trans (add_le_add hρ ?_)
      exact (norm_mul_le _ _).trans (mul_le_mul hDU hMn (norm_nonneg _) (by positivity))
    have t1' := t1.trans (mul_le_mul_of_nonneg_right (mul_le_mul k1 k2 (norm_nonneg _)
      (by positivity)) hu)
    have t2' := t2.trans (mul_le_mul_of_nonneg_right (mul_le_mul k3 hRK (norm_nonneg _)
      (by positivity)) hu)
    calc _ ≤ (1 + δ₁ * BU) * (1 + r₀) * (BU * δ₁) * ((W : ℝ)⁻¹ * Y.trace.re) +
          (r₀ + δ₁ * BU * (1 + r₀)) * 1 * ((W : ℝ)⁻¹ * Y.trace.re) := add_le_add t1' t2'
      _ = _ := by ring
  · intro L
    have e : U * L * U * M - R * L * R = (U - R) * L * (U * M) + R * L * (U * M - R) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]; abel
    rw [← fetS_blockTrace_sub, e]
    refine (lct_norm_blockTrace_le _ a).trans ((norm_add_le _ _).trans ?_)
    have m3 : ∀ A B C : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
      fun A B C => (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
        (norm_nonneg _))
    have u1 := (m3 (U - R) L (U * M)).trans (mul_le_mul (mul_le_mul_of_nonneg_right hURn
      (norm_nonneg L)) hUMn (norm_nonneg _) (by positivity))
    have u2 := (m3 R L (U * M - R)).trans (mul_le_mul (mul_le_mul_of_nonneg_right hRn
      (norm_nonneg L)) hUMR (norm_nonneg _) (by positivity))
    calc _ ≤ BU * δ₁ * BR * ‖L‖ * (BU * (1 + r₀)) + BR * ‖L‖ * (BU * r₀ + BU * δ₁ * BR) :=
          add_le_add u1 u2
      _ = _ := by ring

end Compare

/-!
## 4. The deterministic step: from the exact and differentiated mean identities
-/

section Det

variable {W : ℕ}

/-- `(fromBlocks A 0 0 B * M)₁₁ = A M₁₁`. -/
theorem fetS_toBlocks11_mul {n m : Type*} [Fintype n] [Fintype m] (A : Matrix n n ℂ)
    (B : Matrix m m ℂ) (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (fromBlocks A 0 0 B * M).toBlocks₁₁ = A * M.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M, fromBlocks_multiply]
  simp

/-- `(fromBlocks A 0 0 diag(d) * M)_{yy} = d_y M_{yy}` on the port block. -/
theorem fetS_port_entry {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m] (A : Matrix n n ℂ)
    (d : m → ℂ) (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) (y : m) :
    (fromBlocks A 0 0 (diagonal d) * M) (Sum.inr y) (Sum.inr y) = d y * M (Sum.inr y) (Sum.inr y) := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [fromBlocks, diagonal_apply]

/-- The port row of `(fromBlocks A 0 0 diag(z - b gA_{y.1})) M` averaged over port `j`. -/
theorem fetS_port_trace {b : ℝ} (zz : ℂ) (gA : Fin 2 → ℂ)
    (A : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ)
    (M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) (j : Fin 2) :
    portBlockTrace (fromBlocks A 0 0 (diagonal fun y : PortSite W .separate =>
        meqPortCoef .separate zz (b : ℂ) gA y.1) * M) j =
      (zz - (b : ℂ) * gA j) * portBlockTrace M j := by
  unfold portBlockTrace
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [fetS_port_entry, meqPortCoef, meq_sum_inc_separate_port]
  ring

/-- `T - K` for `T = -E - X - diag(σ_{x.1})`, `K = z - X`. -/
theorem fetS_top_sub (E : ℝ) (z : ℂ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (σ : Fin 2 → ℂ) :
    (-((E : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) - X - diagonal fun x => σ x.1) =
      (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X) +
        diagonal fun x => -(E : ℂ) - z - σ x.1 := by
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    diagonal_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `‖diag(d_{x.1})‖ ≤ B` when every `|d_i| ≤ B`. -/
theorem fetS_norm_diag_le (d : Fin 2 → ℂ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, ‖d i‖ ≤ B) :
    ‖(diagonal fun x : Fin 2 × Fin W => d x.1)‖ ≤ B := by
  rw [l2_opNorm_diagonal]
  exact pi_norm_le_iff_of_nonneg hB |>.mpr fun x => h x.1

/-- `‖(z - X)⁻¹‖ ≤ (Im z)⁻¹`. -/
theorem fetS_norm_R_le {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    ‖(z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹‖ ≤ (z.im)⁻¹ := by
  have e : z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X = -X - diagonal fun _ => -z := by
    ext x y
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, diagonal_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [e]
  exact lct_norm_shifted_inv_le _ hX.neg _ hz fun _ => by simp

/-- Uniform scalar bounds on `bulkInterval κ`: `|a'|, |b a' - z_∂'| ≤ A₁` and `-Im a ≥ ι > 0`. -/
theorem fetS_scal_bounds {b κ : ℝ} (hb : 0 ≤ b) (hκ : 0 < κ) :
    ∃ A₁ ι : ℝ, 0 ≤ A₁ ∧ 0 < ι ∧ ∀ E ∈ bulkInterval κ, ‖tgtAd E‖ ≤ A₁ ∧
      ‖(b : ℂ) * tgtAd E - tgtZd b E‖ ≤ A₁ ∧ ι ≤ -(matchedA E).im := by
  obtain ⟨ι, hι, hιE⟩ := rp_im_a_lower hκ
  have hs0 : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨(2 * b + 2) / Real.sqrt (2 * κ), ι, by positivity, hι, fun E hE => ?_⟩
  have hE2 := abs_le_of_mem_bulkInterval hE
  have hE1 : |E| ≤ 2 := by linarith
  have hsq := sq_le_of_mem_bulkInterval hE
  have hn1 := norm_matchedA hE1
  have hk2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hlow : 2 * κ ≤ ‖1 - matchedA E ^ 2‖ ^ 2 := by
    rw [tgt_norm_one_sub_sq hE1]; nlinarith
  have hlow' : Real.sqrt (2 * κ) ≤ ‖1 - matchedA E ^ 2‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (1 - matchedA E ^ 2))]; exact Real.sqrt_le_sqrt hlow
  have ha1 : ‖tgtAd E‖ ≤ 1 / Real.sqrt (2 * κ) := by
    unfold tgtAd
    rw [norm_div, norm_pow, hn1, one_pow]
    exact div_le_div_of_nonneg_left zero_le_one hs0 hlow'
  have hz1 := tgt_norm_tgtZd_le hb hκ hE
  have hb1 : ‖(b : ℂ) * tgtAd E‖ ≤ b / Real.sqrt (2 * κ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb]
    calc b * ‖tgtAd E‖ ≤ b * (1 / Real.sqrt (2 * κ)) := mul_le_mul_of_nonneg_left ha1 hb
      _ = b / Real.sqrt (2 * κ) := by ring
  refine ⟨ha1.trans ?_, (norm_sub_le _ _).trans ?_, (hιE E hE).1⟩
  · rw [div_le_div_iff_of_pos_right hs0]; linarith
  · refine (add_le_add hb1 hz1).trans ?_
    rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hs0.le

/-- Arithmetic of the comparison constants. -/
theorem fetS_const_le {BU BR er r₀ : ℝ} (hBU : 0 ≤ BU) (hBR : 0 ≤ BR) (her : 0 ≤ er)
    (her1 : er ≤ 1) (hr₀ : 0 ≤ r₀) (hr1 : r₀ ≤ 1) :
    BU * er * ((1 + er * BU) * (1 + r₀)) + (r₀ + er * BU * (1 + r₀)) ≤
        4 * (1 + BU) ^ 2 * (1 + BR) ^ 2 * (er + r₀) ∧
      BU * er * BR * (BU * (1 + r₀)) + BR * (BU * r₀ + BU * er * BR) ≤
        4 * (1 + BU) ^ 2 * (1 + BR) ^ 2 * (er + r₀) := by
  have h1 : (1 + er * BU) * (1 + r₀) ≤ (1 + BU) * 2 := by
    have : er * BU ≤ BU := by nlinarith
    nlinarith
  have hK1 : 1 ≤ (1 + BR) ^ 2 := by nlinarith
  have hK2 : (2 * BU * (1 + BU) + 2 * BU + 1) ≤ 4 * (1 + BU) ^ 2 * (1 + BR) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hK1 (by positivity : (0:ℝ) ≤ 4 * (1 + BU) ^ 2)]
  have hK3 : (2 * BU ^ 2 * BR + BR * BU + BU * BR ^ 2) ≤ 4 * (1 + BU) ^ 2 * (1 + BR) ^ 2 := by
    nlinarith [mul_nonneg hBU hBR, mul_nonneg (mul_nonneg hBU hBU) hBR,
      mul_nonneg (mul_nonneg hBU hBR) hBR, mul_nonneg (mul_nonneg (mul_nonneg hBU hBU) hBR) hBR]
  constructor
  · have a1 : BU * er * ((1 + er * BU) * (1 + r₀)) ≤ 2 * BU * (1 + BU) * er := by
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hBU her); nlinarith
    have a2 : er * BU * (1 + r₀) ≤ 2 * BU * er := by nlinarith [mul_nonneg her hBU]
    have : BU * er * ((1 + er * BU) * (1 + r₀)) + (r₀ + er * BU * (1 + r₀)) ≤
        (2 * BU * (1 + BU) + 2 * BU + 1) * (er + r₀) := by nlinarith [mul_nonneg hBU her]
    exact this.trans (mul_le_mul_of_nonneg_right hK2 (by positivity))
  · have a1 : BU * er * BR * (BU * (1 + r₀)) ≤ 2 * BU ^ 2 * BR * er := by
      have : (1 + r₀) ≤ 2 := by linarith
      have h0 : 0 ≤ BU * er * BR * BU := by positivity
      nlinarith
    have : BU * er * BR * (BU * (1 + r₀)) + BR * (BU * r₀ + BU * er * BR) ≤
        (2 * BU ^ 2 * BR + BR * BU + BU * BR ^ 2) * (er + r₀) := by
      nlinarith [mul_nonneg (mul_nonneg hBU hBR) hr₀, mul_nonneg (mul_nonneg (mul_nonneg hBU hBR) hBR) her,
        mul_nonneg (mul_nonneg hBU hBR) her, mul_nonneg (mul_nonneg (mul_nonneg hBU hBU) hBR) hr₀,
        mul_nonneg (mul_nonneg (mul_nonneg hBU hBR) hBR) hr₀]
    exact this.trans (mul_le_mul_of_nonneg_right hK3 (by positivity))

end Det

/-!
## 5. The deterministic step
-/

section DetStep

variable {W : ℕ}

/-- The inverse bound `B_U = ((1-b)ι/2)⁻¹` of the mean top matrix. -/
def fetSBU (b ι : ℝ) : ℝ := ((1 - b) * ι / 2)⁻¹

/-- The comparison constant `K_c = 4(1 + B_U)²(1 + B_R)²`, `B_R = η₀⁻¹`. -/
def fetSKc (b ι η₀ : ℝ) : ℝ := 4 * (1 + fetSBU b ι) ^ 2 * (1 + η₀⁻¹) ^ 2

theorem fetS_le_sum (v : Fin 2 → ℂ) (i : Fin 2) : ‖v i‖ ≤ ‖v 0‖ + ‖v 1‖ := by
  fin_cases i
  · simp only [Fin.zero_eta]; linarith [norm_nonneg (v 1)]
  · simp only [Fin.mk_one]; linarith [norm_nonneg (v 0)]

theorem fetS_toBlocks11_add {n m : Type*} (A B : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (A + B).toBlocks₁₁ = A.toBlocks₁₁ + B.toBlocks₁₁ := rfl

theorem fetS_portBlockTrace_add (A B : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (j : Fin 2) : portBlockTrace (A + B) j = portBlockTrace A j + portBlockTrace B j := by
  unfold portBlockTrace; rw [← mul_add, ← Finset.sum_add_distrib]; rfl

theorem fetS_negE_sub_z {b E : ℝ} (hE : |E| ≤ 2) :
    -(E : ℂ) - boundaryZ b E = (1 - (b : ℂ)) * matchedA E := by
  have h := matchedA_add_inv hE
  unfold boundaryZ
  linear_combination -h

set_option maxHeartbeats 400000 in
/-- **Physical rows of the differentiated mean identity**: with
`U = T⁻¹` the inverse of the mean top matrix and `M = 1 + Res₁₁`, `ḡ'_A = W⁻¹Tr P (U Res'₁₁ +
U(S + 1 + Λ')UM)`, compared with `R = (z_∂ - X)⁻¹`: `ḡ'_{A,i} = f'_i + Σ_j Q_ij (1 + z_∂' + λ'_j) +
e_i` with `|e_i| ≤ B_U ‖Res'‖ + K_c(er + ‖Res‖)(u + 1 + Σ|ḡ'|)`. -/
theorem fetS_det_phys {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ} (hE : |E| < 2)
    {X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (hS : S.PosSemidef)
    (Gb Gd Res Res' : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (hid : (tflConst .separate E (boundaryZ b E) X - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gb a) (fun j => portBlockTrace Gb j)) * Gb = 1 + Res)
    (hdid : (tflConst .separate 1 (tgtZd b E) S - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gd a) (fun j => portBlockTrace Gd j)) * Gb +
      (tflConst .separate E (boundaryZ b E) X - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gb a) (fun j => portBlockTrace Gb j)) * Gd = Res')
    {er r₀ r₁ ι η₀ : ℝ}
    (her : ∀ i, ‖physBlockTrace Gb i - matchedA E‖ ≤ er ∧ ‖portBlockTrace Gb i - matchedA E‖ ≤ er)
    (hr0 : ‖Res‖ ≤ r₀) (hr1 : ‖Res'‖ ≤ r₁)
    (hι : 0 < ι) (hιa : ι ≤ -(matchedA E).im) (hη₀ : 0 < η₀) (hz : η₀ ≤ (boundaryZ b E).im)
    (her0 : 0 ≤ er) (hr00 : 0 ≤ r₀)
    (hsm : er ≤ ι / 2) (hsm1 : er ≤ 1 / 4) (hr01 : r₀ ≤ 1) :
    ∀ i, ∃ e : ℂ, physBlockTrace Gd i = fetFd b E X S i +
        ∑ j, blockPairTrace (fetR b E X) i j * (1 + tgtZd b E +
          ((1 - 2 * b : ℝ) : ℂ) * physBlockTrace Gd j + (b : ℂ) * portBlockTrace Gd j) + e ∧
      ‖e‖ ≤ (fetSBU b ι * r₁ + fetSKc b ι η₀ * (er + r₀) * fetClock b E X S +
          fetSKc b ι η₀ * (er + r₀)) + fetSKc b ι η₀ * (er + r₀) *
        (‖physBlockTrace Gd 0‖ + ‖physBlockTrace Gd 1‖ + ‖portBlockTrace Gd 0‖ +
          ‖portBlockTrace Gd 1‖) := by
  set a := matchedA E with ha
  set a₁ := tgtAd E with ha₁
  set z := boundaryZ b E with hzdef
  set z₁ := tgtZd b E with hz₁
  set c : ℂ := 1 - 2 * (b : ℂ) with hc
  have hcR : c = ((1 - 2 * b : ℝ) : ℂ) := by rw [hc]; push_cast; ring
  have hE2 : |E| ≤ 2 := hE.le
  have hEI : E ∈ Set.Ioo (-2 : ℝ) 2 := abs_lt.mp hE
  have ha1n : ‖a‖ = 1 := norm_matchedA hE2
  have ha0 : a ≠ 0 := tgt_matchedA_ne_zero hE2
  have hzpos : 0 < z.im := hη₀.trans_le hz
  set gA : Fin 2 → ℂ := fun i => physBlockTrace Gb i with hgA
  set gP : Fin 2 → ℂ := fun i => portBlockTrace Gb i with hgP
  set x : Fin 2 → ℂ := fun i => physBlockTrace Gd i with hx
  set y : Fin 2 → ℂ := fun i => portBlockTrace Gd i with hy
  -- the old resolvent
  set K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X with hK
  set R := fetR b E X with hR
  have hRK' : R = K⁻¹ := rfl
  have hKdet : IsUnit K.det := isUnit_iff_ne_zero.mpr (resolvent_det_ne_zero X hX z hzpos)
  have hKR : K * R = 1 := mul_nonsing_inv _ hKdet
  have hRn : ‖R‖ ≤ η₀⁻¹ := (fetS_norm_R_le hX hzpos).trans (inv_anti₀ hη₀ hz)
  have hRKn : ‖R * Kᴴ‖ ≤ 1 := fetS_norm_RK_le hX hzpos
  -- the mean top matrix
  set σ : Fin 2 → ℂ := fun i => c * gA i + (b : ℂ) * gP i with hσ
  set T := meqTop .separate E X c b gA gP with hT
  have hTeq : T = -((E : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) - X -
      diagonal fun x => σ x.1 := meqTop_separate E X c b gA gP
  have hTcmp : T = cmpTopH E X - diagonal (cmpExt (cmpSepShift b gA gP)) := by
    rw [hTeq]; exact lct_sep_top_eq b E X gA gP
  have himA : ∀ i, ι / 2 ≤ -(gA i).im ∧ ι / 2 ≤ -(gP i).im := fun i => by
    have h1 := (Complex.abs_im_le_norm (gA i - a)).trans (her i).1
    have h2 := (Complex.abs_im_le_norm (gP i - a)).trans (her i).2
    rw [Complex.sub_im] at h1 h2
    constructor <;> linarith [abs_le.mp h1, abs_le.mp h2]
  have hy0 : 0 < (1 - b) * ι / 2 := by
    have h1b : 0 < 1 - b := by linarith
    positivity
  obtain ⟨hTunit, hTn⟩ := lct_top_inv E hX (cmpSepShift b gA gP) hy0 fun i => by
    simp only [cmpSepShift]
    rw [cmp_im_comb]
    have h1 := (himA i).1
    have h2 := (himA i).2
    have hc0 : 0 ≤ 1 - 2 * b := by linarith
    nlinarith
  rw [← hTcmp] at hTunit hTn
  set U := T⁻¹ with hU
  have hUT : U * T = 1 := nonsing_inv_mul _ hTunit
  have hTU : T * U = 1 := mul_nonsing_inv _ hTunit
  have hUn : ‖U‖ ≤ fetSBU b ι := hTn
  set D : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := diagonal fun x => -(E : ℂ) - z - σ x.1 with hD
  have hTKD : T = K + D := by rw [hTeq, hK, hD]; exact fetS_top_sub E z X σ
  have hDn : ‖D‖ ≤ er := by
    refine fetS_norm_diag_le (W := W) (fun i => -(E : ℂ) - z - σ i) her0 fun i => ?_
    have e : -(E : ℂ) - z - σ i = c * (a - gA i) + (b : ℂ) * (a - gP i) := by
      have := fetS_negE_sub_z (b := b) hE2
      simp only [hσ]
      rw [this, hc]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hcR, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * b), Real.norm_of_nonneg hb0.le,
      norm_sub_rev a, norm_sub_rev a]
    have := mul_le_mul_of_nonneg_left (her i).1 (by linarith : (0 : ℝ) ≤ 1 - 2 * b)
    have := mul_le_mul_of_nonneg_left (her i).2 hb0.le
    nlinarith
  -- the top block of the identities
  have hT1 : T * Gb.toBlocks₁₁ = 1 + Res.toBlocks₁₁ := (meq_blocks hid).1
  set M₁ := 1 + Res.toBlocks₁₁ with hM₁
  have hGb11 : Gb.toBlocks₁₁ = U * M₁ := by
    rw [← hT1, ← Matrix.mul_assoc, hUT, Matrix.one_mul]
  rw [meq_D_fromBlocks, meq_D_fromBlocks] at hdid
  set T' := meqTop .separate 1 S c b x y with hT'
  have hdid11 := congrArg Matrix.toBlocks₁₁ hdid
  rw [fetS_toBlocks11_add, fetS_toBlocks11_mul, fetS_toBlocks11_mul] at hdid11
  set lam : Fin 2 → ℂ := fun i => 1 + (c * x i + (b : ℂ) * y i) with hlam
  set L : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := diagonal fun q => lam q.1 with hL
  have hT'eq : -T' = S + L := by
    rw [hT', meqTop_separate, hL]
    ext p q
    simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      diagonal_apply, Matrix.one_apply, smul_eq_mul, hlam]
    split_ifs <;> push_cast <;> ring
  have hGd11 : Gd.toBlocks₁₁ = U * Res'.toBlocks₁₁ + U * S * U * M₁ + U * L * U * M₁ := by
    have h1 : T * Gd.toBlocks₁₁ = Res'.toBlocks₁₁ - T' * Gb.toBlocks₁₁ := by
      rw [← hdid11]; abel
    have h2 : Gd.toBlocks₁₁ = U * (Res'.toBlocks₁₁ - T' * Gb.toBlocks₁₁) := by
      rw [← h1, ← Matrix.mul_assoc, hUT, Matrix.one_mul]
    rw [h2, hGb11, Matrix.mul_sub, ← Matrix.mul_assoc U T', ← Matrix.mul_assoc,
      show U * T' * U * M₁ = -(U * (-T') * U * M₁) by simp,
      hT'eq]
    simp only [Matrix.mul_add, Matrix.add_mul, sub_neg_eq_add, Matrix.mul_assoc]
    abel
  -- the physical rows
  set Q : Fin 2 → Fin 2 → ℂ := fun i j => blockPairTrace R i j with hQ
  set e : Fin 2 → ℂ := fun i => blockTrace (U * Res'.toBlocks₁₁) i +
    (blockTrace (U * S * U * M₁) i - blockTrace (R * S * R) i) +
    (blockTrace (U * L * U * M₁) i - blockTrace (R * L * R) i) with he
  have hxi : ∀ i, x i = fetFd b E X S i +
      ∑ j, Q i j * (1 + z₁ + ((1 - 2 * b : ℝ) : ℂ) * x j + (b : ℂ) * y j) + e i := fun i => by
    have h1 : x i = blockTrace (U * Res'.toBlocks₁₁) i + blockTrace (U * S * U * M₁) i +
        blockTrace (U * L * U * M₁) i := by
      change physBlockTrace Gd i = _
      rw [meq_physBlockTrace_eq_blockTrace, hGd11, fetS_blockTrace_add, fetS_blockTrace_add]
    have h2 : fetFd b E X S i = blockTrace (R * S * R) i - z₁ * ∑ j, Q i j := by
      unfold fetFd
      rw [show fetR b E X * (S - tgtZd b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) *
          fetR b E X = R * S * R - z₁ • (R * R) by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one]; rfl,
        fetS_blockTrace_sub, fetS_blockTrace_smul, fetS_blockTrace_sq]
    have h3 : blockTrace (R * L * R) i = ∑ j, lam j * Q i j := fetS_blockTrace_diag R lam i
    rw [h1, h2]
    simp only [he]
    rw [h3, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, hcR.symm]
    simp only [hlam]
    ring
  -- the error bounds
  have hBU0 : 0 ≤ fetSBU b ι := (norm_nonneg _).trans hUn
  set Y := Rᴴ * S * R with hY
  have hYpsd : Y.PosSemidef := dcv_Y_posSemidef hS
  have hSY : S = Kᴴ * Y * K := dcv_source_eq hKdet
  have hu : fetClock b E X S = (W : ℝ)⁻¹ * Y.trace.re := rfl
  have hρn : ‖Res.toBlocks₁₁‖ ≤ r₀ := (lct_norm_toBlocks11_le _).trans hr0
  have hc := fun i => fetS_compare hKR hRKn hRn hTKD hUT hTU hUn hDn hM₁ hρn hYpsd hBU0 her0
    hr00 hSY i
  obtain ⟨k1, k2⟩ := fetS_const_le hBU0 (inv_nonneg.mpr hη₀.le) her0 (by linarith) hr00 hr01
  have hcn : ‖((1 - 2 * b : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have hLn : ‖L‖ ≤ 1 + (‖x 0‖ + ‖x 1‖ + ‖y 0‖ + ‖y 1‖) := by
    refine fetS_norm_diag_le (W := W) lam (by positivity) fun i => ?_
    simp only [hlam]
    rw [hcR]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one]
    refine add_le_add le_rfl ((norm_add_le _ _).trans ?_)
    have hbn : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
    rw [norm_mul, norm_mul, hbn]
    have h1 := mul_le_mul_of_nonneg_right hcn (norm_nonneg (x i))
    have h2 : b * ‖y i‖ ≤ ‖y i‖ := by
      have := norm_nonneg (y i); nlinarith
    have hx2 : ‖x i‖ ≤ ‖x 0‖ + ‖x 1‖ := fetS_le_sum x i
    have hy2 : ‖y i‖ ≤ ‖y 0‖ + ‖y 1‖ := fetS_le_sum y i
    linarith
  intro i
  refine ⟨e i, hxi i, ?_⟩
  simp only [he]
  have b1 : ‖blockTrace (U * Res'.toBlocks₁₁) i‖ ≤ fetSBU b ι * r₁ :=
    (lct_norm_blockTrace_le _ i).trans ((norm_mul_le _ _).trans (mul_le_mul hUn
      ((lct_norm_toBlocks11_le _).trans hr1) (norm_nonneg _) hBU0))
  have b2 := (hc i).1.trans (mul_le_mul_of_nonneg_right k1 (mul_nonneg (by positivity)
    ((norm_nonneg _).trans (dcv_norm_le_trace hYpsd))))
  have b3 := ((hc i).2 L).trans (mul_le_mul hLn k2 (by positivity) (by positivity))
  rw [← hu] at b2
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  calc _ ≤ fetSBU b ι * r₁ + 4 * (1 + fetSBU b ι) ^ 2 * (1 + η₀⁻¹) ^ 2 * (er + r₀) *
        fetClock b E X S + (1 + (‖x 0‖ + ‖x 1‖ + ‖y 0‖ + ‖y 1‖)) *
          (4 * (1 + fetSBU b ι) ^ 2 * (1 + η₀⁻¹) ^ 2 * (er + r₀)) :=
        add_le_add (add_le_add b1 b2) b3
    _ = _ := by unfold fetSKc; ring

/-- **Port rows of the differentiated mean identity**: `(z' - b ḡ'_A) ḡ_P + (z - b ḡ_A) ḡ'_P =
W⁻¹ Tr Q Res'`, i.e. `ḡ'_P = κ(b ḡ'_A - z') + r` with `|κ - a²| ≤ 3 er`, `|r| ≤ 2‖Res'‖`. -/
theorem fetS_det_port {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ} (hE : |E| < 2)
    {X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (Gb Gd Res' : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (hdid : (tflConst .separate 1 (tgtZd b E) S - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gd a) (fun j => portBlockTrace Gd j)) * Gb +
      (tflConst .separate E (boundaryZ b E) X - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gb a) (fun j => portBlockTrace Gb j)) * Gd = Res')
    {er r₁ : ℝ}
    (her : ∀ i, ‖physBlockTrace Gb i - matchedA E‖ ≤ er ∧ ‖portBlockTrace Gb i - matchedA E‖ ≤ er)
    (hr1 : ‖Res'‖ ≤ r₁) (her0 : 0 ≤ er) (hr10 : 0 ≤ r₁) (hsm1 : er ≤ 1 / 4) :
    ∀ j, ∃ κ r : ℂ, portBlockTrace Gd j = κ * ((b : ℂ) * physBlockTrace Gd j - tgtZd b E) + r ∧
      ‖κ - matchedA E ^ 2‖ ≤ 3 * er ∧ ‖r‖ ≤ 2 * r₁ := by
  set a := matchedA E with ha
  set z := boundaryZ b E with hzdef
  set z₁ := tgtZd b E with hz₁
  have hE2 : |E| ≤ 2 := hE.le
  have ha1n : ‖a‖ = 1 := norm_matchedA hE2
  have ha0 : a ≠ 0 := tgt_matchedA_ne_zero hE2
  set gA : Fin 2 → ℂ := fun i => physBlockTrace Gb i with hgA
  set gP : Fin 2 → ℂ := fun i => portBlockTrace Gb i with hgP
  set x : Fin 2 → ℂ := fun i => physBlockTrace Gd i with hx
  set y : Fin 2 → ℂ := fun i => portBlockTrace Gd i with hy
  rw [meq_D_fromBlocks, meq_D_fromBlocks] at hdid
  -- the port rows
  have hport : ∀ j, (z₁ - (b : ℂ) * x j) * gP j + (z - (b : ℂ) * gA j) * y j =
      portBlockTrace Res' j := fun j => by
    have := congrArg (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
      portBlockTrace M j) hdid
    rw [fetS_portBlockTrace_add, fetS_port_trace, fetS_port_trace] at this
    exact this
  have hden : ∀ j, ‖(z - (b : ℂ) * gA j) - a⁻¹‖ ≤ b * er := fun j => by
    have e : (z - (b : ℂ) * gA j) - a⁻¹ = (b : ℂ) * (a - gA j) := by
      rw [hzdef, boundaryZ]; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (her j).1 hb0.le
  have hainv : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha1n, inv_one]
  have hden2 : ∀ j, 1 / 2 ≤ ‖z - (b : ℂ) * gA j‖ := fun j => by
    have h1 := norm_le_norm_add_norm_sub' a⁻¹ (z - (b : ℂ) * gA j)
    rw [hainv, norm_sub_rev a⁻¹] at h1
    have : b * er ≤ 1 / 2 := by nlinarith
    linarith [hden j]
  have hden0 : ∀ j, z - (b : ℂ) * gA j ≠ 0 := fun j h => by
    have := hden2 j; rw [h, norm_zero] at this; linarith
  intro j
  set κ : Fin 2 → ℂ := fun j => gP j / (z - (b : ℂ) * gA j) with hκ
  set r : Fin 2 → ℂ := fun j => portBlockTrace Res' j / (z - (b : ℂ) * gA j) with hr
  have hyj : ∀ j, y j = κ j * ((b : ℂ) * x j - z₁) + r j := fun j => by
    have h := hport j
    simp only [hκ, hr]
    field_simp [hden0 j]
    linear_combination h
  have hκb : ∀ j, ‖κ j - a ^ 2‖ ≤ 3 * er := fun j => by
    have hzD : z - (b : ℂ) * gA j = a⁻¹ - (b : ℂ) * (gA j - a) := by
      rw [hzdef]; unfold boundaryZ; ring
    have ha2 : a ^ 2 * a⁻¹ = a := by field_simp
    have e : κ j - a ^ 2 = ((gP j - a) + a ^ 2 * (b : ℂ) * (gA j - a)) / (z - (b : ℂ) * gA j) := by
      rw [eq_div_iff (hden0 j)]
      simp only [hκ]
      rw [sub_mul, div_mul_cancel₀ _ (hden0 j), hzD]
      linear_combination (-1 : ℂ) * ha2
    rw [e, norm_div]
    have hnum : ‖(gP j - a) + a ^ 2 * (b : ℂ) * (gA j - a)‖ ≤ (1 + b) * er := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, ha1n, one_pow, one_mul, Complex.norm_real,
        Real.norm_of_nonneg hb0.le]
      have := mul_le_mul_of_nonneg_left (her j).1 hb0.le
      linarith [(her j).2]
    rw [div_le_iff₀ (by linarith [hden2 j])]
    have := mul_le_mul_of_nonneg_left (hden2 j) (by positivity : (0 : ℝ) ≤ 3 * er)
    nlinarith
  have hrb : ∀ j, ‖r j‖ ≤ 2 * r₁ := fun j => by
    simp only [hr]
    rw [norm_div, div_le_iff₀ (by linarith [hden2 j])]
    have h1 := (meq_norm_portBlockTrace_le Res' j).trans hr1
    have := mul_le_mul_of_nonneg_left (hden2 j) (by positivity : (0 : ℝ) ≤ 2 * r₁)
    nlinarith
  exact ⟨κ j, r j, hyj j, hκb j, hrb j⟩

/-- **The deterministic step**: from the exact mean identity
`(𝒟 - 𝒮(ḡ)) Ḡ = I + Res` and its energy derivative `(𝒟' - 𝒮(ḡ')) Ḡ + (𝒟 - 𝒮(ḡ)) Ḡ' = Res'`
(`𝒟' = tflConst 1 z_∂' S = diag(-(I + S), z_∂')`), with means within `er` of `a`, the strict
contraction margin `t < 1 - b` and the row sums `≤ Q_m`, the port derivative mean obeys
`|ḡ'_{port j} - a'| ≤ q d + O(er + ‖Res‖ + ‖Res'‖ + (er + ‖Res‖) u)`,
`q = (b + g/4)/(b + 3g/4)`, `g = 1 - b - t`. -/
theorem fetS_det {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ} (hE : |E| < 2)
    {X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (hS : S.PosSemidef)
    (Gb Gd Res Res' : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (hid : (tflConst .separate E (boundaryZ b E) X - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gb a) (fun j => portBlockTrace Gb j)) * Gb = 1 + Res)
    (hdid : (tflConst .separate 1 (tgtZd b E) S - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gd a) (fun j => portBlockTrace Gd j)) * Gb +
      (tflConst .separate E (boundaryZ b E) X - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gb a) (fun j => portBlockTrace Gb j)) * Gd = Res')
    {er r₀ r₁ ι η₀ t Qm A₁ : ℝ}
    (her : ∀ i, ‖physBlockTrace Gb i - matchedA E‖ ≤ er ∧ ‖portBlockTrace Gb i - matchedA E‖ ≤ er)
    (hr0 : ‖Res‖ ≤ r₀) (hr1 : ‖Res'‖ ≤ r₁)
    (hι : 0 < ι) (hιa : ι ≤ -(matchedA E).im) (hη₀ : 0 < η₀) (hz : η₀ ≤ (boundaryZ b E).im)
    (hmarg : ∀ i, ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ *
      ∑ j, ‖blockPairTrace (fetR b E X) i j‖ ≤ t)
    (hQm : ∀ i, ∑ j, ‖blockPairTrace (fetR b E X) i j‖ ≤ Qm) (hQm0 : 0 ≤ Qm) (ht : t < 1 - b)
    (hA₁ : ‖tgtAd E‖ ≤ A₁) (hA₁' : ‖(b : ℂ) * tgtAd E - tgtZd b E‖ ≤ A₁)
    (her0 : 0 ≤ er) (hr00 : 0 ≤ r₀) (hr10 : 0 ≤ r₁)
    (hsm : er ≤ ι / 2) (hsm1 : er ≤ 1 / 4) (hr01 : r₀ ≤ 1)
    (hsm2 : Qm * b ^ 2 * (3 * er) + fetSKc b ι η₀ * (er + r₀) * (2 + 4 * b) ≤ (1 - b - t) / 4)
    (hsm3 : b * (3 * er) ≤ (1 - b - t) / 4) :
    ∀ j, ‖portBlockTrace Gd j - tgtAd E‖ ≤
      (b + (1 - b - t) / 4) / (b + 3 * (1 - b - t) / 4) * fetDist b E X S +
        ((Qm * b + 3) * (A₁ * (3 * er) + 2 * r₁) +
          (fetSBU b ι * r₁ + fetSKc b ι η₀ * (er + r₀) * fetClock b E X S +
            fetSKc b ι η₀ * (er + r₀)) + 4 * A₁ * (fetSKc b ι η₀ * (er + r₀))) := by
  have hE2 : |E| ≤ 2 := hE.le
  have hEI : E ∈ Set.Ioo (-2 : ℝ) 2 := abs_lt.mp hE
  have ha0 := tgt_matchedA_ne_zero hE2
  have hphys := fetS_det_phys hb0 hb1 hE hX hS Gb Gd Res Res' hid hdid her hr0 hr1 hι hιa hη₀ hz
    her0 hr00 hsm hsm1 hr01
  have hport := fetS_det_port hb0 hb1 hE Gb Gd Res' hdid her hr1 her0 hr10 hsm1
  choose e he using hphys
  choose κ r hr using hport
  have hK0 : 0 ≤ fetSKc b ι η₀ * (er + r₀) := by unfold fetSKc; positivity
  have hBU0 : 0 ≤ fetSBU b ι := by
    unfold fetSBU
    have h1b : 0 < 1 - b := by linarith
    positivity
  have hu0 : 0 ≤ fetClock b E X S := by
    unfold fetClock clkTrace
    exact mul_nonneg (by positivity) ((norm_nonneg _).trans (dcv_norm_le_trace
      (dcv_Y_posSemidef hS)))
  have hrel : matchedA E ^ 2 * ((b : ℂ) * tgtAd E - tgtZd b E) = tgtAd E := by
    unfold tgtZd; field_simp; ring
  have hcan : 1 + tgtZd b E + (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ)) * tgtAd E = 0 := by
    have := tgt_energy_cancel b hEI
    push_cast
    linear_combination this
  have hη1 : 3 * er ≤ 1 := by linarith
  have hsmall' : Qm * b ^ 2 * (3 * er) + fetSKc b ι η₀ * (er + r₀) * (2 + 4 * b) ≤
      (1 - b - t) / 4 := hsm2
  exact fetS_scalar (matchedA E) (tgtAd E) (tgtZd b E) b (1 - 2 * b) hb0.le
    (norm_matchedA hE2) hrel hcan _ hmarg hQm hQm0 hA₁ hA₁' (fun i => physBlockTrace Gd i)
    (fun j => portBlockTrace Gd j) (fun i => fetFd b E X S i) e κ r (fun i => (he i).1)
    (fun j => (hr j).1) (fun j => (hr j).2.1) (fun j => (hr j).2.2) (fun i => (he i).2)
    (by linarith) (by linarith) (by positivity) hK0 (by linarith) (by linarith) hsmall' hη1 hsm3

end DetStep

/-!
## 6. The analytic input: the exact and the differentiated mean identities
-/

section Analytic

/-- **Derivative of the mean along a curved family** (the `E 𝒢` part of
`tgt_hasDerivAt_cov_family`): `G_h - G₀ = -G_h Δ(h) G₀` a.e., `Δ(0) = 0`, `Δ'(0) = P`,
`E‖G_h‖⁴ ≤ C₄` for `|h| ≤ δ` give `∂_h E G_h = E[-G₀ P G₀]` at `0`. -/
theorem fetS_hasDerivAt_integral {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (G : ℝ → Ω → Matrix ι ι ℂ)
    (Δ : ℝ → Matrix ι ι ℂ) (P : Matrix ι ι ℂ) (hΔ : HasDerivAt Δ P 0) (hΔ0 : Δ 0 = 0)
    (hGm : ∀ h, Measurable (G h)) {δ : ℝ} (hδ : 0 < δ)
    (hres : ∀ h : ℝ, |h| ≤ δ → ∀ᵐ ω ∂μ, G h ω - G 0 ω = -(G h ω * Δ h * G 0 ω))
    {C4 : ℝ} (hmom : ∀ h : ℝ, |h| ≤ δ →
      Integrable (fun ω => ‖G h ω‖ ^ 4) μ ∧ ∫ ω, ‖G h ω‖ ^ 4 ∂μ ≤ C4) :
    HasDerivAt (fun h : ℝ => ∫ ω, G h ω ∂μ) (∫ ω, -(G 0 ω * P * G 0 ω) ∂μ) 0 := by
  set p := ‖P‖ with hp
  have hp0 : 0 ≤ p := norm_nonneg _
  obtain ⟨he, δ₁, hδ₁, hsmall⟩ := tgt_small_of_hasDerivAt hΔ hΔ0
  set c₁ := p + 1 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set k2 := c₁ ^ 2 + 1 with hk2
  set Gd : Ω → Matrix ι ι ℂ := fun ω => -(G 0 ω * P * G 0 ω) with hGd
  have h0 : |(0 : ℝ)| ≤ δ := by simp [hδ.le]
  have hC4 : 0 ≤ C4 := (integral_nonneg fun ω => by positivity).trans (hmom 0 h0).2
  set Q : ℝ → Ω → ℝ := fun h ω => 1 + ‖G h ω‖ ^ 4 + ‖G 0 ω‖ ^ 4 with hQ
  set B := 1 + 2 * C4 with hB
  have hQi : ∀ h, |h| ≤ δ → Integrable (Q h) μ := fun h hh =>
    ((integrable_const 1).add (hmom h hh).1).add (hmom 0 h0).1
  have hQB : ∀ h, |h| ≤ δ → ∫ ω, Q h ω ∂μ ≤ B := fun h hh => by
    simp only [hQ]
    have i1 : Integrable (fun ω => (1 : ℝ) + ‖G h ω‖ ^ 4) μ :=
      (integrable_const 1).add (hmom h hh).1
    rw [integral_add i1 (hmom 0 h0).1, integral_add (integrable_const 1) (hmom h hh).1,
      integral_const, probReal_univ, one_smul]
    linarith [(hmom h hh).2, (hmom 0 h0).2]
  have hGQ : ∀ h ω, ‖G h ω‖ ≤ Q h ω := fun h ω => by
    simpa using dcv_mono_le (norm_nonneg (G h ω)) (norm_nonneg (G 0 ω)) (i := 1) (j := 0)
      (by norm_num)
  have hG02 : ∀ ω, ‖G 0 ω‖ ^ 2 ≤ Q 0 ω := fun ω => by
    simpa using dcv_mono_le (norm_nonneg (G 0 ω)) (norm_nonneg (G 0 ω)) (i := 0) (j := 2)
      (by norm_num)
  have m3 : ∀ A B C : Matrix ι ι ℂ, ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := fun A B C =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have hGdn : ∀ ω, ‖Gd ω‖ ≤ p * ‖G 0 ω‖ ^ 2 := fun ω => by
    simp only [hGd, norm_neg]; exact (m3 _ _ _).trans (le_of_eq (by ring))
  have mG : ∀ h, AEStronglyMeasurable (G h) μ := fun h => (hGm h).aestronglyMeasurable
  have hGdm : Measurable Gd :=
    (((continuous_id.mul continuous_const).mul continuous_id).neg.measurable).comp (hGm 0)
  have iG : ∀ h, |h| ≤ δ → Integrable (G h) μ := fun h hh =>
    Integrable.mono' (hQi h hh) (mG h) (ae_of_all _ fun ω => hGQ h ω)
  have iGd : Integrable Gd μ :=
    Integrable.mono' ((hQi 0 h0).const_mul p) hGdm.aestronglyMeasurable (ae_of_all _ fun ω =>
      (hGdn ω).trans (mul_le_mul_of_nonneg_left (hG02 ω) hp0))
  set e : ℝ → ℝ := fun t => ‖Δ t - (t : ℂ) • P‖ with he_def
  have hδ₂ : 0 < min δ δ₁ := lt_min hδ hδ₁
  refine tgt_hasDerivAt_of_rem (r := e) (K := k2 * B) hδ₂ (fun t => norm_nonneg _) he
    fun t ht => ?_
  have htδ : |t| ≤ δ := ht.trans (min_le_left _ _)
  have htδ₁ : |t| ≤ δ₁ := ht.trans (min_le_right _ _)
  set ρ := t ^ 2 + e t with hρ
  have hexp : ∀ᵐ ω ∂μ, _ := (hres t htδ).mono fun ω hω =>
    tgt_expand_le (0 : Matrix ι ι ℂ →L[ℝ] ℂ) le_rfl (fun N => by simp) (Gh := G t ω)
      (G0 := G 0 ω) (P := P) (Δ := Δ t) hc₁0 hω (hsmall t htδ₁)
  have j1 : Integrable (fun ω => G t ω - G 0 ω) μ := (iG t htδ).sub (iG 0 h0)
  have j2 : Integrable (fun ω => (t : ℂ) • Gd ω) μ := iGd.smul (t : ℂ)
  have e1 : (∫ ω, G t ω ∂μ) - (∫ ω, G 0 ω ∂μ) - t • ∫ ω, Gd ω ∂μ =
      ∫ ω, (G t ω - G 0 ω - (t : ℂ) • Gd ω) ∂μ := by
    rw [integral_sub j1 j2, integral_sub (iG t htδ) (iG 0 h0), integral_smul,
      Complex.coe_smul]
  rw [e1]
  refine (dcv_norm_integral_le (hQi t htδ) (k := ρ * k2) ?_).trans ?_
  · filter_upwards [hexp] with ω hω
    have := hω.2.1
    simp only [hGd] at this ⊢
    refine this.trans (le_of_eq ?_)
    simp only [hQ, hρ, he_def, hk2]; ring
  · have := mul_le_mul_of_nonneg_left (hQB t htδ) (by positivity : 0 ≤ ρ * k2)
    nlinarith

/-- **The energy family of one separate-port layer** (setup of `tgt_energy_clause`, plus the
derivative of the mean): after `b, κ` there are `C_A, η₀ > 0` and `W₀`; for `W ≥ W₀` and every
Hermitian family `X(E)` near `E₀ ∈ bulkInterval κ` with `X'(E₀) = S`, near `E₀` the layer at
`(E, z_∂(E), X(E))` is a.s. invertible with `E‖𝒢‖⁴ ≤ C_A⁴`, `Im z_∂ ≥ η₀`, `|z_∂| ≤ 3`, and
`∂_E E 𝒢 = E[-𝒢 P 𝒢]` at `E₀`, `P = -Ŝ + D₀`. -/
theorem fetS_energy_family (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (CA η₀ : ℝ) (W₀ : ℕ), 0 < CA ∧ 0 < η₀ ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ (Xf : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (E₀ δ : ℝ),
      E₀ ∈ bulkInterval κ → 0 < δ → HasDerivAt Xf S E₀ →
      (∀ E : ℝ, |E - E₀| ≤ δ → (Xf E).IsHermitian) →
      ∃ δ' : ℝ, 0 < δ' ∧
        (∀ E : ℝ, |E - E₀| ≤ δ' → η₀ ≤ (boundaryZ b E).im ∧ ‖boundaryZ b E‖ ≤ 3 ∧
          (Xf E).IsHermitian ∧
          (∀ᵐ ω ∂layerLaw W b .separate,
            IsUnit (layerMatrix .separate E (boundaryZ b E) (Xf E) ω).det) ∧
          Integrable (fun ω => ‖layerResolvent .separate E (boundaryZ b E) (Xf E) ω‖ ^ 4)
            (layerLaw W b .separate) ∧
          ∫ ω, ‖layerResolvent .separate E (boundaryZ b E) (Xf E) ω‖ ^ 4
            ∂layerLaw W b .separate ≤ CA ^ 4) ∧
        HasDerivAt (fun E : ℝ => ∫ ω, layerResolvent .separate E (boundaryZ b E) (Xf E) ω
            ∂layerLaw W b .separate)
          (∫ ω, -(layerResolvent .separate E₀ (boundaryZ b E₀) (Xf E₀) ω *
            (-dcvHat S + tgtD0 (tgtZd b E₀)) *
              layerResolvent .separate E₀ (boundaryZ b E₀) (Xf E₀) ω) ∂layerLaw W b .separate)
          E₀ := by
  have hκ2 : 0 < κ / 2 := by positivity
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ2
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ :=
    BlockBand.Layers.gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  refine ⟨CA, η₀, ⌈4 / ε₁⌉₊, hCA, hη₀, ?_⟩
  intro W hW hWW Xf S E₀ δ hE₀ hδ hXd hXh
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  have hW4 : ((4 : ℕ) : ℝ) ≤ ε₁ * W := by
    have h1 : 4 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWW)
    rw [div_le_iff₀ hε₁] at h1; push_cast; linarith
  have hE₀' : E₀ ∈ Set.Ioo (-2 : ℝ) 2 := abs_lt.mp (abs_lt_two_of_mem_bulkInterval hκ hE₀)
  set z₁ := tgtZd b E₀ with hz₁
  set P : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
    -dcvHat S + tgtD0 z₁ with hPdef
  set Δ : ℝ → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ := fun t =>
    tgtBlk ((-t) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + (Xf E₀ - Xf (E₀ + t)),
      (boundaryZ b (E₀ + t) - boundaryZ b E₀) •
        (1 : Matrix (PortSite W .separate) (PortSite W .separate) ℂ)) with hΔdef
  have hX' : HasDerivAt (fun t => Xf (E₀ + t)) S 0 :=
    HasDerivAt.comp_const_add E₀ 0 (by rwa [add_zero])
  have hz' : HasDerivAt (fun t => boundaryZ b (E₀ + t)) z₁ 0 :=
    HasDerivAt.comp_const_add E₀ 0 (by rw [add_zero]; exact tgt_hasDerivAt_boundaryZ b hE₀')
  have ha : HasDerivAt (fun t : ℝ => (-t) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      (Xf E₀ - Xf (E₀ + t))) ((-1 : ℝ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + -S) 0 :=
    ((hasDerivAt_neg 0).smul_const _).add (hX'.const_sub _)
  have hb' : HasDerivAt (fun t : ℝ => (boundaryZ b (E₀ + t) - boundaryZ b E₀) •
      (1 : Matrix (PortSite W .separate) (PortSite W .separate) ℂ)) (z₁ • 1) 0 :=
    (hz'.sub_const _).smul_const _
  have hΔ' := tgtBlk.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (ha.prodMk hb')
  have hPeq : tgtBlk ((-1 : ℝ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + -S,
      z₁ • (1 : Matrix (PortSite W .separate) (PortSite W .separate) ℂ)) = P := by
    rw [tgtBlk_apply]
    change _ = -dcvHat S + tgtD0 z₁
    rw [dcvHat, tgtD0, fromBlocks_neg, fromBlocks_add]
    congr 1
    · rw [neg_one_smul]; abel
    · simp
    · simp
    · simp
  have hΔ : HasDerivAt Δ P 0 := by rw [← hPeq]; exact hΔ'
  have hΔ0 : Δ 0 = 0 := by simp [hΔdef, tgtBlk_apply]
  have hshift : ∀ (t : ℝ) ω, layerMatrix .separate (E₀ + t) (boundaryZ b (E₀ + t)) (Xf (E₀ + t)) ω =
      layerMatrix .separate (E₀ + 0) (boundaryZ b (E₀ + 0)) (Xf (E₀ + 0)) ω + Δ t := by
    intro t ω
    simp only [add_zero]
    exact tgt_layerMatrix_energy E₀ t _ _ _ _ ω
  have hδ' : 0 < min δ (κ / 2) := lt_min hδ hκ2
  have hmem : ∀ t : ℝ, |t| ≤ min δ (κ / 2) →
      E₀ + t ∈ bulkInterval (κ / 2) ∧ (Xf (E₀ + t)).IsHermitian := fun t ht => by
    have h1 := abs_le.mp (ht.trans (min_le_right _ _))
    refine ⟨⟨by linarith [hE₀.1], by linarith [hE₀.2]⟩, hXh _ ?_⟩
    rw [add_sub_cancel_left]; exact ht.trans (min_le_left _ _)
  have hinv : ∀ t : ℝ, |t| ≤ min δ (κ / 2) → ∀ᵐ ω ∂layerLaw W b .separate,
      IsUnit (layerMatrix .separate (E₀ + t) (boundaryZ b (E₀ + t)) (Xf (E₀ + t)) ω).det :=
    fun t ht => (habs W hW .separate _ (hmem t ht).2 _ _ (hbulk _ (hmem t ht).1).1
      (hbulk _ (hmem t ht).1).2.1).1
  have hmom : ∀ t : ℝ, |t| ≤ min δ (κ / 2) →
      Integrable (fun ω => ‖layerResolvent .separate (E₀ + t) (boundaryZ b (E₀ + t))
        (Xf (E₀ + t)) ω‖ ^ 4) (layerLaw W b .separate) ∧
      ∫ ω, ‖layerResolvent .separate (E₀ + t) (boundaryZ b (E₀ + t)) (Xf (E₀ + t)) ω‖ ^ 4
        ∂layerLaw W b .separate ≤ CA ^ 4 :=
    fun t ht => tcv_moment (m := 4) (by norm_num) hCA.le
      ((habs W hW .separate _ (hmem t ht).2 _ _ (hbulk _ (hmem t ht).1).1
        (hbulk _ (hmem t ht).1).2.1).2 _ (by norm_num) hW4)
  have h0 : |(0 : ℝ)| ≤ min δ (κ / 2) := by simp [hδ'.le]
  have hres : ∀ t : ℝ, |t| ≤ min δ (κ / 2) → ∀ᵐ ω ∂layerLaw W b .separate,
      layerResolvent .separate (E₀ + t) (boundaryZ b (E₀ + t)) (Xf (E₀ + t)) ω -
        layerResolvent .separate (E₀ + 0) (boundaryZ b (E₀ + 0)) (Xf (E₀ + 0)) ω =
        -(layerResolvent .separate (E₀ + t) (boundaryZ b (E₀ + t)) (Xf (E₀ + t)) ω * Δ t *
          layerResolvent .separate (E₀ + 0) (boundaryZ b (E₀ + 0)) (Xf (E₀ + 0)) ω) :=
    fun t ht => by
      filter_upwards [hinv t ht, hinv 0 h0] with ω h1 h2
      exact tgt_inv_sub_of_add (hshift t ω) h1 h2
  have hd := fetS_hasDerivAt_integral (μ := layerLaw W b .separate)
    (fun (t : ℝ) ω => layerResolvent .separate (E₀ + t) (boundaryZ b (E₀ + t)) (Xf (E₀ + t)) ω)
    Δ P hΔ hΔ0 (fun t => measurable_layerResolvent .separate _ _ _) hδ' hres hmom
  simp only [add_zero] at hd
  refine ⟨min δ (κ / 2), hδ', fun E hE => ?_, tgt_hasDerivAt_shift hd⟩
  have hE' : |E - E₀| ≤ min δ (κ / 2) := hE
  have e : E = E₀ + (E - E₀) := by ring
  have hm := hmem (E - E₀) hE'
  have hi := hinv (E - E₀) hE'
  have hmo := hmom (E - E₀) hE'
  rw [← e] at hm hi hmo
  exact ⟨(hbulk _ hm.1).1, (hbulk _ hm.1).2.1, hm.2, hi, hmo.1, hmo.2⟩

/-- Integrability from a fourth moment. -/
theorem fetS_integrable_four {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Ω → Matrix ι ι ℂ}
    (hG : Measurable G) (h4 : Integrable (fun ω => ‖G ω‖ ^ 4) μ) :
    Integrable G μ ∧ (∀ P : Matrix ι ι ℂ, Integrable (fun ω => G ω * P * G ω) μ) ∧
      ∀ (τ : Matrix ι ι ℂ →L[ℝ] ℂ) (cτ : ℝ), 0 ≤ cτ → (∀ N, ‖τ N‖ ≤ cτ * ‖N‖) →
        Integrable (fun ω => τ (G ω) • G ω) μ := by
  have hQ : Integrable (fun ω => 1 + ‖G ω‖ ^ 4 + ‖G ω‖ ^ 4) μ :=
    ((integrable_const 1).add h4).add h4
  have b1 : ∀ ω, ‖G ω‖ ≤ 1 + ‖G ω‖ ^ 4 + ‖G ω‖ ^ 4 := fun ω => by
    simpa using dcv_mono_le (norm_nonneg (G ω)) (norm_nonneg (G ω)) (i := 1) (j := 0)
      (by norm_num)
  have b2 : ∀ ω, ‖G ω‖ ^ 2 ≤ 1 + ‖G ω‖ ^ 4 + ‖G ω‖ ^ 4 := fun ω => by
    simpa using dcv_mono_le (norm_nonneg (G ω)) (norm_nonneg (G ω)) (i := 0) (j := 2)
      (by norm_num)
  refine ⟨Integrable.mono' hQ hG.aestronglyMeasurable (ae_of_all _ b1), fun P => ?_,
    fun τ cτ hcτ hτ => ?_⟩
  · refine Integrable.mono' (hQ.const_mul ‖P‖)
      ((((continuous_id.mul continuous_const).mul continuous_id).measurable).comp
        hG).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    calc ‖G ω * P * G ω‖ ≤ ‖G ω‖ * ‖P‖ * ‖G ω‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = ‖P‖ * ‖G ω‖ ^ 2 := by ring
      _ ≤ ‖P‖ * (1 + ‖G ω‖ ^ 4 + ‖G ω‖ ^ 4) := mul_le_mul_of_nonneg_left (b2 ω) (norm_nonneg _)
  · refine Integrable.mono' (hQ.const_mul cτ)
      ((τ.continuous.measurable.comp hG).aestronglyMeasurable.smul hG.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [norm_smul]
    calc ‖τ (G ω)‖ * ‖G ω‖ ≤ cτ * ‖G ω‖ * ‖G ω‖ :=
          mul_le_mul_of_nonneg_right (hτ _) (norm_nonneg _)
      _ = cτ * ‖G ω‖ ^ 2 := by ring
      _ ≤ cτ * (1 + ‖G ω‖ ^ 4 + ‖G ω‖ ^ 4) := mul_le_mul_of_nonneg_left (b2 ω) hcτ

/-- `Cov(f, P U) = P Cov(f, U)`. -/
theorem fetS_cov_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} (f : Ω → ℂ) (U : Ω → Matrix ι ι ℂ) (P : Matrix ι ι ℂ)
    (hfU : Integrable (fun ω => f ω • U ω) ν) (hU : Integrable U ν) :
    meqCov ν f (fun ω => P * U ω) = P * dcvCov ν f U := by
  set L : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ := ContinuousLinearMap.mul ℂ (Matrix ι ι ℂ) P with hL
  have hLapp : ∀ M, L M = P * M := fun M => rfl
  have hPU : Integrable (fun ω => P * U ω) ν := L.integrable_comp hU
  have hfPU : Integrable (fun ω => f ω • (P * U ω)) ν := by
    have : (fun ω => f ω • (P * U ω)) = fun ω => L (f ω • U ω) := by
      funext ω; rw [hLapp, Matrix.mul_smul]
    rw [this]; exact L.integrable_comp hfU
  unfold meqCov dcvCov
  rw [dcv_matrixExpect_eq_integral hfPU, dcv_matrixExpect_eq_integral hPU,
    dcv_matrixExpect_eq_integral hfU, dcv_matrixExpect_eq_integral hU]
  have e1 : ∫ ω, f ω • (P * U ω) ∂ν = P * ∫ ω, f ω • U ω ∂ν := by
    have : (fun ω => f ω • (P * U ω)) = fun ω => L (f ω • U ω) := by
      funext ω; rw [hLapp, Matrix.mul_smul]
    rw [this, L.integral_comp_comm hfU]; rfl
  have e2 : ∫ ω, P * U ω ∂ν = P * ∫ ω, U ω ∂ν := by
    change ∫ ω, L (U ω) ∂ν = _
    rw [L.integral_comp_comm hU]; rfl
  rw [e1, e2, Matrix.mul_sub, Matrix.mul_smul]

variable {W : ℕ}

/-- **The covariance residual as a combination of `Cov(W⁻¹ Tr(D𝒢), 𝒢)`** (separate ports). -/
theorem fetS_resid_eq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (G : Ω → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) (hGi : Integrable G ν)
    (hfG : ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
      Integrable (fun ω => ((W : ℂ)⁻¹ * (D * G ω).trace) • G ω) ν) (c b : ℂ) :
    meqResid ν c b G =
      ∑ a, c • (meqPhysProj a * dcvCov ν
          (fun ω => (W : ℂ)⁻¹ * (meqPhysProj (W := W) (σ := .separate) a * G ω).trace) G) +
        ∑ a, ∑ j, (b * meqInc .separate a j) •
          (meqPhysProj a * dcvCov ν
              (fun ω => (W : ℂ)⁻¹ * (meqPortProj (W := W) (σ := .separate) j * G ω).trace) G +
            meqPortProj j * dcvCov ν
              (fun ω => (W : ℂ)⁻¹ * (meqPhysProj (W := W) (σ := .separate) a * G ω).trace) G) := by
  unfold meqResid
  simp only [lct_phys_eq_trace, lct_port_eq_trace]
  have key : ∀ D P : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
      meqCov ν (fun ω => (W : ℂ)⁻¹ * (D * G ω).trace) (fun ω => P * G ω) =
        P * dcvCov ν (fun ω => (W : ℂ)⁻¹ * (D * G ω).trace) G :=
    fun D P => fetS_cov_mul _ _ _ (hfG D) hGi
  simp only [key]

theorem fetS_phys_add (M N : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (a : Fin LayerShape.separate.blocks) :
    physBlockTrace (M + N) a = physBlockTrace M a + physBlockTrace N a := by
  unfold physBlockTrace; rw [← mul_add, ← Finset.sum_add_distrib]; rfl

theorem fetS_port_add (M N : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (j : Fin LayerShape.separate.ports) :
    portBlockTrace (M + N) j = portBlockTrace M j + portBlockTrace N j := by
  unfold portBlockTrace; rw [← mul_add, ← Finset.sum_add_distrib]; rfl

theorem fetS_phys_smul (r : ℝ) (M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (a : Fin LayerShape.separate.blocks) : physBlockTrace (r • M) a = (r : ℂ) * physBlockTrace M a := by
  unfold physBlockTrace
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.smul_apply, Complex.real_smul]; ring

theorem fetS_port_smul (r : ℝ) (M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (j : Fin LayerShape.separate.ports) : portBlockTrace (r • M) j = (r : ℂ) * portBlockTrace M j := by
  unfold portBlockTrace
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.smul_apply, Complex.real_smul]; ring

theorem fetS_meqShift_eq (c b : ℂ) (gA gP : Fin 2 → ℂ) :
    (meqShift .separate c b gA gP : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) =
      diagonal (Sum.elim (fun x => c * gA x.1 + b * gP x.1) (fun y => b * gA y.1)) := by
  unfold meqShift
  congr 1
  funext p
  rcases p with p | p
  · simp only [Sum.elim_inl]; rw [meq_sum_inc_separate_phys]
  · simp only [Sum.elim_inr]; rw [meq_sum_inc_separate_port]

/-- The self-energy shift `M ↦ 𝒮_{c,b}(g(M))` of the separate-port layer, a real-linear map. -/
def fetSShift (W : ℕ) (b : ℝ) :
    Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ →L[ℝ]
      Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => meqShift .separate (1 - 2 * (b : ℂ)) b (fun a => physBlockTrace M a)
        (fun j => portBlockTrace M j)
      map_add' := fun M N => by
        simp only [fetS_meqShift_eq]
        ext p q
        rcases p with p | p <;> rcases q with q | q <;>
          simp only [Matrix.add_apply, diagonal_apply, Sum.elim_inl, Sum.elim_inr,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false, add_zero] <;>
          split_ifs <;> (try simp only [physBlockTrace, portBlockTrace, Matrix.add_apply,
            Finset.sum_add_distrib]) <;> ring
      map_smul' := fun r M => by
        simp only [fetS_meqShift_eq, RingHom.id_apply]
        ext p q
        rcases p with p | p <;> rcases q with q | q <;>
          simp only [Matrix.smul_apply, diagonal_apply, Sum.elim_inl, Sum.elim_inr,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false, smul_zero, Complex.real_smul] <;>
          split_ifs <;> (try simp only [physBlockTrace, portBlockTrace, Matrix.smul_apply,
            Complex.real_smul, Finset.mul_sum, ← Finset.sum_add_distrib]) <;>
          (try refine Finset.sum_congr rfl fun _ _ => ?_) <;> ring }

theorem fetSShift_apply (b : ℝ) (M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    fetSShift W b M = meqShift .separate (1 - 2 * (b : ℂ)) b (fun a => physBlockTrace M a)
      (fun j => portBlockTrace M j) := rfl

/-- `E ↦ tflConst(E, z_∂(E), X(E))` has derivative `tflConst(1, z_∂', S)`. -/
theorem fetS_hasDerivAt_tflConst {b E₀ : ℝ} (hE₀ : E₀ ∈ Set.Ioo (-2 : ℝ) 2)
    {Xf : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXf : HasDerivAt Xf S E₀) :
    HasDerivAt (fun E : ℝ => tflConst .separate E (boundaryZ b E) (Xf E))
      (tflConst .separate 1 (tgtZd b E₀) S) E₀ := by
  have hE' : HasDerivAt (fun E : ℝ => ((E : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)))
      (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) E₀ := by
    have := (hasDerivAt_id E₀).smul_const (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    simpa [Complex.coe_smul] using this
  have h1 : HasDerivAt (fun E : ℝ => -((E : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) -
      Xf E) (-1 - S) E₀ := hE'.neg.sub hXf
  have h2 : HasDerivAt (fun E : ℝ => boundaryZ b E •
      (1 : Matrix (PortSite W .separate) (PortSite W .separate) ℂ)) (tgtZd b E₀ • 1) E₀ :=
    (tgt_hasDerivAt_boundaryZ b hE₀).smul_const _
  have h3 := (tgtBlk (n := Fin 2 × Fin W) (m := PortSite W .separate)).hasFDerivAt.comp_hasDerivAt
    E₀ (h1.prodMk h2)
  convert h3 using 1
  · funext E; simp only [Function.comp_apply, tgtBlk_apply, tflConst]
  · simp only [tgtBlk_apply, tflConst, Complex.ofReal_one, one_smul]

theorem fetS_norm_c_le {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) : ‖(1 - 2 * (b : ℂ))‖ ≤ 1 := by
  rw [show (1 - 2 * (b : ℂ)) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]
  linarith

theorem fetS_norm_binc_le {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (a j : Fin 2) :
    ‖(b : ℂ) * meqInc .separate a j‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have := lct_norm_meqInc_le (σ := .separate) a j
  have := norm_nonneg (meqInc .separate a j)
  nlinarith

/-- **Derivative of the covariance residual**: if every `E ↦ Cov(W⁻¹ Tr(D𝒢(E)), 𝒢(E))`
(`‖D‖ ≤ 1`) has derivative `V_D` at `E₀` with `‖V_D‖ ≤ B`, then the residual combination of
`fetS_resid_eq` has derivative `Rd` with `‖Rd‖ ≤ 10 B`. -/
theorem fetS_resid_deriv {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (F : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ → ℝ →
      Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (V : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ →
      Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) {E₀ B : ℝ}
    (hF : ∀ D, ‖D‖ ≤ 1 → HasDerivAt (F D) (V D) E₀ ∧ ‖V D‖ ≤ B) :
    ∃ Rd, HasDerivAt (fun E => ∑ a, (1 - 2 * (b : ℂ)) • (meqPhysProj a *
          F (meqPhysProj (W := W) (σ := .separate) a) E) +
        ∑ a, ∑ j, ((b : ℂ) * meqInc .separate a j) •
          (meqPhysProj a * F (meqPortProj (W := W) (σ := .separate) j) E +
            meqPortProj j * F (meqPhysProj (W := W) (σ := .separate) a) E)) Rd E₀ ∧
      ‖Rd‖ ≤ 10 * B := by
  have hPa : ∀ a : Fin LayerShape.separate.blocks,
      ‖(meqPhysProj (W := W) (σ := .separate) a)‖ ≤ 1 := meq_norm_physProj_le
  have hQj : ∀ j : Fin LayerShape.separate.ports,
      ‖(meqPortProj (W := W) (σ := .separate) j)‖ ≤ 1 := meq_norm_portProj_le
  have hB : 0 ≤ B := (norm_nonneg _).trans (hF 0 (by simp)).2
  refine ⟨∑ a, (1 - 2 * (b : ℂ)) • (meqPhysProj a * V (meqPhysProj a)) +
      ∑ a, ∑ j, ((b : ℂ) * meqInc .separate a j) •
        (meqPhysProj a * V (meqPortProj j) + meqPortProj j * V (meqPhysProj a)), ?_, ?_⟩
  · have h := (HasDerivAt.sum (u := Finset.univ) fun a _ =>
      ((hF _ (hPa a)).1.const_mul (meqPhysProj (W := W) (σ := .separate) a)).const_smul
        (1 - 2 * (b : ℂ))).add
      (HasDerivAt.sum (u := Finset.univ) fun a _ => HasDerivAt.sum (u := Finset.univ) fun j _ =>
        ((((hF _ (hQj j)).1.const_mul (meqPhysProj (W := W) (σ := .separate) a)).add
          ((hF _ (hPa a)).1.const_mul (meqPortProj (W := W) (σ := .separate) j)))).const_smul
          ((b : ℂ) * meqInc .separate a j))
    convert h using 1
    funext E
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  · have m1 : ∀ (P D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ), ‖P‖ ≤ 1 →
        ‖D‖ ≤ 1 → ‖P * V D‖ ≤ B := fun P D hP hD =>
      (norm_mul_le _ _).trans ((mul_le_mul hP (hF D hD).2 (norm_nonneg _) zero_le_one).trans
        (by linarith))
    have hc := fetS_norm_c_le hb0 hb1
    refine (norm_add_le _ _).trans ?_
    have s1 : ‖∑ a : Fin LayerShape.separate.blocks, (1 - 2 * (b : ℂ)) •
        (meqPhysProj a * V (meqPhysProj (W := W) (σ := .separate) a))‖ ≤ 2 * B := by
      refine (norm_sum_le _ _).trans ?_
      rw [Fin.sum_univ_two]
      have : ∀ a, ‖(1 - 2 * (b : ℂ)) • (meqPhysProj a *
          V (meqPhysProj (W := W) (σ := .separate) a))‖ ≤ B := fun a => by
        rw [norm_smul]
        have := m1 _ _ (hPa a) (hPa a)
        nlinarith [norm_nonneg (1 - 2 * (b : ℂ)), norm_nonneg (meqPhysProj (W := W)
          (σ := .separate) a * V (meqPhysProj a))]
      linarith [this 0, this 1]
    have s2 : ‖∑ a : Fin LayerShape.separate.blocks, ∑ j : Fin LayerShape.separate.ports,
        ((b : ℂ) * meqInc .separate a j) •
          (meqPhysProj a * V (meqPortProj (W := W) (σ := .separate) j) +
            meqPortProj j * V (meqPhysProj (W := W) (σ := .separate) a))‖ ≤ 8 * B := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ a j, ‖((b : ℂ) * meqInc .separate a j) •
          (meqPhysProj a * V (meqPortProj (W := W) (σ := .separate) j) +
            meqPortProj j * V (meqPhysProj (W := W) (σ := .separate) a))‖ ≤ 2 * B := fun a j => by
        rw [norm_smul]
        have h1 := (norm_add_le _ _).trans (add_le_add (m1 _ _ (hPa a) (hQj j))
          (m1 _ _ (hQj j) (hPa a)))
        have h2 := fetS_norm_binc_le hb0 hb1 a j
        nlinarith [norm_nonneg ((b : ℂ) * meqInc .separate a j), norm_nonneg
          (meqPhysProj (W := W) (σ := .separate) a * V (meqPortProj j) +
            meqPortProj j * V (meqPhysProj a))]
      have hs : ∀ a : Fin LayerShape.separate.blocks, ‖∑ j : Fin LayerShape.separate.ports,
          ((b : ℂ) * meqInc .separate a j) •
            (meqPhysProj a * V (meqPortProj (W := W) (σ := .separate) j) +
              meqPortProj j * V (meqPhysProj (W := W) (σ := .separate) a))‖ ≤ 4 * B := fun a => by
        refine (norm_sum_le _ _).trans ?_
        rw [Fin.sum_univ_two]; linarith [this a 0, this a 1]
      rw [Fin.sum_univ_two]; linarith [hs 0, hs 1]
    linarith

/-- **Base residual**: `‖Res‖ ≤ 10 B` when every one-letter covariance is `≤ B`. -/
theorem fetS_resid_base {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (G : Ω → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) {B : ℝ}
    (hcov : ∀ P Q : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 →
      ‖meqCov ν (fun ω => (W : ℂ)⁻¹ * (P * G ω).trace) (fun ω => Q * G ω)‖ ≤ B) :
    ‖meqResid ν (1 - 2 * (b : ℂ)) b G‖ ≤ 10 * B := by
  have hPa : ∀ a : Fin LayerShape.separate.blocks,
      ‖(meqPhysProj (W := W) (σ := .separate) a)‖ ≤ 1 := meq_norm_physProj_le
  have hQj : ∀ j : Fin LayerShape.separate.ports,
      ‖(meqPortProj (W := W) (σ := .separate) j)‖ ≤ 1 := meq_norm_portProj_le
  have hB : 0 ≤ B := (norm_nonneg _).trans (hcov 0 0 (by simp) (by simp))
  have hc := fetS_norm_c_le hb0 hb1
  unfold meqResid
  simp only [lct_phys_eq_trace, lct_port_eq_trace]
  refine (norm_add_le _ _).trans ?_
  have s1 : ∀ a : Fin LayerShape.separate.blocks, ‖(1 - 2 * (b : ℂ)) • meqCov ν
      (fun ω => (W : ℂ)⁻¹ * (meqPhysProj a * G ω).trace) (fun ω => meqPhysProj a * G ω)‖ ≤ B :=
    fun a => by
      rw [norm_smul]
      have := hcov _ _ (hPa a) (hPa a)
      nlinarith [norm_nonneg (1 - 2 * (b : ℂ)), norm_nonneg (meqCov ν
        (fun ω => (W : ℂ)⁻¹ * (meqPhysProj a * G ω).trace) (fun ω => meqPhysProj a * G ω))]
  have s2 : ∀ (a : Fin LayerShape.separate.blocks) (j : Fin LayerShape.separate.ports),
      ‖((b : ℂ) * meqInc .separate a j) • (meqCov ν
        (fun ω => (W : ℂ)⁻¹ * (meqPortProj j * G ω).trace) (fun ω => meqPhysProj a * G ω) +
        meqCov ν (fun ω => (W : ℂ)⁻¹ * (meqPhysProj a * G ω).trace)
          (fun ω => meqPortProj j * G ω))‖ ≤ 2 * B := fun a j => by
    rw [norm_smul]
    have h1 := (norm_add_le _ _).trans (add_le_add (hcov _ _ (hQj j) (hPa a))
      (hcov _ _ (hPa a) (hQj j)))
    have h2 := fetS_norm_binc_le hb0 hb1 a j
    nlinarith [norm_nonneg ((b : ℂ) * meqInc .separate a j), norm_nonneg (meqCov ν
        (fun ω => (W : ℂ)⁻¹ * (meqPortProj j * G ω).trace) (fun ω => meqPhysProj a * G ω) +
        meqCov ν (fun ω => (W : ℂ)⁻¹ * (meqPhysProj a * G ω).trace)
          (fun ω => meqPortProj j * G ω))]
  have t1 : ‖∑ a : Fin LayerShape.separate.blocks, (1 - 2 * (b : ℂ)) • meqCov ν
      (fun ω => (W : ℂ)⁻¹ * (meqPhysProj a * G ω).trace) (fun ω => meqPhysProj a * G ω)‖ ≤
        2 * B := by
    refine (norm_sum_le _ _).trans ?_
    rw [Fin.sum_univ_two]; linarith [s1 0, s1 1]
  have t2 : ‖∑ a : Fin LayerShape.separate.blocks, ∑ j : Fin LayerShape.separate.ports,
      ((b : ℂ) * meqInc .separate a j) • (meqCov ν
        (fun ω => (W : ℂ)⁻¹ * (meqPortProj j * G ω).trace) (fun ω => meqPhysProj a * G ω) +
        meqCov ν (fun ω => (W : ℂ)⁻¹ * (meqPhysProj a * G ω).trace)
          (fun ω => meqPortProj j * G ω))‖ ≤ 8 * B := by
    refine (norm_sum_le _ _).trans ?_
    rw [Fin.sum_univ_two]
    have hs : ∀ a, ‖∑ j : Fin LayerShape.separate.ports, ((b : ℂ) * meqInc .separate a j) •
        (meqCov ν (fun ω => (W : ℂ)⁻¹ * (meqPortProj j * G ω).trace)
          (fun ω => meqPhysProj a * G ω) +
        meqCov ν (fun ω => (W : ℂ)⁻¹ * (meqPhysProj a * G ω).trace)
          (fun ω => meqPortProj j * G ω))‖ ≤ 4 * B := fun a => by
      refine (norm_sum_le _ _).trans ?_
      rw [Fin.sum_univ_two]; linarith [s2 a 0, s2 a 1]
    linarith [hs 0, hs 1]
  linarith

/-- `∫ g_j(F) = g_j(∫ F)` for integrable `F` (both trace kinds). -/
theorem fetS_port_integral {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {F : Ω → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ} (hF : Integrable F ν)
    (j : Fin LayerShape.separate.ports) : ∫ ω, portBlockTrace (F ω) j ∂ν = portBlockTrace (∫ ω, F ω ∂ν) j := by
  rw [← meq_matrixExpect_eq hF, meq_portBlockTrace_matrixExpect hF j]; rfl

theorem fetS_phys_integral {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {F : Ω → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ} (hF : Integrable F ν)
    (i : Fin LayerShape.separate.blocks) : ∫ ω, physBlockTrace (F ω) i ∂ν = physBlockTrace (∫ ω, F ω ∂ν) i := by
  rw [← meq_matrixExpect_eq hF, meq_physBlockTrace_matrixExpect hF i]; rfl

/-- The linear family `X(E) = X + (E - E₀) S`. -/
theorem fetS_linear_family {X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (hS : S.PosSemidef) (E₀ : ℝ) :
    HasDerivAt (fun E : ℝ => X + ((E - E₀ : ℝ) : ℂ) • S) S E₀ ∧
      (∀ E : ℝ, (X + ((E - E₀ : ℝ) : ℂ) • S).IsHermitian) ∧
      X + ((E₀ - E₀ : ℝ) : ℂ) • S = X := by
  refine ⟨?_, fun E => ?_, by simp⟩
  · have h1 : HasDerivAt (fun E : ℝ => ((E - E₀ : ℝ) : ℂ)) 1 E₀ := by
      have := ((hasDerivAt_id E₀).sub_const E₀).ofReal_comp
      simpa using this
    have h2 := (h1.smul_const S).const_add X
    simpa using h2
  · unfold IsHermitian
    rw [conjTranspose_add, conjTranspose_smul, hX.eq, hS.isHermitian.eq, Complex.star_def,
      Complex.conj_ofReal]

set_option maxHeartbeats 400000 in
/-- **The exact and the differentiated mean identities of one separate-port layer** ("differentiate this identity before estimating"). After `b, κ` there are `C ≥ 0`,
`W₀`; for `W ≥ W₀`, Hermitian `X`, `S ⪰ 0`, `E ∈ bulkInterval κ`, with `Ḡ = E 𝒢`, `Ḡ' = E[-𝒢P𝒢]`
(`P = -Ŝ + D₀`): `(𝒟 - 𝒮(ḡ)) Ḡ = I + Res`, `(𝒟' - 𝒮(ḡ')) Ḡ + (𝒟 - 𝒮(ḡ)) Ḡ' = Res'`,
`‖Res‖ ≤ C/W²`, `‖Res'‖ ≤ C(1 + u)/W`, and `E ġ_j = W⁻¹ Tr Q_j Ḡ'`. -/
theorem fetS_analytic (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
    ∀ E ∈ bulkInterval κ,
    ∃ Gb Gd Res Res' : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
      Gb = ∫ ω, layerResolvent .separate E (boundaryZ b E) X ω ∂layerLaw W b .separate ∧
      (∀ j, ∫ ℓ, fetGd b E X S ℓ j ∂layerLaw W b .separate = portBlockTrace Gd j) ∧
      (∀ i, physBlockTrace Gb i = ∫ ω, physBlockTrace
        (layerResolvent .separate E (boundaryZ b E) X ω) i ∂layerLaw W b .separate) ∧
      (∀ i, portBlockTrace Gb i = ∫ ω, portBlockTrace
        (layerResolvent .separate E (boundaryZ b E) X ω) i ∂layerLaw W b .separate) ∧
      ‖Res‖ ≤ C / (W : ℝ) ^ 2 ∧ ‖Res'‖ ≤ C * (1 + fetClock b E X S) / W ∧
      (tflConst .separate E (boundaryZ b E) X - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gb a) (fun j => portBlockTrace Gb j)) * Gb = 1 + Res ∧
      (tflConst .separate 1 (tgtZd b E) S - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gd a) (fun j => portBlockTrace Gd j)) * Gb +
      (tflConst .separate E (boundaryZ b E) X - meqShift .separate (1 - 2 * (b : ℂ)) b
        (fun a => physBlockTrace Gb a) (fun j => portBlockTrace Gb j)) * Gd = Res' := by
  obtain ⟨CA, η₀f, W₁, hCA, hη₀f, hfam⟩ := fetS_energy_family hcount hb0 hb1 hκ
  obtain ⟨Ce, W₂, hen⟩ := ((diffCovarianceFamily_holds' hcount hgrad) b hb0 hb1 κ hκ).2.1
  have habs := BlockBand.Layers.gaussianAbsorption_holds hcount
  obtain ⟨W₃, hmean⟩ := meanEquation_holds habs b hb0 hb1 η₀f 3 hη₀f
  obtain ⟨Cc1, W₄, hCc1, hcov1⟩ := lct_cov_one_letter habs hb0 hb1 (M := 3) hη₀f
  refine ⟨max (10 * Cc1) (10 * max Ce 0), max (max W₁ W₂) (max W₃ W₄), by positivity, ?_⟩
  intro W hW hWW X S hX hS E₀ hE₀
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hWW
  have hW4 : W₄ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hWW
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  have hE₀' : E₀ ∈ Set.Ioo (-2 : ℝ) 2 := abs_lt.mp (abs_lt_two_of_mem_bulkInterval hκ hE₀)
  obtain ⟨hXd, hXh, hX0⟩ := fetS_linear_family hX hS E₀
  set Xf : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fun E => X + ((E - E₀ : ℝ) : ℂ) • S
    with hXfdef
  obtain ⟨δ', hδ', hnear, hderG⟩ := hfam W hW hW1 Xf S E₀ 1 hE₀ one_pos hXd (fun E _ => hXh E)
  set μ := layerLaw W b .separate with hμ
  set P : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
    -dcvHat S + tgtD0 (tgtZd b E₀) with hP
  set Gf : ℝ → LayerSample W .separate → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
    fun E ω => layerResolvent .separate E (boundaryZ b E) (Xf E) ω with hGf
  set Gb : ℝ → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
    fun E => ∫ ω, Gf E ω ∂μ with hGb
  -- integrability near `E₀`
  have hint : ∀ E, |E - E₀| ≤ δ' → Integrable (Gf E) μ ∧
      (∀ Q : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
        Integrable (fun ω => Gf E ω * Q * Gf E ω) μ) ∧
      ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
        Integrable (fun ω => ((W : ℂ)⁻¹ * (D * Gf E ω).trace) • Gf E ω) μ := fun E hE => by
    obtain ⟨h1, h2, h3⟩ := fetS_integrable_four (measurable_layerResolvent .separate E
      (boundaryZ b E) (Xf E)) (hnear E hE).2.2.2.2.1
    exact ⟨h1, h2, fun D => h3 (tflTraceCLM W .separate D) (4 * ‖D‖) (by positivity)
      (fun N => dcv_traceCLM_le .separate hW D N)⟩
  -- the residual combination
  set F : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ → ℝ →
      Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
    fun D E => dcvCov μ (fun ω => (W : ℂ)⁻¹ * (D * Gf E ω).trace) (Gf E) with hF
  set Rform : ℝ → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ := fun E =>
    ∑ a, (1 - 2 * (b : ℂ)) • (meqPhysProj a * F (meqPhysProj (W := W) (σ := .separate) a) E) +
      ∑ a, ∑ j, ((b : ℂ) * meqInc .separate a j) •
        (meqPhysProj a * F (meqPortProj (W := W) (σ := .separate) j) E +
          meqPortProj j * F (meqPhysProj (W := W) (σ := .separate) a) E) with hRform
  -- the mean identity near `E₀`
  have hidE : ∀ E, |E - E₀| ≤ δ' →
      (tflConst .separate E (boundaryZ b E) (Xf E) - fetSShift W b (Gb E)) * Gb E =
        1 + Rform E := fun E hE => by
    obtain ⟨hz1, hz3, hXE, hinvE, -, -⟩ := hnear E hE
    obtain ⟨hGi, -, hfG⟩ := hint E hE
    have h := hmean W hW hW3 .separate (Xf E) hXE E (boundaryZ b E) hz1 hz3
    have hmA : meqMeanA μ (Gf E) = fun a => physBlockTrace (Gb E) a := by
      funext a; rw [← meq_physBlockTrace_matrixExpect hGi a, meq_matrixExpect_eq hGi]
    have hmP : meqMeanP μ (Gf E) = fun j => portBlockTrace (Gb E) j := by
      funext j; rw [← meq_portBlockTrace_matrixExpect hGi j, meq_matrixExpect_eq hGi]
    have hR := fetS_resid_eq (Gf E) hGi hfG (1 - 2 * (b : ℂ)) b
    change (tflConst .separate E (boundaryZ b E) (Xf E) - meqShift .separate (1 - 2 * (b : ℂ)) b
        (meqMeanA μ (Gf E)) (meqMeanP μ (Gf E))) * matrixExpect μ (Gf E) =
          1 + meqResid μ (1 - 2 * (b : ℂ)) b (Gf E) at h
    rw [hmA, hmP, meq_matrixExpect_eq hGi, hR] at h
    rw [fetSShift_apply]
    exact h
  -- derivatives
  have hcov : ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
      HasDerivAt (F D) (dcvCovDir μ D (Gf E₀) P) E₀ ∧
        ‖dcvCovDir μ D (Gf E₀) P‖ ≤ max Ce 0 * (1 + fetClock b E₀ X S) / W := fun D hD => by
    obtain ⟨h1, -, h3⟩ := hen W hW hW2 Xf S E₀ 1 hE₀ one_pos hS hXd (fun E _ => hXh E) D hD
    refine ⟨h1, h3.trans ?_⟩
    have hu : 0 ≤ 1 + fetClock b E₀ X S := by
      have : 0 ≤ fetClock b E₀ X S := by
        unfold fetClock clkTrace
        exact mul_nonneg (by positivity) ((norm_nonneg _).trans (dcv_norm_le_trace
          (dcv_Y_posSemidef hS)))
      linarith
    have e : (W : ℝ)⁻¹ * ((boundaryZ b E₀ • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        Xf E₀)⁻¹ᴴ * S * (boundaryZ b E₀ • 1 - Xf E₀)⁻¹).trace.re = fetClock b E₀ X S := by
      rw [show Xf E₀ = X from hX0]; rfl
    rw [e]
    gcongr
    exact le_max_left _ _
  obtain ⟨Rd, hRd, hRdn⟩ := fetS_resid_deriv hb0 hb1 F (fun D => dcvCovDir μ D (Gf E₀) P) hcov
  have hL : HasDerivAt (fun E => (tflConst .separate E (boundaryZ b E) (Xf E) -
      fetSShift W b (Gb E)) * Gb E)
      ((tflConst .separate 1 (tgtZd b E₀) S - fetSShift W b (∫ ω, -(Gf E₀ ω * P * Gf E₀ ω) ∂μ)) *
        Gb E₀ + (tflConst .separate E₀ (boundaryZ b E₀) (Xf E₀) - fetSShift W b (Gb E₀)) *
          ∫ ω, -(Gf E₀ ω * P * Gf E₀ ω) ∂μ) E₀ :=
    ((fetS_hasDerivAt_tflConst hE₀' hXd).sub
      ((fetSShift W b).hasFDerivAt.comp_hasDerivAt E₀ hderG)).mul hderG
  have hev : (fun E => (tflConst .separate E (boundaryZ b E) (Xf E) - fetSShift W b (Gb E)) *
      Gb E) =ᶠ[𝓝 E₀] fun E => 1 + Rform E := by
    filter_upwards [Metric.closedBall_mem_nhds E₀ hδ'] with E hE
    exact hidE E (by rwa [Metric.mem_closedBall, Real.dist_eq] at hE)
  have hR1 : HasDerivAt (fun E => 1 + Rform E) Rd E₀ := by
    exact hRd.const_add (1 : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
  have huniq := (hL.congr_of_eventuallyEq hev.symm).unique hR1
  -- assemble at `E₀`
  have h0 : |E₀ - E₀| ≤ δ' := by simp [hδ'.le]
  obtain ⟨hGi0, hGPG0, -⟩ := hint E₀ h0
  have hXE0 : Xf E₀ = X := hX0
  refine ⟨Gb E₀, ∫ ω, -(Gf E₀ ω * P * Gf E₀ ω) ∂μ, Rform E₀, Rd, ?_, fun j => ?_,
    fun i => ?_, fun i => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hGb, hGf, hXE0]
  · have e : (fun ℓ => fetGd b E₀ X S ℓ j) = fun ℓ => portBlockTrace (-(Gf E₀ ℓ * P * Gf E₀ ℓ)) j := by
      funext ℓ
      rw [lct_port_eq_trace, fetGd, hGf]
      simp only [hXE0, trace_neg, mul_neg]
      rfl
    rw [e]
    exact fetS_port_integral (F := fun ω => -(Gf E₀ ω * P * Gf E₀ ω)) ((hGPG0 P).neg) j
  · have := fetS_phys_integral (F := Gf E₀) hGi0 i
    simp only [hGb, hGf, hXE0] at this ⊢
    exact this.symm
  · have := fetS_port_integral (F := Gf E₀) hGi0 i
    simp only [hGb, hGf, hXE0] at this ⊢
    exact this.symm
  · have h := hidE E₀ h0
    have hb := fetS_resid_base (ν := μ) hb0 hb1 (Gf E₀) (B := Cc1 / (W : ℝ) ^ 2)
      (fun P' Q' hP' hQ' => hcov1 W hW hW4 .separate (Xf E₀) (hXh E₀) E₀ (boundaryZ b E₀)
        (hnear E₀ h0).1 (hnear E₀ h0).2.1 P' Q' hP' hQ')
    have hR := fetS_resid_eq (Gf E₀) hGi0 (hint E₀ h0).2.2 (1 - 2 * (b : ℂ)) b
    rw [show Rform E₀ = meqResid μ (1 - 2 * (b : ℂ)) b (Gf E₀) from hR.symm]
    refine hb.trans ?_
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  · refine hRdn.trans ?_
    have hu : 0 ≤ (1 + fetClock b E₀ X S) / W := by
      have : 0 ≤ fetClock b E₀ X S := by
        unfold fetClock clkTrace
        exact mul_nonneg (by positivity) ((norm_nonneg _).trans (dcv_norm_le_trace
          (dcv_Y_posSemidef hS)))
      positivity
    calc 10 * (max Ce 0 * (1 + fetClock b E₀ X S) / W) = 10 * max Ce 0 *
          ((1 + fetClock b E₀ X S) / W) := by ring
      _ ≤ max (10 * Cc1) (10 * max Ce 0) * ((1 + fetClock b E₀ X S) / W) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hu
      _ = _ := by ring
  · have h := hidE E₀ h0
    rw [fetSShift_apply] at h
    simpa only [hXE0] using h
  · rw [fetSShift_apply, fetSShift_apply] at huniq
    simpa only [hXE0] using huniq

end Analytic

/-!
## 7. Assembly: `FetStepMean`
-/

section Assembly

/-- The final error arithmetic. -/
theorem fetS_final_arith {Qm b A₁ BU Kc Cc Ca er r₀ r₁ u δ W : ℝ} (hQm : 0 ≤ Qm) (hb : 0 ≤ b)
    (hA₁ : 0 ≤ A₁) (hBU : 0 ≤ BU) (hKc : 0 ≤ Kc) (hCc : 0 ≤ Cc) (hCa : 0 ≤ Ca) (hu : 0 ≤ u)
    (hδ : 0 ≤ δ) (hW : 1 ≤ W) (her : er ≤ Cc * δ + Cc / W ^ 2) (hr₀ : r₀ ≤ Ca / W ^ 2)
    (hr₁ : r₁ ≤ Ca * (1 + u) / W) :
    (Qm * b + 3) * (A₁ * (3 * er) + 2 * r₁) + (BU * r₁ + Kc * (er + r₀) * u + Kc * (er + r₀)) +
        4 * A₁ * (Kc * (er + r₀)) ≤
      ((Qm * b + 3) * (3 * A₁ * Cc + 2 * Ca) + BU * Ca + Kc * (Cc + Ca) +
        4 * A₁ * Kc * (Cc + Ca)) * (1 + u) * (δ + 1 / W) := by
  have hW0 : 0 < W := by linarith
  have hx0 : 0 ≤ δ + 1 / W := by positivity
  have hW2 : 1 / W ^ 2 ≤ 1 / W := by
    rw [div_le_div_iff₀ (by positivity) hW0]; nlinarith
  have her' : er ≤ Cc * (δ + 1 / W) := by
    have : Cc / W ^ 2 ≤ Cc * (1 / W) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hW2 hCc
    nlinarith
  have hr₀' : r₀ ≤ Ca * (δ + 1 / W) := by
    have : Ca / W ^ 2 ≤ Ca * (1 / W) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hW2 hCa
    nlinarith [mul_nonneg hCa hδ]
  have hr₁' : r₁ ≤ Ca * (1 + u) * (δ + 1 / W) := by
    have : Ca * (1 + u) / W ≤ Ca * (1 + u) * (δ + 1 / W) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  set x := δ + 1 / W with hx
  set U := 1 + u with hU
  have hU1 : 1 ≤ U := by linarith
  have hsum : er + r₀ ≤ (Cc + Ca) * x := by nlinarith
  have t1 : (Qm * b + 3) * (A₁ * (3 * er) + 2 * r₁) ≤ (Qm * b + 3) * (3 * A₁ * Cc + 2 * Ca) * U * x := by
    have h1 : A₁ * (3 * er) ≤ 3 * A₁ * Cc * x * U := by
      have := mul_le_mul_of_nonneg_left her' (by positivity : 0 ≤ 3 * A₁)
      have h2 : 0 ≤ 3 * A₁ * Cc * x := by positivity
      nlinarith
    have h3 : 2 * r₁ ≤ 2 * Ca * U * x := by nlinarith
    have h4 : A₁ * (3 * er) + 2 * r₁ ≤ (3 * A₁ * Cc + 2 * Ca) * U * x := by nlinarith
    calc (Qm * b + 3) * (A₁ * (3 * er) + 2 * r₁) ≤ (Qm * b + 3) * ((3 * A₁ * Cc + 2 * Ca) * U * x) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
  have t2 : BU * r₁ ≤ BU * Ca * U * x := by
    have := mul_le_mul_of_nonneg_left hr₁' hBU; linarith [show BU * (Ca * U * x) = BU * Ca * U * x by ring]
  have t3 : Kc * (er + r₀) * u + Kc * (er + r₀) ≤ Kc * (Cc + Ca) * U * x := by
    have h1 : Kc * (er + r₀) ≤ Kc * ((Cc + Ca) * x) := mul_le_mul_of_nonneg_left hsum hKc
    have e : Kc * (er + r₀) * u + Kc * (er + r₀) = Kc * (er + r₀) * U := by rw [hU]; ring
    rw [e]
    calc Kc * (er + r₀) * U ≤ Kc * ((Cc + Ca) * x) * U := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = _ := by ring
  have t4 : 4 * A₁ * (Kc * (er + r₀)) ≤ 4 * A₁ * Kc * (Cc + Ca) * U * x := by
    have h1 : 4 * A₁ * (Kc * (er + r₀)) ≤ 4 * A₁ * (Kc * ((Cc + Ca) * x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hKc) (by positivity)
    have h2 : 0 ≤ 4 * A₁ * Kc * (Cc + Ca) * x := by positivity
    nlinarith
  calc _ ≤ (Qm * b + 3) * (3 * A₁ * Cc + 2 * Ca) * U * x + (BU * Ca * U * x +
        Kc * (Cc + Ca) * U * x) + 4 * A₁ * Kc * (Cc + Ca) * U * x := by linarith
    _ = _ := by ring

/-- The choice of the radius `d_*` and of the width threshold (real arithmetic only). -/
theorem fetS_small {b t ι Qm Kc Cc Ca : ℝ} (hb0 : 0 < b) (hι : 0 < ι) (hg : 0 < 1 - b - t)
    (hQm0 : 0 ≤ Qm) (hKc0 : 0 ≤ Kc) (hCc0 : 0 ≤ Cc) (hCa0 : 0 ≤ Ca) :
    ∃ dstar N : ℝ, 0 < dstar ∧ dstar ≤ 1 ∧ ∀ δ W : ℝ, 0 ≤ δ → δ ≤ dstar → 1 ≤ W → N ≤ W →
      Cc * δ + Cc / W ^ 2 ≤ ι / 2 ∧ Cc * δ + Cc / W ^ 2 ≤ 1 / 4 ∧ Ca / W ^ 2 ≤ 1 ∧
      Qm * b ^ 2 * (3 * (Cc * δ + Cc / W ^ 2)) +
          Kc * ((Cc * δ + Cc / W ^ 2) + Ca / W ^ 2) * (2 + 4 * b) ≤ (1 - b - t) / 4 ∧
      b * (3 * (Cc * δ + Cc / W ^ 2)) ≤ (1 - b - t) / 4 := by
  set g := 1 - b - t with hgdef
  set Dn := 3 * Qm * b ^ 2 + 2 * Kc * (2 + 4 * b) + 3 * b + 1 with hDn
  have hDn0 : 0 < Dn := by positivity
  set εs := min (min (ι / 2) (1 / 4)) (g / (4 * Dn)) with hεs
  have hεs0 : 0 < εs := by positivity
  have hεs1 : εs ≤ ι / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hεs2 : εs ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hεsD : εs * Dn ≤ g / 4 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Dn)).mp (min_le_right _ _ : εs ≤ _)
    linarith
  refine ⟨min 1 (εs / (2 * (Cc + 1))), (2 * Cc + Ca + 1) / εs, by positivity, min_le_left _ _,
    fun δ W hδ hδd hW hWN => ?_⟩
  have hW0 : 0 < W := by linarith
  have hWe : 2 * Cc + Ca + 1 ≤ εs * W := by
    have := (div_le_iff₀ hεs0).mp hWN; linarith
  have hW2 : W ≤ W ^ 2 := by nlinarith
  have hCcW : Cc / W ^ 2 ≤ εs / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hW2 hεs0.le]
  have hCaW : Ca / W ^ 2 ≤ εs := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hW2 hεs0.le]
  have hd2 : δ ≤ εs / (2 * (Cc + 1)) := hδd.trans (min_le_right _ _)
  have hCd : Cc * δ ≤ εs / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hd2 hCc0
    have h2 : Cc * (εs / (2 * (Cc + 1))) ≤ εs / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have her : Cc * δ + Cc / W ^ 2 ≤ εs := by linarith
  have her0 : 0 ≤ Cc * δ + Cc / W ^ 2 := by positivity
  refine ⟨her.trans hεs1, her.trans hεs2, hCaW.trans (hεs2.trans (by norm_num)), ?_, ?_⟩
  · have h1 : Qm * b ^ 2 * (3 * (Cc * δ + Cc / W ^ 2)) ≤ Qm * b ^ 2 * (3 * εs) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : Kc * ((Cc * δ + Cc / W ^ 2) + Ca / W ^ 2) * (2 + 4 * b) ≤
        Kc * (2 * εs) * (2 + 4 * b) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hKc0) (by positivity)
    have h3 : Qm * b ^ 2 * (3 * εs) + Kc * (2 * εs) * (2 + 4 * b) ≤ εs * Dn := by
      rw [hDn]; nlinarith [mul_nonneg hεs0.le hb0.le]
    linarith
  · have h1 : b * (3 * (Cc * δ + Cc / W ^ 2)) ≤ b * (3 * εs) :=
      mul_le_mul_of_nonneg_left (by linarith) hb0.le
    have h3 : b * (3 * εs) ≤ εs * Dn := by
      rw [hDn]; nlinarith [mul_nonneg hQm0 (sq_nonneg b), mul_nonneg hεs0.le
        (mul_nonneg hQm0 (sq_nonneg b)), mul_nonneg hεs0.le hKc0, mul_nonneg hεs0.le
        (mul_nonneg hKc0 hb0.le)]
    linarith

/-- The comparison means: `|ḡ - a| ≤ C δ + C/W²`. -/
theorem fetS_means_close {W : ℕ} {b E : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {Gb : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ} {Cc0 : ℝ} {m u : Fin 2 → ℂ}
    (hδ0 : 0 ≤ matchedDistance b E X)
    (hphysI : ∀ i, physBlockTrace Gb i = ∫ ω, physBlockTrace
        (layerResolvent .separate E (boundaryZ b E) X ω) i ∂layerLaw W b .separate)
    (hportI : ∀ i, portBlockTrace Gb i = ∫ ω, portBlockTrace
        (layerResolvent .separate E (boundaryZ b E) X ω) i ∂layerLaw W b .separate)
    (hmu : ∀ i, ‖m i - matchedA E‖ + ‖u i - matchedA E‖ ≤ Cc0 * matchedDistance b E X)
    (hmeans : ∀ i : Fin 2,
      ‖(∫ ω, physBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) i
          ∂layerLaw W b .separate) - m i‖ ≤ Cc0 / (W : ℝ) ^ 2 ∧
      ‖(∫ ω, portBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) i
          ∂layerLaw W b .separate) - u i‖ ≤ Cc0 / (W : ℝ) ^ 2) :
    ∀ i, ‖physBlockTrace Gb i - matchedA E‖ ≤
        max Cc0 0 * matchedDistance b E X + max Cc0 0 / (W : ℝ) ^ 2 ∧
      ‖portBlockTrace Gb i - matchedA E‖ ≤
        max Cc0 0 * matchedDistance b E X + max Cc0 0 / (W : ℝ) ^ 2 := fun i => by
  have h1 := (hmeans i).1
  have h2 := (hmeans i).2
  have h3 := hmu i
  have hm0 := norm_nonneg (m i - matchedA E)
  have hu0 := norm_nonneg (u i - matchedA E)
  have k1 : Cc0 * matchedDistance b E X ≤ max Cc0 0 * matchedDistance b E X :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
  have k2 : Cc0 / (W : ℝ) ^ 2 ≤ max Cc0 0 / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  rw [hphysI i, hportI i]
  exact ⟨(norm_sub_le_norm_sub_add_norm_sub _ (m i) _).trans (by linarith),
    (norm_sub_le_norm_sub_add_norm_sub _ (u i) _).trans (by linarith)⟩

theorem fetS_rowSum_le {s Crs δ : ℝ} {b : ℝ} (h : s ≤ (1 - b)⁻¹ + Crs * δ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) : s ≤ (1 - b)⁻¹ + max Crs 0 := by
  have : Crs * δ ≤ max Crs 0 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0).trans
      (by have := mul_le_mul_of_nonneg_left hδ1 (le_max_right Crs 0); linarith)
  linarith

set_option maxHeartbeats 400000 in
/-- **`FetStepMean`** — the energy paragraph of the tagged-trace lemma, one
separate-port step, conditional mean.

*Law.* The fresh layer `layerLaw W b .separate` (`A_a ~ GUE_W(c/W)`, `c = 1 - 2b`, bonds
`Gin(b/W)`), conditional on the old input: `X` Hermitian and `S ⪰ 0` are deterministic.

*Domain and objects.* `b ∈ (0, 1/2)`, `E ∈ bulkInterval κ`, `z = z_∂(E)`, `a = matchedA E`,
`a' = tgtAd E`; `ġ_j = fetGd b E X S ℓ j = -W⁻¹ Tr Q_j 𝒢 P 𝒢`, `P = -Ŝ + diag(-I, z_∂' I)` (the
a.s. energy derivative of the outgoing port trace along any Hermitian family with `X'(E) = S`);
`d = fetDist b E X S` (`max_i |W⁻¹ Tr[R(S - z_∂')R]_{ii} - a'|`, `R = (z - X)⁻¹`),
`u = fetClock b E X S = W⁻¹ Re Tr R* S R`, `δ = matchedDistance b E X`.

*Norms.* Complex modulus of the Bochner mean `E ġ_j` (in the proof: `ℓ²` operator norms of
matrices).

*Quantifiers and uniformity.* `b, κ` first; then `d_* > 0`, `q ∈ [0, 1)`, `C ≥ 0`, `W₀`; then
uniformly in `W ≥ W₀`, every Hermitian `X` (no norm bound), `S ⪰ 0`, `E ∈ bulkInterval κ`, `j`,
on `δ ≤ d_*`: `|E ġ_j - a'| ≤ q d + C(1 + u)(δ + 1/W)`. No limits are taken.

*Proof.* The exact mean identity of the layer `(𝒟 - 𝒮(ḡ))Ḡ = I + Res` holds at every energy near
`E` along the linear family `X + (E' - E)S`; it is differentiated (`fetS_analytic`: `∂_E Ḡ =
E[-𝒢P𝒢]` by dominated convergence, `∂_E Res` from the differentiated-covariance lemma, energy
clause, `‖∂_E Res‖ ≤ C(1+u)/W`, `‖Res‖ ≤ C/W²` from the trace–matrix lemma). The port rows give
`ḡ'_P = κ(bḡ'_A - z_∂') + r`, `κ ≈ a²`; the physical rows, compared with `R` through the clock
pairing `|W⁻¹ Tr(A S B)| ≤ ‖KB‖‖AK*‖u` (`R` normal), give
`ḡ'_A = f' + Q(1 + z_∂' + cḡ'_A + bḡ'_P) + e`; the constants cancel by `1 + (1-b)a' + z_∂' = 0`
and the strict-contraction margin closes the linear system (`fetS_scalar`, `fetS_det`). -/
theorem fetStepMean_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) : FetStepMean := by
  intro b hb0 hb1 κ hκ
  obtain ⟨Ca, Wa, hCa0, han⟩ := fetS_analytic hcount hgrad hb0 hb1 hκ
  obtain ⟨dc, Cc0, Wc, hdc, hcomp⟩ := layerComparison_holds hcount b hb0 hb1 κ hκ
  obtain ⟨dm, t, hdm, ht, hmarg⟩ := strictContraction_holds.margin b hb0 hb1 κ hκ
  obtain ⟨Crs, hrs⟩ := strictContraction_holds.rowSum b hb0 hb1 κ hκ
  obtain ⟨A₁, ι, hA₁0, hι, hsc⟩ := fetS_scal_bounds hb0.le hκ
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ
  have hCc0 : 0 ≤ max Cc0 0 := le_max_right _ _
  have h1b : 0 < 1 - b := by linarith
  have hQm0 : 0 ≤ (1 - b)⁻¹ + max Crs 0 := by positivity
  have hKc0 : 0 ≤ fetSKc b ι η₀ := by unfold fetSKc; positivity
  have hBU0 : 0 ≤ fetSBU b ι := by unfold fetSBU; positivity
  obtain ⟨ds, N, hds0, hds1, hsmall⟩ := fetS_small (t := t) hb0 hι (by linarith) hQm0 hKc0 hCc0
    hCa0
  have hq0 : 0 ≤ (b + (1 - b - t) / 4) / (b + 3 * (1 - b - t) / 4) := by
    have : 0 < 1 - b - t := by linarith
    positivity
  have hq1 : (b + (1 - b - t) / 4) / (b + 3 * (1 - b - t) / 4) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  refine ⟨min (min dc dm) ds, (b + (1 - b - t) / 4) / (b + 3 * (1 - b - t) / 4),
    (((1 - b)⁻¹ + max Crs 0) * b + 3) * (3 * A₁ * max Cc0 0 + 2 * Ca) +
      fetSBU b ι * Ca + fetSKc b ι η₀ * (max Cc0 0 + Ca) +
      4 * A₁ * fetSKc b ι η₀ * (max Cc0 0 + Ca), max (max Wa Wc) (max 1 ⌈N⌉₊),
    lt_min (lt_min hdc hdm) hds0, hq0, hq1, by positivity, ?_⟩
  intro W hW hWW X S hX hS E hE hd j
  have hWa : Wa ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWW
  have hWc : Wc ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWW
  have hW1 : (1 : ℝ) ≤ W := by
    exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hWW
  have hWN : N ≤ W := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hWW)
  have hE2 : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  have hdc' : matchedDistance b E X ≤ dc := hd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdm' : matchedDistance b E X ≤ dm := hd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hds' : matchedDistance b E X ≤ ds := hd.trans (min_le_right _ _)
  have hδ0 : 0 ≤ matchedDistance b E X := clk_matchedDistance_nonneg b E X
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hsmall _ _ hδ0 hds' hW1 hWN
  obtain ⟨Gb, Gd, Res, Res', -, hint, hphysI, hportI, hRes, hRes', hid, hdid⟩ :=
    han W hW hWa X S hX hS E hE
  obtain ⟨⟨m, u, -, -, hmu, hmeans⟩, -⟩ := hcomp W hW hWc X hX E hE hdc'
  have her' := fetS_means_close hδ0 (W := W) hphysI hportI hmu hmeans
  have hu0 : 0 ≤ fetClock b E X S := by
    unfold fetClock clkTrace
    exact mul_nonneg (by positivity) ((norm_nonneg _).trans (dcv_norm_le_trace
      (dcv_Y_posSemidef hS)))
  have hRes'0 : 0 ≤ Ca * (1 + fetClock b E X S) / W := (norm_nonneg _).trans hRes'
  have hQmb : ∀ i, ∑ k, ‖blockPairTrace (fetR b E X) i k‖ ≤ (1 - b)⁻¹ + max Crs 0 := fun i =>
    fetS_rowSum_le (hrs W hW X hX E hE i) hδ0 (hd.trans ((min_le_right _ _).trans hds1))
  have hdet := fetS_det hb0 hb1 hE2 hX hS Gb Gd Res Res' hid hdid her' hRes hRes' hι
    (hsc E hE).2.2 hη₀ (hbulk E hE).1 (hmarg W hW X hX E hE hdm') hQmb hQm0 ht (hsc E hE).1
    (hsc E hE).2.1 (by positivity) (by positivity) hRes'0 hs1 hs2 hs3 hs4 hs5 j
  rw [hint j]
  refine hdet.trans ?_
  have hfa := fetS_final_arith (Qm := (1 - b)⁻¹ + max Crs 0) (b := b) (A₁ := A₁)
    (BU := fetSBU b ι) (Kc := fetSKc b ι η₀) (Cc := max Cc0 0) (Ca := Ca)
    (er := max Cc0 0 * matchedDistance b E X + max Cc0 0 / (W : ℝ) ^ 2)
    (r₀ := Ca / (W : ℝ) ^ 2) (r₁ := Ca * (1 + fetClock b E X S) / W)
    (u := fetClock b E X S) (δ := matchedDistance b E X) (W := W) hQm0 hb0.le hA₁0 hBU0 hKc0
    hCc0 hCa0 hu0 hδ0 hW1 le_rfl le_rfl le_rfl
  exact add_le_add le_rfl hfa

end Assembly

end BlockBand.Layers

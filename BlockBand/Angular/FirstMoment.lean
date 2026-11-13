module

public import BlockBand.Angular.FirstMomentTransport

/-!
# The angular first moment on a good domain

* `zdet` — the generic determinant factor `𝔷(v) = E_{G}[|det(U_v*FU_v + G - E)|² 1{N_- + n₀ = a}]`
  (`detFactor_eq_zdet`: the pair `detFactor` of `FiberAngular` is `zdet` with
  `n₀ = N_R(E)`, `a = α`).
* `freshEigenpairFiber_reindex` — the fresh eigenpair fiber of the reindexed deformation, tested
  against a function of `v`, is `∫ ν(dv) c_{N,t} 𝓡(E,v,F) 𝔷(v) g(v)` on the original index set,
  in the rank `ℓ = a - n₀`.
* `angular_first_moment` — the generic statement (any index type `ι`, `N = |ι|`, frame index
  `Fin (N-1)`, crossing factor `κ_c ≥ 0`).
* `pair_angular_first_moment` — the pair form for the angular measure
  `ν_E(dv) = c_{2W,t}(n/2) exp(expo v) 𝔷_E(v) ν_{2W}(dv)` of `FiberAngular`.

Normalization. In the fresh eigenpair density, `Z = E w` is the unnormalized eigenpair
density at `E` in rank `ℓ` *without* the crossing factor; the angular measure under the
size-biased pair law carries the extra factor `n/2` (`angularWeight`), so its mass is
`Z_ang = (n/2) Z`. The fresh Palm theorem at order one gives, uniformly in `N, F, E, ℓ, q`,
`E[w|√N q*u|²] ≤ (1+|C₁|)(Z + |C₁C_{1,K}|N^{-K}) q*Γq`, hence
`∫|w*v|² dν ≤ C₀ (Z_ang + (n/2)C_K N^{-K}) w*Γw / N`, `C₀ = 1 + |C₁|`, `C_K = |C₁C_{1,K}|`.
The remainder is `r = (n/2) C_K N^{-K}`; with `n ≤ TW` the factor `n/2 ≤ T N/4` is absorbed
by taking `K + 1` for `K`. If the inertia constraint has no admissible fresh rank
(`a < n₀` or `a - n₀ ≥ N`) the measure vanishes and the bound is trivial.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.FirstMoment

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.QUE.Fourier BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Stein BlockBand.Angular.ConeDivergence
open BlockBand.Angular.FiberAngular BlockBand.Angular.Stein.AngularData
open BlockBand.Angular.PairCoareaBridge BlockBand.Model
open scoped ENNReal NNReal ComplexConjugate

/-!
## The generic determinant factor
-/

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `𝔷(v) = E_{G ~ GUE_m(t)}[|det(U_v*FU_v + G - E)|² 1{N_-(·) + n₀ = a}]`. -/
def zdet {m : ℕ} (U : (ι → ℂ) → Matrix ι (Fin m) ℂ) (F : Matrix ι ι ℂ) (t : ℝ≥0) (E : ℝ)
    (n₀ a : ℕ) (v : ι → ℂ) : ℝ≥0∞ :=
  ∫⁻ G', ENNReal.ofReal (Complex.normSq ((U v)ᴴ * F * U v + G' - (E : ℂ) • 1).det) *
      (if negativeCount ((U v)ᴴ * F * U v + G' - (E : ℂ) • 1) + n₀ = a then 1 else 0)
    ∂(gueMeasure (Fin m) t)

theorem negativeCount_le_card {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ) :
    negativeCount M ≤ Fintype.card κ := by
  classical
  unfold negativeCount
  split_ifs
  · exact (Finset.card_filter_le _ _).trans (Finset.card_univ).le
  · exact Nat.zero_le _

/-- With no admissible rank (`ℓ + n₀ = a` has no solution `ℓ ≤ m`) the factor vanishes. -/
theorem zdet_eq_zero {m : ℕ} (U : (ι → ℂ) → Matrix ι (Fin m) ℂ) (F : Matrix ι ι ℂ) (t : ℝ≥0)
    (E : ℝ) {n₀ a : ℕ} (h : ∀ ℓ : ℕ, ℓ ≤ m → ℓ + n₀ ≠ a) (v : ι → ℂ) :
    zdet U F t E n₀ a v = 0 := by
  unfold zdet
  have : ∀ G' : Matrix (Fin m) (Fin m) ℂ,
      ENNReal.ofReal (Complex.normSq ((U v)ᴴ * F * U v + G' - (E : ℂ) • 1).det) *
        (if negativeCount ((U v)ᴴ * F * U v + G' - (E : ℂ) • 1) + n₀ = a then 1 else 0) = 0 := by
    intro G'
    have hle := negativeCount_le_card ((U v)ᴴ * F * U v + G' - (E : ℂ) • 1)
    rw [Fintype.card_fin] at hle
    simp only [h _ hle, ↓reduceIte, mul_zero]
  simp only [this, lintegral_zero]

theorem coareaConstant_nonneg (d : ℕ) (t : ℝ≥0) : 0 ≤ coareaConstant d t := by
  unfold coareaConstant
  positivity

theorem regressionFactor_pos {κ : Type} [Fintype κ] (t E : ℝ) (v : κ → ℂ) (F : Matrix κ κ ℂ) :
    0 < regressionFactor t E v F := Real.exp_pos _

/-- **The fresh eigenpair fiber in original coordinates.** For `e : ι ≃ Fin N`, a frame `U` of
`v^⊥ ⊂ ℂ^ι` with frame index `Fin (N-1)`, rank `ℓ` with `ℓ + n₀ = a`, and a finite test
function `g` of the direction, the fresh eigenpair density (`freshEigenpairFiber`) of the
reindexed deformation tested against `g(v' ∘ e)` is `∫ ν_ι(dv) c_{N,t} 𝓡(E,v,F) 𝔷(v) g(v)`. -/
theorem freshEigenpairFiber_reindex {N : ℕ} (e : ι ≃ Fin N)
    (U : (ι → ℂ) → Matrix ι (Fin (N - 1)) ℂ) (F : Matrix ι ι ℂ) (t : ℝ≥0) (E : ℝ) (ℓ : Fin N)
    {n₀ a : ℕ} (hℓ : ℓ.val + n₀ = a) (g : (ι → ℂ) → ℝ≥0∞) (hg : ∀ v, g v ≠ ∞) :
    freshEigenpairFiber (F.submatrix e.symm e.symm) t ℓ (reindexFrame e U) E
        (fun v' _ => g (v' ∘ e)) =
      ∫⁻ v, ENNReal.ofReal (coareaConstant N t * regressionFactor t E v F) *
          zdet U F t E n₀ a v * g v ∂projectiveHaar ι := by
  unfold freshEigenpairFiber
  rw [lintegral_projectiveHaar_reindex e]
  refine lintegral_congr fun v => ?_
  have hv : (v ∘ e.symm) ∘ e = v := by funext b; simp
  simp only [freshFrameM, compress_reindex, regressionFactor_reindex, hv]
  unfold zdet
  have hcR : 0 ≤ coareaConstant N t * regressionFactor t E v F :=
    mul_nonneg (coareaConstant_nonneg N t) (regressionFactor_pos _ _ _ _).le
  conv_rhs => rw [mul_right_comm]
  rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hg v))]
  refine lintegral_congr fun G' => ?_
  rw [ENNReal.ofReal_mul hcR]
  have hi : negativeCount ((U v)ᴴ * F * U v + G' - (E : ℂ) • 1) = ℓ.val ↔
      negativeCount ((U v)ᴴ * F * U v + G' - (E : ℂ) • 1) + n₀ = a := by omega
  rw [if_congr hi rfl rfl]
  ring

/-- `Re(q*(uu*)q) = |q*u|²`. -/
theorem re_dotProduct_vecMulVec {κ : Type} [Fintype κ] (q u : κ → ℂ) :
    (star q ⬝ᵥ (vecMulVec u (star u) *ᵥ q)).re = ‖star q ⬝ᵥ u‖ ^ 2 := by
  have h1 : vecMulVec u (star u) *ᵥ q = (star u ⬝ᵥ q) • u := by
    ext x
    simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]
  have h2 : star u ⬝ᵥ q = conj (star q ⬝ᵥ u) := by
    simp [dotProduct, map_sum, mul_comm]
  rw [h1, dotProduct_smul, smul_eq_mul, h2, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re]

theorem measurable_palmWeight {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N) :
    Measurable (fun A0 => palmWeight F c₀ E ℓ A0) := by
  unfold palmWeight BlockBand.Palm.scalarWeight freshEigenvalue
  exact (measurable_gaussianPDFReal _ _).comp (measurable_const.sub
    ((measurable_rawIncreasingEigenvalue _).comp (measurable_id.const_add F)))

theorem measurable_palmOverlap {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ)
    (ℓ : Fin N) : Measurable (fun A0 => palmOverlap F q ℓ A0) := by
  unfold palmOverlap freshEigenvector
  refine measurable_const.mul ((Measurable.norm ?_).pow_const 2)
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun x _ => measurable_const.mul
    ((measurable_rawOrderedColumnSelection _ x).comp (measurable_id.const_add F))

theorem palmWeight_nonneg {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ palmWeight F c₀ E ℓ A0 := by
  unfold palmWeight BlockBand.Palm.scalarWeight
  exact gaussianPDFReal_nonneg _ _ _

theorem palmOverlap_nonneg {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ palmOverlap F q ℓ A0 := by
  unfold palmOverlap
  positivity

/-- The order-one fresh Palm bound in the form used: from
`|M - γZ| ≤ C(xZ + C' y)γ` with `0 ≤ x ≤ 1` one gets `M ≤ (1+|C|)(Z + |CC'|y)γ`. -/
theorem first_moment_arith {M Z γ Cr CrK x y : ℝ} (hZ : 0 ≤ Z) (hγ : 0 ≤ γ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (hy : 0 ≤ y) (h : |M - γ * Z| ≤ Cr * (x * Z + CrK * y) * γ) :
    M ≤ (1 + |Cr|) * (Z + |Cr * CrK| * y) * γ := by
  have h1 := (le_abs_self _).trans h
  have hx : Cr * x ≤ |Cr| :=
    (mul_le_mul_of_nonneg_right (le_abs_self Cr) hx0).trans
      (mul_le_of_le_one_right (abs_nonneg _) hx1)
  have h2 : Cr * x * Z * γ ≤ |Cr| * Z * γ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx hZ) hγ
  have h3 : Cr * CrK * y * γ ≤ |Cr * CrK| * y * γ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hy) hγ
  have h4 : 0 ≤ |Cr| * (|Cr * CrK| * y) * γ := by positivity
  nlinarith [h1, h2, h3, h4]

/-!
## The first moment from the fresh Palm theorem at order one
-/

/-- Fix fresh constants
`FreshConstants c₀ r₀ s₀ v₀` and the norm exponent `A`.
Then there is `C₀ ≥ 1`, and for every
`K > 0` a `C_K ≥ 0`, such that uniformly in: the index set `ι` (`N = |ι| ≥ 1`), a measurable
orthonormal frame `U_v` of `v^⊥` (frame index `Fin (N-1)`), a deterministic deformation `F`
on `ℂ^ι` whose reindexing is in the fresh class at `(c₀, E)` (`‖F‖ ≤ N^A` and
), angular data `D` with `s = c₀`, `K₀ = F - E` and
`ζ = c₀ m_{c₀}(E)` (so that `D.Γ` is the fresh `Γ`, `freshGamma_reindex_eq`), inertia data
`n₀, a` (the fresh rank is `ℓ = a - n₀`), a crossing factor `κ_c ≥ 0` and any measurable
`Zf ≥ 0` with `Zf = κ_c c_{N,t} 𝔷` `ν_N`-a.e.
(`t = c₀/N`): for every `w`,
`∫ e^{expo} Zf |w*v|² dν_N ≤ C₀ (∫ e^{expo} Zf dν_N + κ_c C_K N^{-K}) / N · Re(w*Γw)`.
This is hypothesis `hFM` of `Angular.Ratio.angular_ratio` with `r = κ_c C_K N^{-K}`.
`C₀ = 1 + |C₁|`, `C_K = |C₁ C_{1,K}|` with the order-one constants of.
-/
theorem angular_first_moment (hP : FreshPalmContract) (hD : FreshEigenpairDensityContract)
    {A c₀ r₀ s₀ v₀ : ℝ} (hc : FreshConstants c₀ r₀ s₀ v₀) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ K : ℝ, 0 < K → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (m : ℕ),
        m = Fintype.card ι - 1 →
      ∀ U : (ι → ℂ) → Matrix ι (Fin m) ℂ, Measurable U →
        (∀ v : ι → ℂ, l2Norm v = 1 → (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0) →
      ∀ (D : AngularData ι) (F : Matrix ι ι ℂ) (E : ℝ), D.s = c₀ → D.K = F - (E : ℂ) • 1 →
        FreshClass (Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) F)
          A c₀ E r₀ s₀ v₀ →
        D.ζ = (c₀ : ℂ) *
          freshDyson (Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) F) c₀ E →
      ∀ (n₀ a : ℕ) (κc : ℝ), 0 ≤ κc →
      ∀ Zf : (ι → ℂ) → ℝ, Measurable Zf → (∀ v, 0 ≤ Zf v) →
        (∀ᵐ v ∂projectiveHaar ι, ENNReal.ofReal (Zf v) =
          ENNReal.ofReal (κc * coareaConstant (Fintype.card ι)
              (Real.toNNReal (c₀ / Fintype.card ι))) *
            zdet U F (Real.toNNReal (c₀ / Fintype.card ι)) E n₀ a v) →
      ∀ w : ι → ℂ,
        ∫ v, Real.exp (D.expo v) * Zf v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar ι ≤
          C₀ * ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι) +
              κc * CK * (Fintype.card ι : ℝ) ^ (-K)) / Fintype.card ι *
            (star w ⬝ᵥ (D.Γ *ᵥ w)).re := by
  obtain ⟨κ, hκ, Cr, hCr⟩ := hP A c₀ r₀ s₀ v₀ hc 1 le_rfl
  refine ⟨1 + |Cr|, by linarith [abs_nonneg Cr], fun K hK => ?_⟩
  obtain ⟨CrK, hCrK⟩ := hCr K hK
  refine ⟨|Cr * CrK|, abs_nonneg _, ?_⟩
  intro ι _ _ _ m hm U hUm hU D F E hDs hDK hcls hDζ n₀ a κc hκc Zf hZm hZ0 hZf w
  subst hm
  rw [Matrix.reindex_apply] at hcls hDζ
  have hN : 0 < (Fintype.card ι) := Fintype.card_pos
  have hNr : (0 : ℝ) < (Fintype.card ι) := by exact_mod_cast hN
  set e := Fintype.equivFin ι with he
  set t := Real.toNNReal (c₀ / (Fintype.card ι)) with ht
  have hc0 : 0 < c₀ := hc.1
  -- the two covariances coincide
  have hγ : quadForm (freshGamma (F.submatrix e.symm e.symm) c₀ E) (w ∘ e.symm) =
      (star w ⬝ᵥ (D.Γ *ᵥ w)).re := by
    rw [freshGamma_reindex_eq e F c₀ E D.hK hDK hDζ D.hz, quadForm_reindex, AngularData.Γ, hDs]
    rfl
  have hγ0 : 0 ≤ (star w ⬝ᵥ (D.Γ *ᵥ w)).re := by
    show 0 ≤ quadNum D.Γ w
    rw [D.Γ_eq, quadNum_real_smul, ← reInner_mulVec, ← normSqSum_eq_reInner]
    exact mul_nonneg D.hs.le (by unfold normSqSum; positivity)
  have hmeasDot : Measurable (fun v : ι → ℂ => ‖star w ⬝ᵥ v‖ ^ 2) :=
    (Measurable.norm (Finset.measurable_sum _ fun x _ => measurable_const.mul
      (measurable_pi_apply x) : Measurable fun v : ι → ℂ => ∑ x, star w x * v x)).pow_const 2
  have hρm : Measurable (fun v => Real.exp (D.expo v) * Zf v) :=
    (Real.measurable_exp.comp D.expo_meas).mul hZm
  have hρ0 : ∀ v, 0 ≤ Real.exp (D.expo v) * Zf v := fun v =>
    mul_nonneg (Real.exp_pos _).le (hZ0 v)
  have hZang : 0 ≤ ∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι :=
    integral_nonneg hρ0
  have hy0 : 0 ≤ ((Fintype.card ι) : ℝ) ^ (-K) := Real.rpow_nonneg hNr.le _
  have hC₀ : 0 ≤ 1 + |Cr| := by linarith [abs_nonneg Cr]
  by_cases hℓ : ∃ ℓ : ℕ, ℓ ≤ (Fintype.card ι) - 1 ∧ ℓ + n₀ = a
  swap
  · -- no admissible fresh rank: the angular measure vanishes
    push Not at hℓ
    have hz : ∀ v, zdet U F t E n₀ a v = 0 := zdet_eq_zero U F t E (fun ℓ h1 => hℓ ℓ h1)
    have hZf0 : ∀ᵐ v ∂projectiveHaar ι, Zf v = 0 := by
      filter_upwards [hZf] with v hv
      rw [hz, mul_zero, ENNReal.ofReal_eq_zero] at hv
      exact le_antisymm hv (hZ0 v)
    have hL : ∫ v, Real.exp (D.expo v) * Zf v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar ι = 0 :=
      integral_eq_zero_of_ae (by filter_upwards [hZf0] with v hv; simp [hv])
    rw [hL]
    exact mul_nonneg (div_nonneg (mul_nonneg hC₀ (add_nonneg hZang
      (mul_nonneg (mul_nonneg hκc (abs_nonneg _)) hy0))) hNr.le) hγ0
  obtain ⟨ℓ, hℓN, hℓa⟩ := hℓ
  set L : Fin (Fintype.card ι) := ⟨ℓ, by omega⟩ with hL
  have hU' : IsFreshFrame (reindexFrame e U) := isFreshFrame_reindexFrame e hUm hU
  have hF' : (F.submatrix e.symm e.symm).IsHermitian := hcls.1
  have hF : F.IsHermitian := by
    have h := hF'.submatrix e
    rwa [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] at h
  set q := w ∘ e.symm with hq
  -- the angular integrands, as ℝ≥0∞ integrals on `ι`
  set cR : (ι → ℂ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (coareaConstant (Fintype.card ι) t * regressionFactor t E v F) *
      zdet U F t E n₀ a v with hcR
  set Iq := ∫⁻ v, cR v * ENNReal.ofReal (‖star w ⬝ᵥ v‖ ^ 2) ∂projectiveHaar ι with hIq
  set I1 := ∫⁻ v, cR v ∂projectiveHaar ι with hI1
  -- palm identities (`FreshEigenpairDensityContract.palm`) at `f = N Re(q*Pq)` and `f = 1`
  have hfq : Measurable (fun P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ =>
      ENNReal.ofReal (((Fintype.card ι) : ℝ) * (star q ⬝ᵥ (P *ᵥ q)).re)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Complex.measurable_re.comp
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)).measurable))
  have hPq := hD.palm (Fintype.card ι) hN (F.submatrix e.symm e.symm) hF' c₀ hc0 L
    (reindexFrame e U) hU' _ hfq E
  have hP1 := hD.palm (Fintype.card ι) hN (F.submatrix e.symm e.symm) hF' c₀ hc0 L
    (reindexFrame e U) hU' (fun _ => 1) measurable_const E
  have hfibq : freshEigenpairFiber (F.submatrix e.symm e.symm) t L (reindexFrame e U) E
      (fun v _ => ENNReal.ofReal (((Fintype.card ι) : ℝ) *
        (star q ⬝ᵥ (vecMulVec v (star v) *ᵥ q)).re)) =
      ENNReal.ofReal (Fintype.card ι) * Iq := by
    have hfun : (fun (v : Fin (Fintype.card ι) → ℂ)
        (_ : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) =>
        ENNReal.ofReal (((Fintype.card ι) : ℝ) * (star q ⬝ᵥ (vecMulVec v (star v) *ᵥ q)).re)) =
        fun v' _ => (fun v => ENNReal.ofReal (((Fintype.card ι) : ℝ) * ‖star w ⬝ᵥ v‖ ^ 2))
          (v' ∘ e) := by
      funext v' G
      rw [re_dotProduct_vecMulVec]
      have : v' = (v' ∘ e) ∘ e.symm := by funext b; simp
      rw [this, hq, star_comp, dotProduct_comp_symm, ← this]
    rw [hfun, freshEigenpairFiber_reindex e U F t E L (n₀ := n₀) (a := a) hℓa
      (fun v => ENNReal.ofReal (((Fintype.card ι) : ℝ) * ‖star w ⬝ᵥ v‖ ^ 2))
      (fun _ => ENNReal.ofReal_ne_top), hIq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun v => ?_
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp only [hcR]
    ring
  have hfib1 : freshEigenpairFiber (F.submatrix e.symm e.symm) t L (reindexFrame e U) E
      (fun v _ => (fun _ => 1) (vecMulVec v (star v))) = I1 := by
    have hfun : (fun (v : Fin (Fintype.card ι) → ℂ)
        (_ : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) =>
        (fun _ => (1 : ℝ≥0∞)) (vecMulVec v (star v))) =
        fun v' _ => (fun _ => (1 : ℝ≥0∞)) (v' ∘ e) := rfl
    rw [hfun, freshEigenpairFiber_reindex e U F t E L (n₀ := n₀) (a := a) hℓa
      (fun _ => (1 : ℝ≥0∞)) (fun _ => ENNReal.one_ne_top), hI1]
    simp only [mul_one, hcR]
  -- Bochner forms of the fresh moments
  have hMB : ∫ A0, palmWeight (F.submatrix e.symm e.symm) c₀ E L A0 *
      palmOverlap (F.submatrix e.symm e.symm) q L A0 ^ 1 ∂freshTracelessLaw (Fintype.card ι) c₀ =
      (ENNReal.ofReal (Fintype.card ι) * Iq).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun A0 =>
        mul_nonneg (palmWeight_nonneg _ _ _ _ _) (pow_nonneg (palmOverlap_nonneg _ _ _ _) 1))
      (((measurable_palmWeight (F.submatrix e.symm e.symm) c₀ E L).mul
        ((measurable_palmOverlap (F.submatrix e.symm e.symm) q L).pow_const
          1)).aestronglyMeasurable)]
    congr 1
    rw [← hfibq, ← hPq]
    refine lintegral_congr fun A0 => ?_
    rw [pow_one, ENNReal.ofReal_mul (palmWeight_nonneg _ _ _ _ _), re_dotProduct_vecMulVec]
    rfl
  have hZB : ∫ A0, palmWeight (F.submatrix e.symm e.symm) c₀ E L A0
      ∂freshTracelessLaw (Fintype.card ι) c₀ = I1.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun A0 => palmWeight_nonneg _ _ _ _ _)
      (measurable_palmWeight (F.submatrix e.symm e.symm) c₀ E L).aestronglyMeasurable]
    congr 1
    rw [← hfib1, ← hP1]
    simp only [mul_one]
  -- Bochner forms of the angular moments
  have hkey : ∀ᵐ v ∂projectiveHaar ι, ∀ x : ℝ, 0 ≤ x →
      ENNReal.ofReal (Real.exp (D.expo v) * Zf v * x) =
        ENNReal.ofReal κc * (cR v * ENNReal.ofReal x) := by
    filter_upwards [hZf, ae_projectiveHaar_unit] with v hv hu x hx
    have hl2 : l2Norm v = 1 := by rw [l2Norm, ← normSqSum, hu, Real.sqrt_one]
    have hR : regressionFactor t E v F = Real.exp (D.expo v) := by
      rw [ht, ← hDs]; exact regressionFactor_eq_exp_expo D E F hF hDK hl2
    rw [ENNReal.ofReal_mul (hρ0 v), ENNReal.ofReal_mul (Real.exp_pos _).le, hv,
      ENNReal.ofReal_mul hκc, hcR]
    simp only
    rw [hR, ENNReal.ofReal_mul (coareaConstant_nonneg (Fintype.card ι) t)]
    ring
  have hLB : ∫ v, Real.exp (D.expo v) * Zf v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar ι =
      (ENNReal.ofReal κc * Iq).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun v =>
        mul_nonneg (hρ0 v) (sq_nonneg _)) (hρm.mul hmeasDot).aestronglyMeasurable]
    congr 1
    rw [hIq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hkey] with v hv
    exact hv _ (sq_nonneg _)
  have hZA : ∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι =
      (ENNReal.ofReal κc * I1).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hρ0) hρm.aestronglyMeasurable]
    congr 1
    rw [hI1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hkey] with v hv
    have := hv 1 zero_le_one
    rwa [mul_one, ENNReal.ofReal_one, mul_one] at this
  -- the order-one fresh Palm bound
  have hcon := hCrK (Fintype.card ι) hN (F.submatrix e.symm e.symm) E hcls q L
  dsimp only at hcon
  rw [hMB, hZB, hγ, Nat.factorial_one, Nat.cast_one, one_mul, pow_one,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hNr.le] at hcon
  have hM := first_moment_arith ENNReal.toReal_nonneg hγ0 (Real.rpow_nonneg hNr.le _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (neg_nonpos.2 hκ.le)) hy0 hcon
  rw [hLB, hZA, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hκc]
  set iq := Iq.toReal
  set i1 := I1.toReal
  set γ := (star w ⬝ᵥ (D.Γ *ᵥ w)).re
  have hrw : (1 + |Cr|) * (κc * i1 + κc * |Cr * CrK| * ((Fintype.card ι) : ℝ) ^ (-K)) /
      (Fintype.card ι) * γ = κc * ((1 + |Cr|) * (i1 + |Cr * CrK| * ((Fintype.card ι) : ℝ) ^ (-K)) *
        γ) / (Fintype.card ι) := by ring
  rw [hrw, le_div_iff₀ hNr]
  nlinarith [mul_le_mul_of_nonneg_left hM hκc]

end Generic

/-!
## The pair form for the angular measure of `FiberAngular`
-/

section Pair

variable (p : Parameters) (i : ZMod p.n)

/-- The pair determinant factor is the generic `zdet` with `n₀ = N_R(E) = N_-(H_R - E)` and
`a = α` (zero-based rank; the fresh rank is `α - N_R(E)`). -/
theorem detFactor_eq_zdet (α : Fin p.N) (s : ℝ)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (ω : SplitState p i)
    (E : ℝ) (v : PairSite p i → ℂ) :
    detFactor p i α s U ω E v =
      zdet U (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) (pairTime p s) E
        (negativeCount (ω.1 - (E : ℂ) • 1)) α.val v := rfl

/-- Then there is `C₀ ≥ 1`, and for every `K > 0` a `C_K ≥ 0`, such that for every admissible
`p`, pair `i`, rank `α`, pair frame `U`, deterministic exterior data `ω = (H_R, C, V)` and energy
`E` on the good domain — `F(E)` (reindexed to `Fin (2W)`, `pairToFin`) in the fresh class at
`(c₀, E)`:
Hermitian, `‖F(E)‖ ≤ (2W)^A` and — and angular data `D` with
`s = c₀`, `K₀ = F(E) - E`, `ζ = c₀ m_{c₀}(E)`, every measurable `Zf ≥ 0` agreeing `ν`-a.e. with
the Step 1 density `c_{2W,t}(n/2) 𝔷_E` (`t = c₀/(2W)`, `𝔷 = detFactor`) satisfies, for every `w`,
`∫ e^{expo}Zf|w*v|² dν ≤ C₀(∫ e^{expo}Zf dν + (n/2) C_K N^{-K})/N · Re(w*Γw)`, `N = |S| = 2W`.
So the angular measure `ν_E = e^{expo} Zf ν_{2W}` of the size-biased pair law satisfies
 with `r = (n/2) C_K N^{-K}` (`hFM` of `angular_ratio`).
-/
theorem pair_angular_first_moment (hP : FreshPalmContract) (hD : FreshEigenpairDensityContract)
    {A c₀ r₀ s₀ v₀ : ℝ} (hc : FreshConstants c₀ r₀ s₀ v₀) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ K : ℝ, 0 < K → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ (p : Parameters) (i : ZMod p.n) (α : Fin p.N)
        (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ), IsPairFrame p i U →
      ∀ (ω : SplitState p i) (E : ℝ) (D : AngularData (PairSite p i)), D.s = c₀ →
        D.K = physicalCoareaF ω.1 ω.2.1 ω.2.2 E - (E : ℂ) • 1 →
        FreshClass (pairToFin (physicalCoareaF ω.1 ω.2.1 ω.2.2 E)) A c₀ E r₀ s₀ v₀ →
        D.ζ = (c₀ : ℂ) * freshDyson (pairToFin (physicalCoareaF ω.1 ω.2.1 ω.2.2 E)) c₀ E →
      ∀ Zf : (PairSite p i → ℂ) → ℝ, Measurable Zf → (∀ v, 0 ≤ Zf v) →
        (∀ᵐ v ∂projectiveHaar (PairSite p i), ENNReal.ofReal (Zf v) =
          ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p c₀) * ((p.n : ℝ) / 2)) *
            detFactor p i α c₀ U ω E v) →
      ∀ w : PairSite p i → ℂ,
        ∫ v, Real.exp (D.expo v) * Zf v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar (PairSite p i) ≤
          C₀ * ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar (PairSite p i)) +
              (p.n : ℝ) / 2 * CK * (Fintype.card (PairSite p i) : ℝ) ^ (-K)) /
            Fintype.card (PairSite p i) * (star w ⬝ᵥ (D.Γ *ᵥ w)).re := by
  obtain ⟨C₀, hC₀, hK⟩ := angular_first_moment (A := A) hP hD hc
  refine ⟨C₀, hC₀, fun K hK' => ?_⟩
  obtain ⟨CK, hCK, h⟩ := hK K hK'
  refine ⟨CK, hCK, ?_⟩
  intro p i α U hU ω E D hDs hDK hcls hDζ Zf hZm hZ0 hZf w
  refine h (PairSite p i) (2 * p.W - 1) (by rw [card_pairSite]) U hU.1 hU.2 D _ E hDs hDK hcls
    hDζ (negativeCount (ω.1 - (E : ℂ) • 1)) α.val ((p.n : ℝ) / 2) (by positivity) Zf hZm hZ0
    ?_ w
  filter_upwards [hZf] with v hv
  rw [hv, detFactor_eq_zdet, pairTime_eq_card p i, card_pairSite p i, mul_comm (_ / 2)]

theorem exteriorBlock_isHermitian {H : p.SiteMatrix} (hH : H.IsHermitian) :
    (exteriorBlock p i H).IsHermitian := by
  funext x y; exact congrFun (congrFun hH x.1) y.1

theorem pairBlock_isHermitian {H : p.SiteMatrix} (hH : H.IsHermitian) :
    (pairBlock p i H).IsHermitian := by
  funext x y; exact congrFun (congrFun hH x.1) y.1

theorem sub_real_smul_one_isHermitian {κ : Type} [Fintype κ] [DecidableEq κ]
    {F : Matrix κ κ ℂ} (hF : F.IsHermitian) (E : ℝ) : (F - (E : ℂ) • 1).IsHermitian := by
  refine hF.sub ?_
  unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_one]; simp

end Pair

/-!
## The polynomial deformation domain
-/

/-- On the good domain `‖F(E)‖ ≤ W + W^{M₀+2}` (from `dist(E, Spec H_R) ≥ W^{-M₀}`
and `‖V‖ + ‖C‖ ≤ W`), the reindexed deformation has polynomial size `‖F‖ ≤ N^{M₀+3}`,
`N = 2W` (the norm clause of `FreshClass` with `A = M₀ + 3`). -/
theorem normBound_pairToFin (p : Parameters) (i : ZMod p.n) {F : PairMatrix p i} {M₀ : ℝ}
    (hM₀ : 0 ≤ M₀)
    (h : ∀ x, l2Norm (F *ᵥ x) ≤ ((p.W : ℝ) + (p.W : ℝ) ^ (M₀ + 2)) * l2Norm x) :
    NormBound (pairToFin F) (M₀ + 3) := by
  intro x'
  set e := Fintype.equivFin (PairSite p i)
  have hx : x' = (x' ∘ e) ∘ e.symm := by funext b; simp
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  rw [hx, pairToFin, Matrix.reindex_apply, mulVec_reindex, l2Norm_comp_symm, l2Norm_comp_symm]
  refine (h _).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have hcard' : ((Fintype.card (PairSite p i) : ℕ) : ℝ) = 2 * p.W := by
    rw [card_pairSite]; push_cast; ring
  rw [hcard']
  have h1 : (p.W : ℝ) ≤ (p.W : ℝ) ^ (M₀ + 3) := by
    conv_lhs => rw [← Real.rpow_one (p.W : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have h2 : (p.W : ℝ) ^ (M₀ + 2) ≤ (p.W : ℝ) ^ (M₀ + 3) :=
    Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have h3 : (2 : ℝ) ≤ 2 ^ (M₀ + 3) := by
    conv_lhs => rw [← Real.rpow_one (2 : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hWp : 0 ≤ (p.W : ℝ) ^ (M₀ + 3) := Real.rpow_nonneg (by linarith) _
  rw [Real.mul_rpow (by norm_num) (by linarith)]
  nlinarith

/-!
## On the regular center domain (`CenterDomainContract.regular`)
-/

/-- **Step 2 on the regular domain of the center.** With `CenterDomainContract.regular`
(fresh constants for `c₀ = s = min(c,b)`, the regularity certificate `FreshRegular` of
`F = K_e(E) + E`, the Dyson root `ζ_e = s m_s(E)` with `ℛ_e(ζ_e) = (K_e - ζ_e)⁻¹`,
`Im ζ_e ≥ y₀`, `|ζ_e| ≤ C`): for `b, ϑ` and the norm exponent `A` fixed, there are `C₀ ≥ 1` and,
for every `K > 0`, `C_K`, such that for every `ϑ`-bulk rank `α`, pair, Hermitian residual
`H^{(e)}`, energy `E` off the Schur poles in the regular domain with `‖F(E)‖ ≤ (2W)^A`
(the polynomial deformation domain), the angular data `D = (K_e(E), s, ζ_e)` exists and the
Step 1 angular measure of `ω = (H^{(e)}_R, C, V)` satisfies the first-moment bound with
`r = (n/2) C_K N^{-K}`. Only `FreshPalmContract`, `FreshEigenpairDensityContract` and the
domain clause are used. -/
theorem center_angular_first_moment (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (cst : CenterDomainConstants)
    (hcd : CenterDomainContract cst) {b ϑ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hϑ0 : 0 < ϑ)
    (hϑ1 : ϑ < 1 / 2) (A : ℝ) :
    ∃ y₀ Cζ : ℝ, 0 < y₀ ∧ ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ K : ℝ, 0 < K → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ (p : Parameters), p.b = b → ∀ (α : Fin p.N), IsBulkRank p ϑ α →
      ∀ (i : ZMod p.n) (Hres : p.SiteMatrix), Hres.IsHermitian → ∀ E : ℝ,
        (exteriorBlock p i Hres - (E : ℂ) • 1).det ≠ 0 → InCenterDomain p i cst α Hres E →
        NormBound (pairToFin (edgeSchur p i Hres E + (E : ℂ) • 1)) A →
      ∃ D : AngularData (PairSite p i), D.K = edgeSchur p i Hres E ∧ D.s = splitS p ∧
        D.ζ = dysonRoot p i (cst.ρ₀ p.b (rankMargin p α)) Hres E ∧ y₀ ≤ D.ζ.im ∧
        ‖D.ζ‖ ≤ Cζ ∧
        ∀ U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ, IsPairFrame p i U →
        ∀ Zf : (PairSite p i → ℂ) → ℝ, Measurable Zf → (∀ v, 0 ≤ Zf v) →
          (∀ᵐ v ∂projectiveHaar (PairSite p i), ENNReal.ofReal (Zf v) =
            ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (splitS p)) *
                ((p.n : ℝ) / 2)) *
              detFactor p i α (splitS p) U (splitOf p i Hres) E v) →
        ∀ w : PairSite p i → ℂ,
          ∫ v, Real.exp (D.expo v) * Zf v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar (PairSite p i) ≤
            C₀ * ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar (PairSite p i)) +
                (p.n : ℝ) / 2 * CK * (Fintype.card (PairSite p i) : ℝ) ^ (-K)) /
              Fintype.card (PairSite p i) * (star w ⬝ᵥ (D.Γ *ᵥ w)).re := by
  obtain ⟨r₀, s₀, v₀, y₀, Cζ, hfc, hy₀, hreg⟩ := hcd.regular b hb0 hb1 ϑ hϑ0 hϑ1
  obtain ⟨C₀, hC₀, hK⟩ := pair_angular_first_moment (A := A) hP hD hfc
  refine ⟨y₀, Cζ, hy₀, C₀, hC₀, fun K hK' => ?_⟩
  obtain ⟨CK, hCK, h⟩ := hK K hK'
  refine ⟨CK, hCK, ?_⟩
  intro p hpb α hα i Hres hH E hdet hdom hnorm
  obtain ⟨hfr, hroot, hcomp, -, hζ, hy, hζC, -⟩ := hreg p hpb α hα i Hres hH E hdet hdom
  have hs : splitS p = min (1 - 2 * b) b := by
    unfold splitS Parameters.c; rw [hpb]
  have hs0 : 0 < splitS p := hs ▸ hfc.1
  set F := physicalCoareaF (exteriorBlock p i Hres) (couplingBlock p i Hres) (pairBlock p i Hres)
    E with hFdef
  have hKF : edgeSchur p i Hres E + (E : ℂ) • 1 = F := sub_add_cancel _ _
  have hFH : F.IsHermitian := physicalCoareaF_isHermitian (exteriorBlock_isHermitian p i hH) _
    (pairBlock_isHermitian p i hH) E
  have hKH : (edgeSchur p i Hres E).IsHermitian := sub_real_smul_one_isHermitian hFH E
  set ζ := dysonRoot p i (cst.ρ₀ p.b (rankMargin p α)) Hres E with hζdef
  have hroot' : Reference.IsAngularRoot (edgeSchur p i Hres E) (splitS p) ζ := by
    refine ⟨hroot.1, ?_⟩
    conv_lhs => rw [hroot.2]
    rw [hcomp, card_pairSite]
    push_cast
    rfl
  let D : AngularData (PairSite p i) := ⟨edgeSchur p i Hres E, splitS p, ζ, hKH, hs0, hroot'⟩
  refine ⟨D, rfl, rfl, rfl, hy, hζC, ?_⟩
  intro U hU Zf hZm hZ0 hZf w
  have hFin : (pairToFin F).IsHermitian := by
    unfold pairToFin; rw [Matrix.reindex_apply]; exact hFH.submatrix _
  rw [hKF] at hfr hζ hnorm
  rw [hs] at hfr hζ hZf
  exact h p i α U hU (splitOf p i Hres) E D hs rfl ⟨hFin, hnorm, hfr⟩ hζ Zf hZm hZ0 hZf w

end BlockBand.Angular.FirstMoment

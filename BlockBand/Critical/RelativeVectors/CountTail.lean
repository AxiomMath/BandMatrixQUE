module

public import BlockBand.Layers.AbsorberCount
public import BlockBand.Wegner.ConditionalCount
public import BlockBand.Coarea.FreshPalmDensity
public import BlockBand.Critical.PointDensity.Boundary

/-!
# The one-block PSSS count tail at variance `c`

*Law.* `G ~ gueMeasure (Fin N) (c/N)` (`GUE_N(c/N)`), `F` deterministic Hermitian.
*Count.* `windowCount F G I = #{ℓ : λ_ℓ(F + G) ∈ I}` (multiplicity; `freshEigenvalue`).

* `windowCount_factorialMoment`: `E (N_{[a,b]})_r ≤ (C/√c · N · (b-a))^r`, integrable.
* `windowCount_tail`: `P(N_{[a,b]} ≥ r) ≤ (C/√c · N · (b-a))^r / r!`.
* `unfoldedCount_tail`: under `FreshClass F A c E r₀ s₀ v₀`, with
  `x_ℓ = Nρ(λ_ℓ - E)`, `ρ = π^{-1} Im m_{F,c}(E)`:
  `P(#{ℓ : |x_ℓ| ≤ R} ≥ k+1) ≤ (2πCR/(√c v₀))^{k+1}/(k+1)!`, uniformly in `N ≥ 1`, `F`, `E`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.External
open BlockBand.Layers (blockLaw absorbedCount absorbedMatrix hermPart_of_isHermitian
  ae_blocks_isHermitian absorbedCount_tail absorbedCount_factorialMoment)
open BlockBand.Counting (hermitianReindex nativeEigenCount_hermitianReindex)
open scoped ENNReal NNReal

variable {N : ℕ}

/-- Number of eigenvalues of `F + G` in `I`, with multiplicity (increasing ranks). -/
def windowCount (F G : Matrix (Fin N) (Fin N) ℂ) (I : Set ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun ℓ : Fin N => freshEigenvalue (F + G) ℓ ∈ I).card

theorem measurable_windowCount (F : Matrix (Fin N) (Fin N) ℂ) {I : Set ℝ}
    (hI : MeasurableSet I) : Measurable fun G => windowCount F G I := by
  classical
  have h : (fun G => windowCount F G I) =
      fun G => ∑ ℓ : Fin N, if freshEigenvalue (F + G) ℓ ∈ I then 1 else 0 := by
    funext G
    simp only [windowCount, Finset.card_filter]
  rw [h]
  refine Finset.measurable_sum _ fun ℓ _ => Measurable.ite ?_ measurable_const measurable_const
  exact ((BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue ℓ).comp
    (continuous_const.add continuous_id).measurable) hI

/-- For Hermitian `F + G`, `windowCount` is the PSSS count. -/
theorem windowCount_eq_eigenCount (F G : Matrix (Fin N) (Fin N) ℂ) (h : (F + G).IsHermitian)
    (I : Set ℝ) : windowCount F G I = PSSS.eigenCount ⟨F + G, h⟩ I := by
  classical
  unfold windowCount PSSS.eigenCount
  refine Finset.card_bij (fun ℓ _ => Fin.cast (Fintype.card_fin N).symm ℓ) ?_ ?_ ?_
  · intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ ⊢
    unfold freshEigenvalue at hℓ
    rwa [BlockBand.Model.Construction.rawIncreasingEigenvalue_eq _ _ h] at hℓ
  · intro a _ b _ hab
    exact Fin.cast_injective _ hab
  · intro i hi
    refine ⟨Fin.cast (Fintype.card_fin N) i, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    unfold freshEigenvalue
    rw [BlockBand.Model.Construction.rawIncreasingEigenvalue_eq _ _ h]
    simpa using hi

/-- `Fin N ≃ Fin 1 × Fin N`. -/
def oneBlockEquiv (N : ℕ) : Fin N ≃ Fin 1 × Fin N := (Equiv.uniqueProd (Fin N) (Fin 1)).symm

/-- The PSSS deformation `X = -F` on the one-block index `Fin 1 × Fin N`. -/
def oneBlockX (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) :
    PSSS.HermitianMatrix (Fin 1 × Fin N) :=
  hermitianReindex (oneBlockEquiv N) ⟨-F, hF.neg⟩

/-- With one block and `X = -F`, the absorbed count at `E = 0` is `windowCount F (A 0) I`
whenever `A 0` is Hermitian. -/
theorem absorbedCount_oneBlock (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) (I : Set ℝ)
    (A : Fin 1 → Matrix (Fin N) (Fin N) ℂ) (hA : (A 0).IsHermitian) :
    absorbedCount 0 (oneBlockX F hF) I A = windowCount F (A 0) I := by
  have hA' : ∀ j, (A j).IsHermitian := fun j => by rw [Subsingleton.elim j 0]; exact hA
  have hm : absorbedMatrix 0 (oneBlockX F hF) A =
      hermitianReindex (oneBlockEquiv N) ⟨F + A 0, hF.add hA⟩ := by
    apply Subtype.ext
    rw [BlockBand.Layers.absorbedMatrix_val 0 (oneBlockX F hF) hA']
    ext x y
    simp only [oneBlockX, hermitianReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
      BlockBand.Internal.Contracts.Layers.blockDiag, Complex.ofReal_zero, zero_smul, sub_zero]
    have hx : x.1 = 0 := Subsingleton.elim _ _
    have hy : y.1 = 0 := Subsingleton.elim _ _
    simp only [hx, hy, ite_true, oneBlockEquiv, Equiv.symm_symm, Equiv.uniqueProd_apply]
    ring
  unfold absorbedCount
  rw [hm, nativeEigenCount_hermitianReindex, windowCount_eq_eigenCount]

/-- Transfer of a statistic of `A 0` from `blockLaw 1 N c` to `GUE_N(c/N)`. -/
theorem blockLaw_one_map (N : ℕ) (c : ℝ) :
    MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) (Matrix (Fin N) (Fin N) ℂ))
      (blockLaw 1 N c) (gueMeasure (Fin N) (Real.toNNReal (c / N))) :=
  measurePreserving_funUnique _ _

/-- A.e. equality of the one-block count and `windowCount` under `blockLaw 1 N c`. -/
theorem ae_absorbedCount_oneBlock (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian)
    (I : Set ℝ) (c : ℝ) :
    ∀ᵐ A ∂(blockLaw 1 N c), absorbedCount 0 (oneBlockX F hF) I A = windowCount F (A 0) I := by
  filter_upwards [ae_blocks_isHermitian 1 N (Real.toNNReal (c / N))] with A hA
  exact absorbedCount_oneBlock F hF I A (hA 0)

/-- **Factorial moments of the count at variance `c`** (PSSS, one block, `√c` rescaling). With
`C` the absolute PSSS constant, for all `N ≥ 1`, `c > 0`, Hermitian `F`, `a ≤ b`, `r ≥ 1`, under
`G ~ GUE_N(c/N)`: `(N_{[a,b]})_r` is integrable and `E (N_{[a,b]})_r ≤ (C/√c · N · (b-a))^r`.
Uniform in `F` (no norm bound). Hypothesis: the native `PSSS.SourceContract` only. -/
theorem windowCount_factorialMoment (source : PSSS.SourceContract.{0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ c : ℝ, 0 < c →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ (a b : ℝ), a ≤ b →
      ∀ r : ℕ, 1 ≤ r →
        Integrable (fun G => (Nat.descFactorial (windowCount F G (Set.Icc a b)) r : ℝ))
          (gueMeasure (Fin N) (Real.toNNReal (c / N))) ∧
        (∫ G, (Nat.descFactorial (windowCount F G (Set.Icc a b)) r : ℝ)
            ∂gueMeasure (Fin N) (Real.toNNReal (c / N))) ≤
          (C / Real.sqrt c * N * (b - a)) ^ r := by
  obtain ⟨C, hC, h⟩ :=
    absorbedCount_factorialMoment (BlockBand.Wegner.conditionalBlockGUECount_holds source)
  refine ⟨C, hC, fun N hN c hc F hF a b hab r hr => ?_⟩
  obtain ⟨hint, hbd⟩ := h 1 N hN c hc 0 (oneBlockX F hF) a b hab r hr
  have hmp := blockLaw_one_map N c
  have hae : PSSS.factorialCount (absorbedCount 0 (oneBlockX F hF) (Set.Icc a b)) r =ᵐ[blockLaw 1 N c]
      fun A => (Nat.descFactorial (windowCount F (A 0) (Set.Icc a b)) r : ℝ) := by
    filter_upwards [ae_absorbedCount_oneBlock F hF (Set.Icc a b) c] with A hA
    simp only [PSSS.factorialCount, hA]
  have hcomp : (fun A : Fin 1 → Matrix (Fin N) (Fin N) ℂ =>
      (Nat.descFactorial (windowCount F (A 0) (Set.Icc a b)) r : ℝ)) =
      (fun G => (Nat.descFactorial (windowCount F G (Set.Icc a b)) r : ℝ)) ∘
        MeasurableEquiv.funUnique (Fin 1) (Matrix (Fin N) (Fin N) ℂ) := by
    funext A; rfl
  have hint' := (integrable_congr hae).1 hint
  rw [hcomp] at hint'
  refine ⟨(hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 hint', ?_⟩
  have heq := hmp.integral_comp'
    (fun G => (Nat.descFactorial (windowCount F G (Set.Icc a b)) r : ℝ))
  rw [integral_congr_ae hae] at hbd
  have heq' : (∫ A : Fin 1 → Matrix (Fin N) (Fin N) ℂ,
      (Nat.descFactorial (windowCount F (A 0) (Set.Icc a b)) r : ℝ) ∂blockLaw 1 N c) =
      ∫ G, (Nat.descFactorial (windowCount F G (Set.Icc a b)) r : ℝ)
        ∂gueMeasure (Fin N) (Real.toNNReal (c / N)) := heq
  rw [heq', Nat.cast_one, one_mul] at hbd
  exact hbd

/-- **Count tail at variance `c`** (Markov on the factorial moment). With `C` the PSSS
constant, for all `N ≥ 1`, `c > 0`, Hermitian `F`, `a ≤ b`, `r ≥ 1`, under `G ~ GUE_N(c/N)`:
`P(N_{[a,b]} ≥ r) ≤ (C/√c · N · (b-a))^r / r!`. Hypothesis: the native `PSSS.SourceContract`. -/
theorem windowCount_tail (source : PSSS.SourceContract.{0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ c : ℝ, 0 < c →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ (a b : ℝ), a ≤ b →
      ∀ r : ℕ, 1 ≤ r →
        gueMeasure (Fin N) (Real.toNNReal (c / N)) {G | r ≤ windowCount F G (Set.Icc a b)} ≤
          ENNReal.ofReal ((C / Real.sqrt c * N * (b - a)) ^ r / r.factorial) := by
  obtain ⟨C, hC, h⟩ :=
    absorbedCount_tail (BlockBand.Wegner.conditionalBlockGUECount_holds source)
  refine ⟨C, hC, fun N hN c hc F hF a b hab r hr => ?_⟩
  have hbd := h 1 N hN c hc 0 (oneBlockX F hF) a b hab r hr
  have hmp := blockLaw_one_map N c
  have hS : MeasurableSet {G : Matrix (Fin N) (Fin N) ℂ | r ≤ windowCount F G (Set.Icc a b)} :=
    measurableSet_le measurable_const (measurable_windowCount F measurableSet_Icc)
  have hpre : (blockLaw 1 N c) {A | r ≤ absorbedCount 0 (oneBlockX F hF) (Set.Icc a b) A} =
      (blockLaw 1 N c) (MeasurableEquiv.funUnique (Fin 1) (Matrix (Fin N) (Fin N) ℂ) ⁻¹'
        {G | r ≤ windowCount F G (Set.Icc a b)}) := by
    apply measure_congr
    filter_upwards [ae_absorbedCount_oneBlock F hF (Set.Icc a b) c] with A hA
    change (r ≤ absorbedCount 0 (oneBlockX F hF) (Set.Icc a b) A) =
      (r ≤ windowCount F (A 0) (Set.Icc a b))
    rw [hA]
  rw [hpre, hmp.measure_preimage hS.nullMeasurableSet, Nat.cast_one, one_mul] at hbd
  exact hbd

/-- Unfolded window: for `N ≥ 1`, `ρ > 0`, `R ≥ 0`, `|Nρ(λ - E)| ≤ R` iff
`λ ∈ [E - R/(Nρ), E + R/(Nρ)]`. -/
theorem abs_unfold_le_iff {N : ℕ} (hN : 0 < N) {ρ : ℝ} (hρ : 0 < ρ) (E R lam : ℝ) :
    |(N : ℝ) * ρ * (lam - E)| ≤ R ↔ lam ∈ Set.Icc (E - R / (N * ρ)) (E + R / (N * ρ)) := by
  have hNρ : 0 < (N : ℝ) * ρ := mul_pos (by exact_mod_cast hN) hρ
  rw [abs_le, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : E - lam ≤ R / (N * ρ) := by rw [le_div_iff₀ hNρ]; nlinarith
      linarith
    · have : lam - E ≤ R / (N * ρ) := by rw [le_div_iff₀ hNρ]; nlinarith
      linarith
  · rintro ⟨h1, h2⟩
    have h1' : (E - lam) * (N * ρ) ≤ R := (le_div_iff₀ hNρ).1 (by linarith)
    have h2' : (lam - E) * (N * ρ) ≤ R := (le_div_iff₀ hNρ).1 (by linarith)
    constructor <;> nlinarith

/-- **The unfolded count tail, uniformly over the regular class.** With `C` the
absolute PSSS constant: for every `A`, `FreshConstants c r₀ s₀ v₀`, `N ≥ 1`, `F` in
`FreshClass F A c E r₀ s₀ v₀`, `R ≥ 0` and `k`, under `G ~ GUE_N(c/N)`, with
`x_ℓ = Nρ(λ_ℓ(F+G) - E)` and `ρ = π^{-1} Im m_{F,c}(E)`:
`P(#{ℓ : |x_ℓ| ≤ R} ≥ k+1) ≤ (2πCR/(√c v₀))^{k+1}/(k+1)!`.
Uses `ρ ≥ v₀/π` (the fresh regularity bound at `s = c`, `η = 0`). Hypothesis: `PSSS.SourceContract`. -/
theorem unfoldedCount_tail (source : PSSS.SourceContract.{0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A c r₀ s₀ v₀ : ℝ), FreshConstants c r₀ s₀ v₀ →
      ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
      FreshClass F A c E r₀ s₀ v₀ → ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ,
        gueMeasure (Fin N) (Real.toNNReal (c / N))
            {G | k + 1 ≤ (Finset.univ.filter fun ℓ : Fin N =>
              |(N : ℝ) * ((freshDyson F c E).im / Real.pi) * (freshEigenvalue (F + G) ℓ - E)|
                ≤ R).card} ≤
          ENNReal.ofReal ((2 * Real.pi * C * R / (Real.sqrt c * v₀)) ^ (k + 1) /
            (k + 1).factorial) := by
  obtain ⟨C, hC, h⟩ := windowCount_tail source
  refine ⟨C, hC, fun A c r₀ s₀ v₀ hK N hN F E hF R hR k => ?_⟩
  have hc : 0 < c := hK.1
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  obtain ⟨hv, -⟩ := BlockBand.Critical.PointDensity.freshDyson_im_bounds hK hF
  set ρ := (freshDyson F c E).im / Real.pi with hρdef
  have hρ : v₀ / Real.pi ≤ ρ := div_le_div_of_nonneg_right hv Real.pi_pos.le
  have hρ0 : 0 < ρ := lt_of_lt_of_le (div_pos hv0 Real.pi_pos) hρ
  have hNρ : 0 < (N : ℝ) * ρ := mul_pos (by exact_mod_cast hN) hρ0
  have hab : E - R / (N * ρ) ≤ E + R / (N * ρ) := by
    have : 0 ≤ R / (N * ρ) := div_nonneg hR hNρ.le
    linarith
  have hset : {G : Matrix (Fin N) (Fin N) ℂ | k + 1 ≤ (Finset.univ.filter fun ℓ : Fin N =>
      |(N : ℝ) * ρ * (freshEigenvalue (F + G) ℓ - E)| ≤ R).card} =
      {G | k + 1 ≤ windowCount F G (Set.Icc (E - R / (N * ρ)) (E + R / (N * ρ)))} := by
    ext G
    simp only [Set.mem_ofPred_eq, windowCount, abs_unfold_le_iff hN hρ0]
    convert Iff.rfl using 3
    exact Finset.filter_congr_decidable _ _ _
  rw [hset]
  refine (h N hN c hc F hF.1 _ _ hab (k + 1) (Nat.le_add_left 1 k)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  refine div_le_div_of_nonneg_right (pow_le_pow_left₀ ?_ ?_ _) (Nat.cast_nonneg _)
  · have : 0 ≤ R / (N * ρ) := div_nonneg hR hNρ.le
    have : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    have : 0 ≤ C / Real.sqrt c * N := by positivity
    nlinarith
  · have hsq : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    have hlen : E + R / (N * ρ) - (E - R / (N * ρ)) = 2 * R / (N * ρ) := by ring
    rw [hlen]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have e1 : C / Real.sqrt c * N * (2 * R / (N * ρ)) = 2 * C * R / (Real.sqrt c * ρ) := by
      field_simp
    rw [e1]
    have e2 : 2 * Real.pi * C * R / (Real.sqrt c * v₀) = 2 * C * R / (Real.sqrt c * (v₀ / Real.pi)) := by
      field_simp
    rw [e2]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hρ hsq.le

end BlockBand.Critical.RelativeVectors

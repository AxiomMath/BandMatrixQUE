module

public import BlockBand.DeterminantScore.WeylIntegrationReduction
public import BlockBand.DeterminantScore.WeylIntegrationInterlace

/-!
# Weyl integration: the eigenvalue law by induction on the corner

Write an `(n+1) × (n+1)` Hermitian matrix as the bordered matrix
`borderHerm M v a = [[M, v], [v*, a]]` (`M` the `n × n` corner, `v ∈ ℂ^n`, `a ∈ ℝ`). Two classical
facts are isolated as named `Prop`s:

* `CornerFubiniStatement`: Lebesgue measure on `HermCoord (n+1)` is the product of Lebesgue
  measure on `HermCoord n` (the corner), on `ℂ^n` (the last column, `v_i = x(i,n) + i x(n,i)`)
  and on `ℝ` (the last diagonal entry). This is a coordinate permutation.
* `BorderEigenLawStatement`: for every Hermitian `M` with strictly increasing eigenvalues `μ`,
  `∫_{ℂ^n} ∫_ℝ g(λ([[M, v],[v*, a]])) da dv = π^n ∫_{λ ≻ μ} (Δ(λ)/Δ(μ)) g(λ) dλ`, where `λ ≻ μ`
  is strict interlacing `λ_i < μ_i < λ_{i+1}` (the arrowhead / Gelfand–Tsetlin change of
  variables `(a, |w_i|²) ↦ λ`, `w = V*v`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open MeasureTheory Matrix BlockBand.DeterminantScore.Sector
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.DeterminantScore.SpectralConvexity (weylChamber)
open scoped ENNReal NNReal

variable {n : ℕ}

/-- The bordered matrix `[[M, v], [v*, a]]` on `Fin (n+1)` (corner on `castSucc`, border on
`last`). -/
def borderHerm (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (a : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun p q =>
    Fin.lastCases (Fin.lastCases (a : ℂ) (fun j => star (v j)) q)
      (fun i => Fin.lastCases (v i) (fun j => M i j) q) p

/-- Strict interlacing `λ_i < μ_i < λ_{i+1}`. -/
def interlaceSet (μ : Fin n → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {lam | ∀ i, lam i.castSucc < μ i ∧ μ i < lam i.succ}

/-- `∫_{λ ≻ μ} (Δ(λ)/Δ(μ)) g(λ) dλ`. -/
def interlaceAverage (g : (Fin (n + 1) → ℝ) → ℝ≥0∞) (μ : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ lam in interlaceSet μ,
    ENNReal.ofReal (SpectralConvexity.vandermonde lam / SpectralConvexity.vandermonde μ) * g lam

/-- **Corner Fubini** (coordinate permutation): Lebesgue measure on `HermCoord (n+1)` is the
product of Lebesgue measures on the corner coordinates `HermCoord n`, on the border `ℂ^n`
(`v_i = x(i, n) + i·x(n, i)`, the standard volume of `ℂ ≅ ℝ²`) and on the corner entry `ℝ`. -/
def CornerFubiniStatement : Prop :=
  ∀ n : ℕ, ∀ G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ℝ≥0∞, Measurable G →
    ∫⁻ x : HermCoord (n + 1) → ℝ, G (hermOfCoord x) =
      ∫⁻ y : HermCoord n → ℝ, ∫⁻ v : Fin n → ℂ, ∫⁻ a : ℝ, G (borderHerm (hermOfCoord y) v a)

/-- **Eigenvalue law of a bordered matrix** (classical: rotate `v ↦ V*v` with `M = V diag(μ) V*`,
use `det(z - [[diag μ, w],[w*, a]]) = (z - a)∏(z - μ_k) - Σ_i |w_i|² ∏_{k≠i}(z - μ_k)`, polar
coordinates `dw_i = π d|w_i|²`, and the change of variables `(a, |w|²) ↦ λ`, which maps
`ℝ × (0,∞)^n` bijectively onto the strictly interlacing `λ` with Jacobian `Δ(λ)/Δ(μ)`).
For every Hermitian `M` whose increasing eigenvalues `μ` are strictly increasing and every
measurable `g ≥ 0`: `∫_{ℂ^n} ∫_ℝ g(λ(borderHerm M v a)) da dv = π^n ∫_{λ ≻ μ} (Δ(λ)/Δ(μ)) g(λ) dλ`
(Lebesgue measures). -/
def BorderEigenLawStatement : Prop :=
  ∀ n : ℕ, ∀ g : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable g →
    ∀ M : Matrix (Fin n) (Fin n) ℂ, M.IsHermitian → StrictMono (fun k => freshEigenvalue M k) →
      ∫⁻ v : Fin n → ℂ, ∫⁻ a : ℝ, g (fun k => freshEigenvalue (borderHerm M v a) k) =
        ENNReal.ofReal (Real.pi ^ n) * interlaceAverage g (fun k => freshEigenvalue M k)

/-!
## Measurability
-/

/-- The joint interlacing set `{(μ, λ) : λ ≻ μ}`. -/
def interlacePairs (n : ℕ) : Set ((Fin n → ℝ) × (Fin (n + 1) → ℝ)) :=
  {p | ∀ i, p.2 i.castSucc < p.1 i ∧ p.1 i < p.2 i.succ}

theorem measurableSet_interlacePairs : MeasurableSet (interlacePairs n) := by
  have : interlacePairs n = ⋂ i : Fin n,
      ({p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.2 i.castSucc < p.1 i} ∩
        {p | p.1 i < p.2 i.succ}) := by
    ext p; simp [interlacePairs]
  rw [this]
  refine MeasurableSet.iInter fun i => (measurableSet_lt ?_ ?_).inter (measurableSet_lt ?_ ?_)
  · exact (measurable_pi_apply _).comp measurable_snd
  · exact (measurable_pi_apply _).comp measurable_fst
  · exact (measurable_pi_apply _).comp measurable_fst
  · exact (measurable_pi_apply _).comp measurable_snd

theorem measurable_vandermonde {m : ℕ} :
    Measurable fun v : Fin m → ℝ => SpectralConvexity.vandermonde v :=
  continuous_vandermonde.measurable

theorem measurable_interlaceAverage {g : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    Measurable (interlaceAverage g) := by
  have hF : Measurable fun p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) =>
      (interlacePairs n).indicator (fun q => ENNReal.ofReal
        (SpectralConvexity.vandermonde q.2 / SpectralConvexity.vandermonde q.1) * g q.2) p := by
    refine Measurable.indicator ?_ measurableSet_interlacePairs
    refine (ENNReal.measurable_ofReal.comp ?_).mul (hg.comp measurable_snd)
    exact (measurable_vandermonde.comp measurable_snd).div
      (measurable_vandermonde.comp measurable_fst)
  have h := hF.lintegral_prod_right' (ν := volume)
  have heq : interlaceAverage g = fun μ => ∫⁻ lam, (interlacePairs n).indicator (fun q =>
      ENNReal.ofReal (SpectralConvexity.vandermonde q.2 / SpectralConvexity.vandermonde q.1) *
        g q.2) (μ, lam) := by
    funext μ
    simp only [interlaceAverage]
    rw [← lintegral_indicator (show MeasurableSet (interlaceSet μ) from
      measurableSet_interlacePairs.preimage measurable_prodMk_left)]
    rfl
  rw [heq]
  exact h

/-!
## The inductive step
-/

theorem strictMono_lam_of_interlace {μ : Fin n → ℝ} {lam : Fin (n + 1) → ℝ}
    (h : lam ∈ interlaceSet μ) : StrictMono lam :=
  Fin.strictMono_iff_lt_succ.2 fun i => (h i).1.trans (h i).2

theorem strictMono_of_interlace {μ : Fin n → ℝ} {lam : Fin (n + 1) → ℝ}
    (h : lam ∈ interlaceSet μ) : StrictMono μ := by
  intro i j hij
  have hle : lam i.succ ≤ lam j.castSucc := (strictMono_lam_of_interlace h).monotone (by
    rw [Fin.le_def]
    simp only [Fin.val_succ, Fin.val_castSucc]
    exact Fin.lt_def.1 hij)
  linarith [(h i).2, (h j).1]

theorem interlaceBox_eq_empty {lam : Fin (n + 1) → ℝ} (hlam : lam ∉ weylChamber (n + 1)) :
    interlaceBox lam = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun μ hμ => hlam ?_
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  exact (hμ i (Set.mem_univ _)).1.trans (hμ i (Set.mem_univ _)).2

/-- The double integral after Tonelli: `∫_{𝒞_{n+1}} Δ(λ)·Δ(λ)/n!·g(λ) dλ`. -/
theorem lintegral_interlace_swap {g : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ μ in weylChamber n,
        ENNReal.ofReal (SpectralConvexity.vandermonde μ ^ 2) * interlaceAverage g μ =
      ENNReal.ofReal ((n.factorial : ℝ)⁻¹) * ∫⁻ lam in weylChamber (n + 1),
        ENNReal.ofReal (SpectralConvexity.vandermonde lam ^ 2) * g lam := by
  set F : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ℝ≥0∞ := fun p =>
    (interlacePairs n).indicator (fun q => ENNReal.ofReal
      (SpectralConvexity.vandermonde q.1 * SpectralConvexity.vandermonde q.2) * g q.2) p with hFdef
  have hFm : Measurable F := by
    refine Measurable.indicator ?_ measurableSet_interlacePairs
    refine (ENNReal.measurable_ofReal.comp ?_).mul (hg.comp measurable_snd)
    exact (measurable_vandermonde.comp measurable_fst).mul
      (measurable_vandermonde.comp measurable_snd)
  -- the μ-side
  have hL : ∀ μ : Fin n → ℝ, (weylChamber n).indicator
      (fun μ => ENNReal.ofReal (SpectralConvexity.vandermonde μ ^ 2) * interlaceAverage g μ) μ =
      ∫⁻ lam, F (μ, lam) := by
    intro μ
    have hS : MeasurableSet (interlaceSet μ) :=
      measurableSet_interlacePairs.preimage measurable_prodMk_left
    have hFμ : (fun lam => F (μ, lam)) = (interlaceSet μ).indicator (fun lam => ENNReal.ofReal
        (SpectralConvexity.vandermonde μ * SpectralConvexity.vandermonde lam) * g lam) := by
      funext lam
      simp only [hFdef, Set.indicator]
      rfl
    rw [hFμ, lintegral_indicator hS]
    by_cases hμ : μ ∈ weylChamber n
    · rw [Set.indicator_of_mem hμ, interlaceAverage, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun hS fun lam hlam => ?_
      have hpos := SpectralConvexity.vandermonde_pos hμ
      have hlpos := SpectralConvexity.vandermonde_pos (strictMono_lam_of_interlace hlam)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 2
      field_simp
    · rw [Set.indicator_of_notMem hμ]
      have hempty : interlaceSet μ = ∅ :=
        Set.eq_empty_of_forall_notMem fun lam hlam => hμ (strictMono_of_interlace hlam)
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
  -- the λ-side
  have hR : ∀ lam : Fin (n + 1) → ℝ, ∫⁻ μ, F (μ, lam) = ENNReal.ofReal ((n.factorial : ℝ)⁻¹) *
      (weylChamber (n + 1)).indicator
        (fun lam => ENNReal.ofReal (SpectralConvexity.vandermonde lam ^ 2) * g lam) lam := by
    intro lam
    have hB := measurableSet_interlaceBox lam
    have hFl : (fun μ => F (μ, lam)) = (interlaceBox lam).indicator (fun μ =>
        ENNReal.ofReal (SpectralConvexity.vandermonde μ) *
          (ENNReal.ofReal (SpectralConvexity.vandermonde lam) * g lam)) := by
      funext μ
      by_cases hμ : μ ∈ interlaceBox lam
      · have hmem : (μ, lam) ∈ interlacePairs n := fun i => hμ i (Set.mem_univ _)
        have hm : StrictMono μ := strictMono_of_interlace (μ := μ) (lam := lam) hmem
        simp only [hFdef, Set.indicator_of_mem hmem, Set.indicator_of_mem hμ]
        rw [ENNReal.ofReal_mul (vandermonde_nonneg_of_monotone hm.monotone), mul_assoc]
      · have hmem : (μ, lam) ∉ interlacePairs n := fun h => hμ fun i _ => h i
        simp only [hFdef, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hμ]
    have hVm : Measurable fun μ : Fin n → ℝ =>
        ENNReal.ofReal (SpectralConvexity.vandermonde μ) :=
      ENNReal.measurable_ofReal.comp measurable_vandermonde
    rw [hFl, lintegral_indicator hB, lintegral_mul_const _ hVm]
    by_cases hlam : lam ∈ weylChamber (n + 1)
    · rw [Set.indicator_of_mem hlam, lintegral_interlaceBox_vandermonde lam
        (show StrictMono lam from hlam).monotone, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (div_nonneg (SpectralConvexity.vandermonde_pos hlam).le
          (Nat.cast_nonneg _)),
        ← ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg _))]
      congr 2
      ring
    · rw [Set.indicator_of_notMem hlam, interlaceBox_eq_empty hlam, Measure.restrict_empty,
        lintegral_zero_measure, zero_mul, mul_zero]
  rw [← lintegral_indicator (SpectralConvexity.isOpen_weylChamber.measurableSet)]
  simp_rw [hL]
  rw [lintegral_lintegral_swap hFm.aemeasurable]
  simp_rw [hR]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator (SpectralConvexity.isOpen_weylChamber.measurableSet)]

/-!
## The induction
-/

theorem measurable_freshEigs_hermOfCoord {m : ℕ} :
    Measurable fun y : HermCoord m → ℝ => fun k => freshEigenvalue (hermOfCoord y) k :=
  EigenDensity.measurable_freshEigs.comp continuous_hermOfCoord.measurable

/-- Corners with a repeated eigenvalue are Lebesgue-null, by the eigenvalue law itself. -/
theorem ae_mem_weylChamber {m : ℕ} {C : ℝ}
    (hlaw : ∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (fun k => freshEigenvalue (hermOfCoord x) k) =
        ENNReal.ofReal C * ∫⁻ lam in weylChamber m,
          ENNReal.ofReal (SpectralConvexity.vandermonde lam ^ 2) * g lam) :
    ∀ᵐ y : HermCoord m → ℝ, (fun k => freshEigenvalue (hermOfCoord y) k) ∈ weylChamber m := by
  have hch : MeasurableSet (weylChamber m) := SpectralConvexity.isOpen_weylChamber.measurableSet
  have h := hlaw ((weylChamber m)ᶜ.indicator 1) (measurable_one.indicator hch.compl)
  have hz : ∫⁻ lam in weylChamber m, ENNReal.ofReal (SpectralConvexity.vandermonde lam ^ 2) *
      (weylChamber m)ᶜ.indicator 1 lam = 0 := by
    rw [setLIntegral_congr_fun hch (g := fun _ => 0) fun lam hl => by
      simp [Set.indicator_of_notMem (show lam ∉ (weylChamber m)ᶜ from fun h => h hl)]]
    exact lintegral_zero
  rw [hz, mul_zero] at h
  have hpre : MeasurableSet ((fun y : HermCoord m → ℝ => fun k =>
      freshEigenvalue (hermOfCoord y) k) ⁻¹' (weylChamber m)ᶜ) :=
    measurable_freshEigs_hermOfCoord hch.compl
  rw [show (fun y : HermCoord m → ℝ => (weylChamber m)ᶜ.indicator 1
      (fun k => freshEigenvalue (hermOfCoord y) k)) = ((fun y : HermCoord m → ℝ => fun k =>
        freshEigenvalue (hermOfCoord y) k) ⁻¹' (weylChamber m)ᶜ).indicator 1 by
      funext y; simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]; rfl,
    lintegral_indicator_one hpre] at h
  exact ae_iff.2 h

/-- **The eigenvalue law from corner Fubini and the bordered-matrix law**, by induction on the
size: `C_0 = 1`, `C_{n+1} = π^n C_n / n!`. -/
theorem weylEigenLaw_of_border (hC : CornerFubiniStatement) (hB : BorderEigenLawStatement) :
    WeylEigenLawStatement := by
  intro m
  induction m with
  | zero =>
    refine ⟨1, one_pos, fun g hg => ?_⟩
    have hch : weylChamber 0 = Set.univ :=
      Set.eq_univ_of_forall fun lam => fun i => Fin.elim0 i
    rw [hch, Measure.restrict_univ, lintegral_unique, lintegral_unique]
    simp only [SpectralConvexity.vandermonde, volume_pi, Finset.univ_eq_empty,
      Finset.prod_empty, one_pow, ENNReal.ofReal_one, one_mul, Measure.pi_univ, mul_one]
    exact congrArg g (Subsingleton.elim _ _)
  | succ n ih =>
    obtain ⟨C, hCpos, hlaw⟩ := ih
    refine ⟨Real.pi ^ n * C / n.factorial, by positivity, fun g hg => ?_⟩
    rw [hC n (fun M => g (fun k => freshEigenvalue M k)) (hg.comp EigenDensity.measurable_freshEigs)]
    rw [lintegral_congr_ae ((ae_mem_weylChamber hlaw).mono fun y hy =>
      hB n g hg (hermOfCoord y) (isHermitian_hermOfCoord y) hy)]
    rw [lintegral_const_mul (f := fun y : HermCoord n → ℝ =>
        interlaceAverage g (fun k => freshEigenvalue (hermOfCoord y) k)) _
        ((measurable_interlaceAverage hg).comp measurable_freshEigs_hermOfCoord),
      hlaw _ (measurable_interlaceAverage hg), lintegral_interlace_swap hg, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 2

/-- **The Weyl integration formula from corner Fubini and the bordered-matrix law.** -/
theorem weylIntegration_of_border (hC : CornerFubiniStatement) (hB : BorderEigenLawStatement) :
    EigenDensity.WeylIntegrationStatement :=
  weylIntegration_of_eigenLaw (weylEigenLaw_of_border hC hB)

end BlockBand.DeterminantScore.WeylIntegration

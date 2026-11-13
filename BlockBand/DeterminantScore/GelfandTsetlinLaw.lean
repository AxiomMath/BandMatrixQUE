module

public import BlockBand.DeterminantScore.GelfandTsetlinIndex
public import BlockBand.DeterminantScore.WeylIntegrationComplexUnitary

/-!
# The Gelfand–Tsetlin law of Lebesgue measure on Hermitian matrices

Iterating the bordered-matrix eigenvalue law over the corners (Baryshnikov's bordering argument):
for every `n` there is `C > 0` such that for every measurable `g ≥ 0` on `ℝ^n` and every
`k ∈ ℝ^n`,

`∫ g(λ(H(x))) e^{Σ_r k_r H(x)_{rr}} dx = C ∫_𝒞 Δ(λ) g(λ) gtMarginal k λ dλ`

(`gtLaw_of_border`; Lebesgue measure on `HermCoord n`, `λ = freshEigenvalue` the increasing
eigenvalues, `𝒞` the open Weyl chamber, `gtMarginal k λ = ∫ 1_{GT}(λ, y) e^{Σ_r k_r d_r} dy`).
This is a step towards `EigenDensity.GelfandTsetlinStatement`.

Induction on `n` by corner Fubini (`cornerFubini`): the new diagonal entry of
`[[M, v],[v*, a]]` is `a = Σλ - Σμ` (trace), so the integrand factors as
`e^{Σ_{r<n} k_r M_{rr}} · g(λ) e^{k_n (Σλ - Σμ)}`; the bordered law
(`borderEigenLaw_of_diagonal`, from `DiagonalBorderLawStatement`) integrates out `(v, a)`, the
induction hypothesis integrates the corner, and Tonelli over the interlacing pairs together with
the recursion `gtMarginal_succ` closes the step (the telescoping `Δ(λ)/Δ(μ) · Δ(μ) = Δ(λ)`).
The only hypothesis is `DiagonalBorderLawStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.GelfandTsetlin

open MeasureTheory Matrix BlockBand.DeterminantScore.Sector
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.DeterminantScore.EigenDensity
open BlockBand.DeterminantScore.WeylIntegration
open BlockBand.DeterminantScore.SpectralConvexity (weylChamber)
open scoped ENNReal

variable {n : ℕ}

/-- `exp(Σ_r k_r Re M_{rr})`. -/
def diagExp {m : ℕ} (k : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  Real.exp (∑ r, k r * (M r r).re)

theorem diagExp_pos {m : ℕ} (k : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℂ) : 0 < diagExp k M :=
  Real.exp_pos _

theorem continuous_diagExp {m : ℕ} (k : Fin m → ℝ) : Continuous (diagExp k) := by
  unfold diagExp
  refine Real.continuous_exp.comp (continuous_finsetSum _ fun r _ => continuous_const.mul ?_)
  exact Complex.continuous_re.comp ((continuous_apply r).comp (continuous_apply r))

theorem diagExp_borderHerm (k : Fin (n + 1) → ℝ) (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (a : ℝ) : diagExp k (borderHerm M v a) =
      diagExp (fun r => k r.castSucc) M * Real.exp (k (Fin.last n) * a) := by
  unfold diagExp
  rw [Fin.sum_univ_castSucc, Real.exp_add]
  simp [borderHerm]

/-- `Re tr H = Σ_k λ_k(H)` for Hermitian `H`. -/
theorem trace_re_eq_sum_freshEigenvalue {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) : H.trace.re = ∑ j, freshEigenvalue H j := by
  obtain ⟨e, he⟩ := SpectralConvexity.exists_equiv_freshEigenvalue hH
  rw [hH.trace_eq_sum_eigenvalues]
  simp only [he, Complex.re_sum]
  exact (Equiv.sum_comp e (fun i => hH.eigenvalues i)).symm

theorem trace_borderHerm (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (a : ℝ) :
    (borderHerm M v a).trace.re = M.trace.re + a := by
  simp [Matrix.trace, Fin.sum_univ_castSucc, borderHerm, Complex.re_sum]

/-- The new diagonal entry of a bordered matrix is the increment of the eigenvalue sums. -/
theorem border_entry_eq {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (v : Fin n → ℂ)
    (a : ℝ) : a = ∑ j, freshEigenvalue (borderHerm M v a) j - ∑ j, freshEigenvalue M j := by
  rw [← trace_re_eq_sum_freshEigenvalue (isHermitian_borderHerm hM v a),
    ← trace_re_eq_sum_freshEigenvalue hM, trace_borderHerm]
  ring

/-!
## The bordered average
-/

theorem measurable_topWeight_swap (c : ℝ) :
    Measurable fun q : (Fin n → ℝ) × (Fin (n + 1) → ℝ) => topWeight c q.2 q.1 := by
  unfold topWeight
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Continuous.measurable ?_))
  fun_prop

theorem measurable_topWeight_left (c : ℝ) (μ : Fin n → ℝ) :
    Measurable fun lam : Fin (n + 1) → ℝ => topWeight c lam μ := by
  unfold topWeight
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Continuous.measurable ?_))
  fun_prop

/-- `Ξ(μ) = ∫_{λ ≻ μ} (Δ(λ)/Δ(μ)) g(λ) e^{c(Σλ - Σμ)} dλ`. -/
def borderAverage (g : (Fin (n + 1) → ℝ) → ℝ≥0∞) (c : ℝ) (μ : Fin n → ℝ) : ℝ≥0∞ :=
  interlaceAverage (fun lam => g lam * topWeight c lam μ) μ

theorem measurable_borderAverage {g : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hg : Measurable g) (c : ℝ) :
    Measurable (borderAverage g c) := by
  have hF : Measurable fun p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) =>
      (interlacePairs n).indicator (fun q => ENNReal.ofReal
        (SpectralConvexity.vandermonde q.2 / SpectralConvexity.vandermonde q.1) * (g q.2 * topWeight c q.2 q.1)) p := by
    refine Measurable.indicator ?_ measurableSet_interlacePairs
    refine (ENNReal.measurable_ofReal.comp ?_).mul ((hg.comp measurable_snd).mul
      (measurable_topWeight_swap c))
    exact (measurable_vandermonde.comp measurable_snd).div
      (measurable_vandermonde.comp measurable_fst)
  have h := hF.lintegral_prod_right' (ν := volume)
  have heq : borderAverage g c = fun μ => ∫⁻ lam, (interlacePairs n).indicator (fun q =>
      ENNReal.ofReal (SpectralConvexity.vandermonde q.2 / SpectralConvexity.vandermonde q.1) * (g q.2 * topWeight c q.2 q.1))
        (μ, lam) := by
    funext μ
    simp only [borderAverage, interlaceAverage]
    rw [← lintegral_indicator (show MeasurableSet (interlaceSet μ) from
      measurableSet_interlacePairs.preimage measurable_prodMk_left)]
    rfl
  rw [heq]
  exact h

/-- **Tonelli over the interlacing pairs** with the recursion of the marginal:
`∫_{𝒞_n} Δ(μ) Ξ(μ) Φ_n(μ) dμ = ∫_{𝒞_{n+1}} Δ(λ) g(λ) Φ_{n+1}(λ) dλ`. -/
theorem lintegral_borderAverage_swap {g : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hg : Measurable g)
    (k : Fin (n + 1) → ℝ) :
    ∫⁻ μ in weylChamber n, ENNReal.ofReal (SpectralConvexity.vandermonde μ) *
        borderAverage g (k (Fin.last n)) μ * gtMarginal (fun r => k r.castSucc) μ =
      ∫⁻ lam in weylChamber (n + 1), ENNReal.ofReal (SpectralConvexity.vandermonde lam) * g lam *
        gtMarginal k lam := by
  set c := k (Fin.last n)
  set Φ := gtMarginal (fun r : Fin n => k r.castSucc)
  set F : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ℝ≥0∞ := fun p =>
    (interlacePairs n).indicator (fun q => ENNReal.ofReal (SpectralConvexity.vandermonde q.2) * g q.2 *
      (topWeight c q.2 q.1 * Φ q.1)) p with hFdef
  have hFm : Measurable F := by
    refine Measurable.indicator ?_ measurableSet_interlacePairs
    refine ((ENNReal.measurable_ofReal.comp (measurable_vandermonde.comp measurable_snd)).mul
      (hg.comp measurable_snd)).mul ((measurable_topWeight_swap c).mul ((measurable_gtMarginal _).comp measurable_fst))
  -- the μ-side
  have hL : ∀ μ : Fin n → ℝ, (weylChamber n).indicator (fun μ => ENNReal.ofReal (SpectralConvexity.vandermonde μ) *
      borderAverage g c μ * Φ μ) μ = ∫⁻ lam, F (μ, lam) := by
    intro μ
    have hS : MeasurableSet (interlaceSet μ) :=
      measurableSet_interlacePairs.preimage measurable_prodMk_left
    have hFμ : (fun lam => F (μ, lam)) = (interlaceSet μ).indicator (fun lam =>
        ENNReal.ofReal (SpectralConvexity.vandermonde lam) * g lam * (topWeight c lam μ * Φ μ)) := by
      funext lam
      simp only [hFdef, Set.indicator]
      rfl
    rw [hFμ, lintegral_indicator hS]
    by_cases hμ : μ ∈ weylChamber n
    · have hfm : Measurable fun lam : Fin (n + 1) → ℝ =>
          ENNReal.ofReal (SpectralConvexity.vandermonde lam / SpectralConvexity.vandermonde μ) * (g lam * topWeight c lam μ) :=
        (ENNReal.measurable_ofReal.comp (measurable_vandermonde.div_const _)).mul
          (hg.mul (measurable_topWeight_left c μ))
      rw [Set.indicator_of_mem hμ, borderAverage, interlaceAverage,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_mul_const _
          (show Measurable fun lam => ENNReal.ofReal (SpectralConvexity.vandermonde μ) *
            (ENNReal.ofReal (SpectralConvexity.vandermonde lam / SpectralConvexity.vandermonde μ) *
              (g lam * topWeight c lam μ)) from measurable_const.mul hfm)]
      refine setLIntegral_congr_fun hS fun lam _ => ?_
      have hpos := SpectralConvexity.vandermonde_pos hμ
      rw [← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_div_cancel₀ _ hpos.ne']
      ring
    · rw [Set.indicator_of_notMem hμ]
      have hempty : interlaceSet μ = ∅ :=
        Set.eq_empty_of_forall_notMem fun lam hlam => hμ (strictMono_of_interlace hlam)
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
  -- the λ-side
  have hR : ∀ lam : Fin (n + 1) → ℝ, ∫⁻ μ, F (μ, lam) = (weylChamber (n + 1)).indicator
      (fun lam => ENNReal.ofReal (SpectralConvexity.vandermonde lam) * g lam * gtMarginal k lam) lam := by
    intro lam
    have hB := measurableSet_interlaceBox lam
    have hFl : (fun μ => F (μ, lam)) = (interlaceBox lam).indicator (fun μ =>
        ENNReal.ofReal (SpectralConvexity.vandermonde lam) * g lam * (topWeight c lam μ * Φ μ)) := by
      funext μ
      by_cases hμ : μ ∈ interlaceBox lam
      · have hmem : (μ, lam) ∈ interlacePairs n := fun i => hμ i (Set.mem_univ _)
        simp only [hFdef, Set.indicator_of_mem hmem, Set.indicator_of_mem hμ]
      · have hmem : (μ, lam) ∉ interlacePairs n := fun h => hμ fun i _ => h i
        simp only [hFdef, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hμ]
    rw [hFl, lintegral_indicator hB, lintegral_const_mul _
      (show Measurable fun μ => topWeight c lam μ * Φ μ from
        (measurable_topWeight_right c lam).mul (measurable_gtMarginal _))]
    by_cases hlam : lam ∈ weylChamber (n + 1)
    · rw [Set.indicator_of_mem hlam, gtMarginal_succ k lam, lintegral_closedBox_eq]
    · rw [Set.indicator_of_notMem hlam, interlaceBox_eq_empty hlam, Measure.restrict_empty,
        lintegral_zero_measure, mul_zero]
  rw [← lintegral_indicator SpectralConvexity.isOpen_weylChamber.measurableSet]
  simp_rw [hL]
  rw [lintegral_lintegral_swap hFm.aemeasurable]
  simp_rw [hR]
  rw [lintegral_indicator SpectralConvexity.isOpen_weylChamber.measurableSet]

/-!
## The induction over the corners
-/

/-- **Gelfand–Tsetlin law of Lebesgue measure on `HermCoord n`**: for some `C > 0`, every
measurable `g ≥ 0` and every `k`,
`∫ g(λ(H(x))) e^{Σ_r k_r Re H(x)_{rr}} dx = C ∫_𝒞 Δ(λ) g(λ) gtMarginal k λ dλ`. -/
def GTLawStatement (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : (Fin n → ℝ) → ℝ≥0∞, Measurable g → ∀ k : Fin n → ℝ,
    ∫⁻ x : HermCoord n → ℝ, g (fun j => freshEigenvalue (hermOfCoord x) j) *
        ENNReal.ofReal (diagExp k (hermOfCoord x)) =
      ENNReal.ofReal C * ∫⁻ lam in weylChamber n,
        ENNReal.ofReal (SpectralConvexity.vandermonde lam) * g lam * gtMarginal k lam

theorem gtIntegrand_zero (k : Fin 0 → ℝ) (lam : Fin 0 → ℝ) (y : GTIndex 0 → ℝ) :
    gtIntegrand k (lam, y) = 1 := by
  classical
  have hmem : (lam, y) ∈ GTSet 0 := fun r _ hr _ => absurd hr (Nat.not_lt_zero _)
  unfold gtIntegrand
  rw [ite_eq_left hmem]
  simp

theorem gtMarginal_zero (k : Fin 0 → ℝ) (lam : Fin 0 → ℝ) : gtMarginal k lam = 1 := by
  unfold gtMarginal
  rw [lintegral_unique, gtIntegrand_zero]
  simp [volume_pi]

/-- **The Gelfand–Tsetlin law from the diagonal-corner bordered law**, by induction on the size
(`C_0 = 1`, `C_{n+1} = π^n C_n`). -/
theorem gtLaw_of_border (hD : DiagonalBorderLawStatement) (n : ℕ) : GTLawStatement n := by
  have hB : BorderEigenLawStatement := borderEigenLaw_of_diagonal complexUnitaryInvariance hD
  have hE : WeylEigenLawStatement := weylEigenLaw_of_border cornerFubini hB
  induction n with
  | zero =>
    refine ⟨1, one_pos, fun g _ k => ?_⟩
    have hch : weylChamber 0 = Set.univ :=
      Set.eq_univ_of_forall fun lam => fun i => Fin.elim0 i
    rw [hch, Measure.restrict_univ, lintegral_unique, lintegral_unique, gtMarginal_zero]
    simp only [diagExp, SpectralConvexity.vandermonde, volume_pi, Finset.univ_eq_empty,
      Finset.sum_empty, Finset.prod_empty, Real.exp_zero, ENNReal.ofReal_one, one_mul, mul_one,
      Measure.pi_univ]
    exact congrArg g (Subsingleton.elim _ _)
  | succ n ih =>
    obtain ⟨C, hCpos, hlaw⟩ := ih
    obtain ⟨Cw, -, hW⟩ := hE n
    refine ⟨Real.pi ^ n * C, by positivity, fun g hg k => ?_⟩
    set c := k (Fin.last n)
    set k' : Fin n → ℝ := fun r => k r.castSucc
    have hGm : Measurable fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ =>
        g (fun j => freshEigenvalue M j) * ENNReal.ofReal (diagExp k M) :=
      (hg.comp EigenDensity.measurable_freshEigs).mul
        (ENNReal.measurable_ofReal.comp (continuous_diagExp k).measurable)
    rw [cornerFubini n _ hGm]
    have hinner : ∀ y : HermCoord n → ℝ,
        (fun j => freshEigenvalue (hermOfCoord y) j) ∈ weylChamber n →
        ∫⁻ v : Fin n → ℂ, ∫⁻ a : ℝ,
          g (fun j => freshEigenvalue (borderHerm (hermOfCoord y) v a) j) *
            ENNReal.ofReal (diagExp k (borderHerm (hermOfCoord y) v a)) =
          borderAverage g c (fun j => freshEigenvalue (hermOfCoord y) j) *
            ENNReal.ofReal (diagExp k' (hermOfCoord y)) * ENNReal.ofReal (Real.pi ^ n) := by
      intro y hy
      set μ := fun j => freshEigenvalue (hermOfCoord y) j
      have h1 : ∀ (v : Fin n → ℂ) (a : ℝ),
          g (fun j => freshEigenvalue (borderHerm (hermOfCoord y) v a) j) *
            ENNReal.ofReal (diagExp k (borderHerm (hermOfCoord y) v a)) =
          ENNReal.ofReal (diagExp k' (hermOfCoord y)) *
            (g (fun j => freshEigenvalue (borderHerm (hermOfCoord y) v a) j) *
              topWeight c (fun j => freshEigenvalue (borderHerm (hermOfCoord y) v a) j) μ) := by
        intro v a
        simp only [topWeight, μ]
        rw [diagExp_borderHerm, ← border_entry_eq (isHermitian_hermOfCoord y) v a,
          ENNReal.ofReal_mul (diagExp_pos _ _).le]
        ring
      simp_rw [h1]
      simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [hB n (fun lam => g lam * topWeight c lam μ) (hg.mul (measurable_topWeight_left c μ)) _
        (isHermitian_hermOfCoord y) hy]
      unfold borderAverage
      ring
    rw [lintegral_congr_ae ((ae_mem_weylChamber hW).mono fun y hy => hinner y hy),
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hlaw _ (measurable_borderAverage hg c) k',
      lintegral_borderAverage_swap hg k, ENNReal.ofReal_mul (by positivity)]
    ring

end BlockBand.DeterminantScore.GelfandTsetlin

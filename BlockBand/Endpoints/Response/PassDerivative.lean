module

public import BlockBand.Endpoints.Response.PassDerivativePhysical

/-!
# The pass-derivative lemma, clause 1: uniform passage of the physical derivative

Statement: for every fixed bounded nonnegative `q` and `0 < s < 1`, the expected right difference
quotients of `F_L + F_R` differ from their expected zero-source derivatives by `O(κ^{s/2} + κ)`,
uniformly in `W`.

## Lean form (`passDerivative_clause1`)

* Objects: `portRatioSum b E x y W n q κ ω = F_L(κ) + F_R(κ)`, with absorber `iκ Q_q/W²` on the
  physical interior blocks; `x ≥ 0`, `0 ≤ y < 1`; `q : ℝ → ℝ` nonnegative and bounded (no
  continuity is needed for this clause).
* Zero-source derivative: the right derivative `derivWithin (κ ↦ F_L + F_R) (Ici 0) 0`; it
  exists almost surely and equals the explicit `portRatioDeriv` (`F'(T₀)[Ṫ]`, `∂𝕊 = -2η𝕊₀B_q`).
* Hypotheses: `FullSourceMomentsContract` and the fractional inverse moment
  `PathFractionalInverse`.

## Proof

The deterministic part is the exact signed source update, the contraction of
`(I + iκK_q/W²)⁻¹`, the trace-norm source error, and the first and second variations of `F_{x,y}`
on `0 ⪯ T ⪯ I`; together they give, pointwise,
`|(F(κ) - F(0))/κ - F'(0)| ≤ 2(4c₁η Tr B · min(2, κ‖K‖) + κ(36c₁ + 576c₂)η²(Tr B)²)`.
Then `Tr B · min(2, κ‖K‖) ≤ κ^{s/2}((Tr B)² + 4 q̄^s (‖G₀‖/W²)^s)/2` (`min(2,a)² ≤ 4a^s`,
`‖K‖ ≤ q̄‖G₀‖/W²`), and the two moment inputs close the bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix.Norms.L2Operator ENNReal NNReal

/-- The path fractional inverse moment, used as a hypothesis for clause 1 of the pass-derivative
lemma. Fixed `0 < b < 1/2`, bulk `-2 < E < 2`, `τ > 0`, path lengths `j W` with `j W / W → τ`, and
`0 < s < 1`; then there are `C = C_{s,τ}` and `W₀` such that for every `W ≥ W₀`, under the path
law `growthPathLaw W b`:
(a) the full path matrix with its two matched leads, `𝓜 = fullPathMatrix`, is almost surely
invertible (so that `G₀ = 𝓜⁻¹ = fullInverse` is an inverse at the real energy `E`); and
(b) `E (‖G₀‖/W²)^s ≤ C` (Euclidean operator norm). -/
def PathFractionalInverse : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ τ : ℝ, 0 < τ →
    ∀ j : ℕ → ℕ, Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ) →
    ∀ s : ℝ, 0 < s → s < 1 → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      (∀ᵐ ω ∂growthPathLaw W b, IsUnit (fullPathMatrix b E W (j W) ω).det) ∧
      ∫⁻ ω, ENNReal.ofReal ((‖fullInverse b E W (j W) ω‖ / (W : ℝ) ^ 2) ^ s)
          ∂growthPathLaw W b ≤ ENNReal.ofReal C

/-- The explicit zero-source derivative `F_L'(0) + F_R'(0)`:
`Σ_ports Re DF_{x,y}(T(0))[Ṫ]`, `Ṫ = -(ṡ*s₀ + s₀*ṡ)`, `ṡ = J*(-2η𝕊₀B_q)J`. -/
def portRatioDeriv (b E x y : ℝ) (W n : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) : ℝ :=
  ∑ i : Fin 2, (ratioDetDeriv x y
    (pencilPortDefect (etaZ b E) (leadInclusion W n) (fullPathMatrix b E W n ω)
      (sourceRoot W n q) (portInclusion W i) 0)
    (pencilPortDefectDeriv (etaZ b E) (leadInclusion W n) (fullPathMatrix b E W n ω)
      (sourceRoot W n q) (portInclusion W i))).re

/-!
### Pointwise
-/

theorem portRatioSum_eq {b E x y : ℝ} {W n : ℕ} {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (κ : ℝ)
    (ω : GrowthPath W) :
    portRatioSum b E x y W n q κ ω = ∑ i : Fin 2, ratioDet x y
      (pencilPortDefect (etaZ b E) (leadInclusion W n) (fullPathMatrix b E W n ω)
        (sourceRoot W n q) (portInclusion W i) κ) := by
  simp only [portRatioSum, Fin.sum_univ_two, absorbedScattering_eq hq, portDefect_eq,
    pencilPortDefect]

theorem abs_re_add_re_le (z₀ z₁ : ℂ) : |z₀.re + z₁.re| ≤ ‖z₀‖ + ‖z₁‖ :=
  (abs_add_le _ _).trans (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _))

/-- Pointwise facts for a sample with Hermitian GUE blocks (and, for the last three, an
invertible full path matrix). -/
theorem portRatio_pointwise {b E x y : ℝ} (hb : b ≤ 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) {W n : ℕ} {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t)
    {ω : GrowthPath W} (hH : ∀ k, (ω.1 k).IsHermitian) :
    (∀ κ : ℝ, 0 ≤ κ → |portRatioSum b E x y W n q κ ω| ≤ 2) ∧
    (IsUnit (fullPathMatrix b E W n ω).det →
      (∀ κ : ℝ, 0 ≤ κ → |portRatioSum b E x y W n q κ ω - portRatioSum b E x y W n q 0 ω -
          κ * portRatioDeriv b E x y W n q ω| ≤
        2 * (κ * (4 * ratioC1 x y * etaZ b E *
          (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
            (leadInclusion W n)).trace.re *
          min 2 (κ * ‖sourceKernel (fullPathMatrix b E W n ω) (sourceRoot W n q)‖) +
          κ * (36 * ratioC1 x y + 576 * ratioC2 x y) * etaZ b E ^ 2 *
            (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
              (leadInclusion W n)).trace.re ^ 2))) ∧
      HasDerivWithinAt (fun κ => portRatioSum b E x y W n q κ ω)
        (portRatioDeriv b E x y W n q ω) (Set.Ici 0) 0 ∧
      |portRatioDeriv b E x y W n q ω| ≤ 2 * (ratioC1 x y * (4 * etaZ b E *
        (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
          (leadInclusion W n)).trace.re))) := by
  have hη := etaZ_nonneg hb hE1 hE2
  have hW := fullPathMatrix_ward (b := b) (E := E) (n := n) hH
  have hJ := portInclusion_norm_le (W := W)
  refine ⟨fun κ hκ => ?_, fun hM => ⟨fun κ hκ => ?_, ?_, ?_⟩⟩
  · rw [portRatioSum_eq hq, Fin.sum_univ_two]
    refine (abs_re_add_re_le _ _).trans ?_
    have h0 := norm_ratioDetC_le_one hx hy0 hy1 (pencilPortDefect_band (R := sourceRoot W n q)
      hη hκ hW (hJ 0))
    have h1 := norm_ratioDetC_le_one hx hy0 hy1 (pencilPortDefect_band (R := sourceRoot W n q)
      hη hκ hW (hJ 1))
    linarith
  · rw [portRatioSum_eq hq, portRatioSum_eq hq, portRatioDeriv, Fin.sum_univ_two,
      Fin.sum_univ_two, Fin.sum_univ_two]
    have h0 := pencilRatio_pass_bound (R := sourceRoot W n q) hη hκ hx hy0 hy1 hM hW (hJ 0)
    have h1 := pencilRatio_pass_bound (R := sourceRoot W n q) hη hκ hx hy0 hy1 hM hW (hJ 1)
    have e : ∀ a₀ a₁ c₀ c₁ d₀ d₁ : ℂ, a₀.re + a₁.re - (c₀.re + c₁.re) - κ * (d₀.re + d₁.re) =
        (a₀ - c₀ - (κ : ℂ) * d₀).re + (a₁ - c₁ - (κ : ℂ) * d₁).re := by
      intro a₀ a₁ c₀ c₁ d₀ d₁
      simp only [Complex.sub_re, Complex.re_ofReal_mul]
      ring
    simp only [ratioDet]
    rw [e]
    refine (abs_re_add_re_le _ _).trans ?_
    linarith
  · refine hasDerivWithinAt_Ici_of_sq_bound (C := 2 * (4 * ratioC1 x y * etaZ b E *
        (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
          (leadInclusion W n)).trace.re *
        ‖sourceKernel (fullPathMatrix b E W n ω) (sourceRoot W n q)‖ +
        (36 * ratioC1 x y + 576 * ratioC2 x y) * etaZ b E ^ 2 *
          (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
            (leadInclusion W n)).trace.re ^ 2)) fun κ hκ => ?_
    rw [portRatioSum_eq hq, portRatioSum_eq hq, portRatioDeriv, Fin.sum_univ_two,
      Fin.sum_univ_two, Fin.sum_univ_two, Real.norm_eq_abs, smul_eq_mul]
    have h0 := pencilRatio_sq_bound (R := sourceRoot W n q) hη hx hy0 hy1 hM hW (hJ 0) κ hκ
    have h1 := pencilRatio_sq_bound (R := sourceRoot W n q) hη hx hy0 hy1 hM hW (hJ 1) κ hκ
    have e : ∀ a₀ a₁ c₀ c₁ d₀ d₁ : ℂ, a₀.re + a₁.re - (c₀.re + c₁.re) - κ * (d₀.re + d₁.re) =
        (a₀ - c₀ - (κ : ℂ) * d₀).re + (a₁ - c₁ - (κ : ℂ) * d₁).re := by
      intro a₀ a₁ c₀ c₁ d₀ d₁
      simp only [Complex.sub_re, Complex.re_ofReal_mul]
      ring
    simp only [ratioDet]
    rw [e]
    refine (abs_re_add_re_le _ _).trans ?_
    linarith
  · rw [portRatioDeriv, Fin.sum_univ_two]
    refine (abs_re_add_re_le _ _).trans ?_
    have hb0 : ∀ i : Fin 2, IsUnitBand (pencilPortDefect (etaZ b E) (leadInclusion W n)
        (fullPathMatrix b E W n ω) (sourceRoot W n q) (portInclusion W i) 0) :=
      fun i => pencilPortDefect_band hη le_rfl hW (hJ i)
    have h0 := norm_ratioDetDeriv_le hx hy0 hy1 (hb0 0)
      (pencilPortDefectDeriv_traceBound (R := sourceRoot W n q) hη hW (hJ 0))
    have h1 := norm_ratioDetDeriv_le hx hy0 hy1 (hb0 1)
      (pencilPortDefectDeriv_traceBound (R := sourceRoot W n q) hη hW (hJ 1))
    linarith

/-!
### Measurability
-/

section Measurability

theorem passDeriv_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun M : Matrix ι ι ℂ => M⁻¹) := by
  have : (fun M : Matrix ι ι ℂ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (measurable_inv.comp (continuous_id.matrix_det).measurable).smul
    (continuous_id.matrix_adjugate).measurable

theorem measurable_pathAt (W n : ℕ) : Measurable (fun ω : GrowthPath W => pathAt W n ω) := by
  unfold pathAt
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_fst
  · exact Measurable.of_eval fun i =>
      (continuous_id.matrix_conjTranspose).measurable.comp
        ((measurable_pi_apply _).comp measurable_snd)
  · refine Measurable.of_eval fun i => ?_
    fin_cases i <;> simp <;> exact (measurable_pi_apply _).comp measurable_snd

theorem measurable_fromBlocks {α l m n o : Type*} [MeasurableSpace α] {A : α → Matrix n l ℂ}
    {B : α → Matrix n m ℂ} {C : α → Matrix o l ℂ} {D : α → Matrix o m ℂ}
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D) :
    Measurable fun a => fromBlocks (A a) (B a) (C a) (D a) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  rcases x with x | x <;> rcases y with y | y
  · exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hA)
  · exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hB)
  · exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hC)
  · exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hD)

theorem measurable_fullPathMatrix (b E : ℝ) (W n : ℕ) :
    Measurable (fun ω : GrowthPath W => fullPathMatrix b E W n ω) := by
  have hP : Measurable (fun ω : PathSample W n => pathMatrix ω) := by
    unfold pathMatrix; fun_prop
  have hC : Measurable (fun ω : PathSample W n => pathPortCoupling ω) := by
    unfold pathPortCoupling; fun_prop
  have ha := measurable_pathAt W n
  unfold fullPathMatrix
  refine measurable_fromBlocks ((hP.comp ha).sub_const _) (hC.comp ha)
    ((continuous_id.matrix_conjTranspose).measurable.comp (hC.comp ha)) measurable_const

theorem measurable_ratioDet {w : Type*} [Fintype w] [DecidableEq w] (x y : ℝ) :
    Measurable (fun T : Matrix w w ℂ => ratioDet x y T) := by
  unfold ratioDet ratioDetC
  refine Complex.measurable_re.comp (Measurable.div ?_ ?_)
  · exact (show Continuous fun T : Matrix w w ℂ => (1 - (y : ℂ) • T).det by
      fun_prop).measurable
  · exact (show Continuous fun T : Matrix w w ℂ => (1 + (x : ℂ) • T).det by
      fun_prop).measurable

theorem measurable_ratioDetDeriv {w : Type*} [Fintype w] [DecidableEq w] (x y : ℝ) :
    Measurable (fun p : Matrix w w ℂ × Matrix w w ℂ => ratioDetDeriv x y p.1 p.2) := by
  have hmul : Measurable (fun p : Matrix w w ℂ × Matrix w w ℂ => p.1 * p.2) :=
    (show Continuous fun p : Matrix w w ℂ × Matrix w w ℂ => p.1 * p.2 by fun_prop).measurable
  have htr : Measurable (fun M : Matrix w w ℂ => M.trace) :=
    (show Continuous fun M : Matrix w w ℂ => M.trace by fun_prop).measurable
  have hC : Measurable (fun T : Matrix w w ℂ => ratioDetC x y T) := by
    unfold ratioDetC
    refine Measurable.div ?_ ?_
    · exact (show Continuous fun T : Matrix w w ℂ => (1 - (y : ℂ) • T).det by
        fun_prop).measurable
    · exact (show Continuous fun T : Matrix w w ℂ => (1 + (x : ℂ) • T).det by
        fun_prop).measurable
  have hA1 : Measurable (fun p : Matrix w w ℂ × Matrix w w ℂ => (1 - (y : ℂ) • p.1)⁻¹) :=
    passDeriv_measurable_inv.comp (show Continuous fun p : Matrix w w ℂ × Matrix w w ℂ =>
      1 - (y : ℂ) • p.1 by fun_prop).measurable
  have hA2 : Measurable (fun p : Matrix w w ℂ × Matrix w w ℂ => -(y : ℂ) • p.2) :=
    (show Continuous fun p : Matrix w w ℂ × Matrix w w ℂ => -(y : ℂ) • p.2 by
      fun_prop).measurable
  have hB1 : Measurable (fun p : Matrix w w ℂ × Matrix w w ℂ => (1 + (x : ℂ) • p.1)⁻¹) :=
    passDeriv_measurable_inv.comp (show Continuous fun p : Matrix w w ℂ × Matrix w w ℂ =>
      1 + (x : ℂ) • p.1 by fun_prop).measurable
  have hB2 : Measurable (fun p : Matrix w w ℂ × Matrix w w ℂ => (x : ℂ) • p.2) :=
    (show Continuous fun p : Matrix w w ℂ × Matrix w w ℂ => (x : ℂ) • p.2 by
      fun_prop).measurable
  have hA := htr.comp (hmul.comp (hA1.prodMk hA2))
  have hB := htr.comp (hmul.comp (hB1.prodMk hB2))
  unfold ratioDetDeriv
  exact (hC.comp measurable_fst).mul (hA.sub hB)

/-- `𝕊` as a function of `G = M⁻¹`. -/
def scatFromInv {ι p : Type*} [Fintype ι] [Fintype p] [DecidableEq p] (η : ℝ)
    (V : Matrix ι p ℂ) (G : Matrix ι ι ℂ) : Matrix p p ℂ :=
  1 - (((2 * η : ℝ) : ℂ) * Complex.I) • (Vᴴ * G * V)

/-- `Ṫ` as a function of `G = M⁻¹`. -/
def defectDerivFromInv {ι p w : Type*} [Fintype ι] [Fintype p] [DecidableEq p] [Fintype w]
    (η : ℝ)
    (V : Matrix ι p ℂ) (R : Matrix ι ι ℂ) (J : Matrix p w ℂ) (G : Matrix ι ι ℂ) :
    Matrix w w ℂ :=
  -((Jᴴ * (-(((2 * η : ℝ) : ℂ)) • (scatFromInv η V G * ((R * G * V)ᴴ * (R * G * V)))) * J)ᴴ *
      (Jᴴ * scatFromInv η V G * J) +
    (Jᴴ * scatFromInv η V G * J)ᴴ *
      (Jᴴ * (-(((2 * η : ℝ) : ℂ)) • (scatFromInv η V G * ((R * G * V)ᴴ * (R * G * V)))) * J))

variable {b E x y : ℝ} {W n : ℕ} {q : ℝ → ℝ}

theorem measurable_portRatioSum (hq : ∀ t, 0 ≤ q t) (κ : ℝ) :
    Measurable (fun ω => portRatioSum b E x y W n q κ ω) := by
  have hG : Measurable (fun ω => (absorbedPencil (fullPathMatrix b E W n ω)
      (sourceRoot W n q) κ)⁻¹) :=
    passDeriv_measurable_inv.comp ((measurable_fullPathMatrix b E W n).add_const _)
  have hT : ∀ i : Fin 2, Measurable (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      ratioDet x y (portDefectOf (scatFromInv (etaZ b E) (leadInclusion W n) G)
        (portInclusion W i))) := by
    intro i
    have hA : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
        portDefectOf (scatFromInv (etaZ b E) (leadInclusion W n) G) (portInclusion W i)) := by
      unfold portDefectOf scatFromInv; fun_prop
    exact (measurable_ratioDet x y).comp hA.measurable
  have e : (fun ω => portRatioSum b E x y W n q κ ω) = fun ω => ∑ i : Fin 2,
      ratioDet x y (portDefectOf (scatFromInv (etaZ b E) (leadInclusion W n)
        (absorbedPencil (fullPathMatrix b E W n ω) (sourceRoot W n q) κ)⁻¹)
          (portInclusion W i)) := by
    funext ω
    rw [portRatioSum_eq hq]
    rfl
  rw [e]
  exact Finset.measurable_sum _ fun i _ => (hT i).comp hG

theorem measurable_portRatioDeriv :
    Measurable (fun ω => portRatioDeriv b E x y W n q ω) := by
  have hG : Measurable (fun ω => (fullPathMatrix b E W n ω)⁻¹) :=
    passDeriv_measurable_inv.comp (measurable_fullPathMatrix b E W n)
  have hD : ∀ i : Fin 2, Measurable (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      (ratioDetDeriv x y
        (portDefectOf (scatFromInv (etaZ b E) (leadInclusion W n) G) (portInclusion W i))
        (defectDerivFromInv (etaZ b E) (leadInclusion W n) (sourceRoot W n q)
          (portInclusion W i) G)).re) := by
    intro i
    have hA : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
        portDefectOf (scatFromInv (etaZ b E) (leadInclusion W n) G) (portInclusion W i)) := by
      unfold portDefectOf scatFromInv; fun_prop
    have hB : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
        defectDerivFromInv (etaZ b E) (leadInclusion W n) (sourceRoot W n q)
          (portInclusion W i) G) := by
      unfold defectDerivFromInv scatFromInv; fun_prop
    have h1 := (measurable_ratioDetDeriv (w := Fin W) x y).comp
      (hA.measurable.prodMk hB.measurable)
    have h2 := Complex.measurable_re.comp h1
    exact h2
  have e : (fun ω => portRatioDeriv b E x y W n q ω) = fun ω => ∑ i : Fin 2,
      (ratioDetDeriv x y
        (portDefectOf (scatFromInv (etaZ b E) (leadInclusion W n) (fullPathMatrix b E W n ω)⁻¹)
          (portInclusion W i))
        (defectDerivFromInv (etaZ b E) (leadInclusion W n) (sourceRoot W n q)
          (portInclusion W i) (fullPathMatrix b E W n ω)⁻¹)).re := by
    funext ω
    simp only [portRatioDeriv, pencilPortDefect, absorbedPencil_zero]
    rfl
  rw [e]
  exact Finset.measurable_sum _ fun i _ => (hD i).comp hG

theorem measurable_pencilSourceGram_trace :
    Measurable (fun ω => (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
      (leadInclusion W n)).trace.re) := by
  have hG : Measurable (fun ω => (fullPathMatrix b E W n ω)⁻¹) :=
    passDeriv_measurable_inv.comp (measurable_fullPathMatrix b E W n)
  have hc : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      ((sourceRoot W n q * G * leadInclusion W n)ᴴ *
        (sourceRoot W n q * G * leadInclusion W n)).trace.re) := by fun_prop
  exact hc.measurable.comp hG

theorem measurable_clock :
    Measurable (fun ω => ((boundaryToInterior b E W n ω)ᴴ *
      boundaryToInterior b E W n ω).trace) := by
  have hG : Measurable (fun ω => (fullPathMatrix b E W n ω)⁻¹) :=
    passDeriv_measurable_inv.comp (measurable_fullPathMatrix b E W n)
  have hc : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      (G.toBlocks₁₂ᴴ * G.toBlocks₁₂).trace) := by
    unfold toBlocks₁₂; fun_prop
  exact hc.measurable.comp hG

theorem measurable_fullInverse_norm :
    Measurable (fun ω => ‖fullInverse b E W n ω‖) := by
  have hG : Measurable (fun ω => (fullPathMatrix b E W n ω)⁻¹) :=
    passDeriv_measurable_inv.comp (measurable_fullPathMatrix b E W n)
  exact continuous_norm.measurable.comp hG

end Measurability

/-!
### Almost-sure Hermitian blocks
-/

theorem passDeriv_gueSample_isHermitian {ι : Type*} [Fintype ι] (t : ℝ≥0) (X : ι × ι → ℂ) :
    (BlockBand.Internal.Contracts.CoareaPalm.gueSample t X).IsHermitian := by
  ext a c
  simp only [conjTranspose_apply, BlockBand.Internal.Contracts.CoareaPalm.gueSample, of_apply,
    star_mul', star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem ae_gueMeasure_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ≥0) :
    ∀ᵐ A ∂BlockBand.Internal.Contracts.CoareaPalm.gueMeasure ι t, A.IsHermitian := by
  have hm : Measurable (BlockBand.Internal.Contracts.CoareaPalm.gueSample (ι := ι) t) := by
    unfold BlockBand.Internal.Contracts.CoareaPalm.gueSample; fun_prop
  have hS : MeasurableSet {A : Matrix ι ι ℂ | A.IsHermitian} := by
    have : IsClosed {A : Matrix ι ι ℂ | Aᴴ = A} :=
      isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
    exact this.measurableSet
  unfold BlockBand.Internal.Contracts.CoareaPalm.gueMeasure
  exact (ae_map_iff hm.aemeasurable hS).2 (ae_of_all _ fun X => passDeriv_gueSample_isHermitian t X)

theorem passDeriv_isProbabilityMeasure_gue (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    IsProbabilityMeasure (BlockBand.Internal.Contracts.CoareaPalm.gueMeasure ι t) := by
  unfold BlockBand.Internal.Contracts.CoareaPalm.gueMeasure
    BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

theorem passDeriv_isProbabilityMeasure_ginibre (ι κ : Type*) [Fintype ι] [Fintype κ] (t : ℝ≥0) :
    IsProbabilityMeasure (ginibreMeasure ι κ t) := by
  unfold ginibreMeasure
  infer_instance

theorem passDeriv_isProbabilityMeasure_growthPathLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (growthPathLaw W b) := by
  have h1 : ∀ _ : ℕ, IsProbabilityMeasure (BlockBand.Internal.Contracts.CoareaPalm.gueMeasure
      (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) := fun _ => passDeriv_isProbabilityMeasure_gue _ _
  have h2 : ∀ _ : ℕ, IsProbabilityMeasure
      (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) :=
    fun _ => passDeriv_isProbabilityMeasure_ginibre _ _ _
  unfold growthPathLaw
  infer_instance

/-- Under the path law `growthPathLaw W b` every GUE block is almost surely Hermitian. -/
theorem ae_growthPath_isHermitian (W : ℕ) (b : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ k, (ω.1 k).IsHermitian := by
  have i1 : ∀ _ : ℕ, IsProbabilityMeasure (BlockBand.Internal.Contracts.CoareaPalm.gueMeasure
      (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) := fun _ => passDeriv_isProbabilityMeasure_gue _ _
  have i2 : ∀ _ : ℕ, IsProbabilityMeasure
      (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) :=
    fun _ => passDeriv_isProbabilityMeasure_ginibre _ _ _
  have h1 : ∀ᵐ a ∂(Measure.infinitePi fun _ : ℕ =>
      BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))),
      ∀ k, (a k).IsHermitian := by
    rw [ae_all_iff]
    intro k
    have hmap := @Measure.infinitePi_map_eval ℕ (fun _ => Matrix (Fin W) (Fin W) ℂ)
      (fun _ => inferInstance) (fun _ : ℕ =>
      BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W)
        (Real.toNNReal ((1 - 2 * b) / W))) i1 k
    refine ae_of_ae_map (measurable_pi_apply k).aemeasurable ?_
    rw [hmap]
    exact ae_gueMeasure_isHermitian _
  exact Measure.quasiMeasurePreserving_fst.ae h1

/-!
### Real-variable inequalities
-/

theorem min_two_sq_le {a s : ℝ} (ha : 0 ≤ a) (hs0 : 0 < s) (hs2 : s ≤ 2) :
    (min 2 a) ^ 2 ≤ 4 * a ^ s := by
  rcases le_or_gt a 2 with h | h
  · rw [min_eq_right h]
    rcases eq_or_lt_of_le ha with ha' | ha'
    · rw [← ha', Real.zero_rpow hs0.ne']; norm_num
    · have h1 : (a / 2) ^ (2 : ℝ) ≤ (a / 2) ^ s :=
        Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith) hs2
      rw [Real.div_rpow ha zero_le_two, Real.div_rpow ha zero_le_two] at h1
      have h2 : (1 : ℝ) ≤ 2 ^ s := Real.one_le_rpow one_le_two hs0.le
      have h3 : (a : ℝ) ^ (2 : ℝ) = a ^ 2 := by norm_cast
      have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
      rw [h3, h4] at h1
      have h5 : 0 ≤ a ^ s := Real.rpow_nonneg ha s
      have h6 : a ^ s / 2 ^ s ≤ a ^ s := div_le_self h5 h2
      have : a ^ 2 / 4 ≤ a ^ s := h1.trans h6
      linarith
  · rw [min_eq_left h.le]
    have : (1 : ℝ) ≤ a ^ s := Real.one_le_rpow (by linarith) hs0.le
    nlinarith

/-- `t · min(2, κk) ≤ κ^{s/2}(t² + 4k^s)/2` for `t, k ≥ 0`, `κ > 0`, `0 < s ≤ 2`. -/
theorem mul_min_two_le {t κ k s : ℝ} (hκ : 0 < κ) (hk : 0 ≤ k) (hs0 : 0 < s)
    (hs2 : s ≤ 2) : t * min 2 (κ * k) ≤ κ ^ (s / 2) * (t ^ 2 + 4 * k ^ s) / 2 := by
  set l := κ ^ (s / 2) with hl
  have hl0 : 0 < l := Real.rpow_pos_of_pos hκ _
  have hl2 : l ^ 2 = κ ^ s := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hκ.le]; norm_num
  set m := min 2 (κ * k)
  have hm0 : 0 ≤ m := le_min zero_le_two (mul_nonneg hκ.le hk)
  have hm2 : m ^ 2 ≤ 4 * (l ^ 2 * k ^ s) := by
    have := min_two_sq_le (mul_nonneg hκ.le hk) hs0 hs2
    rwa [Real.mul_rpow hκ.le hk, ← hl2] at this
  have hamgm : 2 * l * (t * m) ≤ l ^ 2 * t ^ 2 + m ^ 2 := by nlinarith [sq_nonneg (l * t - m)]
  have : 2 * l * (t * m) ≤ 2 * l * (l * (t ^ 2 + 4 * k ^ s) / 2) := by nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

theorem integrable_and_integral_le_of_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Measurable f) (h0 : ∀ a, 0 ≤ f a) {K : ℝ} (hK : 0 ≤ K)
    (h : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ENNReal.ofReal K) :
    Integrable f μ ∧ ∫ a, f a ∂μ ≤ K := by
  refine ⟨⟨hf.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_enorm]
    simp_rw [Real.enorm_eq_ofReal (h0 _)]
    exact h.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hf.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hK h

/-!
### The clause
-/

/-- **The pass-derivative lemma, clause 1**.
Law `growthPathLaw W b`, `0 < b < 1/2`, `-2 < E < 2`, path lengths `j W` with
`j W / W → τ > 0`; ratio parameters `x ≥ 0`, `0 ≤ y < 1`; a nonnegative bounded source profile
`q`;
`0 < s < 1`.
Then there are `C` and `W₀` such that for every `W ≥ W₀` and every `κ > 0`
the expected right difference quotient of `F_L + F_R` (`portRatioSum`) differs from the expected
zero-source right derivative by at most `C (κ^{s/2} + κ)`.
Hypotheses: `FullSourceMomentsContract` (field `clock`, `p = 2`) and `PathFractionalInverse`
(proved from `ConditionalBlockGUECount` as `pathFractionalInverse_of_contracts`).
-/
theorem passDerivative_clause1 (hMom : FullSourceMomentsContract)
    (hInv : PathFractionalInverse) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ τ : ℝ, 0 < τ → ∀ j : ℕ → ℕ, Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ) →
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y < 1 →
    ∀ q : ℝ → ℝ, (∀ t, 0 ≤ q t) → BddAbove (Set.range q) →
    ∀ s : ℝ, 0 < s → s < 1 →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ κ : ℝ, 0 < κ →
      |(∫ ω, (portRatioSum b E x y W (j W) q κ ω - portRatioSum b E x y W (j W) q 0 ω) / κ
          ∂growthPathLaw W b) -
        ∫ ω, derivWithin (fun κ' => portRatioSum b E x y W (j W) q κ' ω) (Set.Ici 0) 0
          ∂growthPathLaw W b| ≤ C * (κ ^ (s / 2) + κ) := by
  intro b hb0 hb1 E hE1 hE2 τ hτ j hj x y hx hy0 hy1 q hq hqb s hs0 hs1
  obtain ⟨Q, hQ⟩ := hqb
  have hQ' : ∀ t, q t ≤ Q := fun t => hQ ⟨t, rfl⟩
  have hQ0 : 0 ≤ Q := (hq 0).trans (hQ' 0)
  obtain ⟨C₁, W₁, hC₁⟩ := hMom.clock b hb0 hb1 E hE1 hE2 (τ + 1) 2 one_le_two
  obtain ⟨C₂, W₂, hC₂⟩ := hInv b hb0 hb1 E hE1 hE2 τ hτ j hj s hs0 hs1
  have hev : ∀ᶠ W : ℕ in atTop, (j W : ℝ) / W < τ + 1 :=
    hj.eventually (gt_mem_nhds (by linarith))
  obtain ⟨W₃, hW₃⟩ := eventually_atTop.1 hev
  have hb1' : b ≤ 1 := by linarith
  have hη : 0 ≤ etaZ b E := etaZ_nonneg hb1' hE1 hE2
  have hc₁ : 0 ≤ ratioC1 x y := ratioC1_nonneg hx hy0 hy1
  have hc₂ : 0 ≤ ratioC2 x y := ratioC2_nonneg x y
  set η := etaZ b E
  set c₁ := ratioC1 x y
  set c₂ := ratioC2 x y
  set C₁' := max C₁ 0
  set C₂' := max C₂ 0
  set K₁ := Q ^ 2 * (C₁' * (τ + 2)) ^ 2
  have hK₁ : 0 ≤ K₁ := by positivity
  have hC₁' : 0 ≤ C₁' := le_max_right _ _
  have hC₂' : 0 ≤ C₂' := le_max_right _ _
  have hQs : 0 ≤ Q ^ s := Real.rpow_nonneg hQ0 s
  refine ⟨4 * c₁ * η * K₁ + 16 * c₁ * η * Q ^ s * C₂' + 2 * (36 * c₁ + 576 * c₂) * η ^ 2 * K₁,
    max (max W₁ W₂) (max W₃ 1), fun W hW κ hκ => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWpos : (1 : ℝ) ≤ W := by
    exact_mod_cast le_trans (le_trans (le_max_right W₃ 1) (le_max_right _ _)) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hn : (j W : ℝ) ≤ (τ + 1) * W := by
    have := hW₃ W hW3
    rw [div_lt_iff₀ hW0] at this
    linarith
  have : IsProbabilityMeasure (growthPathLaw W b) :=
    passDeriv_isProbabilityMeasure_growthPathLaw W b
  set n := j W
  set μ := growthPathLaw W b
  set F : ℝ → GrowthPath W → ℝ := fun κ' ω => portRatioSum b E x y W n q κ' ω
  set h : GrowthPath W → ℝ := fun ω => portRatioDeriv b E x y W n q ω
  set TrB : GrowthPath W → ℝ := fun ω => (pencilSourceGram (fullPathMatrix b E W n ω)
    (sourceRoot W n q) (leadInclusion W n)).trace.re
  set g : GrowthPath W → ℝ := fun ω => ‖fullInverse b E W n ω‖ / (W : ℝ) ^ 2
  have hTrB0 : ∀ ω, 0 ≤ TrB ω := fun ω => by
    simp only [TrB, pencilSourceGram]
    rw [trace_conjTranspose_mul_self_re_eq_hsSq]; exact hsSq_nonneg _
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by positivity
  
  have hF2 : Integrable (fun ω => TrB ω ^ 2) μ ∧ ∫ ω, TrB ω ^ 2 ∂μ ≤ K₁ := by
    refine integrable_and_integral_le_of_lintegral (measurable_pencilSourceGram_trace.pow_const 2)
      (fun ω => sq_nonneg _) hK₁ ?_
    have hclock := hC₁ W hW1 n hn
    set f : GrowthPath W → ℂ := fun ω => (W : ℂ)⁻¹ *
      ((boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω).trace
    have hfm : AEStronglyMeasurable f μ :=
      (measurable_const.mul measurable_clock).aestronglyMeasurable
    have hL : ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal (C₁' * ((n : ℝ) + 1)) ^ (2 : ℝ) := by
      have h0 := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2) two_ne_zero hfm
      have h2 : ENNReal.ofReal 2 = ((2 : ℝ≥0) : ℝ≥0∞) := by simp
      rw [h2] at hclock
      have e2 : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num
      rw [e2] at h0
      rw [← h0]
      refine ENNReal.rpow_le_rpow (hclock.trans (ENNReal.ofReal_le_ofReal ?_)) (by norm_num)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hpt : ∀ ω, ENNReal.ofReal (TrB ω ^ 2) ≤
        ENNReal.ofReal (Q ^ 2 / (W : ℝ) ^ 2) * ‖f ω‖ₑ ^ (2 : ℝ) := by
      intro ω
      have h1 := pencilSourceGram_trace_le hq hQ' (fullPathMatrix b E W n ω)
      rw [trace_conjTranspose_mul_self_re_eq_hsSq] at h1
      have hf : ‖f ω‖ = hsSq (boundaryToInterior b E W n ω) / W := by
        simp only [f]
        rw [trace_conjTranspose_mul_self_eq_hsSq, norm_mul, norm_inv, Complex.norm_natCast,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsSq_nonneg _)]
        ring
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hf]
      have hb := hsSq_nonneg (boundaryToInterior b E W n ω)
      have h3 : TrB ω ≤ Q / (W : ℝ) ^ 2 * hsSq (boundaryToInterior b E W n ω) := h1
      have h4 : TrB ω ^ 2 ≤ (Q / (W : ℝ) ^ 2 * hsSq (boundaryToInterior b E W n ω)) ^ 2 :=
        pow_le_pow_left₀ (hTrB0 ω) h3 2
      have h5 : (hsSq (boundaryToInterior b E W n ω) / W) ^ (2 : ℝ) =
          (hsSq (boundaryToInterior b E W n ω) / W) ^ 2 := by norm_cast
      rw [h5]
      calc TrB ω ^ 2 ≤ (Q / (W : ℝ) ^ 2 * hsSq (boundaryToInterior b E W n ω)) ^ 2 := h4
        _ = Q ^ 2 / (W : ℝ) ^ 2 * (hsSq (boundaryToInterior b E W n ω) / W) ^ 2 := by
            field_simp
    calc ∫⁻ ω, ENNReal.ofReal (TrB ω ^ 2) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (Q ^ 2 / (W : ℝ) ^ 2) * ‖f ω‖ₑ ^ (2 : ℝ) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (Q ^ 2 / (W : ℝ) ^ 2) * ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Q ^ 2 / (W : ℝ) ^ 2) * ENNReal.ofReal (C₁' * ((n : ℝ) + 1)) ^ (2 : ℝ) :=
          by gcongr
      _ = ENNReal.ofReal (Q ^ 2 / (W : ℝ) ^ 2 * (C₁' * ((n : ℝ) + 1)) ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ← ENNReal.ofReal_mul (by positivity)]
          norm_cast
      _ ≤ ENNReal.ofReal K₁ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hnW : ((n : ℝ) + 1) / W ≤ τ + 2 := by
            rw [div_le_iff₀ hW0]; nlinarith
          have e : Q ^ 2 / (W : ℝ) ^ 2 * (C₁' * ((n : ℝ) + 1)) ^ 2 =
              Q ^ 2 * (C₁' * (((n : ℝ) + 1) / W)) ^ 2 := by field_simp
          rw [e]
          have h0 : 0 ≤ ((n : ℝ) + 1) / W := by positivity
          have : C₁' * (((n : ℝ) + 1) / W) ≤ C₁' * (τ + 2) :=
            mul_le_mul_of_nonneg_left hnW hC₁'
          have h6 : (C₁' * (((n : ℝ) + 1) / W)) ^ 2 ≤ (C₁' * (τ + 2)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) this 2
          exact mul_le_mul_of_nonneg_left h6 (sq_nonneg Q)
  -- fractional inverse moment
  obtain ⟨hInvae, hInvL⟩ := hC₂ W hW2
  have hF3 : Integrable (fun ω => g ω ^ s) μ ∧ ∫ ω, g ω ^ s ∂μ ≤ C₂' :=
    integrable_and_integral_le_of_lintegral
      ((measurable_fullInverse_norm.div_const _).pow_const s)
      (fun ω => Real.rpow_nonneg (hg0 ω) s) hC₂'
      (hInvL.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hgood : ∀ᵐ ω ∂μ, (∀ k, (ω.1 k).IsHermitian) ∧ IsUnit (fullPathMatrix b E W n ω).det :=
    (ae_growthPath_isHermitian W b).and hInvae
  -- pointwise bound
  set l := κ ^ (s / 2)
  have hl0 : 0 ≤ l := Real.rpow_nonneg hκ.le _
  set A := 4 * c₁ * η * l + 2 * (36 * c₁ + 576 * c₂) * η ^ 2 * κ
  set B := 16 * c₁ * η * Q ^ s * l
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hpt : ∀ ω, (∀ k, (ω.1 k).IsHermitian) → IsUnit (fullPathMatrix b E W n ω).det →
      |(F κ ω - F 0 ω) / κ - h ω| ≤ A * TrB ω ^ 2 + B * g ω ^ s := by
    intro ω hH hM
    obtain ⟨-, h2⟩ := portRatio_pointwise hb1' hE1 hE2 hx hy0 hy1 hq hH
    obtain ⟨hdiff, -, -⟩ := h2 hM
    have hd := hdiff κ hκ.le
    have e : (F κ ω - F 0 ω) / κ - h ω = (F κ ω - F 0 ω - κ * h ω) / κ := by
      field_simp
    rw [e, abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
    have hK := sourceKernel_norm_le hq hQ' (fullPathMatrix b E W n ω)
    set k := ‖sourceKernel (fullPathMatrix b E W n ω) (sourceRoot W n q)‖
    have hk0 : 0 ≤ k := norm_nonneg _
    have hkg : k ≤ Q * g ω := by
      have : Q / (W : ℝ) ^ 2 * ‖(fullPathMatrix b E W n ω)⁻¹‖ = Q * g ω := by
        simp only [g, fullInverse]; ring
      linarith
    have hks : k ^ s ≤ Q ^ s * g ω ^ s := by
      rw [← Real.mul_rpow hQ0 (hg0 ω)]
      exact Real.rpow_le_rpow hk0 hkg hs0.le
    have hm := mul_min_two_le (t := TrB ω) hκ hk0 hs0 (by linarith)
    have hd' : |F κ ω - F 0 ω - κ * h ω| ≤ 2 * (κ * (4 * c₁ * η * TrB ω * min 2 (κ * k) +
        κ * (36 * c₁ + 576 * c₂) * η ^ 2 * TrB ω ^ 2)) := hd
    refine hd'.trans ?_
    have hc : 0 ≤ 4 * c₁ * η := by positivity
    have h7 : 4 * c₁ * η * TrB ω * min 2 (κ * k) ≤
        4 * c₁ * η * (l * (TrB ω ^ 2 + 4 * (Q ^ s * g ω ^ s)) / 2) := by
      rw [mul_assoc (4 * c₁ * η)]
      refine mul_le_mul_of_nonneg_left (hm.trans ?_) hc
      have : l * (TrB ω ^ 2 + 4 * k ^ s) ≤ l * (TrB ω ^ 2 + 4 * (Q ^ s * g ω ^ s)) :=
        mul_le_mul_of_nonneg_left (by linarith) hl0
      linarith
    have h8 : 2 * (κ * (4 * c₁ * η * TrB ω * min 2 (κ * k) +
        κ * (36 * c₁ + 576 * c₂) * η ^ 2 * TrB ω ^ 2)) ≤
        2 * (κ * (4 * c₁ * η * (l * (TrB ω ^ 2 + 4 * (Q ^ s * g ω ^ s)) / 2) +
        κ * (36 * c₁ + 576 * c₂) * η ^ 2 * TrB ω ^ 2)) := by
      have := mul_le_mul_of_nonneg_left h7 hκ.le
      nlinarith
    refine h8.trans (le_of_eq ?_)
    simp only [A, B]
    ring
  -- integrability
  have hFm : ∀ κ', Measurable (F κ') := fun κ' => measurable_portRatioSum hq κ'
  have hΔm : Measurable (fun ω => (F κ ω - F 0 ω) / κ) :=
    ((hFm κ).sub (hFm 0)).div_const κ
  have hΔi : Integrable (fun ω => (F κ ω - F 0 ω) / κ) μ := by
    refine Integrable.mono' (integrable_const (4 / κ)) hΔm.aestronglyMeasurable ?_
    refine hgood.mono fun ω hω => ?_
    obtain ⟨h1, -⟩ := portRatio_pointwise hb1' hE1 hE2 hx hy0 hy1 hq hω.1
    have a1 := h1 κ hκ.le
    have a0 := h1 0 le_rfl
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hκ, div_le_div_iff_of_pos_right hκ]
    exact (abs_sub _ _).trans (by linarith)
  have hhi : Integrable h μ := by
    refine Integrable.mono' ((integrable_const (8 * c₁ * η)).add (hF2.1.const_mul (8 * c₁ * η)))
      measurable_portRatioDeriv.aestronglyMeasurable ?_
    refine hgood.mono fun ω hω => ?_
    obtain ⟨-, h2⟩ := portRatio_pointwise hb1' hE1 hE2 hx hy0 hy1 hq hω.1
    obtain ⟨-, -, hh⟩ := h2 hω.2
    rw [Real.norm_eq_abs]
    refine hh.trans ?_
    have : TrB ω ≤ 1 + TrB ω ^ 2 := by nlinarith [sq_nonneg (TrB ω - 1)]
    have hc : 0 ≤ 8 * c₁ * η := by positivity
    have h9 := mul_le_mul_of_nonneg_left this hc
    show 2 * (c₁ * (4 * η * TrB ω)) ≤ 8 * c₁ * η + 8 * c₁ * η * TrB ω ^ 2
    calc 2 * (c₁ * (4 * η * TrB ω)) = 8 * c₁ * η * TrB ω := by ring
      _ ≤ 8 * c₁ * η * (1 + TrB ω ^ 2) := h9
      _ = _ := by ring
  have hderiv : ∀ᵐ ω ∂μ, derivWithin (fun κ' => F κ' ω) (Set.Ici 0) 0 = h ω := by
    refine hgood.mono fun ω hω => ?_
    obtain ⟨-, h2⟩ := portRatio_pointwise hb1' hE1 hE2 hx hy0 hy1 hq hω.1
    exact (h2 hω.2).2.1.derivWithin (uniqueDiffWithinAt_Ici 0)
  -- conclusion
  have hdW : (∫ ω, derivWithin (fun κ' => F κ' ω) (Set.Ici 0) 0 ∂μ) = ∫ ω, h ω ∂μ :=
    integral_congr_ae hderiv
  show |(∫ ω, (F κ ω - F 0 ω) / κ ∂μ) - ∫ ω, derivWithin (fun κ' => F κ' ω) (Set.Ici 0) 0 ∂μ| ≤ _
  rw [hdW, ← integral_sub hΔi hhi]
  have hbd : Integrable (fun ω => A * TrB ω ^ 2 + B * g ω ^ s) μ :=
    (hF2.1.const_mul A).add (hF3.1.const_mul B)
  calc |∫ ω, ((F κ ω - F 0 ω) / κ - h ω) ∂μ|
      ≤ ∫ ω, |(F κ ω - F 0 ω) / κ - h ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (A * TrB ω ^ 2 + B * g ω ^ s) ∂μ :=
        integral_mono_ae (hΔi.sub hhi).abs hbd (hgood.mono fun ω hω => hpt ω hω.1 hω.2)
    _ = A * ∫ ω, TrB ω ^ 2 ∂μ + B * ∫ ω, g ω ^ s ∂μ := by
        rw [integral_add (hF2.1.const_mul A) (hF3.1.const_mul B), integral_const_mul,
          integral_const_mul]
    _ ≤ A * K₁ + B * C₂' :=
        add_le_add (mul_le_mul_of_nonneg_left hF2.2 hA0) (mul_le_mul_of_nonneg_left hF3.2 hB0)
    _ ≤ (4 * c₁ * η * K₁ + 16 * c₁ * η * Q ^ s * C₂' + 2 * (36 * c₁ + 576 * c₂) * η ^ 2 * K₁) *
          (l + κ) := by
        have e : A * K₁ + B * C₂' = l * (4 * c₁ * η * K₁ + 16 * c₁ * η * Q ^ s * C₂') +
            κ * (2 * (36 * c₁ + 576 * c₂) * η ^ 2 * K₁) := by
          simp only [A, B]; ring
        rw [e]
        have h1 : 0 ≤ 4 * c₁ * η * K₁ + 16 * c₁ * η * Q ^ s * C₂' := by positivity
        have h3 : 0 ≤ 2 * (36 * c₁ + 576 * c₂) * η ^ 2 * K₁ := by positivity
        have i1 : l * (4 * c₁ * η * K₁ + 16 * c₁ * η * Q ^ s * C₂') ≤
            l * (4 * c₁ * η * K₁ + 16 * c₁ * η * Q ^ s * C₂' +
              2 * (36 * c₁ + 576 * c₂) * η ^ 2 * K₁) :=
          mul_le_mul_of_nonneg_left (by linarith) hl0
        have i2 : κ * (2 * (36 * c₁ + 576 * c₂) * η ^ 2 * K₁) ≤
            κ * (4 * c₁ * η * K₁ + 16 * c₁ * η * Q ^ s * C₂' +
              2 * (36 * c₁ + 576 * c₂) * η ^ 2 * K₁) :=
          mul_le_mul_of_nonneg_left (by linarith) hκ.le
        calc _ ≤ l * (4 * c₁ * η * K₁ + 16 * c₁ * η * Q ^ s * C₂' +
              2 * (36 * c₁ + 576 * c₂) * η ^ 2 * K₁) +
            κ * (4 * c₁ * η * K₁ + 16 * c₁ * η * Q ^ s * C₂' +
              2 * (36 * c₁ + 576 * c₂) * η ^ 2 * K₁) := add_le_add i1 i2
          _ = _ := by ring

end BlockBand.Endpoints

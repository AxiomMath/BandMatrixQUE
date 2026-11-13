module

public import BlockBand.Transmission.Generator.ProdFixedAlg
public import BlockBand.Transmission.Generator.ModFour
public import BlockBand.Transmission.Generator.PowL2Tools

/-!
# The finite-`W` tested product `E[Φ(M^W_kM^W_l - Σ B/W)]`, bounded at one width

**`prod_fixedW`**: with `M^W_k = N^k + S_k` (`prodM_eq`), `S_k = Σ driftError`,
`|E[Φ(M^W_kM^W_l - Σ_r B(P_r)/W)]| ≤ B(β + σ_kσ_l + a_lσ_k + a_kσ_l + n a_ka_l + νσ_l + σ_kν + σ_kσ_l)`
where `β = Σ‖bracketError‖₁`, `σ_k = Σ‖driftError^k‖₂`, `a_k = √((Dk²/W)²C_g)` bounds
`‖A_k(P_r)/W‖₂`, and `ν = √(1 + 320n²M₄)` bounds `‖N‖₂` (`integral_modSum_pow_four_le`).
Only Hölder (`abs_integral_mul_mul_le`) and Minkowski (`eLpNorm_sum_le`) are used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Finset
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal

theorem abs_integral_mul_le_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Φ f : Ω → ℝ}
    {B : ℝ} (hΦ : AEStronglyMeasurable Φ μ) (hB : ∀ ω, |Φ ω| ≤ B) (hf : Integrable f μ) :
    |∫ ω, Φ ω * f ω ∂μ| ≤ B * (eLpNorm f 1 μ).toReal := by
  have hB' : ∀ᵐ ω ∂μ, ‖Φ ω‖ ≤ B := ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hB ω
  calc |∫ ω, Φ ω * f ω ∂μ| ≤ ∫ ω, |Φ ω * f ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, B * |f ω| ∂μ := integral_mono (hf.bdd_mul hΦ hB').abs (hf.abs.const_mul B)
        fun ω => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB ω) (abs_nonneg _)
    _ = B * (eLpNorm f 1 μ).toReal := by
        rw [integral_const_mul, eLpNorm_one_eq_lintegral_enorm,
          ← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]
        · simp [Real.norm_eq_abs]
        · exact hf.aestronglyMeasurable

theorem toReal_eLpNorm_two_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hi : Integrable (fun ω => f ω ^ 2) μ) {A : ℝ}
    (hI : ∫ ω, f ω ^ 2 ∂μ ≤ A) : (eLpNorm f 2 μ).toReal ≤ Real.sqrt A :=
  ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) (eLpNorm_two_le_sqrt hf hi hI)

theorem sum_mul_le_sum_mul_sum {s : Finset ℕ} {x y : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    ∑ i ∈ s, x i * y i ≤ (∑ i ∈ s, x i) * ∑ i ∈ s, y i := by
  rw [sum_mul]
  exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
    (single_le_sum (fun j _ => hy j) hi) (hx i)

section Fixed

variable {b E E' : ℝ} (hb : b < 1) (h1 : -2 < E') (h2 : E' < 2) (hD : 0 ≤ transportD0 b E)
  {W : ℕ}
include hb h1 h2 hD

theorem toReal_driftSum_le {k : ℕ} (hk : 1 ≤ k) (a n : ℕ) :
    (eLpNorm (driftSum b E E' W k a n) 2 (growthPathLaw W b)).toReal ≤
      ∑ u ∈ range n, (eLpNorm (driftError b E E' W k (a + u)) 2 (growthPathLaw W b)).toReal := by
  rw [← ENNReal.toReal_sum fun u _ => ((modBdd_driftError hb h1 h2 hD hk (a + u)).memLp
    2).eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun u _ =>
    ((modBdd_driftError hb h1 h2 hD hk (a + u)).memLp 2).eLpNorm_ne_top)
    (eLpNorm_sum_le one_le_two)

theorem toReal_condExp_le {k : ℕ} (hk : 1 ≤ k) (r : ℕ) {Cg : ℝ}
    (hg : ∫ ω, pathConductance b E' W r ω ^ 4 ∂growthPathLaw W b ≤ Cg) :
    (eLpNorm ((growthPathLaw W b)[modInc (fun r => pathPower b E' W k r) r |
        growthFiltration W r]) 2 (growthPathLaw W b)).toReal ≤
      (eLpNorm (driftError b E E' W k r) 2 (growthPathLaw W b)).toReal +
        Real.sqrt ((transportD0 b E * k ^ 2 / W) ^ 2 * Cg) := by
  set μ := growthPathLaw W b
  set D := transportD0 b E
  set A : GrowthPath W → ℝ := fun ω => transmissionDrift D k (pathPowers b E' W r ω) / W
  have he : μ[modInc (fun r => pathPower b E' W k r) r | growthFiltration W r] =
      driftError b E E' W k r + A := funext fun ω => condExp_powerIncrement_eq (E := E) k r ω
  have hA := modBdd_drift (W := W) hb h1 h2 hD k r
  have hdr := (modBdd_driftError (W := W) hb h1 h2 hD hk r).memLp 2
  have hgB : ModBdd μ (pathConductance b E' W r) :=
    ⟨(SourceMixing.measurable_pathConductance b E' r).aestronglyMeasurable, W,
      (pathPower_bound (k := 1) hb h1 h2 le_rfl r).mono fun ω h => by rwa [pathPower_one] at h⟩
  have hpt : ∀ᵐ ω ∂μ, A ω ^ 2 ≤ (D * k ^ 2 / W) ^ 2 * pathConductance b E' W r ω ^ 4 := by
    filter_upwards [pathPower_mem (W := W) hb h1 h2] with ω hm
    have hA' : |transmissionDrift D k (pathPowers b E' W r ω)| ≤
        D * k ^ 2 * pathConductance b E' W r ω ^ 2 :=
      abs_transmissionDrift_le hD k fun j hj1 _ => by
        obtain ⟨a0, a1, -⟩ := hm j r hj1
        show |pathPower b E' W j r ω| ≤ _
        rw [abs_of_nonneg a0]; exact a1
    have : |A ω| ≤ D * k ^ 2 / W * pathConductance b E' W r ω ^ 2 := by
      simp only [A]; rw [abs_div, Nat.abs_cast, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hA' (Nat.cast_nonneg _)
    calc A ω ^ 2 = |A ω| ^ 2 := (sq_abs _).symm
      _ ≤ (D * k ^ 2 / W * pathConductance b E' W r ω ^ 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = _ := by ring
  have hAI : ∫ ω, A ω ^ 2 ∂μ ≤ (D * k ^ 2 / W) ^ 2 * Cg := by
    refine (integral_mono_ae (hA.pow 2).integrable
      (((hgB.pow 4).integrable).const_mul _) hpt).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hg (sq_nonneg _)
  have hAn := toReal_eLpNorm_two_le hA.1 (hA.pow 2).integrable hAI
  rw [he]
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hdr.eLpNorm_ne_top,
    (hA.memLp 2).eLpNorm_ne_top⟩) (eLpNorm_add_le one_le_two)).trans ?_
  rw [ENNReal.toReal_add hdr.eLpNorm_ne_top (hA.memLp 2).eLpNorm_ne_top]
  exact add_le_add le_rfl hAn

omit hD in
theorem toReal_modSum_le {k : ℕ} (hk : 1 ≤ k) (a n : ℕ) {M₄ : ℝ}
    (h4 : ∀ u < n, ∫ ω, modInc (fun r => pathPower b E' W k r) (a + u) ω ^ 4
      ∂growthPathLaw W b ≤ M₄) :
    (eLpNorm (modSum (growthPathLaw W b) (growthFiltration W) (fun r => pathPower b E' W k r)
      a n) 2 (growthPathLaw W b)).toReal ≤ Real.sqrt (1 + 320 * (n : ℝ) ^ 2 * M₄) := by
  set μ := growthPathLaw W b
  have hX : ∀ r, StronglyMeasurable[growthFiltration W r] (pathPower b E' W k r) := fun r =>
    (measurable_pathPower_adapted b E' k r).stronglyMeasurable
  have hBk : ∀ r, ∀ᵐ ω ∂μ, |pathPower b E' W k r ω| ≤ W := fun r => pathPower_bound hb h1 h2 hk r
  set N := modSum μ (growthFiltration W) (fun r => pathPower b E' W k r) a n with hNdef
  have hN : ModBdd μ N := modBdd_modSum (growthFiltration W) hX hBk a n
  have h4N : ∫ ω, N ω ^ 4 ∂μ ≤ 320 * (n : ℝ) ^ 2 * M₄ :=
    integral_modSum_pow_four_le (growthFiltration W) hX hBk a n h4
  have hI2 : Integrable (fun ω => N ω ^ 2) μ := (hN.pow 2).integrable
  have hI4 : Integrable (fun ω => N ω ^ 4) μ := (hN.pow 4).integrable
  refine toReal_eLpNorm_two_le hN.1 hI2 ?_
  calc ∫ ω, N ω ^ 2 ∂μ ≤ ∫ ω, (1 + N ω ^ 4) ∂μ :=
        integral_mono hI2 ((integrable_const 1).add hI4) fun ω => by
          have := sq_nonneg (N ω ^ 2 - 1)
          nlinarith
    _ ≤ 1 + 320 * (n : ℝ) ^ 2 * M₄ := by
        rw [integral_add (integrable_const _) hI4, integral_const]
        simp only [probReal_univ, one_smul]
        linarith

/-- **The tested product at one width.** -/
theorem prod_fixedW {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (a n : ℕ) {Φ : GrowthPath W → ℝ}
    (hΦ : Measurable[growthSigma W a] Φ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ ω, |Φ ω| ≤ B)
    {M₄ Cg : ℝ}
    (h4k : ∀ u < n, ∫ ω, modInc (fun r => pathPower b E' W k r) (a + u) ω ^ 4
      ∂growthPathLaw W b ≤ M₄)
    (h4l : ∀ u < n, ∫ ω, modInc (fun r => pathPower b E' W l r) (a + u) ω ^ 4
      ∂growthPathLaw W b ≤ M₄)
    (hg : ∀ u < n, ∫ ω, pathConductance b E' W (a + u) ω ^ 4 ∂growthPathLaw W b ≤ Cg) :
    let β := ∑ u ∈ range n, (eLpNorm (bracketError b E E' W k l (a + u)) 1 (growthPathLaw W b)).toReal
    let σk := ∑ u ∈ range n, (eLpNorm (driftError b E E' W k (a + u)) 2 (growthPathLaw W b)).toReal
    let σl := ∑ u ∈ range n, (eLpNorm (driftError b E E' W l (a + u)) 2 (growthPathLaw W b)).toReal
    let ak := Real.sqrt ((transportD0 b E * k ^ 2 / W) ^ 2 * Cg)
    let al := Real.sqrt ((transportD0 b E * l ^ 2 / W) ^ 2 * Cg)
    let ν := Real.sqrt (1 + 320 * (n : ℝ) ^ 2 * M₄)
    |∫ ω, Φ ω * (prodM b E E' W k a (a + n) ω * prodM b E E' W l a (a + n) ω -
        bracketSum b E E' W k l a (a + n) ω) ∂growthPathLaw W b| ≤
      B * (β + (σk * σl + al * σk + ak * σl + n * (ak * al)) + ν * σl + σk * ν + σk * σl) := by
  set μ := growthPathLaw W b
  intro β σk σl ak al ν
  set F := growthFiltration W
  set Nk := modSum μ F (fun r => pathPower b E' W k r) a n
  set Nl := modSum μ F (fun r => pathPower b E' W l r) a n
  set Sk := driftSum b E E' W k a n
  set Sl := driftSum b E E' W l a n
  set dk : ℕ → GrowthPath W → ℝ := fun u => μ[modInc (fun r => pathPower b E' W k r) (a + u) | F (a + u)]
  set dl : ℕ → GrowthPath W → ℝ := fun u => μ[modInc (fun r => pathPower b E' W l r) (a + u) | F (a + u)]
  have hΦm : Measurable Φ := hΦ.mono (growthSigma_le W a) le_rfl
  have hΦb : ∀ᵐ ω ∂μ, ‖Φ ω‖ ≤ B := ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hB ω
  have hΦa : ∀ᵐ ω ∂μ, |Φ ω| ≤ B := ae_of_all _ hB
  have hXk : ∀ r, StronglyMeasurable[F r] (pathPower b E' W k r) := fun r =>
    (measurable_pathPower_adapted b E' k r).stronglyMeasurable
  have hXl : ∀ r, StronglyMeasurable[F r] (pathPower b E' W l r) := fun r =>
    (measurable_pathPower_adapted b E' l r).stronglyMeasurable
  have hNk := modBdd_modSum F hXk (fun r => pathPower_bound hb h1 h2 hk r) a n
  have hNl := modBdd_modSum F hXl (fun r => pathPower_bound hb h1 h2 hl r) a n
  have hSk := modBdd_driftSum (W := W) hb h1 h2 hD hk a n
  have hSl := modBdd_driftSum (W := W) hb h1 h2 hD hl a n
  have hBs : ModBdd μ (bracketSum b E E' W k l a (a + n)) := by
    have : bracketSum b E E' W k l a (a + n) = ∑ u ∈ range n, fun ω =>
        transmissionBracket (transportD0 b E) k l (pathPowers b E' W (a + u) ω) / W := by
      funext ω; simp [bracketSum, sum_Ico_eq_sum_range, Finset.sum_apply]
    rw [this]; exact modBdd_sum (fun u => modBdd_bracket hb h1 h2 hD hk (a + u)) n
  have int : ∀ {f : GrowthPath W → ℝ}, ModBdd μ f → Integrable (fun ω => Φ ω * f ω) μ :=
    fun hf => hf.integrable.bdd_mul hΦm.aestronglyMeasurable hΦb
  -- expansion
  have hexp : ∫ ω, Φ ω * (prodM b E E' W k a (a + n) ω * prodM b E E' W l a (a + n) ω -
      bracketSum b E E' W k l a (a + n) ω) ∂μ =
      (∫ ω, Φ ω * (Nk ω * Nl ω) ∂μ - ∫ ω, Φ ω * bracketSum b E E' W k l a (a + n) ω ∂μ) +
      ∫ ω, Φ ω * (Nk ω * Sl ω) ∂μ + ∫ ω, Φ ω * (Sk ω * Nl ω) ∂μ + ∫ ω, Φ ω * (Sk ω * Sl ω) ∂μ := by
    have i1 : Integrable (fun ω => Φ ω * (Nk ω * Nl ω)) μ := int (hNk.mul hNl)
    have i2 : Integrable (fun ω => Φ ω * bracketSum b E E' W k l a (a + n) ω) μ := int hBs
    have i3 : Integrable (fun ω => Φ ω * (Nk ω * Sl ω)) μ := int (hNk.mul hSl)
    have i4 : Integrable (fun ω => Φ ω * (Sk ω * Nl ω)) μ := int (hSk.mul hNl)
    have i5 : Integrable (fun ω => Φ ω * (Sk ω * Sl ω)) μ := int (hSk.mul hSl)
    have i12 : Integrable (fun ω => Φ ω * (Nk ω * Nl ω) -
        Φ ω * bracketSum b E E' W k l a (a + n) ω) μ := i1.sub i2
    have i123 : Integrable (fun ω => Φ ω * (Nk ω * Nl ω) -
        Φ ω * bracketSum b E E' W k l a (a + n) ω + Φ ω * (Nk ω * Sl ω)) μ := i12.add i3
    have i1234 : Integrable (fun ω => Φ ω * (Nk ω * Nl ω) -
        Φ ω * bracketSum b E E' W k l a (a + n) ω + Φ ω * (Nk ω * Sl ω) +
          Φ ω * (Sk ω * Nl ω)) μ := i123.add i4
    rw [← integral_sub i1 i2, ← integral_add i12 i3, ← integral_add i123 i4,
      ← integral_add i1234 i5]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [prodM_eq (E := E) k a n ω, prodM_eq (E := E) l a n ω, Nk, Nl, Sk, Sl]
    ring
  rw [hexp, prod_main_eq hb h1 h2 hD hk hl a n hΦ hB]
  -- the bounds
  have hβ : |∑ u ∈ range n, ∫ ω, Φ ω * bracketError b E E' W k l (a + u) ω ∂μ| ≤ B * β := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    exact sum_le_sum fun u _ => abs_integral_mul_le_one hΦm.aestronglyMeasurable hB
      (modBdd_bracketError hb h1 h2 hD hk hl (a + u)).integrable
  have hdk : ∀ u < n, (eLpNorm (dk u) 2 μ).toReal ≤
      (eLpNorm (driftError b E E' W k (a + u)) 2 μ).toReal + ak := fun u hu =>
    toReal_condExp_le hb h1 h2 hD hk (a + u) (hg u hu)
  have hdl : ∀ u < n, (eLpNorm (dl u) 2 μ).toReal ≤
      (eLpNorm (driftError b E E' W l (a + u)) 2 μ).toReal + al := fun u hu =>
    toReal_condExp_le hb h1 h2 hD hl (a + u) (hg u hu)
  have hmk : ∀ u, MemLp (dk u) 2 μ := fun u => (modBdd_condExp_modInc F
    (fun r => pathPower_bound hb h1 h2 hk r) (a + u)).memLp 2
  have hml : ∀ u, MemLp (dl u) 2 μ := fun u => (modBdd_condExp_modInc F
    (fun r => pathPower_bound hb h1 h2 hl r) (a + u)).memLp 2
  have hak : 0 ≤ ak := Real.sqrt_nonneg _
  have hal : 0 ≤ al := Real.sqrt_nonneg _
  have he0 : ∀ (j : ℕ) (u : ℕ), 0 ≤ (eLpNorm (driftError b E E' W j (a + u)) 2 μ).toReal :=
    fun _ _ => ENNReal.toReal_nonneg
  have hdd : |∑ u ∈ range n, ∫ ω, Φ ω * (dk u ω * dl u ω) ∂μ| ≤
      B * (σk * σl + al * σk + ak * σl + n * (ak * al)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ u ∈ range n, |∫ ω, Φ ω * (dk u ω * dl u ω) ∂μ|
        ≤ ∑ u ∈ range n, B * (((eLpNorm (driftError b E E' W k (a + u)) 2 μ).toReal + ak) *
            ((eLpNorm (driftError b E E' W l (a + u)) 2 μ).toReal + al)) := by
          refine sum_le_sum fun u hu => ?_
          have hu' := mem_range.mp hu
          refine (abs_integral_mul_mul_le hB0 hΦm.aestronglyMeasurable hΦa (hmk u)
            (hml u)).trans ?_
          rw [ENNReal.toReal_mul]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hdk u hu') (hdl u hu')
            ENNReal.toReal_nonneg (add_nonneg (he0 k u) hak)) hB0
      _ = B * (∑ u ∈ range n, (eLpNorm (driftError b E E' W k (a + u)) 2 μ).toReal *
            (eLpNorm (driftError b E E' W l (a + u)) 2 μ).toReal + al * σk + ak * σl +
            n * (ak * al)) := by
          rw [← mul_sum]; congr 1
          rw [show (n : ℝ) * (ak * al) = ∑ _u ∈ range n, ak * al by simp]
          simp only [σk, σl, mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun u _ => by ring
      _ ≤ _ := by
          gcongr
          exact sum_mul_le_sum_mul_sum (fun u => he0 k u) (fun u => he0 l u)
  have hσk := toReal_driftSum_le (W := W) hb h1 h2 hD hk a n
  have hσl := toReal_driftSum_le (W := W) hb h1 h2 hD hl a n
  have hνk := toReal_modSum_le (W := W) hb h1 h2 hk a n h4k
  have hνl := toReal_modSum_le (W := W) hb h1 h2 hl a n h4l
  have hpair : ∀ {f g : GrowthPath W → ℝ} {x y : ℝ}, ModBdd μ f → ModBdd μ g →
      (eLpNorm f 2 μ).toReal ≤ x → (eLpNorm g 2 μ).toReal ≤ y →
      |∫ ω, Φ ω * (f ω * g ω) ∂μ| ≤ B * (x * y) := by
    intro f g x y hf hg' hx hy
    refine (abs_integral_mul_mul_le hB0 hΦm.aestronglyMeasurable hΦa (hf.memLp 2)
      (hg'.memLp 2)).trans ?_
    rw [ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hx hy ENNReal.toReal_nonneg
      (ENNReal.toReal_nonneg.trans hx)) hB0
  have c1 := hpair hNk hSl hνk hσl
  have c2 := hpair hSk hNl hσk hνl
  have c3 := hpair hSk hSl hσk hσl
  have t1 := abs_sub _ _ |>.trans (add_le_add hβ hdd)
  calc _ ≤ |∑ u ∈ range n, ∫ ω, Φ ω * bracketError b E E' W k l (a + u) ω ∂μ -
        ∑ u ∈ range n, ∫ ω, Φ ω * (dk u ω * dl u ω) ∂μ| + |∫ ω, Φ ω * (Nk ω * Sl ω) ∂μ| +
        |∫ ω, Φ ω * (Sk ω * Nl ω) ∂μ| + |∫ ω, Φ ω * (Sk ω * Sl ω) ∂μ| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ B * β + B * (σk * σl + al * σk + ak * σl + n * (ak * al)) + B * (ν * σl) +
        B * (σk * ν) + B * (σk * σl) := by gcongr
    _ = _ := by ring

end Fixed

end BlockBand.Transmission.Generator

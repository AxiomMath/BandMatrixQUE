module

public import BlockBand.Critical.MatrixClosing.Boundary.Kernel
public import BlockBand.Critical.MatrixClosing.Boundary.CircleLaw
public import BlockBand.Critical.MatrixClosing.MiddleShift.Main
public import BlockBand.Critical.MatrixClosing.Reduction

/-!
# Matrix closing: the boundary clause `CollarBoundaryClause`

* **`collarBoundaryClause_of_middleShift : MiddleShiftBoundaryMeanStatement →
  CollarBoundaryClause`**.
* **`collarBoundaryClause_of_exactBoundaryMean : ExactBoundaryMeanContract →
  CollarBoundaryClause`** (through `middleShiftBoundaryMean_of_exactBoundaryMean`).
* `matrixClosing_of_poles_mean : CollarPolesClause → CollarMeanClause →
  ExactBoundaryMeanContract → MatrixClosingStatement`: the reduction with the boundary clause
  discharged. `CollarPolesClause` fails at `r = 0`, so this form is vacuous; the reduction used
  is `Poles.matrixClosing_of_clauses_pos`.

Proof: along an old sequence, a.s. `Re v*F_W(x)v = 2‖v‖² Im q`, `q = u*(I - U_s r)⁻¹u`,
`u = ‖v‖⁻¹Jv`, `s = x/(Wρ)` (`re_quad_closingMatrix`, `ae_collarFunction_eval_eq`); `Re q = 1/2`
and `c(2 Im q) = ζ = 1 - q⁻¹`, `c(t) = (t+i)/(t-i)`. For the rank-one damped twist
`X' = twistOld b e w u X` (`-Im X' ⪰ 0`, `d(X') ≤ d(X) + 1/(ηW)`, `g(r') = 1 - |w|²`), the
middle-shifted kernel at `X'` is the scalar Poisson kernel `P(wζ_t)`, so the middle-shift bound
gives `|E P(wζ) - 1| ≤ |C|{d(X) + 1/(η_min W) + |ε_W| + W^{-1/8} + W^{-1/4} + |s|} → 0` uniformly
in `‖w‖ < 1`. `tendsto_cauchy_of_poisson` (tightness, Fourier moments of the Cayley phase
and Mathlib `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`) gives
`Re v*F v/‖v‖² ⇒ Cauchy(0,1)`; dilation (`cauchyMeasure_map_mul`) gives `Cauchy(0,‖v‖²)`; `v = 0`
is `δ₀`.

Law: `collarLaw W b` along an old sequence. The only hypothesis is
`MiddleShiftBoundaryMeanStatement` (equivalently, through
`middleShiftBoundaryMean_of_exactBoundaryMean`, `ExactBoundaryMeanContract`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Boundary

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Herglotz
open scoped ComplexOrder ComplexConjugate NNReal

variable {W : ℕ}

theorem star_dotProduct_self_eq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum,
    Complex.ofReal_pow]

/-- The normalized frame vector `u = ‖v‖⁻¹ Jv` is a unit vector. -/
theorem frameVec_unit {r : ℕ} {J : Matrix (Fin 2 × Fin W) (Fin r) ℂ} (hJ : Jᴴ * J = 1)
    {v : Fin r → ℂ} (hγ : 0 < ∑ i, ‖v i‖ ^ 2) :
    star ((((Real.sqrt (∑ i, ‖v i‖ ^ 2))⁻¹ : ℝ) : ℂ) • (J *ᵥ v)) ⬝ᵥ
      ((((Real.sqrt (∑ i, ‖v i‖ ^ 2))⁻¹ : ℝ) : ℂ) • (J *ᵥ v)) = 1 := by
  set γ := ∑ i, ‖v i‖ ^ 2
  have hs : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt hγ.le
  have hs0 : Real.sqrt γ ≠ 0 := (Real.sqrt_pos.2 hγ).ne'
  rw [star_smul, smul_dotProduct, dotProduct_smul, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, hJ, one_mulVec, star_dotProduct_self_eq]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have : (Real.sqrt γ)⁻¹ * ((Real.sqrt γ)⁻¹ * γ) = 1 := by
    rw [show (Real.sqrt γ)⁻¹ * ((Real.sqrt γ)⁻¹ * γ) = γ / Real.sqrt γ ^ 2 by ring, hs,
      div_self hγ.ne']
  rw [this, Complex.ofReal_one]

/-- **The quadratic form of the closing matrix**: `Re v*𝒞v = 2‖v‖² Im q`, `q = u*(I - U_s r)⁻¹u`,
`u = ‖v‖⁻¹Jv` (`-iJ*{2(I - U_s r)⁻¹ - I}J`). -/
theorem re_quad_closingMatrix {r : ℕ} (b e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {J : Matrix (Fin 2 × Fin W) (Fin r) ℂ} (hJ : Jᴴ * J = 1) {v : Fin r → ℂ}
    (hγ : 0 < ∑ i, ‖v i‖ ^ 2) (ω : CollarSample W) :
    (star v ⬝ᵥ (closingMatrix b e s X J ω *ᵥ v)).re =
      2 * (∑ i, ‖v i‖ ^ 2) * (closedQuad b e s 1 X
        ((((Real.sqrt (∑ i, ‖v i‖ ^ 2))⁻¹ : ℝ) : ℂ) • (J *ᵥ v)) ω).im := by
  set γ := ∑ i, ‖v i‖ ^ 2
  set σ := Real.sqrt γ
  set u := (((σ)⁻¹ : ℝ) : ℂ) • (J *ᵥ v)
  have hs : σ ^ 2 = γ := Real.sq_sqrt hγ.le
  have hs0 : σ ≠ 0 := (Real.sqrt_pos.2 hγ).ne'
  have hJv : J *ᵥ v = (σ : ℂ) • u := by
    simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0, Complex.ofReal_one,
      one_smul]
  have hu := frameVec_unit (W := W) hJ hγ
  set R := (1 - closedScattering b e s X ω)⁻¹
  have hq : closedQuad b e s 1 X u ω = star u ⬝ᵥ (R *ᵥ u) := by
    simp [closedQuad, R]
  rw [hq]
  have e1 : star v ⬝ᵥ (closingMatrix b e s X J ω *ᵥ v) =
      (-Complex.I) * ((γ : ℂ) * (2 * (star u ⬝ᵥ (R *ᵥ u)) - 1)) := by
    rw [closingMatrix, smul_mulVec, dotProduct_smul, smul_eq_mul, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hJv]
    change (-Complex.I) * (star ((σ : ℂ) • u) ⬝ᵥ
      (((2 : ℂ) • R - 1) *ᵥ ((σ : ℂ) • u))) = _
    rw [star_smul, smul_dotProduct, mulVec_smul, dotProduct_smul, sub_mulVec, smul_mulVec,
      one_mulVec, dotProduct_sub, dotProduct_smul, hu]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    rw [← hs]; push_cast; ring
  rw [e1]
  simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  norm_num
  ring

/-- `Cauchy(0,1)` dilated by `γ ≥ 0` is `Cauchy(0,γ)` (characteristic functions). -/
theorem cauchyMeasure_map_mul (γ : ℝ≥0) :
    (ProbabilityTheory.cauchyMeasure 0 1).map (fun t => (γ : ℝ) * t) =
      ProbabilityTheory.cauchyMeasure 0 γ := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_mul, BlockBand.Critical.Herglotz.charFun_cauchyMeasure,
    BlockBand.Critical.Herglotz.charFun_cauchyMeasure, abs_mul,
    abs_of_nonneg (NNReal.coe_nonneg γ)]
  simp

/-- Dilation of a standard Cauchy limit in law. -/
theorem tendstoInDistribution_mul_cauchy {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {Y : ∀ N, Ω N → ℝ}
    (h : TendstoInDistribution Y atTop id P (ProbabilityTheory.cauchyMeasure 0 1)) (γ : ℝ≥0) :
    TendstoInDistribution (fun N ω => (γ : ℝ) * Y N ω) atTop id P
      (ProbabilityTheory.cauchyMeasure 0 γ) := by
  have hg : Continuous fun t : ℝ => (γ : ℝ) * t := continuous_const.mul continuous_id
  have h2 := h.continuous_comp hg
  refine ⟨h2.forall_aemeasurable, aemeasurable_id, ?_⟩
  have h3 := h2.tendsto
  have e2 : (⟨(ProbabilityTheory.cauchyMeasure 0 γ).map id, inferInstance⟩ : ProbabilityMeasure ℝ) =
      ⟨(ProbabilityTheory.cauchyMeasure 0 1).map ((fun t => (γ : ℝ) * t) ∘ id), inferInstance⟩ := by
    apply Subtype.ext
    simp only [Measure.map_id, Function.comp_id, cauchyMeasure_map_mul]
  rw [e2]
  exact h3

/-- The constant zero converges in law to `Cauchy(0,0) = δ₀`. -/
theorem tendstoInDistribution_zero_cauchy {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {Y : ∀ N, Ω N → ℝ}
    (hY : ∀ N ω, Y N ω = 0) {γ : ℝ≥0} (hγ : γ = 0) :
    TendstoInDistribution Y atTop id P (ProbabilityTheory.cauchyMeasure 0 γ) := by
  subst hγ
  have hY' : Y = fun _ _ => 0 := funext fun N => funext fun ω => hY N ω
  subst hY'
  refine ⟨fun N => aemeasurable_const, aemeasurable_id, ?_⟩
  have e : ∀ N, ((⟨(P N).map (fun _ => (0 : ℝ)), inferInstance⟩ :
      ProbabilityMeasure ℝ)) = ⟨(ProbabilityTheory.cauchyMeasure 0 0).map id,
        inferInstance⟩ := by
    intro N
    apply Subtype.ext
    simp only [Measure.map_id, Measure.map_const, measure_univ, one_smul,
      ProbabilityTheory.cauchyMeasure_zero_scale]
  simp only [e]
  exact tendsto_const_nhds

/-- A uniform lower bound for the semicircle density on the bulk. -/
theorem semicircleDensity_ge {κ e : ℝ} (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    0 < Real.sqrt (4 - (2 - κ) ^ 2) / (2 * Real.pi) ∧
      Real.sqrt (4 - (2 - κ) ^ 2) / (2 * Real.pi) ≤ Parameters.semicircleDensity e := by
  have hκ2 : κ ≤ 2 := by linarith [he.1, he.2]
  have hpos : 0 < 4 - (2 - κ) ^ 2 := by nlinarith
  refine ⟨div_pos (Real.sqrt_pos.2 hpos) (by positivity), ?_⟩
  unfold Parameters.semicircleDensity
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt
    (by linarith [BlockBand.Layers.sq_le_of_mem_bulkInterval he])) (by positivity)

/-- The arithmetic of the error term: `C(a + ε + p + gq + |s|) ≤ |C|(A + |ε| + p + q + |s|)`. -/
theorem error_arith {C a A e p q g s : ℝ} (ha : 0 ≤ a) (haA : a ≤ A) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hg : |g| ≤ 1) : C * (a + e + p + g * q + abs s) ≤ |C| * (A + abs e + p + q + abs s) := by
  have hgq : abs (g * q) ≤ q := by
    rw [abs_mul, abs_of_nonneg hq]; nlinarith [abs_nonneg g]
  have h1 : abs (a + e + p + g * q + abs s) ≤ A + abs e + p + q + abs s := by
    have t1 := abs_add_le (a + e + p + g * q) (abs s)
    have t2 := abs_add_le (a + e + p) (g * q)
    have t3 := abs_add_le (a + e) p
    have t4 := abs_add_le a e
    rw [abs_abs] at t1
    rw [abs_of_nonneg hp] at t3
    rw [abs_of_nonneg ha] at t4
    linarith
  calc C * (a + e + p + g * q + abs s) ≤ abs (C * (a + e + p + g * q + abs s)) := le_abs_self _
    _ = |C| * abs (a + e + p + g * q + abs s) := abs_mul _ _
    _ ≤ |C| * (A + abs e + p + q + abs s) := by gcongr

theorem measurable_collarFunction_eval_real {r : ℕ} (b e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (x : ℝ)
    (i j : Fin r) :
    Measurable fun ω : CollarSample W => (collarFunction b e X J ω).eval (x : ℂ) i j := by
  have hp : Measurable fun ω : CollarSample W => (ω, (x : ℂ)) :=
    measurable_id.prodMk measurable_const
  have := (measurable_collarFunction_eval b e X J i j).comp hp
  simp only [Function.comp_def] at this
  exact this

/-- The real boundary quadratic form `Re v*F_W(x)v` is measurable. -/
theorem measurable_collar_quad {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (v : Fin r → ℂ) (x : ℝ) :
    Measurable fun ω : CollarSample W => ((collarFunction b e X J ω).quadForm v x).re := by
  have hij := measurable_collarFunction_eval_real (W := W) b e X J x
  unfold AtomicHerglotz.quadForm
  simp only [dotProduct, mulVec, Complex.re_sum]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Complex.measurable_re.comp ?_
  refine measurable_const.mul ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (hij i j).mul measurable_const

theorem matchedDistance_nonneg' (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    0 ≤ matchedDistance b e X :=
  le_max_of_le_left (norm_nonneg _)

/-- **The boundary hypothesis of the Herglotz tail lemma for the collar**
(`CollarBoundaryClause`), from the middle-only shifted collar mean. Along every admissible old
sequence, for every real `x` and `v ∈ ℂ^r`, `Re v*F_{W_n}(x)v ⇒ Cauchy(0, ‖v‖²)`. Proof: a.s.
`Re v*F(x)v = 2‖v‖² Im q`, `q = u*(I - U_s r)⁻¹u`, `u = ‖v‖⁻¹Jv`, `s = x/(Wρ)`; `Re q = 1/2` and
the Cayley phase of `2 Im q` is `ζ = 1 - q⁻¹`; the rank-one twists `X'` of the old response give
`|E P(wζ) - 1| ≤ |C|{d(X) + 1/(η_min W) + |ε_W| + W^{-1/8} + W^{-1/4} + |s|} → 0` uniformly in
`‖w‖ < 1` (`abs_integral_pk_sub_one_le`); `tendsto_cauchy_of_poisson` and the dilation by `‖v‖²`
conclude. -/
theorem collarBoundaryClause_of_middleShift (hMS : MiddleShiftBoundaryMeanStatement) :
    CollarBoundaryClause := by
  intro b hb0 hb κ hκ r S x v
  by_cases hv : ∑ i, ‖v i‖ ^ 2 = 0
  · have hv0 : v = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).1 hv i
        (Finset.mem_univ i)
      simpa using this
    subst hv0
    have hE : euclidSqNorm (0 : Fin r → ℂ) = 0 := by
      apply Subtype.ext; simp [euclidSqNorm]
    exact tendstoInDistribution_zero_cauchy (fun N ω => by simp [AtomicHerglotz.quadForm]) hE
  have hγ : 0 < ∑ i, ‖v i‖ ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hv)
  set γ := ∑ i, ‖v i‖ ^ 2 with hγdef
  set Y : ∀ N, CollarSample (S.W N) → ℝ := fun N ω => ((S.collarFns N ω).quadForm v x).re / γ
  suffices hY : TendstoInDistribution Y atTop id (fun N => collarLaw (S.W N) b)
      (ProbabilityTheory.cauchyMeasure 0 1) by
    have h := tendstoInDistribution_mul_cauchy hY (euclidSqNorm v)
    have hfun : (fun N (ω : CollarSample (S.W N)) => ((euclidSqNorm v : ℝ≥0) : ℝ) * Y N ω) =
        fun N ω => ((S.collarFns N ω).quadForm v x).re := by
      funext N ω
      change γ * (((S.collarFns N ω).quadForm v x).re / γ) = _
      field_simp
    rw [hfun] at h
    exact h
  -- measurability
  have hmeasY : ∀ N, Measurable (Y N) := fun N =>
    (measurable_collar_quad b (S.e N) (S.X N) (S.J N) v x).div_const γ
  obtain ⟨ε, C, d₁, s₀, W₀, hε, hd₁, hs₀, hmain⟩ := hMS b hb0 hb κ hκ
  -- bulk constants
  set ηmin := (1 - b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2
  set ρmin := Real.sqrt (4 - (2 - κ) ^ 2) / (2 * Real.pi)
  have hηmin : 0 < ηmin :=
    (BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b) (by linarith) hκ
      (S.e_mem 0)).1
  have hηle : ∀ N, ηmin ≤ (boundaryZ b (S.e N)).im := fun N =>
    (BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b) (by linarith) hκ
      (S.e_mem N)).2
  have hρmin : 0 < ρmin := (semicircleDensity_ge hκ (S.e_mem 0)).1
  have hρle : ∀ N, ρmin ≤ Parameters.semicircleDensity (S.e N) := fun N =>
    (semicircleDensity_ge hκ (S.e_mem N)).2
  set s : ℕ → ℝ := fun N => microShift (S.W N) (S.e N) x
  have hWr : Tendsto (fun N => (S.W N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp S.tendsto_W
  have hWinv : Tendsto (fun N => ((S.W N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hWr
  have hs : Tendsto (fun N => |s N|) atTop (𝓝 0) := by
    have hb' : Tendsto (fun N => (|x| * ρmin⁻¹) * ((S.W N : ℝ))⁻¹) atTop (𝓝 0) := by
      simpa using hWinv.const_mul (|x| * ρmin⁻¹)
    refine squeeze_zero (fun N => abs_nonneg _) (fun N => ?_) hb'
    have hW : (0 : ℝ) < S.W N := by exact_mod_cast S.W_pos N
    have hρ := hρle N
    simp only [s, microShift]
    rw [abs_div, abs_of_pos (mul_pos hW (hρmin.trans_le hρ))]
    rw [div_le_iff₀ (mul_pos hW (hρmin.trans_le hρ))]
    have : (|x| * ρmin⁻¹) * ((S.W N : ℝ))⁻¹ * ((S.W N : ℝ) * Parameters.semicircleDensity (S.e N)) =
        |x| * (Parameters.semicircleDensity (S.e N) / ρmin) := by
      field_simp
    rw [this]
    have h1 : 1 ≤ Parameters.semicircleDensity (S.e N) / ρmin := by rw [le_div_iff₀ hρmin]; linarith
    nlinarith [abs_nonneg x]
  set err : ℕ → ℝ := fun N => |C| * ((matchedDistance b (S.e N) (S.X N) +
    ηmin⁻¹ * ((S.W N : ℝ))⁻¹) + |ε (S.W N)| + (S.W N : ℝ) ^ (-(1 : ℝ) / 8) +
      (S.W N : ℝ) ^ (-(1 : ℝ) / 4) + |s N|)
  have hrpow : ∀ c : ℝ, 0 < c → Tendsto (fun N => (S.W N : ℝ) ^ (-c)) atTop (𝓝 0) :=
    fun c hc => (tendsto_rpow_neg_atTop hc).comp hWr
  have h8 : Tendsto (fun N => (S.W N : ℝ) ^ (-(1 : ℝ) / 8)) atTop (𝓝 0) := by
    have := hrpow (1 / 8) (by norm_num); simpa [neg_div] using this
  have h4 : Tendsto (fun N => (S.W N : ℝ) ^ (-(1 : ℝ) / 4)) atTop (𝓝 0) := by
    have := hrpow (1 / 4) (by norm_num); simpa [neg_div] using this
  have hdW : Tendsto (fun N => matchedDistance b (S.e N) (S.X N) + ηmin⁻¹ * ((S.W N : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa using S.tendsto_d.add (hWinv.const_mul ηmin⁻¹)
  have hεW : Tendsto (fun N => |ε (S.W N)|) atTop (𝓝 0) := by
    simpa using (hε.comp S.tendsto_W).abs
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa using ((((hdW.add hεW).add h8).add h4).add hs).const_mul |C|
  have hev : ∀ᶠ N in atTop, W₀ ≤ S.W N ∧ |s N| ≤ s₀ ∧
      matchedDistance b (S.e N) (S.X N) + ηmin⁻¹ * ((S.W N : ℝ))⁻¹ ≤ d₁ :=
    (S.tendsto_W.eventually_ge_atTop W₀).and ((hs.eventually (Iic_mem_nhds hs₀)).and
      (hdW.eventually (Iic_mem_nhds hd₁)))
  refine ⟨fun N => (hmeasY N).aemeasurable, aemeasurable_id, ?_⟩
  have hL := tendsto_cauchy_of_poisson
    (μ := fun N => ⟨(collarLaw (S.W N) b).map (Y N), inferInstance⟩) herr ?_
  · have e : (⟨(ProbabilityTheory.cauchyMeasure 0 1).map id, inferInstance⟩ :
        ProbabilityMeasure ℝ) = ⟨ProbabilityTheory.cauchyMeasure 0 1, inferInstance⟩ :=
      Subtype.ext (Measure.map_id)
    rw [e]
    exact hL
  filter_upwards [hev] with N hN
  obtain ⟨hW₀, hsN, hdN⟩ := hN
  intro w hw
  have hW := S.W_pos N
  have he := S.e_mem N
  have hη := boundaryZ_im_pos hb hκ he
  have hc := poleScale_pos hW hκ he
  have hX := S.X_herm N
  set u : Fin 2 × Fin (S.W N) → ℂ :=
    (((Real.sqrt γ)⁻¹ : ℝ) : ℂ) • (S.J N *ᵥ v) with hudef
  have hu : star u ⬝ᵥ u = 1 := frameVec_unit (S.J_frame N) hγ
  set X' := twistOld b (S.e N) w u (S.X N)
  have hdX' : matchedDistance b (S.e N) X' ≤
      matchedDistance b (S.e N) (S.X N) + ηmin⁻¹ * ((S.W N : ℝ))⁻¹ := by
    refine (matchedDistance_twistOld_le hW hη hX hu hw).trans ?_
    gcongr
    exact hηle N
  have hk := (hmain (S.W N) hW hW₀ (S.e N) he (s N) (abs_le.1 hsN) X'
    (hdX'.trans hdN)).2 (posSemidef_neg_imPart_twistOld hη hX hu hw)
  have hinv := ae_isUnit_det_one_sub_closedScattering hb hW (S.e N) hη hc hX hu x
  have hbound := abs_integral_pk_sub_one_le hη hX hu hw hinv hk
  have herrle : middleMeanError b (S.e N) (s N) ε C X' ≤ err N := by
    unfold middleMeanError
    have hg : |conductance (oldScattering b (S.e N) X')| ≤ 1 := by
      rw [conductance_twistOld hη hX hu hw]
      have h0 : 0 ≤ Complex.normSq w := Complex.normSq_nonneg w
      have h1 : Complex.normSq w ≤ 1 := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
      rw [abs_le]; constructor <;> linarith
    exact error_arith (matchedDistance_nonneg' _ _ _) hdX' (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _) hg
  have hint : ∫ t, pk w (cay t) ∂((collarLaw (S.W N) b).map (Y N)) =
      ∫ ω, pk w (1 - (closedQuad b (S.e N) (s N) 1 (S.X N) u ω)⁻¹) ∂collarLaw (S.W N) b := by
    rw [integral_map (hmeasY N).aemeasurable (continuous_pk_cay hw).aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [ae_collarFunction_eval_eq hb hW (S.e N) hη hc hX (S.J N) x, hinv,
      Collar.Density.ae_collarMatrix_isHermitian b (S.e N) hX] with ω h1 h2 h3
    have hYq : Y N ω = 2 * (closedQuad b (S.e N) (s N) 1 (S.X N) u ω).im := by
      change ((collarFunction b (S.e N) (S.X N) (S.J N) ω).quadForm v x).re / γ = _
      rw [AtomicHerglotz.quadForm, h1, re_quad_closingMatrix b (S.e N) (s N) (S.X N)
        (S.J_frame N) hγ ω]
      rw [mul_right_comm, mul_div_cancel_right₀ _ hγ.ne']
    have hre : (closedQuad b (S.e N) (s N) 1 (S.X N) u ω).re = 1 / 2 := by
      have := re_quad_inv_eq (closedScattering b (S.e N) (s N) (S.X N) ω) hu h2
        (closedScattering_mul_conjTranspose b (S.e N) (s N) hη hX h3.2.1 h3.2.2)
      simpa [closedQuad] using this
    change pk w (cay (Y N ω)) = _
    rw [hYq, cay_two_mul_im hre]
  change |∫ t, pk w (cay t) ∂((collarLaw (S.W N) b).map (Y N)) - 1| ≤ err N
  rw [hint]
  exact hbound.trans herrle

/-- **`CollarBoundaryClause` from the `ExactBoundaryMeanContract`.** -/
theorem collarBoundaryClause_of_exactBoundaryMean (hEB : ExactBoundaryMeanContract) :
    CollarBoundaryClause :=
  collarBoundaryClause_of_middleShift (middleShiftBoundaryMean_of_exactBoundaryMean hEB)

/-- **`MatrixClosingStatement` from hypotheses 1 and 2 and `ExactBoundaryMeanContract`.**
`CollarPolesClause` fails at frame rank `r = 0`, so this implication is vacuous. The usable form
is `Poles.matrixClosing_of_clauses_pos` (hypothesis 1 only at `r ≥ 1`, `Poles.CollarPolesAt r`;
`r = 0` by `Poles.matrixClosingAt_zero`), together with `Poles.matrixClosing_of_relativeVectors`.
-/
theorem matrixClosing_of_poles_mean (h1 : CollarPolesClause) (h2 : CollarMeanClause)
    (hEB : ExactBoundaryMeanContract) : MatrixClosingStatement :=
  matrixClosing_of_clauses h1 h2 (collarBoundaryClause_of_exactBoundaryMean hEB)

end BlockBand.Critical.MatrixClosing.Boundary

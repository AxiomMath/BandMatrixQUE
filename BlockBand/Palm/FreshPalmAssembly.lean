module

public import BlockBand.Palm.FreshPalmFlow
public import BlockBand.Palm.MomentFlow.PalmTransfer
public import BlockBand.RankLocation.WindowTransferGaussianTail

/-!
# The fresh Palm theorem from the conditional-moments lemma

*Measures.* `A⁰ ~ freshTracelessLaw N c₀`; the flow law `flowLaw N a` with
`a = c₀ - N^{-1/100}`, conditioning on `𝓛 = pathSigma F a a c₀` (the conditional expectation
`condExp`).
*Domain, uniformity.* Fixed `A, c₀, r₀, s₀, v₀` (`FreshConstants`), then `r ≥ 1` gives `κ`
(the lemma's `κ_r`) and `C_r = r! max(C,0) + 1`; then each `K > 0` gives `C_{r,K}`; uniform in
**every** `N ≥ 1`, every `F` in `FreshClass`, every `E`, every `q ∈ ℂ^N`, every rank `ℓ`. No lower
bound on `Z` and no division by `Z`.

## Proof

1. *Homogeneity*: both sides have degree `2r` in `q`; `q = 0` is trivial (`r ≥ 1`), otherwise
   `q ↦ q/√(q*Γq)` (`Γ ≻ 0`, `freshGamma_quad_pos`).
2. *Small `N < N₁`* (`palm_error_raw`): `|E[w(X^r - r!)]| ≤ W((N‖q‖²)^r + r!)` with
   `W = N/√(2πc₀)` and `‖q‖² ≤ (v₀ L)^{-1} N^{2max(A,1)}`, i.e. `≤ rawConst · N^{rawExp}`,
   absorbed into `C_{r,K}` as `rawConst · N₁^{rawExp+K} · N^{-K}`.
3. *Large `N`* (`palm_error_flow`): the law of `A⁰` is the traceless part of the flow increment
   at terminal variance `c₀`; `w = φ(E - λ_ℓ(c₀) + g)` with `g = (∑λ_k(c₀) - Re Tr F)/N`, so `w`
   is `𝓛`-measurable and `E[wX^r] = E[w E[X^r|𝓛]]`; `E[X^r|𝓛] = r! F_r(c₀, rδ_ℓ)`. The window
   transfer `conditional_weighted_error_le_window` with good set `Bᶜ ∩ {|g| ≤ δ/4}`,
   window `{|g| ≤ δ/4 → |λ_ℓ - E| ≤ δ}`, `δ = N^{-1+ε}`, error `r! C⁺ N^{-κ}`, off-window weight
   `≤ W exp(-(3δ/4)²/(2c₀/N²))` (`scalarWeight_le_offWindow`), bad mass `≤ N^{-D} + 2 exp(-N^{2ε}/(32c₀))`
   (`flowLaw_traceShift_tail`), raw bound `rawConst N^{rawExp}`.
4. *Constants*: `D = K + rawExp`, the Gaussian tail paid by `gaussian_tail_power` at power
   `N^{-(K + rawExp)}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.FreshPalmAssembly

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Model.Construction
  BlockBand.Palm.MomentFlow BlockBand.Coarea.PoleExclusion BlockBand.Coarea.FreshPalm
  BlockBand.Palm.CoarseRelative
open scoped ENNReal NNReal ComplexConjugate

variable {N : ℕ}

/-- Polynomial exponent of the raw bound: `r(1 + 2max(A,1)) + 1`. -/
def rawExp (A : ℝ) (r : ℕ) : ℝ := r * (1 + 2 * max A 1) + 1

/-- Constant of the raw bound: `((v₀ L)^{-r} + r!)/√(2πc₀)`, `L = lowConst c₀ s₀ v₀`. -/
def rawConst (c₀ s₀ v₀ : ℝ) (r : ℕ) : ℝ :=
  ((v₀ * lowConst c₀ s₀ v₀)⁻¹ ^ r + r.factorial) * (Real.sqrt (2 * Real.pi * c₀))⁻¹

theorem lowConst_pos {c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) :
    0 < v₀ * lowConst c₀ s₀ v₀ := by
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  have : 0 < c₀ - s₀ := by linarith [hK.2.2.2.2.1, hK.1]
  unfold lowConst
  positivity

theorem rawConst_nonneg {c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (r : ℕ) :
    0 ≤ rawConst c₀ s₀ v₀ r := by
  have := lowConst_pos hK
  unfold rawConst
  positivity

theorem rawExp_pos (A : ℝ) (r : ℕ) : 0 < rawExp A r := by
  unfold rawExp
  have : 0 ≤ 1 + 2 * max A 1 := by have := le_max_right A 1; linarith
  positivity

/-- `W = (2π c₀/N²)^{-1/2} = N/√(2πc₀)`. -/
theorem prefactor_eq {c₀ : ℝ} (hc₀ : 0 < c₀) (hN : 0 < N) :
    (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹ =
      (N : ℝ) * (Real.sqrt (2 * Real.pi * c₀))⁻¹ := by
  rw [BlockBand.Palm.coe_scalarVariance, Real.coe_toNNReal _ hc₀.le]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show 2 * Real.pi * (c₀ / (N : ℝ) ^ 2) = (2 * Real.pi * c₀) / (N : ℝ) ^ 2 by ring,
    Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hN'.le, inv_div, div_eq_mul_inv]

/-- **Raw bound.** On the fresh class with `q*Γq = 1`:
`W·((N‖q‖²)^r + r!) ≤ rawConst · N^{rawExp}`. -/
theorem prefactor_mul_rawB_le {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} {E : ℝ} (hC : FreshClass F A c₀ E r₀ s₀ v₀) {q : Fin N → ℂ}
    (hq : quadForm (freshGamma F c₀ E) q = 1) (r : ℕ) :
    (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹ *
        (((N : ℝ) * ∑ i, ‖q i‖ ^ 2) ^ r + r.factorial) ≤
      rawConst c₀ s₀ v₀ r * (N : ℝ) ^ rawExp A r := by
  have hc₀ : 0 < c₀ := hK.1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set m := max A 1
  set lam := v₀ * lowConst c₀ s₀ v₀
  have hlam : 0 < lam := lowConst_pos hK
  have hl := freshGamma_quad_lower hN hK hC q
  rw [hq] at hl
  change lam * (N : ℝ) ^ (-(2 * m)) * (∑ i, ‖q i‖ ^ 2) ≤ 1 at hl
  have hs0 : 0 ≤ ∑ i, ‖q i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hNm : 0 < (N : ℝ) ^ (-(2 * m)) := Real.rpow_pos_of_pos hN' _
  have hn : ∑ i, ‖q i‖ ^ 2 ≤ lam⁻¹ * (N : ℝ) ^ (2 * m) := by
    have h1 : ∑ i, ‖q i‖ ^ 2 ≤ 1 / (lam * (N : ℝ) ^ (-(2 * m))) := by
      rw [le_div_iff₀ (mul_pos hlam hNm)]; linarith
    rwa [Real.rpow_neg hN'.le, one_div, mul_inv, inv_inv] at h1
  have hx0 : 0 ≤ 1 + 2 * m := by have := le_max_right A 1; linarith
  have h1 : (N : ℝ) * ∑ i, ‖q i‖ ^ 2 ≤ lam⁻¹ * (N : ℝ) ^ (1 + 2 * m) := by
    rw [Real.rpow_add hN', Real.rpow_one]
    calc (N : ℝ) * ∑ i, ‖q i‖ ^ 2 ≤ (N : ℝ) * (lam⁻¹ * (N : ℝ) ^ (2 * m)) :=
          mul_le_mul_of_nonneg_left hn hN'.le
      _ = _ := by ring
  have h2 : ((N : ℝ) * ∑ i, ‖q i‖ ^ 2) ^ r ≤ lam⁻¹ ^ r * (N : ℝ) ^ ((r : ℝ) * (1 + 2 * m)) := by
    refine (pow_le_pow_left₀ (by positivity) h1 r).trans (le_of_eq ?_)
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 + 2 * m)), ← Real.rpow_mul hN'.le, mul_comm (1 + 2 * m)]
  have h3 : (r.factorial : ℝ) ≤ r.factorial * (N : ℝ) ^ ((r : ℝ) * (1 + 2 * m)) :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hN1 (by positivity))
  have hB : ((N : ℝ) * ∑ i, ‖q i‖ ^ 2) ^ r + r.factorial ≤
      (lam⁻¹ ^ r + r.factorial) * (N : ℝ) ^ ((r : ℝ) * (1 + 2 * m)) := by
    rw [add_mul]; linarith
  rw [prefactor_eq hc₀ hN]
  have hW : 0 ≤ (N : ℝ) * (Real.sqrt (2 * Real.pi * c₀))⁻¹ := by positivity
  refine (mul_le_mul_of_nonneg_left hB hW).trans (le_of_eq ?_)
  unfold rawConst rawExp
  rw [Real.rpow_add_one hN'.ne']
  ring

theorem measurable_palmOverlap (F : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) (ℓ : Fin N) :
    Measurable (palmOverlap F q ℓ) :=
  (measurable_overlapOf q ℓ).comp (measurable_matrix_add.comp (measurable_const.prodMk measurable_id))

/-- **Raw Palm error** (every `N ≥ 1`): `|E[w X^r] - r! Z| ≤ rawConst · N^{rawExp}` for
`q*Γq = 1`. -/
theorem palm_error_raw {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} {E : ℝ} (hC : FreshClass F A c₀ E r₀ s₀ v₀) {q : Fin N → ℂ}
    (hq : quadForm (freshGamma F c₀ E) q = 1) (ℓ : Fin N) (r : ℕ) :
    |(∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F q ℓ A0 ^ r ∂freshTracelessLaw N c₀) -
        (r.factorial : ℝ) * ∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀| ≤
      rawConst c₀ s₀ v₀ r * (N : ℝ) ^ rawExp A r := by
  set W := (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹
  set Bq := ((N : ℝ) * ∑ i, ‖q i‖ ^ 2) ^ r + r.factorial
  have hwm := measurable_palmWeight F c₀ E ℓ
  have hYm := (measurable_palmOverlap F q ℓ).pow_const r
  have hw0 : ∀ A0, 0 ≤ palmWeight F c₀ E ℓ A0 := fun A0 => BlockBand.Palm.scalarWeight_nonneg _ _ _ _
  have hwW : ∀ A0, palmWeight F c₀ E ℓ A0 ≤ W := fun A0 =>
    BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _
  have hY0 : ∀ A0, 0 ≤ palmOverlap F q ℓ A0 := fun A0 => by unfold palmOverlap; positivity
  have hYB : ∀ A0, palmOverlap F q ℓ A0 ^ r ≤ ((N : ℝ) * ∑ i, ‖q i‖ ^ 2) ^ r := fun A0 =>
    pow_le_pow_left₀ (hY0 A0) (overlap_le_nsq _ q ℓ) r
  have hwI : Integrable (palmWeight F c₀ E ℓ) (freshTracelessLaw N c₀) :=
    Integrable.of_bound hwm.aestronglyMeasurable W (ae_of_all _ fun A0 => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 A0)]; exact hwW A0)
  have hwYI : Integrable (fun A0 => palmWeight F c₀ E ℓ A0 * palmOverlap F q ℓ A0 ^ r)
      (freshTracelessLaw N c₀) :=
    Integrable.of_bound (hwm.mul hYm).aestronglyMeasurable (W * ((N : ℝ) * ∑ i, ‖q i‖ ^ 2) ^ r)
      (ae_of_all _ fun A0 => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 A0) (pow_nonneg (hY0 A0) r))]
        exact mul_le_mul (hwW A0) (hYB A0) (pow_nonneg (hY0 A0) r) ((hw0 A0).trans (hwW A0)))
  rw [← integral_const_mul, ← integral_sub hwYI (hwI.const_mul _)]
  have hbound : ∀ᵐ A0 ∂freshTracelessLaw N c₀,
      ‖palmWeight F c₀ E ℓ A0 * palmOverlap F q ℓ A0 ^ r - (r.factorial : ℝ) * palmWeight F c₀ E ℓ A0‖
        ≤ W * Bq := ae_of_all _ fun A0 => by
    rw [Real.norm_eq_abs, show palmWeight F c₀ E ℓ A0 * palmOverlap F q ℓ A0 ^ r -
      (r.factorial : ℝ) * palmWeight F c₀ E ℓ A0 =
        palmWeight F c₀ E ℓ A0 * (palmOverlap F q ℓ A0 ^ r - r.factorial) by ring, abs_mul,
      abs_of_nonneg (hw0 A0)]
    have h1 : |palmOverlap F q ℓ A0 ^ r - r.factorial| ≤ Bq := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (pow_nonneg (hY0 A0) r), abs_of_nonneg (by positivity)]
      linarith [hYB A0]
    exact mul_le_mul (hwW A0) h1 (abs_nonneg _) ((hw0 A0).trans (hwW A0))
  have h := norm_integral_le_of_norm_le_const hbound
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h.trans (prefactor_mul_rawB_le hK hN hC hq r)

/-- Exponent of the scalar tail at `δ = N^{-1+ε}`: `(δ/4)²/(2c₀/N²) = (32c₀)^{-1} (N^ε)²`. -/
theorem tail_exponent_eq {c₀ : ℝ} (hc₀ : 0 < c₀) (hN : 0 < N) (ε : ℝ) :
    ((N : ℝ) ^ (-1 + ε) / 4) ^ 2 / (2 * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N) =
      (32 * c₀)⁻¹ * ((N : ℝ) ^ ε) ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [BlockBand.Palm.coe_scalarVariance, Real.coe_toNNReal _ hc₀.le, Real.rpow_add hN',
    Real.rpow_neg_one]
  field_simp
  ring

/-- `exp(-(δ/4)²/(2c₀/N²)) ≤ C₂ N^{-Q}` with an explicit `C₂ = C₂(Q, ε, c₀)`. -/
theorem tail_le_power {c₀ : ℝ} (hc₀ : 0 < c₀) (hN : 0 < N) {ε Q : ℝ} (hε : 0 < ε) (hQ : 0 < Q) :
    Real.exp (-((N : ℝ) ^ (-1 + ε) / 4) ^ 2 /
        (2 * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N)) ≤
      ((Q / ε) / (2 * (32 * c₀)⁻¹)) ^ ((Q / ε) / 2) * (N : ℝ) ^ (-Q) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := BlockBand.RankLocation.WindowTransfer.gaussian_tail_power (Q / ε) (32 * c₀)⁻¹
    ((N : ℝ) ^ ε) (div_pos hQ hε) (by positivity) (Real.rpow_pos_of_pos hN' ε)
  rw [neg_div, tail_exponent_eq hc₀ hN ε, ← neg_mul]
  refine h.trans (le_of_eq ?_)
  rw [← Real.rpow_mul hN'.le]
  congr 2
  field_simp

/-- The conditional-moments lemma, stated with the path σ-algebra `pathSigma` and the conditional
moments `condMoment`. -/
def ConditionalMomentsStatement : Prop :=
  ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ →
  ∀ r : ℕ, 1 ≤ r → ∃ ε κ C : ℝ, 0 < ε ∧ 0 < κ ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ q : Fin N → ℂ, quadForm (freshGamma F c₀ E) q = 1 →
      let a : ℝ := c₀ - (N : ℝ) ^ (-(1 / 100 : ℝ))
      ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c₀] B ∧
        flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ k : Fin N, ∀ᵐ ω ∂flowLaw N a, ω ∉ B →
          |flowEigenvalue F a ω c₀ k - E| ≤ (N : ℝ) ^ (-1 + ε) →
          |condMoment F a c₀ q c₀ (fun i => if i = k then r else 0) ω - 1| ≤
            C * (N : ℝ) ^ (-κ)

theorem momentMonomial_single (X : Fin N → ℝ) (ℓ : Fin N) (r : ℕ) :
    momentMonomial X (fun i => if i = ℓ then r else 0) = ((r.factorial : ℝ))⁻¹ * X ℓ ^ r := by
  unfold momentMonomial
  rw [Finset.prod_eq_single ℓ]
  · simp [div_eq_inv_mul]
  · intro b _ hb; simp [hb]
  · simp

/-- **Palm transfer on the flow**, for `q*Γq = 1`, at one `N`, given the
conclusion of the conditional-moments lemma at that `N` (bad path set `B`). With
`δ = N^{-1+ε}`, `T = exp(-(δ/4)²/(2c₀/N²))`:
`|E[w X^r] - r! Z| ≤ r! C⁺ N^{-κ} Z + rawConst N^{rawExp} (N^{-D} + 3T)`. -/
theorem palm_error_flow {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} {E : ℝ} (hC : FreshClass F A c₀ E r₀ s₀ v₀) {q : Fin N → ℂ}
    (hq : quadForm (freshGamma F c₀ E) q = 1) (ℓ : Fin N) (r : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hac : a ≤ c₀) {ε κ C D : ℝ} {B : Set (FlowSample N)}
    (hBm : MeasurableSet[pathSigma F a a c₀] B)
    (hBμ : flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)))
    (hBcm : ∀ k : Fin N, ∀ᵐ ω ∂flowLaw N a, ω ∉ B →
          |flowEigenvalue F a ω c₀ k - E| ≤ (N : ℝ) ^ (-1 + ε) →
          |condMoment F a c₀ q c₀ (fun i => if i = k then r else 0) ω - 1| ≤
            C * (N : ℝ) ^ (-κ)) :
    |(∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F q ℓ A0 ^ r ∂freshTracelessLaw N c₀) -
        (r.factorial : ℝ) * ∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀| ≤
      (r.factorial : ℝ) * max C 0 * (N : ℝ) ^ (-κ) *
          (∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀) +
        rawConst c₀ s₀ v₀ r * (N : ℝ) ^ rawExp A r * ((N : ℝ) ^ (-D) +
          3 * Real.exp (-((N : ℝ) ^ (-1 + ε) / 4) ^ 2 /
            (2 * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))) := by
  classical
  have hc₀ : 0 < c₀ := hK.1
  have hF : F.IsHermitian := hC.1
  set μ := flowLaw N a with hμ
  have hm : pathSigma F a a c₀ ≤ (inferInstance : MeasurableSpace (FlowSample N)) := pathSigma_le F a a c₀
  set v := BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N with hv
  set W := (Real.sqrt (2 * Real.pi * v))⁻¹ with hW
  set δ := (N : ℝ) ^ (-1 + ε) with hδ
  set T := Real.exp (-(δ / 4) ^ 2 / (2 * (v : ℝ))) with hT
  set Bq := ((N : ℝ) * ∑ i, ‖q i‖ ^ 2) ^ r + r.factorial with hBq
  set w := flowWeight F a c₀ E ℓ with hwdef
  set X : FlowSample N → ℝ := fun ω => flowOverlap F a q c₀ ℓ ω ^ r with hXdef
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hT0 : 0 ≤ T := (Real.exp_pos _).le
  have hW0 : 0 ≤ W := by positivity
  have hBq0 : 0 ≤ Bq := by positivity
  -- measurability (the weight is `𝓛`-measurable)
  have hν : ∀ k, Measurable[pathSigma F a a c₀] (fun ω => flowEigenvalue F a ω c₀ k) := fun k =>
    measurable_flowEigenvalue_pathSigma F a a c₀ ⟨hac, le_rfl⟩ k
  have hts : Measurable[pathSigma F a a c₀] (traceShift F a c₀) := by
    unfold traceShift
    exact ((Finset.measurable_sum _ fun k _ => hν k).sub measurable_const).div_const _
  have hwm : Measurable[pathSigma F a a c₀] w := by
    rw [hwdef]
    unfold flowWeight BlockBand.Palm.scalarWeight
    exact (measurable_gaussianPDFReal _ _).comp (measurable_const.sub ((hν ℓ).sub hts))
  have hwm' : Measurable w := hwm.mono hm le_rfl
  have hts' : Measurable (traceShift F a c₀) := hts.mono hm le_rfl
  have hXm : Measurable X := (measurable_flowOverlap F a q c₀ ℓ).pow_const r
  -- bounds
  have hw0 : ∀ ω, 0 ≤ w ω := fun ω => BlockBand.Palm.scalarWeight_nonneg _ _ _ _
  have hwW : ∀ ω, w ω ≤ W := fun ω => BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _
  have hO0 : ∀ ω, 0 ≤ flowOverlap F a q c₀ ℓ ω := fun ω => by unfold flowOverlap; positivity
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => pow_nonneg (hO0 ω) r
  have hXB : ∀ ω, X ω ≤ ((N : ℝ) * ∑ i, ‖q i‖ ^ 2) ^ r := fun ω =>
    pow_le_pow_left₀ (hO0 ω) (overlap_le_nsq _ q ℓ) r
  have hwI : Integrable w μ :=
    Integrable.of_bound hwm'.aestronglyMeasurable W (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 ω)]; exact hwW ω)
  have hXI : Integrable X μ :=
    Integrable.of_bound hXm.aestronglyMeasurable (((N : ℝ) * ∑ i, ‖q i‖ ^ 2) ^ r)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]; exact hXB ω)
  have hwXI : Integrable (w * X) μ :=
    Integrable.of_bound (hwm'.mul hXm).aestronglyMeasurable (W * ((N : ℝ) * ∑ i, ‖q i‖ ^ 2) ^ r)
      (ae_of_all _ fun ω => by
        rw [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 ω) (hX0 ω))]
        exact mul_le_mul (hwW ω) (hXB ω) (hX0 ω) hW0)
  -- good set and window
  set S : Set (FlowSample N) := {ω | |traceShift F a c₀ ω| ≤ δ / 4} with hS
  set good : Set (FlowSample N) := Bᶜ ∩ S with hgood
  set window : Set (FlowSample N) :=
    {ω | |traceShift F a c₀ ω| ≤ δ / 4 → |flowEigenvalue F a ω c₀ ℓ - E| ≤ δ} with hwin
  have hSm : MeasurableSet S := measurableSet_le (continuous_abs.measurable.comp hts') measurable_const
  have hgoodSet : MeasurableSet good := (hm _ hBm).compl.inter hSm
  -- conditional moments
  have hce : μ[X | pathSigma F a a c₀] =ᵐ[μ] fun ω =>
      (r.factorial : ℝ) * condMoment F a c₀ q c₀ (fun i => if i = ℓ then r else 0) ω := by
    have hmono : (fun ω => momentMonomial (fun k => flowOverlap F a q c₀ k ω)
        (fun i => if i = ℓ then r else 0)) = ((r.factorial : ℝ))⁻¹ • X := by
      funext ω
      rw [momentMonomial_single, Pi.smul_apply, smul_eq_mul]
    have h1 := condExp_smul (μ := μ) ((r.factorial : ℝ))⁻¹ X (pathSigma F a a c₀)
    unfold condMoment
    rw [hmono]
    filter_upwards [h1] with ω hω
    rw [hω, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (by positivity : (r.factorial : ℝ) ≠ 0), one_mul]
  have hδ' : 0 ≤ (r.factorial : ℝ) * max C 0 * (N : ℝ) ^ (-κ) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg N) (-κ)
    have := le_max_right C 0
    positivity
  have hgoodcm : ∀ᵐ ω ∂μ, ω ∈ good → ω ∈ window →
      |(μ[X | pathSigma F a a c₀]) ω - r.factorial| ≤ (r.factorial : ℝ) * max C 0 * (N : ℝ) ^ (-κ) := by
    filter_upwards [hce, hBcm ℓ] with ω h1 h2 hg hw
    have hνE : |flowEigenvalue F a ω c₀ ℓ - E| ≤ δ := hw hg.2
    have h3 := h2 hg.1 hνE
    rw [h1, ← mul_sub_one, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r.factorial),
      mul_assoc]
    refine mul_le_mul_of_nonneg_left (h3.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  -- off the window the weight is exponentially small
  have hoff : ∀ ω, ω ∉ window → w ω ≤ W * T := by
    intro ω hω
    simp only [hwin, Set.mem_ofPred_eq, not_imp, not_le] at hω
    have h := BlockBand.Palm.scalarWeight_le_offWindow (Real.toNNReal c₀) N (E := E)
      (ν := flowEigenvalue F a ω c₀ ℓ - traceShift F a c₀ ω) (g := traceShift F a c₀ ω)
      hδ0 hω.1 (by rw [sub_add_cancel]; exact hω.2.le)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hW0)
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply neg_le_neg
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hraw : ∀ ω, |X ω - r.factorial| ≤ Bq := by
    intro ω
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (hX0 ω), abs_of_nonneg (by positivity : (0 : ℝ) ≤ r.factorial)]
    linarith [hXB ω]
  have key := conditional_weighted_error_le_window hm hwm.stronglyMeasurable hwI hXI hwXI
    hgoodSet hδ' hBq0 (mul_nonneg hW0 hT0) (ae_of_all _ hw0) (ae_of_all _ hwW) hgoodcm
    (ae_of_all _ hoff) (ae_of_all _ hraw)
  -- identify both sides with the integrals in the statement
  have hΦ : Measurable fun A0 => palmWeight F c₀ E ℓ A0 * palmOverlap F q ℓ A0 ^ r :=
    (measurable_palmWeight F c₀ E ℓ).mul ((measurable_palmOverlap F q ℓ).pow_const r)
  have hid := ae_flow_identification hF hN ha hac E q ℓ
  have hLHS : (∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F q ℓ A0 ^ r ∂freshTracelessLaw N c₀) =
      ∫ ω, w ω * X ω ∂μ := by
    rw [integral_freshTracelessLaw_eq_flow F ha hac hΦ]
    refine integral_congr_ae ?_
    filter_upwards [hid] with ω hω
    rw [hω.1, hω.2.1]
  have hZ : (∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀) = ∫ ω, w ω ∂μ := by
    rw [integral_freshTracelessLaw_eq_flow F ha hac (measurable_palmWeight F c₀ E ℓ)]
    refine integral_congr_ae ?_
    filter_upwards [hid] with ω hω
    rw [hω.1]
  rw [hLHS, hZ]
  refine key.trans ?_
  -- the bad mass
  have hBr : μ.real B ≤ (N : ℝ) ^ (-D) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (Nat.cast_nonneg N) _) hBμ
  have hSc : μ.real Sᶜ ≤ 2 * T := by
    have hsub : Sᶜ ⊆ {ω | δ / 4 ≤ |traceShift F a c₀ ω|} := by
      intro ω hω
      simp only [hS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
      exact hω.le
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans
      (flowLaw_traceShift_tail hF hN hc₀.le ha hac (by positivity))
  have hgc : μ.real goodᶜ ≤ (N : ℝ) ^ (-D) + 2 * T := by
    rw [hgood, Set.compl_inter, compl_compl]
    exact (measureReal_union_le _ _).trans (add_le_add hBr hSc)
  have hWB := prefactor_mul_rawB_le hK hN hC hq r
  rw [probReal_univ, mul_one]
  have hZ0 : 0 ≤ ∫ ω, w ω ∂μ := integral_nonneg hw0
  have e1 : Bq * W * μ.real goodᶜ ≤ Bq * W * ((N : ℝ) ^ (-D) + 2 * T) :=
    mul_le_mul_of_nonneg_left hgc (mul_nonneg hBq0 hW0)
  have e2 : Bq * W * ((N : ℝ) ^ (-D) + 3 * T) ≤
      rawConst c₀ s₀ v₀ r * (N : ℝ) ^ rawExp A r * ((N : ℝ) ^ (-D) + 3 * T) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [mul_comm Bq W]; exact hWB
  nlinarith [e1, e2]

/-- `N ≥ c₀^{-100}` gives `N^{-1/100} ≤ c₀`, i.e. the flow start `a = c₀ - N^{-1/100} ≥ 0`. -/
theorem rpow_neg_hundredth_le {c₀ : ℝ} (hc₀ : 0 < c₀) {x : ℝ} (hx : c₀ ^ (-100 : ℝ) ≤ x) :
    x ^ (-(1 / 100 : ℝ)) ≤ c₀ := by
  have hp : 0 < c₀ ^ (-100 : ℝ) := Real.rpow_pos_of_pos hc₀ _
  refine (Real.rpow_le_rpow_of_nonpos hp hx (by norm_num)).trans (le_of_eq ?_)
  rw [← Real.rpow_mul hc₀.le]
  norm_num

/-- Normalized form (`q*Γq = 1`) of the target bound, for every `N ≥ 1`. -/
theorem palm_error_normalized {A c₀ r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) {r : ℕ} {ε κ C : ℝ} (hε : 0 < ε)
    (hCMr : ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ q : Fin N → ℂ, quadForm (freshGamma F c₀ E) q = 1 →
        let a : ℝ := c₀ - (N : ℝ) ^ (-(1 / 100 : ℝ))
        ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c₀] B ∧
          flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ k : Fin N, ∀ᵐ ω ∂flowLaw N a, ω ∉ B →
            |flowEigenvalue F a ω c₀ k - E| ≤ (N : ℝ) ^ (-1 + ε) →
            |condMoment F a c₀ q c₀ (fun i => if i = k then r else 0) ω - 1| ≤
              C * (N : ℝ) ^ (-κ))
    {K : ℝ} (hKpos : 0 < K) :
    ∃ CrK : ℝ, ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
      FreshClass F A c₀ E r₀ s₀ v₀ → ∀ (q : Fin N → ℂ), quadForm (freshGamma F c₀ E) q = 1 →
      ∀ ℓ : Fin N,
      |(∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F q ℓ A0 ^ r ∂freshTracelessLaw N c₀) -
          (r.factorial : ℝ) * ∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀| ≤
        ((r.factorial : ℝ) * max C 0 + 1) *
          ((N : ℝ) ^ (-κ) * (∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀) +
            CrK * (N : ℝ) ^ (-K)) := by
  have hc₀ : 0 < c₀ := hK.1
  set P := rawExp A r with hP
  set C1 := rawConst c₀ s₀ v₀ r with hC1
  have hC10 : 0 ≤ C1 := rawConst_nonneg hK r
  have hP0 : 0 < P := rawExp_pos A r
  set Q := K + P with hQ
  have hQ0 : 0 < Q := by linarith
  obtain ⟨N₀, hN₀⟩ := hCMr Q
  set C2 := ((Q / ε) / (2 * (32 * c₀)⁻¹)) ^ ((Q / ε) / 2) with hC2
  have hC20 : 0 ≤ C2 := Real.rpow_nonneg (by positivity) _
  set N₁ : ℕ := max N₀ (⌈c₀ ^ (-100 : ℝ)⌉₊ + 1) with hN₁
  set Cr := (r.factorial : ℝ) * max C 0 + 1 with hCr
  have hCr1 : 1 ≤ Cr := by
    have : 0 ≤ (r.factorial : ℝ) * max C 0 := mul_nonneg (by positivity) (le_max_right _ _)
    linarith
  refine ⟨C1 * (1 + 3 * C2 + (N₁ : ℝ) ^ (P + K)), fun N hN F E hC q hq ℓ => ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set Z := ∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀ with hZdef
  have hZ0 : 0 ≤ Z := integral_nonneg fun A0 => BlockBand.Palm.scalarWeight_nonneg _ _ _ _
  have hNκ : 0 ≤ (N : ℝ) ^ (-κ) := Real.rpow_nonneg hN'.le _
  have hNK : 0 ≤ (N : ℝ) ^ (-K) := Real.rpow_nonneg hN'.le _
  have hN1pow : 0 ≤ (N₁ : ℝ) ^ (P + K) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCrK0 : 0 ≤ C1 * (1 + 3 * C2 + (N₁ : ℝ) ^ (P + K)) := by positivity
  -- the target is implied by an error of size `C1 (1 + 3C2 + N₁^{P+K}) N^{-K}` plus `r!C⁺N^{-κ}Z`
  have hfinal : ∀ e : ℝ, e ≤ (r.factorial : ℝ) * max C 0 * (N : ℝ) ^ (-κ) * Z +
      C1 * (1 + 3 * C2 + (N₁ : ℝ) ^ (P + K)) * (N : ℝ) ^ (-K) →
      e ≤ Cr * ((N : ℝ) ^ (-κ) * Z + C1 * (1 + 3 * C2 + (N₁ : ℝ) ^ (P + K)) * (N : ℝ) ^ (-K)) := by
    intro e he
    have h1 : 0 ≤ (N : ℝ) ^ (-κ) * Z := mul_nonneg hNκ hZ0
    have h2 : 0 ≤ C1 * (1 + 3 * C2 + (N₁ : ℝ) ^ (P + K)) * (N : ℝ) ^ (-K) :=
      mul_nonneg hCrK0 hNK
    rw [hCr]
    nlinarith
  apply hfinal
  by_cases hNN : N₁ ≤ N
  · -- large `N`: the conditional-moment lemma and the window transfer
    have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hNN
    have hNc : c₀ ^ (-100 : ℝ) ≤ (N : ℝ) := by
      have h1 : (⌈c₀ ^ (-100 : ℝ)⌉₊ + 1 : ℕ) ≤ N := le_trans (le_max_right _ _) hNN
      have h2 : c₀ ^ (-100 : ℝ) ≤ (⌈c₀ ^ (-100 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ((⌈c₀ ^ (-100 : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
      push_cast at h3
      linarith
    have ha : 0 ≤ c₀ - (N : ℝ) ^ (-(1 / 100 : ℝ)) := sub_nonneg.mpr (rpow_neg_hundredth_le hc₀ hNc)
    have hac : c₀ - (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ c₀ :=
      sub_le_self _ (Real.rpow_nonneg hN'.le _)
    obtain ⟨B, hBm, hBμ, hBcm⟩ := hN₀ N hN0 F E hC q hq
    have h := palm_error_flow hK hN hC hq ℓ r ha hac hBm hBμ hBcm
    have hT := tail_le_power hc₀ hN hε hQ0
    refine h.trans ?_
    have hPQ : (N : ℝ) ^ P * (N : ℝ) ^ (-Q) = (N : ℝ) ^ (-K) := by
      rw [← Real.rpow_add hN']; congr 1; rw [hQ]; ring
    have e1 : C1 * (N : ℝ) ^ P * ((N : ℝ) ^ (-Q) + 3 * Real.exp (-((N : ℝ) ^ (-1 + ε) / 4) ^ 2 /
          (2 * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))) ≤
        C1 * (N : ℝ) ^ P * ((N : ℝ) ^ (-Q) + 3 * (C2 * (N : ℝ) ^ (-Q))) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC10 (Real.rpow_nonneg hN'.le _))
    have e2 : C1 * (N : ℝ) ^ P * ((N : ℝ) ^ (-Q) + 3 * (C2 * (N : ℝ) ^ (-Q))) =
        C1 * (1 + 3 * C2) * ((N : ℝ) ^ P * (N : ℝ) ^ (-Q)) := by ring
    rw [hPQ] at e2
    have e3 : C1 * (1 + 3 * C2) * (N : ℝ) ^ (-K) ≤
        C1 * (1 + 3 * C2 + (N₁ : ℝ) ^ (P + K)) * (N : ℝ) ^ (-K) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC10) hNK
    linarith
  · -- small `N < N₁`: the raw bound
    have hlt : (N : ℝ) ≤ N₁ := by exact_mod_cast (le_of_lt (not_le.mp hNN))
    have h := palm_error_raw hK hN hC hq ℓ r
    refine h.trans ?_
    have hsplit : (N : ℝ) ^ P = (N : ℝ) ^ (P + K) * (N : ℝ) ^ (-K) := by
      rw [← Real.rpow_add hN']; congr 1; ring
    have e1 : (N : ℝ) ^ (P + K) ≤ (N₁ : ℝ) ^ (P + K) :=
      Real.rpow_le_rpow hN'.le hlt (by linarith)
    have e2 : C1 * (N : ℝ) ^ P ≤ C1 * (1 + 3 * C2 + (N₁ : ℝ) ^ (P + K)) * (N : ℝ) ^ (-K) := by
      rw [hsplit, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC10) hNK
    have e3 : 0 ≤ (r.factorial : ℝ) * max C 0 * (N : ℝ) ^ (-κ) * Z :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (le_max_right _ _)) hNκ) hZ0
    linarith

/-- **The fresh Palm theorem from the conditional-moments lemma.** Constants: `κ` is the lemma's
`κ_r`, `C_r = r! max(C,0) + 1`, and for each `K > 0`,
`C_{r,K} = rawConst (1 + 3 C₂ + N₁^{P+K})` with `P = rawExp A r`, `N₁` from the lemma at
`D = K + P`. -/
theorem freshPalm_of_conditionalMoments (hCM : ConditionalMomentsStatement) :
    FreshPalmContract := by
  intro A c₀ r₀ s₀ v₀ hK r hr
  obtain ⟨ε, κ, C, hε, hκ, hCMr⟩ := hCM A c₀ r₀ s₀ v₀ hK r hr
  refine ⟨κ, hκ, (r.factorial : ℝ) * max C 0 + 1, fun K hKpos => ?_⟩
  obtain ⟨CrK, hCrK⟩ := palm_error_normalized hK hε hCMr hKpos
  refine ⟨CrK, fun N hN F E hC q ℓ => ?_⟩
  dsimp only
  have hr0 : r ≠ 0 := by omega
  by_cases hq0 : q = 0
  · subst hq0
    have h0 : ∀ A0, palmOverlap F 0 ℓ A0 = 0 := fun A0 => by simp [palmOverlap]
    have hγ : quadForm (freshGamma F c₀ E) (0 : Fin N → ℂ) = 0 := by simp [quadForm]
    simp only [h0, hγ, zero_pow hr0, mul_zero, zero_mul, integral_zero, sub_zero, abs_zero, le_refl]
  · set γ := quadForm (freshGamma F c₀ E) q with hγdef
    have hγ : 0 < γ := freshGamma_quad_pos hN hK hC hq0
    set s := Real.sqrt γ with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hγ
    set q' : Fin N → ℂ := ((s⁻¹ : ℝ) : ℂ) • q with hq'
    have hq'1 : quadForm (freshGamma F c₀ E) q' = 1 := by
      rw [hq', quadForm_smul, ← hγdef, inv_pow, hs, Real.sq_sqrt hγ.le, inv_mul_cancel₀ hγ.ne']
    have hqq : q = ((s : ℝ) : ℂ) • q' := by
      rw [hq', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one,
        one_smul]
    have hpo : ∀ A0, palmOverlap F q ℓ A0 = γ * palmOverlap F q' ℓ A0 := fun A0 => by
      conv_lhs => rw [hqq]
      rw [palmOverlap_smul, hs, Real.sq_sqrt hγ.le]
    have hL : (∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F q ℓ A0 ^ r ∂freshTracelessLaw N c₀) =
        γ ^ r * ∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F q' ℓ A0 ^ r ∂freshTracelessLaw N c₀ := by
      rw [← integral_const_mul]
      congr 1
      funext A0
      rw [hpo, mul_pow]
      ring
    have h := hCrK N hN F E hC q' hq'1 ℓ
    rw [hL]
    have hγr : 0 < γ ^ r := pow_pos hγ r
    calc |γ ^ r * (∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F q' ℓ A0 ^ r ∂freshTracelessLaw N c₀) -
          (r.factorial : ℝ) * γ ^ r * ∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀|
        = γ ^ r * |(∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F q' ℓ A0 ^ r
            ∂freshTracelessLaw N c₀) -
            (r.factorial : ℝ) * ∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀| := by
          rw [← abs_of_pos hγr, ← abs_mul, abs_of_pos hγr]
          ring_nf
      _ ≤ γ ^ r * (((r.factorial : ℝ) * max C 0 + 1) *
          ((N : ℝ) ^ (-κ) * (∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀) +
            CrK * (N : ℝ) ^ (-K))) := mul_le_mul_of_nonneg_left h hγr.le
      _ = _ := by ring

end BlockBand.Palm.FreshPalmAssembly

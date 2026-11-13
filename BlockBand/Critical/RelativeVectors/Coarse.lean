module

public import BlockBand.Critical.RelativeVectors.Distant
public import BlockBand.Palm.GoodEventHolds
public import BlockBand.Palm.MomentFlow.EventTimeDet
public import BlockBand.Palm.MomentFlow.EventGamma
public import BlockBand.Critical.WeightedDensity.Relative

/-!
# The coarse law along the flow

The distant-label bound and the first line of the interval bound for the relative vectors.

*Measure:* `flowLaw N a`, `a = rmvStart c N = c - N^{-1/500}`; `H_s = flowMatrix F a ω s`.
*Domain:* fixed `A`, `FreshConstants c r₀ s₀ v₀`; every `F` in `FreshClass F A c E r₀ s₀ v₀`.
*Uniformity:* the constants depend on `(c, r₀, s₀, v₀)` and `r` only; the event is uniform over
all `s ∈ [a, c]`, all energies `|x - E| ≤ r₀/2`, heights `N^{-1/100} ≤ η ≤ 1`, labels and frames.

* `coarseBadSet`: the failure set of `CoarseRelativeContract`.
* `column_quad_le_of_good` (deterministic, all times): on the dyadic chaining event of the
  Brownian part and off the failure sets at the dyadic times `a + jt2^{-m}`, the same bound with
  constant `2K + 1` holds at every `s ∈ [a, c]` (resolvent comparison and the chaining modulus;
  the mesh level absorbs `‖w‖² ≤ N^{2max(A,1)} w^*Γw/(v₀ lowConst)`).
* `coarse_quad_uniform`: for every finite family `Q` with `|Q| ≤ N^b`, the bound
  `Im w^*G_s(x+iη)w ≤ (2K+1) w^*Γw` holds for all `s ∈ [a,c]`, `|x-E| ≤ r₀/2`,
  `N^{-1/100} ≤ η ≤ 1`, `w ∈ Q` outside `flowLaw`-probability `N^{-D}`.
* `relativeCoarse_event`: with `Q` the columns of a frame `V` with `V^*ΓV = I_r`, outside
  probability `N^{-D}`, at every `s ∈ [a, c]` with simple spectrum:
  1. `‖z_i(s)‖² ≤ C_r N h` (`h = N^{-1/100}`) whenever `|λ_i(s) - E| ≤ r₀/2`, `C_r = r(2K+1)`;
  2. the distant-label bound in quadratic-form form: for `|λ_j(s) - E| ≤ r₀/8` and all
     `q ∈ ℂ^r`, `Σ_{|λ_i-E|>r₀/4} |q^*z_i|²/(N(λ_i-λ_j)²) ≤ C_r' Σ_a |q_a|²`,
     `C_r' = r(4 + 64/r₀²)(2K+1)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Set Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Critical.WeightedDensity BlockBand.Coarea.FreshPalm
open BlockBand.Palm.GoodEvent BlockBand.Palm.MomentFlow BlockBand.Palm.CoarseRelative
open scoped ENNReal NNReal

variable {N r : ℕ}

/-- The failure set of `CoarseRelativeContract` at variance `σ` for the family `Q`. -/
def coarseBadSet (F : Matrix (Fin N) (Fin N) ℂ) (E r₀ σ : ℝ) (Q : Finset (Fin N → ℂ)) :
    Set (Matrix (Fin N) (Fin N) ℂ) :=
  {G | ∃ x η : ℝ, |x - E| ≤ r₀ / 2 ∧ (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η ∧ η ≤ 1 ∧
    let z : ℂ := ⟨x, η⟩
    let R := (F + (Real.sqrt σ : ℂ) • G - z • 1)⁻¹
    (N : ℝ) ^ (-(1 / 3 : ℝ)) < ‖(N : ℂ)⁻¹ * R.trace - freshDyson F σ z‖ ∨
      ∃ q ∈ Q, (N : ℝ) ^ (-(1 / 3 : ℝ)) * (star q ⬝ᵥ (freshM F σ z *ᵥ q)).im <
        ‖star q ⬝ᵥ ((R - freshM F σ z) *ᵥ q)‖}

theorem gammaCompConst_pos {c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) :
    0 < gammaCompConst c r₀ s₀ v₀ := by
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hκ : 0 < (c - s₀) * v₀ := mul_pos (by linarith) hv0
  unfold gammaCompConst
  positivity

theorem lowConst_pos' {c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) :
    0 < lowConst c s₀ v₀ := by
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hκ : 0 < (c - s₀) * v₀ := mul_pos (by linarith) hv0
  unfold lowConst
  positivity

/-- **One time, off the coarse failure set.** `Im w^*G_σ(z)w ≤ 2K w^*Γw` for `w ∈ Q`. -/
theorem quad_im_le_of_not_coarseBad {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c E r₀ s₀ v₀ σ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    (hσ : σ ∈ Icc (c - s₀) c) {Q : Finset (Fin N → ℂ)} {G : Matrix (Fin N) (Fin N) ℂ}
    (hG : G ∉ coarseBadSet F E r₀ σ Q) {x η : ℝ} (hx : |x - E| ≤ r₀ / 2)
    (hη : (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η) (hη1 : η ≤ 1) {w : Fin N → ℂ} (hw : w ∈ Q) :
    (star w ⬝ᵥ ((F + (Real.sqrt σ : ℂ) • G - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ
        w)).im ≤ 2 * gammaCompConst c r₀ s₀ v₀ * quadForm (freshGamma F c E) w := by
  set R := (F + (Real.sqrt σ : ℂ) • G - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  set M := freshM F σ ⟨x, η⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hNr _
  have hp1 : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  have h2 : ‖star w ⬝ᵥ ((R - M) *ᵥ w)‖ ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)) * (star w ⬝ᵥ (M *ᵥ w)).im := by
    by_contra h
    exact hG ⟨x, η, hx, hη, hη1, Or.inr ⟨w, hw, lt_of_not_ge h⟩⟩
  have hMpos : 0 ≤ (star w ⬝ᵥ (M *ᵥ w)).im := by
    have := (norm_nonneg _).trans h2
    exact nonneg_of_mul_nonneg_right (by linarith) hp
  have h1 := im_quad_le R M w
  have hηpos : 0 ≤ η := le_trans (Real.rpow_pos_of_pos hNr _).le hη
  have h3 := quad_im_le_gamma hN hK hC hσ (z := ⟨x, η⟩) (by simpa using hx.trans (by
    linarith [hK.2.2.1])) hηpos hη1 w
  have hΓ : 0 ≤ quadForm (freshGamma F c E) w :=
    quadForm_freshGamma_nonneg F hK.1.le E w
  nlinarith

/-- `1/η² ≤ N^{1/50}` for `η ≥ N^{-1/100}`. -/
theorem inv_sq_le_of_ge {η : ℝ} (hN : 0 < N) (hη : (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η) :
    1 / η ^ 2 ≤ (N : ℝ) ^ (1 / 50 : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < (N : ℝ) ^ (-(1 / 100 : ℝ)) := Real.rpow_pos_of_pos hNr _
  have hsq : ((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 2 = ((N : ℝ) ^ (1 / 50 : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le, ← Real.rpow_neg hNr.le]
    norm_num
  have : ((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hh.le hη 2
  rw [hsq] at this
  have hpos : 0 < (N : ℝ) ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos hNr _
  rw [div_le_iff₀ (lt_of_lt_of_le (inv_pos.2 hpos) this)]
  calc (1 : ℝ) = (N : ℝ) ^ (1 / 50 : ℝ) * ((N : ℝ) ^ (1 / 50 : ℝ))⁻¹ := by field_simp
    _ ≤ (N : ℝ) ^ (1 / 50 : ℝ) * η ^ 2 := mul_le_mul_of_nonneg_left this hpos.le

/-- **All times, on the mesh good event** (deterministic). -/
theorem column_quad_le_of_good {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {a t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hapos : 0 < a) (has₀ : c - s₀ ≤ a) (hac : a + t = c)
    {K₁ : ℝ} (hK₁ : 0 ≤ K₁) {m : ℕ}
    (hm : K₁ * chainRatio ^ m / (1 - chainRatio) ≤
      v₀ * lowConst c s₀ v₀ * (N : ℝ) ^ (-(2 * max A 1 + 1 / 50)))
    {Q : Finset (Fin N → ℂ)} {ω : FlowSample N} (hω : ω.1.IsHermitian)
    (hch : ChainGood K₁ t ω.2)
    (hgood : ∀ j : ℕ, j < 2 ^ m →
      flowNormalized a (a + (j : ℝ) * t / 2 ^ m) ω ∉
        coarseBadSet F E r₀ (a + (j : ℝ) * t / 2 ^ m) Q) :
    ∀ s ∈ Icc a c, ∀ x η : ℝ, |x - E| ≤ r₀ / 2 → (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 →
      ∀ w ∈ Q, (star w ⬝ᵥ ((flowMatrix F a ω s - (⟨x, η⟩ : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ w)).im ≤
        (2 * gammaCompConst c r₀ s₀ v₀ + 1) * quadForm (freshGamma F c E) w := by
  intro s hs x η hx hη hη1 w hw
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨j, hj, hj1, hj2⟩ := exists_cell ht (sub_nonneg.2 hs.1) (by linarith [hs.2]) m
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hj0 : 0 ≤ (j : ℝ) * t / 2 ^ m := by positivity
  have hjt : (j : ℝ) * t / 2 ^ m ≤ t := by
    rw [div_le_iff₀ h2m]
    have : (j : ℝ) ≤ 2 ^ m := by exact_mod_cast hj.le
    nlinarith
  set sj := a + (j : ℝ) * t / 2 ^ m with hsj
  have hsjpos : 0 < sj := by linarith
  have hsjreg : sj ∈ Icc (c - s₀) c := ⟨by linarith, by linarith⟩
  have hηpos : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr _) hη
  have hcmp := resolvent_quad_im_compare (BlockBand.Palm.GoodEvent.flowMatrix_isHermitian hC.1 a hω s)
    (BlockBand.Palm.GoodEvent.flowMatrix_isHermitian hC.1 a hω sj) (z := ⟨x, η⟩) hηpos w
  -- the value at the mesh time
  have hmesh := quad_im_le_of_not_coarseBad hN hK hC hsjreg (hgood j hj) hx hη hη1 hw
  rw [← flowMatrix_eq_normalized F a ω hsjpos] at hmesh
  -- the modulus
  have hmod : opB (flowMatrix F a ω s - flowMatrix F a ω sj) ≤
      v₀ * lowConst c s₀ v₀ * (N : ℝ) ^ (-(2 * max A 1 + 1 / 50)) := by
    rw [BlockBand.Palm.GoodEvent.flowMatrix_sub, show sj - a = (j : ℝ) * t / 2 ^ m by rw [hsj]; ring]
    refine (chainGood_modulus hK₁ ht hch m j hj (u := s - a) hj1 hj2).trans (le_trans ?_ hm)
    have hq1 : 0 < 1 - chainRatio := sub_pos.mpr chainRatio_lt_one
    apply div_le_div_of_nonneg_right _ hq1.le
    have hst : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
    have h0 : 0 ≤ K₁ * chainRatio ^ m := by have := chainRatio_pos; positivity
    nlinarith [Real.sqrt_nonneg t]
  -- the error term
  have hnsq := nsq_le_of_gamma hN hK hC w
  have hL := lowConst_pos' hK
  have hv0 := hK.2.2.2.2.2
  have hΓ : 0 ≤ quadForm (freshGamma F c E) w := quadForm_freshGamma_nonneg F hK.1.le E w
  have hinv := inv_sq_le_of_ge hN hη
  have herr : opB (flowMatrix F a ω s - flowMatrix F a ω sj) * nsq w / (⟨x, η⟩ : ℂ).im ^ 2 ≤
      quadForm (freshGamma F c E) w := by
    have him : (⟨x, η⟩ : ℂ).im = η := rfl
    rw [him]
    have hop0 : 0 ≤ opB (flowMatrix F a ω s - flowMatrix F a ω sj) := norm_nonneg _
    have hns0 : 0 ≤ nsq w := nsq_nonneg w
    set P := (N : ℝ) ^ (2 * max A 1)
    have hP : 0 < P := Real.rpow_pos_of_pos hNr _
    have hkey : (N : ℝ) ^ (-(2 * max A 1 + 1 / 50)) * P * (N : ℝ) ^ (1 / 50 : ℝ) = 1 := by
      rw [← Real.rpow_add hNr, ← Real.rpow_add hNr]; norm_num
    calc opB (flowMatrix F a ω s - flowMatrix F a ω sj) * nsq w / η ^ 2
        = opB (flowMatrix F a ω s - flowMatrix F a ω sj) * nsq w * (1 / η ^ 2) := by ring
      _ ≤ (v₀ * lowConst c s₀ v₀ * (N : ℝ) ^ (-(2 * max A 1 + 1 / 50))) *
            (P * quadForm (freshGamma F c E) w / (v₀ * lowConst c s₀ v₀)) *
            (N : ℝ) ^ (1 / 50 : ℝ) := by
          apply mul_le_mul (mul_le_mul hmod hnsq hns0 (by positivity)) hinv (by positivity)
            (by positivity)
      _ = quadForm (freshGamma F c E) w *
            ((N : ℝ) ^ (-(2 * max A 1 + 1 / 50)) * P * (N : ℝ) ^ (1 / 50 : ℝ)) := by
          field_simp
      _ = quadForm (freshGamma F c E) w := by rw [hkey, mul_one]
  linarith

/-- Polynomial bookkeeping of the union bound. -/
theorem coarse_numeric (A' D Qc : ℝ) (hA' : 0 ≤ A') : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    2 * (1 / 2 : ℝ) ^ N + (1 + Qc * (N : ℝ) ^ (8 * A' + 8 / 100)) *
      (N : ℝ) ^ (-(D + 8 * A' + 1)) ≤ (N : ℝ) ^ (-D) := by
  have e1 := ev_exp_le 6 0 (-D)
  have e2 := ev_poly_le 3 (-(D + 8 * A' + 1)) (-D) (by linarith)
  have e3 := ev_poly_le (3 * Qc) (-D - 1 + 8 / 100) (-D) (by linarith)
  obtain ⟨N₀, hN₀⟩ := (e1.and (e2.and (e3.and (eventually_ge_atTop 1)))).exists_forall_of_atTop
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3, hN1⟩ := hN₀ N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.rpow_zero, mul_one] at h1
  have e : (1 + Qc * (N : ℝ) ^ (8 * A' + 8 / 100)) * (N : ℝ) ^ (-(D + 8 * A' + 1)) =
      (N : ℝ) ^ (-(D + 8 * A' + 1)) + Qc * (N : ℝ) ^ (-D - 1 + 8 / 100) := by
    rw [add_mul, one_mul, mul_assoc, ← Real.rpow_add hNr]
    congr 3; ring
  rw [e]
  nlinarith

/-- **The coarse isotropic bound along the flow, uniformly in time.** -/
theorem coarse_quad_uniform (hCR : CoarseRelativeContract) (hLp : GaussianLpGradient)
    {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) (b : ℝ) :
    ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
    ∀ Q : Finset (Fin N → ℂ), (Q.card : ℝ) ≤ (N : ℝ) ^ b →
      flowLaw N (rmvStart c N) {ω | ¬ ∀ s ∈ Icc (rmvStart c N) c, ∀ x η : ℝ,
        |x - E| ≤ r₀ / 2 → (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 → ∀ w ∈ Q,
          (star w ⬝ᵥ ((flowMatrix F (rmvStart c N) ω s - (⟨x, η⟩ : ℂ) •
            (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ w)).im ≤
          (2 * gammaCompConst c r₀ s₀ v₀ + 1) * quadForm (freshGamma F c E) w} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro D
  have hK0 := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK0
  obtain ⟨K₁, hK₁, hCE⟩ := chain_event hLp
  have hq1 : 0 < 1 - chainRatio := sub_pos.mpr chainRatio_lt_one
  have hL := lowConst_pos' hK
  set A' := max A 1 with hA'
  set Qc := 2 * (K₁ / (1 - chainRatio)) ^ 4 * ((v₀ * lowConst c s₀ v₀)⁻¹) ^ 4 with hQc
  have hQc0 : 0 ≤ Qc := by positivity
  set D' := D + 8 * A' + 1 with hD'
  obtain ⟨Ncr, hNcr⟩ := hCR A c r₀ s₀ v₀ hK b D'
  obtain ⟨Nnum, hNnum⟩ := coarse_numeric A' D Qc (by positivity)
  have ht0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 500 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nt, hNt⟩ := (eventually_atTop.1 (ht0.eventually (gt_mem_nhds hs0)))
  refine ⟨max (max Ncr Nnum) (max Nt 8), ?_⟩
  intro N hN F E hC Q hQ
  have hNcr' := hNcr N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have hnum := hNnum N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have htN := hNt N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have h8 : 8 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hK' : FreshConstants c r₀ s₀ v₀ := ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩
  set t := (N : ℝ) ^ (-(1 / 500 : ℝ)) with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos hNr _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN0) (by norm_num)
  have ha : rmvStart c N = c - t := rfl
  rw [ha]
  set a := c - t with hadef
  have hapos : 0 < a := by linarith
  have has₀ : c - s₀ ≤ a := by linarith
  have hac : a + t = c := by ring
  set δ := v₀ * lowConst c s₀ v₀ * (N : ℝ) ^ (-(2 * A' + 1 / 50)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨m, hm, h2m⟩ := exists_mesh_level hK₁ hδpos
  -- covering
  have hsub : {ω : FlowSample N | ¬ ∀ s ∈ Icc a c, ∀ x η : ℝ,
        |x - E| ≤ r₀ / 2 → (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 → ∀ w ∈ Q,
          (star w ⬝ᵥ ((flowMatrix F a ω s - (⟨x, η⟩ : ℂ) •
            (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ w)).im ≤
          (2 * gammaCompConst c r₀ s₀ v₀ + 1) * quadForm (freshGamma F c E) w} ⊆
      ({ω : FlowSample N | ¬ ω.1.IsHermitian} ∪ {ω | ¬ ChainGood K₁ t ω.2}) ∪
        ⋃ j ∈ Finset.range (2 ^ m), {ω | flowNormalized a (a + (j : ℝ) * t / 2 ^ m) ω ∈
          coarseBadSet F E r₀ (a + (j : ℝ) * t / 2 ^ m) Q} := by
    intro ω hω
    by_contra hcon
    apply hω
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
      Finset.mem_range] at hcon
    obtain ⟨⟨hH, hCh⟩, hJ⟩ := hcon
    push Not at hH hCh
    exact column_quad_le_of_good hN0 hK' hC ht ht1 hapos has₀ hac hK₁.le hm hH hCh
      (fun j hj => hJ j hj)
  refine (measure_mono hsub).trans ?_
  refine ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _))).trans ?_
  have hS : ∀ j ∈ Finset.range (2 ^ m), flowLaw N a {ω | flowNormalized a (a + (j : ℝ) * t / 2 ^ m)
      ω ∈ coarseBadSet F E r₀ (a + (j : ℝ) * t / 2 ^ m) Q} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h2m0 : (0 : ℝ) < 2 ^ m := by positivity
    have hjt : (j : ℝ) * t / 2 ^ m ≤ t := by
      rw [div_le_iff₀ h2m0]
      have : (j : ℝ) ≤ 2 ^ m := by exact_mod_cast hj.le
      nlinarith
    have hj0 : 0 ≤ (j : ℝ) * t / 2 ^ m := by positivity
    have hsja : a ≤ a + (j : ℝ) * t / 2 ^ m := le_add_of_nonneg_right hj0
    have hsjreg : a + (j : ℝ) * t / 2 ^ m ∈ Icc (c - s₀) c := ⟨by linarith, by linarith⟩
    refine (flowLaw_preimage_normalized_le hN0 hapos hsja _).trans ?_
    exact hNcr' F E hC _ hsjreg Q hQ
  refine (add_le_add (add_le_add (le_of_eq (flowLaw_not_hermitian a)) (hCE N h8 a t ht))
    (Finset.sum_le_sum hS)).trans ?_
  rw [Finset.sum_const, Finset.card_range, zero_add, nsmul_eq_mul]
  have hc2m : ((2 ^ m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ m) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [hc2m, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ hnum
  have hδinv : (δ⁻¹) ^ 4 = ((v₀ * lowConst c s₀ v₀)⁻¹) ^ 4 * (N : ℝ) ^ (8 * A' + 8 / 100) := by
    have e1 : δ⁻¹ = (v₀ * lowConst c s₀ v₀)⁻¹ * (N : ℝ) ^ (2 * A' + 1 / 50) := by
      rw [hδ, mul_inv, Real.rpow_neg hNr.le, inv_inv]
    have e2 : ((N : ℝ) ^ (2 * A' + 1 / 50)) ^ 4 = (N : ℝ) ^ (8 * A' + 8 / 100) := by
      rw [← Real.rpow_mul_natCast hNr.le]; congr 1; push_cast; ring
    rw [e1, mul_pow, e2]
  have h2m' : (2 : ℝ) ^ m ≤ 1 + Qc * (N : ℝ) ^ (8 * A' + 8 / 100) := by
    refine h2m.trans (le_of_eq ?_)
    rw [hδinv, hQc]; ring
  have := mul_le_mul_of_nonneg_right h2m' (Real.rpow_nonneg hNr.le (-D'))
  linarith

/-!
## The frame columns: the coarse interval and distant-label bounds
-/

/-- `Im w^*(K - x - iη)⁻¹w = Σ_ℓ |w^*u_ℓ|² η/((λ_ℓ-x)² + η²)` on simple spectrum. -/
theorem im_resolvent_quad_eq_at {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (w : Fin N → ℂ) (x η : ℝ) (hη : η ≠ 0) :
    (star w ⬝ᵥ ((K - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ w)).im =
      ∑ ℓ, Complex.normSq (star w ⬝ᵥ freshEigenvector K ℓ) * η /
        ((freshEigenvalue K ℓ - x) ^ 2 + η ^ 2) := by
  rw [hK.inv_eq_sum (z := (⟨x, η⟩ : ℂ)) hη, Matrix.sum_mulVec, dotProduct_sum,
    Complex.im_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [smul_mulVec, dotProduct_smul, freshProjector, vecMulVec_mulVec]
  set u := freshEigenvector K ℓ
  set p := star w ⬝ᵥ u with hp
  have hprod : star w ⬝ᵥ (MulOpposite.op (star u ⬝ᵥ w) • u) = (Complex.normSq p : ℂ) := by
    rw [op_smul_eq_smul, dotProduct_smul, smul_eq_mul, star_dotProduct, ← hp,
      Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hprod, smul_eq_mul, mul_comm, Complex.im_ofReal_mul, Complex.inv_im]
  have hns : Complex.normSq (((freshEigenvalue K ℓ : ℝ) : ℂ) - (⟨x, η⟩ : ℂ)) =
      (freshEigenvalue K ℓ - x) ^ 2 + η ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [hns]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub]
  ring

/-- `|w^*u_i|² ≤ η Im w^*(K - λ_i - iη)⁻¹w`. -/
theorem normSq_le_eta_im {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (w : Fin N → ℂ) (i : Fin N) {η : ℝ} (hη : 0 < η) :
    Complex.normSq (star w ⬝ᵥ freshEigenvector K i) ≤
      η * (star w ⬝ᵥ ((K - (⟨freshEigenvalue K i, η⟩ : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ w)).im := by
  rw [im_resolvent_quad_eq_at hK w _ η hη.ne', Finset.mul_sum]
  have hterm : ∀ ℓ, 0 ≤ η * (Complex.normSq (star w ⬝ᵥ freshEigenvector K ℓ) * η /
      ((freshEigenvalue K ℓ - freshEigenvalue K i) ^ 2 + η ^ 2)) := fun ℓ => by
    have := Complex.normSq_nonneg (star w ⬝ᵥ freshEigenvector K ℓ)
    positivity
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun ℓ _ => hterm ℓ) (Finset.mem_univ i))
  rw [sub_self, show (0 : ℝ) ^ 2 + η ^ 2 = η ^ 2 by ring]
  field_simp

/-- The frame columns `V e_a`. -/
def frameColumns (V : Matrix (Fin N) (Fin r) ℂ) : Finset (Fin N → ℂ) :=
  Finset.univ.image fun b : Fin r => V *ᵥ Pi.single b 1

theorem frameColumns_card_le (V : Matrix (Fin N) (Fin r) ℂ) :
    (frameColumns V).card ≤ r := by
  unfold frameColumns
  exact (Finset.card_image_le).trans (by simp)

theorem quadForm_column {Γ : Matrix (Fin N) (Fin N) ℂ} {V : Matrix (Fin N) (Fin r) ℂ}
    (hV : Vᴴ * Γ * V = 1) (b : Fin r) : quadForm Γ (V *ᵥ Pi.single b 1) = 1 := by
  unfold quadForm
  have h : star (V *ᵥ Pi.single b 1) ⬝ᵥ (Γ *ᵥ (V *ᵥ Pi.single b 1)) = (Vᴴ * Γ * V) b b := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, mulVec_single_one]
    simp [dotProduct, Pi.single_apply, Matrix.mul_assoc]
  rw [h, hV]; simp

/-- `|q^*z|² ≤ (Σ_a |q_a|²)(Σ_a |z_a|²)` (Cauchy–Schwarz). -/
theorem norm_star_dot_sq_le (q z : Fin r → ℂ) :
    ‖star q ⬝ᵥ z‖ ^ 2 ≤ (∑ b, ‖q b‖ ^ 2) * ∑ b, ‖z b‖ ^ 2 := by
  have h1 : ‖star q ⬝ᵥ z‖ ≤ ∑ b, ‖q b‖ * ‖z b‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    rw [norm_mul, Pi.star_apply, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => ‖q b‖) (fun b => ‖z b‖)
  calc ‖star q ⬝ᵥ z‖ ^ 2 ≤ (∑ b, ‖q b‖ * ‖z b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem frameArray_apply_sq (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ)
    (i : Fin N) (b : Fin r) :
    ‖frameArray V K i b‖ ^ 2 =
      N * Complex.normSq (star (V *ᵥ Pi.single b 1) ⬝ᵥ freshEigenvector K i) := by
  rw [← norm_star_frameArray_sq]
  congr 2
  simp [dotProduct, Pi.single_apply]

/-- `C_r = r(2K+1)`, the constant of the first line of the interval bound. -/
def relCompConst (c r₀ s₀ v₀ : ℝ) (r : ℕ) : ℝ := r * (2 * gammaCompConst c r₀ s₀ v₀ + 1)

/-- `C_r' = r(4 + 64/r₀²)(2K+1)`, the constant of the distant-label bound. -/
def relDistConst (c r₀ s₀ v₀ : ℝ) (r : ℕ) : ℝ :=
  r * (4 + 64 / r₀ ^ 2) * (2 * gammaCompConst c r₀ s₀ v₀ + 1)

/-- **Deterministic bound.** If every frame column has `Im w^*G(x+iη)w ≤ B` on the coarse domain,
then the first line of the interval bound and the distant-label bound hold. -/
theorem relativeCoarse_of_quad {K : Matrix (Fin N) (Fin N) ℂ} (hKs : SimpleSpectrum K)
    (V : Matrix (Fin N) (Fin r) ℂ) {E r₀ B : ℝ} (hr₀ : 0 < r₀) (hN : 0 < N)
    (hB : ∀ x η : ℝ, |x - E| ≤ r₀ / 2 → (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 → ∀ b : Fin r,
      (star (V *ᵥ Pi.single b 1) ⬝ᵥ ((K - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ
        (V *ᵥ Pi.single b 1))).im ≤ B) :
    (∀ i : Fin N, |freshEigenvalue K i - E| ≤ r₀ / 2 →
      ∑ b, ‖frameArray V K i b‖ ^ 2 ≤ r * B * (N * (N : ℝ) ^ (-(1 / 100 : ℝ)))) ∧
    (∀ j : Fin N, |freshEigenvalue K j - E| ≤ r₀ / 8 → ∀ q : Fin r → ℂ,
      ∑ i ∈ Finset.univ.filter (fun i => r₀ / 4 < |freshEigenvalue K i - E|),
          ‖star q ⬝ᵥ frameArray V K i‖ ^ 2 /
            ((N : ℝ) * (freshEigenvalue K i - freshEigenvalue K j) ^ 2) ≤
        r * (4 + 64 / r₀ ^ 2) * B * ∑ b, ‖q b‖ ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < (N : ℝ) ^ (-(1 / 100 : ℝ)) := Real.rpow_pos_of_pos hNr _
  have hh1 : (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  refine ⟨fun i hi => ?_, fun j hj q => ?_⟩
  · calc ∑ b, ‖frameArray V K i b‖ ^ 2
        ≤ ∑ _b : Fin r, (N : ℝ) * ((N : ℝ) ^ (-(1 / 100 : ℝ)) * B) := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [frameArray_apply_sq]
          refine mul_le_mul_of_nonneg_left ?_ hNr.le
          refine (normSq_le_eta_im hKs _ i hh).trans ?_
          exact mul_le_mul_of_nonneg_left (hB _ _ hi le_rfl hh1 b) hh.le
      _ = r * B * (N * (N : ℝ) ^ (-(1 / 100 : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · set S := Finset.univ.filter (fun i => r₀ / 4 < |freshEigenvalue K i - E|)
    set d : Fin N → ℝ := fun i => (N : ℝ) * (freshEigenvalue K i - freshEigenvalue K j) ^ 2
    have hd : ∀ i, 0 ≤ d i := fun i => by positivity
    have hEI : ((E : ℂ) + Complex.I) = (⟨E, 1⟩ : ℂ) := Complex.ext (by simp) (by simp)
    have hcol : ∀ b : Fin r, ∑ i ∈ S, ‖frameArray V K i b‖ ^ 2 / d i ≤
        (4 + 64 / r₀ ^ 2) * B := by
      intro b
      have h := distant_sum_le hKs V (Pi.single b 1) hr₀ j hj
      have he : ∀ i, star (Pi.single b (1 : ℂ)) ⬝ᵥ frameArray V K i = frameArray V K i b := by
        intro i; simp [dotProduct, Pi.single_apply]
      simp only [he] at h
      rw [hEI] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact hB E 1 (by simp only [sub_self, abs_zero]; linarith) (by linarith) le_rfl b
    calc ∑ i ∈ S, ‖star q ⬝ᵥ frameArray V K i‖ ^ 2 / d i
        ≤ ∑ i ∈ S, (∑ b, ‖q b‖ ^ 2) * (∑ b, ‖frameArray V K i b‖ ^ 2) / d i :=
          Finset.sum_le_sum fun i _ =>
            div_le_div_of_nonneg_right (norm_star_dot_sq_le q _) (hd i)
      _ = (∑ b, ‖q b‖ ^ 2) * ∑ b, ∑ i ∈ S, ‖frameArray V K i b‖ ^ 2 / d i := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_div_assoc, Finset.sum_div]
      _ ≤ (∑ b, ‖q b‖ ^ 2) * ∑ _b : Fin r, (4 + 64 / r₀ ^ 2) * B :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hcol b)
            (Finset.sum_nonneg fun _ _ => by positivity)
      _ = r * (4 + 64 / r₀ ^ 2) * B * ∑ b, ‖q b‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **The coarse interval and distant-label bounds along the flow**, uniformly in `s ∈ [a, c]`,
outside `flowLaw`-probability `N^{-D}`. -/
theorem relativeCoarse_event (hCR : CoarseRelativeContract) (hLp : GaussianLpGradient)
    {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) (r : ℕ) :
    ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
    ∀ V : Matrix (Fin N) (Fin r) ℂ, Vᴴ * freshGamma F c E * V = 1 →
      flowLaw N (rmvStart c N) {ω | ¬ ∀ s ∈ Icc (rmvStart c N) c,
        SimpleSpectrum (flowMatrix F (rmvStart c N) ω s) →
        (∀ i : Fin N, |flowEigenvalue F (rmvStart c N) ω s i - E| ≤ r₀ / 2 →
          ∑ b, ‖frameArray V (flowMatrix F (rmvStart c N) ω s) i b‖ ^ 2 ≤
            relCompConst c r₀ s₀ v₀ r * (N * (N : ℝ) ^ (-(1 / 100 : ℝ)))) ∧
        (∀ j : Fin N, |flowEigenvalue F (rmvStart c N) ω s j - E| ≤ r₀ / 8 →
          ∀ q : Fin r → ℂ,
          ∑ i ∈ Finset.univ.filter
              (fun i => r₀ / 4 < |flowEigenvalue F (rmvStart c N) ω s i - E|),
            ‖star q ⬝ᵥ frameArray V (flowMatrix F (rmvStart c N) ω s) i‖ ^ 2 /
              ((N : ℝ) * (flowEigenvalue F (rmvStart c N) ω s i -
                flowEigenvalue F (rmvStart c N) ω s j) ^ 2) ≤
            relDistConst c r₀ s₀ v₀ r * ∑ b, ‖q b‖ ^ 2)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro D
  obtain ⟨N₁, hN₁⟩ := coarse_quad_uniform hCR hLp hK 1 D
  refine ⟨max N₁ (max r 1), fun N hN F E hC V hV => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le (by omega) (le_trans (le_max_right r 1)
    (le_trans (le_max_right _ _) hN))
  have hrN : r ≤ N := le_trans (le_trans (le_max_left r 1) (le_max_right _ _)) hN
  have hQ : ((frameColumns V).card : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]; exact_mod_cast (frameColumns_card_le V).trans hrN
  refine le_trans (measure_mono ?_) (hN₁ N (le_trans (le_max_left _ _) hN) F E hC _ hQ)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hgood
  apply hω
  intro s hs hKs
  have hB : ∀ x η : ℝ, |x - E| ≤ r₀ / 2 → (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 →
      ∀ b : Fin r, (star (V *ᵥ Pi.single b 1) ⬝ᵥ ((flowMatrix F (rmvStart c N) ω s -
        (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ (V *ᵥ Pi.single b 1))).im ≤
        2 * gammaCompConst c r₀ s₀ v₀ + 1 := by
    intro x η hx hη hη1 b
    have h := hgood s hs x η hx hη hη1 (V *ᵥ Pi.single b 1)
      (Finset.mem_image_of_mem _ (Finset.mem_univ b))
    rwa [quadForm_column hV, mul_one] at h
  obtain ⟨h1, h2⟩ := relativeCoarse_of_quad hKs V hK.2.2.1 hN0 hB
  refine ⟨fun i hi => ?_, fun j hj q => ?_⟩
  · have := h1 i hi
    unfold relCompConst
    exact this
  · have := h2 j hj q
    unfold relDistConst
    exact this

end BlockBand.Critical.RelativeVectors

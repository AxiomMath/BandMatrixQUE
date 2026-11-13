module

public import BlockBand.Critical.BoundaryMean.Phases
public import BlockBand.Critical.BoundaryMean.KernelForm
public import BlockBand.Critical.BoundaryMean.NormBound

/-!
# Step 6: the strict clause from the Hermitian statement

`strictClause_of_hermitian : HermitianCollarMeanStatement → (∀ b κ, ∃ constants,
StrictBoundaryMeanClause …)`. For `Y = -Im X ≻ 0`, `d(X) ≤ d_H/2`, `W ≥ W₀` and every direction `q`:
1. `q*E𝒫(Ur)q = η⁻¹ E f_0` (`KernelForm`);
2. `E f_0 = lim_{ν↓0} E f_ν` (dominated convergence, `Domination`);
3. `E f_ν = E_t h_ν(X_t, q)` (Fubini for the Cauchy dilation, `Fubini`);
4. retained phases `d(X_t) ≤ d(X) + W^{-1/8} ≤ d_H`: the Hermitian statement gives
   `|h_ν - η‖q‖²| ≤ (|C|(d(X) + W^{-1/8} + |ε_W|) + δ)‖q‖²` for small `ν`; omitted phases: mass
   `≤ C_D g/(W·W^{-1/4})` (`Phases`) and `|h_ν - η‖q‖²| ≤ (C_{b,w}√W + η)‖q‖²` (fresh-row bound);
5. `δ ↓ 0`; divide by `η ≥ η_min`; the Hermitian quadratic-form bound gives the operator norm.
The constants: `ε_W = |ε^H_W|`, `C = η_min⁻¹ max(|C_H|, (C_{b,5} + 1)C_D)`, `d₂ = d_H/2`,
`W₀ = max(W_H, W₁, 1)` with `W₁^{-1/8} < d_H/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Collar.Density (collarMatrix collarRowVec collarRowConst)
open BlockBand.Critical.Collar.Kernel (topLift rePart)
open BlockBand.Critical.Collar (stdCauchy)
open scoped ComplexOrder ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Step 6 for one direction `q`** (`Y ≻ 0`). If the Hermitian form is `A + δ‖q‖²`-close to
`η‖q‖²` on the retained phases `d(X_t) ≤ d̄` for all small heights, and the omitted phases have
Cauchy mass `≤ m`, then `|E_collar f_0 - η‖q‖²| ≤ A + (C_{b,w}√W + η)‖q‖² m`. -/
theorem abs_integral_regForm_sub_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 0 < W) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosDef)
    (q : Fin 2 × Fin W → ℂ) {dbar A m : ℝ} (hA : 0 ≤ A) (hm0 : 0 ≤ m)
    (hη : 0 ≤ (boundaryZ b e).im)
    (hret : ∀ δ : ℝ, 0 < δ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Set.Ioo 0 ν₀, ∀ t : ℝ,
      matchedDistance b e (dilatedOld X t) ≤ dbar →
        |hermitianCollarForm W b e ν (dilatedOld X t) q - (boundaryZ b e).im * ∑ x, ‖q x‖ ^ 2| ≤
          A + δ * ∑ x, ‖q x‖ ^ 2)
    (hexc : stdCauchy {t | ¬ matchedDistance b e (dilatedOld X t) ≤ dbar} ≤ ENNReal.ofReal m) :
    |∫ ω, regForm b e 0 X q ω ∂collarLaw W b - (boundaryZ b e).im * ∑ x, ‖q x‖ ^ 2| ≤
      A + (collarRowConst b (Collar.Kernel.rowCoeff b e 0) * Real.sqrt W +
        (boundaryZ b e).im) * (∑ x, ‖q x‖ ^ 2) * m := by
  set S := ∑ x, ‖q x‖ ^ 2
  set η := (boundaryZ b e).im
  set Cr := collarRowConst b (Collar.Kernel.rowCoeff b e 0)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hCr : 0 ≤ Cr := Collar.Density.collarRowConst_nonneg hb0.le _
  set K := (Cr * Real.sqrt W + η) * S
  have hK : 0 ≤ K := by positivity
  -- each small height
  have hstep : ∀ δ : ℝ, 0 < δ → |∫ ω, regForm b e 0 X q ω ∂collarLaw W b - η * S| ≤
      A + δ * S + K * m := by
    intro δ hδ
    obtain ⟨ν₀, hν₀, hν⟩ := hret δ hδ
    set ν' := min ν₀ 1
    have hν' : 0 < ν' := lt_min hν₀ one_pos
    set u : ℕ → ℝ := fun n => ν' / ((n : ℝ) + 2)
    have hu0 : ∀ n, 0 < u n := fun n => by positivity
    have hu1 : ∀ n, u n < ν' := fun n => by
      simp only [u]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hut : Tendsto u atTop (𝓝 0) := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
      simpa [u] using (tendsto_const_nhds (x := ν')).div_atTop h
    have hlim := tendsto_integral_regForm hb e hY q hu0
      (fun n => (hu1 n).le.trans (min_le_right _ _)) hut
    have hn : ∀ n, |∫ ω, regForm b e (u n) X q ω ∂collarLaw W b - η * S| ≤ A + δ * S + K * m := by
      intro n
      obtain ⟨hint, hbd, heq⟩ := integral_regForm_eq hb0 hb hW e hY.posSemidef (hu0 n) q
      rw [heq]
      refine abs_integral_sub_le_of_phases hint (by positivity) hK hm0 (fun t => ?_)
        (fun t ht => ?_) hexc
      · obtain ⟨h1, h2⟩ := hbd t
        rw [abs_le]
        constructor <;> nlinarith [mul_nonneg hη hS]
      · simp only [Set.mem_ofPred_eq, not_not] at ht
        exact hν (u n) ⟨hu0 n, (hu1 n).trans_le (min_le_left _ _)⟩ t ht
    have hc : Tendsto (fun n => |∫ ω, regForm b e (u n) X q ω ∂collarLaw W b - η * S|) atTop
        (𝓝 |∫ ω, regForm b e 0 X q ω ∂collarLaw W b - η * S|) :=
      ((hlim.sub tendsto_const_nhds).abs)
    exact le_of_tendsto' hc hn
  have hfin : |∫ ω, regForm b e 0 X q ω ∂collarLaw W b - η * S| ≤ A + K * m := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have h := hstep (δ / (S + 1)) (by positivity)
    have : δ / (S + 1) * S ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  calc _ ≤ A + K * m := hfin
    _ = _ := by simp only [K]

/-- Step 6 for one direction, with the Hermitian statement's data at fixed `W`, `e`. -/
theorem dir_bound {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 0 < W) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosDef)
    (q : Fin 2 × Fin W → ℂ) {CH εW w8 dH m : ℝ} (hw8 : 0 ≤ w8)
    (hd : matchedDistance b e X + w8 ≤ dH) (hm0 : 0 ≤ m) (hη : 0 ≤ (boundaryZ b e).im)
    (hHS : ∀ δ : ℝ, 0 < δ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Set.Ioo 0 ν₀,
      ∀ X' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X'.IsHermitian →
        matchedDistance b e X' ≤ dH → ∀ q : Fin 2 × Fin W → ℂ,
          |hermitianCollarForm W b e ν X' q - (boundaryZ b e).im * ∑ x, ‖q x‖ ^ 2| ≤
            (CH * (matchedDistance b e X' + εW) + δ) * ∑ x, ‖q x‖ ^ 2)
    (hmass : stdCauchy {t | ¬ matchedDistance b e (dilatedOld X t) ≤
      matchedDistance b e X + w8} ≤ ENNReal.ofReal m) :
    |∫ ω, regForm b e 0 X q ω ∂collarLaw W b - (boundaryZ b e).im * ∑ x, ‖q x‖ ^ 2| ≤
      (|CH| * (matchedDistance b e X + w8 + |εW|)) * ∑ x, ‖q x‖ ^ 2 +
        (collarRowConst b (Collar.Kernel.rowCoeff b e 0) * Real.sqrt W +
          (boundaryZ b e).im) * (∑ x, ‖q x‖ ^ 2) * m := by
  have hS : 0 ≤ ∑ x, ‖q x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hd0 : 0 ≤ matchedDistance b e X := (norm_nonneg _).trans (le_max_left _ _)
  have hA : 0 ≤ |CH| * (matchedDistance b e X + w8 + |εW|) * ∑ x, ‖q x‖ ^ 2 :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (by linarith [abs_nonneg εW])) hS
  refine abs_integral_regForm_sub_le hb0 hb hW e hY q hA hm0 hη ?_ hmass
  intro δ hδ
  obtain ⟨ν₀, hν₀, hν⟩ := hHS δ hδ
  refine ⟨ν₀, hν₀, fun ν hν' t ht => ?_⟩
  have hdt : matchedDistance b e (dilatedOld X t) ≤ dH := ht.trans hd
  have hdt0 : 0 ≤ matchedDistance b e (dilatedOld X t) := (norm_nonneg _).trans (le_max_left _ _)
  have h1 := hν ν hν' (dilatedOld X t) (Collar.Kernel.dilatedOld_isHermitian X t) hdt q
  refine h1.trans ?_
  have h2 : CH * (matchedDistance b e (dilatedOld X t) + εW) ≤
      |CH| * (matchedDistance b e X + w8 + |εW|) := by
    calc CH * (matchedDistance b e (dilatedOld X t) + εW)
        ≤ |CH| * |matchedDistance b e (dilatedOld X t) + εW| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ |CH| * (matchedDistance b e (dilatedOld X t) + |εW|) := by
          gcongr
          exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hdt0])
      _ ≤ |CH| * (matchedDistance b e X + w8 + |εW|) := by gcongr
  have := mul_le_mul_of_nonneg_right h2 hS
  nlinarith

/-- The final arithmetic of Step 6: `η⁻¹|x| ≤ η_min⁻¹ M (d + |ε| + W^{-1/8} + g W^{-1/4}) ‖q‖²`. -/
theorem final_arith {x η ηmin CH CU Cr CD d w8 w4 εW g S m sW : ℝ} (hηmin : 0 < ηmin)
    (hη : ηmin ≤ η) (hη1 : η ≤ 1) (hCr : Cr ≤ CU) (hg : 0 ≤ g)
    (hw4 : 0 ≤ w4) (hS : 0 ≤ S) (hm0 : 0 ≤ m) (hsW : 0 ≤ sW) (hd : 0 ≤ d) (hw8 : 0 ≤ w8)
    (hm : (CU * sW + 1) * m ≤ (CU + 1) * w4 * (CD * g))
    (hx : |x| ≤ (|CH| * (d + w8 + |εW|)) * S + (Cr * sW + η) * S * m) :
    η⁻¹ * |x| ≤ ηmin⁻¹ * max |CH| ((CU + 1) * CD) * (d + |εW| + w8 + g * w4) * S := by
  set M := max |CH| ((CU + 1) * CD)
  have hη0 : 0 < η := hηmin.trans_le hη
  have h1 : (Cr * sW + η) * m ≤ (CU * sW + 1) * m := by
    apply mul_le_mul_of_nonneg_right _ hm0
    nlinarith
  have hom : (Cr * sW + η) * S * m ≤ (CU + 1) * CD * g * w4 * S := by
    calc (Cr * sW + η) * S * m = (Cr * sW + η) * m * S := by ring
      _ ≤ (CU + 1) * w4 * (CD * g) * S := mul_le_mul_of_nonneg_right (h1.trans hm) hS
      _ = _ := by ring
  have hA : |CH| * (d + w8 + |εW|) ≤ M * (d + |εW| + w8) := by
    rw [show d + |εW| + w8 = d + w8 + |εW| by ring]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [abs_nonneg εW])
  have hB : (CU + 1) * CD * g * w4 ≤ M * (g * w4) := by
    rw [show (CU + 1) * CD * g * w4 = ((CU + 1) * CD) * (g * w4) by ring]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hg hw4)
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have hsum : |x| ≤ M * (d + |εW| + w8 + g * w4) * S := by
    have e1 := mul_le_mul_of_nonneg_right hA hS
    have e2 := mul_le_mul_of_nonneg_right hB hS
    nlinarith
  have hT : 0 ≤ M * (d + |εW| + w8 + g * w4) * S :=
    mul_nonneg (mul_nonneg hM (by linarith [abs_nonneg εW, mul_nonneg hg hw4])) hS
  calc η⁻¹ * |x| ≤ η⁻¹ * (M * (d + |εW| + w8 + g * w4) * S) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hη0.le)
    _ ≤ ηmin⁻¹ * (M * (d + |εW| + w8 + g * w4) * S) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hηmin hη) hT
    _ = _ := by ring

/-- **The strict clause from the Hermitian statement** (Step 6 of the paper's proof). -/
theorem strictClause_of_hermitian (hH : HermitianCollarMeanStatement) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (ε : ℕ → ℝ) (C d₂ : ℝ) (W₀ : ℕ), Tendsto ε atTop (𝓝 0) ∧ 0 < d₂ ∧ 0 ≤ C ∧
        (∀ W, 0 ≤ ε W) ∧ StrictBoundaryMeanClause b κ ε C d₂ W₀ := by
  intro b hb0 hb κ hκ
  by_cases h4 : 4 ≤ κ
  · refine ⟨fun _ => 0, 0, 1, 0, tendsto_const_nhds, one_pos, le_refl _, fun _ => le_refl _, ?_⟩
    intro W _ _ e he
    exfalso
    have := he.1.trans he.2
    linarith
  push Not at h4
  obtain ⟨εH, CH, dH, WH, hεH, hdH, hHS⟩ := hH b hb0 hb κ hκ
  set ηmin := (1 - b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hηmin_def
  have hηmin : 0 < ηmin := by
    have := Real.sqrt_pos.2 (BlockBand.Layers.four_sub_sq_pos hκ h4)
    have : 0 < 1 - b := by linarith
    positivity
  obtain ⟨CD, hCD, hexc⟩ := exceptional_phase_mass hηmin
  set CU := collarRowConst b (5 : ℂ)
  have hrp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 8)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := (1 : ℝ) / 8) (by norm_num)
    have h' := h.comp tendsto_natCast_atTop_atTop
    refine h'.congr fun n => ?_
    simp only [Function.comp_apply]
    congr 1
    ring
  obtain ⟨W₁, hW₁⟩ := eventually_atTop.1 ((tendsto_order.1 hrp).2 (dH / 2) (by positivity))
  obtain ⟨Cu, -, hu⟩ := Collar.Kernel.collarKernel_universal_all hb0 hb hκ 0 0
  have hM : 0 ≤ max |CH| ((CU + 1) * CD) := (abs_nonneg _).trans (le_max_left _ _)
  refine ⟨fun W => |εH W|, ηmin⁻¹ * max |CH| ((CU + 1) * CD), dH / 2, max (max WH W₁) 1, ?_,
    by positivity, mul_nonneg (inv_nonneg.2 hηmin.le) hM, fun W => abs_nonneg _, ?_⟩
  · simpa using hεH.abs
  intro W hW hW₀ e he X hY hd
  have hWH : WH ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW₀)
  have hW1 : W₁ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW₀)
  have hWone : (1 : ℝ) ≤ W := by
    have : 1 ≤ W := (le_max_right _ _).trans hW₀
    exact_mod_cast this
  have hWr : (0 : ℝ) < W := by linarith
  obtain ⟨-, hηe⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b)
    (by linarith) hκ he
  have hη : 0 < (boundaryZ b e).im := hηmin.trans_le hηe
  have hw8 : 0 < (W : ℝ) ^ (-(1 : ℝ) / 8) := Real.rpow_pos_of_pos hWr _
  have hw4 : 0 < (W : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos hWr _
  have hw8d : (W : ℝ) ^ (-(1 : ℝ) / 8) < dH / 2 := hW₁ W hW1
  have hg := Collar.Kernel.conductance_oldScattering_nonneg b e hη hY.posSemidef
  have hd0 : 0 ≤ matchedDistance b e X := (norm_nonneg _).trans (le_max_left _ _)
  obtain ⟨hint, -⟩ := (hu W hW e he 0 ⟨by norm_num, le_refl _⟩ 0 ⟨le_refl _, le_refl _⟩ X).1 hY
  refine ⟨hint, ?_⟩
  have hCr : collarRowConst b (Collar.Kernel.rowCoeff b e 0) ≤ CU :=
    Collar.Density.collarRowConst_mono b (norm_rowCoeff_le hb0.le (by linarith) hκ he)
  have hm0 : 0 ≤ CD * conductance (oldScattering b e X) /
      (W * ((W : ℝ) ^ (-(1 : ℝ) / 8)) ^ 2) := by positivity
  have hmass := hexc W hW b e hηe X hY.posSemidef _ hw8
  have hm : (CU * Real.sqrt W + 1) * (CD * conductance (oldScattering b e X) /
      (W * ((W : ℝ) ^ (-(1 : ℝ) / 8)) ^ 2)) ≤
      (CU + 1) * (W : ℝ) ^ (-(1 : ℝ) / 4) * (CD * conductance (oldScattering b e X)) := by
    rw [← mul_div_assoc, mul_comm _ (CD * _), mul_div_assoc]
    rw [mul_comm ((CU + 1) * _)]
    exact mul_le_mul_of_nonneg_left (omitted_rate_le hWone CU) (by positivity)
  have hHerm : (expectedCollarKernel b e 0 0 1 X - 1).IsHermitian :=
    (matrixExpect_isHermitian fun ω => poissonKernel_isHermitian _).sub isHermitian_one
  have hC0 : 0 ≤ meanError b e (fun W => |εH W|) (ηmin⁻¹ * max |CH| ((CU + 1) * CD)) X := by
    unfold meanError; positivity
  refine norm_le_of_abs_re_quad_le hHerm hC0 fun q => ?_
  have hS : 0 ≤ ∑ x, ‖q x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hre : (star q ⬝ᵥ ((expectedCollarKernel b e 0 0 1 X - 1) *ᵥ q)).re =
      (boundaryZ b e).im⁻¹ * (∫ ω, regForm b e 0 X q ω ∂collarLaw W b -
        (boundaryZ b e).im * ∑ x, ‖q x‖ ^ 2) := by
    rw [sub_mulVec, dotProduct_sub, one_mulVec, Complex.sub_re,
      dotProduct_expectedCollarKernel hb e hη hY hint q, Complex.ofReal_re,
      BlockBand.Wegner.re_star_dotProduct_self]
    field_simp
  rw [hre, abs_mul, abs_of_pos (inv_pos.2 hη)]
  have hq := dir_bound hb0 hb hW e hY q hw8.le (by linarith) hm0 hη.le (hHS W hW hWH e he) hmass
  have hfin := final_arith hηmin hηe (boundaryZ_im_le_one hb0.le hκ he) hCr hg hw4.le hS
    hm0 (Real.sqrt_nonneg _) hd0 hw8.le hm hq
  refine hfin.trans (le_of_eq ?_)
  unfold meanError
  ring

end BlockBand.Critical.BoundaryMean

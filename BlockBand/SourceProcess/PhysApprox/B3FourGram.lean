module

public import BlockBand.SourceProcess.PhysApprox.B3FourK

/-!
# The Gram half of the Lindeberg clause, reduced to the closed frame step

The centered increment of every fixed trace polynomial has conditional `L^p` size `C_K W^{-1/2}` and
its drift has `L^p` size `C_K/W`, so `E Σ_j |ΔZ_j|^p ≤ C_K W^{1-p/2}` away from births. This file
carries this out for the Gram coordinates of the closed path.

A Gram coordinate is an entry of `Fᴴ D F` (`D = 1` or `P`) of the closed frame `F_j`
(`b3ClosedFrameAt`). For an old coordinate (no newborn column) let `q = ‖ΔF_old‖²_F`, the old
columns of `F_{j+1} − F_j`, and `r = ‖F_j‖²_F = Re Tr M_j < R` on the alive set:
* `Four.norm_gramEntry_sub_le`: `|ΔG| ≤ 2√(qr) + q` (Cauchy–Schwarz), applied to the
  old columns (`Four.gramEntry_maskCols`);
* `enorm_gramStep_le`: on `A_j`, `|ΔG|⁴ ≤ 8(16R²q² + q⁴)`;
* **`ClosedFrameStepEight`**, stated as a hypothesis: `E[1_{A_j} q⁴] ≤ C/W⁴` at every step
  `n_s ≤ j < ⌊WT⌋` (the eighth moment of the old columns of one closed frame step, `L⁸` size
  `C W^{-1/2}`); under it, `lintegral_gramStep_at` gives `E[1_{A_j}|ΔG|⁴] ≤ C/W²`;
* **`gramStopStepFour_of_frame`**: `ClosedFrameStepEight ⇒ GramStopStepFour`
  (`q² ≤ W²q⁴ + W⁻²`), hence **`complexGramLindeberg_of_frame`** and, with the `𝒦` half,
  **`complexClosedLindeberg_of_frame`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal

namespace Four

/-- The squared Frobenius norm `Σ_{x,d}|V_{xd}|²`. -/
def frameSq {ι c : Type*} [Fintype ι] [Fintype c] (V : Matrix ι c ℂ) : ℝ :=
  ∑ x, ∑ d, ‖V x d‖ ^ 2

theorem frameSq_nonneg {ι c : Type*} [Fintype ι] [Fintype c] (V : Matrix ι c ℂ) :
    0 ≤ frameSq V :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem reTrace_conjTranspose_mul {ι c : Type*} [Fintype ι] [Fintype c] (V : Matrix ι c ℂ) :
    ((Vᴴ * V).trace).re = frameSq V := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum, frameSq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- **Cauchy–Schwarz for one entry**: `|(Yᴴ diag(D) Z)_{ab}| ≤ ‖Y‖_F‖Z‖_F` when `|D| ≤ 1`. -/
theorem norm_entry_le {ι c : Type*} [Fintype ι] [Fintype c] [DecidableEq ι] (Y Z : Matrix ι c ℂ)
    (D : ι → ℂ) (hD : ∀ x, ‖D x‖ ≤ 1) (a b : c) :
    ‖(Yᴴ * diagonal D * Z) a b‖ ≤ Real.sqrt (frameSq Y) * Real.sqrt (frameSq Z) := by
  have hcol : ∀ (V : Matrix ι c ℂ) (a : c), ∑ x, ‖V x a‖ ^ 2 ≤ frameSq V := fun V a =>
    Finset.sum_le_sum fun x _ => Finset.single_le_sum (f := fun d => ‖V x d‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  rw [mul_apply]
  simp only [mul_diagonal, conjTranspose_apply]
  calc ‖∑ x, star (Y x a) * D x * Z x b‖ ≤ ∑ x, ‖Y x a‖ * ‖Z x b‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        rw [norm_mul, norm_mul, norm_star]
        calc ‖Y x a‖ * ‖D x‖ * ‖Z x b‖ ≤ ‖Y x a‖ * 1 * ‖Z x b‖ := by gcongr; exact hD x
          _ = _ := by ring
    _ ≤ Real.sqrt (∑ x, ‖Y x a‖ ^ 2) * Real.sqrt (∑ x, ‖Z x b‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ _ := by gcongr <;> exact hcol _ _

theorem gramEntry_eq {ι c : Type*} [Fintype ι] [DecidableEq ι] (Pd : ι → ℂ) (V : Matrix ι c ℂ)
    (e : Fin 2 × c × c) :
    gramEntry e (gramPair (diagonal Pd) V) =
      (Vᴴ * diagonal (if e.1 = 0 then fun _ => (1 : ℂ) else Pd) * V) e.2.1 e.2.2 := by
  unfold gramEntry gramPair BlockBand.SourceProcess.sourceGram BlockBand.SourceProcess.nearGram
  split_ifs <;> simp [diagonal_one]

/-- **The Gram step**: `|ΔG_e| ≤ 2√(q r) + q`, `q = ‖V' − V‖²_F`, `r = ‖V‖²_F`. -/
theorem norm_gramEntry_sub_le {ι c : Type*} [Fintype ι] [Fintype c] [DecidableEq ι]
    (Pd : ι → ℂ) (hP : ∀ x, ‖Pd x‖ ≤ 1) (V V' : Matrix ι c ℂ) (e : Fin 2 × c × c) :
    ‖gramEntry e (gramPair (diagonal Pd) V') - gramEntry e (gramPair (diagonal Pd) V)‖ ≤
      2 * (Real.sqrt (frameSq (V' - V)) * Real.sqrt (frameSq V)) + frameSq (V' - V) := by
  set D : ι → ℂ := if e.1 = 0 then fun _ => (1 : ℂ) else Pd
  have hD : ∀ x, ‖D x‖ ≤ 1 := fun x => by
    simp only [D]; split_ifs
    · simp
    · exact hP x
  set X := V' - V
  have hV' : V' = V + X := by simp only [X]; abel
  rw [gramEntry_eq, gramEntry_eq, hV']
  have e1 : (V + X)ᴴ * diagonal D * (V + X) - Vᴴ * diagonal D * V =
      Xᴴ * diagonal D * V + Vᴴ * diagonal D * X + Xᴴ * diagonal D * X := by
    simp only [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
  have e2 := congrFun (congrFun e1 e.2.1) e.2.2
  simp only [Matrix.sub_apply, Matrix.add_apply] at e2
  rw [show (D = if e.1 = 0 then fun _ => (1 : ℂ) else Pd) from rfl] at e2
  rw [e2]
  have h1 := norm_entry_le X V D hD e.2.1 e.2.2
  have h2 := norm_entry_le V X D hD e.2.1 e.2.2
  have h3 := norm_entry_le X X D hD e.2.1 e.2.2
  rw [Real.mul_self_sqrt (frameSq_nonneg X)] at h3
  calc _ ≤ ‖(Xᴴ * diagonal D * V) e.2.1 e.2.2‖ + ‖(Vᴴ * diagonal D * X) e.2.1 e.2.2‖ +
        ‖(Xᴴ * diagonal D * X) e.2.1 e.2.2‖ := norm_add₃_le
    _ ≤ _ := by linarith

theorem add_pow_four_le_real (x y : ℝ) :
    (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h2 : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h4 : (x ^ 2 + y ^ 2) ^ 2 ≤ 2 * (x ^ 4 + y ^ 4) := by nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  calc (x + y) ^ 4 = ((x + y) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (x ^ 2 + y ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
    _ = 4 * (x ^ 2 + y ^ 2) ^ 2 := by ring
    _ ≤ 4 * (2 * (x ^ 4 + y ^ 4)) := by gcongr
    _ = _ := by ring

/-- **The fourth power of the Gram step**: if `r ≤ R`, `|ΔG|⁴ ≤ 8(16R²q² + q⁴)`. -/
theorem norm_gramEntry_sub_pow_le {ι c : Type*} [Fintype ι] [Fintype c] [DecidableEq ι]
    (Pd : ι → ℂ) (hP : ∀ x, ‖Pd x‖ ≤ 1) (V V' : Matrix ι c ℂ) (e : Fin 2 × c × c) {R : ℝ}
    (hR : frameSq V ≤ R) :
    ‖gramEntry e (gramPair (diagonal Pd) V') - gramEntry e (gramPair (diagonal Pd) V)‖ ^ 4 ≤
      8 * (16 * R ^ 2 * frameSq (V' - V) ^ 2 + frameSq (V' - V) ^ 4) := by
  set q := frameSq (V' - V)
  set r := frameSq V
  have hq := frameSq_nonneg (V' - V)
  have hr := frameSq_nonneg V
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr
  have hstep := norm_gramEntry_sub_le Pd hP V V' e
  calc _ ≤ (2 * (Real.sqrt q * Real.sqrt r) + q) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) hstep 4
    _ ≤ 8 * ((2 * (Real.sqrt q * Real.sqrt r)) ^ 4 + q ^ 4) :=
        add_pow_four_le_real _ _
    _ = 8 * (16 * q ^ 2 * r ^ 2 + q ^ 4) := by
        rw [show (2 * (Real.sqrt q * Real.sqrt r)) ^ 4 =
          16 * (Real.sqrt q ^ 2) ^ 2 * (Real.sqrt r ^ 2) ^ 2 by ring, hsq, hsr]
    _ ≤ 8 * (16 * R ^ 2 * q ^ 2 + q ^ 4) := by
        have : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr hR 2
        nlinarith [sq_nonneg q]

/-- The columns of `V` in `p`, the others set to `0`. -/
def maskCols {ι c : Type*} (p : c → Prop) (V : Matrix ι c ℂ) : Matrix ι c ℂ :=
  open scoped Classical in Matrix.of fun x d => if p d then V x d else 0

theorem maskCols_sub {ι c : Type*} (p : c → Prop) (V V' : Matrix ι c ℂ) :
    maskCols p V' - maskCols p V = maskCols p (V' - V) := by
  ext x d
  simp only [maskCols, Matrix.sub_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem frameSq_maskCols_le {ι c : Type*} [Fintype ι] [Fintype c] (p : c → Prop)
    (V : Matrix ι c ℂ) : frameSq (maskCols p V) ≤ frameSq V := by
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun d _ => ?_
  simp only [maskCols, Matrix.of_apply]
  split_ifs <;> simp

/-- A Gram entry of two columns in `p` only sees the columns in `p`. -/
theorem gramEntry_maskCols {ι c : Type*} [Fintype ι] [DecidableEq ι] (Pd : ι → ℂ)
    (p : c → Prop) (V : Matrix ι c ℂ) (e : Fin 2 × c × c) (h1 : p e.2.1) (h2 : p e.2.2) :
    gramEntry e (gramPair (diagonal Pd) (maskCols p V)) =
      gramEntry e (gramPair (diagonal Pd) V) := by
  rw [gramEntry_eq, gramEntry_eq, mul_apply, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, maskCols, Matrix.of_apply, h1, h2, ↓reduceIte]

end Four

open Four

variable {W np K : ℕ}

/-- One step `F_{j+1} − F_j` of the closed frame. -/
def b3FrameStep (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ) :
    Matrix (Fin 2 × Fin W) (SrcCol K (Fin np)) ℂ :=
  b3ClosedFrameAt b E s h τ m W (j + 1) Vs y - b3ClosedFrameAt b E s h τ m W j Vs y

/-- **The per-step frame hypothesis `ClosedFrameStepEight`** (the closed frame step has
conditional `L^p` size `C_KW^{-1/2}` on the trace stop; at a birth step the old columns move as at
a regular step): at every step `n_s ≤ j < ⌊WT⌋`, the old
columns (no tag born at `j`; all columns at a step without a birth) of one closed frame step have
`E[1_{A_j}‖ΔF_old‖_F⁸] ≤ C/W⁴`, uniformly in the step. -/
def ClosedFrameStepEight : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            ENNReal.ofReal (frameSq (maskCols (fun d => ¬ IsNewCol τ W j d)
              (b3FrameStep b E s h τ m W j (Vs W) y)) ^ 4)) y
          ∂closedLaw b W np ≤ ENNReal.ofReal (C / (W : ℝ) ^ 4)

/-- On the alive set at `j ≥ n_s`, the step of an old Gram coordinate is controlled by the old
columns of the frame step. -/
theorem enorm_gramStep_le (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) {W j : ℕ}
    (hj : closeLen s W ≤ j) (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np))
    (he : ¬ IsNewCoord τ W j (Sum.inl e : CIdx K np)) (hW : 1 ≤ W)
    (y : ProbedPath W np × ℝ) :
    ‖(b3Alive b E s h τ m R W j Vs).indicator
        (b3dX b E s h τ m W j Vs (Sum.inl e : CIdx K np)) y‖ₑ ^ 4 ≤
      ENNReal.ofReal (128 * R ^ 2 * (W : ℝ) ^ 2 + 8) *
          (b3Alive b E s h τ m R W j Vs).indicator (fun y =>
            ENNReal.ofReal (frameSq (maskCols (fun d => ¬ IsNewCol τ W j d)
              (b3FrameStep b E s h τ m W j Vs y)) ^ 4)) y +
        ENNReal.ofReal (128 * R ^ 2 / (W : ℝ) ^ 2) := by
  by_cases hy : y ∈ b3Alive b E s h τ m R W j Vs
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    set p : SrcCol K (Fin np) → Prop := fun d => ¬ IsNewCol τ W j d
    have he' : p e.2.1 ∧ p e.2.2 := by
      have : ¬ (IsNewCol τ W j e.2.1 ∨ IsNewCol τ W j e.2.2) := he
      exact not_or.1 this
    set F := b3ClosedFrameAt b E s h τ m W j Vs y
    set F' := b3ClosedFrameAt b E s h τ m W (j + 1) Vs y
    have hr : frameSq (maskCols p F) ≤ R := by
      have := hy.2 j hj le_rfl
      simp only [b3ClosedGramAt, gramPair, BlockBand.SourceProcess.sourceGram,
        reTrace_conjTranspose_mul] at this
      exact (frameSq_maskCols_le p F).trans this.le
    set Pd : Fin 2 × Fin W → ℂ := fun z => if z.1 = 0 then (1 : ℂ) else 0
    have hPd : ∀ x, ‖Pd x‖ ≤ 1 := fun x => by simp only [Pd]; split_ifs <;> simp
    have hpow := norm_gramEntry_sub_pow_le Pd hPd (maskCols p F) (maskCols p F') e hr
    rw [gramEntry_maskCols Pd p F' e he'.1 he'.2, gramEntry_maskCols Pd p F e he'.1 he'.2,
      maskCols_sub] at hpow
    set q := frameSq (maskCols p (b3FrameStep b E s h τ m W j Vs y))
    have hq : 0 ≤ q := frameSq_nonneg _
    have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
    have hamgm : q ^ 2 ≤ (W : ℝ) ^ 2 * q ^ 4 + 1 / (W : ℝ) ^ 2 := by
      have h0 : 0 ≤ ((W : ℝ) * q ^ 2 - 1 / W) ^ 2 := sq_nonneg _
      have e0 : ((W : ℝ) * q ^ 2 - 1 / W) ^ 2 = (W : ℝ) ^ 2 * q ^ 4 - 2 * q ^ 2 +
          1 / (W : ℝ) ^ 2 := by field_simp; ring
      nlinarith [sq_nonneg q]
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hstep : b3dX b E s h τ m W j Vs (Sum.inl e : CIdx K np) y =
        gramEntry e (gramPair (diagonal Pd) F') - gramEntry e (gramPair (diagonal Pd) F) := rfl
    rw [hstep]
    refine hpow.trans ?_
    have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
    have : 8 * (16 * R ^ 2 * q ^ 2) ≤ 128 * R ^ 2 * ((W : ℝ) ^ 2 * q ^ 4 + 1 / (W : ℝ) ^ 2) := by
      nlinarith
    calc 8 * (16 * R ^ 2 * q ^ 2 + q ^ 4) ≤
          128 * R ^ 2 * ((W : ℝ) ^ 2 * q ^ 4 + 1 / (W : ℝ) ^ 2) + 8 * q ^ 4 := by linarith
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hy, enorm_zero]
    norm_num

/-- **The per-step fourth moment of an old Gram coordinate** at every step `n_s ≤ j < ⌊WT⌋`:
`E[1_{A_j}|dX_e|⁴] ≤ C/W²`, from `ClosedFrameStepEight`. -/
theorem lintegral_gramStep_at (hF : ClosedFrameStepEight) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
            ¬ IsNewCoord τ W j (Sum.inl e : CIdx K np) →
            ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
                (b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np)) y‖ₑ ^ 4
              ∂closedLaw b W np ≤ ENNReal.ofReal (C / (W : ℝ) ^ 2) := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, hC⟩ := hF b E np τ m T s h K Vs hD R
  set C' := (128 * R ^ 2 + 8) * max C 0 + 128 * R ^ 2
  refine ⟨C', by positivity, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with W hW hW1 j hj e he
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hjs := (Finset.mem_Ico.1 hj).1
  refine (lintegral_mono fun y => enorm_gramStep_le b E s h τ m R hjs (Vs W) e he hW1 y).trans ?_
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const, measure_univ, mul_one]
  calc ENNReal.ofReal (128 * R ^ 2 * (W : ℝ) ^ 2 + 8) *
        ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
          ENNReal.ofReal (frameSq (maskCols (fun d => ¬ IsNewCol τ W j d)
            (b3FrameStep b E s h τ m W j (Vs W) y)) ^ 4)) y
          ∂closedLaw b W np + ENNReal.ofReal (128 * R ^ 2 / (W : ℝ) ^ 2)
      ≤ ENNReal.ofReal (128 * R ^ 2 * (W : ℝ) ^ 2 + 8) * ENNReal.ofReal (max C 0 / (W : ℝ) ^ 4) +
          ENNReal.ofReal (128 * R ^ 2 / (W : ℝ) ^ 2) := by
        gcongr
        exact (hW j hj).trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
    _ = ENNReal.ofReal ((128 * R ^ 2 * (W : ℝ) ^ 2 + 8) * (max C 0 / (W : ℝ) ^ 4) +
          128 * R ^ 2 / (W : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal (C' / (W : ℝ) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hC0 : 0 ≤ max C 0 := le_max_right _ _
        have hW2 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ hW1r
        have e1 : (128 * R ^ 2 * (W : ℝ) ^ 2 + 8) * (max C 0 / (W : ℝ) ^ 4) +
            128 * R ^ 2 / (W : ℝ) ^ 2 =
            (128 * R ^ 2 * max C 0 + 8 * max C 0 / (W : ℝ) ^ 2 + 128 * R ^ 2) / (W : ℝ) ^ 2 := by
          field_simp
        rw [e1]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have : 8 * max C 0 / (W : ℝ) ^ 2 ≤ 8 * max C 0 := div_le_self (by positivity) hW2
        simp only [C']
        nlinarith

/-- **`GramStopStepFour` from `ClosedFrameStepEight`.** -/
theorem gramStopStepFour_of_frame (hF : ClosedFrameStepEight) : GramStopStepFour := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, hC0, hC⟩ := lintegral_gramStep_at hF b E np τ m T s h K Vs hD R
  refine ⟨8 * (C * max T 0 + max 0 0), ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with W hW hW1 e
  refine rate_sum_le hC0 hW1 (card_filter_Ico_le s T τ W)
    (fun j => ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
      (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np) y‖ₑ ^ 4) y
        ∂closedLaw b W np) (fun _ => 0) (fun j hj => ?_) (by simp)
  obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
  rw [add_zero]
  simp_rw [indicator_enorm_pow_four]
  exact (hW j hj1 e (not_isNewCoord_of_not_birth hj2 _)).trans
    (le_mul_of_one_le_left' (by norm_num))

/-- **`ComplexGramLindeberg` from `ClosedFrameStepEight`.** -/
theorem complexGramLindeberg_of_frame (hF : ClosedFrameStepEight) : ComplexGramLindeberg :=
  complexGramLindeberg_of_stepFour (gramStopStepFour_of_frame hF)

/-- **`ComplexClosedLindeberg` from the two per-step hypotheses `KCorrStepFourAt` and
`ClosedFrameStepEight` and the contract hypotheses.** -/
theorem complexClosedLindeberg_of_frame (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract)
    (hC : KCorrStepFourAt) (hF : ClosedFrameStepEight) : ComplexClosedLindeberg :=
  complexClosedLindeberg_of_pins hGA hLp hSR hMT (kCorrStepFour_of_at hC)
    (gramStopStepFour_of_frame hF)

end BlockBand.SourceProcess.PhysApprox.B3

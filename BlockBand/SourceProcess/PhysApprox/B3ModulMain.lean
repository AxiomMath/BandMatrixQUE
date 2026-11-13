module

public import BlockBand.SourceProcess.PhysApprox.B3ModulAdapt
public import BlockBand.SourceProcess.PhysApprox.B3ModulWin
public import BlockBand.SourceProcess.PhysApprox.B3GenSplit
public import BlockBand.SourceProcess.PhysApprox.B3Pins2
public import BlockBand.SourceProcess.ClosedSumProof.TightMain

/-!
# `TargetModulus` and `ComplexClosedFourth ↔ ComplexClosedLindeberg`

**`targetModulus_holds : TargetModulus`**, i.e. `ComplexClosedSummed → ComplexClosedFourth →
ComplexClosedStopTail → ComplexClosedModulus`: the complex copy of `closedTight_of`
(modulus half). For a coordinate `c : CIdx` (Gram or `𝒦`):
* the stop (`ComplexClosedStopTail`, `θ/4`);
* the real and imaginary parts `Re(u(X_c - J_c))`, `u ∈ {1, -i}`, of the births-removed coordinate
  on the window `[⌊Wt₁⌋, ⌊WT⌋]` (`window_of_close`), each bounded by `window_modulus`
  (`3θ/8`) with filtration `b3Sigma` (adaptedness: `measurable_b3X_past`),
  events `b3AliveM`, variance constant `W⁻¹C_c(R)`, drift constant `W⁻¹C_b(R)`;
* the inputs of `window_modulus` from the estimates: drift and birth errors from `b3SummedErr c c`;
  the bracket against the conjugate `Δ̄` from `b3SummedErr (σ,k,l) (σ,l,k)` for a Gram coordinate
  (`Δ̄G_{σkl} = ΔG_{σlk}`) and from `b3ConjErr ij ij` for a `𝒦` coordinate; the fourth moments
  from `ComplexClosedFourth`. The predictions are bounded on the alive set by the trace level
  (`norm_cDrift_le`, `norm_partnerP_le`).
Constants as in the real case: `λ = κ = κ' = η/16`,
`δ = min(1/2, η/(16(C_b+1)), θλ⁴/(1024(C_c²+1)(T+1)))`.

Also **`complexClosedFourth_iff_lindeberg`** (`Iff.rfl`): the two estimates have the same summed
error (the complex analogue of `closedFourth_iff_lindeberg`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Modul

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ClosingAux
open ClosedSumProof (l1 swapE reMul)
open scoped ENNReal ComplexConjugate

variable {W np K : ℕ}

/-!
## The constants
-/

/-- The level `ρ = |cols|² max(R, 0)` bounding `l1 M, l1 B` on the alive set. -/
def rhoC (K np : ℕ) (R : ℝ) : ℝ := (Fintype.card (SrcCol K (Fin np)) : ℝ) ^ 2 * max R 0

/-- The drift constant `C_b(R)`. -/
def driftCC (b E : ℝ) (K np : ℕ) (R : ℝ) : ℝ :=
  |transportD0 b E| * (l1 (srcSignature K (Fin np)) * rhoC K np R) ^ 2 * rhoC K np R

/-- The conjugate-bracket constant `C_c(R)` (Gram and `𝒦` coordinates). -/
def covCC (b E : ℝ) (K np : ℕ) (R : ℝ) : ℝ :=
  (|transportD0 b E| + |2 * etaZ b E ^ 2 * transportD0 b E|) * rhoC K np R *
    (rhoC K np R + rhoC K np R * l1 (srcSignature K (Fin np)) * rhoC K np R)

theorem rhoC_nonneg (K np : ℕ) (R : ℝ) : 0 ≤ rhoC K np R := by unfold rhoC; positivity

theorem driftCC_nonneg (b E : ℝ) (K np : ℕ) (R : ℝ) : 0 ≤ driftCC b E K np R := by
  have := rhoC_nonneg K np R; have := ClosedSumProof.l1_nonneg (srcSignature K (Fin np))
  unfold driftCC; positivity

theorem covCC_nonneg (b E : ℝ) (K np : ℕ) (R : ℝ) : 0 ≤ covCC b E K np R := by
  have := rhoC_nonneg K np R; have := ClosedSumProof.l1_nonneg (srcSignature K (Fin np))
  unfold covCC; positivity

/-!
## The conjugate partner and the predictions
-/

/-- The conjugate partner of the increment: `ΔG_{σlk}` for `G_{σkl}`, `Δ𝒦̄_ij` for `𝒦_ij`. -/
def partnerD (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np)
    (y : ProbedPath W np × ℝ) : ℂ :=
  match c with
  | Sum.inl e => b3dX b E s h τ m W j Vs (Sum.inl (swapE e)) y
  | Sum.inr ij => conj (b3dX b E s h τ m W j Vs (Sum.inr ij) y)

/-- The prediction of `ΔX_c · partner`: `cCov (σ,k,l) (σ,l,k)` and `kConjCov ij ij`. -/
def partnerP (b E : ℝ) (c : CIdx K np) (G : GramState (SrcCol K (Fin np))) : ℂ :=
  match c with
  | Sum.inl e => cCov b E (Sum.inl e) (Sum.inl (swapE e)) G
  | Sum.inr ij => kConjCov b E ij ij G

theorem partnerD_eq_star (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np)
    (y : ProbedPath W np × ℝ) :
    partnerD b E s h τ m W j Vs c y = star (b3dX b E s h τ m W j Vs c y) := by
  cases c with
  | inl e =>
      simp only [partnerD, b3dX, b3X, cEntry, b3ClosedGramAt, star_sub,
        ClosedSumProof.star_gramEntry _ (nearPortProj_conjTranspose (W := W))]
  | inr ij => rfl

theorem l1_b3Gram_le {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {j : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hj : closeLen s W ≤ j)
    {y : ProbedPath W np × ℝ} (hy : y ∈ b3AliveM b E s h τ m R W j Vs) :
    l1 (b3ClosedGramAt b E s h τ m W j Vs y).1 ≤ rhoC K np R ∧
      l1 (b3ClosedGramAt b E s h τ m W j Vs y).2 ≤ rhoC K np R := by
  have htr := hy.2 j hj le_rfl
  have hent : ∀ e', ‖gramEntry e' (b3ClosedGramAt b E s h τ m W j Vs y)‖ ≤ max R 0 := fun e' =>
    (norm_gramEntry_b3ClosedGramAt_le b E s h τ m W j Vs y e').trans
      (htr.le.trans (le_max_left _ _))
  exact ⟨ClosedSumProof.l1_le_of_entry fun a c => by simpa [gramEntry] using hent (0, a, c),
    ClosedSumProof.l1_le_of_entry fun a c => by simpa [gramEntry] using hent (1, a, c)⟩

theorem norm_cDrift_le (b E : ℝ) (R : ℝ) (c : CIdx K np) (G : GramState (SrcCol K (Fin np)))
    (hM : l1 G.1 ≤ rhoC K np R) (hB : l1 G.2 ≤ rhoC K np R) :
    ‖cDrift b E c G‖ ≤ driftCC b E K np R := by
  cases c with
  | inl e => exact ClosedSumProof.norm_gramDriftEntry_le_rho _ _ e G hM hB
  | inr ij => simp only [cDrift, norm_zero]; exact driftCC_nonneg b E K np R

theorem l1_gramC0_le_rho {ρ : ℝ} (G : GramState (SrcCol K (Fin np))) (hM : l1 G.1 ≤ ρ)
    (hB : l1 G.2 ≤ ρ) :
    l1 (BlockBand.SourceProcess.gramC0 G.1 G.2 (srcSignature K (Fin np))) ≤
      ρ + ρ * l1 (srcSignature K (Fin np)) * ρ := by
  have hρ : 0 ≤ ρ := (ClosedSumProof.l1_nonneg _).trans hM
  have hD := ClosedSumProof.l1_nonneg (srcSignature K (Fin np))
  unfold BlockBand.SourceProcess.gramC0
  refine (ClosedSumProof.l1_add_le _ _).trans (add_le_add hB
    ((ClosedSumProof.l1_mul_le _ _).trans ?_))
  have h1 := (ClosedSumProof.l1_mul_le G.1 (srcSignature K (Fin np))).trans
    (mul_le_mul_of_nonneg_right hM hD)
  exact mul_le_mul h1 hM (ClosedSumProof.l1_nonneg _) (mul_nonneg hρ hD)

theorem norm_partnerP_le (b E : ℝ) (R : ℝ) (c : CIdx K np) (G : GramState (SrcCol K (Fin np)))
    (hM : l1 G.1 ≤ rhoC K np R) (hB : l1 G.2 ≤ rhoC K np R) :
    ‖partnerP b E c G‖ ≤ covCC b E K np R := by
  have hρ := rhoC_nonneg K np R
  have hD := ClosedSumProof.l1_nonneg (srcSignature K (Fin np))
  have hQ : 0 ≤ rhoC K np R * (rhoC K np R + rhoC K np R * l1 (srcSignature K (Fin np)) *
      rhoC K np R) := by positivity
  cases c with
  | inl e =>
      refine (ClosedSumProof.norm_gramCovEntry_le_rho _ _ e (swapE e) G hM hB).trans ?_
      unfold covCC
      rw [mul_assoc, mul_assoc (_ + _)]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) hQ
  | inr ij =>
      have h2 : ‖G.2 (Sum.inr ij.1) (Sum.inr ij.1)‖ ≤ rhoC K np R :=
        (ClosedSumProof.norm_entry_le_l1 _ _ _).trans hB
      have h0 : ‖BlockBand.SourceProcess.gramC0 G.1 G.2 (srcSignature K (Fin np))
          (Sum.inr ij.2) (Sum.inr ij.2)‖ ≤
            rhoC K np R + rhoC K np R * l1 (srcSignature K (Fin np)) * rhoC K np R :=
        (ClosedSumProof.norm_entry_le_l1 _ _ _).trans (l1_gramC0_le_rho G hM hB)
      have e1 : ‖partnerP b E (Sum.inr ij : CIdx K np) G‖ =
          |2 * etaZ b E ^ 2 * transportD0 b E| * ‖G.2 (Sum.inr ij.1) (Sum.inr ij.1)‖ *
            ‖BlockBand.SourceProcess.gramC0 G.1 G.2 (srcSignature K (Fin np))
              (Sum.inr ij.2) (Sum.inr ij.2)‖ := by
        simp only [partnerP, kConjCov, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      rw [e1]
      unfold covCC
      calc |2 * etaZ b E ^ 2 * transportD0 b E| * ‖G.2 (Sum.inr ij.1) (Sum.inr ij.1)‖ *
            ‖BlockBand.SourceProcess.gramC0 G.1 G.2 (srcSignature K (Fin np))
              (Sum.inr ij.2) (Sum.inr ij.2)‖
          ≤ |2 * etaZ b E ^ 2 * transportD0 b E| * rhoC K np R *
              (rhoC K np R + rhoC K np R * l1 (srcSignature K (Fin np)) * rhoC K np R) := by
            gcongr
        _ ≤ _ := by
            rw [mul_assoc, mul_assoc (_ + _)]
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg _)) hQ

theorem measurable_cDrift_comp {α : Type*} [MeasurableSpace α] (b E : ℝ) (c : CIdx K np)
    {G : α → GramState (SrcCol K (Fin np))} (hG : Measurable G) :
    Measurable fun a => cDrift b E c (G a) := by
  cases c with
  | inl e => exact ClosedSumProof.measurable_drift_comp _ _ e hG
  | inr ij => exact measurable_const

theorem measurable_partnerP_comp {α : Type*} [MeasurableSpace α] (b E : ℝ) (c : CIdx K np)
    {G : α → GramState (SrcCol K (Fin np))} (hG : Measurable G) :
    Measurable fun a => partnerP b E c (G a) := by
  cases c with
  | inl e => exact ClosedSumProof.measurable_cov_comp _ _ e (swapE e) hG
  | inr ij =>
      have hM : Measurable fun a => (G a).1 := measurable_fst.comp hG
      have hB : Measurable fun a => (G a).2 := measurable_snd.comp hG
      have hC : Measurable fun a => BlockBand.SourceProcess.gramC0 (G a).1 (G a).2
          (srcSignature K (Fin np)) :=
        measurable_matrix_add hB (measurable_matrix_mul' (measurable_matrix_mul' hM
          measurable_const) hM)
      simp only [partnerP, kConjCov]
      exact (measurable_const.mul hB.eval_matrix).mul hC.eval_matrix

/-!
## Births
-/

theorem cEntry_add (c : CIdx K np) (G G' : GramState (SrcCol K (Fin np)))
    (Kc Kc' : Matrix (Fin np) (Fin np) ℂ) :
    cEntry c (G + G') (Kc + Kc') = cEntry c G Kc + cEntry c G' Kc' := by
  cases c with
  | inl e => exact ClosedSumProof.gramEntry_add e G G'
  | inr ij => rfl

theorem cEntry_zero (c : CIdx K np) :
    cEntry c (0 : GramState (SrcCol K (Fin np))) (0 : Matrix (Fin np) (Fin np) ℂ) = 0 := by
  cases c with
  | inl e => show gramEntry e 0 = 0; unfold gramEntry; split_ifs <;> rfl
  | inr ij => rfl

theorem birth_eq_zero (b E : ℝ) (τ m : Fin np → ℝ) {W j : ℕ} (hj : ¬ IsBirthStep τ W j)
    (c : CIdx K np) : cEntry c (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j) = 0 := by
  have h1 : b3BirthAt (K := K) b τ m W j = 0 :=
    Finset.sum_eq_zero fun i _ => ite_eq_right fun h => hj ⟨i, h⟩
  have h2 : b3KBirthAt E τ m W j = 0 :=
    Finset.sum_eq_zero fun i _ => ite_eq_right fun h => hj ⟨i, h⟩
  rw [h1, h2, cEntry_zero]

/-- The births-removed coordinate `X_c - J_c`. -/
def zB (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) (j : ℕ)
    (y : ProbedPath W np × ℝ) : ℂ :=
  b3X b E s h τ m W j Vs c y - cEntry c (b3JumpAt b s τ m W j) (b3KJumpAt E s τ m W j)

theorem zB_step (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) {j : ℕ}
    (hj : closeLen s W ≤ j) (y : ProbedPath W np × ℝ) :
    zB b E s h τ m W Vs c (j + 1) y - zB b E s h τ m W Vs c j y =
      b3dX b E s h τ m W j Vs c y - cEntry c (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j) := by
  have h1 : b3JumpAt (K := K) b s τ m W (j + 1) = b3JumpAt b s τ m W j + b3BirthAt b τ m W j := by
    unfold b3JumpAt; rw [Finset.sum_Ico_succ_top hj]
  have h2 : b3KJumpAt E s τ m W (j + 1) = b3KJumpAt E s τ m W j + b3KBirthAt E τ m W j := by
    unfold b3KJumpAt; rw [Finset.sum_Ico_succ_top hj]
  simp only [zB, b3dX, h1, h2, cEntry_add]
  ring

/-!
## The window inclusion (deterministic)
-/

/-- **A large move of `Z` on `[t₁, T]` at time resolution `δ` is a large window move of
`Re Z` or of `Im Z = Re(-iZ)`** (the deterministic part of `modulus_incl`). -/
theorem window_of_close {Ω : Type*} (Z : ℕ → Ω → ℂ) (y : Ω) {W N : ℕ} {t₁ T δ η thr t t' : ℝ}
    (ht₁ : 0 ≤ t₁) (hδ : 0 ≤ δ) (hj : ⌊(W : ℝ) * t₁⌋₊ ≤ ⌊(W : ℝ) * T⌋₊)
    (hNL : ⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * t₁⌋₊ ≤ N * (⌊(W : ℝ) * δ⌋₊ + 1)) (hthr : thr ≤ η / 2)
    (ht : t ∈ Set.Icc t₁ T) (ht' : t' ∈ Set.Icc t₁ T) (htt : |t - t'| ≤ δ)
    (hη : η < ‖Z ⌊(W : ℝ) * t⌋₊ y - Z ⌊(W : ℝ) * t'⌋₊ y‖) :
    (∃ x y', x ≤ y' ∧ y' ≤ N * (⌊(W : ℝ) * δ⌋₊ + 1) ∧ y' ≤ x + (⌊(W : ℝ) * δ⌋₊ + 1) ∧
      thr < |wX Z 1 ⌊(W : ℝ) * t₁⌋₊ (⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * t₁⌋₊) y' y -
        wX Z 1 ⌊(W : ℝ) * t₁⌋₊ (⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * t₁⌋₊) x y|) ∨
    (∃ x y', x ≤ y' ∧ y' ≤ N * (⌊(W : ℝ) * δ⌋₊ + 1) ∧ y' ≤ x + (⌊(W : ℝ) * δ⌋₊ + 1) ∧
      thr < |wX Z (-Complex.I) ⌊(W : ℝ) * t₁⌋₊ (⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * t₁⌋₊) y' y -
        wX Z (-Complex.I) ⌊(W : ℝ) * t₁⌋₊ (⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * t₁⌋₊) x y|) := by
  set j₁ := ⌊(W : ℝ) * t₁⌋₊
  set L := ⌊(W : ℝ) * T⌋₊ - j₁
  have hW := Nat.cast_nonneg (α := ℝ) W
  have hrange : ∀ τ ∈ Set.Icc t₁ T, j₁ ≤ ⌊(W : ℝ) * τ⌋₊ ∧ ⌊(W : ℝ) * τ⌋₊ ≤ j₁ + L :=
    fun τ hτ => ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left hτ.1 hW), by
      have := Nat.floor_mono (mul_le_mul_of_nonneg_left hτ.2 hW); omega⟩
  have h1 := ClosedSumProof.floor_close (W := W) (t := t) (t' := t') (ht₁.trans ht'.1) hδ
    (by linarith [le_abs_self (t - t')])
  have h2 := ClosedSumProof.floor_close (W := W) (t := t') (t' := t) (ht₁.trans ht.1) hδ
    (by linarith [neg_abs_le (t - t')])
  have hat : ∀ (u : ℂ) (a : ℕ), j₁ ≤ a → a ≤ j₁ + L → wX Z u j₁ L (a - j₁) y = reMul u (Z a y) :=
    fun u a ha1 ha2 => by
      unfold wX
      rw [min_eq_left (by omega : a - j₁ ≤ L), Nat.add_sub_cancel' ha1]
  have hX : ∀ u : ℂ, reMul u (Z ⌊(W : ℝ) * t⌋₊ y - Z ⌊(W : ℝ) * t'⌋₊ y) =
      wX Z u j₁ L (⌊(W : ℝ) * t⌋₊ - j₁) y - wX Z u j₁ L (⌊(W : ℝ) * t'⌋₊ - j₁) y := fun u => by
    rw [hat u _ (hrange t ht).1 (hrange t ht).2, hat u _ (hrange t' ht').1 (hrange t' ht').2,
      map_sub]
  have hsplit := Complex.norm_le_abs_re_add_abs_im (Z ⌊(W : ℝ) * t⌋₊ y - Z ⌊(W : ℝ) * t'⌋₊ y)
  by_cases hre : η / 2 < |(Z ⌊(W : ℝ) * t⌋₊ y - Z ⌊(W : ℝ) * t'⌋₊ y).re|
  · refine Or.inl (ClosedSumProof.exists_window (fun k => wX Z 1 j₁ L k y) (hrange t ht)
      (hrange t' ht') h1 h2 hNL ?_)
    have e1 : (Z ⌊(W : ℝ) * t⌋₊ y - Z ⌊(W : ℝ) * t'⌋₊ y).re =
        reMul 1 (Z ⌊(W : ℝ) * t⌋₊ y - Z ⌊(W : ℝ) * t'⌋₊ y) := by
      rw [ClosedSumProof.reMul_apply, one_mul]
    rw [e1, hX] at hre
    linarith
  · refine Or.inr (ClosedSumProof.exists_window (fun k => wX Z (-Complex.I) j₁ L k y)
      (hrange t ht) (hrange t' ht') h1 h2 hNL ?_)
    have e1 : (Z ⌊(W : ℝ) * t⌋₊ y - Z ⌊(W : ℝ) * t'⌋₊ y).im =
        reMul (-Complex.I) (Z ⌊(W : ℝ) * t⌋₊ y - Z ⌊(W : ℝ) * t'⌋₊ y) := by
      rw [ClosedSumProof.reMul_apply]; simp
    have him : η / 2 < |(Z ⌊(W : ℝ) * t⌋₊ y - Z ⌊(W : ℝ) * t'⌋₊ y).im| := by linarith
    rw [e1, hX] at him
    linarith

/-!
## The error budgets at fixed `W`
-/

/-- The summed bracket error of `c` against its conjugate partner (on `b3Alive`). -/
def brErr (b E s T h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) : ℝ≥0∞ :=
  ∑ j ∈ genNoBirthSteps s T τ W, ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
      (closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
          b3dX b E s h τ m W j Vs c y * partnerD b E s h τ m W j Vs c y) | b3Sigma W j np] y -
        (W : ℂ)⁻¹ * partnerP b E c (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ ∂closedLaw b W np

section Budgets

variable {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s T h : ℝ) (τ m : Fin np → ℝ)
  (R : ℝ) (W : ℕ) (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np)

include hb hE1 hE2

theorem errD_le :
    ∑ j ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => ¬ IsBirthStep τ W j),
      ∫⁻ y, ‖(b3AliveM b E s h τ m R W j Vs).indicator (fun y =>
        (closedLaw b W np)[(b3AliveM b E s h τ m R W j Vs).indicator
          (b3dX b E s h τ m W j Vs c) | b3Sigma W j np] y -
          (((W : ℝ)⁻¹ : ℝ) : ℂ) * cDrift b E c (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ
        ∂closedLaw b W np ≤ b3SummedErr b E s T h τ m R W Vs c c := by
  rw [b3SummedErr_eq_gen]
  refine le_trans (le_of_eq ?_) (le_self_add.trans le_self_add)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ClosedSumProof.ofReal_inv_natCast]
  exact (ClosedSumProof.lintegral_condErr_congr (b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs)
    _ _).symm

theorem errB_le :
    ∑ j ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => IsBirthStep τ W j),
      ∫⁻ y, ‖(b3AliveM b E s h τ m R W j Vs).indicator (fun y =>
        b3dX b E s h τ m W j Vs c y - cEntry c (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j)) y‖ₑ
        ∂closedLaw b W np ≤ b3SummedErr b E s T h τ m R W Vs c c := by
  rw [b3SummedErr_eq_gen]
  refine le_trans (le_of_eq ?_) le_add_self
  refine Finset.sum_congr rfl fun j _ => lintegral_congr_ae ?_
  filter_upwards [indicator_ae_eq_of_ae_eq_set (f := fun y =>
    b3dX b E s h τ m W j Vs c y - cEntry c (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j))
    (b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs)] with y hy
  rw [hy]

theorem errF_le :
    ∑ j ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => ¬ IsBirthStep τ W j),
      ∫⁻ y, ‖(b3AliveM b E s h τ m R W j Vs).indicator (fun y =>
        (closedLaw b W np)[(b3AliveM b E s h τ m R W j Vs).indicator (fun y =>
          b3dX b E s h τ m W j Vs c y * partnerD b E s h τ m W j Vs c y) | b3Sigma W j np] y -
          (((W : ℝ)⁻¹ : ℝ) : ℂ) * partnerP b E c (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ
        ∂closedLaw b W np ≤ brErr b E s T h τ m R W Vs c := by
  refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
  rw [ClosedSumProof.ofReal_inv_natCast]
  exact (ClosedSumProof.lintegral_condErr_congr (b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs)
    _ _).symm

theorem err4_eq :
    ∑ j ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => ¬ IsBirthStep τ W j),
      ∫⁻ y, (b3AliveM b E s h τ m R W j Vs).indicator (fun y =>
        ‖b3dX b E s h τ m W j Vs c y‖ₑ ^ 4) y ∂closedLaw b W np =
    ∑ j ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => ¬ IsBirthStep τ W j),
      ∫⁻ y, (b3Alive b E s h τ m R W j Vs).indicator (fun y =>
        ‖b3dX b E s h τ m W j Vs c y‖ₑ ^ 4) y ∂closedLaw b W np := by
  refine Finset.sum_congr rfl fun j _ => lintegral_congr_ae ?_
  filter_upwards [indicator_ae_eq_of_ae_eq_set (f := fun y =>
    ‖b3dX b E s h τ m W j Vs c y‖ₑ ^ 4) (b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs)] with y hy
  rw [hy]

end Budgets

/-- The bracket error of `c` against its partner tends to `0` (`ComplexClosedSummed`). -/
theorem tendsto_brErr (hS : ComplexClosedSummed) {b E : ℝ} {τ m : Fin np → ℝ} {T s h : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) (R : ℝ) (c : CIdx K np) :
    Tendsto (fun W => brErr b E s T h τ m R W (Vs W) c) atTop (𝓝 0) := by
  obtain ⟨hSum, hConj⟩ := hS b E np τ m T s h K Vs hD R
  cases c with
  | inl e =>
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hSum (Sum.inl e) (Sum.inl (swapE e))) (fun W => zero_le) fun W => ?_
      rw [b3SummedErr_eq_gen]
      exact le_trans (le_of_eq rfl) (le_add_self.trans le_self_add)
  | inr ij => exact hConj ij ij

/-!
## The modulus
-/

/-- **`TargetModulus` holds**: `ComplexClosedSummed + ComplexClosedFourth + ComplexClosedStopTail ⇒
ComplexClosedModulus`. -/
theorem targetModulus_holds : TargetModulus := by
  intro hS hF hT b E np τ m T s h K Vs hD c t₁ ht₁ ht₁T η θ hη hθ
  obtain ⟨hdom, hs0, -, -, -, hVs⟩ := id hD
  obtain ⟨hb0, hb, hE1, hE2, -, -, -, -⟩ := hdom
  have hb1 : b < 1 := by linarith
  have hfl : ∀ W : ℕ, closeLen s W ≤ ⌊(W : ℝ) * t₁⌋₊ ∧ ⌊(W : ℝ) * t₁⌋₊ ≤ ⌊(W : ℝ) * T⌋₊ :=
    fun W => ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left ht₁.le (Nat.cast_nonneg _)),
      Nat.floor_mono (mul_le_mul_of_nonneg_left ht₁T.le (Nat.cast_nonneg _))⟩
  have ht0 : 0 ≤ t₁ := (hs0.trans ht₁).le
  have hT0 : 0 < T := hs0.trans (ht₁.trans ht₁T)
  obtain ⟨R, hR⟩ := hT b E np τ m T s h K Vs hD (θ / 4) (by positivity)
  set Cb := driftCC b E K np R
  set Cc := covCC b E K np R
  have hCb0 : 0 ≤ Cb := driftCC_nonneg b E K np R
  have hCc0 : 0 ≤ Cc := covCC_nonneg b E K np R
  set lam := η / 16
  have hlam : 0 < lam := by positivity
  set δ := min (1 / 2) (min (η / (16 * (Cb + 1))) (θ * lam ^ 4 / (1024 * (Cc ^ 2 + 1) * (T + 1))))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδb : δ ≤ η / (16 * (Cb + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ ≤ θ * lam ^ 4 / (1024 * (Cc ^ 2 + 1) * (T + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  set A := (64 + 8 * lam ^ 2) / lam ^ 4 + 1 / lam + 1 / lam
  have hA0 : 0 ≤ A := by positivity
  set ε₀ := min 1 (θ / (8 * (A + 1)))
  have hε₀ : 0 < ε₀ := lt_min one_pos (by positivity)
  have hε₁ : ε₀ ≤ 1 := min_le_left _ _
  have hε₀A : ε₀ * A ≤ θ / 8 := by
    have h1 : ε₀ ≤ θ / (8 * (A + 1)) := min_le_right _ _
    have h2 : θ / (8 * (A + 1)) * A ≤ θ / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    exact (mul_le_mul_of_nonneg_right h1 hA0).trans h2
  have hSW := (ENNReal.tendsto_nhds_zero.mp ((hS b E np τ m T s h K Vs hD R).1 c c)) _
    (ENNReal.ofReal_pos.mpr hε₀)
  have hBW := (ENNReal.tendsto_nhds_zero.mp (tendsto_brErr hS hD R c)) _
    (ENNReal.ofReal_pos.mpr hε₀)
  have hFW := (ENNReal.tendsto_nhds_zero.mp (hF b E np τ m T s h K Vs hD R c)) _
    (ENNReal.ofReal_pos.mpr hε₀)
  have hWδ : ∀ᶠ W : ℕ in atTop, (1 : ℝ) ≤ W * δ := by
    filter_upwards [eventually_ge_atTop ⌈1 / δ⌉₊] with W hW
    have : (1 / δ : ℝ) ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hW)
    rwa [div_le_iff₀ hδ] at this
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp
    (hVs.and (hR.and (hSW.and (hBW.and (hFW.and hWδ)))))
  refine ⟨δ, hδ, W₀, fun W hW => ?_⟩
  obtain ⟨hV, hRW, hSW', hBW', hFW', hWδ'⟩ := hW₀ W hW
  have hW0 : (0 : ℝ) < W := by
    by_contra hc
    have h0 : (W : ℝ) = 0 := le_antisymm (not_lt.mp hc) (Nat.cast_nonneg _)
    rw [h0, zero_mul] at hWδ'
    linarith
  have hVm : Measurable (Vs W) :=
    hV.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set j₁ := ⌊(W : ℝ) * t₁⌋₊
  set L := ⌊(W : ℝ) * T⌋₊ - j₁
  set ℓ := ⌊(W : ℝ) * δ⌋₊ + 1
  set N := L / ℓ + 1
  have hℓ : 0 < ℓ := Nat.succ_pos _
  have hdm := Nat.div_add_mod L ℓ
  have hml := Nat.mod_lt L hℓ
  have hNL : L ≤ N * ℓ := by
    have e : N * ℓ = ℓ * (L / ℓ) + ℓ := by simp only [N]; ring
    omega
  have hNL2 : N * ℓ ≤ L + ℓ := by
    have e : N * ℓ = ℓ * (L / ℓ) + ℓ := by simp only [N]; ring
    omega
  have hjL : j₁ + L = ⌊(W : ℝ) * T⌋₊ := by have := (hfl W).2; omega
  have hℓR : (ℓ : ℝ) ≤ W * δ + 1 := by
    simp only [ℓ, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le (mul_nonneg hW0.le hδ.le)]
  set thr := 3 * lam + ℓ * ((W : ℝ)⁻¹ * Cb) + lam + lam
  have hthr : thr ≤ η / 2 := by
    have h1 : (ℓ : ℝ) * (W : ℝ)⁻¹ ≤ 2 * δ := by
      rw [← div_eq_mul_inv, div_le_iff₀ hW0]; linarith
    have h2 : 2 * δ * Cb ≤ η / 8 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (Cb + 1))).mp hδb
      nlinarith
    have h3 : (ℓ : ℝ) * ((W : ℝ)⁻¹ * Cb) ≤ 2 * δ * Cb := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hCb0
    simp only [thr, lam]; linarith
  -- the event inclusion
  set Z := zB b E s h τ m W (Vs W) c
  set stop := {y : ProbedPath W np × ℝ | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i,
    closeLen s W ≤ i ∧ i ≤ ⌊(W : ℝ) * T⌋₊ ∧
      R ≤ ((b3ClosedGramAt b E s h τ m W i (Vs W) y).1.trace).re}
  set mod : ℂ → Set (ProbedPath W np × ℝ) := fun u => {y | ∃ x y', x ≤ y' ∧ y' ≤ N * ℓ ∧
    y' ≤ x + ℓ ∧ thr < |wX Z u j₁ L y' y - wX Z u j₁ L x y|}
  have hincl : {y : ProbedPath W np × ℝ | y.1.1 ∈ physCapEventC b E s h K W ∧
      ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧ η <
        ‖b3X b E s h τ m W ⌊(W : ℝ) * t⌋₊ (Vs W) c y -
          cEntry c (b3JumpAt b s τ m W ⌊(W : ℝ) * t⌋₊) (b3KJumpAt E s τ m W ⌊(W : ℝ) * t⌋₊) -
          (b3X b E s h τ m W ⌊(W : ℝ) * t'⌋₊ (Vs W) c y -
            cEntry c (b3JumpAt b s τ m W ⌊(W : ℝ) * t'⌋₊)
              (b3KJumpAt E s τ m W ⌊(W : ℝ) * t'⌋₊))‖} ⊆
      stop ∪ ((b3Alive b E s h τ m R W ⌊(W : ℝ) * T⌋₊ (Vs W) ∩ mod 1) ∪
        (b3Alive b E s h τ m R W ⌊(W : ℝ) * T⌋₊ (Vs W) ∩ mod (-Complex.I))) := by
    rintro y ⟨hcap, t, ht, t', ht', htt, hη'⟩
    by_cases hst : y ∈ stop
    · exact Or.inl hst
    right
    have hal : y ∈ b3Alive b E s h τ m R W ⌊(W : ℝ) * T⌋₊ (Vs W) :=
      ⟨hcap, fun i hi1 hi2 => not_le.mp fun hR => hst ⟨hcap, i, hi1, hi2, hR⟩⟩
    rcases window_of_close Z y ht0 hδ.le (hfl W).2 hNL hthr ht ht' htt hη' with h1 | h1
    · exact Or.inl ⟨hal, h1⟩
    · exact Or.inr ⟨hal, h1⟩
  -- one part
  have hpart : ∀ u : ℂ, ‖u‖ = 1 → closedLaw b W np
      (b3Alive b E s h τ m R W ⌊(W : ℝ) * T⌋₊ (Vs W) ∩ mod u) ≤ ENNReal.ofReal (3 * θ / 8) := by
    intro u hu
    refine le_of_eq_of_le (measure_congr ((b3Alive_ae_eq hb1 hE1 hE2 s h τ m R W
      ⌊(W : ℝ) * T⌋₊ (Vs W)).inter (EventuallyEq.refl _ (mod u)))) ?_
    have hmod := window_modulus (closedLaw b W np) (fun j => b3Sigma W j np)
      (fun i => gen_sigma_le W i np) (fun i i' hii' => b3Sigma_mono hii')
      (fun j => b3AliveM b E s h τ m R W j (Vs W)) (fun j => b3dX b E s h τ m W j (Vs W) c)
      (fun j => partnerD b E s h τ m W j (Vs W) c) Z
      (fun j => cEntry c (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j))
      (fun j => IsBirthStep τ W j)
      (fun j y => cDrift b E c (b3ClosedGramAt b E s h τ m W j (Vs W) y))
      (fun j y => partnerP b E c (b3ClosedGramAt b E s h τ m W j (Vs W) y))
      (sc := (W : ℝ)⁻¹) (by positivity) hCb0 hCc0 (j₁ := j₁) (L := L)
      (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊)
      (fun k hk => Finset.mem_Ico.mpr ⟨by have := (hfl W).1; omega, by omega⟩)
      (fun k hk => measurableSet_b3AliveM_past s h τ m R
        (by have := (hfl W).1; omega) le_rfl hV.1)
      (fun k hk y hy => ⟨hy.1, fun i h1 h2 => hy.2 i h1 (by omega)⟩)
      (fun k hk => by
        have h1 : closeLen s W ≤ j₁ + k := by have := (hfl W).1; omega
        unfold b3dX
        exact ((measurable_b3X_past s h τ m (by omega) le_rfl hV.1 c).sub
          (measurable_b3X_past s h τ m h1 (Nat.le_succ _) hV.1 c)).stronglyMeasurable)
      (fun k hk y => partnerD_eq_star b E s h τ m W _ (Vs W) c y)
      (fun k hk y => zB_step b E s h τ m W (Vs W) c (by have := (hfl W).1; omega) y)
      (fun j hj => birth_eq_zero b E τ m hj c)
      (fun k hk => (measurable_cDrift_comp b E c
        (measurable_b3ClosedGramAt b E s h τ m W _ hVm)).aestronglyMeasurable)
      (fun k hk => (measurable_partnerP_comp b E c
        (measurable_b3ClosedGramAt b E s h τ m W _ hVm)).aestronglyMeasurable)
      (fun k hk y hy => by
        have hb := l1_b3Gram_le (by have := (hfl W).1; omega) hy
        exact norm_cDrift_le b E R c _ hb.1 hb.2)
      (fun k hk y hy => by
        have hb := l1_b3Gram_le (by have := (hfl W).1; omega) hy
        exact norm_partnerP_le b E R c _ hb.1 hb.2)
      hε₀.le hε₁
      ((errD_le hb1 hE1 hE2 s T h τ m R W (Vs W) c).trans hSW')
      ((errF_le hb1 hE1 hE2 s T h τ m R W (Vs W) c).trans hBW')
      ((errB_le hb1 hE1 hE2 s T h τ m R W (Vs W) c).trans hSW')
      ((err4_eq hb1 hE1 hE2 s T h τ m R W (Vs W) c).trans_le hFW')
      N ℓ hℓ hNL hu hlam hlam hlam
    rw [hjL] at hmod
    refine hmod.trans (ENNReal.ofReal_le_ofReal ?_)
    have hNLR : ((N : ℝ) * ℓ) ≤ W * T + (W * δ + 1) := by
      have h1 : ((N * ℓ : ℕ) : ℝ) ≤ (L : ℝ) + ℓ := by exact_mod_cast hNL2
      have h2 : (L : ℝ) ≤ W * T := (Nat.cast_le.mpr (Nat.sub_le _ _)).trans
        (Nat.floor_le (mul_nonneg hW0.le hT0.le))
      push_cast at h1; linarith
    have hc := ClosedSumProof.coeff_bound (Cc := Cc) hW0 hWδ' hT0 hNLR hδ2 (by positivity) hℓR
    have hb1' : 16 * ((W : ℝ)⁻¹ * Cc) ^ 2 * ((N : ℝ) * ℓ) * ℓ / lam ^ 4 ≤ θ / 32 := by
      have hl4 : 0 < lam ^ 4 := by positivity
      rw [div_le_iff₀ hl4]
      have h1 : 16 * ((W : ℝ)⁻¹ * Cc) ^ 2 * ((N : ℝ) * ℓ) * ℓ ≤ 32 * Cc ^ 2 * (T + 1) * δ := by
        nlinarith
      have h2 : 32 * Cc ^ 2 * (T + 1) * δ ≤ θ / 32 * lam ^ 4 := by
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 1024 * (Cc ^ 2 + 1) * (T + 1))).mp hδc
        have hC : Cc ^ 2 ≤ Cc ^ 2 + 1 := by linarith
        have hδ0 := hδ.le
        nlinarith [mul_le_mul_of_nonneg_right hC (mul_nonneg (by linarith : (0 : ℝ) ≤ T + 1) hδ0)]
      linarith
    have : ε₀ * ((64 + 8 * lam ^ 2) / lam ^ 4 + 1 / lam + 1 / lam) ≤ θ / 8 := hε₀A
    linarith
  refine (measure_mono hincl).trans ((measure_union_le _ _).trans
    ((add_le_add hRW (measure_union_le _ _)).trans ?_))
  refine (add_le_add le_rfl (add_le_add (hpart 1 (by simp))
    (hpart (-Complex.I) (by simp)))).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-!
## The fourth-moment estimate is the Lindeberg estimate
-/

/-- **`ComplexClosedFourth ↔ ComplexClosedLindeberg`**: the summed error of `ComplexClosedFourth`
is `b3LindebergErr` by definition (complex analogue of `closedFourth_iff_lindeberg`). -/
theorem complexClosedFourth_iff_lindeberg : ComplexClosedFourth ↔ ComplexClosedLindeberg :=
  Iff.rfl

end BlockBand.SourceProcess.PhysApprox.B3.Modul

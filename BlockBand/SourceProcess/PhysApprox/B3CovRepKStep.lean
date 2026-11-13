module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepKCond
public import BlockBand.SourceProcess.PhysApprox.B3CovRepCond

/-!
# The conditional `𝒦` brackets at one step as fresh-layer integrals

At a no-birth step `n_s ≤ j`, `1 ≤ j`, with `u_k = closedNearU`, `v_l = closedNearV`,
`X_cl = b3ClosedX` and `op ∈ {id, conj}`:

* `indicator_kdX_ae`: `1_{A_j}d𝒦_ij =ᵐ 1_{A_j^M} u_i*Δ(X_cl, F_j)v_j` for every entry (born:
  `closedStep_indicator`; unborn: both sides vanish, `b3ClosedKAt_dead`);
* **`ae_condExp_kBracket`**: a.e. on `A_j`,
  `E_j[1_{A_j}d𝒦_ij·op(d𝒦_kl)] = ∫ (u_i*Δv_j)·op(u_k*Δv_l) dF_j`, with `‖u‖, ‖v‖ ≤ √R`, `X_cl`
  passive and the near-rows identity (`ae_closedNearV_eq_closedPS`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Bridge
open scoped ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W np K : ℕ}

theorem closedNearU_dead (b E s h : ℝ) (τ m : Fin np → ℝ) {j : ℕ} {k : Fin np}
    (hk : j ≤ ⌊(W : ℝ) * τ k⌋₊) (y : ProbedPath W np × ℝ) :
    closedNearU b E s h τ m W j k y = 0 := by
  have hp : probeCol b E τ m W j k y.1 = 0 := funext fun a => probeFrame_dead b E τ m hk y.1 a
  simp [closedNearU, hp]

theorem closedNearV_dead (b E s h : ℝ) (τ m : Fin np → ℝ) {j : ℕ} {k : Fin np}
    (hk : j ≤ ⌊(W : ℝ) * τ k⌋₊) (y : ProbedPath W np × ℝ) :
    closedNearV b E s h τ m W j k y = 0 := by
  have hp : probeCol b E τ m W j k y.1 = 0 := funext fun a => probeFrame_dead b E τ m hk y.1 a
  simp [closedNearV, hp]

/-- The closed `𝒦` step of an entry, as an alive indicator of `u*Δv`. -/
theorem indicator_kdX_ae {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (hW : 1 ≤ W)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (R : ℝ) {T : ℝ} {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j ∈ genNoBirthSteps s T τ W) (ij : Fin np × Fin np) :
    (b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs (Sum.inr ij))
      =ᵐ[closedLaw b W np] (b3AliveM b E s h τ m R W j Vs).indicator fun y =>
        bilinear (closedNearU b E s h τ m W j ij.1 y)
          (freshDelta b E (b3ClosedX b E s h τ m W j y) (freshSample W j y.1.1))
          (closedNearV b E s h τ m W j ij.2 y) := by
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  obtain ⟨⟨hsj, -⟩, hnb⟩ := hj'
  by_cases hborn : ⌊(W : ℝ) * τ ij.1⌋₊ < j ∧ ⌊(W : ℝ) * τ ij.2⌋₊ < j
  · exact closedStep_indicator hb0 hb hE1 hE2 s h hh τ m hW Vs R hj1 hsj ij hborn.1 hborn.2
  · have hdead : ∀ k : Fin np, ¬ ⌊(W : ℝ) * τ k⌋₊ < j → j + 1 ≤ ⌊(W : ℝ) * τ k⌋₊ := by
      intro k hk
      have hne : ⌊(W : ℝ) * τ k⌋₊ ≠ j := fun h' => hnb ⟨k, h'⟩
      omega
    refine Eventually.of_forall fun y => ?_
    have h0 : b3dX b E s h τ m W j Vs (Sum.inr ij) y = 0 := by
      have hd : (j + 1 ≤ ⌊(W : ℝ) * τ ij.1⌋₊ ∨ j + 1 ≤ ⌊(W : ℝ) * τ ij.2⌋₊) := by
        rcases not_and_or.mp hborn with h1 | h1
        · exact Or.inl (hdead _ h1)
        · exact Or.inr (hdead _ h1)
      have hd' : (j ≤ ⌊(W : ℝ) * τ ij.1⌋₊ ∨ j ≤ ⌊(W : ℝ) * τ ij.2⌋₊) := by omega
      show b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2 -
        b3ClosedKAt b E s h τ m W j y ij.1 ij.2 = 0
      rw [b3ClosedKAt_dead b E s h τ m hd y, b3ClosedKAt_dead b E s h τ m hd' y, sub_zero]
    have h1 : bilinear (closedNearU b E s h τ m W j ij.1 y)
        (freshDelta b E (b3ClosedX b E s h τ m W j y) (freshSample W j y.1.1))
        (closedNearV b E s h τ m W j ij.2 y) = 0 := by
      rcases not_and_or.mp hborn with hk | hk
      · rw [closedNearU_dead b E s h τ m (by omega) y]; simp [bilinear]
      · rw [closedNearV_dead b E s h τ m (by omega) y]; simp [bilinear]
    show (b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs (Sum.inr ij)) y =
      (b3AliveM b E s h τ m R W j Vs).indicator (fun y =>
        bilinear (closedNearU b E s h τ m W j ij.1 y)
          (freshDelta b E (b3ClosedX b E s h τ m W j y) (freshSample W j y.1.1))
          (closedNearV b E s h τ m W j ij.2 y)) y
    rw [Set.indicator_apply_eq_zero.mpr (fun _ => h0)]
    by_cases hyM : y ∈ b3AliveM b E s h τ m R W j Vs
    · rw [Set.indicator_of_mem hyM, h1]
    · rw [Set.indicator_of_notMem hyM]

theorem clipVec_of_le {C : ℝ} {w : Fin W → ℂ} (h : vecNorm w ≤ C) : clipVec C w = w := by
  simp [clipVec, h]

/-- **The conditional `𝒦` bracket at one step is a fresh-layer integral.** -/
theorem ae_condExp_kBracket {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (hW : 1 ≤ W)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) (R : ℝ) {T : ℝ} {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j ∈ genNoBirthSteps s T τ W)
    (op : ℂ → ℂ) (hop : Continuous op) (hopn : ∀ z, ‖op z‖ = ‖z‖)
    (hint : Integrable (fun y =>
      ‖freshDelta b E (b3ClosedX b E s h τ m W j y) (freshSample W j y.1.1)‖ ^ 2)
      (closedLaw b W np))
    (ij kl : Fin np × Fin np) :
    ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
      (closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
          b3dX b E s h τ m W j Vs (Sum.inr ij) y * op (b3dX b E s h τ m W j Vs (Sum.inr kl) y)) |
          b3Sigma W j np] y =
        ∫ F, bilinear (closedNearU b E s h τ m W j ij.1 y)
            (freshDelta b E (b3ClosedX b E s h τ m W j y) F) (closedNearV b E s h τ m W j ij.2 y) *
          op (bilinear (closedNearU b E s h τ m W j kl.1 y)
            (freshDelta b E (b3ClosedX b E s h τ m W j y) F)
            (closedNearV b E s h τ m W j kl.2 y)) ∂freshLaw W b := by
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  have hsj : closeLen s W ≤ j := hj'.1.1
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j Vs
  set Am := b3AliveM b E s h τ m R W j Vs
  have hA : A =ᵐ[μ] Am := b3Alive_ae_eq (by linarith) hE1 hE2 s h τ m R W j Vs
  have hAm : MeasurableSet[b3Sigma W j np] Am :=
    Modul.measurableSet_b3AliveM_past (b := b) (E := E) s h τ m R hsj le_rfl hVs
  set X := b3ClosedX b E s h τ m W j
  set u : Fin np → ProbedPath W np × ℝ → Fin W → ℂ := fun k y => closedNearU b E s h τ m W j k y
  set v : Fin np → ProbedPath W np × ℝ → Fin W → ℂ := fun k y => closedNearV b E s h τ m W j k y
  set cu : Fin np → ProbedPath W np × ℝ → Fin W → ℂ := fun k y => clipVec (Real.sqrt R) (u k y)
  set cv : Fin np → ProbedPath W np × ℝ → Fin W → ℂ := fun k y => clipVec (Real.sqrt R) (v k y)
  -- the frames are bounded by `√R` a.e. on the alive set
  have hnorm : ∀ᵐ y ∂μ, y ∈ A → ∀ k, vecNorm (u k y) ≤ Real.sqrt R ∧
      vecNorm (v k y) ≤ Real.sqrt R := by
    filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
      ae_closedPhase_good (W := W) (np := np) b E s h j] with y hP hQ hyA k
    have htr := hyA.2 j hsj le_rfl
    exact ⟨norm_closedNearU_le b E s h τ m j Vs k y htr,
      norm_closedNearV_le b E s h hh τ m j Vs k y (hP.2.2.2 j) (isUnit_iff_ne_zero.2 hQ.1) htr⟩
  set g : Fin np × Fin np → ProbedPath W np × ℝ → ℂ := fun e y =>
    bilinear (cu e.1 y) (freshDelta b E (X y) (freshSample W j y.1.1)) (cv e.2 y)
  have hstep1 : A.indicator (fun y => b3dX b E s h τ m W j Vs (Sum.inr ij) y *
      op (b3dX b E s h τ m W j Vs (Sum.inr kl) y)) =ᵐ[μ]
      Am.indicator (fun y => g ij y * op (g kl y)) := by
    filter_upwards [indicator_kdX_ae hb0 hb hE1 hE2 s h hh τ m hW Vs R hj1 hj ij,
      indicator_kdX_ae hb0 hb hE1 hE2 s h hh τ m hW Vs R hj1 hj kl, hA, hnorm]
      with y h1 h2 hyA hn
    by_cases hy : y ∈ A
    · have hyM : y ∈ Am := (Iff.of_eq hyA).mp hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hyM] at h1 h2
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hyM, h1, h2]
      simp only [g, cu, cv, clipVec_of_le (hn hy _).1, clipVec_of_le (hn hy _).2, u, v, X]
    · have hyM : y ∉ Am := fun hh' => hy ((Iff.of_eq hyA).mpr hh')
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hyM]
  have hbd : ∀ k y, vecNorm (cu k y) ≤ Real.sqrt R ∧ vecNorm (cv k y) ≤ Real.sqrt R :=
    fun k y => ⟨vecNorm_clipVec_le (Real.sqrt_nonneg _) _,
      vecNorm_clipVec_le (Real.sqrt_nonneg _) _⟩
  have hmu : ∀ k, Measurable (cu k) := fun k =>
    measurable_clipVec_comp _ (measurable_closedNearU b E s h τ m j k)
  have hmv : ∀ k, Measurable (cv k) := fun k =>
    measurable_clipVec_comp _ (measurable_closedNearV b E s h τ m j k)
  have hiu : ∀ k y, cu k (b3Ext W j y) = cu k y := fun k y => by
    simp only [cu, u, closedNearU_b3Ext hsj le_rfl]
  have hiv : ∀ k y, cv k (b3Ext W j y) = cv k y := fun k y => by
    simp only [cv, v, closedNearV_b3Ext hsj le_rfl]
  obtain ⟨hgi, hce⟩ := condExp_bilinear_pair b E j op hop hopn (hmu ij.1) (hmv ij.2) (hmu kl.1)
    (hmv kl.2) (measurable_b3ClosedX b E s h τ m j) (hiu ij.1) (hiv ij.2) (hiu kl.1) (hiv kl.2)
    (fun y => b3ClosedX_b3Ext hsj le_rfl y) (fun y => (hbd ij.1 y).1) (fun y => (hbd ij.2 y).2)
    (fun y => (hbd kl.1 y).1) (fun y => (hbd kl.2 y).2) hint
  have hall := (condExp_congr_ae (m := b3Sigma W j np) hstep1).trans
    (condExp_indicator hgi hAm)
  filter_upwards [hall, hce, hA, hnorm] with y hy hy2 hyA hn hyAl
  have hyM : y ∈ Am := (Iff.of_eq hyA).mp hyAl
  rw [hy, Set.indicator_of_mem hyM, hy2]
  simp only [cu, cv, clipVec_of_le (hn hyAl _).1, clipVec_of_le (hn hyAl _).2, u, v, X]

end BlockBand.SourceProcess.PhysApprox.B3

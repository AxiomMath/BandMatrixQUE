module

public import BlockBand.Native.ErdosRiabov.ZigProof.Bootstrap
public import BlockBand.Native.ErdosRiabov.Flow.Exponents
public import BlockBand.Native.ErdosRiabov.Flow.Scales

/-!
# From the `φ`-form of the master inequalities to `MasterIneqConclusion`

The master inequalities are stated with the control parameters
`φ_k = Flow.Expo.phiIso/phiAv N ξ L_t Y_t k` with `L_t = P.lEta t` and
`Y_t = √(Nη_t)/(ℓ_tη_t)` (`Forcing.yScale P t`; here `yZig P t`, the same expression). The
master inequalities themselves are a hypothesis here (they are proved in `MI` and `SatLin`,
through `MI.masterIneqPhi_of_MI` and `SatLin.masterIneqSat`).
* `MasterIneqPhi` (a statement): the master inequalities, fixed-time form, with very high
  probability:
  `P(t ≤ τ ∧ N^{ε'} φ^{iso}_{k,t} < isoRatio i t H_t) ≤ N^{-D}` and the averaged analogue, with
  the same quantifiers, law, `τ = zigTau p d z` and hypotheses as `MasterIneqConclusion`.
* `phi_level_le`: the exponent inequality (`Flow.Expo.phi_le`) with the scale bounds
  (`Flow.vsScales`): `N^{ε'} φ_{k,t} ≤ N^{ε'} C_φ (N^ξ + N^{-ν/2} ψ_k)` for `t ∈ [0,1]`,
  `C_φ = phiConst` (the monomial counts, an absolute constant).
* **`masterIneqConclusion_of_phi`**: `MasterIneqPhi → MasterIneqConclusion` (event inclusion,
  `C = phiConst`); **`shortRingLocalLaw_of_masterIneqPhi`**: `MasterIneqPhi →
  Inputs.ShortRingLocalLaw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.ZigProof

open MeasureTheory Set
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Assembly
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

/-- `Y_t = √(N η_t)/(ℓ_t η_t)` (the same expression as `Forcing.yScale P t`). -/
def yZig {N : ℕ} (P : PsiData N) (t : ℝ) : ℝ :=
  Real.sqrt ((N : ℝ) * vsHeight P.z t) / P.lEta t

/-- **the master inequality, fixed-time form, with the control parameters `φ`.**
For every `d : VSData` and `D > 0` there is `N₀: ℕ` such that for every ring `p` with
`p.b = d.b`, `N ≥ N₀`, `ζ₀ < 1`, `N^{1+ζ₀} ≤ W²`, every model, every `z ∈ 𝒟`, every
deterministic `t ∈ [0,1]`, `k ∈ [1,8]` and every isotropic/averaged index `i`, under
`driverLaw model.law`:
`P(t ≤ τ ∧ N^{ε'} φ^{iso}_{k,t} < isoRatio i t H_t) ≤ N^{-D}` with
`φ^{iso}_{k,t} = Expo.phiIso N ξ (P.lEta t) (yZig P t) k`, and likewise with `Expo.phiAv`,
`avRatio`.
-/
def MasterIneqPhi : Prop :=
  ∀ (d : VSData) (D : ℝ), 0 < D → ∃ N₀ : ℕ,
    ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W → d.zeta0 < 1 →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ),
        BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z →
        ∀ t : ℝ≥0, t ≤ 1 → ∀ k ∈ kRange,
          (∀ i : IsoIdx (p.n * p.W) k,
            driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
                {x | (t : WithTop ℝ≥0) ≤ zigTau p d z x ∧
                  ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
                      Expo.phiIso ((p.n * p.W : ℕ) : ℝ) d.xi ((zigPsiData p d.D z).lEta t)
                        (yZig (zigPsiData p d.D z) t) k <
                    (zigPsiData p d.D z).isoRatio i t (VS.vsBandFin p t x)} ≤
              ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D))) ∧
          ∀ i : AvIdx (p.n * p.W) k,
            driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
                {x | (t : WithTop ℝ≥0) ≤ zigTau p d z x ∧
                  ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
                      Expo.phiAv ((p.n * p.W : ℕ) : ℝ) d.xi ((zigPsiData p d.D z).lEta t)
                        (yZig (zigPsiData p d.D z) t) k <
                    (zigPsiData p d.D z).avRatio i t (VS.vsBandFin p t x)} ≤
              ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D))

/-- The constant of the exponent inequality: `1 + ∑_{k ≤ 8}` (number of monomials of `φ^{iso}_k` and
`φ^{av}_k`); an absolute constant. -/
def phiConst : ℝ :=
  ∑ k ∈ Finset.range 9, (((Expo.isoMonos k).length : ℝ) + ((Expo.avMonos k).length : ℝ)) + 1

theorem phiConst_pos : 0 < phiConst := by
  unfold phiConst
  positivity

theorem length_le_phiConst {k : ℕ} (hk : k ≤ 8) :
    ((Expo.isoMonos k).length : ℝ) ≤ phiConst ∧ ((Expo.avMonos k).length : ℝ) ≤ phiConst := by
  have hmem : k ∈ Finset.range 9 := Finset.mem_range.2 (by omega)
  have h : ((Expo.isoMonos k).length : ℝ) + ((Expo.avMonos k).length : ℝ) ≤
      ∑ j ∈ Finset.range 9, (((Expo.isoMonos j).length : ℝ) + ((Expo.avMonos j).length : ℝ)) :=
    Finset.single_le_sum (f := fun j => ((Expo.isoMonos j).length : ℝ) +
      ((Expo.avMonos j).length : ℝ)) (fun j _ => by positivity) hmem
  have h0 : (0 : ℝ) ≤ (Expo.isoMonos k).length := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ (Expo.avMonos k).length := Nat.cast_nonneg _
  unfold phiConst
  constructor <;> linarith

/-- ** along the VS flow.** For a ring with `N^{1+ζ₀} ≤ W²`, `z ∈ 𝒟`, `t ∈ [0,1]` and
`k ∈ [1,8]`:
`N^{ε'} φ^{iso}_{k,t} ≤ miLevelIso d phiConst N k` and
`N^{ε'} φ^{av}_{k,t} ≤ miLevelAv d phiConst N k` (Lemma *expo* `Expo.phi_le` with Lemma
*scales* (a), (c) `vsScales`, and `ξ < δ₀/100`).
Deterministic.
-/
theorem phi_level_le (d : VSData) {p : BlockBand.Parameters}
    (hband : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2) {z : ℂ}
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z) {t : ℝ≥0} (ht : t ≤ 1) {k : ℕ}
    (hk : k ∈ kRange) :
    ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
        Expo.phiIso ((p.n * p.W : ℕ) : ℝ) d.xi ((zigPsiData p d.D z).lEta t)
          (yZig (zigPsiData p d.D z) t) k ≤ miLevelIso d phiConst (p.n * p.W) k ∧
      ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
        Expo.phiAv ((p.n * p.W : ℕ) : ℝ) d.xi ((zigPsiData p d.D z).lEta t)
          (yZig (zigPsiData p d.D z) t) k ≤ miLevelAv d phiConst (p.n * p.W) k := by
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hNR0 : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hNR1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hWN : p.W ≤ p.n * p.W := Nat.le_mul_of_pos_left _ (by have := p.n_ge_four; omega)
  have ht1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  obtain ⟨-, -, hX, -, -, hY, -⟩ := vsScales hNpos hWN d.kappa_pos (by linarith [d.C0_ge_one])
    d.delta0_lt_zeta0.le hband hz le_rfl (NNReal.coe_nonneg t) ht1
  have hzim : 0 < z.im := hz.im_pos hNpos
  have hη : 0 < vsHeight z t := vsHeight_pos hzim ht1
  have hL : 0 < (zigPsiData p d.D z).lEta t :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNR0 _) hX
  have hY0 : 0 < yZig (zigPsiData p d.D z) t :=
    div_pos (Real.sqrt_pos.2 (mul_pos hNR0 hη)) hL
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk8 : k ≤ 8 := (Finset.mem_Icc.mp hk).2
  obtain ⟨hφI, hφA⟩ := Expo.phi_le (X := (zigPsiData p d.D z).lEta t)
    (Y := yZig (zigPsiData p d.D z) t) hNR1 d.xi_pos d.xi_lt_delta0_div.le hX hY0 hY hk1 hk8
  obtain ⟨hlI, hlA⟩ := length_le_phiConst hk8
  have hpow : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ d.epsP := Real.rpow_nonneg hNR0.le _
  constructor
  · unfold miLevelIso
    refine mul_le_mul_of_nonneg_left (hφI.trans (mul_le_mul_of_nonneg_right hlI ?_)) hpow
    unfold Expo.thrIso
    positivity
  · unfold miLevelAv
    refine mul_le_mul_of_nonneg_left (hφA.trans (mul_le_mul_of_nonneg_right hlA ?_)) hpow
    unfold Expo.thrAv
    positivity

/-- **`MasterIneqPhi → MasterIneqConclusion`** with `C = phiConst`, `N₀` unchanged (event
inclusion by `phi_level_le`).
-/
theorem masterIneqConclusion_of_phi (h : MasterIneqPhi) : MasterIneqConclusion := by
  intro d D hD
  obtain ⟨N₀, hN₀⟩ := h d D hD
  refine ⟨phiConst, phiConst_pos, N₀, fun p hpb hN hζ hband model z hz t ht k hk => ?_⟩
  obtain ⟨hI, hA⟩ := hN₀ p hpb hN hζ hband model z hz t ht k hk
  obtain ⟨hlI, hlA⟩ := phi_level_le d hband hz ht hk
  refine ⟨fun i => le_trans (measure_mono ?_) (hI i), fun i => le_trans (measure_mono ?_) (hA i)⟩
  · exact fun x hx => ⟨hx.1, lt_of_le_of_lt hlI hx.2⟩
  · exact fun x hx => ⟨hx.1, lt_of_le_of_lt hlA hx.2⟩

/-- **The short-ring local law from the `φ`-form master inequalities.** The statement
`Inputs.ShortRingLocalLaw` from `MasterIneqPhi`, via `masterIneqConclusion_of_phi` and
`shortRingLocalLaw_of_masterIneq`.
-/
theorem shortRingLocalLaw_of_masterIneqPhi (h : MasterIneqPhi) :
    BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw :=
  shortRingLocalLaw_of_masterIneq (masterIneqConclusion_of_phi h)

end BlockBand.Native.ErdosRiabov.ZigProof

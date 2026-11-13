module

public import BlockBand.Native.ErdosRiabov.Evol.Defs
public import BlockBand.Native.ErdosRiabov.VS.ResolventItoGlue

/-!
# Evolution of `𝒳^k`, `𝒴^k` along the VS band process

The averaged and isotropic chain fluctuations are continuous semimartingales whose drift is the
generator term plus the forcing.

* **(a) `evol_av`**: `Re 𝒳^k_t` and `Im 𝒳^k_t` (`𝒳 = Tr[(G - M^{(t)})_{[1,k]} S^{x_k}]`) are
  continuous semimartingales (bracket: `VS.chainBracket` with `K = 1`, resp. `K = -i·1`); for
  `t ≤ 1` the process is `Re/Im 𝒳^k_t(H_t)` and the drift is
  `Re/Im[(⊕_{j=1}^k Â_{j,t})[𝒳^k] + 𝓕^av]`.
* **(b) `evol_iso`**: the same for `𝒴^k_t(a,x',b) = ((G - M^{(t)})_{[1,k]})_{ab}` with
  `(⊕_{j=1}^{k-1} Â_{j,t})[𝒴^k] + 𝓕^iso` (`K = E_ba`, resp. `-i E_ba`).
* **(c) `evol_iso_one`** (`k = 1`, unconditional): `d(G - m)_{ab} = (G 𝒮[G - m] G)_{ab} dt + d𝓜`;
  no propagator, no scalar; also `forcingIso_one`: `𝓕^iso = (G𝒮[G - m]G)_{ab}` for `k = 1`.

`𝓕` is the remainder `dG-drift - M-derivative - Â-terms`; it is split further elsewhere. The
deterministic Duhamel form is `Flow.duhamel_det`; the stochastic Duhamel form is not treated
here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Evol

open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.CEH.Flow
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ComplexConjugate

variable {p : BlockBand.Parameters} {k : ℕ}

/-!
### Values of the chain test functions
-/

theorem chainTestT_eq_reTr_gChain {z : ℂ} (hz : 0 < z.im) (σ : Fin k → Bool)
    (B : Fin k → RingMat p) (K : RingMat p) {t : ℝ} (ht : t ≤ 1) (y : Fin (ringDim p) → ℝ) :
    chainTestT 0 (ringMatrixFin p) (vsPatternSpec z (semicircleM z) σ) B K (t, y) =
      reTr K (gChain (patZ z σ t) B (ringMatrixFin p y)) := by
  have hy := semicircleM_im_pos hz
  have hδ : 0 ≤ z.im / (2 * (semicircleM z).im) := by positivity
  rw [chainTestT, chainTest, resChain_zero_eq_gChain]
  congr 2
  funext j
  exact (patZ_eq_vsPatternSpec z σ ht hδ j).symm

theorem reTr_one_eq {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) : reTr 1 X = (trace X).re := by
  simp [reTr]

theorem reTr_negI_one_eq {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    reTr (-Complex.I • (1 : Matrix (Fin N) (Fin N) ℂ)) X = (trace X).im := by
  rw [reTr_neg_I_smul, one_mul]

theorem reTr_negI_single_eq {N : ℕ} (a b : Fin N) (X : Matrix (Fin N) (Fin N) ℂ) :
    reTr (-Complex.I • Matrix.single b a (1 : ℂ)) X = (X a b).im := by
  rw [reTr_neg_I_smul, trace_single_mul, one_smul]

theorem min_coe_eq {t : ℝ≥0} (ht : (t : ℝ) ≤ 1) : min (t : ℝ) 1 = t := min_eq_left ht

/-!
### (a) The averaged chains
-/

/-- **Conditional on `Split.DerivStatement`**.
For `Im z > 0`, `P.S = shortRingProfile p.b p.n p.W` (and
stochastic symmetric), `1 ≤ k`, every pattern `σ` and sites `x`:
`Re 𝒳` and `Im 𝒳` are
continuous semimartingales for `driverAugmented μ` under `driverLaw μ`, with drift
`chainDrift - (d/dt Re/Im Tr[M S^{x_k}])` and bracket `chainBracket`; for `t ≤ 1` they are
`Re/Im 𝒳^k_t(H_t)` and the drifts are `Re/Im[(⊕_j Â_{j,t})[𝒳^k_t] + 𝓕^av_t]`.
-/
theorem evol_av (hD : Split.DerivStatement) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {P : PsiData (p.n * p.W)} (hz : 0 < P.z.im) (hS : StochasticSymm P.S)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (x : Fin k → Fin (p.n * p.W)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
        (driverAugmented (κ := Fin (ringDim p)) μ)
        (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
          (avSlots P.S x) 1 ((t : ℝ), vsNoise p t ω) - (avM P σ x (min (t : ℝ) 1)).re)
        (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x) 1 t
          (vsNoise p t ω) - frozenDeriv (fun s => (dMav P σ x s).re) t)
        (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
          chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x) 1 t
            (vsNoise p t ω)) ∧
      IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
        (driverAugmented (κ := Fin (ringDim p)) μ)
        (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
          (avSlots P.S x) (-Complex.I • 1) ((t : ℝ), vsNoise p t ω) -
            (avM P σ x (min (t : ℝ) 1)).im)
        (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x)
          (-Complex.I • 1) t (vsNoise p t ω) - frozenDeriv (fun s => (dMav P σ x s).im) t)
        (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
          chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x)
            (-Complex.I • 1) t (vsNoise p t ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ ω : RingSample p,
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
            (avSlots P.S x) 1 ((t : ℝ), vsNoise p t ω) - (avM P σ x (min (t : ℝ) 1)).re =
          (P.avErr σ x t (vsBandFin p t ω)).re ∧
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
            (avSlots P.S x) (-Complex.I • 1) ((t : ℝ), vsNoise p t ω) -
            (avM P σ x (min (t : ℝ) 1)).im = (P.avErr σ x t (vsBandFin p t ω)).im ∧
        chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x) 1 t
            (vsNoise p t ω) - frozenDeriv (fun s => (dMav P σ x s).re) t =
          (aTermAv P σ x t (vsBandFin p t ω) + forcingAv P σ x t (vsBandFin p t ω)).re ∧
        chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x) (-Complex.I • 1) t
            (vsNoise p t ω) - frozenDeriv (fun s => (dMav P σ x s).im) t =
          (aTermAv P σ x t (vsBandFin p t ω) + forcingAv P σ x t (vsBandFin p t ω)).im := by
  have hm := semicircleM_im_pos hz
  have hF := fun s (hs : s ∈ Icc (0 : ℝ) 1) => hasDerivAt_avM P hD hz.ne' hS hk σ x hs
  have hF' := continuousOn_dMav P hz.ne' hS σ x
  refine ⟨chain_sub_ito μ hz hm σ _ _ (fun s hs => hasDerivAt_re (hF s hs))
      (Complex.continuous_re.comp_continuousOn hF'),
    chain_sub_ito μ hz hm σ _ _ (fun s hs => hasDerivAt_im (hF s hs))
      (Complex.continuous_im.comp_continuousOn hF'), fun t ht ω => ?_⟩
  have hval : ∀ K, chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
      (avSlots P.S x) K ((t : ℝ), vsNoise p t ω) =
        reTr K (gChain (patZ P.z σ t) (avSlots P.S x) (vsBandFin p t ω)) :=
    fun K => chainTestT_eq_reTr_gChain hz σ _ K ht _
  have hdr : ∀ K, chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x) K t
      (vsNoise p t ω) = reTr K (dGmat P.S P.z σ (avSlots P.S x) t (vsBandFin p t ω)) := by
    intro K
    rw [hPS]
    exact chainDrift_eq_reTr_dGmat hz σ _ K ht _
  have hsum : aTermAv P σ x t (vsBandFin p t ω) + forcingAv P σ x t (vsBandFin p t ω) =
      dGav P σ x t (vsBandFin p t ω) - dMav P σ x t := aTermAv_add_forcingAv P σ x t _
  rw [min_coe_eq ht, frozenDeriv_of_le ht, frozenDeriv_of_le ht, hval, hval, hdr, hdr, hsum,
    reTr_one_eq, reTr_one_eq, reTr_negI_one_eq, reTr_negI_one_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [PsiData.avErr, avM, dGav]

/-!
### (b) The isotropic chains
-/

/-- **Conditional on `Split.DerivStatement`**.
Hypotheses as in `evol_av`, plus sites `a, b`:
`Re 𝒴` and
`Im 𝒴` (`𝒴 = ((G - M^{(t)})_{[1,k]})_{ab}`) are continuous semimartingales with drift
`chainDrift - d/dt(δ_ab Re/Im M_aa)` and bracket `chainBracket` (`K = E_ba`, `-i E_ba`); for
`t ≤ 1` they are `Re/Im 𝒴^k_t(H_t)` and the drifts are
`Re/Im[(⊕_{j=1}^{k-1} Â_{j,t})[𝒴^k_t] + 𝓕^iso_t]`.
-/
theorem evol_iso (hD : Split.DerivStatement) (μ : Measure p.SiteMatrix)
    [IsProbabilityMeasure μ] {P : PsiData (p.n * p.W)} (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (a b : Fin (p.n * p.W)) (x : Fin k → Fin (p.n * p.W)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
        (driverAugmented (κ := Fin (ringDim p)) μ)
        (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
          (isoSlots P.S x) (Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x (min (t : ℝ) 1)).re)
        (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
          (Matrix.single b a 1) t (vsNoise p t ω) -
            frozenDeriv (fun s => (dMiso P σ a b x s).re) t)
        (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
          chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (Matrix.single b a 1) t (vsNoise p t ω)) ∧
      IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
        (driverAugmented (κ := Fin (ringDim p)) μ)
        (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
          (isoSlots P.S x) (-Complex.I • Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x (min (t : ℝ) 1)).im)
        (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
          (-Complex.I • Matrix.single b a 1) t (vsNoise p t ω) -
            frozenDeriv (fun s => (dMiso P σ a b x s).im) t)
        (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
          chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (-Complex.I • Matrix.single b a 1) t (vsNoise p t ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ ω : RingSample p,
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
            (isoSlots P.S x) (Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x (min (t : ℝ) 1)).re = (P.isoErr σ a b x t (vsBandFin p t ω)).re ∧
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
            (isoSlots P.S x) (-Complex.I • Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x (min (t : ℝ) 1)).im = (P.isoErr σ a b x t (vsBandFin p t ω)).im ∧
        chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (Matrix.single b a 1) t (vsNoise p t ω) -
            frozenDeriv (fun s => (dMiso P σ a b x s).re) t =
          (aTermIso P σ a b x t (vsBandFin p t ω) +
            forcingIso P σ a b x t (vsBandFin p t ω)).re ∧
        chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (-Complex.I • Matrix.single b a 1) t (vsNoise p t ω) -
            frozenDeriv (fun s => (dMiso P σ a b x s).im) t =
          (aTermIso P σ a b x t (vsBandFin p t ω) +
            forcingIso P σ a b x t (vsBandFin p t ω)).im := by
  have hm := semicircleM_im_pos hz
  have hF := fun s (hs : s ∈ Icc (0 : ℝ) 1) => hasDerivAt_isoM P hD hz.ne' hS hk σ a b x hs
  have hF' := continuousOn_dMiso P hz.ne' hS σ a b x
  refine ⟨chain_sub_ito μ hz hm σ _ _ (fun s hs => hasDerivAt_re (hF s hs))
      (Complex.continuous_re.comp_continuousOn hF'),
    chain_sub_ito μ hz hm σ _ _ (fun s hs => hasDerivAt_im (hF s hs))
      (Complex.continuous_im.comp_continuousOn hF'), fun t ht ω => ?_⟩
  have hval : ∀ K, chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
      (isoSlots P.S x) K ((t : ℝ), vsNoise p t ω) =
        reTr K (gChain (patZ P.z σ t) (isoSlots P.S x) (vsBandFin p t ω)) :=
    fun K => chainTestT_eq_reTr_gChain hz σ _ K ht _
  have hdr : ∀ K, chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x) K t
      (vsNoise p t ω) = reTr K (dGmat P.S P.z σ (isoSlots P.S x) t (vsBandFin p t ω)) := by
    intro K
    rw [hPS]
    exact chainDrift_eq_reTr_dGmat hz σ _ K ht _
  have hsum : aTermIso P σ a b x t (vsBandFin p t ω) + forcingIso P σ a b x t (vsBandFin p t ω) =
      dGiso P σ a b x t (vsBandFin p t ω) - dMiso P σ a b x t :=
    aTermIso_add_forcingIso P σ a b x t _
  rw [min_coe_eq ht, frozenDeriv_of_le ht, frozenDeriv_of_le ht, hval, hval, hdr, hdr, hsum,
    reTr_single, reTr_single, reTr_negI_single_eq, reTr_negI_single_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [PsiData.isoErr, isoM, dGiso]

/-!
### (c) The case `k = 1` (no propagator)
-/

theorem mChain_one {N : ℕ} (P : PsiData N) (σ : Fin 1 → Bool) (x : Fin 1 → Fin N) (s : ℝ) :
    P.mChain σ x s = fun _ => patM P.z σ 1 := by
  funext a
  rw [PsiData.mChain, Split.chainM, Split.chainTilde_eq, ite_eq_right (lt_irrefl 1)]
  simp

theorem mDerivP_one {N : ℕ} (P : PsiData N) (σ : Fin 1 → Bool) (x : Fin 1 → Fin N) (s : ℝ) :
    mDerivP P σ x s = 0 := by
  funext a
  simp [mDerivP, mDeriv]

theorem dGmat_one {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (σ : Fin 1 → Bool)
    (x : Fin 1 → Fin N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    dGmat S z σ (isoSlots S x) t H =
      slotsH z σ t H 0 *
        bandSelfEnergy S (slotsH z σ t H 0 - VS.patConj (σ 0) (semicircleM z) • 1) *
          slotsH z σ t H 0 := by
  have hB : isoSlots S x 0 = 1 := by simp [isoSlots]
  simp [dGmat, pairIns, segProd_self, hB]

theorem frozenDeriv_zero (t : ℝ≥0) : frozenDeriv (fun _ => (0 : ℝ)) t = 0 := by
  unfold frozenDeriv
  split_ifs <;> rfl

/-- For `k = 1` the isotropic forcing is the whole `G`-drift: `𝓕^iso = (G 𝒮[G - m_1] G)_{ab}`
(no generator term, `d/dt M_{[1,1]} = 0`). -/
theorem forcingIso_one {N : ℕ} (P : PsiData N) (σ : Fin 1 → Bool) (a b : Fin N)
    (x : Fin 1 → Fin N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    forcingIso P σ a b x t H =
      (slotsH P.z σ t H 0 *
        bandSelfEnergy P.S (slotsH P.z σ t H 0 - VS.patConj (σ 0) (semicircleM P.z) • 1) *
          slotsH P.z σ t H 0) a b := by
  have hA : aTermIso P σ a b x t H = 0 := by
    unfold aTermIso
    apply Finset.sum_eq_zero
    intro j hj
    simp at hj
  have hM : dMiso P σ a b x t = 0 := by
    simp [dMiso, mDerivP_one]
  rw [forcingIso, hA, hM, dGiso, dGmat_one, sub_zero, sub_zero]

/-- For `Im z > 0`,
`P.S = shortRingProfile p.b p.n p.W`, a pattern `σ:
Fin 1 → Bool` and sites `a, b`:
`Re (G - m)_{ab}` and `Im (G - m)_{ab}` along the VS band process are continuous
semimartingales with drift `chainDrift` (no `M`-derivative:
`M^{(t)}_{[1,1]} = m_1`) and bracket
`chainBracket`; for `t ≤ 1` the processes are `Re/Im 𝒴^1_t(H_t)` and the drifts are
`Re/Im (G 𝒮[G - m_1] G)_{ab}`, `G = (H_t - z_{1,t})⁻¹`: no propagator, no scalar.
-/
theorem evol_iso_one (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {P : PsiData (p.n * p.W)} (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W)
    (σ : Fin 1 → Bool) (a b : Fin (p.n * p.W)) (x : Fin 1 → Fin (p.n * p.W)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
        (driverAugmented (κ := Fin (ringDim p)) μ)
        (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
          (isoSlots P.S x) (Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x 0).re)
        (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
          (Matrix.single b a 1) t (vsNoise p t ω))
        (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
          chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (Matrix.single b a 1) t (vsNoise p t ω)) ∧
      IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
        (driverAugmented (κ := Fin (ringDim p)) μ)
        (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
          (isoSlots P.S x) (-Complex.I • Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x 0).im)
        (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
          (-Complex.I • Matrix.single b a 1) t (vsNoise p t ω))
        (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
          chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (-Complex.I • Matrix.single b a 1) t (vsNoise p t ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ ω : RingSample p,
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
            (isoSlots P.S x) (Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x 0).re = (P.isoErr σ a b x t (vsBandFin p t ω)).re ∧
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
            (isoSlots P.S x) (-Complex.I • Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x 0).im = (P.isoErr σ a b x t (vsBandFin p t ω)).im ∧
        chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (Matrix.single b a 1) t (vsNoise p t ω) =
          ((slotsH P.z σ t (vsBandFin p t ω) 0 * bandSelfEnergy P.S
            (slotsH P.z σ t (vsBandFin p t ω) 0 - VS.patConj (σ 0) (semicircleM P.z) • 1) *
              slotsH P.z σ t (vsBandFin p t ω) 0) a b).re ∧
        chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (-Complex.I • Matrix.single b a 1) t (vsNoise p t ω) =
          ((slotsH P.z σ t (vsBandFin p t ω) 0 * bandSelfEnergy P.S
            (slotsH P.z σ t (vsBandFin p t ω) 0 - VS.patConj (σ 0) (semicircleM P.z) • 1) *
              slotsH P.z σ t (vsBandFin p t ω) 0) a b).im := by
  have hm := semicircleM_im_pos hz
  have hconst : ∀ s, isoM P σ a b x s = isoM P σ a b x 0 := fun s => by
    simp [isoM, mChain_one]
  have hcsm : ∀ K : RingMat p, ∀ c : ℝ, IsContinuousSemimartingale (d := 1)
      (driverLaw (κ := Fin (ringDim p)) μ) (driverAugmented (κ := Fin (ringDim p)) μ)
      (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
        (isoSlots P.S x) K ((t : ℝ), vsNoise p t ω) - c)
      (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x) K t
        (vsNoise p t ω))
      (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
        chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x) K t
          (vsNoise p t ω)) := by
    intro K c
    have h := chain_sub_ito μ hz hm σ (isoSlots P.S x) K (F := fun _ => c) (F' := fun _ => 0)
      (fun s _ => hasDerivAt_const s c) continuousOn_const
    simp only [frozenDeriv_zero, sub_zero] at h
    exact h
  refine ⟨hcsm _ _, hcsm _ _, fun t ht ω => ?_⟩
  have hval : ∀ K, chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
      (isoSlots P.S x) K ((t : ℝ), vsNoise p t ω) =
        reTr K (gChain (patZ P.z σ t) (isoSlots P.S x) (vsBandFin p t ω)) :=
    fun K => chainTestT_eq_reTr_gChain hz σ _ K ht _
  have hdr : ∀ K, chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x) K t
      (vsNoise p t ω) = reTr K (dGmat P.S P.z σ (isoSlots P.S x) t (vsBandFin p t ω)) := by
    intro K
    rw [hPS]
    exact chainDrift_eq_reTr_dGmat hz σ _ K ht _
  rw [hval, hval, hdr, hdr, dGmat_one, ← hconst t, reTr_single, reTr_single,
    reTr_negI_single_eq, reTr_negI_single_eq]
  refine ⟨?_, ?_, rfl, rfl⟩ <;> simp [PsiData.isoErr, isoM]

end BlockBand.Native.ErdosRiabov.Evol

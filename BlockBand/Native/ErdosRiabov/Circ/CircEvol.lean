module

public import BlockBand.Native.ErdosRiabov.Circ.Duhamel
public import BlockBand.Native.ErdosRiabov.Prop.Bridge
public import BlockBand.Native.ErdosRiabov.Psi.Zero

/-!
# Equation for regularized chains

The Duhamel equation of the regularized saturated averaged chains, for short and long chains.

Setting: `Im P.z > 0`, `P.S = shortRingProfile p.b p.n p.W`, a pattern `σ`
with no non-saturated factor (`¬ HasDesatFactor σ`: `σ_{j+1} ≠ σ_j` cyclically, the saturated
alternating chains of ER §6), the path `H_r = vsBandFin p r⁺ ω`, `𝒳_r(x) = 𝒳^k_r(x)(H_r)`
(`P.avErr`), `𝓕^av_r` = `Evol.forcingAv`, `m = semicircleM P.z`, `T̂_s = vsKernel S m m̄ s`,
`P̂^{⊗k}_{s,t} = goodProp S z (fun _ => .sat) s t`, and `𝓜_r(x)` the chain martingale part
(`VS.chainMg`, `K = 1`). Coordinates are 0-based.

* `T̂^{⊕k}` is the Duhamel generator of the saturated chains (`circ_vsTensorGen_muAv`).
* Short chains `k = n+2`: `𝒰_t = Θ̊^{(k)}_t = ringOp … (Fin.last (n+1)) ⟨n⟩` (ring on `x_k`,
  anchor `x_{k-1}`), `F̃_s = extraForcingShort`.
  Long chains `k = n+4`: `𝒰_t = Θ̊^{(k-2)}_t Θ̊^{(k)}_t` (rings on `x_{k-2}` and `x_k`, anchors
  `x_{k-3}`, `x_{k-1}`), `F̃_s = extraForcingLong` (both lines).
* **`circEvol_short`, `circEvol_long`** (every sample, every `t ∈ [0,1]`):
  `𝒰_t[𝒳_t] = P̂^{⊗k}_{0,t} 𝒰_t[𝒳_0] + ∫_0^t P̂^{⊗k}_{s,t} 𝒰_t[𝓕^av_s + F̃_s] ds +
  propagatedNoise P̂^{⊗k} T̂^{⊕k} (𝒰_t 𝓜) 0 t`; the scalar factor is `1` (ER: `e^{k(s-t)/2}`).
* **`circEvol_short_combMg`, `circEvol_long_combMg`** (`∀ᵐ ω`, every `t ≤ 1`, every `u`; with
  `hZ` the initial term is dropped): `𝒰_t[𝒳_t](u) = ∫_0^t (P̂^{⊗k}_{s,t} 𝒰_t[𝓕^av_s + F̃_s])(u) ds
  + combMg 0 … (fun α s => (P̂^{⊗k}_{s,t} 𝒰_t)(u, α)) t`, i.e.
  `𝒵_t = ∫_0^t P̂^{⊗k}_{s,t} ∘ 𝒰_t [d𝓜_s + (𝓕 + F̃)_s ds]`; `𝒰_t` as a matrix is `circShortMat`,
  `circLongMat`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.SourceProcess.FiniteDriverIntegration
open ERNative.BlockBand.GaussianRing.ERZigStoppedDuhamel (propagatedNoise)
open scoped NNReal ComplexConjugate

/-!
### The saturated kernel
-/

section Kernel

variable {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}

theorem circ_norm_smul_lt_one (hz : z.im ≠ 0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖(s : ℂ) * (semicircleM z * conj (semicircleM z))‖ < 1 :=
  norm_smul_lt_one (norm_semicircleM_lt_one hz)
    (by rw [Complex.norm_conj]; exact norm_semicircleM_lt_one hz) hs.1 hs.2

theorem circ_kernel_symm (hS : StochasticSymm S) (hz : z.im ≠ 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (u v : Fin N) :
    vsKernel S (semicircleM z) (conj (semicircleM z)) s u v =
      vsKernel S (semicircleM z) (conj (semicircleM z)) s v u :=
  vsKernel_symm hS (circ_norm_smul_lt_one hz hs) u v

theorem circ_kernel_rowSum (hS : StochasticSymm S) (hz : z.im ≠ 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (u : Fin N) :
    ∑ v, vsKernel S (semicircleM z) (conj (semicircleM z)) s u v =
      (semicircleM z * conj (semicircleM z)) /
        (1 - (s : ℂ) * (semicircleM z * conj (semicircleM z))) :=
  vsKernel_rowSum hS (circ_norm_smul_lt_one hz hs) u

theorem circ_kernel_commute (hS : StochasticSymm S) (hz : z.im ≠ 0) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    Commute (vsKernel S (semicircleM z) (conj (semicircleM z)) t)
      (vsKernel S (semicircleM z) (conj (semicircleM z)) s) :=
  commute_vsKernel_of_commute hS (commute_cMat_vsKernel hS (circ_norm_smul_lt_one hz ht)).symm
    (circ_norm_smul_lt_one hz hs)

end Kernel

/-!
### Operators as matrices
-/

section Mat

variable {N k : ℕ}

theorem circ_propOp_toMatrix' (L : Module.End ℂ (CircFun N k)) (f : CircFun N k) :
    propOp (LinearMap.toMatrix' L) f = L f := by
  funext a
  rw [propOp_apply, ← LinearMap.toMatrix'_mulVec L f]
  rfl

/-- `T̂^{⊕k}_s` as an operator: the saturated tensor generator acts as `circGen T̂_s`. -/
theorem circ_propOp_gen_sat (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (s : ℝ)
    (f : CircFun N k) :
    propOp (vsTensorGen S (fun _ => semicircleM z) (fun _ => conj (semicircleM z)) s) f =
      circGen (vsKernel S (semicircleM z) (conj (semicircleM z)) s) f := by
  funext x
  rw [propOp_vsTensorGen_apply, circGen, LinearMap.sum_apply, Finset.sum_apply]
  rfl

/-- `𝒰_t = Θ̊^{(k)}_t` (`k = n+2`) as a matrix on site vectors. -/
def circShortMat {n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) :
    Matrix (Fin (n + 2) → Fin N) (Fin (n + 2) → Fin N) ℂ :=
  LinearMap.toMatrix' (circRing (Fin.last (n + 1)) ⟨n, by omega⟩
    (vsKernel S (semicircleM z) (conj (semicircleM z)) t))

/-- `𝒰_t = Θ̊^{(k-2)}_t Θ̊^{(k)}_t` (`k = n+4`) as a matrix on site vectors. -/
def circLongMat {n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) :
    Matrix (Fin (n + 2 + 2) → Fin N) (Fin (n + 2 + 2) → Fin N) ℂ :=
  LinearMap.toMatrix' (circRing ⟨n + 1, by omega⟩ ⟨n, by omega⟩
      (vsKernel S (semicircleM z) (conj (semicircleM z)) t) *
    circRing (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
      (vsKernel S (semicircleM z) (conj (semicircleM z)) t))

theorem propOp_circShortMat {n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ)
    (f : CircFun N (n + 2)) :
    propOp (circShortMat S z t) f = ringOp S z t (Fin.last (n + 1)) ⟨n, by omega⟩ f := by
  rw [circShortMat, circ_propOp_toMatrix', ringOp_eq_circRing]
  exact Fin.ne_of_lt (by simp [Fin.lt_def])

theorem propOp_circLongMat {n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ)
    (f : CircFun N (n + 2 + 2)) :
    propOp (circLongMat S z t) f = ringOp S z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
      (ringOp S z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩ f) := by
  rw [circLongMat, circ_propOp_toMatrix', ringOp_eq_circRing, ringOp_eq_circRing]
  · rfl
  · exact Fin.ne_of_lt (by simp [Fin.lt_def])
  · exact Fin.ne_of_lt (by simp [Fin.lt_def])

/-- **The extra forcing of short chains** (`k = n+2`, with `T̂_s`):
`F̃_s[f](x) = T̂_s(x_{k-1}, x_k) (𝒯_k[f](x'', x_k) + 𝒯_k[f](x'))`. -/
def extraForcingShort {n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (s : ℝ)
    (f : CircFun N (n + 2)) : CircFun N (n + 2) :=
  circExtra (vsKernel S (semicircleM z) (conj (semicircleM z)) s) ⟨n, by omega⟩
    (Fin.last (n + 1)) f

/-- **The extra forcing of long chains** (`k = n+4`, with `T̂_s`): the
pair `(x_{k-3}, x_{k-2})` term plus the pair `(x_{k-1}, x_k)` term. -/
def extraForcingLong {n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (s : ℝ)
    (f : CircFun N (n + 2 + 2)) : CircFun N (n + 2 + 2) :=
  circExtra (vsKernel S (semicircleM z) (conj (semicircleM z)) s) ⟨n, by omega⟩
      ⟨n + 1, by omega⟩ f +
    circExtra (vsKernel S (semicircleM z) (conj (semicircleM z)) s) ⟨n + 2, by omega⟩
      (Fin.last (n + 2 + 1)) f

end Mat

/-!
### The commutator for the two regularizers
-/

section Comm

variable {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}

theorem circShortMat_commutator (hS : StochasticSymm S) (hz : z.im ≠ 0) {n : ℕ} {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (f : CircFun N (n + 2)) :
    propOp (circShortMat S z t)
        (propOp (vsTensorGen S (fun _ => semicircleM z) (fun _ => conj (semicircleM z)) s) f) =
      propOp (vsTensorGen S (fun _ => semicircleM z) (fun _ => conj (semicircleM z)) s)
          (propOp (circShortMat S z t) f) +
        propOp (circShortMat S z t) (extraForcingShort S z s f) := by
  simp only [circ_propOp_gen_sat, circShortMat, circ_propOp_toMatrix', extraForcingShort]
  have h := circRing_mul_circGen (circ_kernel_commute hS hz hs ht)
    (circ_kernel_symm hS hz hs) (circ_kernel_rowSum hS hz hs)
    (j := Fin.last (n + 1)) (a := ⟨n, by omega⟩) (Fin.ne_of_lt (by simp [Fin.lt_def]))
  have h' := congrArg (fun L : Module.End ℂ (CircFun N (n + 2)) => L f) h
  simpa only [Module.End.mul_apply, LinearMap.add_apply] using h'

theorem circLongMat_commutator (hS : StochasticSymm S) (hz : z.im ≠ 0) {n : ℕ} {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (f : CircFun N (n + 2 + 2)) :
    propOp (circLongMat S z t)
        (propOp (vsTensorGen S (fun _ => semicircleM z) (fun _ => conj (semicircleM z)) s) f) =
      propOp (vsTensorGen S (fun _ => semicircleM z) (fun _ => conj (semicircleM z)) s)
          (propOp (circLongMat S z t) f) +
        propOp (circLongMat S z t) (extraForcingLong S z s f) := by
  simp only [circ_propOp_gen_sat, circLongMat, circ_propOp_toMatrix', extraForcingLong]
  have h := circRing2_mul_circGen (circ_kernel_commute hS hz hs ht)
    (circ_kernel_symm hS hz hs) (circ_kernel_rowSum hS hz hs)
    (a₁ := ⟨n, by omega⟩) (j₁ := ⟨n + 1, by omega⟩) (a₂ := ⟨n + 2, by omega⟩)
    (j₂ := Fin.last (n + 2 + 1)) (Fin.ne_of_lt (by simp [Fin.lt_def]))
    (Fin.ne_of_lt (by simp [Fin.lt_def])) (Fin.ne_of_gt (by simp [Fin.lt_def]))
    (Fin.ne_of_gt (by simp [Fin.lt_def])) (Fin.ne_of_gt (by simp [Fin.lt_def]))
    (Fin.ne_of_gt (by simp [Fin.lt_def]))
  have h' := congrArg (fun L : Module.End ℂ (CircFun N (n + 2 + 2)) => L f) h
  simpa only [Module.End.mul_apply, LinearMap.add_apply] using h'

end Comm

/-!
### The saturated averaged chains
-/

variable {p : BlockBand.Parameters} {P : PsiData (p.n * p.W)}

theorem circ_vsTensorGen_muAv {k : ℕ} (σ : Fin k → Bool) (hσ : ¬ HasDesatFactor σ) (s : ℝ) :
    vsTensorGen P.S (muAv P σ) (muNext P σ) s =
      vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s := by
  unfold vsTensorGen
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : σ i ≠ patNext σ i := fun h => hσ ⟨i, h⟩
  rw [muAv_apply, muNext_apply]
  congr 2
  cases h1 : σ i <;> cases h2 : patNext σ i
  · exact absurd (h1.trans h2.symm) hne
  · rfl
  · simp only [VS.patConj, ite_true, Bool.false_eq_true, ite_false]
    rw [vsKernel_swap]
  · exact absurd (h1.trans h2.symm) hne

theorem circ_goodProp_sat {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (s t : ℝ) :
    goodProp S z (fun _ : Fin k => .sat) s t =
      vsTensorProp S (fun _ => semicircleM z) (fun _ => conj (semicircleM z)) s t := rfl

/-- The hypotheses of `duhamel_frozen` for the saturated averaged chains. -/
theorem circ_hF (hz : 0 < P.z.im) {k : ℕ} (σ : Fin k → Bool) (hσ : ¬ HasDesatFactor σ)
    (ω : RingSample p) (r : ℝ) (x : Sites p k) :
    propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) r)
        (fun y => cVal P σ (avSlots P.S y) 1 ω r - avM P σ y r) x +
      forcingAv P σ x r (pathH p ω r) =
        cDrift P σ (avSlots P.S x) 1 ω r - dMav P σ x r := by
  have _ := hz
  simp only [cVal_av]
  rw [← circ_vsTensorGen_muAv σ hσ, ← aTermAv_eq_propOp, aTermAv_add_forcingAv, dGav, cDrift,
    Matrix.one_mul]

/-- **Duhamel form of the circular part, short chains**, from `Split.DerivStatement` (`hD`,
proved as `MTerms.deriv_holds`). For every sample `ω` and every `t ∈ [0,1]`:
`Θ̊^{(k)}_t[𝒳_t] = P̂^{⊗k}_{0,t} Θ̊^{(k)}_t[𝒳_0] + ∫_0^t P̂^{⊗k}_{s,t} Θ̊^{(k)}_t[𝓕^av_s + F̃_s] ds
+ propagatedNoise P̂^{⊗k} T̂^{⊕k} (Θ̊^{(k)}_t 𝓜) 0 t`, `F̃ = extraForcingShort`.
-/
theorem circEvol_short (hD : Split.DerivStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (hσ : ¬ HasDesatFactor σ) (ω : RingSample p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ringOp P.S P.z t (Fin.last (n + 1)) ⟨n, by omega⟩ (fun x => P.avErr σ x t (pathH p ω t)) =
      propOp (goodProp P.S P.z (fun _ => .sat) 0 t)
          (ringOp P.S P.z t (Fin.last (n + 1)) ⟨n, by omega⟩
            (fun x => P.avErr σ x 0 (pathH p ω 0))) +
        (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (fun _ => .sat) s t)
          (ringOp P.S P.z t (Fin.last (n + 1)) ⟨n, by omega⟩
            ((fun x => forcingAv P σ x s (pathH p ω s)) +
              extraForcingShort P.S P.z s (fun y => P.avErr σ y s (pathH p ω s))))) +
        propagatedNoise (fun s t => propOp (goodProp P.S P.z (fun _ => .sat) s t))
          (fun s => propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
            (fun _ => conj (semicircleM P.z)) s))
          (fun r => propOp (circShortMat P.S P.z t)
            (fun x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x
              r.toNNReal ω)) 0 t := by
  have hS : StochasticSymm P.S := hPS ▸ stochasticSymm_ring p
  have hm : ‖semicircleM P.z‖ < 1 := norm_semicircleM_lt_one hz.ne'
  have hm' : ‖conj (semicircleM P.z)‖ < 1 := by rw [Complex.norm_conj]; exact hm
  have h := duhamel_frozen hz hPS σ (fun x => avSlots P.S x) (fun _ => 1) (avM P σ) (dMav P σ)
    (fun x s hs => hasDerivAt_avM P hD hz.ne' hS (by omega) σ x hs)
    (fun x => continuousOn_dMav P hz.ne' hS σ x) (μ := fun _ => semicircleM P.z)
    (μ' := fun _ => conj (semicircleM P.z)) (fun _ => hm) (fun _ => hm') ω
    (fun r x => forcingAv P σ x r (pathH p ω r))
    (fun r => extraForcingShort P.S P.z r (fun y => P.avErr σ y r (pathH p ω r)))
    (fun r _ x => circ_hF hz σ hσ ω r x) (circShortMat P.S P.z t) ?_ ht
  · simp only [cVal_av] at h
    simp only [propOp_circShortMat] at h ⊢
    exact h
  · intro r hr
    simp only [cVal_av]
    exact circShortMat_commutator hS hz.ne' hr ht _

/-- **Duhamel form of the circular part, long chains**, from `Split.DerivStatement` (`hD`,
proved as `MTerms.deriv_holds`). For every sample `ω` and every `t ∈ [0,1]`, with
`𝒰_t = Θ̊^{(k-2)}_t Θ̊^{(k)}_t`:
`𝒰_t[𝒳_t] = P̂^{⊗k}_{0,t} 𝒰_t[𝒳_0] + ∫_0^t P̂^{⊗k}_{s,t} 𝒰_t[𝓕^av_s + F̃_s] ds
+ propagatedNoise P̂^{⊗k} T̂^{⊕k} (𝒰_t 𝓜) 0 t`, `F̃ = extraForcingLong`.
-/
theorem circEvol_long (hD : Split.DerivStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) (ω : RingSample p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ringOp P.S P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
        (ringOp P.S P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
          (fun x => P.avErr σ x t (pathH p ω t))) =
      propOp (goodProp P.S P.z (fun _ => .sat) 0 t)
          (ringOp P.S P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
            (ringOp P.S P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
              (fun x => P.avErr σ x 0 (pathH p ω 0)))) +
        (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (fun _ => .sat) s t)
          (ringOp P.S P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
            (ringOp P.S P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
              ((fun x => forcingAv P σ x s (pathH p ω s)) +
                extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p ω s)))))) +
        propagatedNoise (fun s t => propOp (goodProp P.S P.z (fun _ => .sat) s t))
          (fun s => propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
            (fun _ => conj (semicircleM P.z)) s))
          (fun r => propOp (circLongMat P.S P.z t)
            (fun x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x
              r.toNNReal ω)) 0 t := by
  have hS : StochasticSymm P.S := hPS ▸ stochasticSymm_ring p
  have hm : ‖semicircleM P.z‖ < 1 := norm_semicircleM_lt_one hz.ne'
  have hm' : ‖conj (semicircleM P.z)‖ < 1 := by rw [Complex.norm_conj]; exact hm
  have h := duhamel_frozen hz hPS σ (fun x => avSlots P.S x) (fun _ => 1) (avM P σ) (dMav P σ)
    (fun x s hs => hasDerivAt_avM P hD hz.ne' hS (by omega) σ x hs)
    (fun x => continuousOn_dMav P hz.ne' hS σ x) (μ := fun _ => semicircleM P.z)
    (μ' := fun _ => conj (semicircleM P.z)) (fun _ => hm) (fun _ => hm') ω
    (fun r x => forcingAv P σ x r (pathH p ω r))
    (fun r => extraForcingLong P.S P.z r (fun y => P.avErr σ y r (pathH p ω r)))
    (fun r _ x => circ_hF hz σ hσ ω r x) (circLongMat P.S P.z t) ?_ ht
  · simp only [cVal_av] at h
    simp only [propOp_circLongMat] at h ⊢
    exact h
  · intro r hr
    simp only [cVal_av]
    exact circLongMat_commutator hS hz.ne' hr ht _

/-!
### Zero initial state and the `combMg` form
-/

/-- From `Split.ZeroStatement`: the averaged errors vanish at time `0` along the path. -/
theorem circ_avErr_pathH_zero (hZ : Split.ZeroStatement) {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool)
    (ω : RingSample p) : (fun x => P.avErr σ x 0 (pathH p ω 0)) = 0 := by
  funext x
  rw [pathH, Real.toNNReal_zero, vsBandFin_zero]
  exact P.avErr_zero hZ hk σ x

theorem circ_ringOp_zero {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) (j a : Fin k) :
    ringOp S z t j a 0 = 0 := by
  funext x
  simp [ringOp]

/-- **The circular part of short chains in `combMg` form**, from `Split.DerivStatement` and
`Split.ZeroStatement` (`hD`, `hZ`; proved as `MTerms.deriv_holds`, `MTerms.zero_holds`).
Almost surely, for every `t ∈ [0,1]` and every site vector `u`:
`Θ̊^{(k)}_t[𝒳_t](u) = (∫_0^t P̂^{⊗k}_{s,t} Θ̊^{(k)}_t[𝓕^av_s + F̃_s] ds)(u) + combMg 0 … c t`
with `c_α(s) = (P̂^{⊗k}_{s,t} 𝒰_t)(u, α)`, `𝒰_t = circShortMat`, i.e.
`𝒵_t = ∫_0^t P̂^{⊗k}_{s,t} ∘ 𝒰_t [d𝓜_s + (𝓕^av_s + F̃_s) ds]`.
-/
theorem circEvol_short_combMg (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hD : Split.DerivStatement) (hZ : Split.ZeroStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
      ∀ u : Sites p (n + 2),
        ringOp P.S P.z t (Fin.last (n + 1)) ⟨n, by omega⟩
            (fun x => P.avErr σ x t (pathH p ω t)) u =
          (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (fun _ => .sat) s t)
            (ringOp P.S P.z t (Fin.last (n + 1)) ⟨n, by omega⟩
              ((fun x => forcingAv P σ x s (pathH p ω s)) +
                extraForcingShort P.S P.z s (fun y => P.avErr σ y s (pathH p ω s))))) u +
          combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
            (fun α s => ((goodProp P.S P.z (fun _ => .sat) s t * circShortMat P.S P.z t :
              Matrix (Sites p (n + 2)) (Sites p (n + 2)) ℂ)) u α)
            t ω := by
  have hm : ‖semicircleM P.z‖ < 1 := norm_semicircleM_lt_one hz.ne'
  have hm' : ‖conj (semicircleM P.z)‖ < 1 := by rw [Complex.norm_conj]; exact hm
  filter_upwards [frozenNoise_eq_combMg μ₀ hz hPS σ (fun x => avSlots P.S x) (fun _ => 1)
    (μ := fun _ => semicircleM P.z) (μ' := fun _ => conj (semicircleM P.z)) (fun _ => hm)
    (fun _ => hm') (fun t => circShortMat P.S P.z t)] with ω hω t ht u
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨t.2, ht⟩
  rw [circEvol_short hD hz hPS σ hσ ω ht', circ_avErr_pathH_zero hZ (by omega) σ ω,
    circ_ringOp_zero, map_zero, zero_add, Pi.add_apply]
  congr 1
  exact hω t ht u

/-- **The circular part of long chains in `combMg` form**, from `Split.DerivStatement` and
`Split.ZeroStatement` (`hD`, `hZ`; proved as `MTerms.deriv_holds`, `MTerms.zero_holds`).
Almost surely, for every `t ∈ [0,1]` and every `u`:
`𝒰_t[𝒳_t](u) = (∫_0^t P̂^{⊗k}_{s,t} 𝒰_t[𝓕^av_s + F̃_s] ds)(u) + combMg 0 … c t`,
`c_α(s) = (P̂^{⊗k}_{s,t} 𝒰_t)(u, α)`.
-/
theorem circEvol_long_combMg (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hD : Split.DerivStatement) (hZ : Split.ZeroStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
      ∀ u : Sites p (n + 2 + 2),
        ringOp P.S P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
            (ringOp P.S P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
              (fun x => P.avErr σ x t (pathH p ω t))) u =
          (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (fun _ => .sat) s t)
            (ringOp P.S P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
              (ringOp P.S P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
                ((fun x => forcingAv P σ x s (pathH p ω s)) +
                  extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p ω s)))))) u +
          combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
            (fun α s => ((goodProp P.S P.z (fun _ => .sat) s t * circLongMat P.S P.z t :
              Matrix (Sites p (n + 2 + 2)) (Sites p (n + 2 + 2)) ℂ)) u α)
            t ω := by
  have hm : ‖semicircleM P.z‖ < 1 := norm_semicircleM_lt_one hz.ne'
  have hm' : ‖conj (semicircleM P.z)‖ < 1 := by rw [Complex.norm_conj]; exact hm
  filter_upwards [frozenNoise_eq_combMg μ₀ hz hPS σ (fun x => avSlots P.S x) (fun _ => 1)
    (μ := fun _ => semicircleM P.z) (μ' := fun _ => conj (semicircleM P.z)) (fun _ => hm)
    (fun _ => hm') (fun t => circLongMat P.S P.z t)] with ω hω t ht u
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨t.2, ht⟩
  rw [circEvol_long hD hz hPS σ hσ ω ht', circ_avErr_pathH_zero hZ (by omega) σ ω, circ_ringOp_zero,
    circ_ringOp_zero, map_zero, zero_add, Pi.add_apply]
  congr 1
  exact hω t ht u

end BlockBand.Native.ErdosRiabov.Circ

module

public import BlockBand.Native.ErdosRiabov.Circ.CircEvol

/-!
# The long linear term: Duhamel form of `T̂^{(k)}_t[𝒳^k]`

Setting of the regularized chain equation for long chains `k = n+4` (0-based sites, a saturated
pattern
`σ`, `¬ HasDesatFactor σ`), `m = semicircleM P.z`, `T̂_s = vsKernel S m m̄ s`. ER separates the
generator term on the coordinate `x_{k-2}` (0-based `⟨n+1⟩`) as a forcing; the remaining
generator is `⊕_{i ≠ k-2} T̂_s^{(i)}` with propagator `P̃^k_{s,t} = ⊗_{i ≠ k-2} P̂^{(i)}_{s,t}`
(identity factor at `k-2`):

* `linFactor n`: the factor list (`.ident` at `⟨n+1⟩`, `.sat` elsewhere); `P̃ = goodProp S z
  (linFactor n)`; its generator is `vsTensorGen S μ μ'` with the weights of `linFactor n`.
* `circLinMat S z t`: `V = T̂^{(k)}_t` (the kernel `T̂_t` on the last coordinate) as a matrix.
* **`linTerm_evol`** (every sample, every `t ∈ [0,1]`; `Circ.duhamel_frozen` with `F̃ = 0`,
  since `T̂^{(k)}_t` commutes with every slot of the generator):
  `T̂^{(k)}_t[𝒳_t] = P̃_{0,t} T̂^{(k)}_t[𝒳_0]`
  `+ ∫_0^t P̃_{s,t} T̂^{(k)}_t[𝓕^av_s + T̂^{(k-2)}_s 𝒳_s] ds`
  `+ propagatedNoise P̃ (gen) (T̂^{(k)}_t 𝓜) 0 t`. This is the Erdős–Riabov equation for the
  long linear term with scalar `1`; their second line
  `P̂^{(k)}_{s,t} P̃_{s,t} Θ^{(k-2)}_s Θ^{(k)}_s 𝒳_s` equals
  `P̃_{s,t} T̂^{(k)}_t T̂^{(k-2)}_s 𝒳_s` (`P̂^{(k)}_{s,t} T̂_s = T̂_t`; here obtained directly).
* **`linTerm_evol_combMg`** (with `hZ`; a.s., every `t ≤ 1`, every `u`): the same with the
  initial term dropped and the noise `combMg 0 … (fun α s => (P̃_{s,t} T̂^{(k)}_t)(u, α)) t`
  (`V_t(s) = P̃^k_{s,t} T̂^{(k)}_t`).
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
### The factors and the generator
-/

/-- The factors of `P̃^k = ⊗_{i ≠ k-2} P̂^{(i)}` (`k = n+4`): `.ident` at `⟨n+1⟩`. -/
def linFactor (n : ℕ) : Fin (n + 2 + 2) → PropFactor :=
  fun i => if i = ⟨n + 1, by omega⟩ then .ident else .sat

theorem circ_norm_mu1_lt_one {z : ℂ} (hz : z.im ≠ 0) (c : PropFactor) : ‖c.mu1 z‖ < 1 := by
  have h := norm_semicircleM_lt_one hz
  cases c <;> simp [PropFactor.mu1, h]

theorem circ_norm_mu2_lt_one {z : ℂ} (hz : z.im ≠ 0) (c : PropFactor) : ‖c.mu2 z‖ < 1 := by
  have h := norm_semicircleM_lt_one hz
  cases c <;> simp [PropFactor.mu2, h]

section Gen

variable {N : ℕ}

/-- The tensor generator acts as `Σ_i K_i^{(i)}`, `K_i = vsKernel S (μ i) (μ' i) s`. -/
theorem circ_propOp_tensorGen {k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : Fin k → ℂ) (s : ℝ)
    (f : CircFun N k) :
    propOp (vsTensorGen S μ μ' s) f = (∑ i, circSlot i (vsKernel S (μ i) (μ' i) s)) f := by
  funext x
  rw [propOp_vsTensorGen_apply, LinearMap.sum_apply, Finset.sum_apply]
  rfl

/-- `P̃`'s generator plus the separated slot `⟨n+1⟩` is `T̂_s^{⊕k}`. -/
theorem circ_linGen_add (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) {n : ℕ} (s : ℝ)
    (f : CircFun N (n + 2 + 2)) :
    propOp (vsTensorGen S (fun i => (linFactor n i).mu1 z) (fun i => (linFactor n i).mu2 z) s)
        f + circSlot ⟨n + 1, by omega⟩ (vsKernel S (semicircleM z) (conj (semicircleM z)) s) f =
      propOp (vsTensorGen S (fun _ => semicircleM z) (fun _ => conj (semicircleM z)) s) f := by
  rw [circ_propOp_tensorGen, circ_propOp_tensorGen]
  funext x
  simp only [Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply]
  have hmem : (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) ∈ Finset.univ := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  have h0 : circSlot (⟨n + 1, by omega⟩ : Fin (n + 2 + 2))
      (vsKernel S ((linFactor n ⟨n + 1, by omega⟩).mu1 z)
        ((linFactor n ⟨n + 1, by omega⟩).mu2 z) s) f x = 0 := by
    simp [linFactor, PropFactor.mu1, Evol.vsKernel_zero_left, circSlot_apply]
  have hrest : ∑ i ∈ Finset.univ.erase (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)),
      circSlot i (vsKernel S ((linFactor n i).mu1 z) ((linFactor n i).mu2 z) s) f x =
      ∑ i ∈ Finset.univ.erase (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)),
        circSlot i (vsKernel S (semicircleM z) (conj (semicircleM z)) s) f x := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne := Finset.ne_of_mem_erase hi
    simp only [linFactor, hne, ite_false, PropFactor.mu1, PropFactor.mu2]
  rw [h0, hrest]
  ring

end Gen

/-!
### The fixed-time regularizer `T̂^{(k)}_t`
-/

section Mat

variable {N : ℕ}

/-- `V = T̂^{(k)}_t` (kernel `T̂_t` on the last coordinate, `k = n+4`) as a matrix. -/
def circLinMat {n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) :
    Matrix (Fin (n + 2 + 2) → Fin N) (Fin (n + 2 + 2) → Fin N) ℂ :=
  LinearMap.toMatrix' (circSlot (Fin.last (n + 2 + 1))
    (vsKernel S (semicircleM z) (conj (semicircleM z)) t))

theorem propOp_circLinMat {n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ)
    (f : CircFun N (n + 2 + 2)) :
    propOp (circLinMat S z t) f =
      circSlot (Fin.last (n + 2 + 1)) (vsKernel S (semicircleM z) (conj (semicircleM z)) t) f :=
  circ_propOp_toMatrix' _ f

/-- `T̂^{(k)}_t` commutes with every tensor generator of the profile `S`. -/
theorem circLinMat_commute {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) {z : ℂ}
    (hz : z.im ≠ 0) {n : ℕ} {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    {μ μ' : Fin (n + 2 + 2) → ℂ} (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1)
    (f : CircFun N (n + 2 + 2)) :
    propOp (circLinMat S z t) (propOp (vsTensorGen S μ μ' s) f) =
      propOp (vsTensorGen S μ μ' s) (propOp (circLinMat S z t) f) := by
  simp only [propOp_circLinMat, circ_propOp_tensorGen]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : Fin.last (n + 2 + 1) = i
  · subst hi
    have hT : Commute (vsKernel S (semicircleM z) (conj (semicircleM z)) t) (cMat S) :=
      (commute_cMat_vsKernel hS (circ_norm_smul_lt_one hz ht)).symm
    exact circSlot_comm_same _ (commute_vsKernel_of_commute hS hT
      (norm_smul_lt_one (hμ _) (hμ' _) hs.1 hs.2))
  · exact circSlot_comm hi _ _

end Mat

variable {p : BlockBand.Parameters} {P : PsiData (p.n * p.W)}

/-- **Duhamel form of the long linear term**, under the hypothesis `Split.DerivStatement`
(`hD`, proved as `MTerms.deriv_holds`). For a saturated pattern of length `k = n+4`,
every sample `ω` and every `t ∈ [0,1]`:
`T̂^{(k)}_t[𝒳_t] = P̃_{0,t} T̂^{(k)}_t[𝒳_0]`
`+ ∫_0^t P̃_{s,t} T̂^{(k)}_t[𝓕^av_s + T̂^{(k-2)}_s 𝒳_s] ds`
`+ propagatedNoise P̃ (gen P̃) (T̂^{(k)}_t 𝓜) 0 t`, `P̃ = goodProp S z (linFactor n)`.
-/
theorem linTerm_evol (hD : Split.DerivStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) (ω : RingSample p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    circSlot (Fin.last (n + 2 + 1)) (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t)
        (fun x => P.avErr σ x t (pathH p ω t)) =
      propOp (goodProp P.S P.z (linFactor n) 0 t)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t)
            (fun x => P.avErr σ x 0 (pathH p ω 0))) +
        (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (linFactor n) s t)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t)
            ((fun x => forcingAv P σ x s (pathH p ω s)) +
              circSlot ⟨n + 1, by omega⟩
                (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
                (fun y => P.avErr σ y s (pathH p ω s))))) +
        propagatedNoise (fun s t => propOp (goodProp P.S P.z (linFactor n) s t))
          (fun s => propOp (vsTensorGen P.S (fun i => (linFactor n i).mu1 P.z)
            (fun i => (linFactor n i).mu2 P.z) s))
          (fun r => propOp (circLinMat P.S P.z t)
            (fun x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x
              r.toNNReal ω)) 0 t := by
  have hS : StochasticSymm P.S := hPS ▸ stochasticSymm_ring p
  have hμ := fun j => circ_norm_mu1_lt_one hz.ne' (linFactor n j)
  have hμ' := fun j => circ_norm_mu2_lt_one hz.ne' (linFactor n j)
  have h := duhamel_frozen hz hPS σ (fun x => avSlots P.S x) (fun _ => 1) (avM P σ) (dMav P σ)
    (fun x s hs => hasDerivAt_avM P hD hz.ne' hS (by omega) σ x hs)
    (fun x => continuousOn_dMav P hz.ne' hS σ x) hμ hμ' ω
    (fun r => (fun x => forcingAv P σ x r (pathH p ω r)) +
      circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) r)
        (fun y => P.avErr σ y r (pathH p ω r)))
    (fun _ => 0) ?_ (circLinMat P.S P.z t) ?_ ht
  · simp only [cVal_av, add_zero] at h
    simp only [propOp_circLinMat] at h ⊢
    exact h
  · intro r _ x
    have e := congrFun (circ_linGen_add P.S P.z r
      (fun y => cVal P σ (avSlots P.S y) 1 ω r - avM P σ y r)) x
    have e2 := circ_hF hz σ hσ ω r x
    simp only [Pi.add_apply, cVal_av] at e e2 ⊢
    rw [← e] at e2
    rw [← e2]
    ring
  · intro r hr
    simp only [map_zero, add_zero]
    exact circLinMat_commute hS hz.ne' hr ht hμ hμ' _

/-- **The long linear term in `combMg` form**, under the hypotheses `Split.DerivStatement` and
`Split.ZeroStatement` (proved as `MTerms.deriv_holds`, `MTerms.zero_holds`). Almost surely,
for every `t ∈ [0,1]` and every `u`:
`T̂^{(k)}_t[𝒳_t](u) = (∫_0^t P̃_{s,t} T̂^{(k)}_t[𝓕^av_s + T̂^{(k-2)}_s 𝒳_s] ds)(u)`
`+ combMg 0 … c t`,
`c_α(s) = (P̃_{s,t} T̂^{(k)}_t)(u, α)`.
-/
theorem linTerm_evol_combMg (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hD : Split.DerivStatement) (hZ : Split.ZeroStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
      ∀ u : Sites p (n + 2 + 2),
        circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t)
            (fun x => P.avErr σ x t (pathH p ω t)) u =
          (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (linFactor n) s t)
            (circSlot (Fin.last (n + 2 + 1))
              (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t)
              ((fun x => forcingAv P σ x s (pathH p ω s)) +
                circSlot ⟨n + 1, by omega⟩
                  (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
                  (fun y => P.avErr σ y s (pathH p ω s))))) u +
          combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
            (fun α s => ((goodProp P.S P.z (linFactor n) s t * circLinMat P.S P.z t :
              Matrix (Sites p (n + 2 + 2)) (Sites p (n + 2 + 2)) ℂ)) u α)
            t ω := by
  have hμ := fun j => circ_norm_mu1_lt_one hz.ne' (linFactor n j)
  have hμ' := fun j => circ_norm_mu2_lt_one hz.ne' (linFactor n j)
  filter_upwards [frozenNoise_eq_combMg μ₀ hz hPS σ (fun x => avSlots P.S x) (fun _ => 1)
    hμ hμ' (fun t => circLinMat P.S P.z t)] with ω hω t ht u
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨t.2, ht⟩
  rw [linTerm_evol hD hz hPS σ hσ ω ht', circ_avErr_pathH_zero hZ (by omega) σ ω, map_zero,
    map_zero, zero_add, Pi.add_apply]
  congr 1
  exact hω t ht u

end BlockBand.Native.ErdosRiabov.Circ

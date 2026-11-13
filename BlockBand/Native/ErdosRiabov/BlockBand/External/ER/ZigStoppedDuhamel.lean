module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pathwise Duhamel formula and stopped weighted closure for the ER zig master inequalities

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, Section 6.1 ("Completing the proof of master inequalities"), the
Duhamel representation

`𝒳_τ = e^{k(t₀-τ)/2} 𝒫̃_{t₀,τ}[𝒳_{t₀}] + ∫_{t₀}^τ e^{k(s-τ)/2} 𝒫̃_{s,τ}[d𝓜_s]
        + ∫_{t₀}^τ e^{k(s-τ)/2} 𝒫̃_{s,τ}[𝓕_s] ds`

of the averaged / isotropic evolution equation of Lemma 6.2,
`d𝒳_t = 𝒜_t[𝒳_t] dt + d𝓜_t + 𝓕_t dt`, and the way Lemmas 6.3 (propagator), 6.4
(martingale) and 6.5 (forcing) are combined there into the averaged master
inequality.

What is proved here, pathwise and without any stochastic calculus:

* `pathwise_duhamel` : if a continuous path `X` satisfies the *integral form* of the
  evolution equation, `X_r = X_{t₀} + ∫_{t₀}^r (𝒜_u X_u + 𝓕_u) du + (M_r - M_{t₀})` for a
  continuous path `M` (the martingale part), and `P(s,t)` is a propagator of `𝒜`
  (`∂_s P(s,t) = -P(s,t) 𝒜_s`, `P(t,t) = I`), then
  `X_t = P(t₀,t) X_{t₀} + ∫_{t₀}^t P(s,t) 𝓕_s ds + propagatedNoise`, where
  `propagatedNoise = (M_t - M_{t₀}) + ∫_{t₀}^t P(s,t) 𝒜_s (M_s - M_{t₀}) ds` is the
  integration-by-parts form of `∫_{t₀}^t P(s,t) dM_s`;
* `propagatedNoise_eq_integral` : for a `C¹` path `M` the propagated noise is exactly
  `∫_{t₀}^t P(s,t) M'_s ds`, which identifies it with the source's `∫ 𝒫̃_{s,t}[d𝓜_s]`
  (for a stochastic martingale this identification is the stochastic integration by
  parts with the deterministic `C¹` integrand `s ↦ P(s,t)`, which is not treated in this file);
* `weighted_duhamel_bound`, `stopped_weighted_duhamel_bound` : the consistency
  bookkeeping of the initial, martingale and forcing terms of that proof:
  from a propagator estimate of the form of Lemma 6.3 in a weight `𝔰` (the size
  function), an initial bound, a forcing bound valid only before the stopping time and
  a bound on the propagated noise, the entrywise bound
  `|X_t(x)| ≤ (Ψ₀ κ(t₀,t) + ∫_{t₀}^t f_s κ(s,t) ds + m_t) 𝔰_t(x)` holds for every
  `t ∈ [t₀, τ]`.

Normalization.  The state space is `ι → ℂ` with `ι` finite (source: functions of
`x ∈ [N]^k`, resp. `(a, x', b)`); operators are real-linear (complex-linear maps restrict).
The generator `𝒜` is the full linear part `k/2 + ⊕_j 𝒜_{j,t}` of the evolution equation, so
the source's `e^{k(s-t)/2} 𝒫̃_{s,t}` is the propagator `P(s,t)` here.  Quantifiers: one
fixed path; `t₀ ≤ t`; no limit.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERZigStoppedDuhamel

open Set MeasureTheory

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The integration-by-parts form of `∫_{t₀}^t P(s,t) dM_s`:
`(M_t - M_{t₀}) + ∫_{t₀}^t P(s,t) 𝒜_s (M_s - M_{t₀}) ds`. -/
def propagatedNoise (P : ℝ → ℝ → E →L[ℝ] E) (A : ℝ → E →L[ℝ] E) (M : ℝ → E)
    (t₀ t : ℝ) : E :=
  (M t - M t₀) + ∫ s in t₀..t, P s t (A s (M s - M t₀))

omit [CompleteSpace E] in
/-- Product rule for a propagated path: if `∂_s P(s,t) = -P(s,t) 𝒜_s` and `Z' = z'`,
then `d/ds [P(s,t) Z_s] = P(s,t) (z' - 𝒜_s Z_s)`. -/
theorem hasDerivAt_propagated {P : ℝ → ℝ → E →L[ℝ] E} {A : ℝ → E →L[ℝ] E}
    {Z : ℝ → E} {z' : E} {s t : ℝ}
    (hP : HasDerivAt (fun r => P r t) (-((P s t).comp (A s))) s) (hZ : HasDerivAt Z z' s) :
    HasDerivAt (fun r => P r t (Z r)) (P s t (z' - A s (Z s))) s := by
  have h := hP.clm_apply hZ
  convert h using 1
  simp only [map_sub, neg_apply, ContinuousLinearMap.comp_apply]
  abel

/-- **Pathwise Duhamel formula** (the deterministic content of the Duhamel representation). -/
theorem pathwise_duhamel {A : ℝ → E →L[ℝ] E} {P : ℝ → ℝ → E →L[ℝ] E} {X F M : ℝ → E}
    {t₀ t : ℝ} (hle : t₀ ≤ t)
    (hA : ContinuousOn A (Icc t₀ t)) (hX : ContinuousOn X (Icc t₀ t))
    (hF : ContinuousOn F (Icc t₀ t)) (hM : ContinuousOn M (Icc t₀ t))
    (hPc : ContinuousOn (fun s => P s t) (Icc t₀ t))
    (hPd : ∀ s ∈ Ioo t₀ t, HasDerivAt (fun r => P r t) (-((P s t).comp (A s))) s)
    (hPt : P t t = ContinuousLinearMap.id ℝ E)
    (hIto : ∀ r ∈ Icc t₀ t,
      X r = X t₀ + (∫ u in t₀..r, (A u (X u) + F u)) + (M r - M t₀)) :
    X t = P t₀ t (X t₀) + (∫ s in t₀..t, P s t (F s)) + propagatedNoise P A M t₀ t := by
  set g : ℝ → E := fun u => A u (X u) + F u with hgdef
  have hg : ContinuousOn g (Icc t₀ t) := (hA.clm_apply hX).add hF
  set Z : ℝ → E := fun r => X r - (M r - M t₀) with hZdef
  have hZeq : ∀ r ∈ Icc t₀ t, Z r = X t₀ + ∫ u in t₀..r, g u := by
    intro r hr
    simp only [hZdef]
    rw [hIto r hr]
    abel
  have hZd : ∀ r ∈ Ioo t₀ t, HasDerivAt Z (g r) r := by
    intro r hr
    have hii : IntervalIntegrable g volume t₀ r :=
      (hg.mono (Icc_subset_Icc le_rfl hr.2.le)).intervalIntegrable_of_Icc hr.1.le
    have hsm : StronglyMeasurableAtFilter g (nhds r) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hg.mono Ioo_subset_Icc_self) r hr
    have hca : ContinuousAt g r := hg.continuousAt (Icc_mem_nhds hr.1 hr.2)
    have h1 := (intervalIntegral.integral_hasDerivAt_right hii hsm hca).const_add (X t₀)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with y hy
    exact hZeq y (Ioo_subset_Icc_self hy)
  have hZc : ContinuousOn Z (Icc t₀ t) := hX.sub (hM.sub continuousOn_const)
  have hderiv : ∀ s ∈ Ioo t₀ t,
      HasDerivAt (fun r => P r t (Z r)) (P s t (F s + A s (M s - M t₀))) s := by
    intro s hs
    have h := hasDerivAt_propagated (hPd s hs) (hZd s hs)
    convert h using 2
    simp only [hgdef, hZdef, map_sub]
    abel
  have hc1 : ContinuousOn (fun s => P s t (F s)) (Icc t₀ t) := hPc.clm_apply hF
  have hc2 : ContinuousOn (fun s => P s t (A s (M s - M t₀))) (Icc t₀ t) :=
    hPc.clm_apply (hA.clm_apply (hM.sub continuousOn_const))
  have hint : IntervalIntegrable (fun s => P s t (F s + A s (M s - M t₀))) volume t₀ t :=
    (hPc.clm_apply (hF.add (hA.clm_apply (hM.sub continuousOn_const)))).intervalIntegrable_of_Icc
      hle
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle
    (hPc.clm_apply hZc) hderiv hint
  have hsplit : (∫ s in t₀..t, P s t (F s + A s (M s - M t₀))) =
      (∫ s in t₀..t, P s t (F s)) + ∫ s in t₀..t, P s t (A s (M s - M t₀)) := by
    rw [← intervalIntegral.integral_add (hc1.intervalIntegrable_of_Icc hle)
      (hc2.intervalIntegrable_of_Icc hle)]
    simp
  rw [hsplit, hPt] at hftc
  simp only [hZdef, ContinuousLinearMap.id_apply, sub_self, sub_zero] at hftc
  have hZt : X t - (M t - M t₀) = P t₀ t (X t₀) +
      ((∫ s in t₀..t, P s t (F s)) + ∫ s in t₀..t, P s t (A s (M s - M t₀))) := by
    rw [hftc]; abel
  rw [propagatedNoise]
  calc X t = (X t - (M t - M t₀)) + (M t - M t₀) := (sub_add_cancel _ _).symm
    _ = _ := by rw [hZt]; abel

/-- For a `C¹` path `M`, the propagated noise is the ordinary integral
`∫_{t₀}^t P(s,t) M'_s ds`; this is the Stieltjes form of `∫_{t₀}^t P(s,t) dM_s`. -/
theorem propagatedNoise_eq_integral {A : ℝ → E →L[ℝ] E} {P : ℝ → ℝ → E →L[ℝ] E}
    {M M' : ℝ → E} {t₀ t : ℝ} (hle : t₀ ≤ t)
    (hA : ContinuousOn A (Icc t₀ t)) (hM : ContinuousOn M (Icc t₀ t))
    (hM' : ContinuousOn M' (Icc t₀ t)) (hMd : ∀ s ∈ Ioo t₀ t, HasDerivAt M (M' s) s)
    (hPc : ContinuousOn (fun s => P s t) (Icc t₀ t))
    (hPd : ∀ s ∈ Ioo t₀ t, HasDerivAt (fun r => P r t) (-((P s t).comp (A s))) s)
    (hPt : P t t = ContinuousLinearMap.id ℝ E) :
    propagatedNoise P A M t₀ t = ∫ s in t₀..t, P s t (M' s) := by
  have hderiv : ∀ s ∈ Ioo t₀ t, HasDerivAt (fun r => P r t (M r - M t₀))
      (P s t (M' s - A s (M s - M t₀))) s := fun s hs =>
    hasDerivAt_propagated (hPd s hs) ((hMd s hs).sub_const (M t₀))
  have hc1 : ContinuousOn (fun s => P s t (M' s)) (Icc t₀ t) := hPc.clm_apply hM'
  have hc2 : ContinuousOn (fun s => P s t (A s (M s - M t₀))) (Icc t₀ t) :=
    hPc.clm_apply (hA.clm_apply (hM.sub continuousOn_const))
  have hint : IntervalIntegrable (fun s => P s t (M' s - A s (M s - M t₀))) volume t₀ t :=
    (hPc.clm_apply (hM'.sub (hA.clm_apply (hM.sub continuousOn_const)))).intervalIntegrable_of_Icc
      hle
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun r => P r t (M r - M t₀)) hle
    (hPc.clm_apply (hM.sub continuousOn_const)) hderiv hint
  have hsplit : (∫ s in t₀..t, P s t (M' s - A s (M s - M t₀))) =
      (∫ s in t₀..t, P s t (M' s)) - ∫ s in t₀..t, P s t (A s (M s - M t₀)) := by
    rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable_of_Icc hle)
      (hc2.intervalIntegrable_of_Icc hle)]
    simp
  rw [hsplit, hPt] at hftc
  simp only [ContinuousLinearMap.id_apply, sub_self, map_zero, sub_zero] at hftc
  rw [propagatedNoise, ← hftc]
  abel

end Banach

/-!
### Weighted (size-function) closure
-/

section Weighted

variable {ι : Type*} [Fintype ι]

/-- **Weighted Duhamel bound** (the consistency bookkeeping of the proof of
Proposition 6.1).  Inputs, each mapped to the source:

* `hIto` : the integral form of the evolution equation (Lemma 6.2);
* `hprop` : the propagator estimate in the weight `w_s = 𝔰_s` with gain `κ(s,t)`
  (Lemma 6.3: `κ(s,t) = (ℓ_tη_t/ℓ_sη_s)` resp. its square root, up to constants);
* `hinit` : the initial bound `|X_{t₀}| ≤ Ψ₀ 𝔰_{t₀}`;
* `hforce` : the forcing bound `|𝓕_s| ≤ f_s 𝔰_s` (Lemma 6.5);
* `hnoise` : the bound on the propagated martingale term (Lemma 6.4).

Conclusion: `|X_t(x)| ≤ (Ψ₀ κ(t₀,t) + ∫_{t₀}^t f_s κ(s,t) ds + m) 𝔰_t(x)`. -/
theorem weighted_duhamel_bound
    {A : ℝ → (ι → ℂ) →L[ℝ] (ι → ℂ)} {P : ℝ → ℝ → (ι → ℂ) →L[ℝ] (ι → ℂ)}
    {X F M : ℝ → ι → ℂ} {w : ℝ → ι → ℝ} {κ f : ℝ → ℝ} {Ψ₀ m t₀ t : ℝ} (hle : t₀ ≤ t)
    (hA : ContinuousOn A (Icc t₀ t)) (hX : ContinuousOn X (Icc t₀ t))
    (hF : ContinuousOn F (Icc t₀ t)) (hM : ContinuousOn M (Icc t₀ t))
    (hPc : ContinuousOn (fun s => P s t) (Icc t₀ t))
    (hPd : ∀ s ∈ Ioo t₀ t, HasDerivAt (fun r => P r t) (-((P s t).comp (A s))) s)
    (hPt : P t t = ContinuousLinearMap.id ℝ (ι → ℂ))
    (hIto : ∀ r ∈ Icc t₀ t,
      X r = X t₀ + (∫ u in t₀..r, (A u (X u) + F u)) + (M r - M t₀))
    (hprop : ∀ s ∈ Icc t₀ t, ∀ (g : ι → ℂ) (φ : ℝ),
      (∀ x, ‖g x‖ ≤ φ * w s x) → ∀ x, ‖P s t g x‖ ≤ φ * κ s * w t x)
    (hinit : ∀ x, ‖X t₀ x‖ ≤ Ψ₀ * w t₀ x)
    (hforce : ∀ s ∈ Icc t₀ t, ∀ x, ‖F s x‖ ≤ f s * w s x)
    (hnoise : ∀ x, ‖propagatedNoise P A M t₀ t x‖ ≤ m * w t x)
    (hfκ : IntervalIntegrable (fun s => f s * κ s) volume t₀ t) (x : ι) :
    ‖X t x‖ ≤ (Ψ₀ * κ t₀ + (∫ s in t₀..t, f s * κ s) + m) * w t x := by
  have hD := pathwise_duhamel hle hA hX hF hM hPc hPd hPt hIto
  have hc1 : ContinuousOn (fun s => P s t (F s)) (Icc t₀ t) := hPc.clm_apply hF
  have hcomm : (∫ s in t₀..t, P s t (F s)) x = ∫ s in t₀..t, P s t (F s) x := by
    have hii : IntervalIntegrable (fun s => P s t (F s)) volume t₀ t :=
      hc1.intervalIntegrable_of_Icc hle
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) x).intervalIntegral_comp_comm
      hii
    exact this.symm
  have h1 : ‖P t₀ t (X t₀) x‖ ≤ Ψ₀ * κ t₀ * w t x :=
    hprop t₀ ⟨le_rfl, hle⟩ (X t₀) Ψ₀ hinit x
  have h2 : ‖(∫ s in t₀..t, P s t (F s)) x‖ ≤ (∫ s in t₀..t, f s * κ s) * w t x := by
    rw [hcomm, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.norm_integral_le_of_norm_le hle ?_ (hfκ.mul_const _)
    exact Filter.Eventually.of_forall fun s hs =>
      hprop s ⟨hs.1.le, hs.2⟩ (F s) (f s) (hforce s ⟨hs.1.le, hs.2⟩) x
  rw [hD]
  simp only [Pi.add_apply]
  calc ‖P t₀ t (X t₀) x + (∫ s in t₀..t, P s t (F s)) x + propagatedNoise P A M t₀ t x‖
      ≤ ‖P t₀ t (X t₀) x‖ + ‖(∫ s in t₀..t, P s t (F s)) x‖ +
          ‖propagatedNoise P A M t₀ t x‖ := norm_add₃_le
    _ ≤ Ψ₀ * κ t₀ * w t x + (∫ s in t₀..t, f s * κ s) * w t x + m * w t x := by
        gcongr
        · exact hnoise x
    _ = (Ψ₀ * κ t₀ + (∫ s in t₀..t, f s * κ s) + m) * w t x := by ring

/-- **Stopped weighted closure.**  The inputs of `weighted_duhamel_bound` are required
only on the stopped interval `[t₀, τ]` (as Lemmas 6.4 and 6.5 are stated, `s ≤ τ`),
with a two-time propagator gain `κ(s,t)` and noise bound `m_t`; the conclusion is the
master-type entrywise bound at every time `t ∈ [t₀, τ]`. -/
theorem stopped_weighted_duhamel_bound
    {A : ℝ → (ι → ℂ) →L[ℝ] (ι → ℂ)} {P : ℝ → ℝ → (ι → ℂ) →L[ℝ] (ι → ℂ)}
    {X F M : ℝ → ι → ℂ} {w : ℝ → ι → ℝ} {κ : ℝ → ℝ → ℝ} {f m : ℝ → ℝ} {Ψ₀ t₀ τ : ℝ}
    (hA : ContinuousOn A (Icc t₀ τ)) (hX : ContinuousOn X (Icc t₀ τ))
    (hF : ContinuousOn F (Icc t₀ τ)) (hM : ContinuousOn M (Icc t₀ τ))
    (hPc : ∀ t ∈ Icc t₀ τ, ContinuousOn (fun s => P s t) (Icc t₀ t))
    (hPd : ∀ t ∈ Icc t₀ τ, ∀ s ∈ Ioo t₀ t,
      HasDerivAt (fun r => P r t) (-((P s t).comp (A s))) s)
    (hPt : ∀ t ∈ Icc t₀ τ, P t t = ContinuousLinearMap.id ℝ (ι → ℂ))
    (hIto : ∀ r ∈ Icc t₀ τ,
      X r = X t₀ + (∫ u in t₀..r, (A u (X u) + F u)) + (M r - M t₀))
    (hprop : ∀ t ∈ Icc t₀ τ, ∀ s ∈ Icc t₀ t, ∀ (g : ι → ℂ) (φ : ℝ),
      (∀ x, ‖g x‖ ≤ φ * w s x) → ∀ x, ‖P s t g x‖ ≤ φ * κ s t * w t x)
    (hinit : ∀ x, ‖X t₀ x‖ ≤ Ψ₀ * w t₀ x)
    (hforce : ∀ s ∈ Icc t₀ τ, ∀ x, ‖F s x‖ ≤ f s * w s x)
    (hnoise : ∀ t ∈ Icc t₀ τ, ∀ x, ‖propagatedNoise P A M t₀ t x‖ ≤ m t * w t x)
    (hfκ : ∀ t ∈ Icc t₀ τ, IntervalIntegrable (fun s => f s * κ s t) volume t₀ t)
    {t : ℝ} (ht : t ∈ Icc t₀ τ) (x : ι) :
    ‖X t x‖ ≤ (Ψ₀ * κ t₀ t + (∫ s in t₀..t, f s * κ s t) + m t) * w t x := by
  have hsub : Icc t₀ t ⊆ Icc t₀ τ := Icc_subset_Icc le_rfl ht.2
  exact weighted_duhamel_bound (κ := fun s => κ s t) ht.1 (hA.mono hsub) (hX.mono hsub)
    (hF.mono hsub) (hM.mono hsub) (hPc t ht) (hPd t ht) (hPt t ht)
    (fun r hr => hIto r (hsub hr)) (hprop t ht) hinit (fun s hs => hforce s (hsub hs))
    (hnoise t ht) (hfκ t ht) x

/-- The weighted ratio `max_x |f(x)| / w(x)`: the form of the control quantities `Ψ`
for one fixed choice of spectral parameters, with the weight
`w = (ℓ_tη_t)^{β_k} 𝔰_{k,t}` (resp. `(ℓ_tη_t)^{α_k} 𝔰^iso_{k,t}`). -/
def weightedRatio (w : ι → ℝ) (f : ι → ℂ) : ℝ := ⨆ x, ‖f x‖ / w x

theorem le_weightedRatio_mul {w : ι → ℝ} {f : ι → ℂ} (hw : ∀ x, 0 < w x) (x : ι) :
    ‖f x‖ ≤ weightedRatio w f * w x := by
  have h : ‖f x‖ / w x ≤ weightedRatio w f :=
    le_ciSup (Set.finite_range fun y => ‖f y‖ / w y).bddAbove x
  exact (div_le_iff₀ (hw x)).1 h

omit [Fintype ι] in
theorem weightedRatio_le [Nonempty ι] {w : ι → ℝ} {f : ι → ℂ} {c : ℝ} (hw : ∀ x, 0 < w x)
    (h : ∀ x, ‖f x‖ ≤ c * w x) : weightedRatio w f ≤ c :=
  ciSup_le fun x => (div_le_iff₀ (hw x)).2 (h x)

/-- **Stopped master-type bound for the control quantity** (the initial, martingale and
forcing bounds combined): with
`Ψ_t := max_x |X_t(x)| / w_t(x)`, for every `t ∈ [t₀, τ]`,
`Ψ_t ≤ Ψ_{t₀} κ(t₀,t) + ∫_{t₀}^t f_s κ(s,t) ds + m_t`. -/
theorem stopped_weightedRatio_bound [Nonempty ι]
    {A : ℝ → (ι → ℂ) →L[ℝ] (ι → ℂ)} {P : ℝ → ℝ → (ι → ℂ) →L[ℝ] (ι → ℂ)}
    {X F M : ℝ → ι → ℂ} {w : ℝ → ι → ℝ} {κ : ℝ → ℝ → ℝ} {f m : ℝ → ℝ} {t₀ τ : ℝ}
    (hw : ∀ t ∈ Icc t₀ τ, ∀ x, 0 < w t x)
    (hA : ContinuousOn A (Icc t₀ τ)) (hX : ContinuousOn X (Icc t₀ τ))
    (hF : ContinuousOn F (Icc t₀ τ)) (hM : ContinuousOn M (Icc t₀ τ))
    (hPc : ∀ t ∈ Icc t₀ τ, ContinuousOn (fun s => P s t) (Icc t₀ t))
    (hPd : ∀ t ∈ Icc t₀ τ, ∀ s ∈ Ioo t₀ t,
      HasDerivAt (fun r => P r t) (-((P s t).comp (A s))) s)
    (hPt : ∀ t ∈ Icc t₀ τ, P t t = ContinuousLinearMap.id ℝ (ι → ℂ))
    (hIto : ∀ r ∈ Icc t₀ τ,
      X r = X t₀ + (∫ u in t₀..r, (A u (X u) + F u)) + (M r - M t₀))
    (hprop : ∀ t ∈ Icc t₀ τ, ∀ s ∈ Icc t₀ t, ∀ (g : ι → ℂ) (φ : ℝ),
      (∀ x, ‖g x‖ ≤ φ * w s x) → ∀ x, ‖P s t g x‖ ≤ φ * κ s t * w t x)
    (hforce : ∀ s ∈ Icc t₀ τ, ∀ x, ‖F s x‖ ≤ f s * w s x)
    (hnoise : ∀ t ∈ Icc t₀ τ, ∀ x, ‖propagatedNoise P A M t₀ t x‖ ≤ m t * w t x)
    (hfκ : ∀ t ∈ Icc t₀ τ, IntervalIntegrable (fun s => f s * κ s t) volume t₀ t)
    {t : ℝ} (ht : t ∈ Icc t₀ τ) :
    weightedRatio (w t) (X t) ≤
      weightedRatio (w t₀) (X t₀) * κ t₀ t + (∫ s in t₀..t, f s * κ s t) + m t := by
  have ht₀ : t₀ ∈ Icc t₀ τ := ⟨le_rfl, ht.1.trans ht.2⟩
  exact weightedRatio_le (hw t ht) fun x =>
    stopped_weighted_duhamel_bound hA hX hF hM hPc hPd hPt hIto hprop
      (fun y => le_weightedRatio_mul (hw t₀ ht₀) y) hforce hnoise hfκ ht x

end Weighted

end ERZigStoppedDuhamel
end GaussianRing
end ERNative.BlockBand

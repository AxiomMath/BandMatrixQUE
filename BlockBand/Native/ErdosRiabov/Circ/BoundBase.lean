module

public import BlockBand.Native.ErdosRiabov.Discharge.All2
public import BlockBand.Native.ErdosRiabov.QV.Mart

/-!
# Regularized chains: shared inputs of the bounds

Integral estimates, the interior partial trace, kernel-time lifting and the decomposition of the
linear terms, used by the bounds on the regularized chains.

* `circ_norm_integral_apply_le`: `‖(∫_0^t f)(u)‖ ≤ ∫_0^t g` from `‖f_s(u)‖ ≤ g_s` on `(0, t]`,
  with no integrability hypothesis on `f` (a non-integrable `f` has integral `0`).
* `circ_intRule`: the integration rules (`QV.qv_int_rate`, i.e. `Flow.vsIntRules`) as interval
  integrals: `∫_0^T A L_s^{-γ} η_s⁻¹ ds ≤ A · qvIntRule γ T`.
* **`circ_traceMid_le`** (the Ward identity in size form): for `k = n+4` and
  `σ_{k-2} ≠ σ_{k-1}`,
  `|𝒯_{k-2}[𝒳^k](y)| ≤ η_s⁻¹ Ψ^av_{k-1,s} L_s^{β_{k-1}} s^av_{k-1,s}(y \ y_{k-2})`.
* **`circ_linLift`**:
  `T̂^{(k)}_t T̂^{(k-2)}_s = P̂^{(k)}_{s,t} T̂^{(k-2)}_s T̂^{(k)}_s`
  (`vsKernel_eq_propagator_mul`, `T̂_t = P̂_{s,t} T̂_s`, on the last coordinate).
* `circSlot_eq_ringOp_add`:
  `T̂^{(j)}_t f = Θ̊^{(j)}_t f + T̂_t(x_j, x_a) 𝒯_j f`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open MeasureTheory Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open scoped ComplexConjugate

/-!
### Integrals
-/

/-- `‖(∫_0^t f)(u)‖ ≤ ∫_0^t g` when `‖f_s(u)‖ ≤ g_s` on `(0, t]`, `g ≥ 0` on `[0, t]` and `g`
interval integrable; `f` need not be integrable. -/
theorem circ_norm_integral_apply_le {ι : Type*} [Fintype ι] (f : ℝ → ι → ℂ) (u : ι) {t : ℝ}
    (ht : 0 ≤ t) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 t)
    (hg0 : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ g s) (h : ∀ s ∈ Ioc (0 : ℝ) t, ‖f s u‖ ≤ g s) :
    ‖(∫ s in (0 : ℝ)..t, f s) u‖ ≤ ∫ s in (0 : ℝ)..t, g s := by
  by_cases hf : IntervalIntegrable f volume 0 t
  · have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) u
      ).intervalIntegral_comp_comm hf
    simp only [ContinuousLinearMap.proj_apply] at hproj
    rw [← hproj]
    exact intervalIntegral.norm_integral_le_of_norm_le ht (ae_of_all _ fun s hs => h s hs) hg
  · rw [intervalIntegral.integral_undef hf, Pi.zero_apply, norm_zero]
    exact intervalIntegral.integral_nonneg ht hg0

section Rule

variable {p : BlockBand.Parameters} (d : VSData) (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
include hPW hz

theorem circ_rate_intervalIntegrable (γ A : ℝ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    IntervalIntegrable (fun s => A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹) volume 0 T :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr
    (QV.qv_rate_integrableOn d P hPW hz γ A hT1)

/-- The integration rules as interval integrals (`QV.qv_int_rate`, `Flow.vsIntRules`). -/
theorem circ_intRule {γ A T : ℝ} (hγ : 0 ≤ γ) (hA : 0 ≤ A) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ∫ s in (0 : ℝ)..T, A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹ ≤ A * QV.qvIntRule d P γ T := by
  rw [intervalIntegral.integral_of_le hT0]
  exact QV.qv_int_rate d P hPW hz hγ hA hT0 hT1

end Rule

/-!
### The interior partial trace
-/

variable {N : ℕ}

/-- **Interior partial trace via Ward** (size form): for
`k = n+4`, `σ_{k-2} ≠ σ_{k-1}` (0-based `⟨n+1⟩`, `⟨n+2⟩`), `s ∈ [0,1]`, Hermitian `H`, `L_s > 0`
and `s^av_{k-1}(y \ y_{k-2}) > 0`:
`|Σ_b 𝒳^k(y[y_{k-2} ↦ b])| ≤ η_s⁻¹ Ψ^av_{k-1,s} L_s^{β_{k-1}} s^av_{k-1,s}(y \ y_{k-2})`. -/
theorem circ_traceMid_le (P : PsiData N) (hS : StochasticSymm P.S) (hz : 0 < P.z.im) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : σ ⟨n + 1, by omega⟩ ≠ σ ⟨n + 2, by omega⟩)
    (y : Fin (n + 2 + 2) → Fin N) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hL : 0 < P.lEta s)
    (hsa : 0 < P.sAv (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) y) s) :
    ‖∑ b, P.avErr σ (update y ⟨n + 1, by omega⟩ b) s H‖ ≤ (vsHeight P.z s)⁻¹ *
      (P.bigPsiAv (n + 3) s H * (P.lEta s ^ Expo.lossBeta (n + 3) *
        P.sAv (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) y) s)) := by
  have hη := vsHeight_pos hz hs.2
  have h := Discharge.circ_wardMid_norm_uncond P hS hz σ ⟨n + 1, by omega⟩ hσ y hs hH
  rw [show ((⟨n + 1, by omega⟩ : Fin (n + 3)).castSucc : Fin (n + 2 + 2)) =
    ⟨n + 1, by omega⟩ from rfl] at h
  refine h.trans ((mul_le_mul_of_nonneg_left (add_le_add
    (circ_norm_avErr_le P _ _ H hL hsa) (circ_norm_avErr_le P _ _ H hL hsa))
    (by positivity)).trans (le_of_eq ?_))
  field_simp
  ring

/-!
### Kernel-time lifting
-/

/-- **Kernel-time lifting**: for stochastic symmetric `S`, `Im z ≠ 0`,
`s, t ∈ [0,1]` and `k = n+4`:
`T̂^{(k)}_t[T̂^{(k-2)}_s f] = P̂^{(k)}_{s,t}[T̂^{(k-2)}_s T̂^{(k)}_s f]`
(`T̂_t = P̂_{s,t} T̂_s`). -/
theorem circ_linLift {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) {z : ℂ}
    (hz : z.im ≠ 0) {n : ℕ} {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (f : CircFun N (n + 2 + 2)) :
    circSlot (Fin.last (n + 2 + 1)) (vsKernel S (semicircleM z) (conj (semicircleM z)) t)
        (circSlot ⟨n + 1, by omega⟩ (vsKernel S (semicircleM z) (conj (semicircleM z)) s) f) =
      circSlot (Fin.last (n + 2 + 1))
        (vsPropagator S (semicircleM z) (conj (semicircleM z)) s t)
        (circSlot ⟨n + 1, by omega⟩ (vsKernel S (semicircleM z) (conj (semicircleM z)) s)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel S (semicircleM z) (conj (semicircleM z)) s) f)) := by
  have hne : (Fin.last (n + 2 + 1) : Fin (n + 2 + 2)) ≠ ⟨n + 1, by omega⟩ := by
    intro e
    have := congrArg Fin.val e
    simp at this
  rw [vsKernel_eq_propagator_mul hS (circ_norm_smul_lt_one hz hs) (circ_norm_smul_lt_one hz ht),
    ← circSlot_mul_same, Module.End.mul_apply]
  congr 1
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, circSlot_comm hne]

/-!
### The decompositions of the linear terms
-/

/-- **Decomposition of the linear term** (`T̂ = Θ̊ + remainder`): for `a ≠ j`,
`T̂^{(j)}_t f(x) = Θ̊^{(j)}_t f(x) + T̂_t(x_j, x_a) 𝒯_j f(x)` (`Θ̊ = ringOp`, anchor `a`). -/
theorem circSlot_eq_ringOp_add (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) {k : ℕ}
    {j a : Fin k} (haj : a ≠ j) (f : CircFun N k) :
    circSlot j (vsKernel S (semicircleM z) (conj (semicircleM z)) t) f =
      ringOp S z t j a f + fun x =>
        vsKernel S (semicircleM z) (conj (semicircleM z)) t (x j) (x a) *
          ∑ b, f (update x j b) := by
  funext x
  rw [ringOp_eq_circRing _ _ _ haj]
  simp only [circRing, circDiag, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_sub, Pi.add_apply, Pi.sub_apply, circSlot_apply, circDiagE_apply, update_of_ne haj,
    update_self, update_idem]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

end BlockBand.Native.ErdosRiabov.Circ

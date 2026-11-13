module

public import BlockBand.Transmission.Dual.GHarmonic
public import BlockBand.Transmission.Dual.UniqueCoord

/-!
# The `H_q`-transform identity

`baseGen D₀ F` is the base generator
`L⁰ = (D₀/2)[Σ_i (x_i(1+x_i)∂²_{x_i} + (1+2x_i)∂_{x_i}) + Σ_j (y_j(1−y_j)∂²_{y_j} + (1−2y_j)∂_{y_j})]`
of `2q` independent scalar diffusions (second derivatives as `fderiv (fderiv F) z v v`).
* `baseGen_cauchyH`: `L⁰ H_q = 0` wherever every `x_i + y_j ≠ 0`. Proof: Leibniz expansion; each
  term `Π_i h(x_{σ i}, y_i)` is a product of functions of disjoint pairs of variables, and
  `(L_X + L_Y) h = 0` for `h(x, y) = 1/(x + y)`.
* `baseGen_cauchyH_mul`: **`L⁰(H_q f) = H_q 𝒟_q f`** on the chamber for `f ∈ C²`, with the dual
  generator `𝒟_q = dualGenerator`. With `fderiv_cauchyH_dirX/Y` (`∂ log H_q` is the bracket of
  the dual drifts) this is the h-transform identity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Matrix Finset Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath

variable {q : ℕ}

/-- The base generator `L⁰` (independent scalar diffusions), second-derivative form. -/
def baseGen (D0 : ℝ) (F : DualCoord q → ℝ) (z : DualCoord q) : ℝ :=
  D0 / 2 * ((∑ i, (z.1 i * (1 + z.1 i) * fderiv ℝ (fderiv ℝ F) z (dirX i) (dirX i) +
      (1 + 2 * z.1 i) * fderiv ℝ F z (dirX i))) +
    ∑ j, (z.2 j * (1 - z.2 j) * fderiv ℝ (fderiv ℝ F) z (dirY j) (dirY j) +
      (1 - 2 * z.2 j) * fderiv ℝ F z (dirY j)))

/-!
## Calculus: sums, products, and `(a + r)⁻¹`
-/

theorem baseGen_sum {ι : Type*} (D0 : ℝ) (s : Finset ι) (F : ι → DualCoord q → ℝ)
    {z : DualCoord q} (hF : ∀ i ∈ s, ContDiffAt ℝ 2 (F i) z) :
    baseGen D0 (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, baseGen D0 (F i) z := by
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (F i) z := fun i hi =>
    (hF i hi).differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, fderiv ℝ (F i) z :=
    fderiv_fun_sum hd
  have hev : fderiv ℝ (fun w => ∑ i ∈ s, F i w) =ᶠ[𝓝 z] fun w => ∑ i ∈ s, fderiv ℝ (F i) w := by
    have : ∀ᶠ w in 𝓝 z, ∀ i ∈ s, DifferentiableAt ℝ (F i) w :=
      (eventually_all_finset s).2 fun i hi =>
        ((hF i hi).eventually (by simp)).mono fun w hw => hw.differentiableAt (by norm_num)
    filter_upwards [this] with w hw using fderiv_fun_sum hw
  have h2 : fderiv ℝ (fderiv ℝ fun w => ∑ i ∈ s, F i w) z =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (F i)) z := by
    rw [hev.fderiv_eq]
    exact fderiv_fun_sum fun i hi =>
      ((hF i hi).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simp only [baseGen, h1, h2, FunLike.coe_sum, Finset.sum_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := univ)]

theorem fderiv_mul_apply {F f : DualCoord q → ℝ} {z : DualCoord q}
    (hF : DifferentiableAt ℝ F z) (hf : DifferentiableAt ℝ f z) (v : DualCoord q) :
    fderiv ℝ (fun w => F w * f w) z v = F z * fderiv ℝ f z v + f z * fderiv ℝ F z v := by
  rw [fderiv_fun_mul hF hf]; simp

theorem fderiv_fderiv_mul_apply {F f : DualCoord q → ℝ} {z : DualCoord q}
    (hF : ContDiffAt ℝ 2 F z) (hf : ContDiffAt ℝ 2 f z) (v : DualCoord q) :
    fderiv ℝ (fderiv ℝ fun w => F w * f w) z v v =
      fderiv ℝ (fderiv ℝ F) z v v * f z + 2 * (fderiv ℝ F z v * fderiv ℝ f z v) +
        F z * fderiv ℝ (fderiv ℝ f) z v v := by
  have hev : fderiv ℝ (fun w => F w * f w) =ᶠ[𝓝 z]
      fun w => F w • fderiv ℝ f w + f w • fderiv ℝ F w := by
    filter_upwards [hF.eventually (by simp), hf.eventually (by simp)] with w hFw hfw
    exact fderiv_fun_mul (hFw.differentiableAt (by norm_num)) (hfw.differentiableAt (by norm_num))
  have hFd := hF.differentiableAt (by norm_num)
  have hfd := hf.differentiableAt (by norm_num)
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd : HasFDerivAt (fun w => F w • fderiv ℝ f w + f w • fderiv ℝ F w)
      ((F z • fderiv ℝ (fderiv ℝ f) z + (fderiv ℝ F z).smulRight (fderiv ℝ f z)) +
        (f z • fderiv ℝ (fderiv ℝ F) z + (fderiv ℝ f z).smulRight (fderiv ℝ F z))) z :=
    (hFd.hasFDerivAt.smul hDf.hasFDerivAt).add (hfd.hasFDerivAt.smul hDF.hasFDerivAt)
  rw [hev.fderiv_eq, hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

private theorem hasDerivAt_add_inv (a P : ℝ) {r : ℝ} (hr : a + r ≠ 0) :
    HasDerivAt (fun r : ℝ => (a + r)⁻¹ * P) (-P * ((a + r) ^ 2)⁻¹) r := by
  have h : HasDerivAt (fun r : ℝ => a + r) 1 r := (hasDerivAt_id r).const_add a
  convert (h.inv hr).mul_const P using 1
  field_simp

theorem deriv_inv_line (a P : ℝ) (ha : a ≠ 0) :
    deriv (fun r : ℝ => (a + r)⁻¹ * P) 0 = -P / a ^ 2 := by
  rw [(hasDerivAt_add_inv a P (by simpa using ha)).deriv]; simp [div_eq_mul_inv]

theorem deriv_deriv_inv_line (a P : ℝ) (ha : a ≠ 0) :
    deriv (deriv fun r : ℝ => (a + r)⁻¹ * P) 0 = 2 * P / a ^ 3 := by
  have hev : deriv (fun r : ℝ => (a + r)⁻¹ * P) =ᶠ[𝓝 0] fun r => -P * ((a + r) ^ 2)⁻¹ := by
    have : ∀ᶠ r in 𝓝 (0 : ℝ), a + r ≠ 0 :=
      (continuous_const.add continuous_id).continuousAt.eventually_ne (by simpa using ha)
    filter_upwards [this] with r hr using (hasDerivAt_add_inv a P hr).deriv
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun r : ℝ => a + r) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add a
  have h2 : HasDerivAt (fun r : ℝ => (a + r) ^ 2) (2 * a) 0 := by
    have h := (hasDerivAt_pow 2 (a + 0)).comp (0 : ℝ) h1
    simp only [Function.comp_def] at h
    convert h using 1
    simp
  have h3 : HasDerivAt (fun r : ℝ => -P * ((a + r) ^ 2)⁻¹)
      (-P * (-(2 * a) / ((a + 0) ^ 2) ^ 2)) 0 :=
    (h2.inv (by simpa using pow_ne_zero 2 ha)).const_mul (-P)
  rw [h3.deriv]
  simp only [add_zero]
  field_simp

/-!
## Each Leibniz term is `L⁰`-harmonic
-/

/-- The Leibniz term `Π_i h(x_{σ i}, y_i)`, times a constant. -/
def leibTerm (c : ℝ) (σ : Equiv.Perm (Fin q)) (w : DualCoord q) : ℝ :=
  c * ∏ i, (w.1 (σ i) + w.2 i)⁻¹

theorem contDiffAt_leibTerm (c : ℝ) (σ : Equiv.Perm (Fin q)) {z : DualCoord q}
    (hz : ∀ i j, z.1 i + z.2 j ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) (leibTerm c σ) z := by
  refine contDiffAt_const.mul (contDiffAt_prod fun i _ => ?_)
  have hc : ContDiff ℝ (⊤ : ℕ∞) fun w : DualCoord q => w.1 (σ i) + w.2 i :=
    ((contDiff_apply ℝ ℝ (σ i)).comp contDiff_fst).add ((contDiff_apply ℝ ℝ i).comp contDiff_snd)
  exact hc.contDiffAt.inv (hz (σ i) i)

theorem leibTerm_line_dirX (c : ℝ) (σ : Equiv.Perm (Fin q)) (z : DualCoord q) (m : Fin q)
    (r : ℝ) : leibTerm c σ (z + r • dirX m) = (z.1 m + z.2 (σ.symm m) + r)⁻¹ *
      (c * ∏ i ∈ univ.erase (σ.symm m), (z.1 (σ i) + z.2 i)⁻¹) := by
  rw [leibTerm, ← Finset.mul_prod_erase univ _ (mem_univ (σ.symm m))]
  simp only [line_fst, line_snd, dirX, Equiv.apply_symm_apply, Pi.single_eq_same,
    Pi.zero_apply, mul_zero, add_zero, mul_one]
  rw [show z.1 m + r + z.2 (σ.symm m) = z.1 m + z.2 (σ.symm m) + r by ring]
  have : ∏ i ∈ univ.erase (σ.symm m), (z.1 (σ i) + r * (Pi.single m (1 : ℝ) : Fin q → ℝ) (σ i) +
      z.2 i)⁻¹ = ∏ i ∈ univ.erase (σ.symm m), (z.1 (σ i) + z.2 i)⁻¹ := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : σ i ≠ m := fun h => (Finset.ne_of_mem_erase hi) (by rw [← h]; simp)
    simp [hne]
  rw [this]; ring

theorem leibTerm_line_dirY (c : ℝ) (σ : Equiv.Perm (Fin q)) (z : DualCoord q) (m : Fin q)
    (r : ℝ) : leibTerm c σ (z + r • dirY m) = (z.1 (σ m) + z.2 m + r)⁻¹ *
      (c * ∏ i ∈ univ.erase m, (z.1 (σ i) + z.2 i)⁻¹) := by
  rw [leibTerm, ← Finset.mul_prod_erase univ _ (mem_univ m)]
  simp only [line_fst, line_snd, dirY, Pi.single_eq_same, Pi.zero_apply,
    mul_zero, add_zero, mul_one]
  rw [show z.1 (σ m) + (z.2 m + r) = z.1 (σ m) + z.2 m + r by ring]
  have : ∏ i ∈ univ.erase m, (z.1 (σ i) + (z.2 i + r * (Pi.single m (1 : ℝ) : Fin q → ℝ) i))⁻¹ =
      ∏ i ∈ univ.erase m, (z.1 (σ i) + z.2 i)⁻¹ := by
    refine Finset.prod_congr rfl fun i hi => ?_
    simp [Finset.ne_of_mem_erase hi]
  rw [this]; ring

/-- First and second derivatives of a Leibniz term along a line on which it is `P/(a + r)`. -/
private theorem leib_derivs {G : DualCoord q → ℝ} {z v : DualCoord q} (hG : ContDiffAt ℝ 2 G z)
    {a P : ℝ} (ha : a ≠ 0) (hline : ∀ r : ℝ, G (z + r • v) = (a + r)⁻¹ * P) :
    fderiv ℝ G z v = -G z / a ∧ fderiv ℝ (fderiv ℝ G) z v v = 2 * G z / a ^ 2 := by
  have hl : (fun r : ℝ => G (z + r • v)) = fun r => (a + r)⁻¹ * P := funext hline
  have hz : G z = a⁻¹ * P := by simpa using hline 0
  refine ⟨?_, ?_⟩
  · rw [Exists.fderiv_eq_deriv_line v (hG.differentiableAt (by norm_num)), hl,
      deriv_inv_line a P ha, hz]
    field_simp
  · rw [Exists.fderiv_fderiv_eq_deriv_line v hG, hl, deriv_deriv_inv_line a P ha, hz]
    field_simp

theorem baseGen_leibTerm (D0 c : ℝ) (σ : Equiv.Perm (Fin q)) {z : DualCoord q}
    (hz : ∀ i j, z.1 i + z.2 j ≠ 0) : baseGen D0 (leibTerm c σ) z = 0 := by
  have hG : ContDiffAt ℝ 2 (leibTerm c σ) z := (contDiffAt_leibTerm c σ hz).of_le (by simp)
  set T := leibTerm c σ z
  have hX : ∀ m, fderiv ℝ (leibTerm c σ) z (dirX m) = -T / (z.1 m + z.2 (σ.symm m)) ∧
      fderiv ℝ (fderiv ℝ (leibTerm c σ)) z (dirX m) (dirX m) =
        2 * T / (z.1 m + z.2 (σ.symm m)) ^ 2 := fun m =>
    leib_derivs hG (hz _ _) (leibTerm_line_dirX c σ z m)
  have hY : ∀ m, fderiv ℝ (leibTerm c σ) z (dirY m) = -T / (z.1 (σ m) + z.2 m) ∧
      fderiv ℝ (fderiv ℝ (leibTerm c σ)) z (dirY m) (dirY m) =
        2 * T / (z.1 (σ m) + z.2 m) ^ 2 := fun m =>
    leib_derivs hG (hz _ _) (leibTerm_line_dirY c σ z m)
  simp only [baseGen, fun m => (hX m).1, fun m => (hX m).2, fun m => (hY m).1,
    fun m => (hY m).2]
  rw [← Equiv.sum_comp σ, ← Finset.sum_add_distrib]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
  have h := hz (σ i) i
  field_simp
  ring

/-- **`L⁰ H_q = 0`** wherever every `x_i + y_j ≠ 0`. -/
theorem baseGen_cauchyH (D0 : ℝ) {z : DualCoord q} (hz : ∀ i j, z.1 i + z.2 j ≠ 0) :
    baseGen D0 (cauchyH q) z = 0 := by
  have he : cauchyH q = fun w => ∑ σ : Equiv.Perm (Fin q),
      leibTerm ((Equiv.Perm.sign σ : ℤ) : ℝ) σ w := funext cauchyH_eq_sum
  rw [he, baseGen_sum D0 univ _ fun σ _ =>
    (contDiffAt_leibTerm _ σ hz).of_le (by simp)]
  exact Finset.sum_eq_zero fun σ _ => baseGen_leibTerm D0 _ σ hz

/-!
## The h-transform identity
-/

private theorem hTerm (H f d2H dH d2f df c1 c2 ℓ β : ℝ) (hℓ : dH = H * ℓ)
    (hβ : β = c1 + 2 * c2 * ℓ) :
    c2 * (d2H * f + 2 * (dH * df) + H * d2f) + c1 * (H * df + f * dH) =
      f * (c2 * d2H + c1 * dH) + H * (c2 * d2f + β * df) := by
  subst hℓ hβ; ring

/-- **The h-transform identity** `L⁰(H_q f) = H_q 𝒟_q f` on the chamber, for `f ∈ C²` and the
`dualGenerator` (F8-PROOF F0.2).
-/
theorem baseGen_cauchyH_mul (D0 : ℝ) {f : DualCoord q → ℝ} (hf : ContDiff ℝ 2 f)
    {z : DualCoord q} (hz : z ∈ dualChamber q) :
    baseGen D0 (fun w => cauchyH q w * f w) z = cauchyH q z * dualGenerator D0 f z := by
  have hne : ∀ i j, z.1 i + z.2 j ≠ 0 := fun i j => (add_pos_of_mem hz i j).ne'
  have hH : ContDiffAt ℝ 2 (cauchyH q) z := (contDiffAt_cauchyH_of_mem hz).of_le (by simp)
  have hfz : ContDiffAt ℝ 2 f z := hf.contDiffAt
  have h0 := baseGen_cauchyH D0 hne
  unfold baseGen at h0 ⊢
  unfold dualGenerator
  simp only [fderiv_mul_apply (hH.differentiableAt (by norm_num))
      (hfz.differentiableAt (by norm_num)), fderiv_fderiv_mul_apply hH hfz,
    fderiv_fderiv_apply_eq hf]
  have hx : ∑ i, (z.1 i * (1 + z.1 i) * (fderiv ℝ (fderiv ℝ (cauchyH q)) z (dirX i) (dirX i) *
        f z + 2 * (fderiv ℝ (cauchyH q) z (dirX i) * fderiv ℝ f z (dirX i)) +
        cauchyH q z * fderiv ℝ (fderiv ℝ f) z (dirX i) (dirX i)) +
      (1 + 2 * z.1 i) * (cauchyH q z * fderiv ℝ f z (dirX i) +
        f z * fderiv ℝ (cauchyH q) z (dirX i))) =
      f z * ∑ i, (z.1 i * (1 + z.1 i) * fderiv ℝ (fderiv ℝ (cauchyH q)) z (dirX i) (dirX i) +
        (1 + 2 * z.1 i) * fderiv ℝ (cauchyH q) z (dirX i)) +
      cauchyH q z * ∑ i, (z.1 i * (1 + z.1 i) * fderiv ℝ (fderiv ℝ f) z (dirX i) (dirX i) +
        dualDriftX z i * fderiv ℝ f z (dirX i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hTerm _ _ _ _ _ _ _ _ _ _
      (fderiv_cauchyH_dirX hz i) (by unfold dualDriftX; ring)
  have hy : ∑ j, (z.2 j * (1 - z.2 j) * (fderiv ℝ (fderiv ℝ (cauchyH q)) z (dirY j) (dirY j) *
        f z + 2 * (fderiv ℝ (cauchyH q) z (dirY j) * fderiv ℝ f z (dirY j)) +
        cauchyH q z * fderiv ℝ (fderiv ℝ f) z (dirY j) (dirY j)) +
      (1 - 2 * z.2 j) * (cauchyH q z * fderiv ℝ f z (dirY j) +
        f z * fderiv ℝ (cauchyH q) z (dirY j))) =
      f z * ∑ j, (z.2 j * (1 - z.2 j) * fderiv ℝ (fderiv ℝ (cauchyH q)) z (dirY j) (dirY j) +
        (1 - 2 * z.2 j) * fderiv ℝ (cauchyH q) z (dirY j)) +
      cauchyH q z * ∑ j, (z.2 j * (1 - z.2 j) * fderiv ℝ (fderiv ℝ f) z (dirY j) (dirY j) +
        dualDriftY z j * fderiv ℝ f z (dirY j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hTerm _ _ _ _ _ _ _ _ _ _
      (fderiv_cauchyH_dirY hz j) (by unfold dualDriftY; ring)
  rw [hx, hy]
  linear_combination f z * h0

end BlockBand.Transmission.Dual.G

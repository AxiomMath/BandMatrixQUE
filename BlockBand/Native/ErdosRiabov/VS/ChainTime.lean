module

public import BlockBand.Native.ErdosRiabov.VS.BandIto
public import BlockBand.Native.ErdosRiabov.Chains.ChainCalc

set_option autoImplicit false

/-!
# Resolvent chains with time-dependent spectral parameters

Itô's formula `semimartingaleItoFormula_holds` needs test functions that are `C²` **jointly** in
`(t, y)`, while the derivative theorems for resolvent chains are in `y` at a fixed spectral
parameter. Here the spectral
parameters are functions of time, `z_j : ℝ → ℂ` (in the zig step `z_j(t) = z_{c(t)}` with the
smooth saturation `c`), and

`chainTestT A₀ L z B K (t, y) = chainTest A₀ L (z(t)) B K y = Re tr(K R_0 B_0 ⋯ R_{k-1} B_{k-1})`,
`R_j = (A₀ + L y - z_j(t))⁻¹`.

At every `(t, y)` where all `A₀ + L y - z_j(t)` are invertible:

* `contDiffAt_chainTestT`: `C^n` jointly if every `z_j` is `C^n` at `t` (`contDiffOn_chainTestT`:
  on `ℝ × U` when invertibility holds there, the form needed by Itô's formula);
  `measurable_chainTestT`: Borel measurable on all of `ℝ × V`.
* `partialTime_chainTestT`: `∂_t f = Re tr(K ∑_j R_0 B_0 ⋯ (z_j'(t) R_j²) B_j ⋯)`
  (`dR_j/dt = z_j'(t) R_j²`), for differentiable `z_j`.
* `partialSpace_chainTestT`, `partialSpace2_chainTestT`: the spatial partials of Itô's formula
  are the fixed-time `Chains` derivatives at `z(t)` (`firstVar`, `secondVar`), by the slicing
  lemmas `partialSpace_eq_slice`, `partialSpace2_eq_slice`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open Matrix Filter Topology Function
open BlockBand.Internal.Contracts.Transmission
open BlockBand.Native.CEH.Flow
open BlockBand.Native.ErdosRiabov.Chains

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- `w ↦ w • 1` as a real-linear map `ℂ → Matrix ι ι ℂ`. -/
def specLin (ι : Type) [Fintype ι] [DecidableEq ι] : ℂ →ₗ[ℝ] Matrix ι ι ℂ where
  toFun w := w • (1 : Matrix ι ι ℂ)
  map_add' w w' := add_smul w w' 1
  map_smul' r w := smul_assoc r w (1 : Matrix ι ι ℂ)

/-- The joint affine map `(y, w) ↦ L y - w • 1` on `V × ℂ`. -/
def affT (L : V →ₗ[ℝ] Matrix ι ι ℂ) : V × ℂ →ₗ[ℝ] Matrix ι ι ℂ :=
  L ∘ₗ LinearMap.fst ℝ V ℂ - specLin ι ∘ₗ LinearMap.snd ℝ V ℂ

omit [FiniteDimensional ℝ V] in
theorem affT_apply (L : V →ₗ[ℝ] Matrix ι ι ℂ) (q : V × ℂ) :
    affT L q = L q.1 - q.2 • (1 : Matrix ι ι ℂ) := rfl

omit [FiniteDimensional ℝ V] in
theorem res_eq_affT (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (w : ℂ) (y : V) :
    res A₀ L w y = (A₀ + affT L (y, w))⁻¹ := by
  rw [res, affT_apply, add_sub_assoc]

/-- Chain test function with time-dependent spectral parameters:
`chainTestT A₀ L z B K (t, y) = chainTest A₀ L (z(t)) B K y`. -/
def chainTestT (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℝ → ℂ)
    (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) (q : ℝ × V) : ℝ :=
  chainTest A₀ L (fun j => z j q.1) B K q.2

omit [FiniteDimensional ℝ V] in
theorem chainTestT_slice (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℝ → ℂ)
    (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) (t : ℝ) :
    (fun y => chainTestT A₀ L z B K (t, y)) = chainTest A₀ L (fun j => z j t) B K := rfl

/-!
### Measurability
-/

omit [FiniteDimensional ℝ V] in
theorem measurable_matrix_inv_vs : Measurable fun A : Matrix ι ι ℂ => A⁻¹ := by
  apply Measurable.of_eval_matrix
  intro i j
  have hdet : Measurable fun A : Matrix ι ι ℂ => A.det := continuous_id.matrix_det.measurable
  have hadj : Measurable fun A : Matrix ι ι ℂ => A.adjugate i j :=
    ((continuous_apply j).comp ((continuous_apply i).comp
      continuous_id.matrix_adjugate)).measurable
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact hdet.inv.mul hadj

omit [FiniteDimensional ℝ V] in
theorem continuous_slotProd (B : Fin k → Matrix ι ι ℂ) :
    Continuous fun M : Fin k → Matrix ι ι ℂ => slotProd B M := by
  have e : (fun M : Fin k → Matrix ι ι ℂ => slotProd B M) =
      fun M => ((List.finRange k).map fun l => M l * B l).prod := by
    funext M
    rw [slotProd, slotList, List.ofFn_eq_map]
  rw [e]
  exact continuous_list_prod _ fun l _ => (continuous_apply l).mul continuous_const

/-- `chainTestT` is Borel measurable on `ℝ × V` (needed by Itô's formula). -/
theorem measurable_chainTestT [MeasurableSpace V] [BorelSpace V] (A₀ : Matrix ι ι ℂ)
    (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℝ → ℂ) (B : Fin k → Matrix ι ι ℂ)
    (K : Matrix ι ι ℂ) (hz : ∀ j, Measurable (z j)) : Measurable (chainTestT A₀ L z B K) := by
  have hg : Continuous fun p : V × ℂ => A₀ + affT L p :=
    continuous_const.add (LinearMap.toContinuousLinearMap (affT L)).continuous
  have hR : ∀ j, Measurable fun q : ℝ × V => res A₀ L (z j q.1) q.2 := by
    intro j
    have hf : (fun q : ℝ × V => res A₀ L (z j q.1) q.2) =
        (fun A : Matrix ι ι ℂ => A⁻¹) ∘ (fun p : V × ℂ => A₀ + affT L p) ∘
          fun q : ℝ × V => (q.2, z j q.1) :=
      funext fun q => res_eq_affT A₀ L (z j q.1) q.2
    rw [hf]
    exact measurable_matrix_inv_vs.comp (hg.measurable.comp
      (measurable_snd.prodMk ((hz j).comp measurable_fst)))
  have : SecondCountableTopology (Matrix ι ι ℂ) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → ℂ))
  have hS : Measurable fun q : ℝ × V => resSlots A₀ L (fun j => z j q.1) q.2 :=
    measurable_pi_iff.2 hR
  have hT : Continuous fun M : Fin k → Matrix ι ι ℂ => reTr K (slotProd B M) :=
    (Complex.continuous_re.comp (continuous_const.matrix_mul continuous_id).matrix_trace).comp
      (continuous_slotProd B)
  exact hT.measurable.comp hS

section Smooth

/-!
### Joint smoothness
-/

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiffAt_resT (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : ℝ → ℂ)
    {t : ℝ} {y : V} (hy : IsUnit (A₀ + L y - z t • (1 : Matrix ι ι ℂ)).det) {n : WithTop ℕ∞}
    (hz : ContDiffAt ℝ n z t) :
    ContDiffAt ℝ n (fun q : ℝ × V => res A₀ L (z q.1) q.2) (t, y) := by
  have hy' : IsUnit (A₀ + affT L (y, z t)).det := by
    rw [affT_apply, ← add_sub_assoc]
    exact hy
  have hinner : ContDiffAt ℝ n (fun q : ℝ × V => (q.2, z q.1)) (t, y) :=
    contDiffAt_snd.prodMk (hz.comp (t, y) contDiffAt_fst)
  have h := (contDiffAt_inv_affine A₀ (affT L) hy' (n := n)).comp (t, y) hinner
  have hf : (fun q : ℝ × V => res A₀ L (z q.1) q.2) =
      (fun p : V × ℂ => (A₀ + affT L p)⁻¹) ∘ fun q : ℝ × V => (q.2, z q.1) :=
    funext fun q => res_eq_affT A₀ L (z q.1) q.2
  rw [hf]
  exact h

/-- **Joint smoothness** of the time-dependent chain test function. -/
theorem contDiffAt_chainTestT (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ)
    (z : Fin k → ℝ → ℂ) (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {t : ℝ} {y : V}
    (hy : ∀ j, IsUnit (A₀ + L y - z j t • (1 : Matrix ι ι ℂ)).det) {n : WithTop ℕ∞}
    (hz : ∀ j, ContDiffAt ℝ n (z j) t) : ContDiffAt ℝ n (chainTestT A₀ L z B K) (t, y) := by
  have hs : ContDiffAt ℝ n (fun q : ℝ × V => resChain A₀ L (fun j => z j q.1) B q.2) (t, y) :=
    contDiffAt_slotProd B (M := fun q : ℝ × V => resSlots A₀ L (fun j => z j q.1) q.2)
      fun j => contDiffAt_resT A₀ L (z j) (hy j) (hz j)
  exact ((reTrLin K).toContinuousLinearMap.contDiff.contDiffAt).comp (t, y) hs

/-- `C²` on `ℝ × U` (the hypothesis of Itô's formula) when the `z_j` are `C²` and all
resolvents exist on `ℝ × U`. -/
theorem contDiffOn_chainTestT (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ)
    (z : Fin k → ℝ → ℂ) (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {U : Set V}
    (hU : ∀ t, ∀ y ∈ U, ∀ j, IsUnit (A₀ + L y - z j t • (1 : Matrix ι ι ℂ)).det)
    (hz : ∀ j, ContDiff ℝ 2 (z j)) :
    ContDiffOn ℝ 2 (chainTestT A₀ L z B K) (Set.univ ×ˢ U) := fun q hq =>
  (contDiffAt_chainTestT A₀ L z B K (hU q.1 q.2 hq.2) fun j =>
    (hz j).contDiffAt).contDiffWithinAt

/-!
### The time derivative
-/

theorem hasDerivAt_resT (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) {z : ℝ → ℂ} {z' : ℂ}
    {t : ℝ} {y : V} (hy : IsUnit (A₀ + L y - z t • (1 : Matrix ι ι ℂ)).det)
    (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => res A₀ L (z s) y) (z' • (res A₀ L (z t) y * res A₀ L (z t) y)) t := by
  have hy' : IsUnit (A₀ + affT L (y, z t)).det := by
    rw [affT_apply, ← add_sub_assoc]
    exact hy
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_inv_affine A₀ (affT L) hy'
  have hc := hD.comp_hasDerivAt t ((hasDerivAt_const t y).prodMk hz)
  have hf : (fun s => res A₀ L (z s) y) = (fun p : V × ℂ => (A₀ + affT L p)⁻¹) ∘
      fun s => (y, z s) := funext fun s => res_eq_affT A₀ L (z s) y
  rw [hf]
  refine hc.congr_deriv ((hDu (0, z')).trans ?_)
  rw [← res_eq_affT, affT_apply]
  simp only [map_zero, zero_sub, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul]

theorem differentiableAt_chainTestT (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ)
    (z : Fin k → ℝ → ℂ) (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {t : ℝ} {y : V}
    (hy : ∀ j, IsUnit (A₀ + L y - z j t • (1 : Matrix ι ι ℂ)).det)
    (hz : ∀ j, DifferentiableAt ℝ (z j) t) :
    DifferentiableAt ℝ (chainTestT A₀ L z B K) (t, y) := by
  have hR : ∀ j, DifferentiableAt ℝ (fun q : ℝ × V => res A₀ L (z j q.1) q.2) (t, y) := by
    intro j
    have hy' : IsUnit (A₀ + affT L (y, z j t)).det := by
      rw [affT_apply, ← add_sub_assoc]
      exact hy j
    obtain ⟨D, hD, -⟩ := hasFDerivAt_inv_affine A₀ (affT L) hy'
    have hinner : DifferentiableAt ℝ (fun q : ℝ × V => (q.2, z j q.1)) (t, y) :=
      differentiableAt_snd.prodMk ((hz j).comp (t, y) differentiableAt_fst)
    have hf : (fun q : ℝ × V => res A₀ L (z j q.1) q.2) =
        (fun p : V × ℂ => (A₀ + affT L p)⁻¹) ∘ fun q : ℝ × V => (q.2, z j q.1) :=
      funext fun q => res_eq_affT A₀ L (z j q.1) q.2
    rw [hf]
    exact hD.differentiableAt.comp (t, y) hinner
  obtain ⟨D, hD, -⟩ := hasFDerivAt_slotProd B
    (M := fun q : ℝ × V => resSlots A₀ L (fun j => z j q.1) q.2) fun j => (hR j).hasFDerivAt
  exact (reTrLin K).toContinuousLinearMap.differentiableAt.comp (t, y) hD.differentiableAt

/-- The time derivative of `s ↦ chainTestT (s, y)`:
`Re tr(K ∑_j R_0 B_0 ⋯ (z_j'(t) R_j²) B_j ⋯ R_{k-1} B_{k-1})`. -/
theorem hasDerivAt_chainTestT_time (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ)
    (z : Fin k → ℝ → ℂ) (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {z' : Fin k → ℂ}
    {t : ℝ} {y : V} (hy : ∀ j, IsUnit (A₀ + L y - z j t • (1 : Matrix ι ι ℂ)).det)
    (hz : ∀ j, HasDerivAt (z j) (z' j) t) :
    HasDerivAt (fun s => chainTestT A₀ L z B K (s, y))
      (reTr K (∑ j, slotProd B (update (resSlots A₀ L (fun j => z j t) y) j
        (z' j • (res A₀ L (z j t) y * res A₀ L (z j t) y))))) t := by
  have hR : ∀ j, HasFDerivAt (fun s => resSlots A₀ L (fun j => z j s) y j)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (z' j • (res A₀ L (z j t) y * res A₀ L (z j t) y))) t :=
    fun j => (hasDerivAt_resT A₀ L (hy j) (hz j)).hasFDerivAt
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_slotProd B
    (M := fun s => resSlots A₀ L (fun j => z j s) y) hR
  have hc := ((reTrLin K).toContinuousLinearMap.hasFDerivAt.comp t hD).hasDerivAt
  refine hc.congr_deriv ?_
  change reTr K (D 1) = _
  rw [hDu]
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]

/-!
### The partial derivatives in Itô's formula
-/

section Fin

variable {d : ℕ}

/-- **`partialTime` for a time-dependent spectral parameter:**
`∂_t f(t, y) = Re tr(K ∑_j R_0 B_0 ⋯ (z_j'(t) R_j²) B_j ⋯)`, `R_j = (A₀ + L y - z_j(t))⁻¹`. -/
theorem partialTime_chainTestT (A₀ : Matrix ι ι ℂ) (L : (Fin d → ℝ) →ₗ[ℝ] Matrix ι ι ℂ)
    (z : Fin k → ℝ → ℂ) (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {t : ℝ}
    {y : Fin d → ℝ} (hy : ∀ j, IsUnit (A₀ + L y - z j t • (1 : Matrix ι ι ℂ)).det)
    (hz : ∀ j, DifferentiableAt ℝ (z j) t) :
    partialTime (chainTestT A₀ L z B K) (t, y) =
      reTr K (∑ j, slotProd B (update (resSlots A₀ L (fun j => z j t) y) j
        (deriv (z j) t • (res A₀ L (z j t) y * res A₀ L (z j t) y)))) := by
  rw [partialTime_eq_deriv (differentiableAt_chainTestT A₀ L z B K hy hz)]
  exact (hasDerivAt_chainTestT_time A₀ L z B K hy fun j => (hz j).hasDerivAt).deriv

/-- Spatial first partials: the fixed-time `Chains` derivative at `z(t)`. -/
theorem partialSpace_chainTestT (A₀ : Matrix ι ι ℂ) (L : (Fin d → ℝ) →ₗ[ℝ] Matrix ι ι ℂ)
    (z : Fin k → ℝ → ℂ) (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {t : ℝ}
    {y : Fin d → ℝ} (hy : ∀ j, IsUnit (A₀ + L y - z j t • (1 : Matrix ι ι ℂ)).det)
    (hz : ∀ j, DifferentiableAt ℝ (z j) t) (i : Fin d) :
    partialSpace (chainTestT A₀ L z B K) (t, y) i =
      -reTr K (firstVar B (resSlots A₀ L (fun j => z j t) y) (L (Pi.single i 1))) := by
  rw [partialSpace_eq_slice (differentiableAt_chainTestT A₀ L z B K hy hz), chainTestT_slice,
    fderiv_chainTest A₀ L _ B K hy]

/-- **Spatial second partials** (slicing): the fixed-time `Chains` second derivative
`Re tr(K · secondVar)` at `z(t)`, for `C²` spectral parameters. -/
theorem partialSpace2_chainTestT (A₀ : Matrix ι ι ℂ) (L : (Fin d → ℝ) →ₗ[ℝ] Matrix ι ι ℂ)
    (z : Fin k → ℝ → ℂ) (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {t : ℝ}
    {y : Fin d → ℝ} (hy : ∀ j, IsUnit (A₀ + L y - z j t • (1 : Matrix ι ι ℂ)).det)
    (hz : ∀ j, ContDiffAt ℝ 2 (z j) t) (i l : Fin d) :
    partialSpace2 (chainTestT A₀ L z B K) (t, y) i l =
      reTr K (secondVar B (resSlots A₀ L (fun j => z j t) y) (L (Pi.single i 1))
        (L (Pi.single l 1))) := by
  rw [partialSpace2_eq_slice (contDiffAt_chainTestT A₀ L z B K hy hz), chainTestT_slice,
    fderiv_fderiv_chainTest A₀ L _ B K hy]

end Fin

end Smooth

end BlockBand.Native.ErdosRiabov.VS
